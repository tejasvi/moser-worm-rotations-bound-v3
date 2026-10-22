import WormCore.Bound

/-!
# The certificate tree and its text format (core Lean only)

* `cellBox`: the root cells, a grid of `split0` cells of the root box, distributed over the parts as in the
  certificate (`cells[part::nparts]`, row-major);
* `unitBoxes`: the boxes of the units of a part, walking the part's skeleton (`'0'`-`'9'`, `'a'`, `'b'` split a
  coordinate, lower half first; `'U'` a unit);
* `unitOK`: a unit's subtree (`'L'`, `'K'` a leaf) with every leaf passing `leafOKR`;
* `chunkOK`: the units of a chunk (text format of `tools/wconvert.py`), each against its box from the skeleton.

The data (skeletons, chunks) is untrusted: every box is recomputed here and every leaf is re-verified.
-/

namespace WormCore

open MoserWorm

/-! ## Root cells -/

/-- The global data of the certificate. -/
structure Root where
  lo : Array Int        -- root box, mantissas at `2⁻¹²⁰`
  hi : Array Int
  split0 : Array Nat     -- cells per coordinate
  nparts : Nat

/-- The product of `split0[j+1], …, split0[d-1]` (row-major stride of coordinate `j`). -/
def stride (R : Root) (j : Nat) : Nat := ((R.split0.toList.drop (j + 1))).foldl (· * ·) 1

/-- The index of cell `c` along coordinate `j`. -/
def cellIdx (R : Root) (c j : Nat) : Nat := (c / stride R j) % R.split0[j]!

/-- The box of cell number `c` (row-major index over `split0`). -/
def cellBox (R : Root) (c : Nat) : Array Int × Array Int :=
  let w := fun j => (R.hi[j]! - R.lo[j]!) / ((R.split0[j]! : Nat) : Int)
  ((List.range R.lo.size).toArray.map fun j => R.lo[j]! + w j * (cellIdx R c j : Int),
   (List.range R.lo.size).toArray.map fun j => R.lo[j]! + w j * ((cellIdx R c j : Int) + 1))

/-- The cells are exact: `split0` divides every root width. -/
def rootExact (R : Root) : Bool :=
  (List.range R.split0.size).all fun j => decide ((R.hi[j]! - R.lo[j]!) % (R.split0[j]! : Int) = 0) &&
    decide (R.lo[j]! < R.hi[j]!) && decide (0 < R.split0[j]!)

/-- Number of cells. -/
def ncells (R : Root) : Nat := R.split0.foldl (· * ·) 1

/-! ## Splitting -/

def codeDim (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if c = 'a' then some 10 else if c = 'b' then some 11 else none

/-- The two halves of a box along coordinate `k` (lower first); `none` if the midpoint is not exact. -/
def halves (lo hi : Array Int) (k : Nat) : Option ((Array Int × Array Int) × (Array Int × Array Int)) :=
  let s := lo[k]! + hi[k]!
  if s % 2 = 0 ∧ k < lo.size ∧ k < hi.size then some ((lo, hi.set! k (s / 2)), (lo.set! k (s / 2), hi)) else none

/-- Walk a skeleton from a list of start boxes: the unit boxes in order, or `none` on malformed data. -/
def skelWalk : Nat → List Char → List (Array Int × Array Int) → Array (Array Int × Array Int) →
    Option (Array (Array Int × Array Int) × List Char)
  | 0, _, _, _ => none
  | _ + 1, cs, [], acc => some (acc, cs)
  | fuel + 1, c :: cs, (lo, hi) :: st, acc =>
    if c = 'U' then skelWalk fuel cs st (acc.push (lo, hi))
    else match codeDim c with
      | some k => match halves lo hi k with
        | some (l, u) => skelWalk fuel cs (l :: u :: st) acc
        | none => none
      | none => none
  | _ + 1, [], _ :: _, _ => none

/-- The unit boxes of part `p` from its skeleton (all of its `64` cells in order). -/
def unitBoxes (R : Root) (p : Nat) (skel : String) : Option (Array (Array Int × Array Int)) :=
  let cells := (List.range (ncells R / R.nparts)).map fun k => cellBox R (p + R.nparts * k)
  match skelWalk (2 * skel.length + 2) skel.toList cells #[] with
  | some (acc, []) => some acc
  | _ => none

/-! ## Text parsing -/

def b36val (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat + 10) else none

def parseB36 (s : String) : Option Nat :=
  if s.isEmpty then none
  else s.foldl (fun acc c => match acc, b36val c with
    | some a, some v => some (36 * a + v)
    | _, _ => none) (some 0)

def parseIntDec (s : String) : Option Int := s.toInt?

/-- Chord trees: `s`, `f r`, `c s t L R`. -/
def parseCT : Nat → List Char → Option (CT × List Char)
  | 0, _ => none
  | _ + 1, 's' :: rest => some (.small, rest)
  | _ + 1, 'f' :: r :: rest => (b36val r).map fun v => (.vfan v, rest)
  | fuel + 1, 'c' :: s :: t :: rest =>
    match b36val s, b36val t with
    | some s', some t' => match parseCT fuel rest with
      | some (L, rest2) => match parseCT fuel rest2 with
        | some (R, rest3) => some (.cut s' t' L R, rest3)
        | none => none
      | none => none
    | _, _ => none
  | _, _ => none

def idsOf (s : String) : List Nat := s.toList.map fun c => c.toNat - 'a'.toNat

/-- A structure token: `s<ids>`, `f<ids>|<zx>|<zy>`, `c<ids>|<tree>`. -/
def parseSt (tok : String) : Option St :=
  match tok.toList with
  | 's' :: ids => some (.small (idsOf (String.ofList ids)))
  | 'f' :: rest =>
    match (String.ofList rest).splitOn "|" with
    | [ids, zx, zy] => match parseIntDec zx, parseIntDec zy with
      | some x, some y => some (.fan (idsOf ids) x y)
      | _, _ => none
    | _ => none
  | 'c' :: rest =>
    match (String.ofList rest).splitOn "|" with
    | [ids, t] => match parseCT (t.length + 1) t.toList with
      | some (tr, []) => some (.chord (idsOf ids) tr)
      | _ => none
    | _ => none
  | _ => none

/-- A leaf record token: `<i>` or `<i>,<w>;<i>,<w>;…`. -/
def parseRec (table : Array St) (tok : String) : Option Rec :=
  if tok.any (· = ',') then
    let items := tok.splitOn ";"
    let sts := items.map fun it => match it.splitOn "," with
      | [i, w] => match parseB36 i, parseIntDec w with
        | some i', some w' => if i' < table.size then some (table[i']!, w') else none
        | _, _ => none
      | _ => none
    if sts.all Option.isSome then some ⟨sts.filterMap id⟩ else none
  else
    match parseB36 tok with
    | some i => if i < table.size then some ⟨[(table[i]!, dfxOne)]⟩ else none
    | none => none

/-! ## Units and chunks -/

/-- Walk a unit's subtree: every leaf checked with its record (in order). Returns the remaining records. -/
def unitWalk (F : Fam) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat) :
    Nat → List Char → List (Array Int × Array Int) → List Rec → Option (List Rec)
  | 0, _, _, _ => none
  | _ + 1, [], [], recs => some recs
  | fuel + 1, c :: cs, (lo, hi) :: st, recs =>
    if c = 'L' ∨ c = 'K' then
      match recs with
      | r :: rs => if leafOKR F maxsmall tauHi rdepth lo hi r then unitWalk F maxsmall tauHi rdepth fuel cs st rs else none
      | [] => none
    else match codeDim c with
      | some k => match halves lo hi k with
        | some (l, u) => unitWalk F maxsmall tauHi rdepth fuel cs (l :: u :: st) recs
        | none => none
      | none => none
  | _, _, _, _ => none

/-- A unit: its codes and records against its box; all records used. -/
def unitOK (F : Fam) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat) (box : Array Int × Array Int)
    (codes : String) (recs : List Rec) : Bool :=
  match unitWalk F maxsmall tauHi rdepth (codes.length + 1) codes.toList [box] recs with
  | some [] => true
  | _ => false

/-- The head `U<p>.<u>` of a unit block. -/
def parseUnitHead (t : String) : Option (Nat × Nat) :=
  match t.toList with
  | 'U' :: rest => match (String.ofList rest).splitOn "." with
    | [p, u] => match p.toNat?, u.toNat? with
      | some p', some u' => some (p', u')
      | _, _ => none
    | _ => none
  | _ => none

/-- The codes token `C<codes>`. -/
def parseCodes (t : String) : Option String :=
  match t.toList with
  | 'C' :: cs => some (String.ofList cs)
  | _ => none

def countLeaves (cs : String) : Nat := cs.foldl (fun a c => if c = 'L' ∨ c = 'K' then a + 1 else a) 0

/-- Check the unit blocks of a chunk; returns the list of units checked, in order, or `none`. -/
def unitsCheck (F : Fam) (R : Root) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat) (skel : Nat → String)
    (table : Array St) : Nat → List String → Option (List (Nat × Nat))
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, t :: rest =>
    match parseUnitHead t, rest with
    | some (p, u), c :: rest' =>
      match parseCodes c, unitBoxes R p (skel p) with
      | some cs, some boxes =>
        let nl := countLeaves cs
        let recs := (rest'.take nl).map (parseRec table)
        if u < boxes.size ∧ (rest'.take nl).length = nl ∧ recs.all Option.isSome ∧
            unitOK F maxsmall tauHi rdepth boxes[u]! cs (recs.filterMap id) = true then
          (unitsCheck F R maxsmall tauHi rdepth skel table fuel (rest'.drop nl)).map ((p, u) :: ·)
        else none
      | _, _ => none
    | _, _ => none

/-- Check a chunk: the structure table `T<n> …`, then every unit block against its box from the part's skeleton.
Returns the list of units checked, in order. -/
def chunkCheck (F : Fam) (R : Root) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat) (skel : Nat → String)
    (txt : String) : Option (List (Nat × Nat)) :=
  match txt.splitOn " " with
  | t0 :: rest =>
    match t0.toList with
    | 'T' :: ns =>
      match (String.ofList ns).toNat? with
      | some n =>
        let table := (rest.take n).map parseSt
        if (rest.take n).length = n ∧ table.all Option.isSome then
          unitsCheck F R maxsmall tauHi rdepth skel (table.filterMap id).toArray (rest.length + 1) (rest.drop n)
        else none
      | none => none
    | _ => none
  | [] => none

def chunkOK (F : Fam) (R : Root) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat) (skel : Nat → String)
    (txt : String) : Bool := (chunkCheck F R maxsmall tauHi rdepth skel txt).isSome

end WormCore
