import MoserWorm.Common.Interval.Basic
import MoserWorm.Common.Interval.RationalBasic

/-!
# The checker of the worm certificate (Moser 13a, rotations and translations only): data and validity

The certificate `cert_w2400a` is a binary tree of boxes in the placement space of the four moving bodies (angle `θ`,
translation `t` per body; body 0 is the fixed unit segment). At a leaf, a list of placed vertices (a fan around a
point `z`, a vertex fan or chord decomposition, or at most four points) has shoelace area at least `τ` on the whole box,
possibly as a convex combination (Lemma K). This file has the family data, the per-box context and the validity tests
of the structures (`stOK`); the area bound and the leaf test are in `WormCore.Bound`.

Validity of the structures is checked by interval arithmetic with the movement bounds of the certificate checker
`wcheck_v2`; the winding of a fan is certified at the box centre by a partition of the cycle into arcs `a_s, …, a_e`
with `det(a_s, a_j) > 0` (each turning by less than `π`), and on the whole box by the positive consecutive determinants.

Arithmetic: Keller's dyadic intervals `MoserWorm.DIval` (scale `2⁻⁵⁶`, outward rounding). Box coordinates are exact
mantissas at scale `2⁻¹²⁰`.
-/

namespace WormCore

open MoserWorm

/-- Box coordinates are mantissas at scale `2⁻¹²⁰`. -/
abbrev BS : Nat := 120

/-- Lower and upper rounding of `m / 2¹²⁰` to the interval scale `2⁻⁵⁶`. -/
def toLo (m : Int) : Int := m.fdiv (2 ^ (BS - dfxS))
def toHi (m : Int) : Int := -((-m).fdiv (2 ^ (BS - dfxS)))

instance : Inhabited DIval := ⟨DIval.pt 0⟩

/-! ## Planar interval vectors -/

abbrev V2 := DIval × DIval

namespace V2
def add (a b : V2) : V2 := (a.1.add b.1, a.2.add b.2)
def sub (a b : V2) : V2 := (a.1.sub b.1, a.2.sub b.2)
def smul (c : DIval) (a : V2) : V2 := (c.mul a.1, c.mul a.2)
def J (a : V2) : V2 := (a.2.neg, a.1)
/-- Rotation by the angle with sine `s` and cosine `c`. -/
def rot (s c : DIval) (v : V2) : V2 := ((c.mul v.1).sub (s.mul v.2), (s.mul v.1).add (c.mul v.2))
def det (a b : V2) : DIval := (a.1.mul b.2).sub (a.2.mul b.1)
def norm (a : V2) : DIval := DIval.norm2 a.1 a.2
def zero : V2 := (DIval.pt 0, DIval.pt 0)
end V2

/-! ## The family -/

/-- A polygonal arc: start `(sx, sy)` (rationals `num/den`) and steps `(ℓ_num, ℓ_den, direction in degrees)`. -/
structure Arc where
  sx : Int × Int
  sy : Int × Int
  steps : List (Int × Int × Int)

/-- An enclosure of `π d / 180`. -/
def degI (d : Int) : DIval := DIval.mul DIval.piI (DIval.ratio d 180)

def arcVertsAux : V2 → List (Int × Int × Int) → List V2
  | p, [] => [p]
  | p, (ln, ld, d) :: rest =>
    let sc := DIval.sincosIv (degI d)
    let l := DIval.ratio ln ld
    p :: arcVertsAux (V2.add p (l.mul sc.2, l.mul sc.1)) rest

/-- Enclosures of the vertices of an arc. -/
def arcVerts (a : Arc) : List V2 :=
  arcVertsAux (DIval.ratio a.sx.1 a.sx.2, DIval.ratio a.sy.1 a.sy.2) a.steps

/-- The family data used by the checker. -/
structure Fam where
  /-- body of each global vertex (`0` = the fixed segment) -/
  body : Array Nat
  /-- body-frame point of each global vertex: relative to the mean of the body's vertices (bodies `≥ 1`) -/
  q : Array V2
  /-- `‖q‖` -/
  qn : Array DIval
  /-- number of moving bodies -/
  k : Nat

def meanV : List V2 → V2
  | [] => V2.zero
  | l =>
    let s := l.foldl V2.add V2.zero
    V2.smul (DIval.ratio 1 l.length) s

/-- The family data from the arcs and the global vertex map `(body, vertex index)`. -/
def mkFam (arcs : List Arc) (gid : List (Nat × Nat)) : Fam :=
  let verts := arcs.map arcVerts
  let q := gid.map fun (b, j) =>
    let V := verts.getD b []
    let v := V.getD j V2.zero
    if b = 0 then v else V2.sub v (meanV V)
  { body := (gid.map (·.1)).toArray, q := q.toArray, qn := (q.map V2.norm).toArray, k := arcs.length - 1 }

/-! ## The box at a leaf -/

/-- Per moving body: sine and cosine of the centre angle, the angle half-width (upper mantissa), the centre
translation, the translation half-widths and the Euclidean radius of the translation box. -/
structure BodyData where
  s : DIval
  c : DIval
  h : Int
  tc : V2
  hx : Int
  hy : Int
  trad : DIval

instance : Inhabited BodyData := ⟨⟨DIval.pt 0, DIval.pt 0, 0, V2.zero, 0, 0, DIval.pt 0⟩⟩

/-- Coordinates of body `b ≥ 1` in the box arrays: `3(b-1)` angle, then `x`, `y`. -/
def bodyData (lo hi : Array Int) (b : Nat) : BodyData :=
  let i := 3 * (b - 1)
  let th := (lo[i]! + hi[i]!).fdiv 2
  let hθ := max (hi[i]! - th) (th - lo[i]!)
  let tx := (lo[i+1]! + hi[i+1]!).fdiv 2
  let ty := (lo[i+2]! + hi[i+2]!).fdiv 2
  let hx := toHi (max (hi[i+1]! - tx) (tx - lo[i+1]!))
  let hy := toHi (max (hi[i+2]! - ty) (ty - lo[i+2]!))
  let sc := DIval.sincosIv ⟨toLo th, toHi th⟩
  { s := sc.1, c := sc.2, h := toHi hθ, tc := (⟨toLo tx, toHi tx⟩, ⟨toLo ty, toHi ty⟩), hx := hx, hy := hy,
    trad := DIval.norm2 (DIval.pt hx) (DIval.pt hy) }

/-- Per-leaf data: the body data and, for every global vertex, `R(θ_c) q`, the position at the box centre and the
movement bound `‖q‖ h + t_rad` (zero for the fixed body). -/
structure Ctx where
  F : Fam
  bd : Array BodyData
  RQ : Array V2
  X0 : Array V2
  MV : Array DIval

def mkCtx (F : Fam) (lo hi : Array Int) : Ctx :=
  let bd : Array BodyData := (List.range (F.k + 1)).toArray.map fun b =>
    if b = 0 then default else bodyData lo hi b
  let n := F.body.size
  let RQ := (List.range n).toArray.map fun g =>
    let b := F.body[g]!
    if b = 0 then F.q[g]! else V2.rot bd[b]!.s bd[b]!.c F.q[g]!
  let X0 := (List.range n).toArray.map fun g =>
    let b := F.body[g]!
    if b = 0 then F.q[g]! else V2.add bd[b]!.tc RQ[g]!
  let MV := (List.range n).toArray.map fun g =>
    let b := F.body[g]!
    if b = 0 then DIval.pt 0 else (F.qn[g]!.mul (DIval.pt bd[b]!.h)).add bd[b]!.trad
  ⟨F, bd, RQ, X0, MV⟩

/-- Upper bound of the movement of `x_b - x_a`. -/
def pairMove (C : Ctx) (a b : Nat) : DIval :=
  let ba := C.F.body[a]!
  if ba = C.F.body[b]! then
    if ba = 0 then DIval.pt 0 else (V2.norm (V2.sub C.F.q[b]! C.F.q[a]!)).mul (DIval.pt C.bd[ba]!.h)
  else C.MV[a]!.add C.MV[b]!

/-- `x_b - x_a` at the centre, with the same-body correlation kept. -/
def diff (C : Ctx) (a b : Nat) : V2 :=
  let ba := C.F.body[a]!
  if ba = C.F.body[b]! ∧ ba ≠ 0 then V2.rot C.bd[ba]!.s C.bd[ba]!.c (V2.sub C.F.q[b]! C.F.q[a]!)
  else V2.sub C.X0[b]! C.X0[a]!

/-- Bounds of `det(x_b - x_a, x_i - x_a)` on the box: centre value and error (exact when all three are on one body). -/
def det3 (C : Ctx) (a b i : Nat) : DIval :=
  let ba := C.F.body[a]!
  if ba = C.F.body[b]! ∧ ba = C.F.body[i]! then
    V2.det (V2.sub C.F.q[b]! C.F.q[a]!) (V2.sub C.F.q[i]! C.F.q[a]!)
  else
    let u := diff C a b
    let v := diff C a i
    let eab := pairMove C a b
    let eai := pairMove C a i
    let err := ((eab.mul (V2.norm v)).add (eai.mul (V2.norm u))).add (eab.mul eai)
    let d := V2.det u v
    ⟨(d.sub err).lo, (d.add err).hi⟩

def det3Lo (C : Ctx) (a b i : Nat) : Int := (det3 C a b i).lo
def det3Hi (C : Ctx) (a b i : Nat) : Int := (det3 C a b i).hi

/-- The movement bound of `det(x_a - z, x_b - z)` (and of the dot product) on the box. -/
def fanVar (C : Ctx) (z : V2) (a b : Nat) : DIval :=
  let ba := C.F.body[a]!
  let xa := V2.sub C.X0[a]! z
  let xb := V2.sub C.X0[b]! z
  if ba = C.F.body[b]! then
    if ba = 0 then DIval.pt 0
    else
      let B := C.bd[ba]!
      let w := V2.norm (V2.sub C.F.q[b]! C.F.q[a]!)
      let tz := V2.norm (V2.sub B.tc z)
      w.mul ((B.trad.mul ((DIval.ofInt 1).add (DIval.pt B.h))).add (tz.mul (DIval.pt B.h)))
  else
    let dx := C.MV[a]!
    let dy := C.MV[b]!
    (dx.mul ((V2.norm xb).add dy)).add ((V2.norm xa).mul dy)

/-- Lower bound of `det(x_a - z, x_b - z)` on the box. -/
def fanDetLo (C : Ctx) (z : V2) (a b : Nat) : Int :=
  ((V2.det (V2.sub C.X0[a]! z) (V2.sub C.X0[b]! z)).sub (fanVar C z a b)).lo

/-- Lower bound of `⟨x_a - z, x_b - z⟩` on the box (the general movement bound of a product of two moving vectors). -/
def fanDotLo (C : Ctx) (z : V2) (a b : Nat) : Int :=
  let xa := V2.sub C.X0[a]! z
  let xb := V2.sub C.X0[b]! z
  let dx := C.MV[a]!
  let dy := C.MV[b]!
  let var := (dx.mul ((V2.norm xb).add dy)).add ((V2.norm xa).mul dy)
  (((xa.1.mul xb.1).add (xa.2.mul xb.2)).sub var).lo

/-! ## Structures -/

/-- Chord trees: `small`, vertex fan from position `r`, cut at the chord `(s, t)`. -/
inductive CT where
  | small
  | vfan (r : Nat)
  | cut (s t : Nat) (left right : CT)
  deriving Repr, Inhabited

/-- A structure of a leaf: a list of global vertex ids with its validity data. -/
inductive St where
  | small (v : List Nat)
  | fan (v : List Nat) (zx zy : Int)
  | chord (v : List Nat) (t : CT)
  deriving Repr, Inhabited

def St.verts : St → List Nat
  | .small v => v
  | .fan v _ _ => v
  | .chord v _ => v

/-- The point of index `j` of a cyclic list. -/
def at' (l : List Nat) (j : Nat) : Nat := l.getD (j % l.length) 0

/-- `windScan P D d bs`: the best cost of the steps from a position `i` whose arcs end at `i + d, i + d + 1, …`,
given `bs = [best(i + d), best(i + d + 1), …]`: scan while `P` (the arc condition) stays true. -/
def windScan (P D : Nat → Bool) : Nat → List Nat → Nat
  | _, [] => 100
  | d, b :: bs => if P d then min ((if D d then 1 else 2) + b) (windScan P D (d + 1) bs) else 100

/-- `windBest m P D s0 k = [best(m - k), …, best(m)]`, where `best(i)` is the minimal cost to cover the steps
`i, …, m - 1` (positions relative to `s0`; `100` = impossible). -/
def windBest (m : Nat) (P D : Nat → Nat → Bool) (s0 : Nat) : Nat → List Nat
  | 0 => [0]
  | k + 1 =>
    let bs := windBest m P D s0 k
    windScan (P ((s0 + (m - (k + 1))) % m)) (D ((s0 + (m - (k + 1))) % m)) 1 bs :: bs

/-- Winding certificate of a fan with `m` points at the box centre: a partition of the cycle into arcs `a_s, …, a_e`
(`a = x - z`) with `det(a_s, a_t) > 0` for `s < t ≤ e` (each arc turns by less than `π`), costing `1` if also
`⟨a_s, a_e⟩ > 0` (less than `π/2`) and `2` otherwise; the total cost must be at most `7` (total turning below
`7π/2 < 4π`, so exactly `2π`). `P i d`, `D i d`: positivity of `det(a_i, a_{i+d})` and `⟨a_i, a_{i+d}⟩` at the centre.
On the box the consecutive determinants stay positive, so the total turning is constant there (continuity). -/
def windCost (m : Nat) (P D : Nat → Nat → Bool) (s0 : Nat) : Nat := (windBest m P D s0 m).headD 100

def fanOK (C : Ctx) (v : List Nat) (zx zy : Int) : Bool :=
  let m := v.length
  let z : V2 := (DIval.pt zx, DIval.pt zy)
  let va := v.toArray
  -- the winding at the box centre: P[i][d], D[i][d] (0 ≤ d ≤ m; false for d = 0 and d = m) with the centre values;
  -- on the whole box only the consecutive determinants are needed (the total turning is then constant on the box)
  let P : Array (Array Bool) := (List.range m).toArray.map fun i =>
    (List.range (m + 1)).toArray.map fun d =>
      decide (1 ≤ d) && decide (d < m) &&
        decide (0 < (V2.det (V2.sub C.X0[va[i]!]! z) (V2.sub C.X0[va[(i + d) % m]!]! z)).lo)
  let D : Array (Array Bool) := (List.range m).toArray.map fun i =>
    (List.range (m + 1)).toArray.map fun d =>
      let xa := V2.sub C.X0[va[i]!]! z
      let xb := V2.sub C.X0[va[(i + d) % m]!]! z
      decide (1 ≤ d) && decide (d < m) && decide (0 < ((xa.1.mul xb.1).add (xa.2.mul xb.2)).lo)
  decide (3 ≤ m) &&
  ((List.range m).all fun j => decide (0 < fanDetLo C z va[j]! va[(j + 1) % m]!)) &&
  ((List.range m).any fun s0 => decide (windCost m (fun i d => (P[i]!)[d]!) (fun i d => (D[i]!)[d]!) s0 ≤ 7))

def vfanOK (C : Ctx) (piece : List Nat) (r : Nat) : Bool :=
  let m := piece.length
  let l := piece.drop r ++ piece.take r
  ((List.range m).all fun i => decide (i < 2) || decide (0 < det3Lo C (at' l 0) (at' l 1) (at' l i))) &&
  ((List.range m).all fun i => decide (i < 2) || decide (m ≤ i + 1) ||
    decide (0 < det3Lo C (at' l 0) (at' l i) (at' l (i + 1))))

def chordOK (C : Ctx) (maxsmall : Nat) : CT → List Nat → Bool
  | .small, piece => decide (piece.length ≤ maxsmall)
  | .vfan r, piece => decide (r < piece.length) && decide (3 ≤ piece.length) && vfanOK C piece r
  | .cut s t L R, piece =>
    let n := piece.length
    let dd := (t + n - s) % n
    let ps := at' piece s
    let pt := at' piece t
    decide (s < n) && decide (t < n) && decide (2 ≤ dd) && decide (dd + 2 ≤ n) &&
    decide (0 < ((V2.norm (diff C ps pt)).sub (pairMove C ps pt)).lo) &&
    ((List.range dd).all fun k => decide (k = 0) || decide (det3Hi C ps pt (at' piece (s + k)) ≤ 0)) &&
    ((List.range (n - dd)).all fun k => decide (k = 0) || decide (0 ≤ det3Lo C ps pt (at' piece (t + k)))) &&
    chordOK C maxsmall L ((List.range (dd + 1)).map fun k => at' piece (s + k)) &&
    chordOK C maxsmall R ((List.range (n - dd + 1)).map fun k => at' piece (t + k))

def stOK (C : Ctx) (maxsmall : Nat) : St → Bool
  | .small v => decide (v.length ≤ maxsmall) && v.Nodup && v.all (· < C.F.body.size)
  | .fan v zx zy => v.Nodup && v.all (· < C.F.body.size) && fanOK C v zx zy
  | .chord v t => v.Nodup && v.all (· < C.F.body.size) && chordOK C maxsmall t v

end WormCore
