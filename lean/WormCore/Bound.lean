import WormCore.Check

/-!
# The area bound and the leaf test of the worm checker

The leaf bound (the "Lean model"): on a box with centre angle `θ_c` and half-width `h`, every rotation is
`R(θ) = R(θ_c) ((1 + C) I + S J)` with `C = cos(θ - θ_c) - 1 ∈ [-h²/2, 0]` and `S = sin(θ - θ_c) ∈ [-h, h]`. In the
variables `y = (Δtₓ, Δt_y, C, S)` of the four bodies the shoelace area of a fixed list is exactly a quadratic
`F(y) = F₀ + g·y + yᵀHy/2`, bounded below on the box by
`F(y₀) - ∑ₐ |∇F(y₀)ₐ| wₐ - ∑ₐ σₐ/2`, `σₐ = max(0, ∑_{b≠a} |H̃ₐᵦ| - H̃ₐₐ)`, `H̃ = W H W` (Gershgorin), after adding the
identity terms `β (C² + S² + 2C) = 0`.
-/

namespace WormCore

open MoserWorm


/-! ## The quadratic model and its lower bound -/

/-- The four variables of body `b ≥ 1` are `4(b-1) + (0: Δtₓ, 1: Δt_y, 2: C, 3: S)`. -/
def lcol (C : Ctx) (g k : Nat) : V2 :=
  match k with
  | 0 => (DIval.ofInt 1, DIval.pt 0)
  | 1 => (DIval.pt 0, DIval.ofInt 1)
  | 2 => C.RQ[g]!
  | _ => V2.J C.RQ[g]!

/-- Interval sum (exact: `DIval.add` adds the end points). -/
def isum (l : List DIval) : DIval := l.foldl DIval.add (DIval.pt 0)

/-- The edges `(P_j, P_{j+1})` of the cyclic list `l`. -/
def cycPairs (l : List Nat) : List (Nat × Nat) := (List.range l.length).map fun j => (at' l j, at' l (j + 1))

/-- The term of the edge `(a, b)` in the coefficient `g_k` of `det(x_a, x_b)`. -/
def gTerm (C : Ctx) (a b k : Nat) : DIval :=
  let ba := C.F.body[a]!
  let bb := C.F.body[b]!
  (if bb ≠ 0 ∧ k / 4 = bb - 1 then V2.det C.X0[a]! (lcol C b (k % 4)) else DIval.pt 0).add
    (if ba ≠ 0 ∧ k / 4 = ba - 1 then V2.det (lcol C a (k % 4)) C.X0[b]! else DIval.pt 0)

/-- The term of the edge `(a, b)` in the coefficient `M_kl` of `det(x_a, x_b)`. -/
def MTerm (C : Ctx) (a b k l : Nat) : DIval :=
  let ba := C.F.body[a]!
  let bb := C.F.body[b]!
  if ba ≠ 0 ∧ bb ≠ 0 ∧ k / 4 = ba - 1 ∧ l / 4 = bb - 1 then V2.det (lcol C a (k % 4)) (lcol C b (l % 4))
  else DIval.pt 0

/-- `F₀`, `g` (length `nv`) and the non-symmetric `M` (row-major `nv × nv`) with
`F(y) = F₀ + g·y + ∑ M_kl y_k y_l` for the shoelace area of the cyclic list `l`. -/
def model (C : Ctx) (l : List Nat) : DIval × Array DIval × Array DIval :=
  let nv := 4 * C.F.k
  let ps := cycPairs l
  ((isum (ps.map fun p => V2.det C.X0[p.1]! C.X0[p.2]!)).half,
   (List.range nv).toArray.map (fun k => (isum (ps.map fun p => gTerm C p.1 p.2 k)).half),
   (List.range (nv * nv)).toArray.map (fun i => (isum (ps.map fun p => MTerm C p.1 p.2 (i / nv) (i % nv))).half))

/-- The bound data of one structure for identity weight `β` (mantissa) over the active variables `act`: the value
`F(y₀)` minus the Gershgorin penalty, and `∇F(y₀)` (used on `act` only). -/
def boundParts (nv : Nat) (act : List Nat) (F0 : DIval) (g M : Array DIval) (y0 w : Array Int) (β : Int) :
    DIval × (Nat → DIval) :=
  let H := fun a b => if a = b ∧ a % 4 ≥ 2 then (M[a * nv + b]!.add M[b * nv + a]!).add (DIval.pt (2 * β))
    else M[a * nv + b]!.add M[b * nv + a]!
  let g2 := fun a => if a % 4 = 2 then g[a]!.add (DIval.pt (2 * β)) else g[a]!
  let Fy0 := (F0.add (isum (act.map fun a => (g2 a).mul (DIval.pt y0[a]!)))).add
    (isum (act.flatMap fun a => act.map fun b => (((H a b).mul (DIval.pt y0[a]!)).mul (DIval.pt y0[b]!)).half))
  let grad := fun a => (g2 a).add (isum (act.map fun b => (H a b).mul (DIval.pt y0[b]!)))
  let pen := isum (act.map fun a =>
    ((isum ((act.filter (· ≠ a)).map fun b => (((H a b).mul (DIval.pt w[a]!)).mul (DIval.pt w[b]!)).abs)).sub
      (((H a a).mul (DIval.pt w[a]!)).mul (DIval.pt w[a]!))).pos)
  (Fy0.sub pen.half, grad)

/-- The identity weights tried. -/
def betas : List Int := [0, dfxOne / 5, dfxOne]

/-- A lower mantissa of `-h²/2` for the angle half-width mantissa `h`. -/
def cLo (h : Int) : Int := -((h * h + 2 * dfxOne - 1) / (2 * dfxOne))

/-- The centre `y₀` of the variable box: `C` at the middle of `[cLo h, 0]`, the others at `0`. -/
def y0At (C : Ctx) (a : Nat) : Int := if a % 4 = 2 then (cLo C.bd[a / 4 + 1]!.h).fdiv 2 else 0

/-- The half-widths `w` of the variable box: `hx`, `hy`, `-y₀`, `h`. -/
def wAt (C : Ctx) (a : Nat) : Int :=
  let B := C.bd[a / 4 + 1]!
  match a % 4 with
  | 0 => B.hx
  | 1 => B.hy
  | 2 => -((cLo B.h).fdiv 2)
  | _ => B.h

/-- Some structure has a vertex on body `b`. -/
def bodyUsed (C : Ctx) (sts : List (St × Int)) (b : Nat) : Bool :=
  sts.any fun p => p.1.verts.any fun g => C.F.body[g]! = b

/-- The combination bound for identity weight `β`: `∑ᵢ λᵢ (Fᵢ(y₀) - penᵢ) - ∑ₐ |∑ᵢ λᵢ ∇Fᵢ(y₀)ₐ| wₐ`. -/
def comboVal (nv : Nat) (act : List Nat) (models : List ((DIval × Array DIval × Array DIval) × Int))
    (y0 w : Array Int) (β : Int) : DIval :=
  let parts := models.map fun md => (boundParts nv act md.1.1 md.1.2.1 md.1.2.2 y0 w β, md.2)
  (isum (parts.map fun pt => pt.1.1.mul (DIval.pt pt.2))).sub
    (isum (act.map fun a => (isum (parts.map fun pt => (pt.1.2 a).mul (DIval.pt pt.2))).abs.mul (DIval.pt w[a]!)))

/-- The combination bound of a leaf, maximized over the identity weights; the active variables are those of the
bodies used by some structure. Returns the best lower end. -/
def leafBound (C : Ctx) (sts : List (St × Int)) : Int :=
  let nv := 4 * C.F.k
  let y0 := (List.range nv).toArray.map (y0At C)
  let w := (List.range nv).toArray.map (wAt C)
  let act := (List.range nv).filter fun a => bodyUsed C sts (a / 4 + 1)
  let models := sts.map fun p => (model C p.1.verts, p.2)
  betas.foldl (fun best β => max best (comboVal nv act models y0 w β).lo) (-(1000 * dfxOne))

/-! ## Leaves, refinement, the tree -/

structure Rec where
  sts : List (St × Int)
  deriving Repr, Inhabited

/-- The leaf test on the box `[lo, hi]` (mantissas at `2⁻¹²⁰`): every structure valid (weights `λᵢ ≥ 0`,
`∑ λᵢ ≤ 1`) and the combination bound above `τ` (`tauHi`: an upper mantissa of `τ`). -/
def leafOK (F : Fam) (maxsmall : Nat) (tauHi : Int) (lo hi : Array Int) (r : Rec) : Bool :=
  let C := mkCtx F lo hi
  decide (r.sts ≠ []) &&
  r.sts.all (fun (st, lam) => decide (0 ≤ lam) && stOK C maxsmall st) &&
  decide ((r.sts.map (·.2)).foldl (· + ·) 0 ≤ dfxOne) &&
  decide (tauHi < leafBound C r.sts)

/-- The coordinate of the widest angle half-width (`3(b-1)`). -/
def widestAngle (k : Nat) (lo hi : Array Int) : Nat :=
  (List.range k).foldl (fun best b =>
    if hi[3 * b]! - lo[3 * b]! > hi[3 * best]! - lo[3 * best]! then b else best) 0 |> (3 * ·)

/-- The leaf test with local refinement: if it fails, split the widest angle and check both halves (same record). -/
def leafOKR (F : Fam) (maxsmall : Nat) (tauHi : Int) : Nat → Array Int → Array Int → Rec → Bool
  | 0, lo, hi, r => leafOK F maxsmall tauHi lo hi r
  | d + 1, lo, hi, r =>
    leafOK F maxsmall tauHi lo hi r ||
      (let i := widestAngle F.k lo hi
       let s := lo[i]! + hi[i]!
       decide (s % 2 = 0) &&
         leafOKR F maxsmall tauHi d lo (hi.set! i (s / 2)) r &&
         leafOKR F maxsmall tauHi d (lo.set! i (s / 2)) hi r)

end WormCore
