import Worm13a.GeomInterface
import WormCore.Tree

/-!
# Definitions for the soundness statements of the worm checker

Real-number meaning of the checker data (`WormCore.Check`, `WormCore.Tree`; data format `WormCore/FORMAT.md`):

* a configuration is `x : Fin 12 → ℝ`; body `b = 1, …, 4` has angle `x (3(b-1))` and translation
  `(x (3(b-1)+1), x (3(b-1)+2))`; body `0` is fixed;
* a box is a pair of mantissa arrays `(lo, hi)` at scale `2⁻¹²⁰` (`InBox`: closed box);
* global vertex `g` of the family `(arcs, gid)` is the vertex `gid[g].2` of the arc `gid[g].1`, in the body frame of
  the checker (relative to the mean of the arc's vertices for the moving bodies), placed by `Worm.motion` (`place`);
* `StValid` is the validity of a structure in real terms: the hypotheses of `Worm.Geom.small_le`, `fan_le`, `chord_le`.

The statements using these definitions are in `WormSound.Tree` (tree coverage) and `WormSound.Valid`
(validity of the structures).
-/

noncomputable section

namespace WormCore.Sound

open Worm.Geom

/-! ## Boxes -/

/-- `x` lies in the closed box with mantissas `lo hi` (scale `2⁻¹²⁰`). -/
def InBox (lo hi : Array Int) (x : Fin 12 → ℝ) : Prop :=
  ∀ i : Fin 12, (lo[i.val]! : ℝ) / 2 ^ BS ≤ x i ∧ x i ≤ (hi[i.val]! : ℝ) / 2 ^ BS

/-- The box `(lo, hi)` lies in the box `(lo', hi')` (coordinates `0, …, 11`). -/
def BoxSub (lo hi lo' hi' : Array Int) : Prop :=
  ∀ i < 12, lo'[i]! ≤ lo[i]! ∧ hi[i]! ≤ hi'[i]!

/-- The root data has twelve coordinates and the parts share the cells evenly. -/
def RootShape (R : Root) : Prop :=
  R.lo.size = 12 ∧ R.hi.size = 12 ∧ R.split0.size = 12 ∧ 0 < R.nparts ∧ ncells R % R.nparts = 0

/-- The angle coordinates of the box lie in `[-64, 64]` (the range of Keller's `sincosIv`). -/
def AngleRange (lo hi : Array Int) : Prop :=
  ∀ b < 4, -(64 * 2 ^ BS : Int) ≤ lo[3 * b]! ∧ hi[3 * b]! ≤ 64 * 2 ^ BS

/-! ## The family and the placed vertices -/

/-- Side conditions on the family data: positive denominators, step directions in `[-360, 360]` degrees. -/
def ArcsOK (arcs : List Arc) : Prop :=
  ∀ a ∈ arcs, 0 < a.sx.2 ∧ 0 < a.sy.2 ∧ ∀ s ∈ a.steps, 0 < s.2.1 ∧ -360 ≤ s.2.2 ∧ s.2.2 ≤ 360

/-- Coordinate `i` of a configuration (`0` outside `Fin 12`). -/
def coord (x : Fin 12 → ℝ) (i : ℕ) : ℝ := if h : i < 12 then x ⟨i, h⟩ else 0

/-- The exact vertices of an arc: start `sx + i sy`, then steps `ℓ e^{iπd/180}` (`ℓ = num/den`, `d` in degrees). -/
def arcPts (a : Arc) : List ℂ :=
  stepVertices ⟨(a.sx.1 : ℝ) / a.sx.2, (a.sy.1 : ℝ) / a.sy.2⟩
    (a.steps.map fun s => ((s.1 : ℝ) / s.2.1, (s.2.2 : ℝ)))

/-- The body-frame point of global vertex `g`: the arc vertex itself for body `0`, relative to the mean of the arc's
vertices for the moving bodies. -/
def qReal (arcs : List Arc) (gid : List (Nat × Nat)) (g : ℕ) : ℂ :=
  let V := arcPts (arcs.getD (gid.getD g (0, 0)).1 ⟨(0, 1), (0, 1), []⟩)
  let v := V.getD (gid.getD g (0, 0)).2 0
  if (gid.getD g (0, 0)).1 = 0 then v else v - V.sum / V.length

/-- The position of global vertex `g` in configuration `x`. -/
def place (arcs : List Arc) (gid : List (Nat × Nat)) (x : Fin 12 → ℝ) (g : ℕ) : ℂ :=
  let b := (gid.getD g (0, 0)).1
  if b = 0 then qReal arcs gid g
  else Worm.motion (coord x (3 * (b - 1))) ⟨coord x (3 * (b - 1) + 1), coord x (3 * (b - 1) + 2)⟩
    (qReal arcs gid g)

/-! ## Validity of a structure -/

/-- The centre `z = (zx, zy) 2⁻⁵⁶` of a fan. -/
def fanZ (zx zy : Int) : ℂ := ⟨(zx : ℝ) / 2 ^ MoserWorm.dfxS, (zy : ℝ) / 2 ^ MoserWorm.dfxS⟩

/-- The chord tree of the checker as a chord tree of the geometric interface. -/
def ctOf : CT → CTree
  | .small => .small
  | .vfan r => .vfan r
  | .cut s t L R => .cut s t (ctOf L) (ctOf R)

/-- The total turning of the cyclic list `P` around `z`. -/
def turning (P : List ℂ) (z : ℂ) : ℝ :=
  ∑ j ∈ Finset.range P.length, Complex.arg ((pt P (j + 1) - z) / (pt P j - z))

/-- Validity in real terms of a structure whose placed vertices are `P`: the hypotheses of `small_le`, `fan_le`
(with `turning`), `chord_le`. -/
def StValid (P : List ℂ) : St → Prop
  | .small _ => P.length ≤ 4
  | .fan _ zx zy =>
      3 ≤ P.length ∧ (∀ j < P.length, 0 < cross (pt P j - fanZ zx zy) (pt P (j + 1) - fanZ zx zy)) ∧
        turning P (fanZ zx zy) < 4 * Real.pi
  | .chord _ t => ChordOK (ctOf t) P

end WormCore.Sound
