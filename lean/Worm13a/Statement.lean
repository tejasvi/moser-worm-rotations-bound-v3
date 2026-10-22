import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Moser's worm problem with rotations and translations only (M+): definitions of the statement

A unit arc is a curve `γ : ℝ → ℂ` that is continuous on `[0, 1]` and has length (total variation on `[0, 1]`) exactly
`1`. These definitions follow Keller, arXiv:2609.21968 (Lean development `MoserWorm.Common.Defs`, Apache-2.0), where
congruent copies may also be reflected (`M+-`). Here a set `K` covers `γ` when it contains a rotated and translated copy
of the trace `γ([0, 1])`, i.e. its image under a proper rigid motion `z ↦ e^{iθ} z + t` (`M+`).

Theorem: every convex set that covers every unit arc in this sense has area at least `0.2410`
(`WormLowerAt (2410 / 10000)`, `Worm13a/StatementAt.lean`). `WormLowerM` below is the bound `0.24`.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Worm

/-- The Euclidean plane, with its usual norm and Lebesgue measure. -/
abbrev Plane := ℂ

abbrev I01 : Set ℝ := Icc 0 1

/-- The length of `γ` on `[0, 1]` (total variation). -/
def arcLength (γ : ℝ → Plane) : ℝ≥0∞ := eVariationOn γ I01

/-- The trace `γ([0, 1])`. -/
def trace (γ : ℝ → Plane) : Set Plane := γ '' I01

/-- Unit arcs: continuous on `[0, 1]`, of length exactly `1`. -/
def IsUnitArc (γ : ℝ → Plane) : Prop :=
  ContinuousOn γ I01 ∧ arcLength γ = 1

/-- The proper rigid motion `z ↦ e^{iθ} z + t` (rotation by `θ`, then translation by `t`). -/
def motion (θ : ℝ) (t : Plane) (z : Plane) : Plane :=
  Complex.exp (θ * Complex.I) * z + t

/-- `K` contains a rotated and translated copy of the trace of `γ`. -/
def CoversM (K : Set Plane) (γ : ℝ → Plane) : Prop :=
  ∃ θ : ℝ, ∃ t : Plane, motion θ t '' trace γ ⊆ K

/-- Convex covers of all unit arcs under proper rigid motions. -/
def IsConvexCoverM (K : Set Plane) : Prop :=
  Convex ℝ K ∧ ∀ γ, IsUnitArc γ → CoversM K γ

/-- The least area of such a cover (in `[0, ∞]`, so that unbounded convex covers are allowed). -/
def optimalAreaM : ℝ≥0∞ :=
  sInf {a | ∃ K : Set Plane, IsConvexCoverM K ∧ volume K = a}

/-- The bound `0.24` as a proposition: every convex set that contains a rotated and translated copy of every
unit arc has area at least `0.24`. (This package proves the stronger
`Worm.worm_lower_2410 : WormLowerAt (2410 / 10000)`.) -/
def WormLowerM : Prop :=
  ∀ K : Set Plane, IsConvexCoverM K → ENNReal.ofReal (24 / 100) ≤ volume K

/-- The bound `0.24` for the least area, as a proposition. (This package proves the stronger
`Worm.optimalAreaM_lower_2410 : OptimalAreaLowerAt (2410 / 10000)`.) -/
def OptimalAreaLowerM : Prop :=
  ENNReal.ofReal (24 / 100) ≤ optimalAreaM

end Worm
