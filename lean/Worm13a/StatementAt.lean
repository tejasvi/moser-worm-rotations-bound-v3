import Worm13a.Statement

/-!
# The statement for a general bound `τ`

`WormLowerAt τ`: every convex set that contains a rotated and translated copy of every unit arc has area at least
`τ`; `OptimalAreaLowerAt τ`: the least area of such a set is at least `τ`. For `τ = 24/100` these are `WormLowerM` and
`OptimalAreaLowerM`.
-/

open MeasureTheory

namespace Worm

/-- Every convex set that contains a rotated and translated copy of every unit arc has area at least `τ`. -/
def WormLowerAt (τ : ℝ) : Prop :=
  ∀ K : Set Plane, IsConvexCoverM K → ENNReal.ofReal τ ≤ volume K

/-- The least area of such a set is at least `τ`. -/
def OptimalAreaLowerAt (τ : ℝ) : Prop :=
  ENNReal.ofReal τ ≤ optimalAreaM

lemma wormLowerM_iff : WormLowerM ↔ WormLowerAt (24 / 100) := Iff.rfl

lemma optimalAreaLowerM_iff : OptimalAreaLowerM ↔ OptimalAreaLowerAt (24 / 100) := Iff.rfl

end Worm
