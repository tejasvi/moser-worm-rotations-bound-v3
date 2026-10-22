import Worm13a.Statement

/-!
# Probes of the statement `Worm.WormLowerM`

* `closedBall_cover`: the closed disk of radius `1` is a convex cover (translate the arc so that it starts at the centre;
  every point of a unit arc is within distance `1` of its start), so covers exist and the theorem is not vacuous;
  `optimalAreaM_lt_top`: the least area is finite.
* `unitArc_not_const`: constant curves are not unit arcs (length `0`).
-/

open Set MeasureTheory
open scoped ENNReal

namespace Worm

theorem trace_subset_closedBall {γ : ℝ → Plane} (hγ : IsUnitArc γ) : trace γ ⊆ Metric.closedBall (γ 0) 1 := by
  rintro _ ⟨s, hs, rfl⟩
  rw [Metric.mem_closedBall, dist_comm, dist_edist]
  have h := eVariationOn.edist_le γ (s := I01) (x := 0) (y := s) ⟨le_rfl, zero_le_one⟩ hs
  rw [show eVariationOn γ I01 = 1 from hγ.2] at h
  have hne : edist (γ 0) (γ s) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h
  exact (ENNReal.toReal_le_toReal hne ENNReal.one_ne_top).mpr h |>.trans (by simp)

theorem closedBall_cover : IsConvexCoverM (Metric.closedBall 0 1) := by
  refine ⟨convex_closedBall 0 1, fun γ hγ => ⟨0, -γ 0, ?_⟩⟩
  rintro _ ⟨z, hz, rfl⟩
  have h := trace_subset_closedBall hγ hz
  simp only [motion, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, Metric.mem_closedBall,
    dist_zero_right] at h ⊢
  rw [← sub_eq_add_neg, ← dist_eq_norm]
  exact h

theorem optimalAreaM_lt_top : optimalAreaM < ⊤ := by
  refine lt_of_le_of_lt (sInf_le ⟨_, closedBall_cover, rfl⟩) ?_
  exact measure_closedBall_lt_top

theorem unitArc_not_const (c : Plane) : ¬ IsUnitArc (fun _ => c) := by
  rintro ⟨-, h⟩
  rw [arcLength, eVariationOn.constant_on (by simp)] at h
  exact zero_ne_one h

end Worm
