import Worm13a.GeomInterface

/-!
# The combination lemma for general lists

The interface lemmas bound `ENNReal.ofReal F ≤ volume K` for the shoelace value `F` of each valid list (`fan_le` for
fans, `small_le` for small lists, `chord_le` for chord trees). A nonnegative combination of such values with total
weight at most `1` obeys the same bound (`A ≥ max_i F_i ≥ ∑ λ_i F_i`). Sub-collections need no lemma: every
interface lemma holds for any convex `K` that contains the listed points.
-/

open MeasureTheory

namespace Worm.Geom

/-- **Combination**: if `ENNReal.ofReal (F i) ≤ volume K` for every `i ∈ s`, then the same holds for `∑ λᵢ Fᵢ` with weights
`λᵢ ≥ 0` of total at most `1`. The values `Fᵢ` may be negative. -/
theorem mixture_le (K : Set ℂ) {ι : Type*} (s : Finset ι) (w F : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsum : ∑ i ∈ s, w i ≤ 1) (hF : ∀ i ∈ s, ENNReal.ofReal (F i) ≤ volume K) :
    ENNReal.ofReal (∑ i ∈ s, w i * F i) ≤ volume K := by
  rcases eq_or_ne (volume K) ⊤ with htop | htop
  · rw [htop]; exact le_top
  set V := (volume K).toReal with hVdef
  have hV : volume K = ENNReal.ofReal V := (ENNReal.ofReal_toReal htop).symm
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hFV : ∀ i ∈ s, F i ≤ V := fun i hi => by
    have h := hF i hi
    rw [hV] at h
    exact (ENNReal.ofReal_le_ofReal_iff hV0).mp h
  rw [hV]
  apply ENNReal.ofReal_le_ofReal
  calc ∑ i ∈ s, w i * F i ≤ ∑ i ∈ s, w i * V :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hFV i hi) (hw i hi)
    _ = (∑ i ∈ s, w i) * V := by rw [Finset.sum_mul]
    _ ≤ 1 * V := mul_le_mul_of_nonneg_right hsum hV0
    _ = V := one_mul V

/-- The combination lemma for lists that are valid by chord trees. -/
theorem chord_mixture_le (K : Set ℂ) (hK : Convex ℝ K) {ι : Type*} (s : Finset ι) (w : ι → ℝ) (P : ι → List ℂ)
    (T : ι → CTree) (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i ≤ 1) (hP : ∀ i ∈ s, ∀ x ∈ P i, x ∈ K)
    (hT : ∀ i ∈ s, ChordOK (T i) (P i)) :
    ENNReal.ofReal (∑ i ∈ s, w i * shoelace (P i)) ≤ volume K :=
  mixture_le K s w (fun i => shoelace (P i)) hw hsum fun i hi => chord_le K hK (P i) (hP i hi) (T i) (hT i hi)

end Worm.Geom
