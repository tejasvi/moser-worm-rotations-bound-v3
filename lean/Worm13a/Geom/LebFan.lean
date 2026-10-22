import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.RingTheory.SimpleRing.Principal

/-
Copied from `LebesgueCover/Fan.lean` of the Lean development for Lebesgue's universal covering problem
(sha256 6035970c2de944ec..., 2026-10-21), for the fan lemma of the worm proof. Only change: `import Mathlib`
replaced by the import list printed by `#min_imports`.
-/

/-!
# The fan lemma (Lemma 3.1 of the paper), in the complex plane

Triangles `z + s A + t B` (`s, t ≥ 0`, `s + t ≤ 1`) have area `|det(A, B)|/2`. If points `x_j` of a convex set `K`
turn positively around `z ∈ K` with total angle `2π`, the triangles `conv{z, x_j, x_{j+1}}` meet in null sets, so
`area K ≥ (1/2) Σ det(x_j − z, x_{j+1} − z)`.
-/

open MeasureTheory Set Complex

namespace LebesgueCover

/-- `det(a, b) = Im(conj a · b)`. -/
def detC (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

/-- The triangle `{z + s A + t B : s, t ≥ 0, s + t ≤ 1}`. -/
def triC (z A B : ℂ) : Set ℂ := {y | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 ∧ y = z + s * A + t * B}

/-- The standard simplex `{w : 0 ≤ re w, 0 ≤ im w, re w + im w ≤ 1}`. -/
def simplexC : Set ℂ := {w | 0 ≤ w.re ∧ 0 ≤ w.im ∧ w.re + w.im ≤ 1}

/-- The real-linear map `w ↦ re w · A + im w · B`. -/
noncomputable def linAB (A B : ℂ) : ℂ →ₗ[ℝ] ℂ where
  toFun w := (w.re : ℂ) * A + (w.im : ℂ) * B
  map_add' u v := by simp only [add_re, add_im, ofReal_add]; ring
  map_smul' c u := by
    simp only [RingHom.id_apply, real_smul, re_ofReal_mul, im_ofReal_mul, ofReal_mul]; ring

lemma det_linAB (A B : ℂ) : LinearMap.det (linAB A B) = detC A B := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, linAB,
    LinearMap.coe_mk, AddHom.coe_mk]
  simp [detC]
  ring

lemma volume_simplexC : volume simplexC = ENNReal.ofReal (1 / 2) := by
  have hpre : simplexC = measurableEquivRealProd ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} := by
    ext w; simp [simplexC, measurableEquivRealProd]
  have hms : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} := by
    apply IsClosed.measurableSet
    simp only [Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  rw [hpre, volume_preserving_equiv_real_prod.measure_preimage hms.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_apply hms]
  have hsec : ∀ x : ℝ, volume (Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}) =
      (Icc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (1 - x)) x := by
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem hx]
      have : Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} = Icc 0 (1 - x) := by
        ext y; simp only [mem_preimage, mem_setOf_eq, mem_Icc]; constructor
        · rintro ⟨_, h2, h3⟩; exact ⟨h2, by linarith⟩
        · rintro ⟨h2, h3⟩; exact ⟨hx.1, h2, by linarith⟩
      rw [this, Real.volume_Icc, sub_zero]
    · rw [indicator_of_notMem hx]
      have : Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} = ∅ := by
        ext y; simp only [mem_preimage, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, h3⟩; exact hx ⟨h1, by linarith⟩
      rw [this, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator measurableSet_Icc]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
      integral_id, intervalIntegral.integral_const]
    norm_num
  · exact (continuous_const.sub continuous_id).integrableOn_Icc
  · exact ae_restrict_of_forall_mem measurableSet_Icc fun x hx => by
      simp only [Pi.zero_apply]; linarith [hx.2]

/-- **Area of a triangle.** -/
theorem volume_triC (z A B : ℂ) : volume (triC z A B) = ENNReal.ofReal (|detC A B| / 2) := by
  have himg : triC z A B = (fun w => z + w) '' (linAB A B '' simplexC) := by
    ext y; constructor
    · rintro ⟨s, t, hs, ht, hst, rfl⟩
      refine ⟨linAB A B (s + t * I), ⟨s + t * I, ⟨by simp [hs], by simp [ht], by simp [hst]⟩, rfl⟩, ?_⟩
      simp [linAB]; ring
    · rintro ⟨_, ⟨w, ⟨h1, h2, h3⟩, rfl⟩, rfl⟩
      exact ⟨w.re, w.im, h1, h2, h3, by simp [linAB]; ring⟩
  rw [himg, Set.image_add_left, measure_preimage_add, Measure.addHaar_image_linearMap, det_linAB,
    volume_simplexC, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1; ring

/-! ## Nonnegative combinations of two directions stay in the sector -/

/-- For `s, t ≥ 0`, `s + t > 0` and `θ ∈ (0, π)`: `s + t e^{iθ} = r e^{iψ}` with `r > 0` and `ψ ∈ [0, θ]`. -/
lemma comb_sector {s t θ : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : 0 < s + t) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    ∃ r ψ : ℝ, 0 < r ∧ 0 ≤ ψ ∧ ψ ≤ θ ∧ (s : ℂ) + t * exp (θ * I) = r * exp (ψ * I) := by
  set c := Real.cos (θ / 2) with hc
  set sn := Real.sin (θ / 2) with hsn
  have hc0 : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs0 : 0 < sn := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcs : c ^ 2 + sn ^ 2 = 1 := by rw [hc, hsn]; linarith [Real.cos_sq_add_sin_sq (θ / 2)]
  -- v = s e^{-iθ/2} + t e^{iθ/2}
  set v : ℂ := ((s + t) * c : ℝ) + ((t - s) * sn : ℝ) * I with hv
  have hvre : v.re = (s + t) * c := by simp [hv]
  have hvim : v.im = (t - s) * sn := by simp [hv]
  have hsplit : (s : ℂ) + t * exp (θ * I) = exp ((θ / 2 : ℝ) * I) * v := by
    have e1 : exp (θ * I) = exp ((θ / 2 : ℝ) * I) * exp ((θ / 2 : ℝ) * I) := by
      rw [← exp_add]; congr 1; push_cast; ring
    have e2 : exp ((θ / 2 : ℝ) * I) = (c : ℂ) + (sn : ℂ) * I := by
      rw [exp_mul_I, hc, hsn, ofReal_cos, ofReal_sin]
    rw [e1, e2, hv]
    push_cast
    apply Complex.ext <;> simp <;> nlinarith [hcs]
  have hvre0 : 0 < v.re := by rw [hvre]; positivity
  have hv0 : v ≠ 0 := fun h => by rw [h] at hvre0; simp at hvre0
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  -- |im v| ≤ ‖v‖ sin(θ/2)
  have hbound : |v.im / ‖v‖| ≤ sn := by
    rw [abs_div, abs_norm, div_le_iff₀ hnorm]
    have hn2 : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have key : v.im ^ 2 ≤ (sn * ‖v‖) ^ 2 := by
      rw [mul_pow, hn2, hvre, hvim]
      have : (t - s) ^ 2 ≤ (s + t) ^ 2 := by nlinarith
      nlinarith [sq_nonneg sn, sq_nonneg c, mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ c ^ 2 * sn ^ 2)]
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).mp (by rwa [sq_abs])
  have harg : v.arg = Real.arcsin (v.im / ‖v‖) := Complex.arg_of_re_nonneg hvre0.le
  have hθ2 : θ / 2 ≤ Real.pi / 2 := by linarith
  have hlo : -(θ / 2) ≤ v.arg := by
    rw [harg]
    have h1 : -sn ≤ v.im / ‖v‖ := by linarith [neg_abs_le (v.im / ‖v‖)]
    have h2 := Real.arcsin_le_arcsin h1
    rwa [Real.arcsin_neg, Real.arcsin_sin (by linarith) hθ2] at h2
  have hhi : v.arg ≤ θ / 2 := by
    rw [harg]
    have h1 : v.im / ‖v‖ ≤ sn := le_trans (le_abs_self _) hbound
    have h2 := Real.arcsin_le_arcsin h1
    rwa [Real.arcsin_sin (by linarith) hθ2] at h2
  refine ⟨‖v‖, θ / 2 + v.arg, hnorm, by linarith, by linarith, ?_⟩
  rw [hsplit]
  conv_lhs => rw [← norm_mul_exp_arg_mul_I v]
  rw [show ((θ / 2 + v.arg : ℝ) : ℂ) * I = ((θ / 2 : ℝ) : ℂ) * I + (v.arg : ℂ) * I by push_cast; ring, exp_add]
  ring

/-! ## Lines are null; triangles are compact -/

lemma volume_line (z v : ℂ) (hv : v ≠ 0) : volume {y : ℂ | ∃ c : ℝ, y = z + c * v} = 0 := by
  -- the line lies in z + ker φ, φ(w) = det(v, w), a proper submodule
  let φ : ℂ →ₗ[ℝ] ℝ :=
    { toFun := fun w => detC v w
      map_add' := fun u w => by simp only [detC, add_re, add_im]; ring
      map_smul' := fun c u => by simp only [detC, smul_re, smul_im, smul_eq_mul, RingHom.id_apply]; ring }
  have hker : LinearMap.ker φ ≠ ⊤ := by
    intro h
    have : I * v ∈ LinearMap.ker φ := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at this
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, detC, mul_re, mul_im, I_re, I_im] at this
    have h2 : v.re ^ 2 + v.im ^ 2 = 0 := by nlinarith
    apply hv; apply Complex.ext <;> simp <;> nlinarith [sq_nonneg v.re, sq_nonneg v.im]
  have h0 : volume ((LinearMap.ker φ : Set ℂ)) = 0 := Measure.addHaar_submodule volume _ hker
  apply measure_mono_null (t := (fun w => z + w) '' (LinearMap.ker φ : Set ℂ))
  · rintro y ⟨c, rfl⟩
    refine ⟨c * v, ?_, rfl⟩
    show φ (c * v) = 0
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, detC, re_ofReal_mul, im_ofReal_mul]; ring
  · rw [Set.image_add_left, measure_preimage_add]; exact h0

lemma isCompact_simplexC : IsCompact simplexC := by
  apply Metric.isCompact_of_isClosed_isBounded
  · simp only [simplexC, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_re).inter ((isClosed_le continuous_const continuous_im).inter
      (isClosed_le (continuous_re.add continuous_im) continuous_const))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun w ⟨h1, h2, h3⟩ => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ 2 := by rw [abs_of_nonneg h1, abs_of_nonneg h2]; linarith

lemma measurableSet_triC (z A B : ℂ) : MeasurableSet (triC z A B) := by
  have himg : triC z A B = (fun w => z + linAB A B w) '' simplexC := by
    ext y; constructor
    · rintro ⟨s, t, hs, ht, hst, rfl⟩
      exact ⟨s + t * I, ⟨by simp [hs], by simp [ht], by simp [hst]⟩, by simp [linAB]; ring⟩
    · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
      exact ⟨w.re, w.im, h1, h2, h3, by simp [linAB]; ring⟩
  rw [himg]
  exact (isCompact_simplexC.image (continuous_const.add (linAB A B).continuous_of_finiteDimensional)).isClosed.measurableSet

/-! ## Cumulative angles -/

/-- Index after `j` modulo `m`. -/
def nxt (m j : ℕ) : ℕ := (j + 1) % m

/-- The turning angle at `j`. -/
noncomputable def turn (a : ℕ → ℂ) (m j : ℕ) : ℝ := arg (a (nxt m j) / a j)

/-- The cumulative angle before `j`. -/
noncomputable def cum (a : ℕ → ℂ) (m j : ℕ) : ℝ := arg (a 0) + ∑ l ∈ Finset.range j, turn a m l

lemma turn_mem {a b : ℂ} (ha : a ≠ 0) (hdet : 0 < detC a b) : 0 < arg (b / a) ∧ arg (b / a) < Real.pi := by
  have hn : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
  have him : 0 < (b / a).im := by
    have e : (b / a).im = detC a b / Complex.normSq a := by
      rw [div_im]; simp only [detC]; field_simp
    rw [e]; exact div_pos hdet hn
  refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr him.le) ?_, Complex.arg_lt_pi_iff.mpr (Or.inr him.ne')⟩
  intro h
  have := (Complex.arg_eq_zero_iff.mp h.symm).2
  linarith

variable {a : ℕ → ℂ} {m : ℕ}

lemma cum_succ (j : ℕ) : cum a m (j + 1) = cum a m j + turn a m j := by
  simp [cum, Finset.sum_range_succ]; ring

/-- Polar form along the cycle: `a (j mod m) = ‖a (j mod m)‖ e^{i Φ_j}` for `j ≤ m`. -/
lemma polar_cum (hm : 0 < m) (ha : ∀ j < m, a j ≠ 0) :
    ∀ j ≤ m, a (j % m) = (‖a (j % m)‖ : ℂ) * exp (cum a m j * I) := by
  intro j hj
  induction j with
  | zero =>
    simp only [Nat.zero_mod, cum, Finset.range_zero, Finset.sum_empty, add_zero]
    exact (norm_mul_exp_arg_mul_I (a 0)).symm
  | succ j ih =>
    have hjm : j < m := by omega
    have ih' := ih (by omega)
    rw [Nat.mod_eq_of_lt hjm] at ih'
    have hne : a j ≠ 0 := ha j hjm
    set r := a (nxt m j) / a j with hr
    have e1 : a ((j + 1) % m) = a j * r := by simp only [hr, nxt]; field_simp
    have hpolar := norm_mul_exp_arg_mul_I r
    have hnorm : ‖a ((j + 1) % m)‖ = ‖a j‖ * ‖r‖ := by rw [e1, norm_mul]
    have h2 : a j * r = ((‖a j‖ : ℂ) * exp ((cum a m j : ℂ) * I)) * ((‖r‖ : ℂ) * exp ((arg r : ℂ) * I)) := by
      rw [← ih', hpolar]
    rw [hnorm, cum_succ]
    conv_lhs => rw [e1, h2]
    simp only [turn, ← hr]
    push_cast
    rw [show ((cum a m j : ℂ) + (arg r : ℂ)) * I = (cum a m j : ℂ) * I + (arg r : ℂ) * I by ring, exp_add]
    ring

lemma cum_mono (hdet : ∀ j < m, 0 < detC (a j) (a (nxt m j))) (ha : ∀ j < m, a j ≠ 0) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ m) : cum a m i ≤ cum a m j := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · have h1 := ih (by omega) (by omega)
      rw [cum_succ]
      have := (turn_mem (ha j (by omega)) (hdet j (by omega))).1
      simp only [turn] at *
      linarith
    · have : i = j + 1 := by omega
      subst this; exact le_refl _

/-- Points of the `j`-th triangle other than `z` lie in the sector `[Φ_j, Φ_{j+1}]`. -/
lemma tri_sector (hm : 0 < m) (ha : ∀ j < m, a j ≠ 0) (hdet : ∀ j < m, 0 < detC (a j) (a (nxt m j)))
    {j : ℕ} (hj : j < m) {z y : ℂ} (hy : y ∈ triC z (a j) (a (nxt m j))) (hyz : y ≠ z) :
    ∃ r ψ : ℝ, 0 < r ∧ cum a m j ≤ ψ ∧ ψ ≤ cum a m (j + 1) ∧ y - z = r * exp (ψ * I) := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hy
  have hpj := polar_cum hm ha j hj.le
  rw [Nat.mod_eq_of_lt hj] at hpj
  have hpj1 := polar_cum hm ha (j + 1) hj
  have hnxt : nxt m j = (j + 1) % m := rfl
  rw [← hnxt] at hpj1
  obtain ⟨hθ0, hθ⟩ := turn_mem (ha j hj) (hdet j hj)
  set θ := arg (a (nxt m j) / a j)
  have hnj : 0 < ‖a j‖ := norm_pos_iff.mpr (ha j hj)
  have hnn : 0 < ‖a (nxt m j)‖ := norm_pos_iff.mpr (ha _ (Nat.mod_lt _ hm))
  have hpos : 0 < s * ‖a j‖ + t * ‖a (nxt m j)‖ := by
    rcases (mul_nonneg hs hnj.le).eq_or_lt with h1 | h1
    · rcases (mul_nonneg ht hnn.le).eq_or_lt with h2 | h2
      · exfalso; apply hyz
        have hs0 : s = 0 := by
          rcases mul_eq_zero.mp h1.symm with h | h
          · exact h
          · exact absurd h hnj.ne'
        have ht0 : t = 0 := by
          rcases mul_eq_zero.mp h2.symm with h | h
          · exact h
          · exact absurd h hnn.ne'
        simp [hs0, ht0]
      · linarith
    · linarith [mul_nonneg ht hnn.le]
  obtain ⟨r, ψ', hr, hψ0, hψ1, heq⟩ := comb_sector (mul_nonneg hs hnj.le) (mul_nonneg ht hnn.le) hpos hθ0 hθ
  refine ⟨r, cum a m j + ψ', hr, by linarith, ?_, ?_⟩
  · rw [cum_succ]; simp only [turn]; linarith
  · have hc1 : cum a m (j + 1) = cum a m j + θ := by rw [cum_succ]; rfl
    rw [hc1] at hpj1
    have : z + s * a j + t * a (nxt m j) - z =
        exp ((cum a m j : ℂ) * I) * ((s * ‖a j‖ : ℝ) + (t * ‖a (nxt m j)‖ : ℝ) * exp ((θ : ℂ) * I)) := by
      conv_lhs => rw [hpj, hpj1]
      push_cast
      rw [show ((cum a m j : ℂ) + (θ : ℂ)) * I = (cum a m j : ℂ) * I + (θ : ℂ) * I by ring, exp_add]
      ring
    rw [this, heq]
    push_cast
    rw [show ((cum a m j : ℂ) + (ψ' : ℂ)) * I = (cum a m j : ℂ) * I + (ψ' : ℂ) * I by ring, exp_add]
    ring

lemma norm_real_mul_exp {r ψ : ℝ} (hr : 0 < r) : ‖(r : ℂ) * exp (ψ * I)‖ = r := by
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

lemma line_of_polar {A : ℂ} {r φ : ℝ} (hA : A ≠ 0) (hpA : A = (‖A‖ : ℂ) * exp (φ * I)) :
    (r : ℂ) * exp (φ * I) = ((r / ‖A‖ : ℝ) : ℂ) * A := by
  have hn : (‖A‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hA)
  calc (r : ℂ) * exp (φ * I) = ((r / ‖A‖ : ℝ) : ℂ) * ((‖A‖ : ℂ) * exp (φ * I)) := by
        push_cast; field_simp
    _ = ((r / ‖A‖ : ℝ) : ℂ) * A := by rw [← hpA]

/-- **Two triangles of the fan meet only on lines through `z`.** -/
lemma tri_inter_sub (hm : 0 < m) (ha : ∀ j < m, a j ≠ 0) (hdet : ∀ j < m, 0 < detC (a j) (a (nxt m j)))
    (hwind : cum a m m = cum a m 0 + 2 * Real.pi) {j k : ℕ} (hjk : j < k) (hk : k < m) (z : ℂ) :
    triC z (a j) (a (nxt m j)) ∩ triC z (a k) (a (nxt m k)) ⊆
      {z} ∪ ({y | ∃ c : ℝ, y = z + c * a k} ∪ {y | ∃ c : ℝ, y = z + c * a 0}) := by
  rintro y ⟨hyj, hyk⟩
  by_cases hyz : y = z
  · exact Or.inl hyz
  right
  obtain ⟨r, ψ, hr, hψ1, hψ2, hy1⟩ := tri_sector hm ha hdet (hjk.trans hk) hyj hyz
  obtain ⟨r', ψ', hr', hψ1', hψ2', hy2⟩ := tri_sector hm ha hdet hk hyk hyz
  have hrr : r = r' := by
    have := congrArg norm (hy1.symm.trans hy2)
    rwa [norm_real_mul_exp hr, norm_real_mul_exp hr'] at this
  subst hrr
  have hexp : exp (ψ' * I) = exp (ψ * I) := by
    have h := hy1.symm.trans hy2
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    exact (mul_left_cancel₀ hr0 h).symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hψn : ψ' = ψ + n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simp at this
    linarith
  have h1 : cum a m (j + 1) ≤ cum a m k := cum_mono hdet ha (by omega) (by omega)
  have h2 : cum a m (k + 1) ≤ cum a m m := cum_mono hdet ha (by omega) le_rfl
  have h3 : cum a m 0 ≤ cum a m j := cum_mono hdet ha (by omega) (by omega)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlo : (0 : ℝ) ≤ n * (2 * Real.pi) := by linarith
  have hhi : (n : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi := by linarith
  have hn0 : (0 : ℤ) ≤ n := by
    have : (0 : ℝ) ≤ n := by
      by_contra hc; push Not at hc; nlinarith
    exact_mod_cast this
  have hn1 : n ≤ 1 := by
    have : (n : ℝ) ≤ 1 := by
      by_contra hc; push Not at hc; nlinarith
    exact_mod_cast this
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · -- same angle: `ψ' = Φ_k`, so `y` lies on the ray through `a k`
    norm_num at hψn
    have hψk : ψ' = cum a m k := le_antisymm (by linarith) hψ1'
    have hpk := polar_cum hm ha k hk.le
    rw [Nat.mod_eq_of_lt hk] at hpk
    have hyz' : y = z + (r : ℂ) * exp (ψ' * I) := by rw [← hy2]; ring
    refine Or.inl ⟨r / ‖a k‖, ?_⟩
    rw [hyz', hψk, line_of_polar (ha k hk) hpk]
  · -- angles differ by `2π`: `ψ = Φ_0`, so `y` lies on the ray through `a 0`
    norm_num at hψn
    have hψ0 : ψ = cum a m 0 := le_antisymm (by linarith) (by linarith)
    have hp0 := polar_cum hm ha 0 (Nat.zero_le _)
    simp only [Nat.zero_mod] at hp0
    have hyz' : y = z + (r : ℂ) * exp (ψ * I) := by rw [← hy1]; ring
    refine Or.inr ⟨r / ‖a 0‖, ?_⟩
    rw [hyz', hψ0, line_of_polar (ha 0 hm) hp0]

/-! ## The fan inequality -/

/-- A triangle with vertices in a convex set lies in it. -/
lemma triC_subset {K : Set ℂ} (hK : Convex ℝ K) {z A B : ℂ} (hz : z ∈ K) (hA : z + A ∈ K) (hB : z + B ∈ K) :
    triC z A B ⊆ K := by
  rintro y ⟨s, t, hs, ht, hst, rfl⟩
  rcases eq_or_lt_of_le (add_nonneg hs ht) with h0 | hpos
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    subst hs0; subst ht0; simpa using hz
  · have hw : (s / (s + t)) • (z + A) + (t / (s + t)) • (z + B) ∈ K :=
      hK hA hB (div_nonneg hs hpos.le) (div_nonneg ht hpos.le) (by field_simp)
    have h2 := hK hz hw (a := 1 - (s + t)) (b := s + t) (by linarith) hpos.le (by ring)
    convert h2 using 1
    have hst0 : (s : ℂ) + t ≠ 0 := by exact_mod_cast hpos.ne'
    simp only [Complex.real_smul]
    push_cast
    field_simp
    ring

/-- **The fan lemma.** If `z + a_j ∈ K` (convex, `z ∈ K`) turn positively around `z` with total angle `2π`, then
`area K ≥ (1/2) Σ det(a_j, a_{j+1})`. -/
theorem fan_area_le {K : Set ℂ} (hK : Convex ℝ K) (hm : 0 < m) {z : ℂ} (hz : z ∈ K)
    (hx : ∀ j < m, z + a j ∈ K) (ha : ∀ j < m, a j ≠ 0) (hdet : ∀ j < m, 0 < detC (a j) (a (nxt m j)))
    (hwind : cum a m m = cum a m 0 + 2 * Real.pi) :
    ENNReal.ofReal (∑ j ∈ Finset.range m, detC (a j) (a (nxt m j)) / 2) ≤ volume K := by
  have hnx : ∀ j, nxt m j < m := fun j => Nat.mod_lt _ hm
  have hT : ∀ j ∈ Finset.range m, triC z (a j) (a (nxt m j)) ⊆ K := fun j hj =>
    triC_subset hK hz (hx j (Finset.mem_range.mp hj)) (hx _ (hnx j))
  have hnull : ∀ j k, j < k → k < m →
      volume (triC z (a j) (a (nxt m j)) ∩ triC z (a k) (a (nxt m k))) = 0 := by
    intro j k hjk hk
    apply measure_mono_null (tri_inter_sub hm ha hdet hwind hjk hk z)
    apply measure_union_null (measure_singleton z)
    exact measure_union_null (volume_line z (a k) (ha k hk)) (volume_line z (a 0) (ha 0 hm))
  have hdisj : (↑(Finset.range m) : Set ℕ).Pairwise
      (Function.onFun (AEDisjoint volume) fun j => triC z (a j) (a (nxt m j))) := by
    intro j hj k hk hjk
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact hnull j k h hk
    · show volume (_ ∩ _) = 0
      rw [Set.inter_comm]; exact hnull k j h hj
  have hU := measure_biUnion_finset₀ hdisj
    (fun j _ => (measurableSet_triC z (a j) (a (nxt m j))).nullMeasurableSet)
  calc ENNReal.ofReal (∑ j ∈ Finset.range m, detC (a j) (a (nxt m j)) / 2)
      = ∑ j ∈ Finset.range m, ENNReal.ofReal (detC (a j) (a (nxt m j)) / 2) :=
        ENNReal.ofReal_sum_of_nonneg fun j hj => (div_pos (hdet j (Finset.mem_range.mp hj)) two_pos).le
    _ = ∑ j ∈ Finset.range m, volume (triC z (a j) (a (nxt m j))) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [volume_triC, abs_of_pos (hdet j (Finset.mem_range.mp hj))]
    _ = volume (⋃ j ∈ Finset.range m, triC z (a j) (a (nxt m j))) := hU.symm
    _ ≤ volume K := measure_mono (Set.iUnion₂_subset hT)

/-! ## Winding -/

/-- `dot(a, b) = Re(conj a · b)`. -/
def dotC (a b : ℂ) : ℝ := a.re * b.re + a.im * b.im

lemma div_re_eq (a b : ℂ) : (b / a).re = dotC a b / Complex.normSq a := by
  rw [div_re]; simp only [dotC]; ring

lemma div_im_eq (a b : ℂ) : (b / a).im = detC a b / Complex.normSq a := by
  rw [div_im]; simp only [detC]; ring

lemma ne_zero_of_detC_pos {a b : ℂ} (h : 0 < detC a b) : a ≠ 0 := by
  rintro rfl; simp [detC] at h

/-- The total turning `Σ_{j<m} arg(a_{j+1}/a_j)`. -/
noncomputable def turnSum (a : ℕ → ℂ) (m : ℕ) : ℝ := ∑ j ∈ Finset.range m, turn a m j

lemma cum_m_eq : cum a m m = cum a m 0 + turnSum a m := by
  simp [cum, turnSum]

lemma turnSum_int (hm : 0 < m) (ha : ∀ j < m, a j ≠ 0) : ∃ n : ℤ, turnSum a m = n * (2 * Real.pi) := by
  have h1 := polar_cum hm ha m le_rfl
  have h0 := polar_cum hm ha 0 (Nat.zero_le _)
  rw [Nat.mod_self] at h1
  rw [Nat.zero_mod] at h0
  have hn : (‖a 0‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (ha 0 hm)
  have hexp : exp (cum a m m * I) = exp (cum a m 0 * I) := mul_left_cancel₀ hn (h1.symm.trans h0)
  obtain ⟨n, hn'⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn'
  simp at this
  have e := cum_m_eq (a := a) (m := m)
  linarith

lemma turnSum_pos (hm : 0 < m) (hdet : ∀ j < m, 0 < detC (a j) (a (nxt m j))) : 0 < turnSum a m := by
  unfold turnSum
  apply Finset.sum_pos
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    exact (turn_mem (ne_zero_of_detC_pos (hdet j hj')) (hdet j hj')).1
  · exact ⟨0, Finset.mem_range.mpr hm⟩

/-- Positive turns with total `< 4π` turn exactly once. -/
lemma turnSum_eq_two_pi (hm : 0 < m) (hdet : ∀ j < m, 0 < detC (a j) (a (nxt m j)))
    (h4 : turnSum a m < 4 * Real.pi) : turnSum a m = 2 * Real.pi := by
  have ha : ∀ j < m, a j ≠ 0 := fun j hj => ne_zero_of_detC_pos (hdet j hj)
  obtain ⟨n, hn⟩ := turnSum_int hm ha
  have hpos := turnSum_pos hm hdet
  have hpi := Real.pi_pos
  have h1 : (0 : ℝ) < n := by
    by_contra hc; push Not at hc; nlinarith
  have h2 : (n : ℝ) < 2 := by
    by_contra hc; push Not at hc; nlinarith
  have : n = 1 := by
    have h1' : 0 < n := by exact_mod_cast h1
    have h2' : n < 2 := by exact_mod_cast h2
    omega
  subst this; rw [hn]; push_cast; ring

/-- On the upper half plane, `arg w = π/2 − arctan(Re w / Im w)`. -/
lemma arg_eq_pi_div_two_sub_arctan {w : ℂ} (hw : 0 < w.im) :
    arg w = Real.pi / 2 - Real.arctan (w.re / w.im) := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hpos : 0 < arg w := by
    have hs : 0 < Real.sin (arg w) := by rw [Complex.sin_arg]; exact div_pos hw (norm_pos_iff.mpr hw0)
    rcases (Complex.arg_nonneg_iff.mpr hw.le).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.sin_zero] at hs; exact absurd hs (lt_irrefl 0)
  have hlt : arg w < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hw.ne')
  have key : Real.tan (Real.pi / 2 - arg w) = w.re / w.im := by
    rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, Complex.sin_arg, Complex.cos_arg hw0, inv_div]
    have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    field_simp
  have := Real.arctan_tan (x := Real.pi / 2 - arg w) (by linarith) (by linarith)
  rw [key] at this
  linarith

/-- Real form of the angle bound of the checker: `min(det/dot, π⁺/2)` if `dot > 0`, else
`min(π⁺, π⁺/2 − dot/det)`, with `π⁺ = 3.1416`. -/
noncomputable def angleUBR (d e : ℝ) : ℝ :=
  if 0 < d then min (e / d) (31416 / 20000) else min (31416 / 10000) (31416 / 20000 - d / e)

/-- **The angle bound.** If `det(P, Q) > 0`, the angle from `P` to `Q` is at most `angleUBR(dot, det)`. -/
lemma arg_div_le_angleUBR {P Q : ℂ} (hP : P ≠ 0) (hdet : 0 < detC P Q) :
    arg (Q / P) ≤ angleUBR (dotC P Q) (detC P Q) := by
  have hN : 0 < Complex.normSq P := Complex.normSq_pos.mpr hP
  have him : 0 < (Q / P).im := by rw [div_im_eq]; exact div_pos hdet hN
  have hratio : (Q / P).re / (Q / P).im = dotC P Q / detC P Q := by
    rw [div_re_eq, div_im_eq]; field_simp
  rw [arg_eq_pi_div_two_sub_arctan him, hratio]
  have hpi4 := Real.pi_lt_d4
  unfold angleUBR
  split_ifs with hd
  · have hr : 0 < dotC P Q / detC P Q := div_pos hd hdet
    have e : Real.pi / 2 - Real.arctan (dotC P Q / detC P Q) = Real.arctan (detC P Q / dotC P Q) := by
      rw [← Real.arctan_inv_of_pos hr, inv_div]
    rw [e]
    refine le_min (Real.arctan_le_self (div_pos hdet hd).le) ?_
    have := Real.arctan_lt_pi_div_two (detC P Q / dotC P Q)
    norm_num at hpi4 ⊢; linarith
  · push Not at hd
    have hr : dotC P Q / detC P Q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hd hdet.le
    refine le_min ?_ ?_
    · have := Real.neg_pi_div_two_lt_arctan (dotC P Q / detC P Q)
      norm_num at hpi4 ⊢; linarith
    · have h1 := Real.arctan_le_self (neg_nonneg.mpr hr)
      rw [Real.arctan_neg] at h1
      norm_num at hpi4 ⊢; linarith

/-- The straight homotopy `(1 − t) b + t c`. -/
noncomputable def homC (b c : ℕ → ℂ) (t : ℝ) (j : ℕ) : ℂ := ((1 - t : ℝ) : ℂ) * b j + (t : ℂ) * c j

lemma homC_zero (b c : ℕ → ℂ) : homC b c 0 = b := by funext j; simp [homC]
lemma homC_one (b c : ℕ → ℂ) : homC b c 1 = c := by funext j; simp [homC]

/-- **Winding along a homotopy.** If every turn of the straight homotopy from `b` to `c` stays positive and the
total turning of `b` is `< 4π`, then `c` turns exactly once. -/
theorem wind_homotopy (hm : 0 < m) (b c : ℕ → ℂ)
    (hdet : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ j < m, 0 < detC (homC b c t j) (homC b c t (nxt m j)))
    (h0 : turnSum b m < 4 * Real.pi) : turnSum c m = 2 * Real.pi := by
  set f : ℝ → ℝ := fun t => turnSum (homC b c t) m with hf
  have hint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ n : ℤ, f t = n * (2 * Real.pi) := fun t ht =>
    turnSum_int hm (fun j hj => ne_zero_of_detC_pos (hdet t ht j hj))
  have hf0 : f 0 = 2 * Real.pi := by
    have hd0 := hdet 0 ⟨le_rfl, zero_le_one⟩
    rw [homC_zero] at hd0
    have := turnSum_eq_two_pi hm hd0 h0
    simp only [hf, homC_zero]; exact this
  have hcont : ContinuousOn f (Set.Icc 0 1) := by
    show ContinuousOn (fun t => ∑ j ∈ Finset.range m, turn (homC b c t) m j) _
    apply continuousOn_finset_sum
    intro j hj t ht
    have hj' := Finset.mem_range.mp hj
    apply ContinuousAt.continuousWithinAt
    have hd := hdet t ht j hj'
    have hne : homC b c t j ≠ 0 := ne_zero_of_detC_pos hd
    have hslit : homC b c t (nxt m j) / homC b c t j ∈ slitPlane := by
      rw [mem_slitPlane_iff]; right
      rw [div_im_eq]; exact (div_pos hd (Complex.normSq_pos.mpr hne)).ne'
    have hc1 : ∀ i, Continuous fun t : ℝ => homC b c t i := fun i => by
      unfold homC
      exact ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul continuous_const).add
        (Complex.continuous_ofReal.mul continuous_const)
    have hq : ContinuousAt (fun t => homC b c t (nxt m j) / homC b c t j) t :=
      ((hc1 (nxt m j)).continuousAt).div (hc1 j).continuousAt hne
    show ContinuousAt (fun t => arg (homC b c t (nxt m j) / homC b c t j)) t
    exact ContinuousAt.comp (x := t) (f := fun t => homC b c t (nxt m j) / homC b c t j)
      (continuousAt_arg hslit) hq
  have hpi := Real.pi_pos
  obtain ⟨n, hn⟩ := hint 1 ⟨zero_le_one, le_rfl⟩
  have hpos1 : 0 < f 1 := turnSum_pos hm (hdet 1 ⟨zero_le_one, le_rfl⟩)
  have hn1 : (1 : ℤ) ≤ n := by
    have : (0 : ℝ) < n := by by_contra hc; push Not at hc; nlinarith
    have : (0 : ℤ) < n := by exact_mod_cast this
    omega
  have hn_eq : n = 1 := by
    by_contra hne1
    have hn2 : (2 : ℤ) ≤ n := by omega
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have h3 : 3 * Real.pi ∈ Set.Icc (f 0) (f 1) := by
      rw [hf0, hn]; constructor <;> nlinarith
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc zero_le_one hcont h3
    obtain ⟨n', hn'⟩ := hint t ht
    have h := hft.symm.trans hn'
    have hz : ((2 * n' : ℝ) - 3) * Real.pi = 0 := by linarith
    rcases mul_eq_zero.mp hz with h' | h'
    · have : (2 * n' : ℝ) = 3 := by linarith
      have : (2 * n' : ℤ) = 3 := by exact_mod_cast this
      omega
    · exact absurd h' hpi.ne'
  have e : f 1 = turnSum c m := by simp only [hf, homC_one]
  rw [← e, hn, hn_eq]; push_cast; ring

end LebesgueCover
