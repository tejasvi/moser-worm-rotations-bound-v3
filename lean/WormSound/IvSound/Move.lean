import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Movement bounds for placed points (the real-number side of the checker's error terms)

A point `q` of a body placed by the angle `θ` and the translation `t` is at `t + e^{iθ} q`. With
`det(a, b) = re a · im b − im a · re b`:

* `norm_rot_sub_le`, `norm_place_sub_le`: moving from the centre `(θ_c, t_c)` of a box to `(θ, t)` moves the point by at
  most `‖q‖ |θ − θ_c| + ‖t − t_c‖`;
* `abs_det_le`, `abs_det_sub_le`: `|det(a, b)| ≤ ‖a‖ ‖b‖`, and the perturbation bound
  `|det(u', v') − det(u, v)| ≤ ‖u' − u‖ (‖v‖ + ‖v' − v‖) + ‖u‖ ‖v' − v‖`;
* `det_rot`: rotations preserve `det`; `det_same_body`: for three points of one body, `det(x_b − x_a, x_i − x_a)` does
  not depend on the placement;
* `abs_det_fan_same_body_sub_le`: for two points of one body and a fixed point `z`,
  `det(x_a − z, x_b − z)` moves by at most `‖q_b − q_a‖ (‖t − t_c‖ + |θ − θ_c| ‖t_c − z‖)`.
-/

open Complex

namespace WormCore.Move

/-- `det(a, b) = re a · im b − im a · re b`. -/
def det (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

lemma det_eq_im (a b : ℂ) : det a b = (starRingEnd ℂ a * b).im := by
  simp [det, Complex.mul_im]; ring

lemma abs_det_le (a b : ℂ) : |det a b| ≤ ‖a‖ * ‖b‖ := by
  rw [det_eq_im]
  calc |(starRingEnd ℂ a * b).im| ≤ ‖starRingEnd ℂ a * b‖ := Complex.abs_im_le_norm _
    _ = ‖a‖ * ‖b‖ := by rw [norm_mul, Complex.norm_conj]

lemma det_sub_left (a a' b : ℂ) : det a' b - det a b = det (a' - a) b := by
  simp only [det, Complex.sub_re, Complex.sub_im]; ring

lemma det_sub_right (a b b' : ℂ) : det a b' - det a b = det a (b' - b) := by
  simp only [det, Complex.sub_re, Complex.sub_im]; ring

/-- Perturbation of `det`. -/
lemma abs_det_sub_le (u u' v v' : ℂ) :
    |det u' v' - det u v| ≤ ‖u' - u‖ * (‖v‖ + ‖v' - v‖) + ‖u‖ * ‖v' - v‖ := by
  have e : det u' v' - det u v = det (u' - u) v' + det u (v' - v) := by
    simp only [det, Complex.sub_re, Complex.sub_im]; ring
  have hv' : ‖v'‖ ≤ ‖v‖ + ‖v' - v‖ := by
    calc ‖v'‖ = ‖v + (v' - v)‖ := by ring_nf
      _ ≤ ‖v‖ + ‖v' - v‖ := norm_add_le _ _
  rw [e]
  calc |det (u' - u) v' + det u (v' - v)| ≤ |det (u' - u) v'| + |det u (v' - v)| := abs_add_le _ _
    _ ≤ ‖u' - u‖ * ‖v'‖ + ‖u‖ * ‖v' - v‖ := add_le_add (abs_det_le _ _) (abs_det_le _ _)
    _ ≤ ‖u' - u‖ * (‖v‖ + ‖v' - v‖) + ‖u‖ * ‖v' - v‖ := by
        gcongr

lemma norm_exp_mul_I (θ : ℝ) : ‖exp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

/-- Rotating a point by `θ` instead of `θ_c` moves it by at most `‖q‖ |θ − θ_c|`. -/
lemma norm_rot_sub_le (θ θc : ℝ) (q : ℂ) : ‖exp (θ * I) * q - exp (θc * I) * q‖ ≤ ‖q‖ * |θ - θc| := by
  have e : exp (θ * I) * q - exp (θc * I) * q = exp (θc * I) * (exp (I * ((θ - θc : ℝ) : ℂ)) - 1) * q := by
    rw [mul_sub, mul_one, ← exp_add]
    push_cast
    ring_nf
  rw [e, norm_mul, norm_mul, norm_exp_mul_I, one_mul, mul_comm]
  gcongr
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ - θc)
  rwa [Real.norm_eq_abs] at this

/-- Moving the placement from `(θ_c, t_c)` to `(θ, t)` moves `t + e^{iθ} q` by at most `‖q‖ |θ − θ_c| + ‖t − t_c‖`. -/
lemma norm_place_sub_le (θ θc : ℝ) (t tc q : ℂ) :
    ‖(t + exp (θ * I) * q) - (tc + exp (θc * I) * q)‖ ≤ ‖q‖ * |θ - θc| + ‖t - tc‖ := by
  have e : (t + exp (θ * I) * q) - (tc + exp (θc * I) * q) = (exp (θ * I) * q - exp (θc * I) * q) + (t - tc) := by
    ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (norm_rot_sub_le θ θc q) le_rfl)

/-- Rotations preserve `det`. -/
lemma det_rot (θ : ℝ) (a b : ℂ) : det (exp (θ * I) * a) (exp (θ * I) * b) = det a b := by
  simp only [det, Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have h := Real.sin_sq_add_cos_sq θ
  linear_combination (a.re * b.im - a.im * b.re) * h

/-- For three points of one body, `det(x_b − x_a, x_i − x_a)` does not depend on the placement. -/
lemma det_same_body (θ : ℝ) (t qa qb qi : ℂ) :
    det ((t + exp (θ * I) * qb) - (t + exp (θ * I) * qa)) ((t + exp (θ * I) * qi) - (t + exp (θ * I) * qa)) =
      det (qb - qa) (qi - qa) := by
  have e1 : (t + exp (θ * I) * qb) - (t + exp (θ * I) * qa) = exp (θ * I) * (qb - qa) := by ring
  have e2 : (t + exp (θ * I) * qi) - (t + exp (θ * I) * qa) = exp (θ * I) * (qi - qa) := by ring
  rw [e1, e2, det_rot]

/-- The difference of two points of one body is rotated by the body's angle. -/
lemma place_sub_same_body (θ : ℝ) (t qa qb : ℂ) :
    (t + exp (θ * I) * qb) - (t + exp (θ * I) * qa) = exp (θ * I) * (qb - qa) := by ring

/-- For two points of one body and a fixed point `z`, `det(x_a − z, x_b − z)` moves by at most
`‖q_b − q_a‖ (‖t − t_c‖ + |θ − θ_c| ‖t_c − z‖)`. -/
lemma abs_det_fan_same_body_sub_le (θ θc : ℝ) (t tc qa qb z : ℂ) :
    |det ((t + exp (θ * I) * qa) - z) ((t + exp (θ * I) * qb) - z) -
        det ((tc + exp (θc * I) * qa) - z) ((tc + exp (θc * I) * qb) - z)| ≤
      ‖qb - qa‖ * (‖t - tc‖ + |θ - θc| * ‖tc - z‖) := by
  -- `det(x_a − z, x_b − z) = det(e^{−iθ}(t − z) + q_a, q_b − q_a)`
  have key : ∀ (φ : ℝ) (s : ℂ), det ((s + exp (φ * I) * qa) - z) ((s + exp (φ * I) * qb) - z) =
      det (exp (-φ * I) * (s - z) + qa) (qb - qa) := by
    intro φ s
    have h1 : (s + exp (φ * I) * qa) - z = exp (φ * I) * (exp (-φ * I) * (s - z) + qa) := by
      rw [mul_add, ← mul_assoc, ← exp_add]
      simp only [neg_mul, add_neg_cancel, exp_zero, one_mul]
      ring
    have h2 : (s + exp (φ * I) * qb) - z =
        exp (φ * I) * (exp (-φ * I) * (s - z) + qa) + exp (φ * I) * (qb - qa) := by
      rw [← h1]; ring
    rw [h1, h2]
    have h3 : det (exp (φ * I) * (exp (-φ * I) * (s - z) + qa))
        (exp (φ * I) * (exp (-φ * I) * (s - z) + qa) + exp (φ * I) * (qb - qa)) =
        det (exp (φ * I) * (exp (-φ * I) * (s - z) + qa)) (exp (φ * I) * (qb - qa)) := by
      simp only [det, Complex.add_re, Complex.add_im]; ring
    rw [h3, det_rot]
  rw [key θ t, key θc tc, det_sub_left]
  refine (abs_det_le _ _).trans ?_
  rw [mul_comm]
  gcongr
  -- `‖e^{−iθ}(t − z) − e^{−iθ_c}(t_c − z)‖ ≤ ‖t − t_c‖ + |θ − θ_c| ‖t_c − z‖`
  have e : exp (-θ * I) * (t - z) + qa - (exp (-θc * I) * (tc - z) + qa) =
      exp (-θ * I) * (t - tc) + (exp (-θ * I) * (tc - z) - exp (-θc * I) * (tc - z)) := by ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    have : ‖exp (-θ * I)‖ = 1 := by
      have := norm_exp_mul_I (-θ); push_cast at this; exact this
    rw [this, one_mul]
  · have h := norm_rot_sub_le (-θ) (-θc) (tc - z)
    push_cast at h
    calc _ ≤ ‖tc - z‖ * |-θ - -θc| := h
      _ = |θ - θc| * ‖tc - z‖ := by rw [mul_comm, show -θ - -θc = -(θ - θc) by ring, abs_neg]

end WormCore.Move
