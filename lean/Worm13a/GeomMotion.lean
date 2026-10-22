import Worm13a.Statement
import MoserWorm.Common.Isometry

/-!
# Proper rigid motions preserve area and convexity

`Worm.motion θ t z = e^{iθ} z + t` is an isometry of the plane (`motionIsom`), so it preserves Lebesgue measure
(Keller's `MoserWorm.volume_image_isometry`), and it is affine, so images and preimages of convex sets are convex.
-/

open MeasureTheory

noncomputable section

namespace Worm

lemma motion_dist (θ : ℝ) (t z w : Plane) : dist (motion θ t z) (motion θ t w) = dist z w := by
  simp only [motion, dist_eq_norm]
  rw [show Complex.exp (θ * Complex.I) * z + t - (Complex.exp (θ * Complex.I) * w + t) =
      Complex.exp (θ * Complex.I) * (z - w) by ring, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The inverse motion `z ↦ e^{-iθ} (z − t)`. -/
def motionInv (θ : ℝ) (t : Plane) (z : Plane) : Plane := Complex.exp ((-θ : ℝ) * Complex.I) * (z - t)

lemma exp_neg_mul_exp (θ : ℝ) :
    Complex.exp ((-θ : ℝ) * Complex.I) * Complex.exp (θ * Complex.I) = 1 := by
  rw [← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero

lemma motionInv_motion (θ : ℝ) (t z : Plane) : motionInv θ t (motion θ t z) = z := by
  simp only [motionInv, motion, add_sub_cancel_right, ← mul_assoc, exp_neg_mul_exp, one_mul]

lemma motion_motionInv (θ : ℝ) (t z : Plane) : motion θ t (motionInv θ t z) = z := by
  simp only [motionInv, motion, ← mul_assoc]
  rw [mul_comm (Complex.exp (θ * Complex.I)) (Complex.exp ((-θ : ℝ) * Complex.I)), exp_neg_mul_exp, one_mul,
    sub_add_cancel]

/-- The proper rigid motion `z ↦ e^{iθ} z + t` as an isometry equivalence of the plane. -/
def motionIsom (θ : ℝ) (t : Plane) : Plane ≃ᵢ Plane where
  toFun := motion θ t
  invFun := motionInv θ t
  left_inv := motionInv_motion θ t
  right_inv := motion_motionInv θ t
  isometry_toFun := Isometry.of_dist_eq (motion_dist θ t)

@[simp] lemma coe_motionIsom (θ : ℝ) (t : Plane) : ⇑(motionIsom θ t) = motion θ t := rfl

/-- **Proper rigid motions preserve area** (of arbitrary sets, as outer measure). -/
theorem volume_image_motion (θ : ℝ) (t : Plane) (S : Set Plane) : volume (motion θ t '' S) = volume S := by
  rw [← coe_motionIsom]; exact MoserWorm.volume_image_isometry _ S

/-- Preimage version. -/
theorem volume_preimage_motion (θ : ℝ) (t : Plane) (S : Set Plane) : volume (motion θ t ⁻¹' S) = volume S := by
  rw [← coe_motionIsom]; exact MoserWorm.volume_preimage_isometry _ S

/-- `motion θ t` maps affine combinations to affine combinations. -/
lemma motion_comb (θ : ℝ) (t x y : Plane) {a b : ℝ} (hab : a + b = 1) :
    motion θ t (a • x + b • y) = a • motion θ t x + b • motion θ t y := by
  simp only [motion, Complex.real_smul]
  have ht : t = (a : ℂ) * t + (b : ℂ) * t := by
    rw [← add_mul, ← Complex.ofReal_add, hab, Complex.ofReal_one, one_mul]
  conv_lhs => rw [ht]
  ring

/-- **The preimage of a convex set under a proper rigid motion is convex.** -/
theorem convex_preimage_motion (θ : ℝ) (t : Plane) {K : Set Plane} (hK : Convex ℝ K) :
    Convex ℝ (motion θ t ⁻¹' K) := by
  intro x hx y hy a b ha hb hab
  show motion θ t (a • x + b • y) ∈ K
  rw [motion_comb θ t x y hab]
  exact hK hx hy ha hb hab

/-- The image of a convex set under a proper rigid motion is convex. -/
theorem convex_image_motion (θ : ℝ) (t : Plane) {K : Set Plane} (hK : Convex ℝ K) :
    Convex ℝ (motion θ t '' K) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, hK hx hy ha hb hab, motion_comb θ t x y hab⟩

end Worm
