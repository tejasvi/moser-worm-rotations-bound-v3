import Worm13a.GeomInterface

/-!
# Reduction to the root box: translation bounds from the chord bound

The centred equilateral triangle `vT` of side `1/2` (body `T`) has extent at least `√3/4` in every direction
(`tri_width`; the inequality `tri_width_ineq` is adapted from Keller's `MoserWorm.LowerBound.Domain`,
Apache-2.0). With Keller's four-point bound (`Worm.Geom.quad_le`) this bounds every chord of a convex set of area
below `τ` that contains a placed copy of `vT` (`chord_lt`), and with the triangle bound every point of such a set that
also contains `±1/2` has `|Re z| < 8τ/√3 - 1/2` and `|Im z| < 2τ`.
-/

open MeasureTheory

noncomputable section

namespace WormCore.Sound.W1Proof

open Worm Worm.Geom

/-- The centred vertices of the equilateral triangle `T` of side `1/2`. -/
def vT : List ℂ := [⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩, ⟨0, Real.sqrt 3 / 6⟩, ⟨1 / 4, -(Real.sqrt 3 / 12)⟩]

lemma tri_width_ineq (x y n : ℝ) (hn : 0 ≤ n) (hnorm : n ^ 2 = x ^ 2 + y ^ 2) :
    Real.sqrt 3 * n ≤ 2 * |y| ∨ Real.sqrt 3 * n ≤ |Real.sqrt 3 * x - y| ∨
      Real.sqrt 3 * n ≤ |Real.sqrt 3 * x + y| := by
  have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsx : (Real.sqrt 3 * |x|) ^ 2 = 3 * x ^ 2 := by rw [mul_pow, hs2, sq_abs]
  by_cases hy : Real.sqrt 3 * n ≤ 2 * |y|
  · exact Or.inl hy
  have hxy : |y| ≤ Real.sqrt 3 * |x| := by
    apply (sq_le_sq₀ (abs_nonneg y) (by positivity)).1
    have hysq : (2 * |y|) ^ 2 ≤ (Real.sqrt 3 * n) ^ 2 :=
      (sq_le_sq₀ (by positivity) (mul_nonneg hs hn)).2 (le_of_not_ge hy)
    rw [hsx, sq_abs]
    rw [mul_pow, mul_pow, hs2, sq_abs] at hysq
    nlinarith
  have hsum : Real.sqrt 3 * n ≤ Real.sqrt 3 * |x| + |y| := by
    apply (sq_le_sq₀ (mul_nonneg hs hn) (by positivity)).1
    have hp := mul_nonneg (abs_nonneg y) (sub_nonneg.2 hxy)
    have h3 : (Real.sqrt 3 * n) ^ 2 = 3 * n ^ 2 := by rw [mul_pow, hs2]
    nlinarith [sq_abs y, sq_abs x]
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy' | hy'
  · right; right
    calc Real.sqrt 3 * n ≤ Real.sqrt 3 * |x| + |y| := hsum
      _ = Real.sqrt 3 * x + y := by rw [abs_of_nonneg hx, abs_of_nonneg hy']
      _ ≤ |Real.sqrt 3 * x + y| := le_abs_self _
  · right; left
    calc Real.sqrt 3 * n ≤ Real.sqrt 3 * |x| + |y| := hsum
      _ = Real.sqrt 3 * x - y := by rw [abs_of_nonneg hx, abs_of_nonpos hy']; ring
      _ ≤ |Real.sqrt 3 * x - y| := le_abs_self _
  · right; left
    calc Real.sqrt 3 * n ≤ Real.sqrt 3 * |x| + |y| := hsum
      _ = -(Real.sqrt 3 * x - y) := by rw [abs_of_nonpos hx, abs_of_nonneg hy']; ring
      _ ≤ |Real.sqrt 3 * x - y| := neg_le_abs _
  · right; right
    calc Real.sqrt 3 * n ≤ Real.sqrt 3 * |x| + |y| := hsum
      _ = -(Real.sqrt 3 * x + y) := by rw [abs_of_nonpos hx, abs_of_nonpos hy']; ring
      _ ≤ |Real.sqrt 3 * x + y| := neg_le_abs _

/-- A pair of vertices with `|cross u (v - w)| ≥ √3 ‖u‖ / 4`. -/
lemma tri_width_abs (u : ℂ) : ∃ v ∈ vT, ∃ w ∈ vT, Real.sqrt 3 * ‖u‖ / 4 ≤ |cross u (v - w)| := by
  have hn : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rcases tri_width_ineq u.re u.im ‖u‖ (norm_nonneg _) hn with h | h | h
  · refine ⟨⟨1 / 4, -(Real.sqrt 3 / 12)⟩, by simp [vT], ⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩, by simp [vT], ?_⟩
    have he : cross u (⟨1 / 4, -(Real.sqrt 3 / 12)⟩ - (⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩ : ℂ)) = -u.im / 2 := by
      simp only [cross, Complex.sub_re, Complex.sub_im]; ring
    rw [he, abs_div, abs_neg, abs_two]
    linarith
  · refine ⟨⟨0, Real.sqrt 3 / 6⟩, by simp [vT], ⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩, by simp [vT], ?_⟩
    have he : cross u (⟨0, Real.sqrt 3 / 6⟩ - (⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩ : ℂ)) =
        (Real.sqrt 3 * u.re - u.im) / 4 := by
      simp only [cross, Complex.sub_re, Complex.sub_im]; ring
    rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith
  · refine ⟨⟨0, Real.sqrt 3 / 6⟩, by simp [vT], ⟨1 / 4, -(Real.sqrt 3 / 12)⟩, by simp [vT], ?_⟩
    have he : cross u (⟨0, Real.sqrt 3 / 6⟩ - (⟨1 / 4, -(Real.sqrt 3 / 12)⟩ : ℂ)) =
        (Real.sqrt 3 * u.re + u.im) / 4 := by
      simp only [cross, Complex.sub_re, Complex.sub_im]; ring
    rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith

/-- **Triangle width.** The triangle `vT` has extent at least `√3/4` in every direction. -/
lemma tri_width (u : ℂ) : ∃ v ∈ vT, ∃ w ∈ vT, Real.sqrt 3 * ‖u‖ / 4 ≤ cross u (v - w) := by
  obtain ⟨v, hv, w, hw, h⟩ := tri_width_abs u
  rcases le_total 0 (cross u (v - w)) with h0 | h0
  · exact ⟨v, hv, w, hw, by rwa [abs_of_nonneg h0] at h⟩
  · refine ⟨w, hw, v, hv, ?_⟩
    have : cross u (w - v) = -cross u (v - w) := by simp only [cross, Complex.sub_re, Complex.sub_im]; ring
    rw [this]
    rwa [abs_of_nonpos h0] at h

lemma cross_rot (φ : ℝ) (u z : ℂ) :
    cross u (Complex.exp (φ * Complex.I) * z) = cross ((starRingEnd ℂ) (Complex.exp (φ * Complex.I)) * u) z := by
  simp only [cross, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **Placed triangle width.** -/
lemma placed_tri_width (φ : ℝ) (t u : ℂ) :
    ∃ v ∈ vT, ∃ w ∈ vT, Real.sqrt 3 * ‖u‖ / 4 ≤ cross u (motion φ t v - motion φ t w) := by
  obtain ⟨v, hv, w, hw, h⟩ := tri_width ((starRingEnd ℂ) (Complex.exp (φ * Complex.I)) * u)
  refine ⟨v, hv, w, hw, ?_⟩
  have e1 : motion φ t v - motion φ t w = Complex.exp (φ * Complex.I) * (v - w) := by
    simp only [motion]; ring
  have e2 : ‖(starRingEnd ℂ) (Complex.exp (φ * Complex.I)) * u‖ = ‖u‖ := by
    rw [norm_mul, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [e1, cross_rot]
  rwa [e2] at h

variable {τ : ℝ} {K : Set ℂ}

/-- **Chord bound.** In a convex set of area below `τ` that contains a placed copy of `vT`, every chord is shorter
than `8τ/√3`. -/
lemma chord_lt (hK : Convex ℝ K) (hτ : 0 < τ) (hvol : volume K < ENNReal.ofReal τ) {a c : ℂ} (ha : a ∈ K)
    (hc : c ∈ K) (φ : ℝ) (t : ℂ) (hT : ∀ v ∈ vT, motion φ t v ∈ K) : ‖c - a‖ < 8 * τ / Real.sqrt 3 := by
  obtain ⟨v, hv, w, hw, h⟩ := placed_tri_width φ t (c - a)
  have hq := quad_le hK ha (hT w hw) hc (hT v hv)
  have hlt : ENNReal.ofReal (MoserWorm.cross (c - a) (motion φ t v - motion φ t w) / 2) < ENNReal.ofReal τ :=
    lt_of_le_of_lt hq hvol
  rw [ENNReal.ofReal_lt_ofReal_iff hτ] at hlt
  have hcr : MoserWorm.cross (c - a) (motion φ t v - motion φ t w) =
      cross (c - a) (motion φ t v - motion φ t w) := rfl
  rw [hcr] at hlt
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [lt_div_iff₀ hs]
  linarith

/-- The imaginary part of a point of a convex set of area below `τ` that contains `±1/2`. -/
lemma im_lt (hK : Convex ℝ K) (hτ : 0 < τ) (hvol : volume K < ENNReal.ofReal τ) (hm : ((-(1 / 2) : ℝ) : ℂ) ∈ K)
    (hp : ((1 / 2 : ℝ) : ℂ) ∈ K) {c : ℂ} (hc : c ∈ K) : |c.im| < 2 * τ := by
  have h := MoserWorm.triangle_area_le_volume hK hm hp hc
  have hlt := lt_of_le_of_lt h hvol
  rw [ENNReal.ofReal_lt_ofReal_iff hτ] at hlt
  have e : MoserWorm.cross (((1 / 2 : ℝ) : ℂ) - ((-(1 / 2) : ℝ) : ℂ)) (c - ((-(1 / 2) : ℝ) : ℂ)) = c.im := by
    simp only [MoserWorm.cross_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [e] at hlt
  linarith

/-- The real part of a point of a convex set of area below `τ` that contains `±1/2` and a placed copy of `vT`. -/
lemma re_lt (hK : Convex ℝ K) (hτ : 0 < τ) (hvol : volume K < ENNReal.ofReal τ) (hm : ((-(1 / 2) : ℝ) : ℂ) ∈ K)
    (hp : ((1 / 2 : ℝ) : ℂ) ∈ K) (φ : ℝ) (t : ℂ) (hT : ∀ v ∈ vT, motion φ t v ∈ K) {c : ℂ} (hc : c ∈ K) :
    |c.re| < 8 * τ / Real.sqrt 3 - 1 / 2 := by
  rcases le_total 0 c.re with h0 | h0
  · have h := chord_lt hK hτ hvol hm hc φ t hT
    have hre := Complex.abs_re_le_norm (c - ((-(1 / 2) : ℝ) : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at hre
    rw [abs_of_nonneg h0]
    rw [abs_of_nonneg (by linarith)] at hre
    linarith
  · have h := chord_lt hK hτ hvol hp hc φ t hT
    have hre := Complex.abs_re_le_norm (c - ((1 / 2 : ℝ) : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at hre
    rw [abs_of_nonpos h0]
    rw [abs_of_nonpos (by linarith)] at hre
    linarith

end WormCore.Sound.W1Proof
