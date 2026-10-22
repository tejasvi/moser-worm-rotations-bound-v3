import Worm13a.GeomInterface
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Refutation probes of the geometric interface (`Worm13a/GeomInterface.lean`)

* `vertices_mem_of_coversM_false`: the interface statement of `vertices_mem_of_coversM` before 2026-10-21 (no
  hypotheses on the steps) is false. With `steps = [(2, 0)]` the arc is `s ↦ s` on `[0, 1]`, so the unit segment covers
  it, but the vertex list is `[0, 2]`, and no rigid motion puts two points at distance `2` into the segment. The
  statement now assumes positive steps of total length `1`.
* `fan_le_needs_hwind`: the hypothesis `hwind` of `fan_le` (total turning `< 4π`) cannot be dropped. The square
  `1, i, -1, -i` traversed twice turns positively around `0` with total angle exactly `4π`, and its shoelace value `4`
  exceeds the area `π` of the unit disk, which contains it.
* `fan_le_nonvacuous`: the hypotheses of `fan_le` hold for the square traversed once around `0`.
* `chord_le_needs_ne`: the condition `pt P s ≠ pt P t` of a cut in `ChordOK` cannot be dropped. For the triangle
  `0, 1, i` traversed twice and the "chord" from vertex `0` to vertex `3` (the same point), every other condition of the
  cut holds, with valid pieces, but the shoelace value `1` exceeds the area `1/2` of the triangle.
-/

open Set MeasureTheory

noncomputable section

namespace Worm.Geom

/-! ### `vertices_mem_of_coversM` without hypotheses on the steps -/

/-- The unit segment `[0, 1]` on the real axis. -/
def unitSeg : Set ℂ := {x | x.im = 0 ∧ 0 ≤ x.re ∧ x.re ≤ 1}

lemma stepArc_two (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : stepArc 0 [(2, 0)] s = (s : ℂ) := by
  have h1 : min (max s 0) 2 = s := by
    rw [max_eq_left hs.1, min_eq_left (by linarith [hs.2])]
  simp [stepArc, h1]

lemma covers_two : CoversM unitSeg (stepArc 0 [(2, 0)]) := by
  refine ⟨0, 0, ?_⟩
  rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  rw [stepArc_two s hs]
  simp [motion, unitSeg, hs.1, hs.2]

theorem vertices_mem_of_coversM_false :
    ¬ ∀ (K : Set ℂ) (a : ℂ) (steps : List (ℝ × ℝ)), CoversM K (stepArc a steps) →
      ∃ θ : ℝ, ∃ t : ℂ, ∀ v ∈ stepVertices a steps, motion θ t v ∈ K := by
  intro h
  obtain ⟨θ, t, hv⟩ := h unitSeg 0 [(2, 0)] covers_two
  have h0 := hv 0 (by simp [stepVertices])
  have h2 := hv 2 (by simp [stepVertices])
  simp only [motion, mul_zero, zero_add] at h0 h2
  obtain ⟨h0i, h0a, h0b⟩ := h0
  obtain ⟨h2i, h2a, h2b⟩ := h2
  -- `u = e^{iθ} · 2` is real with `|u| ≤ 1`, but `|u| = 2`
  set u : ℂ := Complex.exp (θ * Complex.I) * 2 with hu
  have hui : u.im = 0 := by
    have := h2i; simp only [Complex.add_im] at this; linarith
  have hur : |u.re| ≤ 1 := by
    have := h2a; have := h2b; simp only [Complex.add_re] at *
    rw [abs_le]; constructor <;> linarith
  have hn : ‖u‖ = 2 := by
    rw [hu, norm_mul, Complex.norm_exp_ofReal_mul_I]; norm_num
  have hsq : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [hn, hui] at hsq
  have : u.re ^ 2 ≤ 1 := by
    have := abs_le.mp hur; nlinarith
  nlinarith

/-! ### `fan_le`: the winding hypothesis -/

/-- The square `1, i, -1, -i` traversed twice. -/
def square2 : List ℂ := [1, Complex.I, -1, -Complex.I, 1, Complex.I, -1, -Complex.I]

/-- The square `1, i, -1, -i` traversed once. -/
def square1 : List ℂ := [1, Complex.I, -1, -Complex.I]

lemma square_ratio (j : ℕ) (P : List ℂ) (hP : P = square2 ∨ P = square1) (hj : j < P.length) :
    pt P (j + 1) / pt P j = Complex.I := by
  rcases hP with rfl | rfl
  · simp only [square2, List.length_cons, List.length_nil] at hj
    interval_cases j <;> simp [pt, square2, Complex.div_I]
  · simp only [square1, List.length_cons, List.length_nil] at hj
    interval_cases j <;> simp [pt, square1, Complex.div_I]

lemma square_cross (j : ℕ) (P : List ℂ) (hP : P = square2 ∨ P = square1) (hj : j < P.length) :
    cross (pt P j - 0) (pt P (j + 1) - 0) = 1 := by
  rcases hP with rfl | rfl
  · simp only [square2, List.length_cons, List.length_nil] at hj
    interval_cases j <;> simp [pt, square2, cross]
  · simp only [square1, List.length_cons, List.length_nil] at hj
    interval_cases j <;> simp [pt, square1, cross]

lemma square_turning (P : List ℂ) (hP : P = square2 ∨ P = square1) :
    ∑ j ∈ Finset.range P.length, Complex.arg ((pt P (j + 1) - 0) / (pt P j - 0)) = P.length * (Real.pi / 2) := by
  rw [Finset.sum_congr rfl fun j hj => by
    rw [sub_zero, sub_zero, square_ratio j P hP (Finset.mem_range.mp hj), Complex.arg_I]]
  simp

lemma shoelace_square2 : shoelace square2 = 4 := by
  simp [shoelace, square2, pt, cross, Finset.sum_range_succ]
  norm_num

theorem fan_le_needs_hwind :
    ∃ (K : Set ℂ) (P : List ℂ) (z : ℂ), Convex ℝ K ∧ (∀ x ∈ P, x ∈ K) ∧ 3 ≤ P.length ∧
      (∀ j < P.length, 0 < cross (pt P j - z) (pt P (j + 1) - z)) ∧
      ∑ j ∈ Finset.range P.length, Complex.arg ((pt P (j + 1) - z) / (pt P j - z)) = 4 * Real.pi ∧
      volume K < ENNReal.ofReal (shoelace P) := by
  refine ⟨Metric.closedBall 0 1, square2, 0, convex_closedBall 0 1, ?_, by simp [square2], ?_, ?_, ?_⟩
  · intro x hx
    simp only [square2, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro j hj; rw [square_cross j square2 (Or.inl rfl) hj]; exact one_pos
  · rw [square_turning square2 (Or.inl rfl)]; simp [square2]; ring
  · rw [Complex.volume_closedBall, shoelace_square2, ENNReal.ofReal_one, one_pow, one_mul,
      ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr Real.pi_lt_four

theorem fan_le_nonvacuous :
    3 ≤ square1.length ∧ (∀ j < square1.length, 0 < cross (pt square1 j - 0) (pt square1 (j + 1) - 0)) ∧
      ∑ j ∈ Finset.range square1.length, Complex.arg ((pt square1 (j + 1) - 0) / (pt square1 j - 0)) <
        4 * Real.pi := by
  refine ⟨by simp [square1], fun j hj => by rw [square_cross j square1 (Or.inr rfl) hj]; exact one_pos, ?_⟩
  rw [square_turning square1 (Or.inr rfl)]
  simp [square1]
  exact Real.pi_pos

/-! ### `chord_le`: the condition `P_s ≠ P_t` of a cut -/

/-- The triangle `0, 1, i` traversed twice. -/
def tri2 : List ℂ := [0, 1, Complex.I, 0, 1, Complex.I]

lemma shoelace_tri2 : shoelace tri2 = 1 := by
  simp [shoelace, tri2, pt, cross, Finset.sum_range_succ]

lemma volume_tri : volume (convexHull ℝ ({0, 1, Complex.I} : Set ℂ)) = ENNReal.ofReal (1 / 2) := by
  rw [MoserWorm.volume_triangle]
  simp [MoserWorm.cross]

/-- All conditions of the cut `(s, t) = (0, 3)` of `tri2` except `pt P s ≠ pt P t` hold (both pieces are the
4-point list `0, 1, i, 0`, valid as small lists), yet the shoelace value exceeds the area of the convex hull. -/
theorem chord_le_needs_ne :
    let P := tri2
    let s := 0
    let t := 3
    s < P.length ∧ t < P.length ∧ 2 ≤ (t + P.length - s) % P.length ∧
      (t + P.length - s) % P.length + 2 ≤ P.length ∧ pt P s = pt P t ∧
      (∀ k, 1 ≤ k → k < (t + P.length - s) % P.length →
        cross (pt P t - pt P s) (pt P (s + k) - pt P s) ≤ 0) ∧
      (∀ k, 1 ≤ k → k < P.length - (t + P.length - s) % P.length →
        0 ≤ cross (pt P t - pt P s) (pt P (t + k) - pt P s)) ∧
      ChordOK .small ((List.range ((t + P.length - s) % P.length + 1)).map fun k => pt P (s + k)) ∧
      ChordOK .small ((List.range (P.length - (t + P.length - s) % P.length + 1)).map fun k => pt P (t + k)) ∧
      (∀ x ∈ P, x ∈ convexHull ℝ ({0, 1, Complex.I} : Set ℂ)) ∧
      volume (convexHull ℝ ({0, 1, Complex.I} : Set ℂ)) < ENNReal.ofReal (shoelace P) := by
  intro P s t
  have hpt : pt P 3 = pt P 0 := by simp [P, pt, tri2]
  refine ⟨by simp [P, s, tri2], by simp [P, t, tri2], by simp [P, s, t, tri2], by simp [P, s, t, tri2], hpt.symm,
    ?_, ?_, by simp [ChordOK, P, s, t, tri2], by simp [ChordOK, P, s, t, tri2], ?_, ?_⟩
  · intro k _ _; simp only [s, t, hpt, sub_self]; simp [cross]
  · intro k _ _; simp only [s, t, hpt, sub_self]; simp [cross]
  · intro x hx
    apply subset_convexHull
    simp only [P, tri2, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [volume_tri, shoelace_tri2]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

end Worm.Geom
