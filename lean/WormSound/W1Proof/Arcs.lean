import WormSound.Defs
import WormCore.Family
import WormSound.W1Proof.Chord

/-!
# Reduction to the root box: the five arcs

The vertices `V b` of body `b` (`arcPts`) and their mean `cen b` (as in `qReal`): the arcs are unit arcs (`cover_V`);
`L = [-1/2, 1/2]`; the centred vertices of `T` are `vT`, which the rotations by `±2π/3` permute; `C` and `S` are
parallelograms (first link = last link), so the half-turn about the mean permutes their vertices.
-/

noncomputable section

namespace WormCore.Sound.W1Proof

open Worm Worm.Geom

/-- The default arc of `qReal`. -/
abbrev arc0 : Arc := ⟨(0, 1), (0, 1), []⟩

/-- The vertices of body `b`. -/
def V (b : ℕ) : List ℂ := arcPts (famArcs.getD b arc0)

/-- The mean of the vertices of body `b`. -/
def cen (b : ℕ) : ℂ := (V b).sum / ((V b).length : ℂ)

lemma stepVertices_length : ∀ (st : List (ℝ × ℝ)) (a : ℂ), (stepVertices a st).length = st.length + 1
  | [], _ => rfl
  | _ :: st, a => by simp [stepVertices, stepVertices_length st]

lemma V_length (b : ℕ) : (V b).length = (famArcs.getD b arc0).steps.length + 1 := by
  simp [V, arcPts, stepVertices_length]

lemma famGid_ok : ∀ p ∈ famGid, p.1 < 5 ∧ p.2 ≤ (famArcs.getD p.1 arc0).steps.length := by
  decide +kernel

lemma arc_unit (b : ℕ) (hb : b < 5) :
    (∀ s ∈ (famArcs.getD b arc0).steps.map (fun s => ((s.1 : ℝ) / s.2.1, (s.2.2 : ℝ))), 0 < s.1) ∧
      (((famArcs.getD b arc0).steps.map (fun s => ((s.1 : ℝ) / s.2.1, (s.2.2 : ℝ)))).map Prod.fst).sum = 1 := by
  interval_cases b <;> simp [famArcs] <;> norm_num

/-- **Covers.** Every body's vertices lie in `Ω` after some proper motion. -/
lemma cover_V {Ω : Set ℂ} (hΩ : IsConvexCoverM Ω) (b : ℕ) (hb : b < 5) :
    ∃ θ : ℝ, ∃ t : ℂ, ∀ v ∈ V b, motion θ t v ∈ Ω := by
  obtain ⟨hpos, hlen⟩ := arc_unit b hb
  exact vertices_mem_of_coversM hpos hlen (hΩ.2 _ (stepArc_isUnitArc _ _ hpos hlen))

lemma exp_ofReal_mul_I_eq (x : ℝ) : Complex.exp (x * Complex.I) = ⟨Real.cos x, Real.sin x⟩ :=
  Complex.ext (Complex.exp_ofReal_mul_I_re x) (Complex.exp_ofReal_mul_I_im x)

/-! ## Body `0`: the unit segment -/

lemma V0_eq : V 0 = [((-(1 / 2) : ℝ) : ℂ), ((1 / 2 : ℝ) : ℂ)] := by
  simp only [V, arcPts, famArcs, List.getD_cons_zero, List.map_cons, List.map_nil, stepVertices]
  rw [show (((0 : ℤ) : ℝ) * Real.pi / 180 : ℝ) = 0 by simp, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  simp only [List.cons.injEq, and_true]
  constructor <;> apply Complex.ext <;> simp <;> norm_num

lemma V0_neg {v : ℂ} (hv : v ∈ V 0) : -v ∈ V 0 := by
  rw [V0_eq] at hv ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
  rcases hv with rfl | rfl
  · right; push_cast; ring
  · left; push_cast; ring

/-! ## Body `1`: the equilateral triangle -/

lemma V1_eq : V 1 = [⟨-(1 / 4), 0⟩, ⟨0, Real.sqrt 3 / 4⟩, ⟨1 / 4, 0⟩] := by
  simp only [V, arcPts, famArcs, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil,
    stepVertices]
  have h1 : (((60 : ℤ) : ℝ) * Real.pi / 180 : ℝ) = Real.pi / 3 := by push_cast; ring
  have h2 : (((-60 : ℤ) : ℝ) * Real.pi / 180 : ℝ) = -(Real.pi / 3) := by push_cast; ring
  rw [h1, h2, exp_ofReal_mul_I_eq, exp_ofReal_mul_I_eq, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> apply Complex.ext <;> simp <;> ring

lemma cen1_eq : cen 1 = ⟨0, Real.sqrt 3 / 12⟩ := by
  rw [cen, V1_eq]
  apply Complex.ext <;> simp
  ring

lemma vT_eq : (V 1).map (fun v => v - cen 1) = vT := by
  rw [V1_eq, cen1_eq]
  simp only [vT, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> apply Complex.ext <;> simp
  ring

lemma sub_cen1_mem {v : ℂ} (hv : v ∈ V 1) : v - cen 1 ∈ vT := by
  rw [← vT_eq]; exact List.mem_map_of_mem hv

lemma add_cen1_mem {w : ℂ} (hw : w ∈ vT) : w + cen 1 ∈ V 1 := by
  rw [← vT_eq] at hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
  simpa using hv

lemma sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

lemma rot_vT {w : ℂ} (hw : w ∈ vT) : Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I) * w ∈ vT := by
  have hc : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  have hs : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [exp_ofReal_mul_I_eq, hc, hs]
  simp only [vT, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
  have h3 := sqrt3_sq
  rcases hw with rfl | rfl | rfl
  · right; right; apply Complex.ext <;> simp <;> nlinarith
  · left; apply Complex.ext <;> simp <;> nlinarith
  · right; left; apply Complex.ext <;> simp <;> nlinarith

lemma rot_vT_neg {w : ℂ} (hw : w ∈ vT) : Complex.exp ((-(2 * Real.pi / 3) : ℝ) * Complex.I) * w ∈ vT := by
  have hc : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  have hs : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [exp_ofReal_mul_I_eq, Real.cos_neg, Real.sin_neg, hc, hs]
  simp only [vT, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
  have h3 := sqrt3_sq
  rcases hw with rfl | rfl | rfl
  · right; left; apply Complex.ext <;> simp <;> nlinarith
  · right; right; apply Complex.ext <;> simp <;> nlinarith
  · left; apply Complex.ext <;> simp <;> nlinarith

/-! ## Bodies `3`, `4`: the parallelograms -/

lemma para_sym (a d1 d2 : ℂ) {v : ℂ} (hv : v ∈ [a, a + d1, a + d1 + d2, a + d1 + d2 + d1]) :
    2 * ([a, a + d1, a + d1 + d2, a + d1 + d2 + d1].sum / (([a, a + d1, a + d1 + d2, a + d1 + d2 + d1].length : ℕ) : ℂ))
      - v ∈ [a, a + d1, a + d1 + d2, a + d1 + d2 + d1] := by
  simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hv ⊢
  push_cast
  rcases hv with rfl | rfl | rfl | rfl
  · right; right; right; ring
  · right; right; left; ring
  · right; left; ring
  · left; ring

lemma V3_form : ∃ a d1 d2 : ℂ, V 3 = [a, a + d1, a + d1 + d2, a + d1 + d2 + d1] := ⟨_, _, _, rfl⟩

lemma V4_form : ∃ a d1 d2 : ℂ, V 4 = [a, a + d1, a + d1 + d2, a + d1 + d2 + d1] := ⟨_, _, _, rfl⟩

lemma V_half_turn {b : ℕ} (hb : b = 3 ∨ b = 4) {v : ℂ} (hv : v ∈ V b) : 2 * cen b - v ∈ V b := by
  obtain ⟨a, d1, d2, h⟩ : ∃ a d1 d2 : ℂ, V b = [a, a + d1, a + d1 + d2, a + d1 + d2 + d1] := by
    rcases hb with rfl | rfl
    · exact V3_form
    · exact V4_form
  rw [h] at hv
  rw [cen, h]
  exact para_sym a d1 d2 hv

end WormCore.Sound.W1Proof
