import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lower bound of a quadratic on a box (Gershgorin form) and the combination bound

For `F(y) = F₀ + ∑ₖ gₖ yₖ + ∑ₖ ∑ₗ Mₖₗ yₖ yₗ` over a finite index set and `|yₐ - y0ₐ| ≤ wₐ`:
`F(y) ≥ F(y0) + ∇F(y0)·(y - y0) - ½ ∑ₐ σₐ`, `σₐ = max(0, ∑_{b≠a} |H_ab wₐ w_b| - H_aa wₐ²)`, `H = M + Mᵀ`.
-/

namespace WormCore.Sound

open Finset

/-- `F(y) = F₀ + ∑ₖ gₖ yₖ + ∑ₖ ∑ₗ Mₖₗ yₖ yₗ` over the index set `s`. -/
def quadF (s : Finset ℕ) (F0 : ℝ) (g : ℕ → ℝ) (M : ℕ → ℕ → ℝ) (y : ℕ → ℝ) : ℝ :=
  F0 + ∑ k ∈ s, g k * y k + ∑ k ∈ s, ∑ l ∈ s, M k l * y k * y l

/-- `∇F(y0)ₐ = gₐ + ∑_b H_ab y0_b`. -/
def quadGrad (s : Finset ℕ) (g : ℕ → ℝ) (M : ℕ → ℕ → ℝ) (y0 : ℕ → ℝ) (a : ℕ) : ℝ :=
  g a + ∑ b ∈ s, (M a b + M b a) * y0 b

/-- The Gershgorin penalty `∑ₐ max(0, ∑_{b≠a} |H_ab wₐ w_b| - H_aa wₐ²)`. -/
def quadPen (s : Finset ℕ) (M : ℕ → ℕ → ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ a ∈ s, max 0 (∑ b ∈ s.erase a, |(M a b + M b a) * w a * w b| - (M a a + M a a) * w a * w a)

/-- Exact expansion of the quadratic at `y0`. -/
lemma quadF_expand (s : Finset ℕ) (F0 : ℝ) (g : ℕ → ℝ) (M : ℕ → ℕ → ℝ) (y y0 : ℕ → ℝ) :
    quadF s F0 g M y = quadF s F0 g M y0 + ∑ a ∈ s, quadGrad s g M y0 a * (y a - y0 a) +
      ∑ a ∈ s, ∑ b ∈ s, M a b * (y a - y0 a) * (y b - y0 b) := by
  unfold quadF quadGrad
  have h1 : ∑ k ∈ s, ∑ l ∈ s, M k l * y k * y l =
      ∑ k ∈ s, ∑ l ∈ s, (M k l * y0 k * y0 l + M k l * y0 k * (y l - y0 l) + M k l * (y k - y0 k) * y0 l +
        M k l * (y k - y0 k) * (y l - y0 l)) := by
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    ring
  have h2 : ∑ a ∈ s, (g a + ∑ b ∈ s, (M a b + M b a) * y0 b) * (y a - y0 a) =
      ∑ a ∈ s, g a * (y a - y0 a) + (∑ k ∈ s, ∑ l ∈ s, M k l * (y k - y0 k) * y0 l +
        ∑ k ∈ s, ∑ l ∈ s, M k l * y0 k * (y l - y0 l)) := by
    have e1 : ∀ a ∈ s, (g a + ∑ b ∈ s, (M a b + M b a) * y0 b) * (y a - y0 a) =
        g a * (y a - y0 a) + (∑ b ∈ s, M a b * (y a - y0 a) * y0 b + ∑ b ∈ s, M b a * y0 b * (y a - y0 a)) := by
      intro a _
      rw [add_mul, sum_mul, ← sum_add_distrib]
      congr 1
      exact sum_congr rfl fun b _ => by ring
    rw [sum_congr rfl e1, sum_add_distrib, sum_add_distrib]
    congr 2
    exact sum_comm
  rw [h1, h2]
  simp only [sum_add_distrib]
  have h3 : ∑ k ∈ s, g k * y k = ∑ k ∈ s, g k * y0 k + ∑ a ∈ s, g a * (y a - y0 a) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [h3]
  ring

/-- The quadratic part is at least `-½ ∑ₐ σₐ` on the box. -/
lemma quad_part_ge (s : Finset ℕ) (M : ℕ → ℕ → ℝ) (d w : ℕ → ℝ) (hw : ∀ a ∈ s, |d a| ≤ w a) :
    -(quadPen s M w) / 2 ≤ ∑ a ∈ s, ∑ b ∈ s, M a b * d a * d b := by
  -- symmetrize: ∑ M_ab d_a d_b = ½ ∑ H_ab d_a d_b
  set H : ℕ → ℕ → ℝ := fun a b => M a b + M b a with hH
  have hsym : ∑ a ∈ s, ∑ b ∈ s, M a b * d a * d b = (∑ a ∈ s, ∑ b ∈ s, H a b * d a * d b) / 2 := by
    have : ∑ a ∈ s, ∑ b ∈ s, H a b * d a * d b =
        ∑ a ∈ s, ∑ b ∈ s, M a b * d a * d b + ∑ a ∈ s, ∑ b ∈ s, M b a * d a * d b := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun a _ => by rw [← sum_add_distrib]; exact sum_congr rfl fun b _ => by ring
    rw [this, sum_comm (f := fun a b => M b a * d a * d b)]
    have : ∑ y ∈ s, ∑ x ∈ s, M y x * d x * d y = ∑ a ∈ s, ∑ b ∈ s, M a b * d a * d b :=
      sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
    rw [this]
    ring
  rw [hsym]
  -- the ratios r_a = |d_a| / w_a ∈ [0, 1]
  set r : ℕ → ℝ := fun a => if w a = 0 then 0 else |d a| / w a with hr
  have hw0 : ∀ a ∈ s, 0 ≤ w a := fun a ha => le_trans (abs_nonneg _) (hw a ha)
  have hdr : ∀ a ∈ s, |d a| = r a * w a := by
    intro a ha
    by_cases h0 : w a = 0
    · have : |d a| ≤ 0 := h0 ▸ hw a ha
      simp only [hr, h0, if_true, zero_mul]
      exact le_antisymm this (abs_nonneg _)
    · simp only [hr, h0, if_false]
      field_simp
  have hr0 : ∀ a ∈ s, 0 ≤ r a := by
    intro a ha
    simp only [hr]
    split_ifs
    · exact le_refl _
    · exact div_nonneg (abs_nonneg _) (hw0 a ha)
  have hr1 : ∀ a ∈ s, r a ≤ 1 := by
    intro a ha
    simp only [hr]
    split_ifs with h0
    · exact zero_le_one
    · exact (div_le_one (lt_of_le_of_ne (hw0 a ha) (Ne.symm h0))).2 (hw a ha)
  -- off-diagonal terms
  have hoff : ∀ a ∈ s, ∀ b ∈ s, b ≠ a →
      -(|H a b * w a * w b| * (r a ^ 2 + r b ^ 2) / 2) ≤ H a b * d a * d b := by
    intro a ha b hb _
    have hab : |H a b * d a * d b| = |H a b * w a * w b| * (r a * r b) := by
      rw [abs_mul, abs_mul, hdr a ha, hdr b hb, abs_mul, abs_mul, abs_of_nonneg (hw0 a ha),
        abs_of_nonneg (hw0 b hb)]
      ring
    have hamgm : r a * r b ≤ (r a ^ 2 + r b ^ 2) / 2 := by nlinarith [sq_nonneg (r a - r b)]
    have := neg_abs_le (H a b * d a * d b)
    rw [hab] at this
    nlinarith [abs_nonneg (H a b * w a * w b)]
  have hdiag : ∀ a ∈ s, H a a * d a * d a = H a a * w a * w a * r a ^ 2 := by
    intro a ha
    have : d a * d a = |d a| * |d a| := (abs_mul_abs_self (d a)).symm
    rw [mul_assoc, this, hdr a ha]
    ring
  -- split each row into the diagonal and the rest
  have hrow : ∀ a ∈ s, ∑ b ∈ s, H a b * d a * d b =
      H a a * d a * d a + ∑ b ∈ s.erase a, H a b * d a * d b := by
    intro a ha
    rw [← add_sum_erase s _ ha]
  have hrowge : ∀ a ∈ s, H a a * w a * w a * r a ^ 2 -
      ∑ b ∈ s.erase a, |H a b * w a * w b| * (r a ^ 2 + r b ^ 2) / 2 ≤ ∑ b ∈ s, H a b * d a * d b := by
    intro a ha
    rw [hrow a ha, hdiag a ha]
    have : -(∑ b ∈ s.erase a, |H a b * w a * w b| * (r a ^ 2 + r b ^ 2) / 2) ≤
        ∑ b ∈ s.erase a, H a b * d a * d b := by
      rw [← sum_neg_distrib]
      exact sum_le_sum fun b hb => hoff a ha b (mem_of_mem_erase hb) (ne_of_mem_erase hb)
    linarith
  -- the symmetric double sum of the off-diagonal weights
  have hswap : ∑ a ∈ s, ∑ b ∈ s.erase a, |H a b * w a * w b| * r b ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s.erase a, |H a b * w a * w b| * r a ^ 2 := by
    have e1 : ∀ a ∈ s, ∑ b ∈ s.erase a, |H a b * w a * w b| * r b ^ 2 =
        ∑ b ∈ s, if b = a then 0 else |H a b * w a * w b| * r b ^ 2 := by
      intro a ha
      rw [← add_sum_erase s _ ha, if_pos rfl, zero_add]
      exact sum_congr rfl fun b hb => by rw [if_neg (ne_of_mem_erase hb)]
    have e2 : ∀ a ∈ s, ∑ b ∈ s.erase a, |H a b * w a * w b| * r a ^ 2 =
        ∑ b ∈ s, if b = a then 0 else |H a b * w a * w b| * r a ^ 2 := by
      intro a ha
      rw [← add_sum_erase s _ ha, if_pos rfl, zero_add]
      exact sum_congr rfl fun b hb => by rw [if_neg (ne_of_mem_erase hb)]
    rw [sum_congr rfl e1, sum_congr rfl e2, sum_comm]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, if_neg (Ne.symm hab)]
      have : H b a * w b * w a = H a b * w a * w b := by simp only [hH]; ring
      rw [this]
  -- assemble
  have hsum : ∑ a ∈ s, (H a a * w a * w a * r a ^ 2 -
      ∑ b ∈ s.erase a, |H a b * w a * w b| * (r a ^ 2 + r b ^ 2) / 2) =
      ∑ a ∈ s, r a ^ 2 * (H a a * w a * w a - ∑ b ∈ s.erase a, |H a b * w a * w b|) := by
    have e : ∀ a ∈ s, H a a * w a * w a * r a ^ 2 -
        ∑ b ∈ s.erase a, |H a b * w a * w b| * (r a ^ 2 + r b ^ 2) / 2 =
        H a a * w a * w a * r a ^ 2 - (∑ b ∈ s.erase a, |H a b * w a * w b| * r a ^ 2) / 2 -
          (∑ b ∈ s.erase a, |H a b * w a * w b| * r b ^ 2) / 2 := by
      intro a _
      have : ∑ b ∈ s.erase a, |H a b * w a * w b| * (r a ^ 2 + r b ^ 2) / 2 =
          (∑ b ∈ s.erase a, |H a b * w a * w b| * r a ^ 2) / 2 +
            (∑ b ∈ s.erase a, |H a b * w a * w b| * r b ^ 2) / 2 := by
        rw [← add_div, ← sum_add_distrib, sum_div]
        exact sum_congr rfl fun b _ => by ring
      rw [this]; ring
    have e2 : ∀ a ∈ s, r a ^ 2 * (H a a * w a * w a - ∑ b ∈ s.erase a, |H a b * w a * w b|) =
        H a a * w a * w a * r a ^ 2 - ∑ b ∈ s.erase a, |H a b * w a * w b| * r a ^ 2 := by
      intro a _
      rw [← sum_mul]; ring
    rw [sum_congr rfl e, sum_congr rfl e2, sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, ← sum_div,
      ← sum_div, hswap]
    ring
  have hpen : ∀ a ∈ s, -(max 0 (∑ b ∈ s.erase a, |H a b * w a * w b| - H a a * w a * w a)) ≤
      r a ^ 2 * (H a a * w a * w a - ∑ b ∈ s.erase a, |H a b * w a * w b|) := by
    intro a ha
    set σ := ∑ b ∈ s.erase a, |H a b * w a * w b| - H a a * w a * w a
    have h0 : 0 ≤ r a ^ 2 := sq_nonneg _
    have h1 : r a ^ 2 ≤ 1 := by nlinarith [hr0 a ha, hr1 a ha]
    have hm : σ ≤ max 0 σ := le_max_right _ _
    have hm0 : 0 ≤ max 0 σ := le_max_left _ _
    have : r a ^ 2 * (H a a * w a * w a - ∑ b ∈ s.erase a, |H a b * w a * w b|) = -(r a ^ 2 * σ) := by ring
    rw [this]
    nlinarith
  have htot : -(quadPen s M w) ≤ ∑ a ∈ s, ∑ b ∈ s, H a b * d a * d b := by
    calc -(quadPen s M w) = ∑ a ∈ s, -(max 0 (∑ b ∈ s.erase a, |H a b * w a * w b| - H a a * w a * w a)) := by
          rw [quadPen, ← sum_neg_distrib]
      _ ≤ ∑ a ∈ s, r a ^ 2 * (H a a * w a * w a - ∑ b ∈ s.erase a, |H a b * w a * w b|) := sum_le_sum hpen
      _ = ∑ a ∈ s, (H a a * w a * w a * r a ^ 2 -
            ∑ b ∈ s.erase a, |H a b * w a * w b| * (r a ^ 2 + r b ^ 2) / 2) := hsum.symm
      _ ≤ ∑ a ∈ s, ∑ b ∈ s, H a b * d a * d b := sum_le_sum hrowge
  linarith

/-- **Gershgorin box bound.** For `|yₐ - y0ₐ| ≤ wₐ` on `s`:
`F(y) ≥ F(y0) + ∇F(y0)·(y - y0) - ½ ∑ₐ σₐ`. -/
theorem quadF_ge (s : Finset ℕ) (F0 : ℝ) (g : ℕ → ℝ) (M : ℕ → ℕ → ℝ) (y y0 w : ℕ → ℝ)
    (hw : ∀ a ∈ s, |y a - y0 a| ≤ w a) :
    quadF s F0 g M y0 + ∑ a ∈ s, quadGrad s g M y0 a * (y a - y0 a) - quadPen s M w / 2 ≤ quadF s F0 g M y := by
  rw [quadF_expand s F0 g M y y0]
  have := quad_part_ge s M (fun a => y a - y0 a) w hw
  linarith

/-- Swap a list sum of weighted gradient terms with the sum over the variables. -/
lemma list_sum_grad {ι : Type*} (L : List ι) (lam : ι → ℝ) (s : Finset ℕ) (G : ι → ℕ → ℝ) (d : ℕ → ℝ) :
    (L.map fun i => lam i * ∑ a ∈ s, G i a * d a).sum = ∑ a ∈ s, (L.map fun i => lam i * G i a).sum * d a := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.map_cons, List.sum_cons, ih, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    simp only [List.map_cons, List.sum_cons]
    ring

/-- **Combination bound** (Lemma K): for weights `λᵢ ≥ 0` and quadratics `Fᵢ` on `s`, on the box
`∑ᵢ λᵢ Fᵢ(y) ≥ ∑ᵢ λᵢ (Fᵢ(y0) - penᵢ/2) - ∑ₐ |∑ᵢ λᵢ ∇Fᵢ(y0)ₐ| wₐ`. -/
theorem combo_ge {ι : Type*} (L : List ι) (lam : ι → ℝ) (hlam : ∀ i ∈ L, 0 ≤ lam i) (s : Finset ℕ)
    (F0 : ι → ℝ) (g : ι → ℕ → ℝ) (M : ι → ℕ → ℕ → ℝ) (y y0 w : ℕ → ℝ) (hw : ∀ a ∈ s, |y a - y0 a| ≤ w a) :
    (L.map fun i => lam i * (quadF s (F0 i) (g i) (M i) y0 - quadPen s (M i) w / 2)).sum -
      ∑ a ∈ s, |(L.map fun i => lam i * quadGrad s (g i) (M i) y0 a).sum| * w a ≤
      (L.map fun i => lam i * quadF s (F0 i) (g i) (M i) y).sum := by
  have h1 : (L.map fun i => lam i * (quadF s (F0 i) (g i) (M i) y0 - quadPen s (M i) w / 2 +
      ∑ a ∈ s, quadGrad s (g i) (M i) y0 a * (y a - y0 a))).sum ≤
      (L.map fun i => lam i * quadF s (F0 i) (g i) (M i) y).sum := by
    refine List.sum_le_sum fun i hi => ?_
    have := quadF_ge s (F0 i) (g i) (M i) y y0 w hw
    exact mul_le_mul_of_nonneg_left (by linarith) (hlam i hi)
  have h2 : (L.map fun i => lam i * (quadF s (F0 i) (g i) (M i) y0 - quadPen s (M i) w / 2 +
      ∑ a ∈ s, quadGrad s (g i) (M i) y0 a * (y a - y0 a))).sum =
      (L.map fun i => lam i * (quadF s (F0 i) (g i) (M i) y0 - quadPen s (M i) w / 2)).sum +
        ∑ a ∈ s, (L.map fun i => lam i * quadGrad s (g i) (M i) y0 a).sum * (y a - y0 a) := by
    rw [← list_sum_grad, ← List.sum_map_add]
    congr 1
    exact List.map_congr_left fun i _ => by ring
  have h3 : -(∑ a ∈ s, |(L.map fun i => lam i * quadGrad s (g i) (M i) y0 a).sum| * w a) ≤
      ∑ a ∈ s, (L.map fun i => lam i * quadGrad s (g i) (M i) y0 a).sum * (y a - y0 a) := by
    rw [← sum_neg_distrib]
    refine sum_le_sum fun a ha => ?_
    set G := (L.map fun i => lam i * quadGrad s (g i) (M i) y0 a).sum
    have h := hw a ha
    have : |G * (y a - y0 a)| ≤ |G| * w a := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    linarith [neg_abs_le (G * (y a - y0 a))]
  linarith

end WormCore.Sound
