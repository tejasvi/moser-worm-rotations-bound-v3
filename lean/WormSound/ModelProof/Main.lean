import WormSound.ModelDefs
import WormSound.ModelProof.Basic

/-!
# Proofs of the area-model statements (`WormSound.Model`)

* `pos_expand`: the position of a vertex is the centre position plus `∑ₖ coefR g k · yₖ` (the coefficients of
  `lcolR` on the four variables of its body);
* `cross_pos_expand`: the cross product of two placed vertices is the quadratic with the coefficients `gTermR`,
  `MTermR`;
* `shoelace_eq_quadF'`, `yOf_circle'`, `yOf_mem_box'`: the three statements of `WormSound.Model`.
-/

noncomputable section

namespace WormCore.Sound.ModelProof

open WormCore WormCore.Sound WormCore.IvSound Complex Finset Worm.Geom
open MoserWorm (dfxS)

variable (F : Fam) (q : ℕ → ℂ) (lo hi : Array Int)

/-- The coefficient of the variable `y_k` in the position of vertex `g`. -/
def coefR (g k : ℕ) : ℂ :=
  if F.body[g]! ≠ 0 ∧ k / 4 = F.body[g]! - 1 then lcolR F q lo hi g (k % 4) else 0

lemma yOf_block0 (x : Fin 12 → ℝ) {b : ℕ} (hb1 : 1 ≤ b) :
    yOf lo hi x (4 * (b - 1)) = (bodyTrans x b - centreTrans lo hi b).re := by
  have h1 : 4 * (b - 1) % 4 = 0 := by omega
  have h2 : 4 * (b - 1) / 4 + 1 = b := by omega
  simp only [yOf, h1, h2]

lemma yOf_block1 (x : Fin 12 → ℝ) {b : ℕ} (hb1 : 1 ≤ b) :
    yOf lo hi x (4 * (b - 1) + 1) = (bodyTrans x b - centreTrans lo hi b).im := by
  have h1 : (4 * (b - 1) + 1) % 4 = 1 := by omega
  have h2 : (4 * (b - 1) + 1) / 4 + 1 = b := by omega
  simp only [yOf, h1, h2]

lemma yOf_block2 (x : Fin 12 → ℝ) {b : ℕ} (hb1 : 1 ≤ b) :
    yOf lo hi x (4 * (b - 1) + 2) = Real.cos (bodyAngle x b - centreAngle lo hi b) - 1 := by
  have h1 : (4 * (b - 1) + 2) % 4 = 2 := by omega
  have h2 : (4 * (b - 1) + 2) / 4 + 1 = b := by omega
  simp only [yOf, h1, h2]

lemma yOf_block3 (x : Fin 12 → ℝ) {b : ℕ} (hb1 : 1 ≤ b) :
    yOf lo hi x (4 * (b - 1) + 3) = Real.sin (bodyAngle x b - centreAngle lo hi b) := by
  have h1 : (4 * (b - 1) + 3) % 4 = 3 := by omega
  have h2 : (4 * (b - 1) + 3) / 4 + 1 = b := by omega
  simp only [yOf, h1, h2]

/-- **Per vertex.** `pos x g = posC g + ∑ₖ coefR g k · yₖ`. -/
theorem pos_expand (hF : FamSpec F q) (hk : F.k = 4) (x : Fin 12 → ℝ) {g : ℕ} (hg : g < F.body.size) :
    pos F q x g = posC F q lo hi g + ∑ k ∈ range 16, coefR F q lo hi g k * (yOf lo hi x k : ℂ) := by
  by_cases h0 : F.body[g]! = 0
  · simp [pos, posC, coefR, h0]
  · have hb1 : 1 ≤ F.body[g]! := Nat.one_le_iff_ne_zero.mpr h0
    have hb4 : F.body[g]! ≤ 4 := hk ▸ hF.body_le g hg
    simp only [coefR, ite_mul, zero_mul]
    rw [sum16_block hb1 hb4]
    have m0 : 4 * (F.body[g]! - 1) % 4 = 0 := by omega
    have m1 : (4 * (F.body[g]! - 1) + 1) % 4 = 1 := by omega
    have m2 : (4 * (F.body[g]! - 1) + 2) % 4 = 2 := by omega
    have m3 : (4 * (F.body[g]! - 1) + 3) % 4 = 3 := by omega
    rw [m0, m1, m2, m3, yOf_block0 lo hi x hb1, yOf_block1 lo hi x hb1, yOf_block2 lo hi x hb1,
      yOf_block3 lo hi x hb1]
    simp only [lcolR]
    unfold pos posC rqR
    rw [ite_eq_right h0, ite_eq_right h0, ite_eq_right h0]
    linear_combination place_expand (bodyAngle x F.body[g]!) (centreAngle lo hi F.body[g]!) (bodyTrans x F.body[g]!)
      (centreTrans lo hi F.body[g]!) (q g)

/-- **Per edge.** `cross (pos x a) (pos x b)` is the quadratic with the coefficients `gTermR`, `MTermR`. -/
theorem cross_pos_expand (hF : FamSpec F q) (hk : F.k = 4) (x : Fin 12 → ℝ) {a b : ℕ} (ha : a < F.body.size)
    (hb : b < F.body.size) :
    cross (pos F q x a) (pos F q x b) = cross (posC F q lo hi a) (posC F q lo hi b) +
      ∑ k ∈ range 16, gTermR F q lo hi a b k * yOf lo hi x k +
      ∑ k ∈ range 16, ∑ m ∈ range 16, MTermR F q lo hi a b k m * yOf lo hi x k * yOf lo hi x m := by
  have hg : ∀ k, cross (posC F q lo hi a) (coefR F q lo hi b k) + cross (coefR F q lo hi a k) (posC F q lo hi b) =
      gTermR F q lo hi a b k := by
    intro k
    unfold gTermR coefR
    split_ifs <;> simp only [cross_zero_left, cross_zero_right, add_zero, zero_add]
  have hm : ∀ k m, cross (coefR F q lo hi a k) (coefR F q lo hi b m) = MTermR F q lo hi a b k m := by
    intro k m
    unfold MTermR coefR
    by_cases h1 : F.body[a]! ≠ 0 ∧ k / 4 = F.body[a]! - 1
    · by_cases h2 : F.body[b]! ≠ 0 ∧ m / 4 = F.body[b]! - 1
      · rw [ite_eq_left h1, ite_eq_left h2,
          ite_eq_left (show F.body[a]! ≠ 0 ∧ F.body[b]! ≠ 0 ∧ k / 4 = F.body[a]! - 1 ∧ m / 4 = F.body[b]! - 1 from
            ⟨h1.1, h2.1, h1.2, h2.2⟩)]
      · rw [ite_eq_right h2,
          ite_eq_right (show ¬(F.body[a]! ≠ 0 ∧ F.body[b]! ≠ 0 ∧ k / 4 = F.body[a]! - 1 ∧ m / 4 = F.body[b]! - 1) from
            fun h => h2 ⟨h.2.1, h.2.2.2⟩), cross_zero_right]
    · rw [ite_eq_right h1,
        ite_eq_right (show ¬(F.body[a]! ≠ 0 ∧ F.body[b]! ≠ 0 ∧ k / 4 = F.body[a]! - 1 ∧ m / 4 = F.body[b]! - 1) from
          fun h => h1 ⟨h.1, h.2.2.1⟩), cross_zero_left]
  rw [pos_expand F q lo hi hF hk x ha, pos_expand F q lo hi hF hk x hb, cross_expand]
  simp only [hg, hm]

/-- **Model identity** (`WormSound.Model.shoelace_eq_quadF`). -/
theorem shoelace_eq_quadF' (hF : FamSpec F q) (hk : F.k = 4) (l : List ℕ) (hl : ∀ g ∈ l, g < F.body.size)
    (x : Fin 12 → ℝ) :
    shoelace (l.map (pos F q x)) =
      quadF (range 16) (F0R F q lo hi l) (gR F q lo hi l) (MR F q lo hi l) (yOf lo hi x) := by
  rw [shoelace_map]
  have hmem : ∀ j ∈ range l.length, at' l j < F.body.size ∧ at' l (j + 1) < F.body.size := by
    intro j hj
    have hn : 0 < l.length := by have := Finset.mem_range.mp hj; omega
    exact ⟨hl _ (at'_mem hn j), hl _ (at'_mem hn (j + 1))⟩
  rw [Finset.sum_congr rfl fun j hj => cross_pos_expand F q lo hi hF hk x (hmem j hj).1 (hmem j hj).2]
  unfold quadF F0R gR MR
  simp only [cycPairs_sum]
  exact sum_quad_assoc _ _ _ _ _ _

/-- `C² + S² + 2C = 0` (`WormSound.Model.yOf_circle`). -/
theorem yOf_circle' (x : Fin 12 → ℝ) (b : ℕ) :
    yOf lo hi x (4 * b + 2) ^ 2 + yOf lo hi x (4 * b + 3) ^ 2 + 2 * yOf lo hi x (4 * b + 2) = 0 := by
  have h2 : (4 * b + 2) % 4 = 2 := by omega
  have h3 : (4 * b + 3) % 4 = 3 := by omega
  have d2 : (4 * b + 2) / 4 = b := by omega
  have d3 : (4 * b + 3) / 4 = b := by omega
  simp only [yOf, h2, h3, d2, d3]
  linear_combination Real.sin_sq_add_cos_sq (bodyAngle x (b + 1) - centreAngle lo hi (b + 1))

/-- The box variables (`WormSound.Model.yOf_mem_box`). -/
theorem yOf_mem_box' (_hF : FamSpec F q) (hk : F.k = 4) (_hB : BoxOK lo hi) (x : Fin 12 → ℝ) (hx : InBox lo hi x)
    (k : ℕ) (hk16 : k < 16) :
    |yOf lo hi x k - (y0At (mkCtx F lo hi) k : ℝ) / 2 ^ dfxS| ≤ (wAt (mkCtx F lo hi) k : ℝ) / 2 ^ dfxS := by
  have hb1 : 1 ≤ k / 4 + 1 := by omega
  have hb4 : k / 4 + 1 ≤ 4 := by omega
  have hbd : (mkCtx F lo hi).bd[k / 4 + 1]! = bodyData lo hi (k / 4 + 1) := ctx_bd hb1 (hk ▸ hb4)
  have hθ := abs_angle_sub_le hx hb1 hb4
  rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h | h | h | h
  · simp only [yOf, y0At, wAt, h, hbd]
    simpa using trans_re_mem hx hb1 hb4
  · simp only [yOf, y0At, wAt, h, hbd]
    simpa using trans_im_mem hx hb1 hb4
  · simp only [yOf, y0At, wAt, h, hbd, ite_true]
    exact cos_var_mem hθ
  · simp only [yOf, y0At, wAt, h, hbd]
    simpa using sin_var_mem hθ

end WormCore.Sound.ModelProof
