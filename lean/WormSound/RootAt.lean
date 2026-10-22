import WormCore.Family
import WormSound.W1Gen
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The domain `D_τ` lies in the root box (instance `τ = 2410/10000`)

The root box of the certificate (`WormCore.rootW`, mantissas at scale `2⁻¹²⁰`) contains the angle ranges `[0, π/3]`,
`[0, 2π]`, `[0, π]`, `[0, π]` and the translation ranges `[-X_τ, X_τ] × [-Y_τ, Y_τ]` for `τ = 2410/10000` (certificate cert_w2410a). The margins are about `3 · 10⁻⁸` for the angles (with
`π < 3.14159265358979323847`), `2.5 · 10⁻⁸` for `X_τ` (with `√3 > 1.7320508075`) and `5 · 10⁻⁸` for `Y_τ`.
-/

noncomputable section

namespace WormCore.Sound.W1ProofAt

open WormCore WormCore.Sound

lemma sqrt3_gt : (17320508075 / 10000000000 : ℝ) < Real.sqrt 3 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma angle_le_third {y : ℝ} (h : y ≤ Real.pi / 3) :
    y ≤ (1391964340902861003041229276090204160 : ℝ) / 2 ^ BS := by
  have := Real.pi_lt_d20
  norm_num [BS] at *
  linarith

lemma angle_le_two {y : ℝ} (h : y ≤ 2 * Real.pi) :
    y ≤ (8351785886960840989718700469453324288 : ℝ) / 2 ^ BS := by
  have := Real.pi_lt_d20
  norm_num [BS] at *
  linarith

lemma angle_le_one {y : ℝ} (h : y ≤ Real.pi) :
    y ≤ (4175892943480420494859350234726662144 : ℝ) / 2 ^ BS := by
  have := Real.pi_lt_d20
  norm_num [BS] at *
  linarith

lemma transX {y : ℝ} (h : |y| ≤ 8 * (2410 / 10000) / Real.sqrt 3 - 1 / 2) :
    ((-814991347961244562870240160652460032 : Int) : ℝ) / 2 ^ BS ≤ y ∧
      y ≤ ((814991347961244562870240160652460032 : Int) : ℝ) / 2 ^ BS := by
  have hs := sqrt3_gt
  have hd : 8 * (2410 / 10000) / Real.sqrt 3 ≤ 8 * (2410 / 10000) / (17320508075 / 10000000000 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs.le
  have h1 := le_abs_self y
  have h2 := neg_abs_le y
  constructor
  · norm_num [BS] at *
    linarith
  · norm_num [BS] at *
    linarith

lemma transY {y : ℝ} (h : |y| ≤ 2 * (2410 / 10000)) :
    ((-640687964322937763406366786122153984 : Int) : ℝ) / 2 ^ BS ≤ y ∧
      y ≤ ((640687964322937763406366786122153984 : Int) : ℝ) / 2 ^ BS := by
  have h1 := le_abs_self y
  have h2 := neg_abs_le y
  constructor
  · norm_num [BS] at *
    linarith
  · norm_num [BS] at *
    linarith

/-- `D_τ ⊆ rootW`, with `X_τ`, `Y_τ` and `D_τ` written out. -/
theorem root_box (x : Fin 12 → ℝ)
    (hx : (0 ≤ x 0 ∧ x 0 ≤ Real.pi / 3) ∧ (0 ≤ x 3 ∧ x 3 ≤ 2 * Real.pi) ∧ (0 ≤ x 6 ∧ x 6 ≤ Real.pi) ∧
      (0 ≤ x 9 ∧ x 9 ≤ Real.pi) ∧ ∀ b < 4, |coord x (3 * b + 1)| ≤ 8 * (2410 / 10000) / Real.sqrt 3 - 1 / 2 ∧
        |coord x (3 * b + 2)| ≤ 2 * (2410 / 10000)) :
    InBox rootW.lo rootW.hi x := by
  obtain ⟨⟨h0a, h0b⟩, ⟨h3a, h3b⟩, ⟨h6a, h6b⟩, ⟨h9a, h9b⟩, ht⟩ := hx
  have t0 := ht 0 (by norm_num)
  have t1 := ht 1 (by norm_num)
  have t2 := ht 2 (by norm_num)
  have t3 := ht 3 (by norm_num)
  simp only [coord, Nat.reduceMul, Nat.reduceAdd, show (1 : ℕ) < 12 by norm_num, show (2 : ℕ) < 12 by norm_num,
    show (4 : ℕ) < 12 by norm_num, show (5 : ℕ) < 12 by norm_num, show (7 : ℕ) < 12 by norm_num,
    show (8 : ℕ) < 12 by norm_num, show (10 : ℕ) < 12 by norm_num, show (11 : ℕ) < 12 by norm_num,
    dite_true] at t0 t1 t2 t3
  intro i
  fin_cases i
  · exact ⟨by simpa [rootW] using h0a, by simpa [rootW] using angle_le_third h0b⟩
  · exact transX t0.1
  · exact transY t0.2
  · exact ⟨by simpa [rootW] using h3a, by simpa [rootW] using angle_le_two h3b⟩
  · exact transX t1.1
  · exact transY t1.2
  · exact ⟨by simpa [rootW] using h6a, by simpa [rootW] using angle_le_one h6b⟩
  · exact transX t2.1
  · exact transY t2.2
  · exact ⟨by simpa [rootW] using h9a, by simpa [rootW] using angle_le_one h9b⟩
  · exact transX t3.1
  · exact transY t3.2

end WormCore.Sound.W1ProofAt

namespace WormCore.Sound

/-- `D_τ ⊆ rootW` for `τ = 2410/10000`. -/
theorem root_box_at : ∀ x : Fin 12 → ℝ, InDtauOf (2410 / 10000) x → InBox rootW.lo rootW.hi x :=
  fun x hx => W1ProofAt.root_box x hx

end WormCore.Sound
