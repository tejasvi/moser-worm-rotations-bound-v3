import WormSound.W1Proof.Arcs
import Worm13a.GeomMotion
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Reduction to the root box: a small convex cover to a placement in `D_τ`

Paper, Lemma 2.2 and Proposition 2.4. The five bodies lie in `Ω` after proper motions `motion θ_b t_b`. With
`α = θ₀` or `θ₀ + π` (the half-turn maps `L` to itself) and `Ω' = (motion α t₀)⁻¹ Ω`, body `b ≥ 1` is placed with the
angle `θ_b - α` reduced modulo its period `per b` (`2π/3`, `2π`, `π`, `π`; its vertex set is invariant under the
rotations by the period about its mean) and the translation `e^{-iα}(e^{iθ_b} c_b + t_b - t₀)`. The translation bounds
follow from `W1Proof.Chord`.
-/

open MeasureTheory

noncomputable section

namespace WormCore.Sound.W1Proof

open Worm Worm.Geom

/-! ## Rotations about a point -/

/-- The rotation by `x` about `c`. -/
def rotAbout (x : ℝ) (c v : ℂ) : ℂ := Complex.exp (x * Complex.I) * (v - c) + c

lemma rotAbout_add (x y : ℝ) (c v : ℂ) : rotAbout (x + y) c v = rotAbout x c (rotAbout y c v) := by
  simp only [rotAbout, add_sub_cancel_right, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

/-- A list invariant under the rotations by `±p` about `c` is invariant under the rotations by `k p`, `k ∈ ℤ`. -/
lemma sym_int (p : ℝ) (L : List ℂ) (c : ℂ) (h1 : ∀ v ∈ L, rotAbout p c v ∈ L)
    (h2 : ∀ v ∈ L, rotAbout (-p) c v ∈ L) (k : ℤ) : ∀ v ∈ L, rotAbout ((k : ℝ) * p) c v ∈ L := by
  induction k using Int.induction_on with
  | zero => intro v hv; simpa [rotAbout] using hv
  | succ n ih =>
    intro v hv
    have e : (((n : ℤ) + 1 : ℤ) : ℝ) * p = p + ((n : ℤ) : ℝ) * p := by push_cast; ring
    rw [e, rotAbout_add]
    exact h1 _ (ih v hv)
  | pred n ih =>
    intro v hv
    have e : ((-(n : ℤ) - 1 : ℤ) : ℝ) * p = -p + ((-(n : ℤ) : ℤ) : ℝ) * p := by push_cast; ring
    rw [e, rotAbout_add]
    exact h2 _ (ih v hv)

/-- The angle periods of bodies `1, …, 4`. -/
def per (b : ℕ) : ℝ := if b = 1 then 2 * Real.pi / 3 else if b = 2 then 2 * Real.pi else Real.pi

lemma per_pos (b : ℕ) : 0 < per b := by
  unfold per; split_ifs <;> positivity

lemma rotAbout_one {x : ℝ} (hc : Real.cos x = 1) (hs : Real.sin x = 0) (c v : ℂ) : rotAbout x c v = v := by
  rw [rotAbout, exp_ofReal_mul_I_eq, hc, hs]
  have : (⟨1, 0⟩ : ℂ) = 1 := Complex.ext (by simp) (by simp)
  rw [this]; ring

lemma rotAbout_neg_one {x : ℝ} (hc : Real.cos x = -1) (hs : Real.sin x = 0) (c v : ℂ) :
    rotAbout x c v = 2 * c - v := by
  rw [rotAbout, exp_ofReal_mul_I_eq, hc, hs]
  have : (⟨-1, 0⟩ : ℂ) = -1 := Complex.ext (by simp) (by simp)
  rw [this]; ring

/-- **Symmetries.** The vertex list of body `b` is invariant under the rotations by multiples of `per b` about its
mean. -/
lemma body_sym (b : ℕ) (hb1 : 1 ≤ b) (hb4 : b ≤ 4) (k : ℤ) :
    ∀ v ∈ V b, rotAbout ((k : ℝ) * per b) (cen b) v ∈ V b := by
  have hb : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
  apply sym_int
  · intro v hv
    rcases hb with rfl | rfl | rfl | rfl
    · simp only [per, ↓reduceIte]
      exact add_cen1_mem (rot_vT (sub_cen1_mem hv))
    · rw [rotAbout_one (by simp [per]) (by simp [per])]; exact hv
    · rw [rotAbout_neg_one (by simp [per]) (by simp [per])]; exact V_half_turn (Or.inl rfl) hv
    · rw [rotAbout_neg_one (by simp [per]) (by simp [per])]; exact V_half_turn (Or.inr rfl) hv
  · intro v hv
    rcases hb with rfl | rfl | rfl | rfl
    · simp only [per, ↓reduceIte]
      exact add_cen1_mem (rot_vT_neg (sub_cen1_mem hv))
    · rw [rotAbout_one (by simp [per]) (by simp [per])]; exact hv
    · rw [rotAbout_neg_one (by simp [per]) (by simp [per])]; exact V_half_turn (Or.inl rfl) hv
    · rw [rotAbout_neg_one (by simp [per]) (by simp [per])]; exact V_half_turn (Or.inr rfl) hv

/-! ## Means -/

lemma sum_map_affine (L : List ℂ) (a c T : ℂ) :
    (L.map fun v => a * (v - c) + T).sum = a * (L.sum - L.length * c) + L.length * T := by
  induction L with
  | nil => simp
  | cons v L ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
    push_cast
    ring

/-- The mean of the placed vertices of a body is its translation. -/
lemma mean_motion (L : List ℂ) (hL : L ≠ []) (φ : ℝ) (T : ℂ) :
    (L.map fun v => motion φ T (v - L.sum / (L.length : ℂ))).sum /
      (((L.map fun v => motion φ T (v - L.sum / (L.length : ℂ))).length : ℕ) : ℂ) = T := by
  rw [List.length_map]
  simp only [motion]
  rw [sum_map_affine]
  have hn : (L.length : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (List.length_pos_iff.2 hL).ne'
  field_simp
  ring

/-- The mean of a nonempty list of points of a convex set lies in the set. -/
lemma mean_mem {K : Set ℂ} (hK : Convex ℝ K) :
    ∀ (L : List ℂ), L ≠ [] → (∀ z ∈ L, z ∈ K) → L.sum / ((L.length : ℕ) : ℂ) ∈ K
  | [], h, _ => absurd rfl h
  | [a], _, h => by simpa using h a (by simp)
  | a :: b :: L, _, h => by
    have hm := mean_mem hK (b :: L) (by simp) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    have ha := h a (by simp)
    have hn : (0 : ℝ) < ((b :: L).length : ℝ) := by simp only [List.length_cons]; positivity
    have hc := hK ha hm (by positivity : (0 : ℝ) ≤ 1 / ((b :: L).length + 1))
      (by positivity : (0 : ℝ) ≤ (b :: L).length / ((b :: L).length + 1)) (by field_simp; ring)
    convert hc using 1
    rw [List.sum_cons, List.length_cons, Complex.real_smul, Complex.real_smul]
    have hn' : ((b :: L).length : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp

/-! ## The reduction -/

/-- **Reduction to the root box** (statement of `WormSound.W1.w1_domain`, with `InDtau` written out). -/
theorem w1_domain' (Ω : Set ℂ) (hΩ : IsConvexCoverM Ω) (hsmall : volume Ω < ENNReal.ofReal (24 / 100)) :
    ∃ Ω' : Set ℂ, Convex ℝ Ω' ∧ volume Ω' = volume Ω ∧ ∃ x : Fin 12 → ℝ,
      ((0 ≤ x 0 ∧ x 0 ≤ Real.pi / 3) ∧ (0 ≤ x 3 ∧ x 3 ≤ 2 * Real.pi) ∧ (0 ≤ x 6 ∧ x 6 ≤ Real.pi) ∧
        (0 ≤ x 9 ∧ x 9 ≤ Real.pi) ∧ ∀ b < 4, |coord x (3 * b + 1)| ≤ 8 * (24 / 100) / Real.sqrt 3 - 1 / 2 ∧
          |coord x (3 * b + 2)| ≤ 2 * (24 / 100)) ∧
      ∀ g < famGid.length, place famArcs famGid x g ∈ Ω' := by
  -- the proper motions of the five bodies
  have hcov : ∀ b : ℕ, ∃ θ : ℝ, ∃ t : ℂ, b < 5 → ∀ v ∈ V b, motion θ t v ∈ Ω := by
    intro b
    by_cases hb : b < 5
    · obtain ⟨θ, t, h⟩ := cover_V hΩ b hb
      exact ⟨θ, t, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hb⟩
  choose θ t hθ using hcov
  have hper1 : per 1 = 2 * Real.pi / 3 := by simp [per]
  -- the angle of body `0`, up to the half-turn
  obtain ⟨α, hαL, hα1⟩ : ∃ α : ℝ, (∀ v ∈ V 0, motion α (t 0) v ∈ Ω) ∧
      toIcoMod (per_pos 1) 0 (θ 1 - α) ≤ Real.pi / 3 := by
    by_cases hr : toIcoMod (per_pos 1) 0 (θ 1 - θ 0) ≤ Real.pi / 3
    · exact ⟨θ 0, hθ 0 (by norm_num), hr⟩
    · refine ⟨θ 0 + Real.pi, fun v hv => ?_, ?_⟩
      · have h := hθ 0 (by norm_num) (-v) (V0_neg hv)
        have e : motion (θ 0 + Real.pi) (t 0) v = motion (θ 0) (t 0) (-v) := by
          simp only [motion]
          rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
          ring
        rw [e]; exact h
      · set r := toIcoMod (per_pos 1) 0 (θ 1 - θ 0) with hrdef
        set n := toIcoDiv (per_pos 1) 0 (θ 1 - θ 0)
        have hrn : θ 1 - θ 0 - n • per 1 = r := self_sub_toIcoDiv_zsmul (per_pos 1) 0 (θ 1 - θ 0)
        have hrI := toIcoMod_mem_Ico' (per_pos 1) (θ 1 - θ 0)
        rw [← hrdef] at hrI
        have e : θ 1 - (θ 0 + Real.pi) = (r - Real.pi / 3) + (n - 1) • per 1 := by
          rw [← hrn, hper1]; simp only [zsmul_eq_mul]; push_cast; ring
        rw [e, toIcoMod_add_zsmul, (toIcoMod_eq_self (per_pos 1)).2]
        · rw [hper1] at hrI; linarith [hrI.2]
        · rw [hper1] at hrI ⊢
          constructor <;> linarith [hrI.2, not_le.1 hr]
  -- the cover in the frame of body `0`
  set Ω' := motion α (t 0) ⁻¹' Ω with hΩ'
  have hconv : Convex ℝ Ω' := convex_preimage_motion α (t 0) hΩ.1
  have hvolΩ' : volume Ω' = volume Ω := volume_preimage_motion α (t 0) Ω
  have hvol : volume Ω' < ENNReal.ofReal (24 / 100) := by rw [hvolΩ']; exact hsmall
  -- the placement
  set φ : ℕ → ℝ := fun b => toIcoMod (per_pos b) 0 (θ b - α) with hφ
  set T : ℕ → ℂ := fun b =>
    Complex.exp ((-α : ℝ) * Complex.I) * (Complex.exp (θ b * Complex.I) * cen b + t b - t 0) with hT
  set x : Fin 12 → ℝ := fun j => if j.val % 3 = 0 then φ (j.val / 3 + 1)
    else if j.val % 3 = 1 then (T (j.val / 3 + 1)).re else (T (j.val / 3 + 1)).im with hx
  -- body `0`
  have hL0 : ∀ v ∈ V 0, v ∈ Ω' := hαL
  -- bodies `1, …, 4`
  have hL : ∀ b, 1 ≤ b → b ≤ 4 → ∀ v ∈ V b, motion (φ b) (T b) (v - cen b) ∈ Ω' := by
    intro b hb1 hb4 v hv
    show motion α (t 0) (motion (φ b) (T b) (v - cen b)) ∈ Ω
    set n := toIcoDiv (per_pos b) 0 (θ b - α)
    have hφb : φ b = θ b - α - n • per b := (self_sub_toIcoDiv_zsmul (per_pos b) 0 (θ b - α)).symm
    have hA : Complex.exp (α * Complex.I) * Complex.exp ((-α : ℝ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero
    have hB : Complex.exp (α * Complex.I) * Complex.exp ((φ b : ℝ) * Complex.I) =
        Complex.exp (θ b * Complex.I) * Complex.exp ((((-n : ℤ) : ℝ) * per b : ℝ) * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add, hφb]
      congr 1
      simp only [zsmul_eq_mul]
      push_cast
      ring
    have e : motion α (t 0) (motion (φ b) (T b) (v - cen b)) =
        motion (θ b) (t b) (rotAbout (((-n : ℤ) : ℝ) * per b) (cen b) v) := by
      simp only [motion, rotAbout, hT]
      linear_combination (v - cen b) * hB + (Complex.exp (θ b * Complex.I) * cen b + t b - t 0) * hA
    rw [e]
    exact hθ b (by omega) _ (body_sym b hb1 hb4 (-n) v hv)
  -- the translations lie in `Ω'`
  have hTmem : ∀ b, 1 ≤ b → b ≤ 4 → T b ∈ Ω' := by
    intro b hb1 hb4
    have hne : V b ≠ [] := List.ne_nil_of_length_pos (by rw [V_length]; omega)
    have h := mean_mem hconv ((V b).map fun v => motion (φ b) (T b) (v - cen b)) (by simpa using hne)
      (fun z hz => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hz
        exact hL b hb1 hb4 v hv)
    rwa [cen, mean_motion (V b) hne (φ b) (T b)] at h
  -- the placed triangle and the unit segment
  have htri : ∀ w ∈ vT, motion (φ 1) (T 1) w ∈ Ω' := by
    intro w hw
    have h := hL 1 le_rfl (by norm_num) _ (add_cen1_mem hw)
    rwa [add_sub_cancel_right] at h
  have hm : ((-(1 / 2) : ℝ) : ℂ) ∈ Ω' := hL0 _ (by rw [V0_eq]; simp)
  have hp : ((1 / 2 : ℝ) : ℂ) ∈ Ω' := hL0 _ (by rw [V0_eq]; simp)
  have hτ : (0 : ℝ) < 24 / 100 := by norm_num
  -- coordinates of the placement
  have hxa : ∀ b, 1 ≤ b → b ≤ 4 → coord x (3 * (b - 1)) = φ b := by
    intro b hb1 hb4
    simp only [coord, hx]
    rw [dite_eq_left (by omega)]
    rw [ite_eq_left (by omega)]
    congr 1; omega
  have hxr : ∀ b, 1 ≤ b → b ≤ 4 → coord x (3 * (b - 1) + 1) = (T b).re := by
    intro b hb1 hb4
    simp only [coord, hx]
    rw [dite_eq_left (by omega)]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 2; omega
  have hxi : ∀ b, 1 ≤ b → b ≤ 4 → coord x (3 * (b - 1) + 2) = (T b).im := by
    intro b hb1 hb4
    simp only [coord, hx]
    rw [dite_eq_left (by omega)]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    congr 2; omega
  refine ⟨Ω', hconv, hvolΩ', x, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have h0 : x 0 = φ 1 := by simp [hx]
    have hI := toIcoMod_mem_Ico' (per_pos 1) (θ 1 - α)
    rw [h0]
    exact ⟨hI.1, hα1⟩
  · have h3 : x 3 = φ 2 := by simp [hx]
    have hI := toIcoMod_mem_Ico' (per_pos 2) (θ 2 - α)
    have hp2 : per 2 = 2 * Real.pi := by simp [per]
    rw [h3]
    exact ⟨hI.1, (hI.2.trans_eq hp2).le⟩
  · have h6 : x 6 = φ 3 := by simp [hx]
    have hI := toIcoMod_mem_Ico' (per_pos 3) (θ 3 - α)
    have hp3 : per 3 = Real.pi := by simp [per]
    rw [h6]
    exact ⟨hI.1, (hI.2.trans_eq hp3).le⟩
  · have h9 : x 9 = φ 4 := by simp [hx]
    have hI := toIcoMod_mem_Ico' (per_pos 4) (θ 4 - α)
    have hp4 : per 4 = Real.pi := by simp [per]
    rw [h9]
    exact ⟨hI.1, (hI.2.trans_eq hp4).le⟩
  · intro b hb
    have hr := hxr (b + 1) (by omega) (by omega)
    have hi := hxi (b + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at hr hi
    rw [hr, hi]
    exact ⟨(re_lt hconv hτ hvol hm hp (φ 1) (T 1) htri (hTmem (b + 1) (by omega) (by omega))).le,
      (im_lt hconv hτ hvol hm hp (hTmem (b + 1) (by omega) (by omega))).le⟩
  · intro g hg
    have hmem : famGid.getD g (0, 0) ∈ famGid := by
      rw [List.getD_eq_getElem _ _ hg]; exact List.getElem_mem hg
    obtain ⟨hb5, hj⟩ := famGid_ok _ hmem
    have hjV : (famGid.getD g (0, 0)).2 < (V (famGid.getD g (0, 0)).1).length := by rw [V_length]; omega
    have hvV : (V (famGid.getD g (0, 0)).1).getD (famGid.getD g (0, 0)).2 0 ∈ V (famGid.getD g (0, 0)).1 := by
      rw [List.getD_eq_getElem _ _ hjV]; exact List.getElem_mem hjV
    have hpl : place famArcs famGid x g =
        if (famGid.getD g (0, 0)).1 = 0 then (V (famGid.getD g (0, 0)).1).getD (famGid.getD g (0, 0)).2 0
        else motion (coord x (3 * ((famGid.getD g (0, 0)).1 - 1)))
          ⟨coord x (3 * ((famGid.getD g (0, 0)).1 - 1) + 1), coord x (3 * ((famGid.getD g (0, 0)).1 - 1) + 2)⟩
          ((V (famGid.getD g (0, 0)).1).getD (famGid.getD g (0, 0)).2 0 - cen (famGid.getD g (0, 0)).1) := by
      unfold place qReal
      dsimp only
      split_ifs <;> rfl
    rw [hpl]
    split_ifs with h0
    · rw [h0] at hvV ⊢
      exact hL0 _ hvV
    · have hb1 : 1 ≤ (famGid.getD g (0, 0)).1 := Nat.one_le_iff_ne_zero.2 h0
      have hb4 : (famGid.getD g (0, 0)).1 ≤ 4 := by omega
      rw [hxa _ hb1 hb4, hxr _ hb1 hb4, hxi _ hb1 hb4, Complex.eta]
      exact hL _ hb1 hb4 _ hvV

end WormCore.Sound.W1Proof
