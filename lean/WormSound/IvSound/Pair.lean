import WormSound.IvSound.Ctx

/-!
# Soundness of the pair and triple bounds of the checker (`pairMove`, `diff`, `det3`, `fanVar`, `fanDetLo`)

For every placement `x` of the box `[lo, hi]` (with `C = mkCtx F lo hi`):

* `pairMove_mem`: some member `r ≥ 0` of `pairMove C a b` bounds the movement of `x_b − x_a` from the centre;
* `mem_diff`: `diff C a b` encloses the centre value of `x_b − x_a`;
* `mem_det3`: `det3 C a b i` encloses `det(x_b − x_a, x_i − x_a)`;
* `fanDetLo_le`: `fanDetLo C z a b · 2⁻⁵⁶ ≤ det(x_a − z, x_b − z)` for the fan centre `z = (zx + i zy) · 2⁻⁵⁶`.
-/

open MoserWorm Complex

namespace WormCore

namespace IvSound

open WormCore.Sound (InBox)

variable {F : Fam} {q : Nat → ℂ} {lo hi : Array Int}

@[simp] theorem mkCtx_F : (mkCtx F lo hi).F = F := rfl

/-- The fan centre `(zx + i zy) · 2⁻⁵⁶`. -/
noncomputable def fanCentre (zx zy : Int) : ℂ :=
  ((zx : ℝ) / 2 ^ dfxS : ℝ) + ((zy : ℝ) / 2 ^ dfxS : ℝ) * I

theorem mem_fanCentre (zx zy : Int) : V2.Mem (DIval.pt zx, DIval.pt zy) (fanCentre zx zy) := by
  refine ⟨?_, ?_⟩
  · have e : (fanCentre zx zy).re = (zx : ℝ) / 2 ^ dfxS := by
      simp only [fanCentre, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, mul_one, add_zero, sub_self]
    rw [e]; exact DIval.mem_pt zx
  · have e : (fanCentre zx zy).im = (zy : ℝ) / 2 ^ dfxS := by
      simp only [fanCentre, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, mul_one, zero_add, add_zero]
    rw [e]; exact DIval.mem_pt zy

lemma mem_zero_pt : (0 : ℝ) ∈ DIval.pt 0 := by simpa using DIval.mem_pt 0

/-- A member of `MV[g]` bounds the movement of `g` on the box. -/
theorem MV_mem (hF : FamSpec F q) {g : Nat} (hg : g < F.body.size) {x : Fin 12 → ℝ} (hx : InBox lo hi x) :
    ∃ r ∈ (mkCtx F lo hi).MV[g]!, 0 ≤ r ∧ ‖pos F q x g - posC F q lo hi g‖ ≤ r := by
  rw [ctx_MV hg]
  unfold pos posC
  split_ifs with h0
  · exact ⟨0, mem_zero_pt, le_rfl, by simp⟩
  · have hb1 : 1 ≤ F.body[g]! := by omega
    have hbk := hF.body_le g hg
    have hb4 := hbk.trans hF.k_le
    rw [ctx_bd hb1 hbk]
    set b := F.body[g]!
    have hθ := abs_angle_sub_le hx hb1 hb4
    have hh : 0 ≤ ((bodyData lo hi b).h : ℝ) / 2 ^ dfxS := (abs_nonneg _).trans hθ
    refine ⟨‖q g‖ * (((bodyData lo hi b).h : ℝ) / 2 ^ dfxS) + transRad lo hi b,
      DIval.mem_add (DIval.mem_mul (hF.qn_mem g hg) (DIval.mem_pt _)) (mem_transRad lo hi b),
      add_nonneg (mul_nonneg (norm_nonneg _) hh) (transRad_nonneg _ _ _), ?_⟩
    calc ‖bodyTrans x b + exp (bodyAngle x b * I) * q g - (centreTrans lo hi b + exp (centreAngle lo hi b * I) * q g)‖
        ≤ ‖q g‖ * |bodyAngle x b - centreAngle lo hi b| + ‖bodyTrans x b - centreTrans lo hi b‖ :=
          Move.norm_place_sub_le _ _ _ _ _
      _ ≤ ‖q g‖ * (((bodyData lo hi b).h : ℝ) / 2 ^ dfxS) + transRad lo hi b := by
          gcongr
          exact norm_trans_sub_le_rad hx hb1 hb4

/-- Positions on one moving body. -/
lemma pos_of_body {g : Nat} {x : Fin 12 → ℝ} (h0 : F.body[g]! ≠ 0) :
    pos F q x g = bodyTrans x F.body[g]! + exp (bodyAngle x F.body[g]! * I) * q g := by
  simp [pos, h0]

lemma posC_of_body {g : Nat} (h0 : F.body[g]! ≠ 0) :
    posC F q lo hi g = centreTrans lo hi F.body[g]! + exp (centreAngle lo hi F.body[g]! * I) * q g := by
  simp [posC, h0]

lemma pos_of_body0 {g : Nat} {x : Fin 12 → ℝ} (h0 : F.body[g]! = 0) : pos F q x g = q g := by simp [pos, h0]
lemma posC_of_body0 {g : Nat} (h0 : F.body[g]! = 0) : posC F q lo hi g = q g := by simp [posC, h0]

/-! ### The three cases of the pair and triple bounds -/

section Cases

variable {a b i : Nat}

lemma pairMove_fixed (hab : F.body[a]! = F.body[b]!) (h0 : F.body[a]! = 0) :
    pairMove (mkCtx F lo hi) a b = DIval.pt 0 := by
  dsimp only [pairMove]
  split_ifs with h1 h2
  · rfl
  · exact absurd h0 h2
  · exact absurd hab h1

lemma pairMove_moving (hab : F.body[a]! = F.body[b]!) (h0 : F.body[a]! ≠ 0) :
    pairMove (mkCtx F lo hi) a b =
      (V2.norm (V2.sub F.q[b]! F.q[a]!)).mul (DIval.pt (mkCtx F lo hi).bd[F.body[a]!]!.h) := by
  dsimp only [pairMove]
  split_ifs with h1 h2
  · exact absurd h2 h0
  · rfl
  · exact absurd hab h1

lemma pairMove_two (hab : F.body[a]! ≠ F.body[b]!) :
    pairMove (mkCtx F lo hi) a b = (mkCtx F lo hi).MV[a]!.add (mkCtx F lo hi).MV[b]! := by
  simp only [pairMove, mkCtx_F, hab, ite_false]

lemma diff_moving (hab : F.body[a]! = F.body[b]!) (h0 : F.body[a]! ≠ 0) :
    diff (mkCtx F lo hi) a b =
      V2.rot (mkCtx F lo hi).bd[F.body[a]!]!.s (mkCtx F lo hi).bd[F.body[a]!]!.c (V2.sub F.q[b]! F.q[a]!) := by
  dsimp only [diff]
  split_ifs with h1
  · rfl
  · exact absurd ⟨hab, h0⟩ h1

lemma diff_other (h : ¬ (F.body[a]! = F.body[b]! ∧ F.body[a]! ≠ 0)) :
    diff (mkCtx F lo hi) a b = V2.sub (mkCtx F lo hi).X0[b]! (mkCtx F lo hi).X0[a]! := by
  dsimp only [diff]
  split_ifs with h1
  · exact absurd h1 h
  · rfl

lemma det3_one (hab : F.body[a]! = F.body[b]!) (hai : F.body[a]! = F.body[i]!) :
    det3 (mkCtx F lo hi) a b i = V2.det (V2.sub F.q[b]! F.q[a]!) (V2.sub F.q[i]! F.q[a]!) := by
  dsimp only [det3]
  split_ifs with h1
  · rfl
  · exact absurd ⟨hab, hai⟩ h1

lemma det3_other (h : ¬ (F.body[a]! = F.body[b]! ∧ F.body[a]! = F.body[i]!)) :
    det3 (mkCtx F lo hi) a b i =
      ⟨((V2.det (diff (mkCtx F lo hi) a b) (diff (mkCtx F lo hi) a i)).sub
          ((((pairMove (mkCtx F lo hi) a b).mul (V2.norm (diff (mkCtx F lo hi) a i))).add
            ((pairMove (mkCtx F lo hi) a i).mul (V2.norm (diff (mkCtx F lo hi) a b)))).add
            ((pairMove (mkCtx F lo hi) a b).mul (pairMove (mkCtx F lo hi) a i)))).lo,
        ((V2.det (diff (mkCtx F lo hi) a b) (diff (mkCtx F lo hi) a i)).add
          ((((pairMove (mkCtx F lo hi) a b).mul (V2.norm (diff (mkCtx F lo hi) a i))).add
            ((pairMove (mkCtx F lo hi) a i).mul (V2.norm (diff (mkCtx F lo hi) a b)))).add
            ((pairMove (mkCtx F lo hi) a b).mul (pairMove (mkCtx F lo hi) a i)))).hi⟩ := by
  dsimp only [det3]
  split_ifs with h1
  · exact absurd h1 h
  · rfl

lemma fanVar_fixed (z : V2) (hab : F.body[a]! = F.body[b]!) (h0 : F.body[a]! = 0) :
    fanVar (mkCtx F lo hi) z a b = DIval.pt 0 := by
  dsimp only [fanVar]
  split_ifs with h1 h2
  · rfl
  · exact absurd h0 h2
  · exact absurd hab h1

lemma fanVar_moving (z : V2) (hab : F.body[a]! = F.body[b]!) (h0 : F.body[a]! ≠ 0) :
    fanVar (mkCtx F lo hi) z a b =
      (V2.norm (V2.sub F.q[b]! F.q[a]!)).mul
        (((mkCtx F lo hi).bd[F.body[a]!]!.trad.mul ((DIval.ofInt 1).add (DIval.pt (mkCtx F lo hi).bd[F.body[a]!]!.h))).add
          ((V2.norm (V2.sub (mkCtx F lo hi).bd[F.body[a]!]!.tc z)).mul (DIval.pt (mkCtx F lo hi).bd[F.body[a]!]!.h))) := by
  dsimp only [fanVar]
  split_ifs with h1 h2
  · exact absurd h2 h0
  · rfl
  · exact absurd hab h1

lemma fanVar_two (z : V2) (hab : F.body[a]! ≠ F.body[b]!) :
    fanVar (mkCtx F lo hi) z a b =
      ((mkCtx F lo hi).MV[a]!.mul ((V2.norm (V2.sub (mkCtx F lo hi).X0[b]! z)).add (mkCtx F lo hi).MV[b]!)).add
        ((V2.norm (V2.sub (mkCtx F lo hi).X0[a]! z)).mul (mkCtx F lo hi).MV[b]!) := by
  simp only [fanVar, mkCtx_F, hab, ite_false]

end Cases

/-- **pairMove.** -/
theorem pairMove_mem (hF : FamSpec F q) {a b : Nat} (ha : a < F.body.size) (hb : b < F.body.size)
    {x : Fin 12 → ℝ} (hx : InBox lo hi x) :
    ∃ r ∈ pairMove (mkCtx F lo hi) a b, 0 ≤ r ∧
      ‖(pos F q x b - pos F q x a) - (posC F q lo hi b - posC F q lo hi a)‖ ≤ r := by
  by_cases hab : F.body[a]! = F.body[b]!
  · by_cases h0 : F.body[a]! = 0
    · -- one fixed body: nothing moves
      rw [pairMove_fixed hab h0]
      refine ⟨0, mem_zero_pt, le_rfl, ?_⟩
      rw [pos_of_body0 h0, pos_of_body0 (hab ▸ h0), posC_of_body0 h0, posC_of_body0 (hab ▸ h0)]
      simp
    · -- one moving body: `x_b − x_a` only rotates
      rw [pairMove_moving hab h0]
      have hb1 : 1 ≤ F.body[a]! := by omega
      have hbk := hF.body_le a ha
      have hb4 := hbk.trans hF.k_le
      rw [ctx_bd hb1 hbk]
      have hθ := abs_angle_sub_le hx hb1 hb4
      have hh : 0 ≤ ((bodyData lo hi F.body[a]!).h : ℝ) / 2 ^ dfxS := (abs_nonneg _).trans hθ
      refine ⟨‖q b - q a‖ * (((bodyData lo hi F.body[a]!).h : ℝ) / 2 ^ dfxS),
        DIval.mem_mul (V2.mem_norm (V2.mem_sub (hF.q_mem b hb) (hF.q_mem a ha))) (DIval.mem_pt _),
        mul_nonneg (norm_nonneg _) hh, ?_⟩
      have h0b : F.body[b]! ≠ 0 := hab ▸ h0
      have e1 : pos F q x b - pos F q x a = exp (bodyAngle x F.body[a]! * I) * (q b - q a) := by
        rw [pos_of_body h0, pos_of_body h0b, ← hab, Move.place_sub_same_body]
      have e2 : posC F q lo hi b - posC F q lo hi a = exp (centreAngle lo hi F.body[a]! * I) * (q b - q a) := by
        rw [posC_of_body h0, posC_of_body h0b, ← hab, Move.place_sub_same_body]
      rw [e1, e2]
      calc ‖exp (bodyAngle x F.body[a]! * I) * (q b - q a) - exp (centreAngle lo hi F.body[a]! * I) * (q b - q a)‖
          ≤ ‖q b - q a‖ * |bodyAngle x F.body[a]! - centreAngle lo hi F.body[a]!| := Move.norm_rot_sub_le _ _ _
        _ ≤ _ := by gcongr
  · -- two bodies: the sum of the two movement bounds
    rw [pairMove_two hab]
    obtain ⟨ra, hra, hra0, hma⟩ := MV_mem hF ha hx
    obtain ⟨rb, hrb, hrb0, hmb⟩ := MV_mem hF hb hx
    refine ⟨ra + rb, DIval.mem_add hra hrb, add_nonneg hra0 hrb0, ?_⟩
    have e : (pos F q x b - pos F q x a) - (posC F q lo hi b - posC F q lo hi a) =
        (pos F q x b - posC F q lo hi b) - (pos F q x a - posC F q lo hi a) := by ring
    rw [e]
    calc ‖(pos F q x b - posC F q lo hi b) - (pos F q x a - posC F q lo hi a)‖
        ≤ ‖pos F q x b - posC F q lo hi b‖ + ‖pos F q x a - posC F q lo hi a‖ := norm_sub_le _ _
      _ ≤ rb + ra := add_le_add hmb hma
      _ = ra + rb := add_comm _ _

/-- **diff.** -/
theorem mem_diff (hF : FamSpec F q) (hB : BoxOK lo hi) {a b : Nat} (ha : a < F.body.size) (hb : b < F.body.size) :
    V2.Mem (diff (mkCtx F lo hi) a b) (posC F q lo hi b - posC F q lo hi a) := by
  by_cases h : F.body[a]! = F.body[b]! ∧ F.body[a]! ≠ 0
  · obtain ⟨hab, h0⟩ := h
    rw [diff_moving hab h0]
    have hb1 : 1 ≤ F.body[a]! := by omega
    have hbk := hF.body_le a ha
    have hb4 := hbk.trans hF.k_le
    have h0b : F.body[b]! ≠ 0 := hab ▸ h0
    have e : posC F q lo hi b - posC F q lo hi a = exp (centreAngle lo hi F.body[a]! * I) * (q b - q a) := by
      rw [posC_of_body h0, posC_of_body h0b, ← hab, Move.place_sub_same_body]
    rw [e, ctx_bd hb1 hbk]
    obtain ⟨hlo, hhi⟩ := hB.2 _ hb1 hb4
    obtain ⟨hs, hc⟩ := mem_centre_sincos (lo := lo) (hi := hi) F.body[a]! hlo hhi
    exact V2.mem_rot hs hc (V2.mem_sub (hF.q_mem b hb) (hF.q_mem a ha))
  · rw [diff_other h]
    exact V2.mem_sub (mem_X0 hF hB hb) (mem_X0 hF hB ha)

/-- Membership in an interval with given ends. -/
lemma mem_mk {l h : Int} {r : ℝ} (hl : (l : ℝ) / 2 ^ dfxS ≤ r) (hh : r ≤ (h : ℝ) / 2 ^ dfxS) :
    r ∈ (⟨l, h⟩ : DIval) := by
  rw [DIval.mem_iff_val]; exact ⟨hl, hh⟩

/-- **det3.** -/
theorem mem_det3 (hF : FamSpec F q) (hB : BoxOK lo hi) {a b i : Nat} (ha : a < F.body.size) (hb : b < F.body.size)
    (hi' : i < F.body.size) {x : Fin 12 → ℝ} (hx : InBox lo hi x) :
    Move.det (pos F q x b - pos F q x a) (pos F q x i - pos F q x a) ∈ det3 (mkCtx F lo hi) a b i := by
  by_cases h : F.body[a]! = F.body[b]! ∧ F.body[a]! = F.body[i]!
  · -- three points of one body: the determinant does not move
    obtain ⟨hab, hai⟩ := h
    rw [det3_one hab hai]
    have e : Move.det (pos F q x b - pos F q x a) (pos F q x i - pos F q x a) = Move.det (q b - q a) (q i - q a) := by
      by_cases h0 : F.body[a]! = 0
      · rw [pos_of_body0 h0, pos_of_body0 (hab ▸ h0), pos_of_body0 (hai ▸ h0)]
      · rw [pos_of_body h0, pos_of_body (hab ▸ h0), pos_of_body (hai ▸ h0), ← hab, ← hai, Move.det_same_body]
    rw [e]
    exact V2.mem_det (V2.mem_sub (hF.q_mem b hb) (hF.q_mem a ha)) (V2.mem_sub (hF.q_mem i hi') (hF.q_mem a ha))
  · -- centre value and perturbation
    rw [det3_other h]
    have hu := mem_diff hF hB ha hb
    have hv := mem_diff hF hB ha hi'
    obtain ⟨r1, hr1, hr10, hm1⟩ := pairMove_mem hF ha hb hx
    obtain ⟨r2, hr2, hr20, hm2⟩ := pairMove_mem hF ha hi' hx
    set U0 := posC F q lo hi b - posC F q lo hi a with hU0
    set V0 := posC F q lo hi i - posC F q lo hi a with hV0
    set U := pos F q x b - pos F q x a with hU
    set V := pos F q x i - pos F q x a with hV
    have hR := DIval.mem_add (DIval.mem_add (DIval.mem_mul hr1 (V2.mem_norm hv)) (DIval.mem_mul hr2 (V2.mem_norm hu)))
        (DIval.mem_mul hr1 hr2)
    have hD := V2.mem_det hu hv
    have hbound : |Move.det U V - Move.det U0 V0| ≤ r1 * ‖V0‖ + r2 * ‖U0‖ + r1 * r2 := by
      refine (Move.abs_det_sub_le U0 U V0 V).trans ?_
      calc ‖U - U0‖ * (‖V0‖ + ‖V - V0‖) + ‖U0‖ * ‖V - V0‖ ≤ r1 * (‖V0‖ + r2) + ‖U0‖ * r2 := by
            gcongr
        _ = r1 * ‖V0‖ + r2 * ‖U0‖ + r1 * r2 := by ring
    have hlo := lo_le (DIval.mem_sub hD hR)
    have hhi := le_hi (DIval.mem_add hD hR)
    rw [abs_le] at hbound
    refine mem_mk ?_ ?_
    · simp only [Move.det] at hlo hbound ⊢; linarith
    · simp only [Move.det] at hhi hbound ⊢; linarith

/-- **fanDetLo.** -/
theorem fanDetLo_le (hF : FamSpec F q) (hB : BoxOK lo hi) {a b : Nat} (ha : a < F.body.size) (hb : b < F.body.size)
    {x : Fin 12 → ℝ} (hx : InBox lo hi x) (zx zy : Int) :
    ((fanDetLo (mkCtx F lo hi) (DIval.pt zx, DIval.pt zy) a b : Int) : ℝ) / 2 ^ dfxS ≤
      Move.det (pos F q x a - fanCentre zx zy) (pos F q x b - fanCentre zx zy) := by
  set z := fanCentre zx zy
  have hz := mem_fanCentre zx zy
  have hxa : V2.Mem (V2.sub (mkCtx F lo hi).X0[a]! (DIval.pt zx, DIval.pt zy)) (posC F q lo hi a - z) :=
    V2.mem_sub (mem_X0 hF hB ha) hz
  have hxb : V2.Mem (V2.sub (mkCtx F lo hi).X0[b]! (DIval.pt zx, DIval.pt zy)) (posC F q lo hi b - z) :=
    V2.mem_sub (mem_X0 hF hB hb) hz
  have hD := V2.mem_det hxa hxb
  -- a member of `fanVar` bounding the movement of the determinant
  have hvar : ∃ r ∈ fanVar (mkCtx F lo hi) (DIval.pt zx, DIval.pt zy) a b,
      |Move.det (pos F q x a - z) (pos F q x b - z) - Move.det (posC F q lo hi a - z) (posC F q lo hi b - z)| ≤ r := by
    by_cases hab : F.body[a]! = F.body[b]!
    · by_cases h0 : F.body[a]! = 0
      · rw [fanVar_fixed _ hab h0]
        refine ⟨0, mem_zero_pt, ?_⟩
        rw [pos_of_body0 h0, pos_of_body0 (hab ▸ h0), posC_of_body0 h0, posC_of_body0 (hab ▸ h0)]
        simp
      · rw [fanVar_moving _ hab h0]
        have hb1 : 1 ≤ F.body[a]! := by omega
        have hbk := hF.body_le a ha
        have hb4 := hbk.trans hF.k_le
        have h0b : F.body[b]! ≠ 0 := hab ▸ h0
        rw [ctx_bd hb1 hbk]
        have hθ := abs_angle_sub_le hx hb1 hb4
        have hh : 0 ≤ ((bodyData lo hi F.body[a]!).h : ℝ) / 2 ^ dfxS := (abs_nonneg _).trans hθ
        have htz : ‖centreTrans lo hi F.body[a]! - z‖ ∈
            V2.norm (V2.sub (bodyData lo hi F.body[a]!).tc (DIval.pt zx, DIval.pt zy)) :=
          V2.mem_norm (V2.mem_sub (mem_centreTrans F.body[a]!) hz)
        have hw : ‖q b - q a‖ ∈ V2.norm (V2.sub F.q[b]! F.q[a]!) :=
          V2.mem_norm (V2.mem_sub (hF.q_mem b hb) (hF.q_mem a ha))
        have hone : (1 : ℝ) ∈ DIval.ofInt 1 := by simpa using DIval.mem_ofInt 1
        refine ⟨‖q b - q a‖ * (transRad lo hi F.body[a]! * (1 + ((bodyData lo hi F.body[a]!).h : ℝ) / 2 ^ dfxS) +
            ‖centreTrans lo hi F.body[a]! - z‖ * (((bodyData lo hi F.body[a]!).h : ℝ) / 2 ^ dfxS)),
          DIval.mem_mul hw (DIval.mem_add (DIval.mem_mul (mem_transRad lo hi F.body[a]!)
            (DIval.mem_add hone (DIval.mem_pt _))) (DIval.mem_mul htz (DIval.mem_pt _))), ?_⟩
        have e1 : pos F q x a = bodyTrans x F.body[a]! + exp (bodyAngle x F.body[a]! * I) * q a := pos_of_body h0
        have e2 : pos F q x b = bodyTrans x F.body[a]! + exp (bodyAngle x F.body[a]! * I) * q b := by
          rw [pos_of_body h0b, ← hab]
        have e3 : posC F q lo hi a = centreTrans lo hi F.body[a]! + exp (centreAngle lo hi F.body[a]! * I) * q a :=
          posC_of_body h0
        have e4 : posC F q lo hi b = centreTrans lo hi F.body[a]! + exp (centreAngle lo hi F.body[a]! * I) * q b := by
          rw [posC_of_body h0b, ← hab]
        rw [e1, e2, e3, e4]
        refine (Move.abs_det_fan_same_body_sub_le _ _ _ _ _ _ _).trans ?_
        have ht := norm_trans_sub_le_rad hx hb1 hb4
        have hr0 := transRad_nonneg lo hi F.body[a]!
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        nlinarith [norm_nonneg (centreTrans lo hi F.body[a]! - z),
          abs_nonneg (bodyAngle x F.body[a]! - centreAngle lo hi F.body[a]!)]
    · rw [fanVar_two _ hab]
      obtain ⟨ra, hra, hra0, hma⟩ := MV_mem hF ha hx
      obtain ⟨rb, hrb, hrb0, hmb⟩ := MV_mem hF hb hx
      refine ⟨ra * (‖posC F q lo hi b - z‖ + rb) + ‖posC F q lo hi a - z‖ * rb,
        DIval.mem_add (DIval.mem_mul hra (DIval.mem_add (V2.mem_norm hxb) hrb)) (DIval.mem_mul (V2.mem_norm hxa) hrb),
        ?_⟩
      refine (Move.abs_det_sub_le _ _ _ _).trans ?_
      have e1 : pos F q x a - z - (posC F q lo hi a - z) = pos F q x a - posC F q lo hi a := by ring
      have e2 : pos F q x b - z - (posC F q lo hi b - z) = pos F q x b - posC F q lo hi b := by ring
      rw [e1, e2]
      gcongr
  obtain ⟨r, hr, hbound⟩ := hvar
  have hlo := lo_le (DIval.mem_sub hD hr)
  rw [abs_le] at hbound
  unfold fanDetLo
  simp only [Move.det] at hlo hbound ⊢
  linarith

end IvSound

end WormCore
