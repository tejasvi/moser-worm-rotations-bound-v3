import WormSound.IvSound.Body
import WormSound.IvSound.Move

/-!
# The exact placement and the soundness of the per-leaf context (`WormCore.mkCtx`)

* `FamSpec F q`: the checker's family `F` encloses the exact body-frame points `q g` (and their moduli);
* `pos F q x g`: the position of global vertex `g` at the placement `x` (body `0` fixed, body `b ≥ 1` at
  `t_b + e^{iθ_b} q g`); `posC F q lo hi g`: the same at the centre of the box `[lo, hi]` (`centrePt`, a point of the
  box);
* `mem_X0`: `X0[g]` encloses `posC g`; `MV_bound`: `‖pos x g − posC g‖ ≤ MV[g].hi · 2⁻⁵⁶` for every `x` of the box.
-/

open MoserWorm Complex

namespace WormCore

namespace IvSound

open WormCore.Sound (InBox)

/-- The exact family: `q g` is the body-frame point of global vertex `g`, enclosed by the checker's data. -/
structure FamSpec (F : Fam) (q : Nat → ℂ) : Prop where
  q_size : F.q.size = F.body.size
  qn_size : F.qn.size = F.body.size
  q_mem : ∀ g < F.body.size, V2.Mem F.q[g]! (q g)
  qn_mem : ∀ g < F.body.size, ‖q g‖ ∈ F.qn[g]!
  body_le : ∀ g < F.body.size, F.body[g]! ≤ F.k
  k_le : F.k ≤ 4

/-- The position of global vertex `g` at the placement `x`. -/
noncomputable def pos (F : Fam) (q : Nat → ℂ) (x : Fin 12 → ℝ) (g : Nat) : ℂ :=
  if F.body[g]! = 0 then q g else bodyTrans x F.body[g]! + exp (bodyAngle x F.body[g]! * I) * q g

/-- The position of global vertex `g` at the centre of the box. -/
noncomputable def posC (F : Fam) (q : Nat → ℂ) (lo hi : Array Int) (g : Nat) : ℂ :=
  if F.body[g]! = 0 then q g
  else centreTrans lo hi F.body[g]! + exp (centreAngle lo hi F.body[g]! * I) * q g

/-- Box shape: `lo ≤ hi` on the twelve coordinates, and centre angle mantissas within `±64` (for `sincosIv`). -/
def BoxOK (lo hi : Array Int) : Prop :=
  (∀ j < 12, lo[j]! ≤ hi[j]!) ∧
    ∀ b, 1 ≤ b → b ≤ 4 →
      -(64 * dfxOne) ≤ toLo ((lo[3 * (b - 1)]! + hi[3 * (b - 1)]!).fdiv 2) ∧
        toHi ((lo[3 * (b - 1)]! + hi[3 * (b - 1)]!).fdiv 2) ≤ 64 * dfxOne

/-- The centre of the box: every coordinate at its floor midpoint. -/
noncomputable def centrePt (lo hi : Array Int) : Fin 12 → ℝ :=
  fun j => (((lo[j.val]! + hi[j.val]!).fdiv 2 : Int) : ℝ) / 2 ^ BS

variable {F : Fam} {q : Nat → ℂ} {lo hi : Array Int}

theorem centrePt_inBox (hB : BoxOK lo hi) : InBox lo hi (centrePt lo hi) := by
  intro j
  obtain ⟨h1, h2⟩ := fdiv2_mem (hB.1 j.val j.isLt)
  constructor
  · show (lo[j.val]! : ℝ) / 2 ^ BS ≤ (((lo[j.val]! + hi[j.val]!).fdiv 2 : Int) : ℝ) / 2 ^ BS
    gcongr
  · show (((lo[j.val]! + hi[j.val]!).fdiv 2 : Int) : ℝ) / 2 ^ BS ≤ (hi[j.val]! : ℝ) / 2 ^ BS
    gcongr

theorem bodyAngle_centrePt {b : Nat} (hb1 : 1 ≤ b) (hb : b ≤ 4) :
    bodyAngle (centrePt lo hi) b = centreAngle lo hi b := by
  have hj : 3 * (b - 1) < 12 := by omega
  simp only [bodyAngle, hj, dite_true, centreAngle, centrePt]

theorem bodyTrans_centrePt {b : Nat} (hb1 : 1 ≤ b) (hb : b ≤ 4) :
    bodyTrans (centrePt lo hi) b = centreTrans lo hi b := by
  have hj1 : 3 * (b - 1) + 1 < 12 := by omega
  have hj2 : 3 * (b - 1) + 2 < 12 := by omega
  simp only [bodyTrans, hj1, hj2, dite_true, centreTrans, centrePt]

theorem pos_centrePt (hF : FamSpec F q) {g : Nat} (hg : g < F.body.size) :
    pos F q (centrePt lo hi) g = posC F q lo hi g := by
  unfold pos posC
  split_ifs with h0
  · rfl
  · have hb := (hF.body_le g hg).trans hF.k_le
    rw [bodyAngle_centrePt (by omega) hb, bodyTrans_centrePt (by omega) hb]

/-! ### The arrays of the context -/

theorem ctx_bd {b : Nat} (hb1 : 1 ≤ b) (hb : b ≤ F.k) : (mkCtx F lo hi).bd[b]! = bodyData lo hi b := by
  have hb' : b < F.k + 1 := by omega
  simp [mkCtx, hb', show b ≠ 0 by omega]

theorem ctx_RQ {g : Nat} (hg : g < F.body.size) :
    (mkCtx F lo hi).RQ[g]! = if F.body[g]! = 0 then F.q[g]!
      else V2.rot (mkCtx F lo hi).bd[F.body[g]!]!.s (mkCtx F lo hi).bd[F.body[g]!]!.c F.q[g]! := by
  simp [mkCtx, hg]

theorem ctx_X0 {g : Nat} (hg : g < F.body.size) :
    (mkCtx F lo hi).X0[g]! = if F.body[g]! = 0 then F.q[g]!
      else V2.add (mkCtx F lo hi).bd[F.body[g]!]!.tc (mkCtx F lo hi).RQ[g]! := by
  simp [mkCtx, hg]

theorem ctx_MV {g : Nat} (hg : g < F.body.size) :
    (mkCtx F lo hi).MV[g]! = if F.body[g]! = 0 then DIval.pt 0
      else (F.qn[g]!.mul (DIval.pt (mkCtx F lo hi).bd[F.body[g]!]!.h)).add (mkCtx F lo hi).bd[F.body[g]!]!.trad := by
  simp [mkCtx, hg]

/-! ### Soundness -/

/-- `X0[g]` encloses the centre position. -/
theorem mem_X0 (hF : FamSpec F q) (hB : BoxOK lo hi) {g : Nat} (hg : g < F.body.size) :
    V2.Mem (mkCtx F lo hi).X0[g]! (posC F q lo hi g) := by
  rw [ctx_X0 hg]
  unfold posC
  split_ifs with h0
  · exact hF.q_mem g hg
  · have hb1 : 1 ≤ F.body[g]! := by omega
    have hbk := hF.body_le g hg
    have hb4 := hbk.trans hF.k_le
    rw [ctx_RQ hg, ite_eq_right h0, ctx_bd hb1 hbk]
    obtain ⟨hlo, hhi⟩ := hB.2 _ hb1 hb4
    obtain ⟨hs, hc⟩ := mem_centre_sincos (lo := lo) (hi := hi) F.body[g]! hlo hhi
    exact V2.mem_add (mem_centreTrans _) (V2.mem_rot hs hc (hF.q_mem g hg))

/-- `RQ[g]` encloses the centre rotation of `q g` (moving bodies). -/
theorem mem_RQ (hF : FamSpec F q) (hB : BoxOK lo hi) {g : Nat} (hg : g < F.body.size) (h0 : F.body[g]! ≠ 0) :
    V2.Mem (mkCtx F lo hi).RQ[g]! (exp (centreAngle lo hi F.body[g]! * I) * q g) := by
  have hb1 : 1 ≤ F.body[g]! := by omega
  have hbk := hF.body_le g hg
  have hb4 := hbk.trans hF.k_le
  rw [ctx_RQ hg, ite_eq_right h0, ctx_bd hb1 hbk]
  obtain ⟨hlo, hhi⟩ := hB.2 _ hb1 hb4
  obtain ⟨hs, hc⟩ := mem_centre_sincos (lo := lo) (hi := hi) F.body[g]! hlo hhi
  exact V2.mem_rot hs hc (hF.q_mem g hg)

/-- The upper end of an interval bounds its members. -/
lemma le_hi {I : DIval} {r : ℝ} (h : r ∈ I) : r ≤ (I.hi : ℝ) / 2 ^ dfxS := by
  have := (DIval.mem_iff_val.mp h).2
  simpa [DIval.val] using this

/-- The lower end of an interval bounds its members. -/
lemma lo_le {I : DIval} {r : ℝ} (h : r ∈ I) : (I.lo : ℝ) / 2 ^ dfxS ≤ r := by
  have := (DIval.mem_iff_val.mp h).1
  simpa [DIval.val] using this

/-- The angle half-width is nonnegative. -/
lemma bodyData_h_nonneg (hB : BoxOK lo hi) {b : Nat} (hb1 : 1 ≤ b) (hb : b ≤ 4) : 0 ≤ (bodyData lo hi b).h := by
  have hj : 3 * (b - 1) < 12 := by omega
  obtain ⟨h1, h2⟩ := fdiv2_mem (hB.1 _ hj)
  have hm : 0 ≤ max (hi[3 * (b - 1)]! - (lo[3 * (b - 1)]! + hi[3 * (b - 1)]!).fdiv 2)
      ((lo[3 * (b - 1)]! + hi[3 * (b - 1)]!).fdiv 2 - lo[3 * (b - 1)]!) := le_max_of_le_left (by omega)
  have := le_toHi (max (hi[3 * (b - 1)]! - (lo[3 * (b - 1)]! + hi[3 * (b - 1)]!).fdiv 2)
      ((lo[3 * (b - 1)]! + hi[3 * (b - 1)]!).fdiv 2 - lo[3 * (b - 1)]!))
  have h0 : (0 : ℝ) ≤ ((max (hi[3 * (b - 1)]! - (lo[3 * (b - 1)]! + hi[3 * (b - 1)]!).fdiv 2)
      ((lo[3 * (b - 1)]! + hi[3 * (b - 1)]!).fdiv 2 - lo[3 * (b - 1)]!) : Int) : ℝ) / 2 ^ BS := by
    apply div_nonneg _ (by positivity); exact_mod_cast hm
  have h3 : (0 : ℝ) ≤ ((bodyData lo hi b).h : ℝ) / 2 ^ dfxS := h0.trans this
  have h4 : (0 : ℝ) ≤ ((bodyData lo hi b).h : ℝ) := by
    have := mul_nonneg h3 (le_of_lt two_pow_dfxS_pos)
    rwa [div_mul_cancel₀ _ two_pow_dfxS_pos.ne'] at this
  exact_mod_cast h4

/-- **Movement bound.** `‖pos x g − posC g‖ ≤ MV[g].hi · 2⁻⁵⁶` on the box. -/
theorem MV_bound (hF : FamSpec F q) {g : Nat} (hg : g < F.body.size) {x : Fin 12 → ℝ}
    (hx : InBox lo hi x) :
    ‖pos F q x g - posC F q lo hi g‖ ≤ ((mkCtx F lo hi).MV[g]!.hi : ℝ) / 2 ^ dfxS := by
  rw [ctx_MV hg]
  unfold pos posC
  split_ifs with h0
  · simp [DIval.pt]
  · have hb1 : 1 ≤ F.body[g]! := by omega
    have hbk := hF.body_le g hg
    have hb4 := hbk.trans hF.k_le
    rw [ctx_bd hb1 hbk]
    set b := F.body[g]!
    have hθ := abs_angle_sub_le hx hb1 hb4
    have ht := norm_trans_sub_le hx hb1 hb4
    have hmov := Move.norm_place_sub_le (bodyAngle x b) (centreAngle lo hi b) (bodyTrans x b) (centreTrans lo hi b) (q g)
    have hmul : ‖q g‖ * (((bodyData lo hi b).h : ℝ) / 2 ^ dfxS) ∈ F.qn[g]!.mul (DIval.pt (bodyData lo hi b).h) :=
      DIval.mem_mul (hF.qn_mem g hg) (DIval.mem_pt _)
    have hm := le_hi hmul
    have hq0 : 0 ≤ ‖q g‖ := norm_nonneg _
    have e : (((F.qn[g]!.mul (DIval.pt (bodyData lo hi b).h)).add (bodyData lo hi b).trad).hi : ℝ) / 2 ^ dfxS =
        ((F.qn[g]!.mul (DIval.pt (bodyData lo hi b).h)).hi : ℝ) / 2 ^ dfxS + ((bodyData lo hi b).trad.hi : ℝ) / 2 ^ dfxS := by
      simp only [DIval.add]; push_cast; ring
    rw [e]
    calc ‖bodyTrans x b + exp (bodyAngle x b * I) * q g - (centreTrans lo hi b + exp (centreAngle lo hi b * I) * q g)‖
        ≤ ‖q g‖ * |bodyAngle x b - centreAngle lo hi b| + ‖bodyTrans x b - centreTrans lo hi b‖ := hmov
      _ ≤ ‖q g‖ * (((bodyData lo hi b).h : ℝ) / 2 ^ dfxS) + ((bodyData lo hi b).trad.hi : ℝ) / 2 ^ dfxS := by
          gcongr
      _ ≤ _ := by linarith

end IvSound

end WormCore
