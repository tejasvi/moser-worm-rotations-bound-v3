import WormSound.IvSound.V2
import WormSound.Defs

/-!
# Soundness of the per-body box data (`WormCore.bodyData`)

For a box with mantissas `lo hi` (scale `2⁻¹²⁰`) and a moving body `b ≥ 1` (coordinates `i = 3(b−1)`: angle, then
`x`, `y`), let `θ_c = th · 2⁻¹²⁰` and `t_c = (tx + i ty) · 2⁻¹²⁰` be the centre computed by `bodyData` (floor
midpoints). For every angle `θ` and translation `t` of the box:

* `θ_c` and `t_c` lie in the box;
* `|θ − θ_c| ≤ h · 2⁻⁵⁶` and `‖t − t_c‖ ≤ trad.hi · 2⁻⁵⁶`;
* `tc` encloses `t_c`, and `s`, `c` enclose `sin θ_c`, `cos θ_c` (when the angle interval is within `±64`).
-/

open MoserWorm

namespace WormCore

namespace IvSound

open WormCore.Sound (InBox)

lemma two_pow_BS_pos : (0 : ℝ) < 2 ^ BS := by positivity
lemma two_pow_dfxS_pos : (0 : ℝ) < 2 ^ dfxS := by positivity

lemma two_pow_BS_eq : (2 : ℝ) ^ BS = 2 ^ (BS - dfxS) * 2 ^ dfxS := by
  rw [← pow_add]; norm_num [BS, dfxS]

/-- `toLo` rounds `m · 2⁻¹²⁰` down to the scale `2⁻⁵⁶`. -/
lemma toLo_le (m : Int) : (toLo m : ℝ) / 2 ^ dfxS ≤ (m : ℝ) / 2 ^ BS := by
  have h : (0 : Int) < 2 ^ (BS - dfxS) := by positivity
  have h2 := Int.ediv_mul_le m (b := 2 ^ (BS - dfxS)) h.ne'
  have h3 : ((m.fdiv (2 ^ (BS - dfxS)) : Int) : ℝ) * 2 ^ (BS - dfxS) ≤ m := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ h.le]; exact_mod_cast h2
  rw [div_le_div_iff₀ two_pow_dfxS_pos two_pow_BS_pos, two_pow_BS_eq]
  unfold toLo
  nlinarith [two_pow_dfxS_pos]

/-- `toHi` rounds `m · 2⁻¹²⁰` up to the scale `2⁻⁵⁶`. -/
lemma le_toHi (m : Int) : (m : ℝ) / 2 ^ BS ≤ (toHi m : ℝ) / 2 ^ dfxS := by
  have h := toLo_le (-m)
  have e1 : (toHi m : ℝ) = -(toLo (-m) : ℝ) := by simp [toHi, toLo]
  rw [e1, neg_div, le_neg]
  push_cast at h ⊢
  linarith [show ((-m : Int) : ℝ) / 2 ^ BS = -((m : ℝ) / 2 ^ BS) by push_cast; ring]

lemma mem_toLoHi (m : Int) : (m : ℝ) / 2 ^ BS ∈ (⟨toLo m, toHi m⟩ : DIval) := by
  rw [DIval.mem_iff_val]
  exact ⟨toLo_le m, le_toHi m⟩

/-- The floor midpoint of `L ≤ H` lies in `[L, H]`. -/
lemma fdiv2_mem {L H : Int} (h : L ≤ H) : L ≤ (L + H).fdiv 2 ∧ (L + H).fdiv 2 ≤ H := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by norm_num)]
  constructor <;> omega

/-- A point of `[L, H] · 2⁻¹²⁰` is within `max(H − c, c − L) · 2⁻¹²⁰` of `c · 2⁻¹²⁰`. -/
lemma abs_sub_le_max {L H c : Int} {x : ℝ} (hL : (L : ℝ) / 2 ^ BS ≤ x) (hH : x ≤ (H : ℝ) / 2 ^ BS) :
    |x - (c : ℝ) / 2 ^ BS| ≤ ((max (H - c) (c - L) : Int) : ℝ) / 2 ^ BS := by
  have h1 : ((H - c : Int) : ℝ) / 2 ^ BS ≤ ((max (H - c) (c - L) : Int) : ℝ) / 2 ^ BS := by
    gcongr; exact_mod_cast le_max_left _ _
  have h2 : ((c - L : Int) : ℝ) / 2 ^ BS ≤ ((max (H - c) (c - L) : Int) : ℝ) / 2 ^ BS := by
    gcongr; exact_mod_cast le_max_right _ _
  push_cast at h1 h2 ⊢
  rw [sub_div] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- The same bound, rounded up to the scale `2⁻⁵⁶`. -/
lemma abs_sub_le_toHi_max {L H c : Int} {x : ℝ} (hL : (L : ℝ) / 2 ^ BS ≤ x) (hH : x ≤ (H : ℝ) / 2 ^ BS) :
    |x - (c : ℝ) / 2 ^ BS| ≤ (toHi (max (H - c) (c - L)) : ℝ) / 2 ^ dfxS :=
  (abs_sub_le_max hL hH).trans (le_toHi _)

/-- The angle and translation coordinates of body `b` at a point `x` of the box (`i = 3(b−1)`). -/
def bodyAngle (x : Fin 12 → ℝ) (b : Nat) : ℝ := if h : 3 * (b - 1) < 12 then x ⟨3 * (b - 1), h⟩ else 0
def bodyTrans (x : Fin 12 → ℝ) (b : Nat) : ℂ :=
  (if h : 3 * (b - 1) + 1 < 12 then x ⟨3 * (b - 1) + 1, h⟩ else 0 : ℝ) +
    (if h : 3 * (b - 1) + 2 < 12 then x ⟨3 * (b - 1) + 2, h⟩ else 0 : ℝ) * Complex.I

/-- The centre angle `θ_c` and translation `t_c` of body `b` used by `bodyData`. -/
noncomputable def centreAngle (lo hi : Array Int) (b : Nat) : ℝ :=
  (((lo[3 * (b - 1)]! + hi[3 * (b - 1)]!).fdiv 2 : Int) : ℝ) / 2 ^ BS
noncomputable def centreTrans (lo hi : Array Int) (b : Nat) : ℂ :=
  ((((lo[3 * (b - 1) + 1]! + hi[3 * (b - 1) + 1]!).fdiv 2 : Int) : ℝ) / 2 ^ BS : ℝ) +
    ((((lo[3 * (b - 1) + 2]! + hi[3 * (b - 1) + 2]!).fdiv 2 : Int) : ℝ) / 2 ^ BS : ℝ) * Complex.I

variable {lo hi : Array Int} {x : Fin 12 → ℝ} {b : Nat}

lemma inBox_coord (hx : InBox lo hi x) (j : Nat) (hj : j < 12) :
    (lo[j]! : ℝ) / 2 ^ BS ≤ x ⟨j, hj⟩ ∧ x ⟨j, hj⟩ ≤ (hi[j]! : ℝ) / 2 ^ BS :=
  hx ⟨j, hj⟩

/-- **Angle.** `|θ − θ_c| ≤ h · 2⁻⁵⁶`. -/
theorem abs_angle_sub_le (hx : InBox lo hi x) (hb1 : 1 ≤ b) (hb : b ≤ 4) :
    |bodyAngle x b - centreAngle lo hi b| ≤ ((bodyData lo hi b).h : ℝ) / 2 ^ dfxS := by
  have hj : 3 * (b - 1) < 12 := by omega
  have hc := inBox_coord hx _ hj
  simp only [bodyAngle, hj, dite_true, centreAngle, bodyData]
  exact abs_sub_le_toHi_max hc.1 hc.2

/-- The Euclidean radius `√(hx² + hy²) · 2⁻⁵⁶` of the translation box (a member of `trad`). -/
noncomputable def transRad (lo hi : Array Int) (b : Nat) : ℝ :=
  Real.sqrt ((((bodyData lo hi b).hx : ℝ) / 2 ^ dfxS) ^ 2 + (((bodyData lo hi b).hy : ℝ) / 2 ^ dfxS) ^ 2)

lemma transRad_nonneg (lo hi : Array Int) (b : Nat) : 0 ≤ transRad lo hi b := Real.sqrt_nonneg _

lemma mem_transRad (lo hi : Array Int) (b : Nat) : transRad lo hi b ∈ (bodyData lo hi b).trad :=
  DIval.mem_norm2 (DIval.mem_pt _) (DIval.mem_pt _)

/-- **Translation.** `‖t − t_c‖ ≤ √(hx² + hy²) · 2⁻⁵⁶`. -/
theorem norm_trans_sub_le_rad (hx : InBox lo hi x) (hb1 : 1 ≤ b) (hb : b ≤ 4) :
    ‖bodyTrans x b - centreTrans lo hi b‖ ≤ transRad lo hi b := by
  have hj1 : 3 * (b - 1) + 1 < 12 := by omega
  have hj2 : 3 * (b - 1) + 2 < 12 := by omega
  have hc1 := inBox_coord hx _ hj1
  have hc2 := inBox_coord hx _ hj2
  set dx := x ⟨3 * (b - 1) + 1, hj1⟩ -
    (((lo[3 * (b - 1) + 1]! + hi[3 * (b - 1) + 1]!).fdiv 2 : Int) : ℝ) / 2 ^ BS with hdx
  set dy := x ⟨3 * (b - 1) + 2, hj2⟩ -
    (((lo[3 * (b - 1) + 2]! + hi[3 * (b - 1) + 2]!).fdiv 2 : Int) : ℝ) / 2 ^ BS with hdy
  have hbx := abs_sub_le_toHi_max (c := (lo[3 * (b - 1) + 1]! + hi[3 * (b - 1) + 1]!).fdiv 2) hc1.1 hc1.2
  have hby := abs_sub_le_toHi_max (c := (lo[3 * (b - 1) + 2]! + hi[3 * (b - 1) + 2]!).fdiv 2) hc2.1 hc2.2
  rw [← hdx] at hbx
  rw [← hdy] at hby
  have hnorm : ‖bodyTrans x b - centreTrans lo hi b‖ = Real.sqrt (dx ^ 2 + dy ^ 2) := by
    simp only [bodyTrans, centreTrans, hj1, hj2, dite_true]
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im, hdx, hdy]
    ring
  rw [hnorm]
  unfold transRad
  apply Real.sqrt_le_sqrt
  have ex : (bodyData lo hi b).hx = toHi (max (hi[3 * (b - 1) + 1]! - (lo[3 * (b - 1) + 1]! +
      hi[3 * (b - 1) + 1]!).fdiv 2) ((lo[3 * (b - 1) + 1]! + hi[3 * (b - 1) + 1]!).fdiv 2 - lo[3 * (b - 1) + 1]!)) := rfl
  have ey : (bodyData lo hi b).hy = toHi (max (hi[3 * (b - 1) + 2]! - (lo[3 * (b - 1) + 2]! +
      hi[3 * (b - 1) + 2]!).fdiv 2) ((lo[3 * (b - 1) + 2]! + hi[3 * (b - 1) + 2]!).fdiv 2 - lo[3 * (b - 1) + 2]!)) := rfl
  rw [← ex] at hbx
  rw [← ey] at hby
  have h1 : dx ^ 2 ≤ (((bodyData lo hi b).hx : ℝ) / 2 ^ dfxS) ^ 2 := by
    rw [← sq_abs dx]; exact pow_le_pow_left₀ (abs_nonneg _) hbx 2
  have h2 : dy ^ 2 ≤ (((bodyData lo hi b).hy : ℝ) / 2 ^ dfxS) ^ 2 := by
    rw [← sq_abs dy]; exact pow_le_pow_left₀ (abs_nonneg _) hby 2
  linarith

/-- **Translation.** `‖t − t_c‖ ≤ trad.hi · 2⁻⁵⁶`. -/
theorem norm_trans_sub_le (hx : InBox lo hi x) (hb1 : 1 ≤ b) (hb : b ≤ 4) :
    ‖bodyTrans x b - centreTrans lo hi b‖ ≤ ((bodyData lo hi b).trad.hi : ℝ) / 2 ^ dfxS := by
  refine (norm_trans_sub_le_rad hx hb1 hb).trans ?_
  have := (DIval.mem_iff_val.mp (mem_transRad lo hi b)).2
  simpa [DIval.val] using this

/-- **Centre translation.** `tc` encloses `t_c`. -/
theorem mem_centreTrans (b : Nat) : V2.Mem (bodyData lo hi b).tc (centreTrans lo hi b) := by
  refine ⟨?_, ?_⟩
  · have e : (centreTrans lo hi b).re =
        (((lo[3 * (b - 1) + 1]! + hi[3 * (b - 1) + 1]!).fdiv 2 : Int) : ℝ) / 2 ^ BS := by
      simp only [centreTrans, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, mul_one, add_zero, sub_self]
    rw [e]; exact mem_toLoHi _
  · have e : (centreTrans lo hi b).im =
        (((lo[3 * (b - 1) + 2]! + hi[3 * (b - 1) + 2]!).fdiv 2 : Int) : ℝ) / 2 ^ BS := by
      simp only [centreTrans, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, mul_one, zero_add, add_zero]
    rw [e]; exact mem_toLoHi _

/-- **Centre angle.** `s`, `c` enclose `sin θ_c`, `cos θ_c` when the angle interval is within `±64`. -/
theorem mem_centre_sincos (b : Nat)
    (hlo : -(64 * dfxOne) ≤ toLo ((lo[3 * (b - 1)]! + hi[3 * (b - 1)]!).fdiv 2))
    (hhi : toHi ((lo[3 * (b - 1)]! + hi[3 * (b - 1)]!).fdiv 2) ≤ 64 * dfxOne) :
    Real.sin (centreAngle lo hi b) ∈ (bodyData lo hi b).s ∧ Real.cos (centreAngle lo hi b) ∈ (bodyData lo hi b).c :=
  DIval.mem_sincosIv (mem_toLoHi _) hlo hhi

/-- The centre lies in the box (when `lo ≤ hi` on its coordinates). -/
theorem centre_mem (hle : ∀ j < 12, lo[j]! ≤ hi[j]!) (hb1 : 1 ≤ b) (hb : b ≤ 4) :
    ∃ x₀ : Fin 12 → ℝ, InBox lo hi x₀ ∧ bodyAngle x₀ b = centreAngle lo hi b ∧
      bodyTrans x₀ b = centreTrans lo hi b := by
  classical
  -- every coordinate at its floor midpoint
  let c : Fin 12 → ℝ := fun j => (((lo[j.val]! + hi[j.val]!).fdiv 2 : Int) : ℝ) / 2 ^ BS
  refine ⟨c, fun j => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := fdiv2_mem (hle j.val j.isLt)
    constructor
    · show (lo[j.val]! : ℝ) / 2 ^ BS ≤ (((lo[j.val]! + hi[j.val]!).fdiv 2 : Int) : ℝ) / 2 ^ BS
      gcongr
    · show (((lo[j.val]! + hi[j.val]!).fdiv 2 : Int) : ℝ) / 2 ^ BS ≤ (hi[j.val]! : ℝ) / 2 ^ BS
      gcongr
  · have hj : 3 * (b - 1) < 12 := by omega
    simp only [bodyAngle, hj, dite_true, centreAngle, c]
  · have hj1 : 3 * (b - 1) + 1 < 12 := by omega
    have hj2 : 3 * (b - 1) + 2 < 12 := by omega
    simp only [bodyTrans, hj1, hj2, dite_true, centreTrans, c]

end IvSound

end WormCore
