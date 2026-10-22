import WormSound.IvSound.Ctx
import WormSound.Quad

/-!
# Helpers for the area-model identity (`WormSound.Model`)

* `cross` is real-bilinear (`cross_expand`: the cross product of two affine expressions in real variables);
* the sums over `range 16` supported on the four variables of one body (`sum16_block`);
* the position of a moving vertex in the box variables (`place_expand`);
* the shoelace sum of a mapped list over the cyclic edges (`shoelace_map`, `cycPairs_sum`);
* the bounds of the box variables: translations, `C = cos d - 1` against `cLo`, `S = sin d`.
-/

noncomputable section

namespace WormCore.Sound.ModelProof

open WormCore WormCore.IvSound Complex Finset Worm.Geom
open MoserWorm (dfxS dfxOne)

/-! ## `cross` is real-bilinear -/

lemma cross_add_left (a b c : ℂ) : cross (a + b) c = cross a c + cross b c := by
  simp only [cross, Complex.add_re, Complex.add_im]; ring

lemma cross_add_right (a b c : ℂ) : cross a (b + c) = cross a b + cross a c := by
  simp only [cross, Complex.add_re, Complex.add_im]; ring

lemma cross_zero_left (a : ℂ) : cross 0 a = 0 := by simp [cross]

lemma cross_zero_right (a : ℂ) : cross a 0 = 0 := by simp [cross]

lemma cross_mul_ofReal_left (a c : ℂ) (r : ℝ) : cross (a * (r : ℂ)) c = cross a c * r := by
  simp only [cross, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring

lemma cross_mul_ofReal_right (a c : ℂ) (r : ℝ) : cross a (c * (r : ℂ)) = cross a c * r := by
  simp only [cross, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring

lemma cross_sum_left (s : Finset ℕ) (f : ℕ → ℂ) (c : ℂ) :
    cross (∑ k ∈ s, f k) c = ∑ k ∈ s, cross (f k) c := by
  simp only [cross, Complex.re_sum, Complex.im_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]

lemma cross_sum_right (s : Finset ℕ) (c : ℂ) (f : ℕ → ℂ) :
    cross c (∑ k ∈ s, f k) = ∑ k ∈ s, cross c (f k) := by
  simp only [cross, Complex.re_sum, Complex.im_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- The cross product of two affine expressions in the real variables `y`. -/
lemma cross_expand (s : Finset ℕ) (X Z : ℂ) (c d : ℕ → ℂ) (y : ℕ → ℝ) :
    cross (X + ∑ k ∈ s, c k * (y k : ℂ)) (Z + ∑ k ∈ s, d k * (y k : ℂ)) =
      cross X Z + ∑ k ∈ s, (cross X (d k) + cross (c k) Z) * y k +
        ∑ k ∈ s, ∑ m ∈ s, cross (c k) (d m) * y k * y m := by
  rw [cross_add_left, cross_add_right, cross_add_right, cross_sum_right, cross_sum_left, cross_sum_left]
  simp only [cross_mul_ofReal_right, cross_mul_ofReal_left, cross_sum_right]
  have h1 : ∑ k ∈ s, (cross X (d k) + cross (c k) Z) * y k =
      ∑ k ∈ s, cross X (d k) * y k + ∑ k ∈ s, cross (c k) Z * y k := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun k _ => by ring
  rw [h1]
  ring

/-! ## Sums supported on one body -/

/-- A sum over `range 16` of terms supported on the four variables of body `b ∈ [1, 4]`. -/
lemma sum16_block {b : ℕ} (hb1 : 1 ≤ b) (hb4 : b ≤ 4) (f : ℕ → ℂ) :
    ∑ k ∈ range 16, (if b ≠ 0 ∧ k / 4 = b - 1 then f k else 0) =
      f (4 * (b - 1)) + f (4 * (b - 1) + 1) + f (4 * (b - 1) + 2) + f (4 * (b - 1) + 3) := by
  interval_cases b <;> simp [Finset.sum_range_succ]

/-- The position `t + e^{iθ} q` in the variables `Δt`, `C = cos(θ - θ_c) - 1`, `S = sin(θ - θ_c)` around the centre
`t_c + e^{iθ_c} q`. -/
lemma place_expand (θ θc : ℝ) (t tc qg : ℂ) :
    t + exp (θ * I) * qg = tc + exp (θc * I) * qg +
      (1 * ((t - tc).re : ℂ) + I * ((t - tc).im : ℂ) +
        exp (θc * I) * qg * ((Real.cos (θ - θc) - 1 : ℝ) : ℂ) +
        I * (exp (θc * I) * qg) * ((Real.sin (θ - θc) : ℝ) : ℂ)) := by
  have e : exp (θ * I) = exp (θc * I) * ((Real.cos (θ - θc) : ℝ) + (Real.sin (θ - θc) : ℝ) * I) := by
    rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have ht : t = tc + ((t - tc).re : ℂ) + ((t - tc).im : ℂ) * I := by
    rw [add_assoc, Complex.re_add_im]; ring
  rw [e]
  push_cast
  linear_combination ht

/-! ## The shoelace sum over the cyclic edges -/

lemma list_sum_range (n : ℕ) (f : ℕ → ℝ) : ((List.range n).map f).sum = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

lemma cycPairs_sum (l : List ℕ) (f : ℕ × ℕ → ℝ) :
    ((cycPairs l).map f).sum = ∑ j ∈ range l.length, f (at' l j, at' l (j + 1)) := by
  unfold cycPairs
  rw [List.map_map]
  exact list_sum_range _ _

lemma at'_mem {l : List ℕ} (hl : 0 < l.length) (j : ℕ) : at' l j ∈ l := by
  unfold at'
  rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hl)]
  exact List.getElem_mem _

lemma shoelace_map (l : List ℕ) (f : ℕ → ℂ) :
    shoelace (l.map f) = (∑ j ∈ range l.length, cross (f (at' l j)) (f (at' l (j + 1)))) / 2 := by
  unfold shoelace
  rw [List.length_map]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hn : 0 < l.length := by have := Finset.mem_range.mp hj; omega
  have hpt : ∀ i, pt (l.map f) i = f (at' l i) := by
    intro i
    unfold pt at'
    rw [List.length_map, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact Nat.mod_lt _ hn),
      List.getElem_map, List.getD_eq_getElem _ _ (Nat.mod_lt _ hn)]
  rw [hpt, hpt]

/-- Regrouping the edge sum of quadratics into one quadratic. -/
lemma sum_quad_assoc (s t : Finset ℕ) (A : ℕ → ℝ) (G : ℕ → ℕ → ℝ) (M : ℕ → ℕ → ℕ → ℝ) (y : ℕ → ℝ) :
    (∑ j ∈ t, (A j + ∑ k ∈ s, G j k * y k + ∑ k ∈ s, ∑ m ∈ s, M j k m * y k * y m)) / 2 =
      (∑ j ∈ t, A j) / 2 + ∑ k ∈ s, (∑ j ∈ t, G j k) / 2 * y k +
        ∑ k ∈ s, ∑ m ∈ s, (∑ j ∈ t, M j k m) / 2 * y k * y m := by
  rw [sum_add_distrib, sum_add_distrib, add_div, add_div]
  have hG : (∑ j ∈ t, ∑ k ∈ s, G j k * y k) / 2 = ∑ k ∈ s, (∑ j ∈ t, G j k) / 2 * y k := by
    rw [sum_comm, sum_div]
    exact sum_congr rfl fun k _ => by rw [← sum_mul]; ring
  have hM : (∑ j ∈ t, ∑ k ∈ s, ∑ m ∈ s, M j k m * y k * y m) / 2 =
      ∑ k ∈ s, ∑ m ∈ s, (∑ j ∈ t, M j k m) / 2 * y k * y m := by
    rw [sum_comm, sum_div]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_comm, sum_div]
    exact sum_congr rfl fun m _ => by rw [← sum_mul, ← sum_mul]; ring
  rw [hG, hM]

/-! ## Bounds of the box variables -/

/-- `cLo h ≤ -h² / 2⁵⁷` (`cLo h = -⌈h² / 2⁵⁷⌉`). -/
lemma cLo_le (h : Int) : ((cLo h : Int) : ℝ) ≤ -((h : ℝ) ^ 2) / (2 * 2 ^ dfxS) := by
  have key : h * h ≤ 2 * dfxOne * ((h * h + 2 * dfxOne - 1) / (2 * dfxOne)) := by
    have hh : 0 ≤ h * h := mul_self_nonneg h
    generalize h * h = H at *
    simp only [dfxOne]
    omega
  have hD : (2 * 2 ^ dfxS : ℝ) = ((2 * dfxOne : Int) : ℝ) := by norm_num [dfxOne, dfxS]
  have hpos : (0 : ℝ) < 2 * 2 ^ dfxS := by positivity
  have key' : (h : ℝ) ^ 2 ≤ (2 * 2 ^ dfxS) * (((h * h + 2 * dfxOne - 1) / (2 * dfxOne) : Int) : ℝ) := by
    rw [hD, sq]; exact_mod_cast key
  unfold cLo
  push_cast
  rw [le_div_iff₀ hpos]
  nlinarith

lemma two_mul_fdiv_two_le (m : Int) : 2 * m.fdiv 2 ≤ m := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by norm_num)]
  omega

/-- The cosine variable `C = cos d - 1` lies in `[2 m, 0] · 2⁻⁵⁶`, `m = (cLo h).fdiv 2`, when `|d| ≤ h · 2⁻⁵⁶`. -/
lemma cos_var_mem {d : ℝ} {h : Int} (hd : |d| ≤ (h : ℝ) / 2 ^ dfxS) :
    |Real.cos d - 1 - (((cLo h).fdiv 2 : Int) : ℝ) / 2 ^ dfxS| ≤ ((-((cLo h).fdiv 2) : Int) : ℝ) / 2 ^ dfxS := by
  have hc1 : Real.cos d ≤ 1 := Real.cos_le_one d
  have hc2 : 1 - d ^ 2 / 2 ≤ Real.cos d := Real.one_sub_sq_div_two_le_cos
  have hm : 2 * (((cLo h).fdiv 2 : Int) : ℝ) ≤ ((cLo h : Int) : ℝ) := by
    exact_mod_cast two_mul_fdiv_two_le (cLo h)
  have hcl := cLo_le h
  have hd2 : d ^ 2 ≤ ((h : ℝ) / 2 ^ dfxS) ^ 2 := by
    rw [← sq_abs d]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hpos : (0 : ℝ) < 2 ^ dfxS := by positivity
  have e : -((h : ℝ) ^ 2) / (2 * 2 ^ dfxS) / 2 ^ dfxS = -(((h : ℝ) / 2 ^ dfxS) ^ 2 / 2) := by
    field_simp
  have h3 : 2 * (((cLo h).fdiv 2 : Int) : ℝ) / 2 ^ dfxS ≤ -((h : ℝ) ^ 2) / (2 * 2 ^ dfxS) / 2 ^ dfxS :=
    div_le_div_of_nonneg_right (hm.trans hcl) hpos.le
  rw [e] at h3
  rw [abs_le]
  push_cast
  constructor
  · have : 2 * (((cLo h).fdiv 2 : Int) : ℝ) / 2 ^ dfxS =
        (((cLo h).fdiv 2 : Int) : ℝ) / 2 ^ dfxS + (((cLo h).fdiv 2 : Int) : ℝ) / 2 ^ dfxS := by ring
    rw [this] at h3
    have : -(-(((cLo h).fdiv 2 : Int) : ℝ) / 2 ^ dfxS) = (((cLo h).fdiv 2 : Int) : ℝ) / 2 ^ dfxS := by ring
    rw [this]
    linarith
  · have : -(((cLo h).fdiv 2 : Int) : ℝ) / 2 ^ dfxS = -((((cLo h).fdiv 2 : Int) : ℝ) / 2 ^ dfxS) := by ring
    rw [this]
    linarith

/-- The sine variable: `|sin d| ≤ h · 2⁻⁵⁶` when `|d| ≤ h · 2⁻⁵⁶`. -/
lemma sin_var_mem {d : ℝ} {h : Int} (hd : |d| ≤ (h : ℝ) / 2 ^ dfxS) : |Real.sin d| ≤ (h : ℝ) / 2 ^ dfxS :=
  Real.abs_sin_le_abs.trans hd

variable {lo hi : Array Int} {x : Fin 12 → ℝ} {b : ℕ}

lemma trans_re_mem (hx : WormCore.Sound.InBox lo hi x) (hb1 : 1 ≤ b) (hb : b ≤ 4) :
    |(bodyTrans x b - centreTrans lo hi b).re| ≤ ((bodyData lo hi b).hx : ℝ) / 2 ^ dfxS := by
  have hj1 : 3 * (b - 1) + 1 < 12 := by omega
  have hc1 := inBox_coord hx _ hj1
  have hbx := abs_sub_le_toHi_max (c := (lo[3 * (b - 1) + 1]! + hi[3 * (b - 1) + 1]!).fdiv 2) hc1.1 hc1.2
  have ex : (bodyData lo hi b).hx = toHi (max (hi[3 * (b - 1) + 1]! - (lo[3 * (b - 1) + 1]! +
      hi[3 * (b - 1) + 1]!).fdiv 2) ((lo[3 * (b - 1) + 1]! + hi[3 * (b - 1) + 1]!).fdiv 2 - lo[3 * (b - 1) + 1]!)) :=
    rfl
  rw [ex]
  have e : (bodyTrans x b - centreTrans lo hi b).re =
      x ⟨3 * (b - 1) + 1, hj1⟩ - (((lo[3 * (b - 1) + 1]! + hi[3 * (b - 1) + 1]!).fdiv 2 : Int) : ℝ) / 2 ^ BS := by
    simp only [bodyTrans, centreTrans, hj1, dite_true, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
  rw [e]
  exact hbx

lemma trans_im_mem (hx : WormCore.Sound.InBox lo hi x) (hb1 : 1 ≤ b) (hb : b ≤ 4) :
    |(bodyTrans x b - centreTrans lo hi b).im| ≤ ((bodyData lo hi b).hy : ℝ) / 2 ^ dfxS := by
  have hj2 : 3 * (b - 1) + 2 < 12 := by omega
  have hc2 := inBox_coord hx _ hj2
  have hby := abs_sub_le_toHi_max (c := (lo[3 * (b - 1) + 2]! + hi[3 * (b - 1) + 2]!).fdiv 2) hc2.1 hc2.2
  have ey : (bodyData lo hi b).hy = toHi (max (hi[3 * (b - 1) + 2]! - (lo[3 * (b - 1) + 2]! +
      hi[3 * (b - 1) + 2]!).fdiv 2) ((lo[3 * (b - 1) + 2]! + hi[3 * (b - 1) + 2]!).fdiv 2 - lo[3 * (b - 1) + 2]!)) :=
    rfl
  rw [ey]
  have e : (bodyTrans x b - centreTrans lo hi b).im =
      x ⟨3 * (b - 1) + 2, hj2⟩ - (((lo[3 * (b - 1) + 2]! + hi[3 * (b - 1) + 2]!).fdiv 2 : Int) : ℝ) / 2 ^ BS := by
    simp only [bodyTrans, centreTrans, hj2, dite_true, Complex.sub_im, Complex.add_im, Complex.ofReal_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, zero_add, add_zero]
  rw [e]
  exact hby

end WormCore.Sound.ModelProof
