import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Data.List.Rotate
import Worm13a.Statement
import MoserWorm.Common.Area
import MoserWorm.LowerBound.Fan
import Worm13a.Geom.LebFan

/-!
# The geometric lemmas used by the worm certificate checker (interface)

Pointwise statements about finitely many points of a convex set `K ⊆ ℂ`, in the terms of the certificate checker:
the small-list lemma, the fan lemma, the vertex-fan lemma, the chord decomposition, and the vertices of the five
arcs. The checker establishes the hypotheses on a whole placement box by interval arithmetic and then applies these
lemmas at every placement of the box.

The proofs use Keller's `moser-worm-improved-bounds` (Apache-2.0) and the fan lemma `LebesgueCover.Fan` of the Lean
proof for Lebesgue's universal covering problem.
-/

open MeasureTheory

noncomputable section

namespace Worm.Geom

/-- `cross a b = det(a, b)`. -/
def cross (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

/-- The point of index `j` of a cyclic list (indices taken modulo the length). -/
def pt (P : List ℂ) (j : ℕ) : ℂ := P.getD (j % P.length) 0

/-- The shoelace area `(1/2) ∑ⱼ det(Pⱼ, Pⱼ₊₁)` of a cyclic list. -/
def shoelace (P : List ℂ) : ℝ :=
  (∑ j ∈ Finset.range P.length, cross (pt P j) (pt P (j + 1))) / 2

/-! ### Helpers: cyclic indexing, Keller's shoelace (`MoserWorm.shoelace`), half-planes, the four-point bound -/

section

open Set

lemma cross_eq_keller (a b : ℂ) : cross a b = MoserWorm.cross a b := rfl

lemma pt_congr (P : List ℂ) {a b : ℕ} (h : a % P.length = b % P.length) : pt P a = pt P b := by
  simp only [pt, h]

lemma pt_mod (P : List ℂ) (j : ℕ) : pt P (j % P.length) = pt P j :=
  pt_congr P (Nat.mod_mod _ _)

lemma pt_add_length (P : List ℂ) (j : ℕ) : pt P (j + P.length) = pt P j :=
  pt_congr P (Nat.add_mod_right _ _)

lemma pt_of_lt (P : List ℂ) {j : ℕ} (hj : j < P.length) : pt P j = P.getD j 0 := by
  simp only [pt, Nat.mod_eq_of_lt hj]

lemma pt_mem (P : List ℂ) (hP : 0 < P.length) (j : ℕ) : pt P j ∈ P := by
  unfold pt
  rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hP)]
  exact List.getElem_mem _

lemma shoelace_eq_keller (P : List ℂ) : shoelace P = MoserWorm.shoelace P := by
  unfold shoelace MoserWorm.shoelace
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [pt_of_lt P (Finset.mem_range.mp hj), pt_mod P (j + 1) |>.symm, pt_of_lt P (Nat.mod_lt _ (by
    have := Finset.mem_range.mp hj; omega))]
  rfl

lemma convex_halfplane_le (v p : ℂ) : Convex ℝ {x : ℂ | cross v (x - p) ≤ 0} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at *
  have e : cross v (a • x + b • y - p) = a * cross v (x - p) + b * cross v (y - p) := by
    simp only [cross, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im, smul_eq_mul]
    linear_combination (v.re * p.im - v.im * p.re) * hab
  rw [e]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx) (mul_nonpos_of_nonneg_of_nonpos hb hy)

lemma convex_halfplane_ge (v p : ℂ) : Convex ℝ {x : ℂ | 0 ≤ cross v (x - p)} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at *
  have e : cross v (a • x + b • y - p) = a * cross v (x - p) + b * cross v (y - p) := by
    simp only [cross, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im, smul_eq_mul]
    linear_combination (v.re * p.im - v.im * p.re) * hab
  rw [e]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

/-- The two closed half-planes of a line cut any set into pieces whose areas add up to at most its area. -/
lemma volume_halfplanes_le (K : Set ℂ) (v p : ℂ) (hv : v ≠ 0) :
    volume (K ∩ {x | cross v (x - p) ≤ 0}) + volume (K ∩ {x | 0 ≤ cross v (x - p)}) ≤ volume K := by
  have hmeas : MeasurableSet {x : ℂ | cross v (x - p) ≤ 0} := by
    apply measurableSet_le _ measurable_const
    unfold cross; fun_prop
  have hL : volume {x : ℂ | cross v (x - p) = 0} = 0 := MoserWorm.volume_cross_line v p hv
  have hsub : K ∩ {x | 0 ≤ cross v (x - p)} ⊆
      (K \ {x | cross v (x - p) ≤ 0}) ∪ {x | cross v (x - p) = 0} := by
    rintro x ⟨hxK, hx⟩
    have hx' : 0 ≤ cross v (x - p) := hx
    rcases hx'.lt_or_eq with h | h
    · left
      refine ⟨hxK, fun h' => ?_⟩
      have h'' : cross v (x - p) ≤ 0 := h'
      exact absurd h'' (not_le.mpr h)
    · right; exact h.symm
  have h2 : volume (K ∩ {x | 0 ≤ cross v (x - p)}) ≤ volume (K \ {x | cross v (x - p) ≤ 0}) :=
    calc volume (K ∩ {x | 0 ≤ cross v (x - p)})
        ≤ volume ((K \ {x | cross v (x - p) ≤ 0}) ∪ {x | cross v (x - p) = 0}) := measure_mono hsub
      _ ≤ volume (K \ {x | cross v (x - p) ≤ 0}) + volume {x : ℂ | cross v (x - p) = 0} :=
        measure_union_le _ _
      _ = volume (K \ {x | cross v (x - p) ≤ 0}) := by rw [hL, add_zero]
  calc volume (K ∩ {x | cross v (x - p) ≤ 0}) + volume (K ∩ {x | 0 ≤ cross v (x - p)})
      ≤ volume (K ∩ {x | cross v (x - p) ≤ 0}) + volume (K \ {x | cross v (x - p) ≤ 0}) :=
        add_le_add le_rfl h2
    _ = volume K := measure_inter_add_sdiff K hmeas

/-- Keller's four-point bound `cross(c - a, d - b) / 2 ≤ area K` (Lemma 3.3), through the half-plane split: if `b`
and `d` lie in opposite closed half-planes of the line through `a` and `c`, the triangles `a b c` and `a c d` lie in the
two halves; otherwise one of the two triangles already has the larger area. -/
lemma quad_le {K : Set ℂ} (hK : Convex ℝ K) {a b c d : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K) :
    ENNReal.ofReal (MoserWorm.cross (c - a) (d - b) / 2) ≤ volume K := by
  have hpq : MoserWorm.cross (c - a) (d - b) = cross (c - a) (d - a) - cross (c - a) (b - a) := by
    simp only [MoserWorm.cross_apply, cross, Complex.sub_re, Complex.sub_im]; ring
  have tri1 : ∀ L : Set ℂ, Convex ℝ L → a ∈ L → b ∈ L → c ∈ L →
      ENNReal.ofReal (|cross (c - a) (b - a)| / 2) ≤ volume L := by
    intro L hL ha' hb' hc'
    have h := MoserWorm.triangle_area_le_volume hL ha' hb' hc'
    rw [MoserWorm.cross_swap, abs_neg] at h
    exact h
  have tri2 : ∀ L : Set ℂ, Convex ℝ L → a ∈ L → c ∈ L → d ∈ L →
      ENNReal.ofReal (|cross (c - a) (d - a)| / 2) ≤ volume L :=
    fun L hL ha' hc' hd' => MoserWorm.triangle_area_le_volume hL ha' hc' hd'
  rw [hpq]
  set p := cross (c - a) (b - a) with hp
  set q := cross (c - a) (d - a) with hq
  rcases le_or_gt (q - p) 0 with hneg | hpos
  · rw [ENNReal.ofReal_of_nonpos (by linarith)]; exact zero_le
  by_cases hp0 : p ≤ 0
  · by_cases hq0 : 0 ≤ q
    · -- `b` and `d` lie in opposite closed half-planes of the line through `a` and `c`
      have hu0 : c - a ≠ 0 := by
        intro h0
        have e1 : p = 0 := by simp only [hp, h0, cross, Complex.zero_re, Complex.zero_im]; ring
        have e2 : q = 0 := by simp only [hq, h0, cross, Complex.zero_re, Complex.zero_im]; ring
        linarith
      have hca : cross (c - a) (c - a) = 0 := by simp only [cross]; ring
      have haa : cross (c - a) (a - a) = 0 := by simp [cross]
      have h1 := tri1 (K ∩ {x | cross (c - a) (x - a) ≤ 0}) (hK.inter (convex_halfplane_le _ _))
        ⟨ha, haa.le⟩ ⟨hb, hp0⟩ ⟨hc, hca.le⟩
      have h2 := tri2 (K ∩ {x | 0 ≤ cross (c - a) (x - a)}) (hK.inter (convex_halfplane_ge _ _))
        ⟨ha, haa.ge⟩ ⟨hc, hca.ge⟩ ⟨hd, hq0⟩
      calc ENNReal.ofReal ((q - p) / 2) = ENNReal.ofReal (|p| / 2 + |q| / 2) := by
            rw [abs_of_nonpos hp0, abs_of_nonneg hq0]; ring_nf
        _ ≤ ENNReal.ofReal (|p| / 2) + ENNReal.ofReal (|q| / 2) := ENNReal.ofReal_add_le
        _ ≤ volume (K ∩ {x | cross (c - a) (x - a) ≤ 0}) + volume (K ∩ {x | 0 ≤ cross (c - a) (x - a)}) :=
            add_le_add h1 h2
        _ ≤ volume K := volume_halfplanes_le K (c - a) a hu0
    · -- `p < q < 0`: the triangle `a b c` alone suffices
      push Not at hq0
      calc ENNReal.ofReal ((q - p) / 2) ≤ ENNReal.ofReal (|p| / 2) := by
            apply ENNReal.ofReal_le_ofReal; rw [abs_of_nonpos hp0]; linarith
        _ ≤ volume K := tri1 K hK ha hb hc
  · -- `0 < p < q`: the triangle `a c d` alone suffices
    push Not at hp0
    calc ENNReal.ofReal ((q - p) / 2) ≤ ENNReal.ofReal (|q| / 2) := by
          apply ENNReal.ofReal_le_ofReal; rw [abs_of_pos (by linarith)]; linarith
      _ ≤ volume K := tri2 K hK ha hc hd

end

/-- **Small lists** (Keller, Lemma 3.3): the shoelace area of at most four points of a convex set, in any order, is at most
its area. -/
theorem small_le (K : Set ℂ) (hK : Convex ℝ K) (P : List ℂ) (hP : ∀ x ∈ P, x ∈ K) (hlen : P.length ≤ 4) :
    ENNReal.ofReal (shoelace P) ≤ volume K := by
  rw [shoelace_eq_keller]
  match P, hP, hlen with
  | [], _, _ => simp [MoserWorm.shoelace]
  | [a], _, _ =>
    have h0 : MoserWorm.shoelace [a] = 0 := by simp [MoserWorm.shoelace]; ring
    simp [h0]
  | [a, b], _, _ =>
    have h0 : MoserWorm.shoelace [a, b] = 0 := by
      simp [MoserWorm.shoelace, Finset.sum_range_succ, MoserWorm.cross]; ring
    simp [h0]
  | [a, b, c], hP, _ =>
    rw [MoserWorm.shoelace_triangle]
    exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_abs_self _) (by norm_num))).trans
      (MoserWorm.triangle_area_le_volume hK (hP a (by simp)) (hP b (by simp)) (hP c (by simp)))
  | [a, b, c, d], hP, _ =>
    rw [MoserWorm.shoelace_quad]
    exact quad_le hK (hP a (by simp)) (hP b (by simp)) (hP c (by simp)) (hP d (by simp))
  | _ :: _ :: _ :: _ :: _ :: _, _, hlen => simp only [List.length_cons] at hlen; omega

/-! ### Helper for the fan lemma: the centre of a positively turning fan lies in the convex hull -/

section

open Set

/-- If every turn `det(x_j - z, x_{j+1} - z)` (indices mod `m`) is positive, then `z` lies in the convex hull of the
`x_j`: otherwise a separating functional puts all `x_j - z` in an open half-plane, where the slopes `Im/Re` would
increase strictly around the cycle. -/
lemma centre_mem_convexHull {x : ℕ → ℂ} {m : ℕ} (hm : 0 < m) {z : ℂ}
    (hdet : ∀ j < m, 0 < cross (x j - z) (x ((j + 1) % m) - z)) :
    z ∈ convexHull ℝ (x '' Iio m) := by
  by_contra hz
  have hfin : (x '' Iio m).Finite := (finite_Iio m).image x
  obtain ⟨f, u, hfu, huz⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ _) (hfin.isClosed_convexHull ℝ) hz
  have hneg : ∀ j < m, f (x j - z) < 0 := by
    intro j hj
    have := hfu (x j) (subset_convexHull ℝ _ ⟨j, hj, rfl⟩)
    rw [map_sub]; linarith
  have hf : ∀ a : ℂ, f a = a.re * f 1 + a.im * f Complex.I := by
    intro a
    have e : a = (a.re : ℝ) • (1 : ℂ) + (a.im : ℝ) • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [e]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  set w : ℂ := -((f 1 : ℂ) - (f Complex.I : ℂ) * Complex.I) with hw
  have hre : ∀ a : ℂ, (a * w).re = -(f a) := by
    intro a; rw [hf a, hw]; simp; ring
  have hpos : ∀ j < m, 0 < ((x j - z) * w).re := by
    intro j hj; rw [hre]; linarith [hneg j hj]
  have hcross : ∀ a b : ℂ, cross (a * w) (b * w) = Complex.normSq w * cross a b := by
    intro a b; simp only [cross, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]; ring
  have hw0 : w ≠ 0 := by
    rintro h0
    have := hpos 0 hm
    rw [h0, mul_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hnw : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
  set g : ℕ → ℝ := fun j => ((x j - z) * w).im / ((x j - z) * w).re with hg
  have hinc : ∀ j < m, g j < g ((j + 1) % m) := by
    intro j hj
    have h1 := hpos j hj
    have h2 := hpos ((j + 1) % m) (Nat.mod_lt _ hm)
    have hc : 0 < cross ((x j - z) * w) ((x ((j + 1) % m) - z) * w) := by
      rw [hcross]; exact mul_pos hnw (hdet j hj)
    simp only [hg]
    rw [div_lt_div_iff₀ h1 h2]
    simp only [cross] at hc
    linarith
  have hchain : ∀ k, k < m → g 0 ≤ g k := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih =>
      intro hk
      have h1 := hinc k (by omega)
      rw [Nat.mod_eq_of_lt hk] at h1
      exact (ih (by omega)).trans h1.le
  have hlast := hinc (m - 1) (by omega)
  rw [show m - 1 + 1 = m by omega, Nat.mod_self] at hlast
  linarith [hchain (m - 1) (by omega)]

end

/-- **Fan lemma** (fan around a point `z`, which is not assumed to lie in `K`): if every turn `det(Pⱼ - z, Pⱼ₊₁ - z)` is
positive and the total turning is below `4π` (so it is exactly `2π`), the shoelace area is at most the area of `K`. -/
theorem fan_le (K : Set ℂ) (hK : Convex ℝ K) (P : List ℂ) (hP : ∀ x ∈ P, x ∈ K) (z : ℂ) (h3 : 3 ≤ P.length)
    (hdet : ∀ j < P.length, 0 < cross (pt P j - z) (pt P (j + 1) - z))
    (hwind : ∑ j ∈ Finset.range P.length, Complex.arg ((pt P (j + 1) - z) / (pt P j - z)) < 4 * Real.pi) :
    ENNReal.ofReal (shoelace P) ≤ volume K := by
  have hn0 : 0 < P.length := by omega
  set a : ℕ → ℂ := fun j => pt P j - z with ha_def
  have hnxt : ∀ j, a (LebesgueCover.nxt P.length j) = pt P (j + 1) - z := by
    intro j; simp only [ha_def, LebesgueCover.nxt, pt_mod]
  have hdet' : ∀ j < P.length, 0 < LebesgueCover.detC (a j) (a (LebesgueCover.nxt P.length j)) := by
    intro j hj; rw [hnxt]; exact hdet j hj
  have hwind' : LebesgueCover.turnSum a P.length < 4 * Real.pi := by
    unfold LebesgueCover.turnSum LebesgueCover.turn
    simp only [hnxt]
    exact hwind
  have h2pi := LebesgueCover.turnSum_eq_two_pi hn0 hdet' hwind'
  have hcum : LebesgueCover.cum a P.length P.length = LebesgueCover.cum a P.length 0 + 2 * Real.pi := by
    rw [LebesgueCover.cum_m_eq, h2pi]
  have hzK : z ∈ K := by
    have hc := centre_mem_convexHull (x := pt P) hn0 (z := z) (fun j hj => by rw [pt_mod]; exact hdet j hj)
    refine (convexHull_min ?_ hK) hc
    rintro _ ⟨j, -, rfl⟩
    exact hP _ (pt_mem P hn0 j)
  have hx : ∀ j < P.length, z + a j ∈ K := by
    intro j _; simp only [ha_def, add_sub_cancel]; exact hP _ (pt_mem P hn0 j)
  have ha0 : ∀ j < P.length, a j ≠ 0 := fun j hj => LebesgueCover.ne_zero_of_detC_pos (hdet' j hj)
  have key := LebesgueCover.fan_area_le hK hn0 hzK hx ha0 hdet' hcum
  have htel : ∑ j ∈ Finset.range P.length, (cross (pt P (j + 1)) z - cross (pt P j) z) = 0 := by
    rw [Finset.sum_range_sub (fun j => cross (pt P j) z)]
    have e : pt P P.length = pt P 0 := pt_congr P (by simp)
    simp only [e, sub_self]
  have hsum : ∑ j ∈ Finset.range P.length, LebesgueCover.detC (a j) (a (LebesgueCover.nxt P.length j)) =
      ∑ j ∈ Finset.range P.length, cross (pt P j) (pt P (j + 1)) := by
    have e : ∀ j, LebesgueCover.detC (a j) (a (LebesgueCover.nxt P.length j)) =
        cross (pt P j) (pt P (j + 1)) + (cross (pt P (j + 1)) z - cross (pt P j) z) := by
      intro j
      rw [hnxt]
      simp only [ha_def, LebesgueCover.detC, cross, Complex.sub_re, Complex.sub_im]
      ring
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, htel, add_zero]
  have hs : shoelace P = ∑ j ∈ Finset.range P.length,
      LebesgueCover.detC (a j) (a (LebesgueCover.nxt P.length j)) / 2 := by
    rw [← Finset.sum_div, hsum]; rfl
  rw [hs]; exact key

/-- Chord trees of the certificate (`"s"`, `["f", r]`, `["c", s, t, left, right]`). -/
inductive CTree where
  | small
  | vfan (r : ℕ)
  | cut (s t : ℕ) (left right : CTree)

/-- **Vertex fans** (Keller, Lemma 3.4), for the list rotated to start at position `r`: with `ξᵢ = Qᵢ - Q₀`,
`det(ξ₁, ξᵢ) > 0` for `2 ≤ i < m` and `det(ξᵢ, ξᵢ₊₁) > 0` for `2 ≤ i < m - 1`. -/
def VFanCond (P : List ℂ) (r : ℕ) : Prop :=
  3 ≤ P.length ∧
    (∀ i, 2 ≤ i → i < P.length →
      0 < cross (pt (P.rotate r) 1 - pt (P.rotate r) 0) (pt (P.rotate r) i - pt (P.rotate r) 0)) ∧
    (∀ i, 2 ≤ i → i + 1 < P.length →
      0 < cross (pt (P.rotate r) i - pt (P.rotate r) 0) (pt (P.rotate r) (i + 1) - pt (P.rotate r) 0))

/-- Validity of a chord tree: the conditions of `wcheck_v2.chord_ok`, `vertex_fan_ok`. A cut at the chord
`(P_s, P_t)` with `2 ≤ (t - s) mod n ≤ n - 2` needs `P_s ≠ P_t`, the points strictly between `s` and `t` in the closed
right half-plane of `P_s → P_t` and those strictly between `t` and `s` in the closed left half-plane; the two pieces
`P_s, …, P_t` and `P_t, …, P_s` are then valid. -/
def ChordOK : CTree → List ℂ → Prop
  | .small, P => P.length ≤ 4
  | .vfan r, P => r < P.length ∧ VFanCond P r
  | .cut s t L R, P =>
      s < P.length ∧ t < P.length ∧ 2 ≤ (t + P.length - s) % P.length ∧
        (t + P.length - s) % P.length + 2 ≤ P.length ∧ pt P s ≠ pt P t ∧
        (∀ k, 1 ≤ k → k < (t + P.length - s) % P.length →
          cross (pt P t - pt P s) (pt P (s + k) - pt P s) ≤ 0) ∧
        (∀ k, 1 ≤ k → k < P.length - (t + P.length - s) % P.length →
          0 ≤ cross (pt P t - pt P s) (pt P (t + k) - pt P s)) ∧
        ChordOK L ((List.range ((t + P.length - s) % P.length + 1)).map fun k => pt P (s + k)) ∧
        ChordOK R ((List.range (P.length - (t + P.length - s) % P.length + 1)).map fun k => pt P (t + k))

/-! ### Helpers for the chord decomposition: rotation, vertex fans and the cut identity -/

section

open Set

/-- Sums of a function of period `n` over `n` consecutive indices do not depend on the start. -/
lemma sum_range_shift {g : ℕ → ℝ} {n : ℕ} (hg : ∀ j, g (j + n) = g j) (s : ℕ) :
    ∑ k ∈ Finset.range n, g (s + k) = ∑ k ∈ Finset.range n, g k := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := Finset.sum_range_succ (fun k => g (s + k)) n
    have h2 := Finset.sum_range_succ' (fun k => g (s + k)) n
    rw [← ih]
    have e : ∀ k, s + 1 + k = s + (k + 1) := fun k => by ring
    simp only [e]
    have hn : g (s + n) = g s := by rw [hg]
    simp only [add_zero] at h2
    linarith

/-- The shoelace is invariant under rotation of the list. -/
lemma shoelace_rotate (P : List ℂ) (r : ℕ) : shoelace (P.rotate r) = shoelace P := by
  have hpt : ∀ j, pt (P.rotate r) j = pt P (j + r) := by
    intro j
    rcases Nat.eq_zero_or_pos P.length with h0 | hpos
    · have : P = [] := List.eq_nil_of_length_eq_zero h0
      subst this; simp [pt]
    · simp only [pt, List.length_rotate]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_rotate]; exact Nat.mod_lt _ hpos),
        List.getD_eq_getElem _ _ (Nat.mod_lt _ hpos), List.getElem_rotate]
      congr 1
      rw [Nat.mod_add_mod]
  unfold shoelace
  rw [List.length_rotate]
  congr 1
  simp only [hpt]
  have e : ∀ k, k + 1 + r = r + k + 1 := fun k => by ring
  simp only [e, add_comm _ r]
  exact sum_range_shift (g := fun j => cross (pt P j) (pt P (j + 1)))
    (fun j => by simp only [show j + P.length + 1 = j + 1 + P.length by ring, pt_add_length]) r

/-- A vertex fan at a leaf of the chord tree. -/
lemma vfan_le (K : Set ℂ) (hK : Convex ℝ K) (P : List ℂ) (hP : ∀ x ∈ P, x ∈ K) (r : ℕ) (hv : VFanCond P r) :
    ENNReal.ofReal (shoelace P) ≤ volume K := by
  obtain ⟨h3, h1, h2⟩ := hv
  set Q := P.rotate r with hQ
  have hQl : Q.length = P.length := List.length_rotate P r
  have hfan : MoserWorm.FanConditions Q := by
    refine ⟨by omega, fun i hi2 hi => ?_, fun i hi2 hi => ?_⟩
    · have := h1 i hi2 (by omega)
      rwa [pt_of_lt Q (by omega), pt_of_lt Q (by omega), pt_of_lt Q (by omega)] at this
    · have := h2 i hi2 (by omega)
      rwa [pt_of_lt Q (by omega), pt_of_lt Q (by omega), pt_of_lt Q (by omega)] at this
  have hmem : ∀ p ∈ Q, p ∈ K := fun p hp => hP p (List.mem_rotate.mp hp)
  have key := (MoserWorm.fan_shoelace_pos_le_volume Q hfan hK hmem).2
  rw [← shoelace_eq_keller, hQ, shoelace_rotate] at key
  exact key

/-- The shoelace of `f s, f (s + 1), …, f (s + d)`. -/
lemma shoelace_range_map (f : ℕ → ℂ) (s d : ℕ) :
    shoelace ((List.range (d + 1)).map fun k => f (s + k)) =
      (∑ k ∈ Finset.range d, cross (f (s + k)) (f (s + k + 1)) + cross (f (s + d)) (f s)) / 2 := by
  have hl : ((List.range (d + 1)).map fun k => f (s + k)).length = d + 1 := by simp
  have hget : ∀ k, k < d + 1 → pt ((List.range (d + 1)).map fun k => f (s + k)) k = f (s + k) := by
    intro k hk
    rw [pt_of_lt _ (by rw [hl]; exact hk), List.getD_eq_getElem _ _ (by rw [hl]; exact hk)]
    simp
  unfold shoelace
  rw [hl, Finset.sum_range_succ]
  congr 2
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [hget k (by omega), hget (k + 1) (by omega), add_assoc]
  · rw [hget d (by omega), pt_congr _ (show (d + 1) % _ = 0 % _ by rw [hl, Nat.mod_self, Nat.zero_mod]),
      hget 0 (by omega), add_zero]

/-- For `d = (t + n - s) mod n`: `s + d ≡ t` and `t + (n - d) ≡ s` modulo `n`. -/
lemma cut_mods {n s t : ℕ} (hs : s < n) (ht : t < n) :
    (s + (t + n - s) % n) % n = t ∧ (t + (n - (t + n - s) % n)) % n = s := by
  by_cases hts : t < s
  · have hd : (t + n - s) % n = t + n - s := Nat.mod_eq_of_lt (by omega)
    rw [hd]
    constructor
    · rw [show s + (t + n - s) = t + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
    · rw [show t + (n - (t + n - s)) = s by omega, Nat.mod_eq_of_lt hs]
  · have hd : (t + n - s) % n = t - s := by
      rw [show t + n - s = (t - s) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hd]
    constructor
    · rw [show s + (t - s) = t by omega, Nat.mod_eq_of_lt ht]
    · rw [show t + (n - (t - s)) = s + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hs]

end

/-- **Chord decomposition** (Keller, Lemma 3.5) with vertex fans and small lists at the leaves of the chord tree. -/
theorem chord_le (K : Set ℂ) (hK : Convex ℝ K) (P : List ℂ) (hP : ∀ x ∈ P, x ∈ K) (T : CTree)
    (h : ChordOK T P) : ENNReal.ofReal (shoelace P) ≤ volume K := by
  induction T generalizing K P with
  | small => exact small_le K hK P hP h
  | vfan r => exact vfan_le K hK P hP r h.2
  | cut s t L R ihL ihR =>
    obtain ⟨hs, ht, hd2, hdn, hne, hright, hleft, hL, hR⟩ := h
    obtain ⟨hmod1, hmod2⟩ := cut_mods hs ht
    set n := P.length with hn
    set d := (t + n - s) % n with hd
    have hn0 : 0 < n := by omega
    have hpt1 : pt P (s + d) = pt P t := pt_congr P (by rw [hmod1, Nat.mod_eq_of_lt ht])
    have hpt2 : pt P (t + (n - d)) = pt P s := pt_congr P (by rw [hmod2, Nat.mod_eq_of_lt hs])
    set v := pt P t - pt P s with hv
    have hv0 : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hcv0 : cross v (pt P s - pt P s) = 0 := by simp [cross]
    have hcvv : cross v (pt P t - pt P s) = 0 := by simp only [hv, cross]; ring
    have hP1 : ∀ x ∈ (List.range (d + 1)).map (fun k => pt P (s + k)),
        x ∈ K ∩ {x : ℂ | cross v (x - pt P s) ≤ 0} := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      have hk' := List.mem_range.mp hk
      refine ⟨hP _ (pt_mem P hn0 _), ?_⟩
      show cross v (pt P (s + k) - pt P s) ≤ 0
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [add_zero, hcv0]
      · rcases Nat.lt_or_ge k d with hkd | hkd
        · exact hright k hk0 hkd
        · have hkd' : k = d := by omega
          rw [hkd', hpt1, hcvv]
    have hP2 : ∀ x ∈ (List.range (n - d + 1)).map (fun k => pt P (t + k)),
        x ∈ K ∩ {x : ℂ | 0 ≤ cross v (x - pt P s)} := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      have hk' := List.mem_range.mp hk
      refine ⟨hP _ (pt_mem P hn0 _), ?_⟩
      show 0 ≤ cross v (pt P (t + k) - pt P s)
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [add_zero, hcvv]
      · rcases Nat.lt_or_ge k (n - d) with hkd | hkd
        · exact hleft k hk0 hkd
        · have hkd' : k = n - d := by omega
          rw [hkd', hpt2, hcv0]
    have h1 := ihL (K ∩ {x : ℂ | cross v (x - pt P s) ≤ 0}) (hK.inter (convex_halfplane_le v (pt P s))) _ hP1 hL
    have h2 := ihR (K ∩ {x : ℂ | 0 ≤ cross v (x - pt P s)}) (hK.inter (convex_halfplane_ge v (pt P s))) _ hP2 hR
    -- the closing edges of the two pieces cancel, and the remaining edges are those of `P`
    have hg : ∀ j, cross (pt P (j + n)) (pt P (j + n + 1)) = cross (pt P j) (pt P (j + 1)) := by
      intro j; rw [pt_add_length, show j + n + 1 = j + 1 + n by ring, pt_add_length]
    have hst : ∀ k, pt P (t + k) = pt P (s + d + k) := by
      intro k
      apply pt_congr
      have h0 : (s + d) % n = t % n := by rw [hmod1, Nat.mod_eq_of_lt ht]
      exact (Nat.ModEq.add_right k h0).symm
    have hB : ∑ k ∈ Finset.range (n - d), cross (pt P (t + k)) (pt P (t + k + 1)) =
        ∑ k ∈ Finset.range (n - d), cross (pt P (s + (d + k))) (pt P (s + (d + k) + 1)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hst k, show t + k + 1 = t + (k + 1) by ring, hst (k + 1)]
      congr 2 <;> ring_nf
    have hfull : ∑ k ∈ Finset.range d, cross (pt P (s + k)) (pt P (s + k + 1)) +
        ∑ k ∈ Finset.range (n - d), cross (pt P (s + (d + k))) (pt P (s + (d + k) + 1)) =
        ∑ k ∈ Finset.range n, cross (pt P k) (pt P (k + 1)) := by
      have e := Finset.sum_range_add (fun k => cross (pt P (s + k)) (pt P (s + k + 1))) d (n - d)
      rw [show d + (n - d) = n by omega] at e
      rw [← e]
      exact sum_range_shift (g := fun j => cross (pt P j) (pt P (j + 1))) hg s
    have hsplit : shoelace P = shoelace ((List.range (d + 1)).map fun k => pt P (s + k)) +
        shoelace ((List.range (n - d + 1)).map fun k => pt P (t + k)) := by
      rw [shoelace_range_map, shoelace_range_map, hpt1, hpt2, hB]
      unfold shoelace
      rw [← hn, ← hfull]
      have hc : cross (pt P t) (pt P s) + cross (pt P s) (pt P t) = 0 := by simp only [cross]; ring
      linarith
    calc ENNReal.ofReal (shoelace P)
        ≤ ENNReal.ofReal (shoelace ((List.range (d + 1)).map fun k => pt P (s + k))) +
          ENNReal.ofReal (shoelace ((List.range (n - d + 1)).map fun k => pt P (t + k))) := by
          rw [hsplit]; exact ENNReal.ofReal_add_le
      _ ≤ volume (K ∩ {x : ℂ | cross v (x - pt P s) ≤ 0}) + volume (K ∩ {x : ℂ | 0 ≤ cross v (x - pt P s)}) :=
          add_le_add h1 h2
      _ ≤ volume K := volume_halfplanes_le K v (pt P s) hv0

/-! ## The five arcs of the family and their vertices -/

/-- The polygonal arc with start `a` and steps `ℓᵢ e^{iθᵢ}` (`θᵢ` in degrees), at unit speed:
`γ(s) = a + ∑ᵢ min(max(s - Lᵢ, 0), ℓᵢ) e^{iθᵢ}` with `Lᵢ = ℓ₀ + … + ℓᵢ₋₁`. -/
def stepArc (a : ℂ) (steps : List (ℝ × ℝ)) (s : ℝ) : ℂ :=
  a + ((List.range steps.length).map fun i =>
    ((min (max (s - ((steps.take i).map Prod.fst).sum) 0) (steps.getD i (0, 0)).1 : ℝ) : ℂ) *
      Complex.exp ((((steps.getD i (0, 0)).2 * Real.pi / 180 : ℝ) : ℂ) * Complex.I)).sum

/-- Its vertices `a, a + ℓ₀e^{iθ₀}, …`. -/
def stepVertices (a : ℂ) : List (ℝ × ℝ) → List ℂ
  | [] => [a]
  | st :: rest => a :: stepVertices (a + (st.1 : ℂ) * Complex.exp (((st.2 * Real.pi / 180 : ℝ) : ℂ) * Complex.I)) rest

/-! ### Helpers: the arc step by step, its length and its vertices -/

section

open Set

/-- The unit vector `e^{iθ}` of a step direction `θ` (in degrees). -/
def dirOf (θ : ℝ) : ℂ := Complex.exp (((θ * Real.pi / 180 : ℝ) : ℂ) * Complex.I)

lemma norm_dirOf (θ : ℝ) : ‖dirOf θ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma stepArc_nil (a : ℂ) (s : ℝ) : stepArc a [] s = a := by simp [stepArc]

lemma stepArc_base (a : ℂ) (steps : List (ℝ × ℝ)) (s : ℝ) : stepArc a steps s = a + stepArc 0 steps s := by
  simp [stepArc]

lemma stepArc_cons (a : ℂ) (st : ℝ × ℝ) (rest : List (ℝ × ℝ)) (s : ℝ) :
    stepArc a (st :: rest) s = stepArc (a + ((min (max s 0) st.1 : ℝ) : ℂ) * dirOf st.2) rest (s - st.1) := by
  unfold stepArc dirOf
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  simp only [List.take_zero, List.map_nil, List.sum_nil, sub_zero, List.getD_cons_zero]
  rw [add_assoc]
  congr 2
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply, List.take_succ_cons, List.map_cons, List.sum_cons, List.getD_cons_succ]
  congr 4
  ring

lemma stepArc_of_nonpos {steps : List (ℝ × ℝ)} (hnn : ∀ st ∈ steps, 0 ≤ st.1) (a : ℂ) {s : ℝ} (hs : s ≤ 0) :
    stepArc a steps s = a := by
  induction steps generalizing a s with
  | nil => exact stepArc_nil a s
  | cons st rest ih =>
    have hl : 0 ≤ st.1 := hnn st (by simp)
    rw [stepArc_cons, max_eq_right hs, min_eq_left hl]
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    exact ih (fun st' h' => hnn st' (by simp [h'])) a (by linarith)

lemma stepArc_cons_shift (a : ℂ) {st : ℝ × ℝ} (rest : List (ℝ × ℝ)) (hl : 0 ≤ st.1) {x : ℝ} (hx : 0 ≤ x) :
    stepArc a (st :: rest) (st.1 + x) = stepArc (a + (st.1 : ℂ) * dirOf st.2) rest x := by
  rw [stepArc_cons, max_eq_left (by linarith), min_eq_right (by linarith), add_sub_cancel_left]

/-- `clamp s ℓ + clamp (s - ℓ) T = clamp s (ℓ + T)` for `ℓ, T ≥ 0`, with `clamp s c = min (max s 0) c`. -/
lemma clamp_add {ℓ T : ℝ} (hl : 0 ≤ ℓ) (hT : 0 ≤ T) (s : ℝ) :
    min (max s 0) ℓ + min (max (s - ℓ) 0) T = min (max s 0) (ℓ + T) := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma clamp_mono {c s s' : ℝ} (h : s ≤ s') : min (max s 0) c ≤ min (max s' 0) c :=
  min_le_min (max_le_max h le_rfl) le_rfl

lemma clamp_sub_le {c s s' : ℝ} (h : s ≤ s') : min (max s' 0) c - min (max s 0) c ≤ s' - s := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- Movement along the arc is bounded by the movement of the clamped parameter. -/
lemma stepArc_dist_le {steps : List (ℝ × ℝ)} (hnn : ∀ st ∈ steps, 0 ≤ st.1) (a : ℂ) {s s' : ℝ} (h : s ≤ s') :
    ‖stepArc a steps s' - stepArc a steps s‖ ≤
      min (max s' 0) (steps.map Prod.fst).sum - min (max s 0) (steps.map Prod.fst).sum := by
  induction steps generalizing a s s' with
  | nil => simp [stepArc_nil]
  | cons st rest ih =>
    have hl : 0 ≤ st.1 := hnn st (by simp)
    have hnn' : ∀ st' ∈ rest, 0 ≤ st'.1 := fun st' h' => hnn st' (by simp [h'])
    have hT : 0 ≤ (rest.map Prod.fst).sum := List.sum_nonneg (by
      intro x hx; obtain ⟨st', h', rfl⟩ := List.mem_map.mp hx; exact hnn' st' h')
    rw [stepArc_cons, stepArc_cons, stepArc_base _ rest (s' - st.1), stepArc_base _ rest (s - st.1)]
    have e : a + ((min (max s' 0) st.1 : ℝ) : ℂ) * dirOf st.2 + stepArc 0 rest (s' - st.1) -
        (a + ((min (max s 0) st.1 : ℝ) : ℂ) * dirOf st.2 + stepArc 0 rest (s - st.1)) =
        (((min (max s' 0) st.1 - min (max s 0) st.1 : ℝ)) : ℂ) * dirOf st.2 +
          (stepArc 0 rest (s' - st.1) - stepArc 0 rest (s - st.1)) := by
      push_cast; ring
    rw [e]
    have h1 := ih hnn' 0 (show s - st.1 ≤ s' - st.1 by linarith)
    have h2 : ‖(((min (max s' 0) st.1 - min (max s 0) st.1 : ℝ)) : ℂ) * dirOf st.2‖ =
        min (max s' 0) st.1 - min (max s 0) st.1 := by
      rw [norm_mul, norm_dirOf, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (clamp_mono h))]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (min (max s' 0) st.1 - min (max s 0) st.1) +
          (min (max (s' - st.1) 0) (rest.map Prod.fst).sum - min (max (s - st.1) 0) (rest.map Prod.fst).sum) := by
          rw [h2]; linarith
      _ = _ := by
          simp only [List.map_cons, List.sum_cons]
          rw [← clamp_add hl hT s', ← clamp_add hl hT s]
          ring

lemma stepArc_continuous (steps : List (ℝ × ℝ)) (a : ℂ) : Continuous (stepArc a steps) := by
  induction steps generalizing a with
  | nil => rw [show stepArc a [] = fun _ => a from funext (stepArc_nil a)]; exact continuous_const
  | cons st rest ih =>
    have e : stepArc a (st :: rest) = fun s =>
        a + ((min (max s 0) st.1 : ℝ) : ℂ) * dirOf st.2 + stepArc 0 rest (s - st.1) := by
      funext s; rw [stepArc_cons, stepArc_base]
    rw [e]
    refine (continuous_const.add ((Complex.continuous_ofReal.comp
      ((continuous_id.max continuous_const).min continuous_const)).mul continuous_const)).add
      ((ih 0).comp (continuous_id.sub continuous_const))

lemma stepArc_lipschitz {steps : List (ℝ × ℝ)} (hnn : ∀ st ∈ steps, 0 ≤ st.1) (a : ℂ) :
    LipschitzWith 1 (stepArc a steps) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs]
  rcases le_total x y with hxy | hxy
  · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact (stepArc_dist_le hnn a hxy).trans (clamp_sub_le hxy)
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact (stepArc_dist_le hnn a hxy).trans (clamp_sub_le hxy)

lemma stepArc_variation_ge {steps : List (ℝ × ℝ)} (hnn : ∀ st ∈ steps, 0 ≤ st.1) (a : ℂ) :
    ENNReal.ofReal (steps.map Prod.fst).sum ≤ eVariationOn (stepArc a steps) (Icc 0 (steps.map Prod.fst).sum) := by
  induction steps generalizing a with
  | nil => simp
  | cons st rest ih =>
    have hl : 0 ≤ st.1 := hnn st (by simp)
    have hnn' : ∀ st' ∈ rest, 0 ≤ st'.1 := fun st' h' => hnn st' (by simp [h'])
    have hT : 0 ≤ (rest.map Prod.fst).sum := List.sum_nonneg (by
      intro x hx; obtain ⟨st', h', rfl⟩ := List.mem_map.mp hx; exact hnn' st' h')
    simp only [List.map_cons, List.sum_cons]
    set T := (rest.map Prod.fst).sum
    have hsplit := eVariationOn.Icc_add_Icc (stepArc a (st :: rest)) (s := univ) (a := 0) (b := st.1)
      (c := st.1 + T) hl (by linarith) (mem_univ _)
    simp only [univ_inter] at hsplit
    rw [← hsplit, ENNReal.ofReal_add hl hT]
    gcongr
    · -- the first step: from `a` to `a + ℓ e^{iθ}`
      have h0 : stepArc a (st :: rest) 0 = a := stepArc_of_nonpos hnn a le_rfl
      have hℓ : stepArc a (st :: rest) st.1 = a + (st.1 : ℂ) * dirOf st.2 := by
        have := stepArc_cons_shift a rest hl (le_refl (0 : ℝ))
        rw [add_zero] at this
        rw [this, stepArc_of_nonpos hnn' _ le_rfl]
      have hle := eVariationOn.edist_le (stepArc a (st :: rest)) (left_mem_Icc.mpr hl) (right_mem_Icc.mpr hl)
      rw [h0, hℓ, edist_dist, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, norm_dirOf, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl] at hle
      exact hle
    · -- the remaining steps, after the shift `x ↦ ℓ + x`
      have hmono : MonotoneOn (fun x : ℝ => st.1 + x) (Icc 0 T) := fun x _ y _ hxy => by simp [hxy]
      have himg : (fun x : ℝ => st.1 + x) '' Icc 0 T = Icc st.1 (st.1 + T) := by
        rw [image_const_add_Icc, add_zero]
      have heq : EqOn (stepArc a (st :: rest) ∘ fun x => st.1 + x) (stepArc (a + (st.1 : ℂ) * dirOf st.2) rest)
          (Icc 0 T) := fun x hx => stepArc_cons_shift a rest hl hx.1
      rw [← himg, ← eVariationOn.comp_eq_of_monotoneOn _ _ hmono, eVariationOn.eq_of_eqOn heq]
      exact ih hnn' _

lemma stepArc_variation_le {steps : List (ℝ × ℝ)} (hnn : ∀ st ∈ steps, 0 ≤ st.1) (a : ℂ) :
    eVariationOn (stepArc a steps) (Icc 0 1) ≤ 1 := by
  have h := ((stepArc_lipschitz hnn a).lipschitzOnWith (s := univ)).comp_eVariationOn_le
    (mapsTo_univ id (Icc (0 : ℝ) 1))
  simp only [Function.comp_id, eVariationOn_id_Icc, sub_zero, ENNReal.ofReal_one, ENNReal.coe_one,
    one_mul] at h
  exact h

/-- Every vertex is a point of the arc, at a parameter in `[0, total length]`. -/
lemma stepVertices_mem {steps : List (ℝ × ℝ)} (hnn : ∀ st ∈ steps, 0 ≤ st.1) (a : ℂ) :
    ∀ v ∈ stepVertices a steps, ∃ x ∈ Icc 0 (steps.map Prod.fst).sum, stepArc a steps x = v := by
  induction steps generalizing a with
  | nil =>
    intro v hv
    simp only [stepVertices, List.mem_singleton] at hv
    exact ⟨0, by simp, by rw [hv, stepArc_nil]⟩
  | cons st rest ih =>
    have hl : 0 ≤ st.1 := hnn st (by simp)
    have hnn' : ∀ st' ∈ rest, 0 ≤ st'.1 := fun st' h' => hnn st' (by simp [h'])
    have hT : 0 ≤ (rest.map Prod.fst).sum := List.sum_nonneg (by
      intro x hx; obtain ⟨st', h', rfl⟩ := List.mem_map.mp hx; exact hnn' st' h')
    intro v hv
    simp only [stepVertices, List.mem_cons] at hv
    simp only [List.map_cons, List.sum_cons]
    rcases hv with rfl | hv
    · exact ⟨0, ⟨le_rfl, by linarith⟩, stepArc_of_nonpos hnn _ le_rfl⟩
    · obtain ⟨x, hx, hxv⟩ := ih hnn' _ v hv
      refine ⟨st.1 + x, ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
      rw [stepArc_cons_shift a rest hl hx.1]
      exact hxv

end

/-- **Arcs** (part): a polygonal arc of total length `1` with positive steps is a unit arc, and a set that covers it
under a proper rigid motion contains the moved vertices. -/
theorem stepArc_isUnitArc (a : ℂ) (steps : List (ℝ × ℝ)) (hpos : ∀ s ∈ steps, 0 < s.1)
    (hlen : (steps.map Prod.fst).sum = 1) : IsUnitArc (stepArc a steps) := by
  have hnn : ∀ st ∈ steps, 0 ≤ st.1 := fun st h => (hpos st h).le
  refine ⟨(stepArc_continuous steps a).continuousOn, le_antisymm (stepArc_variation_le hnn a) ?_⟩
  have h := stepArc_variation_ge hnn a
  rw [hlen, ENNReal.ofReal_one] at h
  exact h

theorem vertices_mem_of_coversM {K : Set ℂ} {a : ℂ} {steps : List (ℝ × ℝ)} (hpos : ∀ s ∈ steps, 0 < s.1)
    (hlen : (steps.map Prod.fst).sum = 1) (h : CoversM K (stepArc a steps)) :
    ∃ θ : ℝ, ∃ t : ℂ, ∀ v ∈ stepVertices a steps, motion θ t v ∈ K := by
  obtain ⟨θ, t, hsub⟩ := h
  refine ⟨θ, t, fun v hv => hsub ⟨v, ?_, rfl⟩⟩
  obtain ⟨x, hx, hxv⟩ := stepVertices_mem (fun st h => (hpos st h).le) a v hv
  rw [hlen] at hx
  exact ⟨x, hx, hxv⟩

end Worm.Geom
