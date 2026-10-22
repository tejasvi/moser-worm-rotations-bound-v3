import WormSound.IvSound.Pair
import WormSound.IvSound.Fam
import WormSound.IvSound.Turning

/-!
# Validity of the structures that pass `stOK` (fan, vertex fan, chord tree, small list)

For the checker's context `C = mkCtx F lo hi` of a box, every structure with `stOK C maxsmall st = true` satisfies at
every placement `x` of the box the hypotheses of `Worm.Geom.small_le`, `fan_le`, `chord_le` for its placed vertices
(`StValid`, with `pos` for the positions):

* fan: positive turns from `fanDetLo` (`fanDetLo_le`), the winding at the box centre from the `P`/`D` tables and
  `windCost` (`turning_lt_of_windCost'`), carried to the box by continuity (`turning_const'`);
* vertex fans and chord cuts: the signs of `det3` (`mem_det3`) and the chord length test (`pairMove_mem`).
-/

open MoserWorm Complex
open Worm.Geom (pt CTree ChordOK VFanCond)

namespace WormCore

namespace IvSound

open WormCore.Sound (InBox)

variable {F : Fam} {q : Nat → ℂ} {lo hi : Array Int}

/-! ### Lists of global vertices -/

lemma pt_map (f : ℕ → ℂ) {l : List ℕ} (hl : 0 < l.length) (j : ℕ) : pt (l.map f) j = f (at' l j) := by
  unfold pt at'
  rw [List.length_map, List.getD_eq_getElem _ _ (by simpa using Nat.mod_lt j hl),
    List.getD_eq_getElem _ _ (Nat.mod_lt j hl)]
  simp

lemma at'_mem {l : List ℕ} (hl : 0 < l.length) (j : ℕ) : at' l j ∈ l := by
  unfold at'; rw [List.getD_eq_getElem _ _ (Nat.mod_lt j hl)]; exact List.getElem_mem _

lemma toArray_getElem!_eq_at' {l : List ℕ} {j : ℕ} (hj : j < l.length) : l.toArray[j]! = at' l j := by
  unfold at'
  rw [Nat.mod_eq_of_lt hj, List.getD_eq_getElem _ _ hj]
  simp [hj]

/-- A lookup in a two-level table built over `range m × range (m + 1)` that is `true` comes from the table function. -/
lemma table_true {m : ℕ} (f : ℕ → ℕ → Bool) {i d : ℕ}
    (h : (((List.range m).toArray.map fun i => (List.range (m + 1)).toArray.map fun d => f i d)[i]!)[d]! = true) :
    i < m ∧ d < m + 1 ∧ f i d = true := by
  by_cases hi : i < m
  · by_cases hd : d < m + 1
    · simp [hi, hd] at h; exact ⟨hi, hd, h⟩
    · simp [hi, hd] at h
  · simp [hi] at h
    have hdef : ((default : Array Bool))[d]! = false := by show ((#[] : Array Bool))[d]! = false; rfl
    rw [hdef] at h
    exact absurd h (by decide)

/-! ### Signs of the checker's bounds -/

lemma det3_pos (hF : FamSpec F q) (hB : BoxOK lo hi) {a b i : ℕ} (ha : a < F.body.size) (hb : b < F.body.size)
    (hi' : i < F.body.size) {x : Fin 12 → ℝ} (hx : InBox lo hi x) (h : 0 < det3Lo (mkCtx F lo hi) a b i) :
    0 < Worm.Geom.cross (pos F q x b - pos F q x a) (pos F q x i - pos F q x a) := by
  have hm := lo_le (mem_det3 hF hB ha hb hi' hx)
  have h' : (0 : ℝ) < ((det3 (mkCtx F lo hi) a b i).lo : ℝ) / 2 ^ dfxS :=
    div_pos (by exact_mod_cast h) two_pow_dfxS_pos
  exact lt_of_lt_of_le h' hm

lemma det3_nonneg (hF : FamSpec F q) (hB : BoxOK lo hi) {a b i : ℕ} (ha : a < F.body.size) (hb : b < F.body.size)
    (hi' : i < F.body.size) {x : Fin 12 → ℝ} (hx : InBox lo hi x) (h : 0 ≤ det3Lo (mkCtx F lo hi) a b i) :
    0 ≤ Worm.Geom.cross (pos F q x b - pos F q x a) (pos F q x i - pos F q x a) := by
  have hm := lo_le (mem_det3 hF hB ha hb hi' hx)
  have h' : (0 : ℝ) ≤ ((det3 (mkCtx F lo hi) a b i).lo : ℝ) / 2 ^ dfxS :=
    div_nonneg (by exact_mod_cast h) two_pow_dfxS_pos.le
  exact le_trans h' hm

lemma det3_nonpos (hF : FamSpec F q) (hB : BoxOK lo hi) {a b i : ℕ} (ha : a < F.body.size) (hb : b < F.body.size)
    (hi' : i < F.body.size) {x : Fin 12 → ℝ} (hx : InBox lo hi x) (h : det3Hi (mkCtx F lo hi) a b i ≤ 0) :
    Worm.Geom.cross (pos F q x b - pos F q x a) (pos F q x i - pos F q x a) ≤ 0 := by
  have hm := le_hi (mem_det3 hF hB ha hb hi' hx)
  have h' : ((det3 (mkCtx F lo hi) a b i).hi : ℝ) / 2 ^ dfxS ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) two_pow_dfxS_pos.le
  exact le_trans hm h'

/-- The chord length test: the two ends of a cut are distinct on the whole box. -/
lemma chord_ends_ne (hF : FamSpec F q) (hB : BoxOK lo hi) {a b : ℕ} (ha : a < F.body.size) (hb : b < F.body.size)
    {x : Fin 12 → ℝ} (hx : InBox lo hi x)
    (h : 0 < ((V2.norm (diff (mkCtx F lo hi) a b)).sub (pairMove (mkCtx F lo hi) a b)).lo) :
    pos F q x a ≠ pos F q x b := by
  obtain ⟨r, hr, _, hmv⟩ := pairMove_mem hF ha hb hx
  have hn := V2.mem_norm (mem_diff hF hB ha hb)
  have hl := lo_le (DIval.mem_sub hn hr)
  have h' : (0 : ℝ) < (((V2.norm (diff (mkCtx F lo hi) a b)).sub (pairMove (mkCtx F lo hi) a b)).lo : ℝ) / 2 ^ dfxS :=
    div_pos (by exact_mod_cast h) two_pow_dfxS_pos
  intro heq
  have h1 : ‖posC F q lo hi b - posC F q lo hi a‖ ≤ r := by
    have : (pos F q x b - pos F q x a) - (posC F q lo hi b - posC F q lo hi a) =
        -(posC F q lo hi b - posC F q lo hi a) := by rw [heq]; ring
    rw [this, norm_neg] at hmv; exact hmv
  linarith

/-! ### Fans -/

lemma isPreconnected_inBox (lo hi : Array Int) : IsPreconnected {x : Fin 12 → ℝ | InBox lo hi x} := by
  apply Convex.isPreconnected
  intro x hx y hy a b ha hb hab i
  obtain ⟨hx1, hx2⟩ := hx i
  obtain ⟨hy1, hy2⟩ := hy i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : (lo[i.val]! : ℝ) / 2 ^ BS = a * ((lo[i.val]! : ℝ) / 2 ^ BS) + b * ((lo[i.val]! : ℝ) / 2 ^ BS) := by
    rw [← add_mul, hab, one_mul]
  have e2 : (hi[i.val]! : ℝ) / 2 ^ BS = a * ((hi[i.val]! : ℝ) / 2 ^ BS) + b * ((hi[i.val]! : ℝ) / 2 ^ BS) := by
    rw [← add_mul, hab, one_mul]
  constructor
  · rw [e1]; exact add_le_add (mul_le_mul_of_nonneg_left hx1 ha) (mul_le_mul_of_nonneg_left hy1 hb)
  · rw [e2]; exact add_le_add (mul_le_mul_of_nonneg_left hx2 ha) (mul_le_mul_of_nonneg_left hy2 hb)

lemma continuous_pos (g : ℕ) : Continuous fun x : Fin 12 → ℝ => pos F q x g := by
  unfold pos
  split_ifs
  · exact continuous_const
  · have hA : Continuous fun x : Fin 12 → ℝ => bodyAngle x F.body[g]! := by
      unfold bodyAngle; split_ifs
      · exact continuous_apply _
      · exact continuous_const
    have hT : Continuous fun x : Fin 12 → ℝ => bodyTrans x F.body[g]! := by
      unfold bodyTrans
      refine (Complex.continuous_ofReal.comp ?_).add ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
      · split_ifs
        · exact continuous_apply _
        · exact continuous_const
      · split_ifs
        · exact continuous_apply _
        · exact continuous_const
    exact hT.add ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hA).mul continuous_const)).mul
      continuous_const)

lemma fanCentre_eq_fanZ (zx zy : Int) : fanCentre zx zy = WormCore.Sound.fanZ zx zy := by
  apply Complex.ext
  · simp only [fanCentre, WormCore.Sound.fanZ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, add_zero, sub_self]
  · simp only [fanCentre, WormCore.Sound.fanZ, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, zero_add, add_zero]

theorem fan_valid (hF : FamSpec F q) (hB : BoxOK lo hi) (v : List ℕ) (zx zy : Int)
    (hv : ∀ g ∈ v, g < F.body.size) (h : fanOK (mkCtx F lo hi) v zx zy = true) {x : Fin 12 → ℝ}
    (hx : InBox lo hi x) :
    3 ≤ (v.map (pos F q x)).length ∧
      (∀ j < (v.map (pos F q x)).length,
        0 < Worm.Geom.cross (pt (v.map (pos F q x)) j - WormCore.Sound.fanZ zx zy)
          (pt (v.map (pos F q x)) (j + 1) - WormCore.Sound.fanZ zx zy)) ∧
      WormCore.Sound.turning (v.map (pos F q x)) (WormCore.Sound.fanZ zx zy) < 4 * Real.pi := by
  unfold fanOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true, List.mem_range] at h
  obtain ⟨⟨h3, hdets⟩, s0, hs0, hw⟩ := h
  set m := v.length with hmdef
  have hm : 0 < m := by omega
  rw [← fanCentre_eq_fanZ]
  set z := fanCentre zx zy
  have hlen : ∀ y : Fin 12 → ℝ, (v.map (pos F q y)).length = m := fun y => by simp [hmdef]
  have hptv : ∀ (y : Fin 12 → ℝ) j, pt (v.map (pos F q y)) j = pos F q y (at' v j) := fun y j => pt_map _ hm j
  have hva : ∀ j, j < m → v.toArray[j]! = at' v j := fun j hj => toArray_getElem!_eq_at' hj
  have hmem : ∀ j, at' v j < F.body.size := fun j => hv _ (at'_mem hm j)
  -- positive turns on the whole box
  have hdet : ∀ y, InBox lo hi y → ∀ j < m,
      0 < Worm.Geom.cross (pt (v.map (pos F q y)) j - z) (pt (v.map (pos F q y)) (j + 1) - z) := by
    intro y hy j hj
    have hd := hdets j hj
    rw [hva j hj, hva ((j + 1) % m) (Nat.mod_lt _ hm)] at hd
    have hle := fanDetLo_le hF hB (hmem j) (hmem ((j + 1) % m)) hy zx zy
    rw [hptv, hptv]
    have e : at' v (j + 1) = at' v ((j + 1) % m) := by unfold at'; rw [Nat.mod_mod]
    rw [e]
    have h' : (0 : ℝ) < ((fanDetLo (mkCtx F lo hi) (DIval.pt zx, DIval.pt zy) (at' v j) (at' v ((j + 1) % m)) : Int) : ℝ) /
        2 ^ dfxS := div_pos (by exact_mod_cast hd) two_pow_dfxS_pos
    exact lt_of_lt_of_le h' hle
  refine ⟨by rw [hlen]; exact h3, fun j hj => hdet x hx j (by rwa [hlen] at hj), ?_⟩
  -- the winding at the box centre
  set x0 := centrePt lo hi
  have hx0 : InBox lo hi x0 := centrePt_inBox hB
  have hpos0 : ∀ j, pos F q x0 (at' v j) = posC F q lo hi (at' v j) := fun j => pos_centrePt hF (hmem j)
  have hzm := mem_fanCentre zx zy
  have hw0 : WormCore.Sound.turning (v.map (pos F q x0)) z < 4 * Real.pi := by
    refine turning_lt_of_windCost' (v.map (pos F q x0)) z (by rw [hlen]; exact h3)
      (fun j hj => hdet x0 hx0 j (by rwa [hlen] at hj)) _ _ ?_ ?_ s0 (by rw [hlen]; exact hw)
    · intro i him d hPd
      rw [hlen] at him
      obtain ⟨-, -, hf⟩ := table_true _ hPd
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
      obtain ⟨⟨-, -⟩, hlo⟩ := hf
      rw [hva i him, hva ((i + d) % m) (Nat.mod_lt _ hm)] at hlo
      have hmd := lo_le (V2.mem_det (V2.mem_sub (mem_X0 hF hB (hmem i)) hzm)
        (V2.mem_sub (mem_X0 hF hB (hmem ((i + d) % m))) hzm))
      rw [hptv, hptv, hpos0, hpos0]
      have e : at' v (i + d) = at' v ((i + d) % m) := by unfold at'; rw [Nat.mod_mod]
      rw [e]
      have h' : (0 : ℝ) < ((V2.det (V2.sub (mkCtx F lo hi).X0[at' v i]! (DIval.pt zx, DIval.pt zy))
          (V2.sub (mkCtx F lo hi).X0[at' v ((i + d) % m)]! (DIval.pt zx, DIval.pt zy))).lo : ℝ) / 2 ^ dfxS :=
        div_pos (by exact_mod_cast hlo) two_pow_dfxS_pos
      exact lt_of_lt_of_le h' hmd
    · intro i him d hDd
      rw [hlen] at him
      obtain ⟨-, -, hf⟩ := table_true _ hDd
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
      obtain ⟨⟨-, -⟩, hlo⟩ := hf
      rw [hva i him, hva ((i + d) % m) (Nat.mod_lt _ hm)] at hlo
      have ha := V2.mem_sub (mem_X0 hF hB (hmem i)) hzm
      have hb := V2.mem_sub (mem_X0 hF hB (hmem ((i + d) % m))) hzm
      have hmd := lo_le (DIval.mem_add (DIval.mem_mul ha.1 hb.1) (DIval.mem_mul ha.2 hb.2))
      rw [hptv, hptv, hpos0, hpos0]
      have e : at' v (i + d) = at' v ((i + d) % m) := by unfold at'; rw [Nat.mod_mod]
      rw [e]
      have h' : (0 : ℝ) < ((((V2.sub (mkCtx F lo hi).X0[at' v i]! (DIval.pt zx, DIval.pt zy)).1.mul
          (V2.sub (mkCtx F lo hi).X0[at' v ((i + d) % m)]! (DIval.pt zx, DIval.pt zy)).1).add
          ((V2.sub (mkCtx F lo hi).X0[at' v i]! (DIval.pt zx, DIval.pt zy)).2.mul
          (V2.sub (mkCtx F lo hi).X0[at' v ((i + d) % m)]! (DIval.pt zx, DIval.pt zy)).2)).lo : ℝ) / 2 ^ dfxS :=
        div_pos (by exact_mod_cast hlo) two_pow_dfxS_pos
      exact lt_of_lt_of_le h' hmd
  -- continuity over the box
  refine turning_const' (isPreconnected_inBox lo hi) (fun y => v.map (pos F q y)) m hlen (fun j hj => ?_) z
    (fun y hy j hj => hdet y hy j hj) hx0 hw0 x hx
  have e : (fun y : Fin 12 → ℝ => (v.map (pos F q y)).getD j 0) = fun y => pos F q y v[j] := by
    funext y; rw [List.getD_eq_getElem _ _ (by simpa using hj)]; simp
  rw [e]
  exact (continuous_pos _).continuousOn

/-! ### Vertex fans and chord trees -/

theorem chord_valid (hF : FamSpec F q) (hB : BoxOK lo hi) {maxsmall : ℕ} (hms : maxsmall ≤ 4) {x : Fin 12 → ℝ}
    (hx : InBox lo hi x) :
    ∀ (t : CT) (piece : List ℕ), (∀ g ∈ piece, g < F.body.size) → chordOK (mkCtx F lo hi) maxsmall t piece = true →
      ChordOK (WormCore.Sound.ctOf t) (piece.map (pos F q x)) := by
  intro t
  induction t with
  | small =>
    intro piece _ h
    simp only [chordOK, decide_eq_true_eq] at h
    show (piece.map (pos F q x)).length ≤ 4
    rw [List.length_map]; omega
  | vfan r =>
    intro piece hp h
    simp only [chordOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hr, h3⟩, hv⟩ := h
    unfold vfanOK at hv
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hv
    obtain ⟨hv1, hv2⟩ := hv
    set l := piece.drop r ++ piece.take r with hl
    have hlen : l.length = piece.length := by simp [hl]; omega
    have hl0 : 0 < l.length := by omega
    have hrot : (piece.map (pos F q x)).rotate r = l.map (pos F q x) := by
      rw [← List.map_rotate, List.rotate_eq_drop_append_take (by omega)]
    have hmeml : ∀ j, at' l j < F.body.size := fun j => by
      have hj := at'_mem hl0 j
      rw [hl, List.mem_append] at hj
      rcases hj with hj | hj
      · exact hp _ (List.mem_of_mem_drop hj)
      · exact hp _ (List.mem_of_mem_take hj)
    refine ⟨by simpa using hr, by simpa using h3, fun i hi2 hi => ?_, fun i hi2 hi => ?_⟩
    · rw [hrot, pt_map _ hl0, pt_map _ hl0, pt_map _ hl0]
      rw [List.length_map] at hi
      rcases hv1 i hi with h0 | h0
      · omega
      · exact det3_pos hF hB (hmeml 0) (hmeml 1) (hmeml i) hx h0
    · rw [hrot, pt_map _ hl0, pt_map _ hl0, pt_map _ hl0]
      rw [List.length_map] at hi
      rcases hv2 i (by omega) with (h0 | h0) | h0
      · omega
      · omega
      · exact det3_pos hF hB (hmeml 0) (hmeml i) (hmeml (i + 1)) hx h0
  | cut s t L R ihL ihR =>
    intro piece hp h
    simp only [chordOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true]
      at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs, ht⟩, hd2⟩, hdn⟩, hne⟩, hright⟩, hleft⟩, hL⟩, hR⟩ := h
    set n := piece.length with hn
    have hn0 : 0 < n := by omega
    have hpt : ∀ j, pt (piece.map (pos F q x)) j = pos F q x (at' piece j) := fun j => pt_map _ hn0 j
    have hmem : ∀ j, at' piece j < F.body.size := fun j => hp _ (at'_mem hn0 j)
    simp only [ChordOK, WormCore.Sound.ctOf, List.length_map]
    refine ⟨hs, ht, hd2, hdn, ?_, fun k hk1 hk2 => ?_, fun k hk1 hk2 => ?_, ?_, ?_⟩
    · rw [hpt, hpt]; exact chord_ends_ne hF hB (hmem s) (hmem t) hx hne
    · rw [hpt, hpt, hpt]
      rcases hright k hk2 with h0 | h0
      · omega
      · exact det3_nonpos hF hB (hmem s) (hmem t) (hmem (s + k)) hx h0
    · rw [hpt, hpt, hpt]
      rcases hleft k hk2 with h0 | h0
      · omega
      · exact det3_nonneg hF hB (hmem s) (hmem t) (hmem (t + k)) hx h0
    · have := ihL ((List.range ((t + n - s) % n + 1)).map fun k => at' piece (s + k))
        (fun g hg => by obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg; exact hmem _) hL
      rw [List.map_map] at this
      convert this using 2
      funext k; simp only [Function.comp_apply, hpt]
    · have := ihR ((List.range (n - (t + n - s) % n + 1)).map fun k => at' piece (t + k))
        (fun g hg => by obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg; exact hmem _) hR
      rw [List.map_map] at this
      convert this using 2
      funext k; simp only [Function.comp_apply, hpt]

/-! ### Structures -/

theorem stOK_valid'' (hF : FamSpec F q) (hB : BoxOK lo hi) {maxsmall : ℕ} (hms : maxsmall ≤ 4) (st : St)
    (h : stOK (mkCtx F lo hi) maxsmall st = true) {x : Fin 12 → ℝ} (hx : InBox lo hi x) :
    WormCore.Sound.StValid (st.verts.map (pos F q x)) st := by
  cases st with
  | small v =>
    simp only [stOK, Bool.and_eq_true, decide_eq_true_eq] at h
    show (v.map (pos F q x)).length ≤ 4
    rw [List.length_map]; omega
  | fan v zx zy =>
    simp only [stOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨-, hv⟩, hf⟩ := h
    exact fan_valid hF hB v zx zy (fun g hg => by simpa using hv g hg) hf hx
  | chord v t =>
    simp only [stOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨-, hv⟩, hc⟩ := h
    exact chord_valid hF hB hms hx t v (fun g hg => by simpa using hv g hg) hc

end IvSound

end WormCore
