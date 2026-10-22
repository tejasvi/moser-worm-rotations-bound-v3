import WormSound.IvSound.Ctx

/-!
# The checker's family encloses the exact family (`mkFam`, `arcVerts`, `meanV`); the box facts

* `famSpec_mkFam`: `mkFam arcs gid` encloses `qReal arcs gid` (the exact body-frame points) — the step directions
  `degI d` (`|d| ≤ 360°`) are within the range of `sincosIv`;
* `place_eq_pos`: `WormCore.Sound.place` is `pos` for this family;
* `boxOK_of`: `AngleRange` and a point of the box give `BoxOK`.
-/

open MoserWorm Complex

namespace WormCore

namespace IvSound

open WormCore.Sound (InBox)

/-! ### Step directions -/

lemma piLo_lt : DIval.piLo < 4 * dfxOne := by norm_num [DIval.piLo, dfxOne]
lemma piLo_pos : 0 < DIval.piLo := by norm_num [DIval.piLo]

lemma ratio_range {d : Int} (hd1 : -360 ≤ d) (hd2 : d ≤ 360) :
    -(2 * dfxOne) ≤ (DIval.ratio d 180).lo ∧ (DIval.ratio d 180).lo ≤ 2 * dfxOne ∧
      -(2 * dfxOne) ≤ (DIval.ratio d 180).hi ∧ (DIval.ratio d 180).hi ≤ 2 * dfxOne := by
  simp only [DIval.ratio]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by norm_num), Int.fdiv_eq_ediv_of_nonneg _ (by norm_num)]
  simp only [dfxOne]
  omega

/-- The step-direction enclosures `degI d` (`|d| ≤ 360`) lie in the range of `sincosIv`. -/
lemma degI_range {d : Int} (hd1 : -360 ≤ d) (hd2 : d ≤ 360) :
    -(64 * dfxOne) ≤ (degI d).lo ∧ (degI d).hi ≤ 64 * dfxOne := by
  obtain ⟨h1, h2, h3, h4⟩ := ratio_range hd1 hd2
  set rl := (DIval.ratio d 180).lo
  set rh := (DIval.ratio d 180).hi
  simp only [degI, DIval.mul, DIval.piI]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by norm_num), Int.fdiv_eq_ediv_of_nonneg _ (by norm_num)]
  have hp1 := piLo_lt
  have hp0 := piLo_pos
  -- each endpoint product is at most `8 · dfxOne²` in absolute value
  have b1 : -(8 * dfxOne * dfxOne) ≤ DIval.piLo * rl ∧ DIval.piLo * rl ≤ 8 * dfxOne * dfxOne := by
    constructor <;> nlinarith
  have b2 : -(8 * dfxOne * dfxOne) ≤ DIval.piLo * rh ∧ DIval.piLo * rh ≤ 8 * dfxOne * dfxOne := by
    constructor <;> nlinarith
  have b3 : -(8 * dfxOne * dfxOne) ≤ (DIval.piLo + 1) * rl ∧ (DIval.piLo + 1) * rl ≤ 8 * dfxOne * dfxOne := by
    constructor <;> nlinarith
  have b4 : -(8 * dfxOne * dfxOne) ≤ (DIval.piLo + 1) * rh ∧ (DIval.piLo + 1) * rh ≤ 8 * dfxOne * dfxOne := by
    constructor <;> nlinarith
  generalize DIval.piLo * rl = p1 at *
  generalize DIval.piLo * rh = p2 at *
  generalize (DIval.piLo + 1) * rl = p3 at *
  generalize (DIval.piLo + 1) * rh = p4 at *
  simp only [dfxOne] at *
  constructor
  · have : -(8 * 72057594037927936 * 72057594037927936) ≤ min (min p1 p2) (min p3 p4) := by
      simp only [le_min_iff]; omega
    omega
  · have : max (max p1 p2) (max p3 p4) ≤ 8 * 72057594037927936 * 72057594037927936 := by
      simp only [max_le_iff]; omega
    omega

/-- `degI d` encloses `d · π / 180`. -/
lemma mem_degI (d : Int) : (d : ℝ) * Real.pi / 180 ∈ degI d := by
  have h := DIval.mem_mul DIval.mem_piI (DIval.mem_ratio d 180 (by norm_num))
  have e : (d : ℝ) * Real.pi / 180 = Real.pi * ((d : ℝ) / ((180 : Int) : ℝ)) := by push_cast; ring
  rw [e]; exact h

/-! ### Arcs -/

/-- `Forall₂` gives pointwise relations for `getD` with related defaults. -/
lemma forall₂_getD {α β : Type*} {R : α → β → Prop} {l : List α} {L : List β} (h : List.Forall₂ R l L) {d : α}
    {e : β} (hde : R d e) : ∀ j, R (l.getD j d) (L.getD j e) := by
  induction h with
  | nil => intro j; simpa using hde
  | cons hab _ ih =>
    intro j
    rcases j with _ | j
    · simpa using hab
    · simpa using ih j

/-- `arcVertsAux` encloses `stepVertices`. -/
lemma arcVertsAux_sound : ∀ (steps : List (Int × Int × Int)) (p : V2) (z : ℂ), V2.Mem p z →
    (∀ s ∈ steps, 0 < s.2.1 ∧ -360 ≤ s.2.2 ∧ s.2.2 ≤ 360) →
    List.Forall₂ V2.Mem (arcVertsAux p steps)
      (Worm.Geom.stepVertices z (steps.map fun s => ((s.1 : ℝ) / s.2.1, (s.2.2 : ℝ)))) := by
  intro steps
  induction steps with
  | nil => intro p z hpz _; exact List.Forall₂.cons hpz List.Forall₂.nil
  | cons st rest ih =>
    intro p z hpz hst
    obtain ⟨ln, ld, d⟩ := st
    obtain ⟨hld, hd1, hd2⟩ := hst (ln, ld, d) (by simp)
    simp only [arcVertsAux, List.map_cons, Worm.Geom.stepVertices]
    refine List.Forall₂.cons hpz (ih _ _ ?_ fun s hs => hst s (by simp [hs]))
    obtain ⟨hlo, hhi⟩ := degI_range hd1 hd2
    obtain ⟨hs, hc⟩ := DIval.mem_sincosIv (mem_degI d) hlo hhi
    have hl := DIval.mem_ratio ln ld hld
    refine V2.mem_add hpz ⟨?_, ?_⟩
    · have e : (((ln : ℝ) / (ld : ℝ) : ℝ) * exp ((((d : ℝ) * Real.pi / 180 : ℝ) : ℂ) * I) : ℂ).re =
          (ln : ℝ) / (ld : ℝ) * Real.cos ((d : ℝ) * Real.pi / 180) := by
        rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
      rw [e]; exact DIval.mem_mul hl hc
    · have e : (((ln : ℝ) / (ld : ℝ) : ℝ) * exp ((((d : ℝ) * Real.pi / 180 : ℝ) : ℂ) * I) : ℂ).im =
          (ln : ℝ) / (ld : ℝ) * Real.sin ((d : ℝ) * Real.pi / 180) := by
        rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
      rw [e]; exact DIval.mem_mul hl hs

/-- `arcVerts` encloses the exact vertices `arcPts`. -/
lemma arcVerts_sound (a : Arc) (ha : 0 < a.sx.2 ∧ 0 < a.sy.2 ∧ ∀ s ∈ a.steps, 0 < s.2.1 ∧ -360 ≤ s.2.2 ∧ s.2.2 ≤ 360) :
    List.Forall₂ V2.Mem (arcVerts a) (WormCore.Sound.arcPts a) := by
  unfold arcVerts WormCore.Sound.arcPts
  refine arcVertsAux_sound _ _ _ ⟨?_, ?_⟩ ha.2.2
  · exact DIval.mem_ratio _ _ ha.1
  · exact DIval.mem_ratio _ _ ha.2.1

/-- The sum by `foldl`. -/
lemma foldl_add_sound : ∀ {l : List V2} {L : List ℂ}, List.Forall₂ V2.Mem l L → ∀ (acc : V2) (w : ℂ), V2.Mem acc w →
    V2.Mem (l.foldl V2.add acc) (w + L.sum) := by
  intro l L h
  induction h with
  | nil => intro acc w hw; simpa using hw
  | cons hab _ ih =>
    intro acc w hw
    simp only [List.foldl_cons, List.sum_cons]
    have := ih _ _ (V2.mem_add hw hab)
    rwa [add_assoc] at this

/-- `meanV` encloses the mean. -/
lemma meanV_sound {l : List V2} {L : List ℂ} (h : List.Forall₂ V2.Mem l L) :
    V2.Mem (meanV l) (L.sum / L.length) := by
  rcases l with _ | ⟨a, t⟩
  · cases h
    simpa [meanV] using V2.mem_zero
  · have hlen : (a :: t).length = L.length := h.length_eq
    have hs := foldl_add_sound h V2.zero 0 V2.mem_zero
    rw [zero_add] at hs
    have hr := DIval.mem_ratio 1 ((a :: t).length : Int) (by simp)
    have e : L.sum / (L.length : ℂ) = (((1 : Int) : ℝ) / (((a :: t).length : Int) : ℝ) : ℝ) * L.sum := by
      rw [hlen]; push_cast; ring
    rw [e]
    exact V2.mem_smul hr hs

/-! ### The family -/

variable {arcs : List Arc} {gid : List (Nat × Nat)}

lemma mkFam_body_size : (mkFam arcs gid).body.size = gid.length := by simp [mkFam]

lemma mkFam_body (g : Nat) : (mkFam arcs gid).body[g]! = (gid.getD g (0, 0)).1 := by
  rcases Nat.lt_or_ge g gid.length with h | h
  · simp [mkFam, h]
  · simp [mkFam, h]

lemma mkFam_k : (mkFam arcs gid).k = arcs.length - 1 := rfl

/-- **The family.** -/
theorem famSpec_mkFam (harcs : WormCore.Sound.ArcsOK arcs) (hk : arcs.length = 5) (hgid : ∀ g ∈ gid, g.1 < 5) :
    FamSpec (mkFam arcs gid) (WormCore.Sound.qReal arcs gid) := by
  -- the enclosure of one body-frame point
  have hq : ∀ g < gid.length, V2.Mem (mkFam arcs gid).q[g]! (WormCore.Sound.qReal arcs gid g) := by
    intro g hg
    have hgd : gid.getD g (0, 0) = gid[g] := List.getD_eq_getElem _ _ hg
    set b := gid[g].1 with hb
    set j := gid[g].2 with hj
    have hb5 : b < arcs.length := by rw [hk]; exact hgid _ (List.getElem_mem hg)
    have hA := arcVerts_sound arcs[b] (harcs _ (List.getElem_mem hb5))
    have hV : (arcs.map arcVerts).getD b [] = arcVerts arcs[b] := by
      rw [List.getD_eq_getElem _ _ (by simpa using hb5)]; simp
    have hAr : arcs.getD b ⟨(0, 1), (0, 1), []⟩ = arcs[b] := List.getD_eq_getElem _ _ hb5
    have hv := forall₂_getD hA V2.mem_zero j
    simp only [mkFam, WormCore.Sound.qReal, hgd, ← hb, ← hj, hAr]
    rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hg]
    simp only [Option.map_some, Option.getD_some, hV, ← hb, ← hj]
    split_ifs with h0
    · exact hv
    · exact V2.mem_sub hv (meanV_sound hA)
  refine ⟨by simp [mkFam], by simp [mkFam], fun g hg => ?_, fun g hg => ?_, fun g hg => ?_, ?_⟩
  · rw [mkFam_body_size] at hg; exact hq g hg
  · rw [mkFam_body_size] at hg
    have hqn : (mkFam arcs gid).qn[g]! = V2.norm (mkFam arcs gid).q[g]! := by
      simp [mkFam, hg]
    rw [hqn]; exact V2.mem_norm (hq g hg)
  · rw [mkFam_body_size] at hg
    rw [mkFam_body, mkFam_k, hk, List.getD_eq_getElem _ _ hg]
    have := hgid _ (List.getElem_mem hg)
    omega
  · rw [mkFam_k, hk]

/-- `place` is `pos` for the checker's family. -/
theorem place_eq_pos (x : Fin 12 → ℝ) (g : Nat) :
    WormCore.Sound.place arcs gid x g = pos (mkFam arcs gid) (WormCore.Sound.qReal arcs gid) x g := by
  unfold WormCore.Sound.place pos
  rw [mkFam_body]
  by_cases h0 : (gid.getD g (0, 0)).1 = 0
  · simp only [h0, ite_true]
  · simp only [h0, ite_false, Worm.motion]
    set b := (gid.getD g (0, 0)).1
    have e : (⟨WormCore.Sound.coord x (3 * (b - 1) + 1), WormCore.Sound.coord x (3 * (b - 1) + 2)⟩ : ℂ) =
        bodyTrans x b := by
      apply Complex.ext <;> simp [bodyTrans, WormCore.Sound.coord]
    rw [e, add_comm]
    rfl

/-! ### The box -/

/-- The centre angle mantissa of body `b` lies in the range of `sincosIv`. -/
lemma toLo_toHi_range {L H : Int} (hle : L ≤ H) (hL : -(64 * 2 ^ BS : Int) ≤ L) (hH : H ≤ 64 * 2 ^ BS) :
    -(64 * dfxOne) ≤ toLo ((L + H).fdiv 2) ∧ toHi ((L + H).fdiv 2) ≤ 64 * dfxOne := by
  obtain ⟨h1, h2⟩ := fdiv2_mem hle
  simp only [toLo, toHi, BS, dfxS, dfxOne] at *
  simp (disch := norm_num) only [Int.fdiv_eq_ediv_of_nonneg] at h1 h2 ⊢
  norm_num at hL hH ⊢
  constructor <;> omega

/-- **Box facts.** `AngleRange` and a point of the box give `BoxOK`. -/
theorem boxOK_of {lo hi : Array Int} (hr : WormCore.Sound.AngleRange lo hi) {x : Fin 12 → ℝ} (hx : InBox lo hi x) :
    BoxOK lo hi := by
  have hle : ∀ j < 12, lo[j]! ≤ hi[j]! := by
    intro j hj
    obtain ⟨h1, h2⟩ := hx ⟨j, hj⟩
    have : (lo[j]! : ℝ) / 2 ^ BS ≤ (hi[j]! : ℝ) / 2 ^ BS := h1.trans h2
    have h3 : (lo[j]! : ℝ) ≤ (hi[j]! : ℝ) := by
      rwa [div_le_div_iff_of_pos_right two_pow_BS_pos] at this
    exact_mod_cast h3
  refine ⟨hle, fun b hb1 hb4 => ?_⟩
  obtain ⟨hL, hH⟩ := hr (b - 1) (by omega)
  exact toLo_toHi_range (hle _ (by omega)) hL hH

end IvSound

end WormCore
