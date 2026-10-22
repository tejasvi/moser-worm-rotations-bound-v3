import WormSound.BoundSound
import WormSound.Valid

/-!
# Soundness of the leaf test

`leafOK_sound`: on a box that passes `leafOK`, every convex set that contains the placed vertices of the family at a
placement of the box has area above `τ` (`tauHi · 2⁻⁵⁶`). The structures are valid there (`stOK_valid`), so each
shoelace area is at most the area (`small_le`, `fan_le`, `chord_le`), and the weights add up to at most `1`, so the
area is at least the weighted sum, which `leafBound` bounds from below (`leafBound_sound`).
-/

noncomputable section

namespace WormCore.Sound

open WormCore.IvSound Complex Finset Worm.Geom MeasureTheory
open MoserWorm hiding cross shoelace

lemma stOK_verts_lt {C : Ctx} {maxsmall : ℕ} {st : St} (h : stOK C maxsmall st = true) :
    ∀ g ∈ st.verts, g < C.F.body.size := by
  cases st with
  | small v =>
    simp only [stOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.2
  | fan v zx zy =>
    simp only [stOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.1.2
  | chord v t =>
    simp only [stOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.1.2

/-- A valid structure has shoelace area at most the area of a convex set containing its vertices. -/
lemma shoelace_le_of_valid (K : Set ℂ) (hK : Convex ℝ K) (P : List ℂ) (hP : ∀ z ∈ P, z ∈ K) (st : St)
    (hv : StValid P st) : ENNReal.ofReal (shoelace P) ≤ volume K := by
  cases st with
  | small v => exact small_le K hK P hP hv
  | fan v zx zy => exact fan_le K hK P hP (fanZ zx zy) hv.1 hv.2.1 hv.2.2
  | chord v t => exact chord_le K hK P hP (ctOf t) hv

lemma foldl_add_eq_sum (l : List Int) : l.foldl (· + ·) 0 = l.sum := by
  suffices H : ∀ a : Int, l.foldl (· + ·) a = a + l.sum by simpa using H 0
  induction l with
  | nil => intro a; simp
  | cons b t ih => intro a; simp only [List.foldl_cons, List.sum_cons, ih]; ring

lemma sum_map_div_cast {ι : Type*} (L : List ι) (f : ι → Int) (c : ℝ) :
    (L.map fun i => (f i : ℝ) / c).sum = ((L.map f).sum : ℝ) / c := by
  induction L with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring

lemma list_sum_mul_const {ι : Type*} (L : List ι) (lam : ι → ℝ) (V : ℝ) :
    (L.map fun i => lam i * V).sum = (L.map lam).sum * V := by
  induction L with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma weighted_sum_le {ι : Type*} (L : List ι) (lam s : ι → ℝ) (V : ℝ) (hV : 0 ≤ V) (hlam : ∀ i ∈ L, 0 ≤ lam i)
    (hs : ∀ i ∈ L, s i ≤ V) (h1 : (L.map lam).sum ≤ 1) : (L.map fun i => lam i * s i).sum ≤ V := by
  have h : (L.map fun i => lam i * s i).sum ≤ (L.map fun i => lam i * V).sum :=
    List.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hs i hi) (hlam i hi)
  rw [list_sum_mul_const] at h
  calc (L.map fun i => lam i * s i).sum ≤ (L.map lam).sum * V := h
    _ ≤ 1 * V := mul_le_mul_of_nonneg_right h1 hV
    _ = V := one_mul V

/-- **Leaf.** On a box that passes `leafOK`, a convex set containing the placed vertices at a placement of the box
has area above `tauHi · 2⁻⁵⁶`. -/
theorem leafOK_sound (arcs : List Arc) (gid : List (ℕ × ℕ)) (harcs : ArcsOK arcs) (hk5 : arcs.length = 5)
    (hgid : ∀ g ∈ gid, g.1 < 5) (maxsmall : ℕ) (hms : maxsmall ≤ 4) (tauHi : Int)
    (htau : 0 ≤ tauHi) (lo hi : Array Int) (hrange : AngleRange lo hi) (r : Rec)
    (h : leafOK (mkFam arcs gid) maxsmall tauHi lo hi r = true) (x : Fin 12 → ℝ) (hx : InBox lo hi x)
    (K : Set ℂ) (hK : Convex ℝ K) (hP : ∀ g < gid.length, place arcs gid x g ∈ K) :
    ENNReal.ofReal ((tauHi : ℝ) / 2 ^ dfxS) < volume K := by
  unfold leafOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨_, hsts⟩, hsum⟩, hlb⟩ := h
  have hF := famSpec_mkFam harcs hk5 hgid
  have hB := boxOK_of hrange hx
  have hk : (mkFam arcs gid).k = 4 := by rw [mkFam_k, hk5]
  have hsize : (mkFam arcs gid).body.size = gid.length := mkFam_body_size
  have hst : ∀ p ∈ r.sts, 0 ≤ p.2 ∧ stOK (mkCtx (mkFam arcs gid) lo hi) maxsmall p.1 = true := by
    intro p hp
    have := hsts p hp
    obtain ⟨st, lam⟩ := p
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
  have hverts : ∀ p ∈ r.sts, ∀ g ∈ p.1.verts, g < (mkFam arcs gid).body.size :=
    fun p hp => stOK_verts_lt (hst p hp).2
  have harea : ∀ p ∈ r.sts, ENNReal.ofReal (shoelace (p.1.verts.map (place arcs gid x))) ≤ volume K := by
    intro p hp
    have hv := stOK_valid arcs gid harcs hk5 hgid maxsmall hms lo hi hrange p.1 (hst p hp).2 x hx
    refine shoelace_le_of_valid K hK _ ?_ p.1 hv
    intro z hz
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hz
    exact hP g (hsize ▸ hverts p hp g hg)
  by_cases hVtop : volume K = ⊤
  · rw [hVtop]; exact ENNReal.ofReal_lt_top
  set V := (volume K).toReal with hVdef
  have hVeq : volume K = ENNReal.ofReal V := (ENNReal.ofReal_toReal hVtop).symm
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hareaV : ∀ p ∈ r.sts, shoelace (p.1.verts.map (pos (mkFam arcs gid) (qReal arcs gid) x)) ≤ V := by
    intro p hp
    have := harea p hp
    rw [hVeq] at this
    have e : p.1.verts.map (place arcs gid x) = p.1.verts.map (pos (mkFam arcs gid) (qReal arcs gid) x) :=
      List.map_congr_left fun g _ => place_eq_pos x g
    rw [← e]
    exact (ENNReal.ofReal_le_ofReal_iff hV0).1 this
  have hlam1 : (r.sts.map fun p => (p.2 : ℝ) / 2 ^ dfxS).sum ≤ 1 := by
    rw [foldl_add_eq_sum] at hsum
    rw [sum_map_div_cast r.sts (fun p => p.2) (2 ^ dfxS)]
    have hc : (((r.sts.map fun p => p.2).sum : ℤ) : ℝ) ≤ ((dfxOne : ℤ) : ℝ) := Int.cast_le.mpr hsum
    have hD : ((dfxOne : ℤ) : ℝ) = 2 ^ dfxS := by norm_num [dfxOne, dfxS]
    rw [div_le_one (by positivity)]
    linarith
  have hws := weighted_sum_le r.sts (fun p => (p.2 : ℝ) / 2 ^ dfxS)
    (fun p => shoelace (p.1.verts.map (pos (mkFam arcs gid) (qReal arcs gid) x))) V hV0
    (fun p hp => by have := (hst p hp).1; positivity) hareaV hlam1
  have htau' : -(1000 * dfxOne) ≤ tauHi := by norm_num [dfxOne]; omega
  have hLB := leafBound_sound hF hk hB r.sts hverts (fun p hp => (hst p hp).1) x hx tauHi htau' hlb
  have htl : (tauHi : ℝ) / 2 ^ dfxS < (leafBound (mkCtx (mkFam arcs gid) lo hi) r.sts : ℝ) / 2 ^ dfxS := by
    have : (tauHi : ℝ) < (leafBound (mkCtx (mkFam arcs gid) lo hi) r.sts : ℝ) := by exact_mod_cast hlb
    exact div_lt_div_of_pos_right this (by positivity)
  have ht0 : (0 : ℝ) ≤ (tauHi : ℝ) / 2 ^ dfxS := by
    have : (0 : ℝ) ≤ (tauHi : ℝ) := by exact_mod_cast htau
    positivity
  rw [hVeq]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht0).2 (by linarith)

end WormCore.Sound
