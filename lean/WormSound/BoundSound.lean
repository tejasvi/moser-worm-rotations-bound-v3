import WormSound.Model

/-!
# Soundness of the area bound of the worm checker (`WormCore.leafBound`)

The interval data of `WormCore.model`, `boundParts`, `comboVal` enclose the real coefficients of the area model
(`WormSound.Model`) and the real bounds of `quadF_ge`/`combo_ge` (`WormSound.Quad`); so `leafBound` is a lower bound
of the combination of the areas on the whole box.
-/

noncomputable section

namespace WormCore.Sound

open WormCore.IvSound Complex Finset Worm.Geom
open MoserWorm hiding cross shoelace

/-! ## Interval sums and arrays -/

lemma mem_zero : (0 : ℝ) ∈ DIval.pt 0 := by simpa using DIval.mem_pt 0

lemma mem_isum_map {α : Type*} (l : List α) (f : α → ℝ) (I : α → DIval) (h : ∀ a ∈ l, f a ∈ I a) :
    (l.map f).sum ∈ isum (l.map I) := by
  unfold isum
  suffices H : ∀ (acc : DIval) (r : ℝ), r ∈ acc → r + (l.map f).sum ∈ (l.map I).foldl DIval.add acc by
    simpa using H (DIval.pt 0) 0 mem_zero
  induction l with
  | nil => intro acc r hr; simpa using hr
  | cons a t ih =>
    intro acc r hr
    simp only [List.map_cons, List.sum_cons, List.foldl_cons]
    have := ih (fun b hb => h b (List.mem_cons_of_mem a hb)) (acc.add (I a)) (r + f a)
      (DIval.mem_add hr (h a List.mem_cons_self))
    simpa [add_assoc] using this

lemma range_map_getElem! {α : Type*} [Inhabited α] (n : ℕ) (f : ℕ → α) {k : ℕ} (hk : k < n) :
    ((List.range n).toArray.map f)[k]! = f k := by
  simp [hk]

variable {F : Fam} {q : ℕ → ℂ} {lo hi : Array Int}

/-! ## The area model -/

lemma mem_rqR (hF : FamSpec F q) (hB : BoxOK lo hi) {g : ℕ} (hg : g < F.body.size) :
    V2.Mem (mkCtx F lo hi).RQ[g]! (rqR F q lo hi g) := by
  unfold rqR
  split_ifs with h0
  · rw [ctx_RQ hg, if_pos h0]; exact hF.q_mem g hg
  · exact mem_RQ hF hB hg h0

lemma mem_lcol (hF : FamSpec F q) (hB : BoxOK lo hi) {g : ℕ} (hg : g < F.body.size) (k : ℕ) :
    V2.Mem (lcol (mkCtx F lo hi) g k) (lcolR F q lo hi g k) := by
  rcases k with _ | _ | _ | k
  · show V2.Mem (DIval.ofInt 1, DIval.pt 0) (1 : ℂ)
    exact ⟨by simpa using DIval.mem_ofInt 1, by simpa using mem_zero⟩
  · show V2.Mem (DIval.pt 0, DIval.ofInt 1) Complex.I
    exact ⟨by simpa using mem_zero, by simpa using DIval.mem_ofInt 1⟩
  · exact mem_rqR hF hB hg
  · exact V2.mem_J (mem_rqR hF hB hg)

lemma mem_cross {u v : V2} {z w : ℂ} (hz : V2.Mem u z) (hw : V2.Mem v w) : cross z w ∈ V2.det u v :=
  V2.mem_det hz hw

lemma mem_gTerm (hF : FamSpec F q) (hB : BoxOK lo hi) {a b : ℕ} (ha : a < F.body.size) (hb : b < F.body.size)
    (k : ℕ) : gTermR F q lo hi a b k ∈ gTerm (mkCtx F lo hi) a b k := by
  unfold gTermR gTerm
  refine DIval.mem_add ?_ ?_
  · show _ ∈ (if F.body[b]! ≠ 0 ∧ k / 4 = F.body[b]! - 1 then _ else _)
    split_ifs
    · exact mem_cross (mem_X0 hF hB ha) (mem_lcol hF hB hb _)
    · exact mem_zero
  · show _ ∈ (if F.body[a]! ≠ 0 ∧ k / 4 = F.body[a]! - 1 then _ else _)
    split_ifs
    · exact mem_cross (mem_lcol hF hB ha _) (mem_X0 hF hB hb)
    · exact mem_zero

lemma mem_MTerm (hF : FamSpec F q) (hB : BoxOK lo hi) {a b : ℕ} (ha : a < F.body.size) (hb : b < F.body.size)
    (k l : ℕ) : MTermR F q lo hi a b k l ∈ MTerm (mkCtx F lo hi) a b k l := by
  unfold MTermR MTerm
  show _ ∈ (if F.body[a]! ≠ 0 ∧ F.body[b]! ≠ 0 ∧ k / 4 = F.body[a]! - 1 ∧ l / 4 = F.body[b]! - 1 then _ else _)
  split_ifs
  · exact mem_cross (mem_lcol hF hB ha _) (mem_lcol hF hB hb _)
  · exact mem_zero

lemma at'_mem {l : List ℕ} (hlen : 0 < l.length) (j : ℕ) : at' l j ∈ l := by
  unfold at'
  rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hlen)]
  exact List.getElem_mem _

lemma cycPairs_mem {l : List ℕ} {p : ℕ × ℕ} (hp : p ∈ cycPairs l) : p.1 ∈ l ∧ p.2 ∈ l := by
  unfold cycPairs at hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  have hlen : 0 < l.length := by
    have := List.mem_range.mp hj; omega
  exact ⟨at'_mem hlen j, at'_mem hlen (j + 1)⟩

/-- **Model enclosure.** `WormCore.model` encloses the real coefficients `F0R`, `gR`, `MR`. -/
theorem mem_model (hF : FamSpec F q) (hB : BoxOK lo hi) (hk : F.k = 4) (l : List ℕ)
    (hl : ∀ g ∈ l, g < F.body.size) :
    F0R F q lo hi l ∈ (model (mkCtx F lo hi) l).1 ∧
      (∀ k < 16, gR F q lo hi l k ∈ (model (mkCtx F lo hi) l).2.1[k]!) ∧
      ∀ k < 16, ∀ k' < 16, MR F q lo hi l k k' ∈ (model (mkCtx F lo hi) l).2.2[k * 16 + k']! := by
  have hC : (mkCtx F lo hi).F.k = 4 := hk
  have hps : ∀ p ∈ cycPairs l, p.1 < F.body.size ∧ p.2 < F.body.size := fun p hp =>
    ⟨hl _ (cycPairs_mem hp).1, hl _ (cycPairs_mem hp).2⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold model F0R
    exact DIval.mem_half (mem_isum_map _ _ _ fun p hp =>
      mem_cross (mem_X0 hF hB (hps p hp).1) (mem_X0 hF hB (hps p hp).2))
  · intro k hk16
    unfold model
    simp only [hC]
    rw [range_map_getElem! _ _ (by omega)]
    exact DIval.mem_half (mem_isum_map _ _ _ fun p hp => mem_gTerm hF hB (hps p hp).1 (hps p hp).2 k)
  · intro k hk16 k' hk'
    unfold model
    simp only [hC]
    rw [range_map_getElem! _ _ (by nlinarith)]
    have e1 : (k * 16 + k') / (4 * 4) = k := by omega
    have e2 : (k * 16 + k') % (4 * 4) = k' := by omega
    rw [e1, e2]
    exact DIval.mem_half (mem_isum_map _ _ _ fun p hp => mem_MTerm hF hB (hps p hp).1 (hps p hp).2 k k')

/-! ## The bound of one structure (`boundParts`) -/

lemma sum_filter_ne {l : List ℕ} (hl : l.Nodup) (a : ℕ) (f : ℕ → ℝ) :
    ((l.filter (· ≠ a)).map f).sum = ∑ b ∈ l.toFinset.erase a, f b := by
  rw [← List.sum_toFinset f (hl.filter _)]
  congr 1
  ext b
  simp [List.mem_filter, and_comm]

lemma sum_flatMap_map (l m : List ℕ) (t : ℕ → ℕ → ℝ) :
    (l.flatMap fun a => m.map fun b => t a b).sum = (l.map fun a => (m.map fun b => t a b).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

lemma mem_isum_flatMap (l : List ℕ) (t : ℕ → ℕ → ℝ) (I : ℕ → ℕ → DIval) (h : ∀ a ∈ l, ∀ b ∈ l, t a b ∈ I a b) :
    (l.flatMap fun a => l.map fun b => t a b).sum ∈ isum (l.flatMap fun a => l.map fun b => I a b) := by
  have hm := mem_isum_map (l.flatMap fun a => l.map fun b => (a, b)) (fun p => t p.1 p.2) (fun p => I p.1 p.2)
    (by
      intro p hp
      obtain ⟨a, ha, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
      exact h a ha b hb)
  simpa [List.map_flatMap, List.map_map, Function.comp_def] using hm

lemma mem_pt_real (m : Int) : (m : ℝ) / 2 ^ dfxS ∈ DIval.pt m := DIval.mem_pt m

/-- The identity-term coefficients: `g̃ₐ = gₐ + 2β [a ≡ 2]`, `M̃ₐₐ = Mₐₐ + β [a ≡ 2, 3]` (mod 4), `β` real. -/
def gTilde (gr : ℕ → ℝ) (βr : ℝ) (a : ℕ) : ℝ := gr a + if a % 4 = 2 then 2 * βr else 0

def MTilde (Mr : ℕ → ℕ → ℝ) (βr : ℝ) (a b : ℕ) : ℝ := Mr a b + if a = b ∧ 2 ≤ a % 4 then βr else 0

lemma MTilde_sym_add (Mr : ℕ → ℕ → ℝ) (βr : ℝ) (a b : ℕ) :
    MTilde Mr βr a b + MTilde Mr βr b a =
      Mr a b + Mr b a + if a = b ∧ 2 ≤ a % 4 then 2 * βr else 0 := by
  unfold MTilde
  by_cases hab : a = b
  · subst hab; split_ifs <;> ring
  · rw [if_neg (fun h => hab h.1), if_neg (fun h => hab h.1.symm), if_neg (fun h => hab h.1)]; ring

/-- **One structure.** `boundParts` encloses `F̃(y₀) - pen̂/2` and `∇F̃(y₀)` for the identity-modified quadratic
over the active variables. -/
theorem mem_boundParts (nv : ℕ) (act : List ℕ) (hnd : act.Nodup) (F0 : DIval) (g M : Array DIval) (y0 w : Array Int)
    (β : Int) (F0r : ℝ) (gr : ℕ → ℝ) (Mr : ℕ → ℕ → ℝ) (hF0 : F0r ∈ F0) (hg : ∀ a ∈ act, gr a ∈ g[a]!)
    (hM : ∀ a ∈ act, ∀ b ∈ act, Mr a b ∈ M[a * nv + b]!) :
    quadF act.toFinset F0r (gTilde gr ((β : ℝ) / 2 ^ dfxS)) (MTilde Mr ((β : ℝ) / 2 ^ dfxS))
        (fun a => (y0[a]! : ℝ) / 2 ^ dfxS) -
      quadPen act.toFinset (MTilde Mr ((β : ℝ) / 2 ^ dfxS)) (fun a => (w[a]! : ℝ) / 2 ^ dfxS) / 2 ∈
        (boundParts nv act F0 g M y0 w β).1 ∧
      ∀ a ∈ act, quadGrad act.toFinset (gTilde gr ((β : ℝ) / 2 ^ dfxS)) (MTilde Mr ((β : ℝ) / 2 ^ dfxS))
        (fun a => (y0[a]! : ℝ) / 2 ^ dfxS) a ∈ (boundParts nv act F0 g M y0 w β).2 a := by
  set βr : ℝ := (β : ℝ) / 2 ^ dfxS with hβr
  set y0r : ℕ → ℝ := fun a => (y0[a]! : ℝ) / 2 ^ dfxS with hy0r
  set wr : ℕ → ℝ := fun a => (w[a]! : ℝ) / 2 ^ dfxS with hwr
  have h2β : 2 * βr ∈ DIval.pt (2 * β) := by
    have h := mem_pt_real (2 * β)
    have e : ((2 * β : Int) : ℝ) / 2 ^ dfxS = 2 * βr := by rw [hβr]; push_cast; ring
    rwa [e] at h
  set Hc : ℕ → ℕ → DIval := fun a b => if a = b ∧ a % 4 ≥ 2 then
    (M[a * nv + b]!.add M[b * nv + a]!).add (DIval.pt (2 * β)) else M[a * nv + b]!.add M[b * nv + a]! with hHc
  set g2c : ℕ → DIval := fun a => if a % 4 = 2 then g[a]!.add (DIval.pt (2 * β)) else g[a]! with hg2c
  have hbp : boundParts nv act F0 g M y0 w β =
      (((F0.add (isum (act.map fun a => (g2c a).mul (DIval.pt y0[a]!)))).add
        (isum (act.flatMap fun a => act.map fun b => (((Hc a b).mul (DIval.pt y0[a]!)).mul (DIval.pt y0[b]!)).half))).sub
        (isum (act.map fun a =>
          ((isum ((act.filter (· ≠ a)).map fun b => (((Hc a b).mul (DIval.pt w[a]!)).mul (DIval.pt w[b]!)).abs)).sub
            (((Hc a a).mul (DIval.pt w[a]!)).mul (DIval.pt w[a]!))).pos)).half,
       fun a => (g2c a).add (isum (act.map fun b => (Hc a b).mul (DIval.pt y0[b]!)))) := rfl
  rw [hbp]
  -- the interval Hessian and gradient entries enclose the real ones
  have hH : ∀ a ∈ act, ∀ b ∈ act, MTilde Mr βr a b + MTilde Mr βr b a ∈ Hc a b := by
    intro a ha b hb
    rw [MTilde_sym_add]
    have hab := DIval.mem_add (hM a ha b hb) (hM b hb a ha)
    by_cases hc : a = b ∧ 2 ≤ a % 4
    · simp only [hHc]; rw [if_pos hc, if_pos hc]; exact DIval.mem_add hab h2β
    · simp only [hHc]; rw [if_neg hc, if_neg hc, add_zero]; exact hab
  have hg2 : ∀ a ∈ act, gTilde gr βr a ∈ g2c a := by
    intro a ha
    unfold gTilde
    by_cases hc : a % 4 = 2
    · simp only [hg2c]; rw [if_pos hc, if_pos hc]; exact DIval.mem_add (hg a ha) h2β
    · simp only [hg2c]; rw [if_neg hc, if_neg hc, add_zero]; exact hg a ha
  have hy : ∀ a, y0r a ∈ DIval.pt y0[a]! := fun a => mem_pt_real _
  have hw : ∀ a, wr a ∈ DIval.pt w[a]! := fun a => mem_pt_real _
  refine ⟨?_, ?_⟩
  · refine DIval.mem_sub ?_ (DIval.mem_half ?_)
    · -- F̃(y₀)
      have hlin := mem_isum_map act (fun a => gTilde gr βr a * y0r a) (fun a => (g2c a).mul (DIval.pt y0[a]!))
        (fun a ha => DIval.mem_mul (hg2 a ha) (hy a))
      have hquad := mem_isum_flatMap act (fun a b => (MTilde Mr βr a b + MTilde Mr βr b a) * y0r a * y0r b / 2)
        (fun a b => (((Hc a b).mul (DIval.pt y0[a]!)).mul (DIval.pt y0[b]!)).half)
        (fun a ha b hb => DIval.mem_half (DIval.mem_mul (DIval.mem_mul (hH a ha b hb) (hy a)) (hy b)))
      have e1 : (act.map fun a => gTilde gr βr a * y0r a).sum = ∑ a ∈ act.toFinset, gTilde gr βr a * y0r a :=
        (List.sum_toFinset _ hnd).symm
      have e2 : (act.flatMap fun a => act.map fun b =>
          (MTilde Mr βr a b + MTilde Mr βr b a) * y0r a * y0r b / 2).sum =
          ∑ a ∈ act.toFinset, ∑ b ∈ act.toFinset, MTilde Mr βr a b * y0r a * y0r b := by
        rw [sum_flatMap_map, ← List.sum_toFinset _ hnd]
        have : ∀ a, (act.map fun b => (MTilde Mr βr a b + MTilde Mr βr b a) * y0r a * y0r b / 2).sum =
            ∑ b ∈ act.toFinset, (MTilde Mr βr a b + MTilde Mr βr b a) * y0r a * y0r b / 2 :=
          fun a => (List.sum_toFinset _ hnd).symm
        simp only [this]
        have hsplit : ∑ a ∈ act.toFinset, ∑ b ∈ act.toFinset,
            (MTilde Mr βr a b + MTilde Mr βr b a) * y0r a * y0r b / 2 =
            (∑ a ∈ act.toFinset, ∑ b ∈ act.toFinset, MTilde Mr βr a b * y0r a * y0r b +
              ∑ a ∈ act.toFinset, ∑ b ∈ act.toFinset, MTilde Mr βr b a * y0r a * y0r b) / 2 := by
          rw [← sum_add_distrib, sum_div]
          refine sum_congr rfl fun a _ => ?_
          rw [← sum_add_distrib, sum_div]
          exact sum_congr rfl fun b _ => by ring
        rw [hsplit, Finset.sum_comm (f := fun a b => MTilde Mr βr b a * y0r a * y0r b)]
        have : ∑ y ∈ act.toFinset, ∑ x ∈ act.toFinset, MTilde Mr βr y x * y0r x * y0r y =
            ∑ a ∈ act.toFinset, ∑ b ∈ act.toFinset, MTilde Mr βr a b * y0r a * y0r b :=
          sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
        rw [this]; ring
      have hF := DIval.mem_add (DIval.mem_add hF0 hlin) hquad
      rw [e1, e2] at hF
      exact hF
    · -- the penalty
      rw [quadPen, List.sum_toFinset _ hnd]
      refine mem_isum_map act _ _ (fun a ha => ?_)
      rw [max_comm]
      refine DIval.mem_pos (DIval.mem_sub ?_ (DIval.mem_mul (DIval.mem_mul (hH a ha a ha) (hw a)) (hw a)))
      rw [← sum_filter_ne hnd a]
      exact mem_isum_map _ _ _ fun b hb =>
        DIval.mem_abs (DIval.mem_mul (DIval.mem_mul (hH a ha b (List.mem_of_mem_filter hb)) (hw a)) (hw b))
  · -- the gradient
    intro a ha
    unfold quadGrad
    have hs := mem_isum_map act (fun b => (MTilde Mr βr a b + MTilde Mr βr b a) * y0r b)
      (fun b => (Hc a b).mul (DIval.pt y0[b]!)) (fun b hb => DIval.mem_mul (hH a ha b hb) (hy b))
    rw [show (act.map fun b => (MTilde Mr βr a b + MTilde Mr βr b a) * y0r b).sum =
        ∑ b ∈ act.toFinset, (MTilde Mr βr a b + MTilde Mr βr b a) * y0r b from (List.sum_toFinset _ hnd).symm] at hs
    exact DIval.mem_add (hg2 a ha) hs

/-! ## The combination (`comboVal`) -/

/-- **Combination.** `comboVal` encloses the right-hand side of `combo_ge` for the identity-modified quadratics. -/
theorem mem_comboVal (nv : ℕ) (act : List ℕ) (hnd : act.Nodup) {ι : Type*} (L : List ι)
    (md : ι → (DIval × Array DIval × Array DIval) × Int) (F0r : ι → ℝ) (gr : ι → ℕ → ℝ) (Mr : ι → ℕ → ℕ → ℝ)
    (hF0 : ∀ i ∈ L, F0r i ∈ (md i).1.1) (hg : ∀ i ∈ L, ∀ a ∈ act, gr i a ∈ (md i).1.2.1[a]!)
    (hM : ∀ i ∈ L, ∀ a ∈ act, ∀ b ∈ act, Mr i a b ∈ (md i).1.2.2[a * nv + b]!) (y0 w : Array Int) (β : Int) :
    (L.map fun i => ((md i).2 : ℝ) / 2 ^ dfxS *
        (quadF act.toFinset (F0r i) (gTilde (gr i) ((β : ℝ) / 2 ^ dfxS)) (MTilde (Mr i) ((β : ℝ) / 2 ^ dfxS))
            (fun a => (y0[a]! : ℝ) / 2 ^ dfxS) -
          quadPen act.toFinset (MTilde (Mr i) ((β : ℝ) / 2 ^ dfxS)) (fun a => (w[a]! : ℝ) / 2 ^ dfxS) / 2)).sum -
      ∑ a ∈ act.toFinset, |(L.map fun i => ((md i).2 : ℝ) / 2 ^ dfxS *
          quadGrad act.toFinset (gTilde (gr i) ((β : ℝ) / 2 ^ dfxS)) (MTilde (Mr i) ((β : ℝ) / 2 ^ dfxS))
            (fun a => (y0[a]! : ℝ) / 2 ^ dfxS) a).sum| * ((w[a]! : ℝ) / 2 ^ dfxS) ∈
      comboVal nv act (L.map md) y0 w β := by
  set βr : ℝ := (β : ℝ) / 2 ^ dfxS
  set y0r : ℕ → ℝ := fun a => (y0[a]! : ℝ) / 2 ^ dfxS
  set wr : ℕ → ℝ := fun a => (w[a]! : ℝ) / 2 ^ dfxS
  have hbp := fun i (hi : i ∈ L) => mem_boundParts nv act hnd (md i).1.1 (md i).1.2.1 (md i).1.2.2 y0 w β
    (F0r i) (gr i) (Mr i) (hF0 i hi) (hg i hi) (hM i hi)
  unfold comboVal
  simp only [List.map_map, Function.comp_def]
  refine DIval.mem_sub ?_ ?_
  · refine mem_isum_map L _ _ (fun i hi => ?_)
    rw [mul_comm]
    exact DIval.mem_mul (hbp i hi).1 (mem_pt_real _)
  · rw [List.sum_toFinset _ hnd]
    refine mem_isum_map act _ _ (fun a ha => ?_)
    refine DIval.mem_mul (DIval.mem_abs ?_) (mem_pt_real _)
    refine mem_isum_map L _ _ (fun i hi => ?_)
    rw [mul_comm]
    exact DIval.mem_mul ((hbp i hi).2 a ha) (mem_pt_real _)

/-! ## Identity terms and active variables -/

/-- The identity-modified quadratic is the quadratic plus `β` times the identity terms. -/
lemma quadF_tilde (S : Finset ℕ) (F0 : ℝ) (g : ℕ → ℝ) (M : ℕ → ℕ → ℝ) (βr : ℝ) (y : ℕ → ℝ) :
    quadF S F0 (gTilde g βr) (MTilde M βr) y = quadF S F0 g M y +
      βr * ∑ a ∈ S, ((if a % 4 = 2 then 2 * y a else 0) + (if 2 ≤ a % 4 then y a ^ 2 else 0)) := by
  unfold quadF gTilde MTilde
  have h1 : ∑ k ∈ S, (g k + (if k % 4 = 2 then 2 * βr else 0)) * y k =
      ∑ k ∈ S, g k * y k + βr * ∑ a ∈ S, (if a % 4 = 2 then 2 * y a else 0) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  have h2 : ∑ k ∈ S, ∑ l ∈ S, (M k l + (if k = l ∧ 2 ≤ k % 4 then βr else 0)) * y k * y l =
      ∑ k ∈ S, ∑ l ∈ S, M k l * y k * y l + βr * ∑ a ∈ S, (if 2 ≤ a % 4 then y a ^ 2 else 0) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    have e : ∑ l ∈ S, (if k = l ∧ 2 ≤ k % 4 then βr else 0) * y k * y l =
        βr * (if 2 ≤ k % 4 then y k ^ 2 else 0) := by
      by_cases hP : 2 ≤ k % 4
      · rw [Finset.sum_eq_single k]
        · rw [if_pos ⟨rfl, hP⟩, if_pos hP]; ring
        · intro l _ hlk
          rw [if_neg (fun h => hlk h.1.symm)]; ring
        · intro hk'; exact absurd hk hk'
      · rw [if_neg hP, mul_zero]
        exact sum_eq_zero fun l _ => by rw [if_neg (fun h => hP h.2)]; ring
    rw [← e, ← sum_add_distrib]
    exact sum_congr rfl fun l _ => by ring
  rw [h1, h2, sum_add_distrib, mul_add]
  ring

/-- The identity terms vanish when every body's angle variables lie on the circle `C² + S² + 2C = 0`. -/
lemma identity_terms_zero (S : Finset ℕ) (hS : ∀ a, a % 4 = 2 → (a ∈ S ↔ a + 1 ∈ S)) (y : ℕ → ℝ)
    (hc : ∀ a ∈ S, a % 4 = 2 → y a ^ 2 + y (a + 1) ^ 2 + 2 * y a = 0) :
    ∑ a ∈ S, ((if a % 4 = 2 then 2 * y a else 0) + (if 2 ≤ a % 4 then y a ^ 2 else 0)) = 0 := by
  have hsplit : ∀ a, ((if a % 4 = 2 then 2 * y a else 0) + (if 2 ≤ a % 4 then y a ^ 2 else 0)) =
      (if a % 4 = 2 then 2 * y a + y a ^ 2 else 0) + (if a % 4 = 3 then y a ^ 2 else 0) := by
    intro a
    have h4 : a % 4 < 4 := Nat.mod_lt _ (by norm_num)
    split_ifs <;> first | ring1 | (exfalso; omega)
  rw [sum_congr rfl fun a _ => hsplit a, sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  have hbij : ∑ a ∈ S.filter (fun a => a % 4 = 3), y a ^ 2 =
      ∑ a ∈ S.filter (fun a => a % 4 = 2), y (a + 1) ^ 2 := by
    apply Finset.sum_nbij' (fun a => a - 1) (fun a => a + 1)
    · intro a ha
      simp only [Finset.mem_filter] at ha ⊢
      have ha1 : 1 ≤ a := by omega
      have hm : (a - 1) % 4 = 2 := by omega
      exact ⟨(hS (a - 1) hm).2 (by rw [Nat.sub_add_cancel ha1]; exact ha.1), hm⟩
    · intro a ha
      simp only [Finset.mem_filter] at ha ⊢
      exact ⟨(hS a ha.2).1 ha.1, by omega⟩
    · intro a ha
      simp only [Finset.mem_filter] at ha
      omega
    · intro a _
      simp
    · intro a ha
      simp only [Finset.mem_filter] at ha
      have ha1 : 1 ≤ a := by omega
      rw [Nat.sub_add_cancel ha1]
  rw [hbij, ← sum_add_distrib]
  refine sum_eq_zero fun a ha => ?_
  simp only [Finset.mem_filter] at ha
  linarith [hc a ha.1 ha.2]

/-- Restriction of the quadratic to the index set outside which its coefficients vanish. -/
lemma quadF_restrict (S T : Finset ℕ) (hST : S ⊆ T) (F0 : ℝ) (g : ℕ → ℝ) (M : ℕ → ℕ → ℝ) (y : ℕ → ℝ)
    (hg : ∀ k ∈ T, k ∉ S → g k = 0) (hM : ∀ k ∈ T, ∀ l ∈ T, (k ∉ S ∨ l ∉ S) → M k l = 0) :
    quadF T F0 g M y = quadF S F0 g M y := by
  unfold quadF
  have e1 : ∑ k ∈ T, g k * y k = ∑ k ∈ S, g k * y k := by
    symm
    exact Finset.sum_subset hST fun k hkT hkS => by rw [hg k hkT hkS, zero_mul]
  have e2 : ∀ k ∈ T, ∑ l ∈ T, M k l * y k * y l = ∑ l ∈ S, M k l * y k * y l := by
    intro k hk
    symm
    exact Finset.sum_subset hST fun l hlT hlS => by rw [hM k hk l hlT (Or.inr hlS), zero_mul, zero_mul]
  have e3 : ∑ k ∈ T, ∑ l ∈ S, M k l * y k * y l = ∑ k ∈ S, ∑ l ∈ S, M k l * y k * y l := by
    symm
    refine Finset.sum_subset hST fun k hkT hkS => sum_eq_zero fun l hl => ?_
    rw [hM k hkT l (hST hl) (Or.inl hkS), zero_mul, zero_mul]
  rw [e1, sum_congr rfl e2, e3]

lemma bodyUsed_of_mem {C : Ctx} {sts : List (St × Int)} {p : St × Int} (hp : p ∈ sts) {g : ℕ} (hg : g ∈ p.1.verts) :
    bodyUsed C sts (C.F.body[g]!) = true := by
  unfold bodyUsed
  rw [List.any_eq_true]
  exact ⟨p, hp, List.any_eq_true.mpr ⟨g, hg, by simp⟩⟩

/-- The real coefficients of a structure vanish at the variables of unused bodies. -/
lemma gR_eq_zero {sts : List (St × Int)} {p : St × Int} (hp : p ∈ sts) {k : ℕ}
    (hk : bodyUsed (mkCtx F lo hi) sts (k / 4 + 1) = false) : gR F q lo hi p.1.verts k = 0 := by
  unfold gR
  rw [div_eq_zero_iff]
  left
  apply List.sum_eq_zero
  intro t ht
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
  obtain ⟨ha, hb⟩ := cycPairs_mem he
  have hua := bodyUsed_of_mem (C := mkCtx F lo hi) hp ha
  have hub := bodyUsed_of_mem (C := mkCtx F lo hi) hp hb
  have hF : (mkCtx F lo hi).F = F := rfl
  rw [hF] at hua hub
  unfold gTermR
  rw [if_neg, if_neg, add_zero]
  · rintro ⟨h0, hk'⟩
    have : F.body[e.1]! = k / 4 + 1 := by omega
    rw [this, hk] at hua; exact Bool.noConfusion hua
  · rintro ⟨h0, hk'⟩
    have : F.body[e.2]! = k / 4 + 1 := by omega
    rw [this, hk] at hub; exact Bool.noConfusion hub

lemma MR_eq_zero {sts : List (St × Int)} {p : St × Int} (hp : p ∈ sts) {k k' : ℕ}
    (hk : bodyUsed (mkCtx F lo hi) sts (k / 4 + 1) = false ∨ bodyUsed (mkCtx F lo hi) sts (k' / 4 + 1) = false) :
    MR F q lo hi p.1.verts k k' = 0 := by
  unfold MR
  rw [div_eq_zero_iff]
  left
  apply List.sum_eq_zero
  intro t ht
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
  obtain ⟨ha, hb⟩ := cycPairs_mem he
  have hua := bodyUsed_of_mem (C := mkCtx F lo hi) hp ha
  have hub := bodyUsed_of_mem (C := mkCtx F lo hi) hp hb
  have hF : (mkCtx F lo hi).F = F := rfl
  rw [hF] at hua hub
  unfold MTermR
  rw [if_neg]
  rintro ⟨h0a, h0b, hka, hkb⟩
  rcases hk with hk | hk
  · have : F.body[e.1]! = k / 4 + 1 := by omega
    rw [this, hk] at hua; exact Bool.noConfusion hua
  · have : F.body[e.2]! = k' / 4 + 1 := by omega
    rw [this, hk] at hub; exact Bool.noConfusion hub

/-- `foldl max` over a list returns the initial value or one of the values. -/
lemma foldl_max_mem {α : Type*} (l : List α) (f : α → Int) (init : Int) :
    l.foldl (fun best β => max best (f β)) init = init ∨
      ∃ β ∈ l, l.foldl (fun best β => max best (f β)) init = f β := by
  induction l generalizing init with
  | nil => left; rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    rcases ih (max init (f a)) with h | ⟨β, hβ, h⟩
    · rw [h]
      rcases le_total init (f a) with hle | hle
      · right; exact ⟨a, List.mem_cons_self, max_eq_right hle⟩
      · left; exact max_eq_left hle
    · right; exact ⟨β, List.mem_cons_of_mem a hβ, h⟩

/-! ## The leaf bound -/

/-- **Leaf bound.** If `leafBound` exceeds `tauHi` (above the initial value of its maximum), it is a lower bound
(scale `2⁻⁵⁶`) of the weighted sum of the shoelace areas of the structures at every placement of the box. -/
theorem leafBound_sound (hF : FamSpec F q) (hk : F.k = 4) (hB : BoxOK lo hi) (sts : List (St × Int))
    (hv : ∀ p ∈ sts, ∀ g ∈ p.1.verts, g < F.body.size) (hlam : ∀ p ∈ sts, 0 ≤ p.2)
    (x : Fin 12 → ℝ) (hx : InBox lo hi x) (tauHi : Int) (htau : -(1000 * dfxOne) ≤ tauHi)
    (hlb : tauHi < leafBound (mkCtx F lo hi) sts) :
    (leafBound (mkCtx F lo hi) sts : ℝ) / 2 ^ dfxS ≤
      (sts.map fun p => (p.2 : ℝ) / 2 ^ dfxS * shoelace (p.1.verts.map (pos F q x))).sum := by
  set C := mkCtx F lo hi with hC
  have hCk : C.F.k = 4 := hk
  set act : List ℕ := (List.range 16).filter fun a => bodyUsed C sts (a / 4 + 1) with hact
  set y0 : Array Int := (List.range 16).toArray.map (y0At C) with hy0
  set w : Array Int := (List.range 16).toArray.map (wAt C) with hw
  set models := sts.map fun p => (model C p.1.verts, p.2) with hmodels
  have hLB : leafBound C sts =
      betas.foldl (fun best β => max best (comboVal 16 act models y0 w β).lo) (-(1000 * dfxOne)) := by
    unfold leafBound
    rw [hCk]
  rcases foldl_max_mem betas (fun β => (comboVal 16 act models y0 w β).lo) (-(1000 * dfxOne)) with h | ⟨β, _, h⟩
  · rw [hLB, h] at hlb; omega
  rw [hLB, h]
  have hnd : act.Nodup := (List.nodup_range).filter _
  have hact16 : ∀ a ∈ act, a < 16 := fun a ha => List.mem_range.mp (List.mem_of_mem_filter ha)
  have hmem := mem_comboVal 16 act hnd sts (fun p => (model C p.1.verts, p.2))
    (fun p => F0R F q lo hi p.1.verts) (fun p => gR F q lo hi p.1.verts) (fun p => MR F q lo hi p.1.verts)
    (fun p hp => (mem_model hF hB hk p.1.verts (hv p hp)).1)
    (fun p hp a ha => (mem_model hF hB hk p.1.verts (hv p hp)).2.1 a (hact16 a ha))
    (fun p hp a ha b hb => (mem_model hF hB hk p.1.verts (hv p hp)).2.2 a (hact16 a ha) b (hact16 b hb))
    y0 w β
  have hlo := lo_le hmem
  set βr : ℝ := (β : ℝ) / 2 ^ dfxS
  -- the variables of the placement lie in the variable box
  have hbox : ∀ a ∈ act.toFinset, |yOf lo hi x a - (y0[a]! : ℝ) / 2 ^ dfxS| ≤ (w[a]! : ℝ) / 2 ^ dfxS := by
    intro a ha
    have ha16 := hact16 a (List.mem_toFinset.mp ha)
    rw [range_map_getElem! 16 (y0At C) ha16, range_map_getElem! 16 (wAt C) ha16]
    exact yOf_mem_box F q lo hi hF hk hB x hx a ha16
  have hcombo := combo_ge sts (fun p => (p.2 : ℝ) / 2 ^ dfxS) (fun p hp => by
      have := hlam p hp; positivity) act.toFinset
    (fun p => F0R F q lo hi p.1.verts) (fun p => gTilde (gR F q lo hi p.1.verts) βr)
    (fun p => MTilde (MR F q lo hi p.1.verts) βr) (yOf lo hi x) (fun a => (y0[a]! : ℝ) / 2 ^ dfxS)
    (fun a => (w[a]! : ℝ) / 2 ^ dfxS) hbox
  -- the modified quadratic at the placement is the shoelace area
  have hS : ∀ a, a % 4 = 2 → (a ∈ act.toFinset ↔ a + 1 ∈ act.toFinset) := by
    intro a ha
    simp only [List.mem_toFinset, hact, List.mem_filter, List.mem_range]
    have e : (a + 1) / 4 = a / 4 := by omega
    rw [e]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  have hcirc : ∀ a ∈ act.toFinset, a % 4 = 2 →
      yOf lo hi x a ^ 2 + yOf lo hi x (a + 1) ^ 2 + 2 * yOf lo hi x a = 0 := by
    intro a _ ha
    obtain ⟨b, rfl⟩ : ∃ b, a = 4 * b + 2 := ⟨a / 4, by omega⟩
    have e : 4 * b + 2 + 1 = 4 * b + 3 := by omega
    rw [e]
    exact yOf_circle lo hi x b
  have hpt : ∀ p ∈ sts, quadF act.toFinset (F0R F q lo hi p.1.verts) (gTilde (gR F q lo hi p.1.verts) βr)
      (MTilde (MR F q lo hi p.1.verts) βr) (yOf lo hi x) = shoelace (p.1.verts.map (pos F q x)) := by
    intro p hp
    rw [quadF_tilde, identity_terms_zero _ hS _ hcirc, mul_zero, add_zero,
      shoelace_eq_quadF F q lo hi hF hk p.1.verts (hv p hp) x]
    symm
    refine quadF_restrict act.toFinset (range 16) ?_ _ _ _ _ ?_ ?_
    · intro a ha; exact Finset.mem_range.mpr (hact16 a (List.mem_toFinset.mp ha))
    · intro k hk16 hka
      apply gR_eq_zero hp
      by_contra hu
      apply hka
      simp only [List.mem_toFinset, hact, List.mem_filter, List.mem_range]
      exact ⟨Finset.mem_range.mp hk16, by simpa using hu⟩
    · intro k hk16 l hl16 hkl
      apply MR_eq_zero hp
      by_contra hu
      push_neg at hu
      rcases hkl with hka | hla
      · apply hka
        simp only [List.mem_toFinset, hact, List.mem_filter, List.mem_range]
        exact ⟨Finset.mem_range.mp hk16, by simpa using hu.1⟩
      · apply hla
        simp only [List.mem_toFinset, hact, List.mem_filter, List.mem_range]
        exact ⟨Finset.mem_range.mp hl16, by simpa using hu.2⟩
  have hsum : (sts.map fun p => (p.2 : ℝ) / 2 ^ dfxS * quadF act.toFinset (F0R F q lo hi p.1.verts)
      (gTilde (gR F q lo hi p.1.verts) βr) (MTilde (MR F q lo hi p.1.verts) βr) (yOf lo hi x)).sum =
      (sts.map fun p => (p.2 : ℝ) / 2 ^ dfxS * shoelace (p.1.verts.map (pos F q x))).sum := by
    congr 1
    exact List.map_congr_left fun p hp => by rw [hpt p hp]
  rw [← hsum]
  exact hlo.trans hcombo

end WormCore.Sound
