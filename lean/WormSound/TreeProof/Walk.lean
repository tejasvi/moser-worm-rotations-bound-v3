import WormSound.TreeProof.Boxes

/-!
# The walks of the checker: skeleton (`skelWalk`), unit (`unitWalk`, `leafOKR`), chunk (`unitsCheck`)
-/

namespace WormCore.Sound

open MoserWorm

lemma codeDim_lt {c : Char} {k : ℕ} (h : codeDim c = some k) : k < 12 := by
  unfold codeDim at h
  split_ifs at h with h1 h2 h3
  · simp only [Option.some.injEq] at h
    have h4 : c.toNat ≤ 57 := h1.2
    have h5 : ('0' : Char).toNat = 48 := rfl
    rw [h5] at h
    omega
  · simp at h; omega
  · simp at h; omega

/-! ## The skeleton -/

/-- A predicate on boxes preserved by `halves` holds for every box that `skelWalk` outputs. -/
theorem skelWalk_inv (P : Array Int × Array Int → Prop)
    (hP : ∀ lo hi k l u, P (lo, hi) → halves lo hi k = some (l, u) → P l ∧ P u) :
    ∀ (fuel : ℕ) (cs : List Char) (st : List (Array Int × Array Int)) (acc acc' : Array (Array Int × Array Int))
      (rest : List Char), skelWalk fuel cs st acc = some (acc', rest) →
      (∀ B ∈ st, P B) → (∀ B ∈ acc.toList, P B) → ∀ B ∈ acc'.toList, P B
  | 0, _, _, _, _, _, h => by simp [skelWalk] at h
  | fuel + 1, cs, [], acc, acc', rest, h => by
    simp only [skelWalk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fun _ hacc => hacc
  | fuel + 1, [], _ :: _, _, _, _, h => by simp [skelWalk] at h
  | fuel + 1, c :: cs, (lo, hi) :: st, acc, acc', rest, h => by
    intro hst hacc
    simp only [skelWalk] at h
    split_ifs at h with hc
    · refine skelWalk_inv P hP fuel cs st (acc.push (lo, hi)) acc' rest h (fun B hB => hst B (by simp [hB])) ?_
      intro B hB
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hB
      rcases hB with hB | rfl
      · exact hacc B hB
      · exact hst _ (by simp)
    · rcases hcd : codeDim c with _ | k
      · simp [hcd] at h
      · rcases hh : halves lo hi k with _ | ⟨l, u⟩
        · simp [hcd, hh] at h
        · simp only [hcd, hh] at h
          obtain ⟨hl, hu⟩ := hP lo hi k l u (hst (lo, hi) (by simp)) hh
          refine skelWalk_inv P hP fuel cs (l :: u :: st) acc acc' rest h ?_ hacc
          intro B hB
          simp only [List.mem_cons] at hB
          rcases hB with rfl | rfl | hB
          · exact hl
          · exact hu
          · exact hst B (by simp [hB])

/-- **Skeleton coverage**: a point of a start box (or of an output box so far) lies in an output box. -/
theorem skelWalk_cover :
    ∀ (fuel : ℕ) (cs : List Char) (st : List (Array Int × Array Int)) (acc acc' : Array (Array Int × Array Int))
      (rest : List Char), skelWalk fuel cs st acc = some (acc', rest) → ∀ x : Fin 12 → ℝ,
      ((∃ B ∈ st, InBox B.1 B.2 x) ∨ (∃ B ∈ acc.toList, InBox B.1 B.2 x)) → ∃ B ∈ acc'.toList, InBox B.1 B.2 x
  | 0, _, _, _, _, _, h => by simp [skelWalk] at h
  | fuel + 1, cs, [], acc, acc', rest, h => by
    simp only [skelWalk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro x hx
    rcases hx with ⟨B, hB, _⟩ | hx
    · simp at hB
    · exact hx
  | fuel + 1, [], _ :: _, _, _, _, h => by simp [skelWalk] at h
  | fuel + 1, c :: cs, (lo, hi) :: st, acc, acc', rest, h => by
    intro x hx
    simp only [skelWalk] at h
    split_ifs at h with hc
    · refine skelWalk_cover fuel cs st (acc.push (lo, hi)) acc' rest h x ?_
      rcases hx with ⟨B, hB, hxB⟩ | ⟨B, hB, hxB⟩
      · simp only [List.mem_cons] at hB
        rcases hB with rfl | hB
        · exact Or.inr ⟨(lo, hi), by simp, hxB⟩
        · exact Or.inl ⟨B, hB, hxB⟩
      · exact Or.inr ⟨B, by simp [hB], hxB⟩
    · rcases hcd : codeDim c with _ | k
      · simp [hcd] at h
      · rcases hh : halves lo hi k with _ | ⟨l, u⟩
        · simp [hcd, hh] at h
        · simp only [hcd, hh] at h
          refine skelWalk_cover fuel cs (l :: u :: st) acc acc' rest h x ?_
          rcases hx with ⟨B, hB, hxB⟩ | hx
          · simp only [List.mem_cons] at hB
            rcases hB with rfl | hB
            · rcases halves_cover hh hxB with h1 | h1
              · exact Or.inl ⟨l, by simp, h1⟩
              · exact Or.inl ⟨u, by simp, h1⟩
            · exact Or.inl ⟨B, by simp [hB], hxB⟩
          · exact Or.inr hx

/-! ## Leaves with refinement -/

/-- **Refinement**: a box passing `leafOKR` is covered by boxes inside it that pass `leafOK` (same record). -/
theorem leafOKR_cover (F : Fam) (maxsmall : Nat) (tauHi : Int) :
    ∀ (d : ℕ) (lo hi : Array Int) (r : Rec), leafOKR F maxsmall tauHi d lo hi r = true → lo.size = 12 →
      hi.size = 12 → ∀ x : Fin 12 → ℝ, InBox lo hi x →
        ∃ lo' hi' : Array Int, leafOK F maxsmall tauHi lo' hi' r = true ∧ InBox lo' hi' x ∧ BoxSub lo' hi' lo hi
  | 0, lo, hi, r, h, _, _, x, hx => ⟨lo, hi, h, hx, BoxSub.refl lo hi⟩
  | d + 1, lo, hi, r, h, hlo, hhi, x, hx => by
    simp only [leafOKR, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨⟨hev, h1⟩, h2⟩
    · exact ⟨lo, hi, h, hx, BoxSub.refl lo hi⟩
    · by_cases hi12 : widestAngle F.k lo hi < 12
      · have hh : halves lo hi (widestAngle F.k lo hi) =
            some ((lo, hi.set! (widestAngle F.k lo hi) ((lo[widestAngle F.k lo hi]! + hi[widestAngle F.k lo hi]!) / 2)),
              (lo.set! (widestAngle F.k lo hi) ((lo[widestAngle F.k lo hi]! + hi[widestAngle F.k lo hi]!) / 2), hi)) := by
          unfold halves
          rw [ite_eq_left_iff.2 (fun h => absurd ⟨hev, by omega, by omega⟩ h)]
        obtain ⟨hs1, hs2⟩ := halves_sub hh (hx.le hi12)
        rcases halves_cover hh hx with hx1 | hx1
        · obtain ⟨lo', hi', hok, hin, hsub⟩ := leafOKR_cover F maxsmall tauHi d _ _ r h1 hlo (by simp [hhi]) x hx1
          exact ⟨lo', hi', hok, hin, hsub.trans hs1⟩
        · obtain ⟨lo', hi', hok, hin, hsub⟩ := leafOKR_cover F maxsmall tauHi d _ _ r h2 (by simp [hlo]) hhi x hx1
          exact ⟨lo', hi', hok, hin, hsub.trans hs2⟩
      · rw [set!_of_size_le (by omega)] at h1
        exact leafOKR_cover F maxsmall tauHi d lo hi r h1 hlo hhi x hx

/-! ## Units -/

/-- **Unit walk coverage**: every point of a box on the stack lies in a box inside it that passes `leafOK` with one
of the records. -/
theorem unitWalk_cover (F : Fam) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat) :
    ∀ (fuel : ℕ) (cs : List Char) (st : List (Array Int × Array Int)) (recs recs' : List Rec),
      unitWalk F maxsmall tauHi rdepth fuel cs st recs = some recs' →
      (∀ B ∈ st, B.1.size = 12 ∧ B.2.size = 12) →
      ∀ B ∈ st, ∀ x : Fin 12 → ℝ, InBox B.1 B.2 x →
        ∃ lo hi : Array Int, ∃ r ∈ recs, leafOK F maxsmall tauHi lo hi r = true ∧ InBox lo hi x ∧
          BoxSub lo hi B.1 B.2
  | 0, _, _, _, _, h => by simp [unitWalk] at h
  | fuel + 1, [], [], _, _, _ => by intro _ B hB; simp at hB
  | fuel + 1, [], _ :: _, _, _, h => by simp [unitWalk] at h
  | fuel + 1, _ :: _, [], _, _, h => by simp [unitWalk] at h
  | fuel + 1, c :: cs, (lo, hi) :: st, recs, recs', h => by
    intro hsz B hB x hx
    have hsz0 := hsz (lo, hi) (by simp)
    have hszst : ∀ B ∈ st, B.1.size = 12 ∧ B.2.size = 12 := fun B hB => hsz B (by simp [hB])
    simp only [unitWalk] at h
    split_ifs at h with hc
    · rcases recs with _ | ⟨r, rs⟩
      · simp at h
      · simp only at h
        split_ifs at h with hok
        simp only [List.mem_cons] at hB
        rcases hB with rfl | hB
        · obtain ⟨lo', hi', hok', hin, hsub⟩ := leafOKR_cover F maxsmall tauHi rdepth lo hi r hok hsz0.1 hsz0.2 x hx
          exact ⟨lo', hi', r, by simp, hok', hin, hsub⟩
        · obtain ⟨lo', hi', r', hr', hok', hin, hsub⟩ :=
            unitWalk_cover F maxsmall tauHi rdepth fuel cs st rs recs' h hszst B hB x hx
          exact ⟨lo', hi', r', by simp [hr'], hok', hin, hsub⟩
    · rcases hcd : codeDim c with _ | k
      · simp [hcd] at h
      · rcases hh : halves lo hi k with _ | ⟨l, u⟩
        · simp [hcd, hh] at h
        · simp only [hcd, hh] at h
          have hk12 := codeDim_lt hcd
          obtain ⟨s1, s2, s3, s4⟩ := halves_size hh
          have hsz' : ∀ B ∈ l :: u :: st, B.1.size = 12 ∧ B.2.size = 12 := by
            intro B hB
            simp only [List.mem_cons] at hB
            rcases hB with rfl | rfl | hB
            · exact ⟨s1.trans hsz0.1, s2.trans hsz0.2⟩
            · exact ⟨s3.trans hsz0.1, s4.trans hsz0.2⟩
            · exact hszst B hB
          simp only [List.mem_cons] at hB
          rcases hB with rfl | hB
          · obtain ⟨hs1, hs2⟩ := halves_sub hh (hx.le hk12)
            rcases halves_cover hh hx with hx1 | hx1
            · obtain ⟨lo', hi', r, hr, hok, hin, hsub⟩ :=
                unitWalk_cover F maxsmall tauHi rdepth fuel cs (l :: u :: st) recs recs' h hsz' l (by simp) x hx1
              exact ⟨lo', hi', r, hr, hok, hin, hsub.trans hs1⟩
            · obtain ⟨lo', hi', r, hr, hok, hin, hsub⟩ :=
                unitWalk_cover F maxsmall tauHi rdepth fuel cs (l :: u :: st) recs recs' h hsz' u (by simp) x hx1
              exact ⟨lo', hi', r, hr, hok, hin, hsub.trans hs2⟩
          · exact unitWalk_cover F maxsmall tauHi rdepth fuel cs (l :: u :: st) recs recs' h hsz' B (by simp [hB]) x hx

end WormCore.Sound
