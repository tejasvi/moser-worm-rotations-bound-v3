import WormSound.TreeProof.Walk

/-!
# The chunk walk: every unit listed by a successful chunk check passed `unitOK` against its box
-/

namespace WormCore.Sound

open MoserWorm

/-- Every unit listed by `unitsCheck` has a box from its part's skeleton and passed `unitOK`. -/
theorem unitsCheck_spec (F : Fam) (R : Root) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat) (skel : Nat → String)
    (table : Array St) :
    ∀ (fuel : ℕ) (toks : List String) (L : List (Nat × Nat)),
      unitsCheck F R maxsmall tauHi rdepth skel table fuel toks = some L →
      ∀ pu ∈ L, ∃ boxes, unitBoxes R pu.1 (skel pu.1) = some boxes ∧ pu.2 < boxes.size ∧
        ∃ cs recs, unitOK F maxsmall tauHi rdepth boxes[pu.2]! cs recs = true
  | 0, _, _, h => by simp [unitsCheck] at h
  | fuel + 1, [], L, h => by
    simp only [unitsCheck, Option.some.injEq] at h
    subst h
    intro pu hpu
    simp at hpu
  | fuel + 1, t :: rest, L, h => by
    simp only [unitsCheck] at h
    rcases hp : parseUnitHead t with _ | ⟨p, u⟩
    · simp [hp] at h
    · rcases rest with _ | ⟨c, rest'⟩
      · simp [hp] at h
      · rcases hc : parseCodes c with _ | cs
        · simp [hp, hc] at h
        · rcases hb : unitBoxes R p (skel p) with _ | boxes
          · simp [hp, hc, hb] at h
          · simp only [hp, hc, hb] at h
            split_ifs at h with hcond
            obtain ⟨hu, -, -, hok⟩ := hcond
            rcases hL : unitsCheck F R maxsmall tauHi rdepth skel table fuel (rest'.drop (countLeaves cs)) with _ | L'
            · simp [hL] at h
            · simp only [hL, Option.map_some, Option.some.injEq] at h
              subst h
              intro pu hpu
              rcases List.mem_cons.1 hpu with rfl | hpu
              · exact ⟨boxes, hb, hu, cs, _, hok⟩
              · exact unitsCheck_spec F R maxsmall tauHi rdepth skel table fuel _ L' hL pu hpu

/-- Every unit listed by a successful `chunkCheck` has a box from its part's skeleton and passed `unitOK`. -/
theorem chunkCheck_spec (F : Fam) (R : Root) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat) (skel : Nat → String)
    (txt : String) (L : List (Nat × Nat)) (h : chunkCheck F R maxsmall tauHi rdepth skel txt = some L) :
    ∀ pu ∈ L, ∃ boxes, unitBoxes R pu.1 (skel pu.1) = some boxes ∧ pu.2 < boxes.size ∧
      ∃ cs recs, unitOK F maxsmall tauHi rdepth boxes[pu.2]! cs recs = true := by
  unfold chunkCheck at h
  split at h
  · split at h
    · split at h
      · dsimp only at h
        split_ifs at h with hcond
        exact unitsCheck_spec F R maxsmall tauHi rdepth skel _ _ _ L h
      · simp at h
    · simp at h
  · simp at h

end WormCore.Sound
