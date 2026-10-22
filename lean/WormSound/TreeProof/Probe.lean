import WormSound.TreeProof.Units

/-!
# Probe: `unitBoxes_cover` needs `rootExact`

Without `rootExact R = true`, part (i) of `unitBoxes_cover` (every unit box lies in a cell of its part) fails. Take a
root box reversed in coordinate `0` (`lo = 10`, `hi = 0`, one cell, one part): the skeleton `0UU` gives the halves
`[10, 5]` and `[5, 0]` of the cell `[10, 0]`, and neither lies in it.
-/

namespace WormCore.Sound

open MoserWorm

/-- The reversed root box of the probe (one cell, one part). -/
def probeRoot : Root :=
  ⟨#[10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 1⟩

lemma probeRoot_shape : RootShape probeRoot := by
  refine ⟨rfl, rfl, rfl, Nat.one_pos, ?_⟩
  decide +kernel

lemma probeRoot_not_exact : rootExact probeRoot = false := by
  decide +kernel

lemma probe_unitBoxes : unitBoxes probeRoot 0 (String.ofList ['0', 'U', 'U']) =
    some #[(probeRoot.lo, probeRoot.hi.set! 0 5), (probeRoot.lo.set! 0 5, probeRoot.hi)] := by
  rw [unitBoxes, String.length_ofList, String.toList_ofList]
  decide +kernel

/-- **Probe.** Part (i) of `unitBoxes_cover` without the hypothesis `rootExact R = true` is false. -/
theorem unitBoxes_sub_needs_rootExact :
    ¬ ∀ (R : Root), RootShape R → ∀ (p : Nat) (skel : String) (boxes : Array (Array Int × Array Int)),
      unitBoxes R p skel = some boxes → ∀ u < boxes.size, ∃ k < ncells R / R.nparts,
        BoxSub boxes[u]!.1 boxes[u]!.2 (cellBox R (p + R.nparts * k)).1 (cellBox R (p + R.nparts * k)).2 := by
  intro H
  obtain ⟨k, hk, hsub⟩ := H probeRoot probeRoot_shape 0 _ _ probe_unitBoxes 0 (by decide)
  have hn : ncells probeRoot / probeRoot.nparts = 1 := by decide +kernel
  rw [hn] at hk
  have hk0 : k = 0 := by omega
  subst hk0
  have h0 := (hsub 0 (by norm_num)).2
  revert h0
  decide +kernel

end WormCore.Sound
