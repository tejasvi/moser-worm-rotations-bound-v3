import WormSound.AssemblyAt
import WormSound.RootAt

/-!
# The instance `τ = 2410/10000` of the assembly, given the certificate facts

`wormLowerAt_2410_of_certificate`: the statement `WormLowerAt (2410/10000)` from the three certificate facts of
`cert_w2410a`
(supplied by the native shards in `WormN.Final`).
-/

noncomputable section

namespace WormCore.Sound

open MoserWorm hiding cross shoelace

/-- The checker's `τ` (`tauHiW · 2⁻⁵⁶`) is at least `2410/10000`. -/
lemma tau_2410_le : (2410 / 10000 : ℝ) ≤ (tauHiW : ℝ) / 2 ^ dfxS := by
  norm_num [tauHiW, dfxS]

theorem wormLowerAt_2410_of_certificate (skelOf : ℕ → String) (unitLists : List (List (ℕ × ℕ)))
    (hskel : (List.range rootW.nparts).all (fun p => (unitBoxes rootW p (skelOf p)).isSome) = true)
    (hcover : allUnitsOf skelOf = unitLists.flatten)
    (hchunks : ∀ L ∈ unitLists, ∃ txt, chunkCheck famW rootW maxsmallW tauHiW rdepthW skelOf txt = some L) :
    Worm.WormLowerAt (2410 / 10000) :=
  wormLowerAt_of_certificate (2410 / 10000) (by norm_num) tau_2410_le root_box_at skelOf unitLists hskel hcover
    hchunks

end WormCore.Sound
