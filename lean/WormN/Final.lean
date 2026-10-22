import WormN.All
import WormSound.FinalAt

/-!
# The lower bound `0.2410` for Moser's worm problem with rotations and translations only (native track)

The certificate facts `WormN.skel_ok`, `WormN.cover` and `WormN.chunks_ok` of `cert_w2410a` (checked by
`native_decide` in the modules `WormN.*`) give `WormLowerAt (2410/10000)` through `wormLowerAt_2410_of_certificate`.
-/

namespace Worm

/-- **Theorem.** Every convex set that contains a rotated and translated copy of every unit arc has area at
least `0.2410`. -/
theorem worm_lower_2410 : WormLowerAt (2410 / 10000) :=
  WormCore.Sound.wormLowerAt_2410_of_certificate WormN.skelOf WormN.unitLists WormN.skel_ok WormN.cover
    WormN.chunks_ok

/-- **Theorem**, for the least area. -/
theorem optimalAreaM_lower_2410 : OptimalAreaLowerAt (2410 / 10000) :=
  WormCore.Sound.optimalAreaLowerAt_of worm_lower_2410

end Worm
