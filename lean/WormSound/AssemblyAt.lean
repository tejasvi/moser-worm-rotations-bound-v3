import WormSound.AssemblyBase
import WormSound.W1Gen
import Worm13a.StatementAt

/-!
# Assembly for a general bound `τ`

`wormLowerAt_of_certificate`: as `wormLowerM_of_certificate`, for any `τ > 0` below the checker's `τ` (`tauHiW`) whose
domain `D_τ` lies in the root box.
-/

noncomputable section

namespace WormCore.Sound

open MeasureTheory Worm
open MoserWorm hiding cross shoelace

/-- **Assembly** for a general `τ`. -/
theorem worm_lower_at_of_certificate (τ : ℝ) (hτ0 : 0 < τ) (hτ : τ ≤ (tauHiW : ℝ) / 2 ^ dfxS)
    (hroot : ∀ x, InDtauOf τ x → InBox rootW.lo rootW.hi x)
    (skelOf : ℕ → String) (unitLists : List (List (ℕ × ℕ)))
    (hskel : (List.range rootW.nparts).all (fun p => (unitBoxes rootW p (skelOf p)).isSome) = true)
    (hcover : allUnitsOf skelOf = unitLists.flatten)
    (hchunks : ∀ L ∈ unitLists, ∃ txt, chunkCheck famW rootW maxsmallW tauHiW rdepthW skelOf txt = some L)
    (K : Set ℂ) (hK : IsConvexCoverM K) : ENNReal.ofReal τ ≤ volume K := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨K', hK'c, hvol, x, hxD, hplace⟩ := w1_domain_of τ hτ0 K hK hlt
  have hxR := hroot x hxD
  obtain ⟨p, hp, k, hk, hxcell⟩ := cells_cover rootW rootExact_rootW rootShape_rootW x hxR
  have hsome : (unitBoxes rootW p (skelOf p)).isSome = true := by
    have := List.all_eq_true.mp hskel p (List.mem_range.mpr hp)
    simpa using this
  obtain ⟨boxes, hboxes⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hsub, hcov⟩ := unitBoxes_cover rootW rootExact_rootW rootShape_rootW p (skelOf p) boxes hboxes
  obtain ⟨u, hu, hxu⟩ := hcov k hk x hxcell
  have hpu : (p, u) ∈ allUnitsOf skelOf := by
    unfold allUnitsOf
    rw [List.mem_flatMap]
    refine ⟨p, List.mem_range.mpr hp, ?_⟩
    rw [hboxes]
    simpa using hu
  rw [hcover, List.mem_flatten] at hpu
  obtain ⟨L, hL, hpuL⟩ := hpu
  obtain ⟨txt, htxt⟩ := hchunks L hL
  obtain ⟨boxes', hboxes', _, hcov'⟩ :=
    chunkCheck_cover famW rootW rootShape_rootW maxsmallW tauHiW rdepthW skelOf txt L htxt (p, u) hpuL
  rw [hboxes] at hboxes'
  cases hboxes'
  obtain ⟨lo, hi, r, hleaf, hxleaf, hsubleaf⟩ := hcov' x hxu
  obtain ⟨k', _, hsubcell⟩ := hsub u hu
  have hsubroot : BoxSub lo hi rootW.lo rootW.hi :=
    boxSub_trans (boxSub_trans hsubleaf hsubcell) (cellBox_sub rootW rootExact_rootW rootShape_rootW _)
  have hlt' := leafOK_sound famArcs famGid arcsOK_famArcs rfl famGid_bodies maxsmallW (by decide) tauHiW
    (by decide) lo hi (angleRange_of_sub hsubroot) r hleaf x hxleaf K' hK'c hplace
  have hτ' : ENNReal.ofReal τ ≤ ENNReal.ofReal ((tauHiW : ℝ) / 2 ^ dfxS) := ENNReal.ofReal_le_ofReal hτ
  rw [hvol] at hlt'
  exact absurd (lt_of_le_of_lt hτ' hlt') (not_lt.mpr hlt.le)

/-- **Assembly** for a general `τ`, in the form of the statement. -/
theorem wormLowerAt_of_certificate (τ : ℝ) (hτ0 : 0 < τ) (hτ : τ ≤ (tauHiW : ℝ) / 2 ^ dfxS)
    (hroot : ∀ x, InDtauOf τ x → InBox rootW.lo rootW.hi x)
    (skelOf : ℕ → String) (unitLists : List (List (ℕ × ℕ)))
    (hskel : (List.range rootW.nparts).all (fun p => (unitBoxes rootW p (skelOf p)).isSome) = true)
    (hcover : allUnitsOf skelOf = unitLists.flatten)
    (hchunks : ∀ L ∈ unitLists, ∃ txt, chunkCheck famW rootW maxsmallW tauHiW rdepthW skelOf txt = some L) :
    WormLowerAt τ :=
  fun K hK => worm_lower_at_of_certificate τ hτ0 hτ hroot skelOf unitLists hskel hcover hchunks K hK

/-- The bound for all covers gives the bound for the least area. -/
theorem optimalAreaLowerAt_of {τ : ℝ} (h : WormLowerAt τ) : OptimalAreaLowerAt τ := by
  unfold OptimalAreaLowerAt optimalAreaM
  exact le_sInf fun a ⟨K, hK, hKa⟩ => hKa ▸ h K hK

end WormCore.Sound
