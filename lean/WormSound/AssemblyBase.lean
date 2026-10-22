import WormSound.LeafSound
import WormSound.Tree
import WormCore.Family

/-!
# Common lemmas of the assembly: the root data and the units of all parts

`allUnitsOf`, the facts about `rootW` checked by `decide`, and the family side conditions.
-/

noncomputable section

namespace WormCore.Sound

open MeasureTheory Worm
open MoserWorm hiding cross shoelace

/-- The units `(p, u)` of all parts, given the skeletons. -/
def allUnitsOf (skelOf : ℕ → String) : List (ℕ × ℕ) :=
  (List.range rootW.nparts).flatMap fun p =>
    (List.range ((unitBoxes rootW p (skelOf p)).getD #[]).size).map (p, ·)

lemma boxSub_trans {a b c d e f : Array Int} (h1 : BoxSub a b c d) (h2 : BoxSub c d e f) : BoxSub a b e f :=
  fun i hi => ⟨(h2 i hi).1.trans (h1 i hi).1, (h1 i hi).2.trans (h2 i hi).2⟩

lemma rootExact_rootW : rootExact rootW = true := by decide

lemma rootShape_rootW : RootShape rootW := by
  unfold RootShape
  decide

lemma angleRange_rootW : AngleRange rootW.lo rootW.hi := by
  unfold AngleRange
  decide

lemma angleRange_of_sub {lo hi : Array Int} (h : BoxSub lo hi rootW.lo rootW.hi) : AngleRange lo hi := by
  intro b hb
  have hr := angleRange_rootW b hb
  have hs := h (3 * b) (by omega)
  exact ⟨hr.1.trans hs.1, hs.2.trans hr.2⟩

lemma arcsOK_famArcs : ArcsOK famArcs := by
  unfold ArcsOK
  decide

lemma famGid_bodies : ∀ g ∈ famGid, g.1 < 5 := by decide

end WormCore.Sound
