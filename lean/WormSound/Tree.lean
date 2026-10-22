import WormSound.Defs
import WormSound.TreeProof.Units

/-!
# Coverage soundness of the certificate tree (statements)

The root cells cover the root box; the unit boxes of a part (from its skeleton) cover its cells; a checked unit covers
its box by boxes that pass `leafOK`; a successful chunk check does so for every unit it lists. Every box lies in the
box it came from (`BoxSub`). Covering "at least once" is enough (closed boxes; overlaps on faces are harmless). The leaf
test `leafOK` is opaque here.
-/

namespace WormCore.Sound

open MoserWorm

/-- **Cells.** The cells `p + nparts·k` (`p < nparts`, `k < ncells/nparts`) cover the root box. -/
theorem cells_cover (R : Root) (hR : rootExact R = true) (hS : RootShape R) (x : Fin 12 → ℝ)
    (hx : InBox R.lo R.hi x) :
    ∃ p < R.nparts, ∃ k < ncells R / R.nparts,
      InBox (cellBox R (p + R.nparts * k)).1 (cellBox R (p + R.nparts * k)).2 x := by
  exact cells_cover' R hR hS x hx

/-- Every cell lies in the root box. -/
theorem cellBox_sub (R : Root) (hR : rootExact R = true) (hS : RootShape R) (c : Nat) :
    BoxSub (cellBox R c).1 (cellBox R c).2 R.lo R.hi := by
  exact cellBox_sub' R hR hS c

/-- **Skeleton.** The unit boxes of a part lie in its cells and cover them. -/
theorem unitBoxes_cover (R : Root) (hR : rootExact R = true) (hS : RootShape R) (p : Nat) (skel : String)
    (boxes : Array (Array Int × Array Int)) (h : unitBoxes R p skel = some boxes) :
    (∀ u < boxes.size, ∃ k < ncells R / R.nparts,
      BoxSub boxes[u]!.1 boxes[u]!.2 (cellBox R (p + R.nparts * k)).1 (cellBox R (p + R.nparts * k)).2) ∧
    ∀ k < ncells R / R.nparts, ∀ x : Fin 12 → ℝ,
      InBox (cellBox R (p + R.nparts * k)).1 (cellBox R (p + R.nparts * k)).2 x →
      ∃ u < boxes.size, InBox boxes[u]!.1 boxes[u]!.2 x := by
  exact ⟨unitBoxes_sub hR hS h, unitBoxes_cover_cells h⟩

/-- **Unit.** A checked unit: every point of its box lies in a box inside it that passes `leafOK` with one of the
unit's records. -/
theorem unitOK_cover (F : Fam) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat) (box : Array Int × Array Int)
    (hb : box.1.size = 12 ∧ box.2.size = 12) (codes : String) (recs : List Rec)
    (h : unitOK F maxsmall tauHi rdepth box codes recs = true) (x : Fin 12 → ℝ) (hx : InBox box.1 box.2 x) :
    ∃ lo hi : Array Int, ∃ r ∈ recs, leafOK F maxsmall tauHi lo hi r = true ∧ InBox lo hi x ∧
      BoxSub lo hi box.1 box.2 := by
  exact unitOK_cover' F maxsmall tauHi rdepth box hb codes recs h x hx

/-- **Chunk.** Every unit listed by a successful chunk check is covered by boxes inside it that pass `leafOK`. -/
theorem chunkCheck_cover (F : Fam) (R : Root) (hS : RootShape R) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat)
    (skel : Nat → String) (txt : String) (L : List (Nat × Nat))
    (h : chunkCheck F R maxsmall tauHi rdepth skel txt = some L) :
    ∀ pu ∈ L, ∃ boxes, unitBoxes R pu.1 (skel pu.1) = some boxes ∧ pu.2 < boxes.size ∧
      ∀ x : Fin 12 → ℝ, InBox boxes[pu.2]!.1 boxes[pu.2]!.2 x →
        ∃ lo hi : Array Int, ∃ r : Rec, leafOK F maxsmall tauHi lo hi r = true ∧ InBox lo hi x ∧
          BoxSub lo hi boxes[pu.2]!.1 boxes[pu.2]!.2 := by
  exact chunkCheck_cover' F R hS maxsmall tauHi rdepth skel txt L h

end WormCore.Sound
