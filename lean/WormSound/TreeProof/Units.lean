import WormSound.TreeProof.Chunk
import WormSound.TreeProof.Cells

/-!
# The unit boxes of a part: sizes, coverage of the part's cells, containment in a cell; units and chunks
-/

namespace WormCore.Sound

open MoserWorm

lemma getElem!_mem_toList {α : Type} [Inhabited α] {a : Array α} {u : ℕ} (hu : u < a.size) : a[u]! ∈ a.toList := by
  rw [getElem!_pos a u hu]
  simp

lemma exists_of_mem_toList {α : Type} [Inhabited α] {a : Array α} {B : α} (h : B ∈ a.toList) :
    ∃ u < a.size, a[u]! = B := by
  obtain ⟨u, hu, rfl⟩ := List.mem_iff_getElem.1 h
  refine ⟨u, by simpa using hu, ?_⟩
  rw [getElem!_pos a u (by simpa using hu)]
  simp

/-- The cells of part `p` are the start boxes of its skeleton walk. -/
lemma unitBoxes_walk {R : Root} {p : ℕ} {skel : String} {boxes : Array (Array Int × Array Int)}
    (h : unitBoxes R p skel = some boxes) :
    skelWalk (2 * skel.length + 2) skel.toList
      ((List.range (ncells R / R.nparts)).map fun k => cellBox R (p + R.nparts * k)) #[] = some (boxes, []) := by
  rw [unitBoxes] at h
  split at h
  · rename_i acc heq
    simp only [Option.some.injEq] at h
    subst h
    exact heq
  · simp at h

lemma cell_mem {R : Root} {p k : ℕ} (hk : k < ncells R / R.nparts) :
    cellBox R (p + R.nparts * k) ∈ (List.range (ncells R / R.nparts)).map fun k => cellBox R (p + R.nparts * k) :=
  List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

/-- Every unit box has twelve coordinates. -/
theorem unitBoxes_size {R : Root} (hS : RootShape R) {p : ℕ} {skel : String} {boxes : Array (Array Int × Array Int)}
    (h : unitBoxes R p skel = some boxes) : ∀ u < boxes.size, boxes[u]!.1.size = 12 ∧ boxes[u]!.2.size = 12 := by
  intro u hu
  refine skelWalk_inv (fun B => B.1.size = 12 ∧ B.2.size = 12) ?_ _ _ _ _ _ _ (unitBoxes_walk h) ?_ (by simp) _
    (getElem!_mem_toList hu)
  · intro lo hi k l u' hP hh
    dsimp only at hP
    obtain ⟨h1, h2, h3, h4⟩ := halves_size hh
    exact ⟨⟨h1.trans hP.1, h2.trans hP.2⟩, ⟨h3.trans hP.1, h4.trans hP.2⟩⟩
  · intro B hB
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hB
    obtain ⟨h1, h2⟩ := cellBox_size R (p + R.nparts * k)
    exact ⟨h1.trans hS.1, h2.trans hS.1⟩

/-- Every point of a cell of part `p` lies in a unit box of `p`. -/
theorem unitBoxes_cover_cells {R : Root} {p : ℕ} {skel : String} {boxes : Array (Array Int × Array Int)}
    (h : unitBoxes R p skel = some boxes) :
    ∀ k < ncells R / R.nparts, ∀ x : Fin 12 → ℝ,
      InBox (cellBox R (p + R.nparts * k)).1 (cellBox R (p + R.nparts * k)).2 x →
      ∃ u < boxes.size, InBox boxes[u]!.1 boxes[u]!.2 x := by
  intro k hk x hx
  obtain ⟨B, hB, hxB⟩ := skelWalk_cover _ _ _ _ _ _ (unitBoxes_walk h) x (Or.inl ⟨_, cell_mem (p := p) hk, hx⟩)
  obtain ⟨u, hu, rfl⟩ := exists_of_mem_toList hB
  exact ⟨u, hu, hxB⟩

/-- Every unit box of part `p` lies in a cell of `p` (the cells are oriented: `rootExact`). -/
theorem unitBoxes_sub {R : Root} (hR : rootExact R = true) (hS : RootShape R) {p : ℕ} {skel : String}
    {boxes : Array (Array Int × Array Int)} (h : unitBoxes R p skel = some boxes) :
    ∀ u < boxes.size, ∃ k < ncells R / R.nparts,
      BoxSub boxes[u]!.1 boxes[u]!.2 (cellBox R (p + R.nparts * k)).1 (cellBox R (p + R.nparts * k)).2 := by
  intro u hu
  have key := skelWalk_inv (fun B => (B.1.size = 12 ∧ B.2.size = 12) ∧ (∀ i < 12, B.1[i]! ≤ B.2[i]!) ∧
      ∃ k < ncells R / R.nparts, BoxSub B.1 B.2 (cellBox R (p + R.nparts * k)).1 (cellBox R (p + R.nparts * k)).2)
    ?_ _ _ _ _ _ _ (unitBoxes_walk h) ?_ (by simp) _ (getElem!_mem_toList hu)
  · exact key.2.2
  · intro lo hi k l u' hP hh
    dsimp only at hP
    obtain ⟨⟨hs1, hs2⟩, hor, k', hk', hsub⟩ := hP
    obtain ⟨h1, h2, h3, h4⟩ := halves_size hh
    obtain ⟨-, hklo, -⟩ := halves_eq hh
    obtain ⟨hor1, hor2⟩ := halves_oriented hh hor
    obtain ⟨hsub1, hsub2⟩ := halves_sub hh (hor k (by omega))
    exact ⟨⟨⟨h1.trans hs1, h2.trans hs2⟩, hor1, k', hk', hsub1.trans hsub⟩,
      ⟨⟨h3.trans hs1, h4.trans hs2⟩, hor2, k', hk', hsub2.trans hsub⟩⟩
  · intro B hB
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hB
    obtain ⟨h1, h2⟩ := cellBox_size R (p + R.nparts * k)
    exact ⟨⟨h1.trans hS.1, h2.trans hS.1⟩, cellBox_oriented R hR hS _, k, List.mem_range.1 hk, BoxSub.refl _ _⟩

/-- A unit that passes `unitOK`: every point of its box lies in a box of a leaf that passed `leafOK`. -/
theorem unitOK_cover' (F : Fam) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat) (box : Array Int × Array Int)
    (hb : box.1.size = 12 ∧ box.2.size = 12) (codes : String) (recs : List Rec)
    (h : unitOK F maxsmall tauHi rdepth box codes recs = true) (x : Fin 12 → ℝ) (hx : InBox box.1 box.2 x) :
    ∃ lo hi : Array Int, ∃ r ∈ recs, leafOK F maxsmall tauHi lo hi r = true ∧ InBox lo hi x ∧
      BoxSub lo hi box.1 box.2 := by
  rw [unitOK] at h
  split at h
  · rename_i heq
    refine unitWalk_cover F maxsmall tauHi rdepth _ _ _ _ _ heq ?_ box (by simp) x hx
    intro B hB
    simp only [List.mem_singleton] at hB
    subst hB
    exact hb
  · simp at h

/-- The units listed by a successful chunk check: every point of the unit's box lies in a box of a leaf that passed
`leafOK`. -/
theorem chunkCheck_cover' (F : Fam) (R : Root) (hS : RootShape R) (maxsmall : Nat) (tauHi : Int) (rdepth : Nat)
    (skel : Nat → String) (txt : String) (L : List (Nat × Nat))
    (h : chunkCheck F R maxsmall tauHi rdepth skel txt = some L) :
    ∀ pu ∈ L, ∃ boxes, unitBoxes R pu.1 (skel pu.1) = some boxes ∧ pu.2 < boxes.size ∧
      ∀ x : Fin 12 → ℝ, InBox boxes[pu.2]!.1 boxes[pu.2]!.2 x →
        ∃ lo hi : Array Int, ∃ r : Rec, leafOK F maxsmall tauHi lo hi r = true ∧ InBox lo hi x ∧
          BoxSub lo hi boxes[pu.2]!.1 boxes[pu.2]!.2 := by
  intro pu hpu
  obtain ⟨boxes, hb, hu, cs, recs, hok⟩ := chunkCheck_spec F R maxsmall tauHi rdepth skel txt L h pu hpu
  refine ⟨boxes, hb, hu, fun x hx => ?_⟩
  obtain ⟨lo, hi, r, -, hr, hxr, hsub⟩ :=
    unitOK_cover' F maxsmall tauHi rdepth _ (unitBoxes_size hS hb _ hu) cs recs hok x hx
  exact ⟨lo, hi, r, hr, hxr, hsub⟩

end WormCore.Sound
