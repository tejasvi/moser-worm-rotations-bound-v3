import WormSound.Defs

/-!
# Boxes: `set!`, `InBox`, `BoxSub`, and the two halves of a box
-/

namespace WormCore.Sound

open MoserWorm

lemma size_set! {α : Type} (a : Array α) (k : ℕ) (v : α) : (a.set! k v).size = a.size := by
  simp

lemma getElem!_set! {a : Array Int} {k i : ℕ} {v : Int} :
    (a.set! k v)[i]! = if k = i ∧ k < a.size then v else a[i]! := by
  by_cases hi : i < a.size
  · rw [getElem!_pos (a.set! k v) i (by simpa using hi), getElem!_pos a i hi]
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds hi]
    by_cases hk : k = i
    · subst hk; simp [hi]
    · simp [hk]
  · rw [getElem!_neg (a.set! k v) i (by simpa using hi), getElem!_neg a i hi]
    split_ifs with h
    · exact absurd (h.1 ▸ h.2) hi
    · rfl

lemma set!_of_size_le {a : Array Int} {k : ℕ} (hk : a.size ≤ k) (v : Int) : a.set! k v = a := by
  simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def]
  exact dite_eq_right_iff.2 fun h => absurd h (by omega)

lemma BoxSub.refl (lo hi : Array Int) : BoxSub lo hi lo hi := fun _ _ => ⟨le_rfl, le_rfl⟩

lemma BoxSub.trans {lo hi lo' hi' lo'' hi'' : Array Int} (h1 : BoxSub lo hi lo' hi') (h2 : BoxSub lo' hi' lo'' hi'') :
    BoxSub lo hi lo'' hi'' := fun i hi12 =>
  ⟨(h2 i hi12).1.trans (h1 i hi12).1, (h1 i hi12).2.trans (h2 i hi12).2⟩

lemma two_pow_BS_pos : (0 : ℝ) < 2 ^ BS := by positivity

/-- A nonempty box has `lo ≤ hi` on the coordinates `0, …, 11`. -/
lemma InBox.le {lo hi : Array Int} {x : Fin 12 → ℝ} (h : InBox lo hi x) {i : ℕ} (hi12 : i < 12) :
    lo[i]! ≤ hi[i]! := by
  have := h ⟨i, hi12⟩
  have h2 : (lo[i]! : ℝ) / 2 ^ BS ≤ (hi[i]! : ℝ) / 2 ^ BS := this.1.trans this.2
  have h3 := (div_le_div_iff_of_pos_right two_pow_BS_pos).1 h2
  exact_mod_cast h3

/-- The two halves of `halves`. -/
lemma halves_eq {lo hi : Array Int} {k : ℕ} {l u : Array Int × Array Int} (h : halves lo hi k = some (l, u)) :
    (lo[k]! + hi[k]!) % 2 = 0 ∧ k < lo.size ∧ k < hi.size ∧
      l = (lo, hi.set! k ((lo[k]! + hi[k]!) / 2)) ∧ u = (lo.set! k ((lo[k]! + hi[k]!) / 2), hi) := by
  simp only [halves] at h
  split_ifs at h with hc
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hc.1, hc.2.1, hc.2.2, h.1.symm, h.2.symm⟩

lemma halves_size {lo hi : Array Int} {k : ℕ} {l u : Array Int × Array Int} (h : halves lo hi k = some (l, u)) :
    l.1.size = lo.size ∧ l.2.size = hi.size ∧ u.1.size = lo.size ∧ u.2.size = hi.size := by
  obtain ⟨-, -, -, rfl, rfl⟩ := halves_eq h
  simp

/-- **Halves cover**: a point of the box lies in one of the two halves. -/
lemma halves_cover {lo hi : Array Int} {k : ℕ} {l u : Array Int × Array Int} (h : halves lo hi k = some (l, u))
    {x : Fin 12 → ℝ} (hx : InBox lo hi x) : InBox l.1 l.2 x ∨ InBox u.1 u.2 x := by
  obtain ⟨-, hklo, hkhi, rfl, rfl⟩ := halves_eq h
  set m := (lo[k]! + hi[k]!) / 2 with hm
  by_cases hk12 : k < 12
  · by_cases hxk : x ⟨k, hk12⟩ ≤ (m : ℝ) / 2 ^ BS
    · left
      intro i
      refine ⟨(hx i).1, ?_⟩
      simp only [getElem!_set!]
      split_ifs with hki
      · have : i = ⟨k, hk12⟩ := Fin.ext hki.1.symm
        rw [this]; exact hxk
      · exact (hx i).2
    · right
      intro i
      refine ⟨?_, (hx i).2⟩
      simp only [getElem!_set!]
      split_ifs with hki
      · have : i = ⟨k, hk12⟩ := Fin.ext hki.1.symm
        rw [this]; exact (not_le.1 hxk).le
      · exact (hx i).1
  · left
    intro i
    refine ⟨(hx i).1, ?_⟩
    simp only [getElem!_set!]
    split_ifs with hki
    · exact absurd (hki.1 ▸ i.isLt) hk12
    · exact (hx i).2

/-- **Halves lie in the box** when the box is oriented along the split coordinate. -/
lemma halves_sub {lo hi : Array Int} {k : ℕ} {l u : Array Int × Array Int} (h : halves lo hi k = some (l, u))
    (hle : lo[k]! ≤ hi[k]!) : BoxSub l.1 l.2 lo hi ∧ BoxSub u.1 u.2 lo hi := by
  obtain ⟨hev, hklo, hkhi, rfl, rfl⟩ := halves_eq h
  have h1 : (lo[k]! + hi[k]!) / 2 ≤ hi[k]! := by omega
  have h2 : lo[k]! ≤ (lo[k]! + hi[k]!) / 2 := by omega
  refine ⟨fun i _ => ⟨le_rfl, ?_⟩, fun i _ => ⟨?_, le_rfl⟩⟩
  · simp only [getElem!_set!]
    split_ifs with hki
    · rw [← hki.1]; exact h1
    · exact le_rfl
  · simp only [getElem!_set!]
    split_ifs with hki
    · rw [← hki.1]; exact h2
    · exact le_rfl

/-- The halves of an oriented box (`lo ≤ hi` on `0, …, 11`) are oriented. -/
lemma halves_oriented {lo hi : Array Int} {k : ℕ} {l u : Array Int × Array Int} (h : halves lo hi k = some (l, u))
    (hle : ∀ i < 12, lo[i]! ≤ hi[i]!) :
    (∀ i < 12, l.1[i]! ≤ l.2[i]!) ∧ (∀ i < 12, u.1[i]! ≤ u.2[i]!) := by
  obtain ⟨hev, hklo, hkhi, rfl, rfl⟩ := halves_eq h
  refine ⟨fun i hi12 => ?_, fun i hi12 => ?_⟩
  · simp only [getElem!_set!]
    split_ifs with hki
    · rw [← hki.1] at hi12 ⊢; have := hle k hi12; omega
    · exact hle i hi12
  · simp only [getElem!_set!]
    split_ifs with hki
    · rw [← hki.1] at hi12 ⊢; have := hle k hi12; omega
    · exact hle i hi12

end WormCore.Sound
