import WormSound.TreeProof.Boxes

/-!
# The root cells: mixed-radix cell numbers, the cells cover the root box and lie in it
-/

namespace WormCore.Sound

open MoserWorm

/-! ## Products and the mixed radix -/

lemma foldl_mul_eq (l : List ℕ) (a : ℕ) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.prod_cons, Nat.mul_assoc]

lemma stride_eq (R : Root) (j : ℕ) : stride R j = (R.split0.toList.drop (j + 1)).prod := by
  rw [stride, foldl_mul_eq, Nat.one_mul]

lemma ncells_eq (R : Root) : ncells R = R.split0.toList.prod := by
  rw [ncells, ← Array.foldl_toList, foldl_mul_eq, Nat.one_mul]

/-- The mixed-radix number with digits `d 0, d 1, …` (most significant first) over the radices `L`. -/
def mrEnc : List ℕ → (ℕ → ℕ) → ℕ
  | [], _ => 0
  | _ :: L, d => d 0 * L.prod + mrEnc L (fun j => d (j + 1))

theorem mrEnc_spec : ∀ (L : List ℕ) (d : ℕ → ℕ), (∀ j < L.length, d j < L[j]!) →
    mrEnc L d < L.prod ∧ ∀ j < L.length, (mrEnc L d / (L.drop (j + 1)).prod) % L[j]! = d j
  | [], d, _ => by simp [mrEnc]
  | s :: L, d, hd => by
    have hd' : ∀ j < L.length, d (j + 1) < L[j]! := fun j hj => by
      have h := hd (j + 1) (by simp; omega)
      rwa [List.getElem!_cons_succ] at h
    obtain ⟨ih1, ih2⟩ := mrEnc_spec L (fun j => d (j + 1)) hd'
    have h0 : d 0 < s := by
      have h := hd 0 (by simp)
      rwa [List.getElem!_cons_zero] at h
    have hP : 0 < L.prod := by omega
    refine ⟨?_, ?_⟩
    · simp only [mrEnc, List.prod_cons]
      calc d 0 * L.prod + mrEnc L (fun j => d (j + 1)) < d 0 * L.prod + L.prod := by omega
        _ = (d 0 + 1) * L.prod := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ s * L.prod := Nat.mul_le_mul_right _ h0
    · intro j hj
      rcases j with _ | j
      · simp only [mrEnc, Nat.zero_add, List.drop_succ_cons, List.drop_zero, List.getElem!_cons_zero]
        rw [Nat.mul_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt ih1, Nat.add_zero, Nat.mod_eq_of_lt h0]
      · have hj' : j < L.length := by simp at hj; omega
        simp only [mrEnc, List.drop_succ_cons, List.getElem!_cons_succ]
        have hLP : L.prod = (L.take (j + 1)).prod * (L.drop (j + 1)).prod :=
          (List.prod_take_mul_prod_drop L (j + 1)).symm
        have hQ : 0 < (L.drop (j + 1)).prod :=
          Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hLP; omega
        have hT : (L.take (j + 1)).prod = (L.take j).prod * L[j]! := by
          rw [getElem!_pos L j hj']; exact List.prod_take_succ L j hj'
        rw [hLP, hT, show d 0 * ((L.take j).prod * L[j]! * (L.drop (j + 1)).prod) =
          (L.drop (j + 1)).prod * (d 0 * (L.take j).prod * L[j]!) by ring, Nat.mul_add_div hQ, Nat.mul_add_mod']
        exact ih2 j hj'

/-- Cell numbers from coordinate indices: `cellIdx` decodes the mixed-radix number. -/
theorem cellIdx_mrEnc (R : Root) (d : ℕ → ℕ) (hd : ∀ j < R.split0.size, d j < R.split0[j]!) :
    mrEnc R.split0.toList d < ncells R ∧ ∀ j < R.split0.size, cellIdx R (mrEnc R.split0.toList d) j = d j := by
  have hd' : ∀ j < R.split0.toList.length, d j < R.split0.toList[j]! := by
    intro j hj
    rw [Array.getElem!_toList]
    exact hd j (by simpa using hj)
  obtain ⟨h1, h2⟩ := mrEnc_spec _ d hd'
  refine ⟨by rw [ncells_eq]; exact h1, fun j hj => ?_⟩
  rw [cellIdx, stride_eq, ← Array.getElem!_toList]
  exact h2 j (by simpa using hj)

/-! ## Cell boxes -/

lemma getElem!_range_map {n i : ℕ} (f : ℕ → Int) (hi : i < n) : ((List.range n).toArray.map f)[i]! = f i := by
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

lemma cellBox_size (R : Root) (c : ℕ) : (cellBox R c).1.size = R.lo.size ∧ (cellBox R c).2.size = R.lo.size := by
  simp [cellBox]

lemma cellBox_fst_get (R : Root) (c : ℕ) {i : ℕ} (hi : i < R.lo.size) :
    (cellBox R c).1[i]! = R.lo[i]! + (R.hi[i]! - R.lo[i]!) / ((R.split0[i]! : ℕ) : ℤ) * (cellIdx R c i : ℤ) := by
  simp only [cellBox]
  exact getElem!_range_map _ hi

lemma cellBox_snd_get (R : Root) (c : ℕ) {i : ℕ} (hi : i < R.lo.size) :
    (cellBox R c).2[i]! =
      R.lo[i]! + (R.hi[i]! - R.lo[i]!) / ((R.split0[i]! : ℕ) : ℤ) * ((cellIdx R c i : ℤ) + 1) := by
  simp only [cellBox]
  exact getElem!_range_map _ hi

lemma rootExact_spec (R : Root) (hR : rootExact R = true) {j : ℕ} (hj : j < R.split0.size) :
    (R.hi[j]! - R.lo[j]!) % ((R.split0[j]! : ℕ) : ℤ) = 0 ∧ R.lo[j]! < R.hi[j]! ∧ 0 < R.split0[j]! := by
  rw [rootExact, List.all_eq_true] at hR
  have h := hR j (List.mem_range.2 hj)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The width of the cells along coordinate `j`. -/
lemma cellW_spec (R : Root) (hR : rootExact R = true) {j : ℕ} (hj : j < R.split0.size) :
    0 < (R.hi[j]! - R.lo[j]!) / ((R.split0[j]! : ℕ) : ℤ) ∧
      (R.hi[j]! - R.lo[j]!) / ((R.split0[j]! : ℕ) : ℤ) * ((R.split0[j]! : ℕ) : ℤ) = R.hi[j]! - R.lo[j]! := by
  obtain ⟨hex, hlt, hpos⟩ := rootExact_spec R hR hj
  have hmul := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hex)
  refine ⟨?_, hmul⟩
  have hs : (0 : ℤ) < ((R.split0[j]! : ℕ) : ℤ) := by exact_mod_cast hpos
  rcases lt_trichotomy ((R.hi[j]! - R.lo[j]!) / ((R.split0[j]! : ℕ) : ℤ)) 0 with h | h | h
  · nlinarith
  · rw [h, zero_mul] at hmul; omega
  · exact h

lemma cellBox_oriented (R : Root) (hR : rootExact R = true) (hS : RootShape R) (c : ℕ) :
    ∀ i < 12, (cellBox R c).1[i]! ≤ (cellBox R c).2[i]! := by
  obtain ⟨hlo, hhi, hsp, hnp, hdiv⟩ := hS
  intro i hi
  rw [cellBox_fst_get R c (by omega : i < R.lo.size), cellBox_snd_get R c (by omega : i < R.lo.size)]
  have hw := (cellW_spec R hR (by omega : i < R.split0.size)).1
  linarith

theorem cellBox_sub' (R : Root) (hR : rootExact R = true) (hS : RootShape R) (c : Nat) :
    BoxSub (cellBox R c).1 (cellBox R c).2 R.lo R.hi := by
  obtain ⟨hlo, hhi, hsp, hnp, hdiv⟩ := hS
  intro i hi
  obtain ⟨hex, hlt, hpos⟩ := rootExact_spec R hR (by omega : i < R.split0.size)
  obtain ⟨hw, hmul⟩ := cellW_spec R hR (by omega : i < R.split0.size)
  rw [cellBox_fst_get R c (by omega : i < R.lo.size), cellBox_snd_get R c (by omega : i < R.lo.size)]
  have hidx : cellIdx R c i < R.split0[i]! := Nat.mod_lt _ hpos
  have hidx' : (cellIdx R c i : ℤ) + 1 ≤ ((R.split0[i]! : ℕ) : ℤ) := by omega
  constructor
  · have : 0 ≤ (R.hi[i]! - R.lo[i]!) / ((R.split0[i]! : ℕ) : ℤ) * (cellIdx R c i : ℤ) :=
      mul_nonneg hw.le (by positivity)
    linarith
  · have := mul_le_mul_of_nonneg_left hidx' hw.le
    linarith

/-! ## The cells cover the root box -/

lemma exists_bracket (a : ℕ → ℝ) (t : ℝ) :
    ∀ s : ℕ, 0 < s → a 0 ≤ t → t ≤ a s → ∃ n < s, a n ≤ t ∧ t ≤ a (n + 1)
  | 0, h, _, _ => absurd h (lt_irrefl 0)
  | s + 1, _, h0, hs => by
    by_cases h : a s ≤ t
    · exact ⟨s, Nat.lt_succ_self s, h, hs⟩
    · rcases Nat.eq_zero_or_pos s with rfl | hpos
      · exact absurd h0 h
      · obtain ⟨n, hn, h1, h2⟩ := exists_bracket a t s hpos h0 (le_of_lt (not_le.1 h))
        exact ⟨n, Nat.lt_succ_of_lt hn, h1, h2⟩

/-- Along coordinate `j`, the point lies in some cell slab. -/
lemma exists_slab (R : Root) (hR : rootExact R = true) {j : ℕ} (hj : j < R.split0.size) (t : ℝ)
    (h0 : (R.lo[j]! : ℝ) / 2 ^ BS ≤ t) (h1 : t ≤ (R.hi[j]! : ℝ) / 2 ^ BS) :
    ∃ n < R.split0[j]!,
      ((R.lo[j]! + (R.hi[j]! - R.lo[j]!) / ((R.split0[j]! : ℕ) : ℤ) * (n : ℤ) : ℤ) : ℝ) / 2 ^ BS ≤ t ∧
      t ≤ ((R.lo[j]! + (R.hi[j]! - R.lo[j]!) / ((R.split0[j]! : ℕ) : ℤ) * ((n : ℤ) + 1) : ℤ) : ℝ) / 2 ^ BS := by
  obtain ⟨hex, hlt, hpos⟩ := rootExact_spec R hR hj
  obtain ⟨hw, hmul⟩ := cellW_spec R hR hj
  have ha0 : ((R.lo[j]! + (R.hi[j]! - R.lo[j]!) / ((R.split0[j]! : ℕ) : ℤ) * ((0 : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ BS ≤ t := by
    simpa using h0
  have has : t ≤ ((R.lo[j]! + (R.hi[j]! - R.lo[j]!) / ((R.split0[j]! : ℕ) : ℤ) * ((R.split0[j]! : ℕ) : ℤ) : ℤ) : ℝ)
      / 2 ^ BS := by
    rw [hmul]; simpa using h1
  obtain ⟨n, hn, ha, hb⟩ := exists_bracket
    (fun n : ℕ => ((R.lo[j]! + (R.hi[j]! - R.lo[j]!) / ((R.split0[j]! : ℕ) : ℤ) * (n : ℤ) : ℤ) : ℝ) / 2 ^ BS) t
    (R.split0[j]!) hpos ha0 has
  refine ⟨n, hn, ha, ?_⟩
  simpa using hb

theorem cells_cover' (R : Root) (hR : rootExact R = true) (hS : RootShape R) (x : Fin 12 → ℝ)
    (hx : InBox R.lo R.hi x) :
    ∃ p < R.nparts, ∃ k < ncells R / R.nparts,
      InBox (cellBox R (p + R.nparts * k)).1 (cellBox R (p + R.nparts * k)).2 x := by
  obtain ⟨hlo, hhi, hsp, hnp, hdiv⟩ := hS
  have hdig : ∀ j : Fin 12, ∃ n < R.split0[j.val]!,
      ((R.lo[j.val]! + (R.hi[j.val]! - R.lo[j.val]!) / ((R.split0[j.val]! : ℕ) : ℤ) * (n : ℤ) : ℤ) : ℝ) / 2 ^ BS
        ≤ x j ∧
      x j ≤ ((R.lo[j.val]! + (R.hi[j.val]! - R.lo[j.val]!) / ((R.split0[j.val]! : ℕ) : ℤ) * ((n : ℤ) + 1) : ℤ) : ℝ)
        / 2 ^ BS :=
    fun j => exists_slab R hR (by have := j.isLt; omega) (x j) (hx j).1 (hx j).2
  choose d hdlt hd using hdig
  let D : ℕ → ℕ := fun j => if h : j < 12 then d ⟨j, h⟩ else 0
  have hD : ∀ j : Fin 12, D j.val = d j := fun j => by simp [D, j.isLt]
  obtain ⟨hc, hidx⟩ := cellIdx_mrEnc R D fun j hj => by
    rw [show D j = d ⟨j, by omega⟩ from hD ⟨j, by omega⟩]; exact hdlt _
  refine ⟨mrEnc R.split0.toList D % R.nparts, Nat.mod_lt _ hnp, mrEnc R.split0.toList D / R.nparts,
    Nat.div_lt_div_of_lt_of_dvd (Nat.dvd_of_mod_eq_zero hdiv) hc, ?_⟩
  rw [Nat.mod_add_div]
  intro i
  have hi12 := i.isLt
  rw [cellBox_fst_get R _ (by omega : i.val < R.lo.size), cellBox_snd_get R _ (by omega : i.val < R.lo.size),
    hidx i.val (by omega), hD i]
  exact hd i

end WormCore.Sound
