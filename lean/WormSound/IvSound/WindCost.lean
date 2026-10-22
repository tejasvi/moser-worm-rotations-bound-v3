import Mathlib.Order.MinMax
import Mathlib.Tactic.Lemma
import WormCore.Check

/-!
# Soundness of the winding-cost computation of the fan test (`windScan`, `windBest`, `windCost`)

`ArcsB m P D s₀ i arcs`: the arcs `(d, c)` cover the positions `i, …, m` (relative to `s₀`, mod `m`); along each arc
`P` holds for every prefix length `1, …, d`, and an arc of cost `1` also has `D` at its end (cost `2` otherwise).
`windCost_sound`: if `windCost m P D s₀ < 100`, such a cover exists from position `0` with total cost at most
`windCost m P D s₀`.
-/

namespace WormCore

namespace IvSound

/-- A cover of the positions `i, …, m` by arcs `(length, cost)`. -/
def ArcsB (m : Nat) (P D : Nat → Nat → Bool) (s₀ : Nat) : Nat → List (Nat × Nat) → Prop
  | i, [] => i = m
  | i, (d, c) :: rest =>
      1 ≤ d ∧ i + d ≤ m ∧ (∀ d', 1 ≤ d' → d' ≤ d → P ((s₀ + i) % m) d' = true) ∧
        (c = 1 ∧ D ((s₀ + i) % m) d = true ∨ c = 2) ∧ ArcsB m P D s₀ (i + d) rest

/-- A cover from position `i` of total cost at most `c`. -/
def CoverB (m : Nat) (P D : Nat → Nat → Bool) (s₀ i c : Nat) : Prop :=
  ∃ arcs : List (Nat × Nat), ArcsB m P D s₀ i arcs ∧ (arcs.map Prod.snd).sum ≤ c

variable {m : Nat} {P D : Nat → Nat → Bool} {s₀ : Nat}

lemma ArcsB.le : ∀ {i : Nat} {arcs : List (Nat × Nat)}, ArcsB m P D s₀ i arcs → i ≤ m
  | _, [], h => le_of_eq h
  | _, (_, _) :: _, h => by have := h.2.1; omega

lemma coverB_mono {i c c' : Nat} (h : CoverB m P D s₀ i c) (hc : c ≤ c') : CoverB m P D s₀ i c' := by
  obtain ⟨arcs, ha, hs⟩ := h
  exact ⟨arcs, ha, hs.trans hc⟩

/-- The scan over the arc ends `i + d, i + d + 1, …` of `windScan`. -/
lemma windScan_sound (i : Nat) :
    ∀ (bs : List Nat) (d : Nat), 1 ≤ d →
      (∀ d', 1 ≤ d' → d' < d → P ((s₀ + i) % m) d' = true) →
      (∀ j, bs.getD j 100 < 100 → CoverB m P D s₀ (i + d + j) (bs.getD j 100)) →
      windScan (P ((s₀ + i) % m)) (D ((s₀ + i) % m)) d bs < 100 →
      CoverB m P D s₀ i (windScan (P ((s₀ + i) % m)) (D ((s₀ + i) % m)) d bs) := by
  intro bs
  induction bs with
  | nil => intro d _ _ _ h; simp [windScan] at h
  | cons b bs ih =>
    intro d hd hpre hent h
    unfold windScan at h ⊢
    by_cases hP : P ((s₀ + i) % m) d = true
    · simp only [hP, ite_true] at h ⊢
      rcases min_choice ((if D ((s₀ + i) % m) d = true then 1 else 2) + b)
          (windScan (P ((s₀ + i) % m)) (D ((s₀ + i) % m)) (d + 1) bs) with hmin | hmin
      · -- the arc of length `d`, then the cover from `i + d`
        rw [hmin] at h ⊢
        have hb : b < 100 := by split_ifs at h <;> omega
        have h0 := hent 0 (by simpa using hb)
        simp only [List.getD_cons_zero, Nat.add_zero] at h0
        obtain ⟨arcs, ha, hs⟩ := h0
        refine ⟨(d, if D ((s₀ + i) % m) d = true then 1 else 2) :: arcs, ?_, ?_⟩
        · refine ⟨hd, ArcsB.le ha, fun d' h1 h2 => ?_, ?_, ha⟩
          · rcases Nat.lt_or_ge d' d with h3 | h3
            · exact hpre d' h1 h3
            · have : d' = d := by omega
              rw [this]; exact hP
          · by_cases hD : D ((s₀ + i) % m) d = true
            · left; simp [hD]
            · right; simp [hD]
        · simp only [List.map_cons, List.sum_cons]
          omega
      · -- a longer arc
        rw [hmin] at h ⊢
        refine ih (d + 1) (by omega) (fun d' h1 h2 => ?_) (fun j hj => ?_) h
        · rcases Nat.lt_or_ge d' d with h3 | h3
          · exact hpre d' h1 h3
          · have : d' = d := by omega
            rw [this]; exact hP
        · have := hent (j + 1) (by simpa using hj)
          simpa [List.getD_cons_succ, show i + d + (j + 1) = i + (d + 1) + j by omega] using this
    · simp only [hP] at h
      simp at h

/-- `windBest m P D s₀ k = [best(m − k), …, best(m)]`: every entry below `100` is the cost bound of a cover. -/
lemma windBest_sound : ∀ k, k ≤ m → ∀ j, (windBest m P D s₀ k).getD j 100 < 100 →
    CoverB m P D s₀ (m - k + j) ((windBest m P D s₀ k).getD j 100) := by
  intro k
  induction k with
  | zero =>
    intro _ j hj
    rcases j with _ | j
    · simp only [windBest, List.getD_cons_zero, Nat.sub_zero, Nat.add_zero]
      exact ⟨[], rfl, le_refl _⟩
    · simp [windBest] at hj
  | succ k ih =>
    intro hk j hj
    rcases j with _ | j
    · simp only [windBest, List.getD_cons_zero, Nat.add_zero] at hj ⊢
      refine windScan_sound (m - (k + 1)) (windBest m P D s₀ k) 1 le_rfl (fun d' h1 h2 => by omega)
        (fun j' hj' => ?_) hj
      have := ih (by omega) j' hj'
      rwa [show m - (k + 1) + 1 + j' = m - k + j' by omega]
    · simp only [windBest, List.getD_cons_succ] at hj ⊢
      have := ih (by omega) j hj
      rwa [show m - (k + 1) + (j + 1) = m - k + j by omega]

/-- **The winding cost.** If `windCost m P D s₀ < 100`, a cover of the whole cycle from `s₀` by arcs exists, of total
cost at most `windCost m P D s₀`. -/
theorem windCost_sound (h : windCost m P D s₀ < 100) : CoverB m P D s₀ 0 (windCost m P D s₀) := by
  have e : windCost m P D s₀ = (windBest m P D s₀ m).getD 0 100 := by
    unfold windCost
    rcases windBest m P D s₀ m with _ | ⟨a, l⟩
    · rfl
    · rfl
  rw [e] at h ⊢
  have := windBest_sound (P := P) (D := D) (s₀ := s₀) m le_rfl 0 h
  rwa [Nat.sub_self, Nat.add_zero] at this

end IvSound

end WormCore
