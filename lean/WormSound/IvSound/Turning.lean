import WormSound.Defs
import WormSound.IvSound.WindCost
import Worm13a.Geom.Wind

/-!
# The winding certificate and the continuity of the turning (proofs for `WormSound.Valid`)

* `turning_eq_turnSum`: `WormCore.Sound.turning P z` is the `turnSum` of `a_j = pt P j − z`;
* `turning_lt_of_windCost'`: positive consecutive turns, certified tables `Pb`, `Db` and `windCost ≤ 7` give turning
  `< 4π` (via `windCost_sound` and `Worm.Geom.turnSum_lt_of_arcs`);
* `turning_const'`: constancy on a preconnected set (via `Worm.Geom.turnSum_eq_two_pi_of_isPreconnected`).
-/

open Worm.Geom LebesgueCover

namespace WormCore

namespace IvSound

/-- `turning` as `turnSum`. -/
lemma turning_eq_turnSum (P : List ℂ) (z : ℂ) :
    WormCore.Sound.turning P z = turnSum (fun j => pt P j - z) P.length := by
  unfold WormCore.Sound.turning turnSum turn nxt
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [pt_mod]

/-- An arc cover of the tables gives an arc cover of the points. -/
lemma arcsB_to_cover {P : List ℂ} {z : ℂ} {Pb Db : ℕ → ℕ → Bool} {s0 : ℕ} (hm : 0 < P.length)
    (hP : ∀ i < P.length, ∀ d, Pb i d = true → 0 < cross (pt P i - z) (pt P (i + d) - z))
    (hD : ∀ i < P.length, ∀ d, Db i d = true →
      0 < (pt P i - z).re * (pt P (i + d) - z).re + (pt P i - z).im * (pt P (i + d) - z).im) :
    ∀ (arcs : List (ℕ × ℕ)) (i : ℕ), ArcsB P.length Pb Db s0 i arcs →
      ArcCover (fun j => pt P j - z) P.length s0 i arcs := by
  intro arcs
  induction arcs with
  | nil => intro i h; exact h
  | cons dc rest ih =>
    obtain ⟨d, c⟩ := dc
    intro i h
    obtain ⟨hd1, hdm, hpre, hcost, hrest⟩ := h
    have hi : (s0 + i) % P.length < P.length := Nat.mod_lt _ hm
    have hshift : ∀ e, pt P ((s0 + i + e) % P.length) = pt P ((s0 + i) % P.length + e) := fun e =>
      pt_congr P (by rw [Nat.mod_mod, Nat.mod_add_mod])
    refine ⟨hd1, hdm, fun d' h1 h2 => ?_, ?_, ih (i + d) hrest⟩
    · have := hP _ hi d' (hpre d' h1 h2)
      simp only [hshift]
      exact this
    · rcases hcost with ⟨hc1, hDt⟩ | hc2
      · left
        refine ⟨hc1, ?_⟩
        have := hD _ hi d hDt
        simp only [dotC, hshift]
        exact this
      · right; exact hc2

/-- **Winding certificate** (the statement of `WormCore.Sound.turning_lt_of_windCost`). -/
theorem turning_lt_of_windCost' (P : List ℂ) (z : ℂ) (h3 : 3 ≤ P.length)
    (hdet : ∀ j < P.length, 0 < cross (pt P j - z) (pt P (j + 1) - z)) (Pb Db : ℕ → ℕ → Bool)
    (hP : ∀ i < P.length, ∀ d, Pb i d = true → 0 < cross (pt P i - z) (pt P (i + d) - z))
    (hD : ∀ i < P.length, ∀ d, Db i d = true →
      0 < (pt P i - z).re * (pt P (i + d) - z).re + (pt P i - z).im * (pt P (i + d) - z).im)
    (s0 : ℕ) (hw : windCost P.length Pb Db s0 ≤ 7) :
    WormCore.Sound.turning P z < 4 * Real.pi := by
  have hm : 0 < P.length := by omega
  obtain ⟨arcs, harcs, hsum⟩ := windCost_sound (m := P.length) (P := Pb) (D := Db) (s₀ := s0) (by omega)
  have hcover := arcsB_to_cover hm hP hD arcs 0 harcs
  have hcons : ∀ j < P.length, 0 < detC (pt P j - z) (pt P (nxt P.length j) - z) := by
    intro j hj
    have := hdet j hj
    simp only [nxt, pt_mod]
    exact this
  rw [turning_eq_turnSum]
  exact turnSum_lt_of_arcs hm s0 hcons arcs hcover (hsum.trans hw)

/-- **Continuity** (the statement of `WormCore.Sound.turning_const`). -/
theorem turning_const' {S : Set (Fin 12 → ℝ)} (hS : IsPreconnected S) (P : (Fin 12 → ℝ) → List ℂ) (m : ℕ)
    (hm : ∀ x, (P x).length = m) (hc : ∀ j < m, ContinuousOn (fun x => (P x).getD j 0) S) (z : ℂ)
    (hdet : ∀ x ∈ S, ∀ j < m, 0 < cross (pt (P x) j - z) (pt (P x) (j + 1) - z)) {x0 : Fin 12 → ℝ}
    (hx0 : x0 ∈ S) (h0 : WormCore.Sound.turning (P x0) z < 4 * Real.pi) :
    ∀ x ∈ S, WormCore.Sound.turning (P x) z < 4 * Real.pi := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · intro x _
    unfold WormCore.Sound.turning
    rw [hm x, hm0, Finset.sum_range_zero]
    positivity
  · have hpt : ∀ x j, j < m → pt (P x) j = (P x).getD j 0 := fun x j hj => by
      unfold pt; rw [hm x, Nat.mod_eq_of_lt hj]
    have hcont : ∀ j < m, ContinuousOn (fun x => pt (P x) j - z) S := by
      intro j hj
      have e : (fun x => pt (P x) j - z) = fun x => (P x).getD j 0 - z := funext fun x => by rw [hpt x j hj]
      rw [e]
      exact (hc j hj).sub continuousOn_const
    have hdet' : ∀ x ∈ S, ∀ j < m, 0 < detC (pt (P x) j - z) (pt (P x) (nxt m j) - z) := by
      intro x hx j hj
      have := hdet x hx j hj
      have e : pt (P x) (nxt m j) = pt (P x) (j + 1) := by
        unfold nxt; rw [← hm x, pt_mod]
      rw [e]; exact this
    have h0' : turnSum (fun j => pt (P x0) j - z) m < 4 * Real.pi := by
      rw [← hm x0, ← turning_eq_turnSum]; exact h0
    have key := turnSum_eq_two_pi_of_isPreconnected hS hm0 (fun x j => pt (P x) j - z) hcont hdet' hx0 h0'
    intro x hx
    rw [turning_eq_turnSum, hm x, key x hx]
    linarith [Real.pi_pos]

end IvSound

end WormCore
