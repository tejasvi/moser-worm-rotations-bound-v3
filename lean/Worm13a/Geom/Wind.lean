import Worm13a.Geom.LebFan

/-!
# The winding of a fan: constancy on a connected parameter set, and certificates by arcs

For points `a_j` (`j < m`, indices mod `m`) with positive turns `det(a_j, a_{j+1}) > 0`, the total turning
`turnSum a m = ∑_j arg(a_{j+1}/a_j)` is a positive multiple of `2π` (as `LebesgueCover.turnSum_int` in the Lean proof for Lebesgue's universal covering problem).

* `turnSum_eq_two_pi_of_isPreconnected`: for a family `a p` that is continuous in `p` on a preconnected set `S`
  (for instance a box of placements), with positive turns at every `p ∈ S` and total turning `< 4π` at one point of
  `S`, the total turning is `2π` at every point of `S`.
* `sum_turn_arc`: over an arc `i, …, i + d` whose points lie strictly left of `a_i`, the turns add up to
  `arg(a_{i+d}/a_i) ∈ (0, π)`.
* `turnSum_lt_of_arcs`: a cover of the cycle by such arcs, each costing `1` (endpoints at an acute angle, turning
  `< π/2`) or `2` (turning `< π`), of total cost at most `7`, gives total turning `< 4π`.
-/

open Set Complex
open LebesgueCover

noncomputable section

namespace Worm.Geom

/-! ### Constancy on a preconnected set -/

/-- **Constancy of the winding.** -/
theorem turnSum_eq_two_pi_of_isPreconnected {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsPreconnected S)
    {m : ℕ} (hm : 0 < m) (a : X → ℕ → ℂ) (hcont : ∀ j < m, ContinuousOn (fun p => a p j) S)
    (hdet : ∀ p ∈ S, ∀ j < m, 0 < detC (a p j) (a p (nxt m j)))
    {p₀ : X} (hp₀ : p₀ ∈ S) (h0 : turnSum (a p₀) m < 4 * Real.pi) :
    ∀ p ∈ S, turnSum (a p) m = 2 * Real.pi := by
  set f : X → ℝ := fun p => turnSum (a p) m with hf
  have hint : ∀ p ∈ S, ∃ n : ℤ, f p = n * (2 * Real.pi) := fun p hp =>
    turnSum_int hm (fun j hj => ne_zero_of_detC_pos (hdet p hp j hj))
  have hf0 : f p₀ = 2 * Real.pi := turnSum_eq_two_pi hm (hdet p₀ hp₀) h0
  have hcont' : ContinuousOn f S := by
    show ContinuousOn (fun p => ∑ j ∈ Finset.range m, turn (a p) m j) S
    apply continuousOn_finsetSum
    intro j hj p hp
    have hj' := Finset.mem_range.mp hj
    have hd := hdet p hp j hj'
    have hne : a p j ≠ 0 := ne_zero_of_detC_pos hd
    have hslit : a p (nxt m j) / a p j ∈ slitPlane := by
      rw [mem_slitPlane_iff]; right
      rw [div_im_eq]; exact (div_pos hd (Complex.normSq_pos.mpr hne)).ne'
    have hnx : nxt m j < m := Nat.mod_lt _ hm
    have hq : ContinuousWithinAt (fun p => a p (nxt m j) / a p j) S p :=
      ((hcont _ hnx) p hp).div ((hcont j hj') p hp) hne
    show ContinuousWithinAt (fun p => arg (a p (nxt m j) / a p j)) S p
    exact ContinuousAt.comp_continuousWithinAt (g := arg) (f := fun p => a p (nxt m j) / a p j)
      (continuousAt_arg hslit) hq
  intro p hp
  obtain ⟨n, hn⟩ := hint p hp
  have hpos : 0 < f p := turnSum_pos hm (hdet p hp)
  have hpi := Real.pi_pos
  have hn1 : (1 : ℤ) ≤ n := by
    have : (0 : ℝ) < n := by
      by_contra hc; push Not at hc
      have : (n : ℝ) * (2 * Real.pi) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by positivity)
      linarith
    have : (0 : ℤ) < n := by exact_mod_cast this
    omega
  by_contra hne1
  have hn2 : (2 : ℤ) ≤ n := by
    rcases eq_or_lt_of_le hn1 with h | h
    · have h2 : f p = 2 * Real.pi := by rw [hn, ← h]; push_cast; ring
      exact absurd h2 hne1
    · omega
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have h3 : 3 * Real.pi ∈ Icc (f p₀) (f p) := by
    rw [hf0, hn]; constructor <;> nlinarith
  obtain ⟨p', hp', hfp'⟩ := hS.intermediate_value hp₀ hp hcont' h3
  obtain ⟨n', hn'⟩ := hint p' hp'
  have h := hfp'.symm.trans hn'
  have hz : ((2 * n' : ℝ) - 3) * Real.pi = 0 := by linarith
  rcases mul_eq_zero.mp hz with h' | h'
  · have h2 : (2 * n' : ℝ) = 3 := by linarith
    have h2' : (2 * n' : ℤ) = 3 := by exact_mod_cast h2
    omega
  · exact absurd h' hpi.ne'

/-! ### Turning over an arc -/

/-- If `det(u, v)`, `det(u, w)` and `det(v, w)` are positive, the angle from `u` to `w` is the angle from `u` to `v`
plus the angle from `v` to `w`. -/
lemma arg_div_add {u v w : ℂ} (huv : 0 < detC u v) (huw : 0 < detC u w) (hvw : 0 < detC v w) :
    arg (w / u) = arg (v / u) + arg (w / v) := by
  have hu : u ≠ 0 := ne_zero_of_detC_pos huv
  have hv : v ≠ 0 := ne_zero_of_detC_pos hvw
  have h1 := turn_mem hu huv
  have h2 := turn_mem hu huw
  have h3 := turn_mem hv hvw
  have hvu : v / u ≠ 0 := div_ne_zero hv hu
  have hw : w ≠ 0 := by
    rintro rfl; simp [detC] at huw
  have hwu : w / u ≠ 0 := div_ne_zero hw hu
  have hang := Complex.arg_div_coe_angle hwu hvu
  rw [show w / u / (v / u) = w / v by field_simp, ← Real.Angle.coe_sub] at hang
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  have hpi := Real.pi_pos
  have hk0 : k = 0 := by
    have hlo : (-1 : ℝ) < 2 * k := by
      have : -Real.pi < 2 * Real.pi * k := by linarith
      nlinarith
    have hhi : (2 * k : ℝ) < 2 := by
      have : 2 * Real.pi * k < 2 * Real.pi := by linarith
      nlinarith
    have hlo' : (-1 : ℤ) < 2 * k := by exact_mod_cast hlo
    have hhi' : (2 * k : ℤ) < 2 := by exact_mod_cast hhi
    omega
  rw [hk0] at hk
  simp at hk
  linarith

/-- **Turning over an arc**: if the points `a_{i+d'}` (`1 ≤ d' ≤ d`, indices mod `m`) lie strictly left of `a_i` and
the turns along the arc are positive, the turns add up to the angle from `a_i` to `a_{i+d}`. -/
lemma sum_turn_arc {a : ℕ → ℂ} {m : ℕ} (i : ℕ) :
    ∀ d, (∀ d', 1 ≤ d' → d' ≤ d → 0 < detC (a (i % m)) (a ((i + d') % m))) →
      (∀ d' < d, 0 < detC (a ((i + d') % m)) (a ((i + d' + 1) % m))) →
      ∑ d' ∈ Finset.range d, turn a m ((i + d') % m) = arg (a ((i + d) % m) / a (i % m)) := by
  intro d
  induction d with
  | zero =>
    intro _ _
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    rcases eq_or_ne (a (i % m)) 0 with h | h
    · rw [h, div_zero, arg_zero]
    · rw [div_self h, arg_one]
  | succ d ih =>
    intro hleft hcons
    rw [Finset.sum_range_succ, ih (fun d' h1 h2 => hleft d' h1 (by omega)) (fun d' h => hcons d' (by omega))]
    have hnext : nxt m ((i + d) % m) = (i + d + 1) % m := by
      simp only [nxt, Nat.mod_add_mod]
    simp only [turn, hnext]
    have hvw := hcons d (by omega)
    have huw := hleft (d + 1) (by omega) le_rfl
    rw [show i + (d + 1) = i + d + 1 by ring] at huw ⊢
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp only [add_zero] at hvw huw ⊢
      have hu : a (i % m) ≠ 0 := ne_zero_of_detC_pos huw
      rw [div_self hu, arg_one, zero_add]
    · have huv := hleft d hd (Nat.le_succ d)
      exact (arg_div_add huv huw hvw).symm

/-! ### Certificates by arcs -/

/-- Sums over a full period of `j ↦ f (j % m)` do not depend on the start. -/
lemma sum_range_mod_shift (f : ℕ → ℝ) (m s : ℕ) :
    ∑ k ∈ Finset.range m, f ((s + k) % m) = ∑ k ∈ Finset.range m, f k := by
  induction s with
  | zero =>
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [zero_add, Nat.mod_eq_of_lt (Finset.mem_range.mp hk)]
  | succ s ih =>
    rw [← ih]
    have h1 := Finset.sum_range_succ (fun k => f ((s + k) % m)) m
    have h2 := Finset.sum_range_succ' (fun k => f ((s + k) % m)) m
    have e : ∀ k, s + 1 + k = s + (k + 1) := fun k => by ring
    simp only [e]
    have hm : f ((s + m) % m) = f ((s + 0) % m) := by rw [Nat.add_mod_right, add_zero]
    linarith

/-- A cover of the cycle `s₀ + i, …, s₀ + m` (positions mod `m`) by arcs `(d, c)` (length `d ≥ 1`, cost `c`): along
each arc all points lie strictly left of its first point; cost `1` requires an acute angle between the endpoints,
cost `2` nothing more. -/
def ArcCover (a : ℕ → ℂ) (m s₀ : ℕ) : ℕ → List (ℕ × ℕ) → Prop
  | i, [] => i = m
  | i, (d, c) :: rest =>
      1 ≤ d ∧ i + d ≤ m ∧
        (∀ d', 1 ≤ d' → d' ≤ d → 0 < detC (a ((s₀ + i) % m)) (a ((s₀ + i + d') % m))) ∧
        (c = 1 ∧ 0 < dotC (a ((s₀ + i) % m)) (a ((s₀ + i + d) % m)) ∨ c = 2) ∧
        ArcCover a m s₀ (i + d) rest

lemma arcs_turn_le {a : ℕ → ℂ} {m : ℕ} (hm : 0 < m) (s₀ : ℕ)
    (hcons : ∀ j < m, 0 < detC (a j) (a (nxt m j))) :
    ∀ (arcs : List (ℕ × ℕ)) (i : ℕ), ArcCover a m s₀ i arcs →
      ∑ k ∈ Finset.range (m - i), turn a m ((s₀ + i + k) % m) ≤ (arcs.map Prod.snd).sum * (Real.pi / 2) := by
  intro arcs
  induction arcs with
  | nil =>
    intro i hi
    simp only [ArcCover] at hi
    subst hi
    simp
  | cons dc rest ih =>
    obtain ⟨d, c⟩ := dc
    intro i hi
    obtain ⟨hd1, hdm, hleft, hcost, hrest⟩ := hi
    have hsplit : m - i = d + (m - (i + d)) := by omega
    rw [hsplit, Finset.sum_range_add]
    have harc : ∑ k ∈ Finset.range d, turn a m ((s₀ + i + k) % m) =
        arg (a ((s₀ + i + d) % m) / a ((s₀ + i) % m)) := by
      apply sum_turn_arc (s₀ + i) d hleft
      intro d' _
      have h := hcons ((s₀ + i + d') % m) (Nat.mod_lt _ hm)
      simpa only [nxt, Nat.mod_add_mod] using h
    have hrest' := ih (i + d) hrest
    have e : ∀ k, s₀ + i + (d + k) = s₀ + (i + d) + k := fun k => by ring
    simp only [e]
    rw [harc]
    have hpi := Real.pi_pos
    have hu : a ((s₀ + i) % m) ≠ 0 := ne_zero_of_detC_pos (hleft d hd1 le_rfl)
    have hmem := turn_mem hu (hleft d hd1 le_rfl)
    have hc : arg (a ((s₀ + i + d) % m) / a ((s₀ + i) % m)) ≤ c * (Real.pi / 2) := by
      rcases hcost with ⟨rfl, hdot⟩ | rfl
      · have hre : 0 < (a ((s₀ + i + d) % m) / a ((s₀ + i) % m)).re := by
          rw [div_re_eq]; exact div_pos hdot (Complex.normSq_pos.mpr hu)
        have := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)
        push_cast; linarith
      · push_cast; linarith [hmem.2]
    simp only [List.map_cons, List.sum_cons]
    have e2 : ((c + (rest.map Prod.snd).sum : ℕ) : ℝ) * (Real.pi / 2) =
        (c : ℝ) * (Real.pi / 2) + ((rest.map Prod.snd).sum : ℝ) * (Real.pi / 2) := by push_cast; ring
    rw [e2]
    linarith

/-- **Winding certificate.** Positive turns and a cover of the cycle by arcs of total cost at most `7` give total
turning below `4π` (so exactly `2π`, by `LebesgueCover.turnSum_eq_two_pi`). -/
theorem turnSum_lt_of_arcs {a : ℕ → ℂ} {m : ℕ} (hm : 0 < m) (s₀ : ℕ)
    (hcons : ∀ j < m, 0 < detC (a j) (a (nxt m j))) (arcs : List (ℕ × ℕ)) (harcs : ArcCover a m s₀ 0 arcs)
    (hcost : (arcs.map Prod.snd).sum ≤ 7) : turnSum a m < 4 * Real.pi := by
  have h := arcs_turn_le hm s₀ hcons arcs 0 harcs
  simp only [Nat.sub_zero, add_zero] at h
  have hshift : turnSum a m = ∑ k ∈ Finset.range m, turn a m ((s₀ + k) % m) := by
    unfold turnSum
    exact (sum_range_mod_shift (fun j => turn a m j) m s₀).symm
  have hc : ((arcs.map Prod.snd).sum : ℝ) ≤ 7 := by exact_mod_cast hcost
  have hpi := Real.pi_pos
  rw [hshift]
  nlinarith

end Worm.Geom
