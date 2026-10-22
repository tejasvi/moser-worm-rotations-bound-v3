import WormSound.Defs
import WormSound.IvSound.Struct

/-!
# Validity of the structures (statements)

`stOK_valid`: a structure that passes the interval test `stOK` on a box is valid (`StValid`) at every configuration of
the box. For a fan the winding is certified at the box centre (`windCost`, `turning_lt_of_windCost`) and carried to
the whole box by continuity (`turning_const`), since the consecutive turns stay positive on the box.
-/

namespace WormCore.Sound

open Worm.Geom

/-- **Winding certificate.** If the consecutive turns around `z` are positive, `Pb i d` certifies
`det(a_i, a_{i+d}) > 0` and `Db i d` certifies `⟨a_i, a_{i+d}⟩ > 0` (`a_j = pt P j - z`), a partition of cost at most
`7` bounds the total turning by `7π/2 < 4π`. -/
theorem turning_lt_of_windCost (P : List ℂ) (z : ℂ) (h3 : 3 ≤ P.length)
    (hdet : ∀ j < P.length, 0 < cross (pt P j - z) (pt P (j + 1) - z)) (Pb Db : ℕ → ℕ → Bool)
    (hP : ∀ i < P.length, ∀ d, Pb i d = true → 0 < cross (pt P i - z) (pt P (i + d) - z))
    (hD : ∀ i < P.length, ∀ d, Db i d = true →
      0 < (pt P i - z).re * (pt P (i + d) - z).re + (pt P i - z).im * (pt P (i + d) - z).im)
    (s0 : ℕ) (hw : windCost P.length Pb Db s0 ≤ 7) :
    turning P z < 4 * Real.pi := by
  exact WormCore.IvSound.turning_lt_of_windCost' P z h3 hdet Pb Db hP hD s0 hw

/-- **Continuity.** On a preconnected set where the vertices move continuously and every turn around `z` is positive,
the total turning is constant; so a bound `< 4π` at one point holds on the whole set. -/
theorem turning_const {S : Set (Fin 12 → ℝ)} (hS : IsPreconnected S) (P : (Fin 12 → ℝ) → List ℂ) (m : ℕ)
    (hm : ∀ x, (P x).length = m) (hc : ∀ j < m, ContinuousOn (fun x => (P x).getD j 0) S) (z : ℂ)
    (hdet : ∀ x ∈ S, ∀ j < m, 0 < cross (pt (P x) j - z) (pt (P x) (j + 1) - z)) {x0 : Fin 12 → ℝ}
    (hx0 : x0 ∈ S) (h0 : turning (P x0) z < 4 * Real.pi) :
    ∀ x ∈ S, turning (P x) z < 4 * Real.pi := by
  exact WormCore.IvSound.turning_const' hS P m hm hc z hdet hx0 h0

/-- **Validity (interval soundness).** A structure that passes `stOK` on a box is valid at every configuration of
the box. -/
theorem stOK_valid (arcs : List Arc) (gid : List (Nat × Nat)) (harcs : ArcsOK arcs) (hk : arcs.length = 5)
    (hgid : ∀ g ∈ gid, g.1 < 5) (maxsmall : Nat) (hms : maxsmall ≤ 4) (lo hi : Array Int)
    (hrange : AngleRange lo hi) (st : St) (h : stOK (mkCtx (mkFam arcs gid) lo hi) maxsmall st = true)
    (x : Fin 12 → ℝ) (hx : InBox lo hi x) :
    StValid (st.verts.map (place arcs gid x)) st := by
  have hF := WormCore.IvSound.famSpec_mkFam harcs hk hgid
  have hB := WormCore.IvSound.boxOK_of hrange hx
  have hv := WormCore.IvSound.stOK_valid'' hF hB hms st h hx
  have e : st.verts.map (place arcs gid x) =
      st.verts.map (WormCore.IvSound.pos (mkFam arcs gid) (qReal arcs gid) x) :=
    List.map_congr_left fun g _ => WormCore.IvSound.place_eq_pos x g
  rw [e]
  exact hv

end WormCore.Sound
