import WormSound.ModelDefs
import WormSound.ModelProof.Main

/-!
# The area of a vertex list as a quadratic in the box variables (statements)

The definitions are in `WormSound.ModelDefs`.
-/

noncomputable section

namespace WormCore.Sound

open WormCore.IvSound Complex Finset Worm.Geom

variable (F : Fam) (q : ℕ → ℂ) (lo hi : Array Int)

/-- **Model identity.** The shoelace area of the placed cyclic list is the quadratic with the real coefficients. -/
theorem shoelace_eq_quadF (hF : FamSpec F q) (hk : F.k = 4) (l : List ℕ) (hl : ∀ g ∈ l, g < F.body.size)
    (x : Fin 12 → ℝ) :
    shoelace (l.map (pos F q x)) = quadF (range 16) (F0R F q lo hi l) (gR F q lo hi l) (MR F q lo hi l) (yOf lo hi x) := by
  exact ModelProof.shoelace_eq_quadF' F q lo hi hF hk l hl x

/-- The identity terms vanish: `C² + S² + 2C = 0`. -/
theorem yOf_circle (x : Fin 12 → ℝ) (b : ℕ) :
    yOf lo hi x (4 * b + 2) ^ 2 + yOf lo hi x (4 * b + 3) ^ 2 + 2 * yOf lo hi x (4 * b + 2) = 0 := by
  exact ModelProof.yOf_circle' lo hi x b

/-- The variables of a placement in the box lie in the variable box of `leafBound` (`y0At ± wAt`). -/
theorem yOf_mem_box (hF : FamSpec F q) (hk : F.k = 4) (hB : BoxOK lo hi) (x : Fin 12 → ℝ) (hx : InBox lo hi x)
    (k : ℕ) (hk16 : k < 16) :
    |yOf lo hi x k - (y0At (mkCtx F lo hi) k : ℝ) / 2 ^ MoserWorm.dfxS| ≤ (wAt (mkCtx F lo hi) k : ℝ) / 2 ^ MoserWorm.dfxS := by
  exact ModelProof.yOf_mem_box' F q lo hi hF hk hB x hx k hk16

end WormCore.Sound
