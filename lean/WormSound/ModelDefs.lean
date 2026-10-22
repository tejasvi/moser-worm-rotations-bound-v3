import WormSound.IvSound.Ctx
import WormSound.Quad

/-!
# The area of a vertex list as a quadratic in the box variables (definitions)

On a box with centre angles `θ_c` and translations `t_c` (`centreAngle`, `centreTrans`), the position of a vertex `g`
of body `b ≥ 1` at the placement `x` is `X_g + Δt_b + C_b R_g + S_b (i R_g)`, where `X_g = posC g` (the position at the
centre), `R_g = e^{iθ_c} q g`, `Δt_b = t_b - t_c`, `C_b = cos(θ_b - θ_c) - 1`, `S_b = sin(θ_b - θ_c)`. In the variables
`y_{4(b-1)+j}` (`j = 0, 1, 2, 3`: `Re Δt_b`, `Im Δt_b`, `C_b`, `S_b`; `yOf`) the shoelace area of a cyclic vertex list
is exactly the quadratic `quadF` with the coefficients `F0R`, `gR`, `MR`: the real counterparts of `WormCore.model`
(`lcol`, `gTerm`, `MTerm`, `cycPairs`).
-/

noncomputable section

namespace WormCore.Sound

open WormCore.IvSound Complex Finset Worm.Geom

variable (F : Fam) (q : ℕ → ℂ) (lo hi : Array Int)

/-- The real `RQ`: `e^{iθ_c} q g` for a moving body, `q g` for body `0`. -/
def rqR (g : ℕ) : ℂ :=
  if F.body[g]! = 0 then q g else exp (centreAngle lo hi F.body[g]! * I) * q g

/-- The real `lcol`: the coefficient of the variable `4(b-1) + k` in the position of a vertex of body `b`. -/
def lcolR (g k : ℕ) : ℂ :=
  match k with
  | 0 => 1
  | 1 => I
  | 2 => rqR F q lo hi g
  | _ => I * rqR F q lo hi g

/-- The real `gTerm`. -/
def gTermR (a b k : ℕ) : ℝ :=
  (if F.body[b]! ≠ 0 ∧ k / 4 = F.body[b]! - 1 then cross (posC F q lo hi a) (lcolR F q lo hi b (k % 4)) else 0) +
    (if F.body[a]! ≠ 0 ∧ k / 4 = F.body[a]! - 1 then cross (lcolR F q lo hi a (k % 4)) (posC F q lo hi b) else 0)

/-- The real `MTerm`. -/
def MTermR (a b k l : ℕ) : ℝ :=
  if F.body[a]! ≠ 0 ∧ F.body[b]! ≠ 0 ∧ k / 4 = F.body[a]! - 1 ∧ l / 4 = F.body[b]! - 1 then
    cross (lcolR F q lo hi a (k % 4)) (lcolR F q lo hi b (l % 4))
  else 0

/-- The real coefficients of `WormCore.model`. -/
def F0R (l : List ℕ) : ℝ := ((cycPairs l).map fun p => cross (posC F q lo hi p.1) (posC F q lo hi p.2)).sum / 2

def gR (l : List ℕ) (k : ℕ) : ℝ := ((cycPairs l).map fun p => gTermR F q lo hi p.1 p.2 k).sum / 2

def MR (l : List ℕ) (k k' : ℕ) : ℝ := ((cycPairs l).map fun p => MTermR F q lo hi p.1 p.2 k k').sum / 2

/-- The box variables of the placement `x`. -/
def yOf (x : Fin 12 → ℝ) (k : ℕ) : ℝ :=
  match k % 4 with
  | 0 => (bodyTrans x (k / 4 + 1) - centreTrans lo hi (k / 4 + 1)).re
  | 1 => (bodyTrans x (k / 4 + 1) - centreTrans lo hi (k / 4 + 1)).im
  | 2 => Real.cos (bodyAngle x (k / 4 + 1) - centreAngle lo hi (k / 4 + 1)) - 1
  | _ => Real.sin (bodyAngle x (k / 4 + 1) - centreAngle lo hi (k / 4 + 1))

end WormCore.Sound
