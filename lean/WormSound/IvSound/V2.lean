import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import MoserWorm.Common.Interval.Sound
import MoserWorm.Common.Interval.Rational
import WormCore.Check

/-!
# Soundness of the planar interval vectors of the worm checker

`V2.Mem v z`: the interval vector `v` (Keller's dyadic intervals `MoserWorm.DIval`, scale `2⁻⁵⁶`) encloses the complex
number `z`, coordinatewise. Each operation of `WormCore.V2` is sound: it encloses the result of the exact operation on
enclosed arguments (`det` is `re a · im b − im a · re b`, `rot s c` is multiplication by `e^{iθ}` when `s`, `c`
enclose `sin θ`, `cos θ`, `J` is multiplication by `i`, `norm` is the modulus).
-/

open MoserWorm

namespace WormCore

namespace V2

/-- `v` encloses `z` coordinatewise. -/
def Mem (v : V2) (z : ℂ) : Prop := z.re ∈ v.1 ∧ z.im ∈ v.2

theorem mem_zero : Mem zero 0 := by
  refine ⟨?_, ?_⟩ <;> simpa [zero, DIval.pt] using DIval.mem_pt 0

theorem mem_add {u v : V2} {z w : ℂ} (hz : Mem u z) (hw : Mem v w) : Mem (add u v) (z + w) := by
  refine ⟨?_, ?_⟩
  · show (z + w).re ∈ u.1.add v.1
    rw [Complex.add_re]; exact DIval.mem_add hz.1 hw.1
  · show (z + w).im ∈ u.2.add v.2
    rw [Complex.add_im]; exact DIval.mem_add hz.2 hw.2

theorem mem_sub {u v : V2} {z w : ℂ} (hz : Mem u z) (hw : Mem v w) : Mem (sub u v) (z - w) := by
  refine ⟨?_, ?_⟩
  · show (z - w).re ∈ u.1.sub v.1
    rw [Complex.sub_re]; exact DIval.mem_sub hz.1 hw.1
  · show (z - w).im ∈ u.2.sub v.2
    rw [Complex.sub_im]; exact DIval.mem_sub hz.2 hw.2

theorem mem_smul {c : DIval} {u : V2} {r : ℝ} {z : ℂ} (hr : r ∈ c) (hz : Mem u z) : Mem (smul c u) (r * z) := by
  refine ⟨?_, ?_⟩
  · show (r * z).re ∈ c.mul u.1
    rw [Complex.re_ofReal_mul]; exact DIval.mem_mul hr hz.1
  · show (r * z).im ∈ c.mul u.2
    rw [Complex.im_ofReal_mul]; exact DIval.mem_mul hr hz.2

theorem mem_J {u : V2} {z : ℂ} (hz : Mem u z) : Mem (J u) (Complex.I * z) := by
  refine ⟨?_, ?_⟩
  · show (Complex.I * z).re ∈ u.2.neg
    rw [Complex.I_mul_re]; exact DIval.mem_neg hz.2
  · show (Complex.I * z).im ∈ u.1
    rw [Complex.I_mul_im]; exact hz.1

/-- `det` encloses `re z · im w − im z · re w`. -/
theorem mem_det {u v : V2} {z w : ℂ} (hz : Mem u z) (hw : Mem v w) :
    (z.re * w.im - z.im * w.re) ∈ det u v :=
  DIval.mem_sub (DIval.mem_mul hz.1 hw.2) (DIval.mem_mul hz.2 hw.1)

/-- `norm` encloses the modulus. -/
theorem mem_norm {u : V2} {z : ℂ} (hz : Mem u z) : ‖z‖ ∈ norm u := by
  have h := DIval.mem_norm2 hz.1 hz.2
  have e : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; ring
  rw [e]; exact h

/-- `rot s c` encloses the rotation by `θ` when `s` and `c` enclose `sin θ` and `cos θ`. -/
theorem mem_rot {s c : DIval} {u : V2} {θ : ℝ} {z : ℂ} (hs : Real.sin θ ∈ s) (hc : Real.cos θ ∈ c)
    (hz : Mem u z) : Mem (rot s c u) (Complex.exp (θ * Complex.I) * z) := by
  have hre : (Complex.exp (θ * Complex.I) * z).re = Real.cos θ * z.re - Real.sin θ * z.im := by
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have him : (Complex.exp (θ * Complex.I) * z).im = Real.sin θ * z.re + Real.cos θ * z.im := by
    rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]; ring
  refine ⟨?_, ?_⟩
  · rw [hre]; exact DIval.mem_sub (DIval.mem_mul hc hz.1) (DIval.mem_mul hs hz.2)
  · rw [him]; exact DIval.mem_add (DIval.mem_mul hs hz.1) (DIval.mem_mul hc hz.2)

end V2

end WormCore
