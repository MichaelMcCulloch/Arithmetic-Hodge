import ArithmeticHodge.Analysis.MultiplicativeWeilFiniteXiContour
import ArithmeticHodge.Analysis.XiRectangleContourData

set_option autoImplicit false

open Complex Set
open scoped Interval Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

theorem bombieriFiniteOuterXiContour_of_horizontal_pair_scratch
    (f : BombieriTest) {sigmaLower sigmaUpper T : ℝ}
    (hlower : sigmaLower < 0) (hupper : 1 < sigmaUpper) (hT : 0 < T)
    (htop : ∀ σ ∈ Set.Icc sigmaLower sigmaUpper,
      xiFunction (σ + T * I) ≠ 0)
    (hbottom : ∀ σ ∈ Set.Icc sigmaLower sigmaUpper,
      xiFunction (σ - T * I) ≠ 0) :
    ∑ rho ∈ xiZerosInRectangle 0 1 (-T) T,
        (xiZeroMultiplicity rho : ℂ) * mellin (f : ℝ → ℂ) rho =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        rectIntegral
          (fun s ↦ mellin (f : ℝ → ℂ) s *
            (deriv riemannZeta s / riemannZeta s +
              1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
                Complex.digamma (s / 2) / 2))
          ((sigmaLower : ℂ) - (T : ℂ) * I)
          ((sigmaUpper : ℂ) + (T : ℂ) * I) := by
  let z : ℂ := (sigmaLower : ℂ) - (T : ℂ) * I
  let w : ℂ := (sigmaUpper : ℂ) + (T : ℂ) * I
  have hrew : z.re < w.re := by
    simp only [z, w, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      zero_mul, mul_zero, sub_zero, add_re, add_zero]
    linarith
  have himw : z.im < w.im := by
    simp only [z, w, sub_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      zero_mul, mul_one, zero_sub, add_im, zero_add]
    linarith
  have hboundary : ∀ s ∈ xiZeroRectangle z.re w.re z.im w.im,
      s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im →
      xiFunction s ≠ 0 := by
    intro s hs hedge hzero
    have hsrect : s ∈ xiZeroRectangle sigmaLower sigmaUpper (-T) T := by
      simpa [z, w] using hs
    have hcoords := hsrect
    rw [xiZeroRectangle, mem_reProdIm] at hcoords
    have hedge' : s.re = sigmaLower ∨ s.re = sigmaUpper ∨
        s.im = -T ∨ s.im = T := by
      simpa [z, w] using hedge
    have hre := xiFunction_zero_re hzero
    rcases hedge' with hreL | hreU | himL | himU
    · linarith
    · linarith
    · have heq : (s.re : ℂ) - T * I = s := by
        apply Complex.ext
        · simp
        · simp [← himL]
      exact hbottom s.re hcoords.1 (by simpa only [heq] using hzero)
    · have heq : (s.re : ℂ) + T * I = s := by
        apply Complex.ext
        · simp
        · simp [himU]
      exact htop s.re hcoords.1 (by simpa only [heq] using hzero)
  have h := bombieriFiniteXiContour_of_boundary_zero_free
    f (z := z) (w := w) hrew himw hboundary
  have h' :
      ∑ rho ∈ xiZerosInRectangle sigmaLower sigmaUpper (-T) T,
          (xiZeroMultiplicity rho : ℂ) * mellin (f : ℝ → ℂ) rho =
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          rectIntegral
            (fun s ↦ mellin (f : ℝ → ℂ) s *
              (deriv riemannZeta s / riemannZeta s +
                1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
                  Complex.digamma (s / 2) / 2)) z w := by
    simpa [z, w] using h
  rw [xiZerosInRectangle_outer_eq_critical hlower.le hupper.le] at h'
  exact h'

#print axioms bombieriFiniteOuterXiContour_of_horizontal_pair_scratch

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
