import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLowSchur

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseStructuralLowData

noncomputable section

open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil

private theorem integral_quartic
    (a₀ a₁ a₂ a₃ a₄ l r : ℝ) :
    (∫ x : ℝ in l..r,
        a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
          (a₃ * x ^ 3 + a₄ * x ^ 4)))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 +
        a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- Exact centered correlation of the constant structural low mode. -/
theorem factorTwoCenteredCorrelationBilinear_p0_p0 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredEvenP0 centeredEvenP0 t =
      2 - t := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation centeredEvenP0
  simp
  ring

/-- Exact centered correlation between the constant and quadratic structural
low modes. -/
theorem factorTwoCenteredCorrelationBilinear_p0_p2 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredEvenP0 centeredEvenP2 t =
      -t * (t - 2) * (t - 1) / 2 := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation centeredEvenP0 centeredEvenP2
  simp only [one_mul, mul_one]
  rw [show (fun x : ℝ ↦ (3 * x ^ 2 - 1) / 2) =
      fun x ↦ (-1 / 2 : ℝ) * x ^ 0 + (0 * x ^ 1 +
        ((3 / 2 : ℝ) * x ^ 2 + (0 * x ^ 3 + 0 * x ^ 4))) by
    funext x
    ring,
    integral_quartic]
  rw [show (fun x : ℝ ↦ (3 * (t + x) ^ 2 - 1) / 2) =
      fun x ↦ ((3 * t ^ 2 - 1) / 2 : ℝ) * x ^ 0 +
        (3 * t * x ^ 1 + ((3 / 2 : ℝ) * x ^ 2 +
          (0 * x ^ 3 + 0 * x ^ 4))) by
    funext x
    ring,
    integral_quartic]
  ring

/-- Exact centered autocorrelation of the quadratic structural low mode. -/
theorem factorTwoCenteredCorrelationBilinear_p2_p2 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredEvenP2 centeredEvenP2 t =
      -(t - 2) *
        (3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40 := by
  rw [factorTwoCenteredCorrelationBilinear_self]
  unfold CenteredEndpointCorrelation.centeredEndpointCorrelation
    centeredEvenP2
  rw [show (fun x : ℝ ↦
      (3 * (t + x) ^ 2 - 1) / 2 * ((3 * x ^ 2 - 1) / 2)) =
      fun x ↦ ((1 / 4 : ℝ) - 3 * t ^ 2 / 4) * x ^ 0 +
        ((-3 * t / 2 : ℝ) * x ^ 1 +
          ((9 * t ^ 2 / 4 - 3 / 2 : ℝ) * x ^ 2 +
            ((9 * t / 2 : ℝ) * x ^ 3 +
              (9 / 4 : ℝ) * x ^ 4))) by
    funext x
    ring,
    integral_quartic]
  ring

/-! ## Exact one-dimensional perturbation entries -/

/-- Exact integral formula for the constant-mode perturbation entry. -/
theorem factorTwoCenteredSymmetricPerturbation_p0_eq :
    factorTwoCenteredSymmetricPerturbation centeredEvenP0 =
      yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoSymmetricWeight (yoshidaEndpointA * t) * (2 - t)) -
        (Real.log 2 / Real.sqrt 2) * 2 -
        (Real.log 3 / Real.sqrt 3) *
          (2 - factorTwoPrimeShift / yoshidaEndpointA) := by
  rw [← factorTwoCenteredSymmetricPerturbationBilinear_self]
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_p0_p0]
  ring

/-- Exact integral formula for the mixed constant/quadratic perturbation
entry. -/
theorem factorTwoCenteredSymmetricPerturbationBilinear_p0_p2_eq :
    factorTwoCenteredSymmetricPerturbationBilinear
        centeredEvenP0 centeredEvenP2 =
      yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoSymmetricWeight (yoshidaEndpointA * t) *
              (-t * (t - 2) * (t - 1) / 2)) -
        (Real.log 3 / Real.sqrt 3) *
          (-(factorTwoPrimeShift / yoshidaEndpointA) *
            (factorTwoPrimeShift / yoshidaEndpointA - 2) *
            (factorTwoPrimeShift / yoshidaEndpointA - 1) / 2) := by
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_p0_p2]
  ring

/-- Exact integral formula for the quadratic-mode perturbation entry. -/
theorem factorTwoCenteredSymmetricPerturbation_p2_eq :
    factorTwoCenteredSymmetricPerturbation centeredEvenP2 =
      yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoSymmetricWeight (yoshidaEndpointA * t) *
              (-(t - 2) *
                (3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) /
                40)) -
        (Real.log 2 / Real.sqrt 2) * (2 / 5) -
        (Real.log 3 / Real.sqrt 3) *
          (-(factorTwoPrimeShift / yoshidaEndpointA - 2) *
            (3 * (factorTwoPrimeShift / yoshidaEndpointA) ^ 4 +
              6 * (factorTwoPrimeShift / yoshidaEndpointA) ^ 3 -
              8 * (factorTwoPrimeShift / yoshidaEndpointA) ^ 2 -
              16 * (factorTwoPrimeShift / yoshidaEndpointA) + 8) / 40) := by
  rw [← factorTwoCenteredSymmetricPerturbationBilinear_self]
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_p2_p2]
  norm_num

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseStructuralLowData
