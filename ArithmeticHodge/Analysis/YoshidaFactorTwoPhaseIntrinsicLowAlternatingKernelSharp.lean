import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddAffineKernelEstimate
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp

noncomputable section

open YoshidaConstantBounds
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaRegularKernelBound
open YoshidaFactorTwoStructuralConstantBounds

/-!
# Sharp polynomial moments for the intrinsic alternating kernel

The linear model in the baseline module is replaced by the full odd
degree-six Taylor model of the pole-free antisymmetric weight.  All four
intrinsic directions share this one model and its one analytic remainder.
-/

private def sharpWideCoshPolynomial6 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 2 + u ^ 4 / 24 + u ^ 6 / 720

/-- Degree-six model of the scaled pole-free antisymmetric kernel. -/
def intrinsicAlternatingKernelPolynomial6 (t : ℝ) : ℝ :=
  let up := yoshidaEndpointA * (2 + t)
  let um := yoshidaEndpointA * (2 - t)
  yoshidaEndpointA *
    (2 * sharpWideCoshPolynomial6 (up / 2) -
      2 * sharpWideCoshPolynomial6 (um / 2) -
      yoshidaRegularKernelPolynomial6 up +
      yoshidaRegularKernelPolynomial6 um)

def intrinsicAlternatingKernelCoeff1 (a : ℝ) : ℝ :=
  a ^ 2 / 24 + (9 / 4 : ℝ) * a ^ 3 - (7 / 480 : ℝ) * a ^ 4 +
    a ^ 5 / 8 + (31 / 12096 : ℝ) * a ^ 6 +
      (23 / 160 : ℝ) * a ^ 7

def intrinsicAlternatingKernelCoeff3 (a : ℝ) : ℝ :=
  -(7 / 5760 : ℝ) * a ^ 4 + a ^ 5 / 32 +
    (31 / 24192 : ℝ) * a ^ 6 + (23 / 192 : ℝ) * a ^ 7

def intrinsicAlternatingKernelCoeff5 (a : ℝ) : ℝ :=
  (31 / 967680 : ℝ) * a ^ 6 + (23 / 2560 : ℝ) * a ^ 7

theorem intrinsicAlternatingKernelPolynomial6_expansion (t : ℝ) :
    intrinsicAlternatingKernelPolynomial6 t =
      intrinsicAlternatingKernelCoeff1 yoshidaEndpointA * t +
        intrinsicAlternatingKernelCoeff3 yoshidaEndpointA * t ^ 3 +
        intrinsicAlternatingKernelCoeff5 yoshidaEndpointA * t ^ 5 := by
  unfold intrinsicAlternatingKernelPolynomial6 sharpWideCoshPolynomial6
    yoshidaRegularKernelPolynomial6 intrinsicAlternatingKernelCoeff1
    intrinsicAlternatingKernelCoeff3 intrinsicAlternatingKernelCoeff5
  ring

/-- Exact polynomial correction to the baseline linear kernel model. -/
def intrinsicAlternatingPolynomialCorrection (q : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ in 0..2,
    (intrinsicAlternatingKernelPolynomial6 t - t / 10) *
      intrinsicAlternatingCorrelation q t

/-- Remainder after the full degree-six antisymmetric model is retained. -/
def intrinsicAlternatingSharpRegularError (q : ℝ → ℝ) : ℝ :=
  intrinsicAlternatingRegularError q -
    intrinsicAlternatingPolynomialCorrection q

/-- Explicit archimedean model with the polynomial correction restored. -/
def intrinsicAlternatingSharpArchModel (q : ℝ → ℝ) : ℝ :=
  intrinsicAlternatingArchModel q +
    intrinsicAlternatingPolynomialCorrection q

theorem intrinsicAlternatingSharp_decomposition (q : ℝ → ℝ) :
    intrinsicAlternatingRegularError q + intrinsicAlternatingArchModel q =
      intrinsicAlternatingSharpRegularError q +
        intrinsicAlternatingSharpArchModel q := by
  unfold intrinsicAlternatingSharpRegularError
    intrinsicAlternatingSharpArchModel
  ring

theorem intrinsicAlternating01_add_21_eq_sharpModel :
    factorTwoIntrinsicAlternating01 + factorTwoIntrinsicAlternating21 =
      intrinsicAlternatingSharpRegularError intrinsicAlternatingQ01Plus21 +
        intrinsicAlternatingSharpArchModel intrinsicAlternatingQ01Plus21 -
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  calc
    _ = intrinsicAlternatingRegularError intrinsicAlternatingQ01Plus21 +
          intrinsicAlternatingArchModel intrinsicAlternatingQ01Plus21 -
          (Real.log 3 / Real.sqrt 3) *
            intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
              (factorTwoPrimeShift / yoshidaEndpointA) :=
      intrinsicAlternating01_add_21_eq_structuralModel
    _ = _ := by rw [intrinsicAlternatingSharp_decomposition]

theorem intrinsicAlternating01_sub_21_eq_sharpModel :
    factorTwoIntrinsicAlternating01 - factorTwoIntrinsicAlternating21 =
      intrinsicAlternatingSharpRegularError intrinsicAlternatingQ01Minus21 +
        intrinsicAlternatingSharpArchModel intrinsicAlternatingQ01Minus21 -
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  calc
    _ = intrinsicAlternatingRegularError intrinsicAlternatingQ01Minus21 +
          intrinsicAlternatingArchModel intrinsicAlternatingQ01Minus21 -
          (Real.log 3 / Real.sqrt 3) *
            intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
              (factorTwoPrimeShift / yoshidaEndpointA) :=
      intrinsicAlternating01_sub_21_eq_structuralModel
    _ = _ := by rw [intrinsicAlternatingSharp_decomposition]

theorem intrinsicAlternating03_add_23_eq_sharpModel :
    factorTwoIntrinsicAlternating03 + factorTwoIntrinsicAlternating23 =
      intrinsicAlternatingSharpRegularError intrinsicAlternatingQ03Plus23 +
        intrinsicAlternatingSharpArchModel intrinsicAlternatingQ03Plus23 -
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  calc
    _ = intrinsicAlternatingRegularError intrinsicAlternatingQ03Plus23 +
          intrinsicAlternatingArchModel intrinsicAlternatingQ03Plus23 -
          (Real.log 3 / Real.sqrt 3) *
            intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
              (factorTwoPrimeShift / yoshidaEndpointA) :=
      intrinsicAlternating03_add_23_eq_structuralModel
    _ = _ := by rw [intrinsicAlternatingSharp_decomposition]

theorem intrinsicAlternating03_sub_23_eq_sharpModel :
    factorTwoIntrinsicAlternating03 - factorTwoIntrinsicAlternating23 =
      intrinsicAlternatingSharpRegularError intrinsicAlternatingQ03Minus23 +
        intrinsicAlternatingSharpArchModel intrinsicAlternatingQ03Minus23 -
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  calc
    _ = intrinsicAlternatingRegularError intrinsicAlternatingQ03Minus23 +
          intrinsicAlternatingArchModel intrinsicAlternatingQ03Minus23 -
          (Real.log 3 / Real.sqrt 3) *
            intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
              (factorTwoPrimeShift / yoshidaEndpointA) :=
      intrinsicAlternating03_sub_23_eq_structuralModel
    _ = _ := by rw [intrinsicAlternatingSharp_decomposition]

private def polynomialElevenLocal
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ x : ℝ) : ℝ :=
  a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
    (a₃ * x ^ 3 + (a₄ * x ^ 4 + (a₅ * x ^ 5 +
      (a₆ * x ^ 6 + (a₇ * x ^ 7 + (a₈ * x ^ 8 +
        (a₉ * x ^ 9 + (a₁₀ * x ^ 10 + a₁₁ * x ^ 11))))))))))

private theorem integral_polynomial_eleven_local
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ l r : ℝ) :
    (∫ x : ℝ in l..r,
      polynomialElevenLocal a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ x) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 +
        a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 +
        a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 +
        a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 +
        a₉ * (r ^ 10 - l ^ 10) / 10 +
        a₁₀ * (r ^ 11 - l ^ 11) / 11 +
        a₁₁ * (r ^ 12 - l ^ 12) / 12 := by
  unfold polynomialElevenLocal
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem integral_monomial_correlation_q01Plus21_one :
    (∫ t : ℝ in 0..2,
      t * intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21 t) =
        4 / 3 := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
  rw [show (fun t : ℝ ↦
      t * (t * (2 - t) * ((1 / 2 : ℝ) * t + (1 / 4 : ℝ) * t ^ 2))) =
      polynomialElevenLocal 0 0 0 1 0 (-1 / 4) 0 0 0 0 0 0 by
    funext t
    unfold polynomialElevenLocal
    ring,
    integral_polynomial_eleven_local]
  norm_num

private theorem integral_monomial_correlation_q01Plus21_three :
    (∫ t : ℝ in 0..2,
      t ^ 3 * intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21 t) =
        8 / 3 := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
  rw [show (fun t : ℝ ↦
      t ^ 3 * (t * (2 - t) * ((1 / 2 : ℝ) * t + (1 / 4 : ℝ) * t ^ 2))) =
      polynomialElevenLocal 0 0 0 0 0 1 0 (-1 / 4) 0 0 0 0 by
    funext t
    unfold polynomialElevenLocal
    ring,
    integral_polynomial_eleven_local]
  norm_num

private theorem integral_monomial_correlation_q01Plus21_five :
    (∫ t : ℝ in 0..2,
      t ^ 5 * intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21 t) =
        32 / 5 := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
  rw [show (fun t : ℝ ↦
      t ^ 5 * (t * (2 - t) * ((1 / 2 : ℝ) * t + (1 / 4 : ℝ) * t ^ 2))) =
      polynomialElevenLocal 0 0 0 0 0 0 0 1 0 (-1 / 4) 0 0 by
    funext t
    unfold polynomialElevenLocal
    ring,
    integral_polynomial_eleven_local]
  norm_num

private theorem integral_monomial_correlation_q01Minus21_one :
    (∫ t : ℝ in 0..2,
      t * intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21 t) =
        4 / 3 := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
  rw [show (fun t : ℝ ↦
      t * (t * (2 - t) *
        (2 - (1 / 2 : ℝ) * t - (1 / 4 : ℝ) * t ^ 2))) =
      polynomialElevenLocal 0 0 4 (-3) 0 (1 / 4) 0 0 0 0 0 0 by
    funext t
    unfold polynomialElevenLocal
    ring,
    integral_polynomial_eleven_local]
  norm_num

private theorem integral_monomial_correlation_q01Minus21_three :
    (∫ t : ℝ in 0..2,
      t ^ 3 * intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21 t) =
        8 / 5 := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
  rw [show (fun t : ℝ ↦
      t ^ 3 * (t * (2 - t) *
        (2 - (1 / 2 : ℝ) * t - (1 / 4 : ℝ) * t ^ 2))) =
      polynomialElevenLocal 0 0 0 0 4 (-3) 0 (1 / 4) 0 0 0 0 by
    funext t
    unfold polynomialElevenLocal
    ring,
    integral_polynomial_eleven_local]
  norm_num

private theorem integral_monomial_correlation_q01Minus21_five :
    (∫ t : ℝ in 0..2,
      t ^ 5 * intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21 t) =
        96 / 35 := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
  rw [show (fun t : ℝ ↦
      t ^ 5 * (t * (2 - t) *
        (2 - (1 / 2 : ℝ) * t - (1 / 4 : ℝ) * t ^ 2))) =
      polynomialElevenLocal 0 0 0 0 0 0 4 (-3) 0 (1 / 4) 0 0 by
    funext t
    unfold polynomialElevenLocal
    ring,
    integral_polynomial_eleven_local]
  norm_num

private theorem integral_monomial_correlation_q03Plus23_one :
    (∫ t : ℝ in 0..2,
      t * intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23 t) = 0 := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
  rw [show (fun t : ℝ ↦
      t * (t * (2 - t) *
        (2 - (7 / 2 : ℝ) * t + (3 / 4 : ℝ) * t ^ 2 +
          (1 / 4 : ℝ) * t ^ 3 + (1 / 8 : ℝ) * t ^ 4))) =
      polynomialElevenLocal 0 0 4 (-9) 5 (-1 / 4) 0 (-1 / 8) 0 0 0 0 by
    funext t
    unfold polynomialElevenLocal
    ring,
    integral_polynomial_eleven_local]
  norm_num

private theorem integral_monomial_correlation_q03Plus23_three :
    (∫ t : ℝ in 0..2,
      t ^ 3 * intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23 t) =
        8 / 35 := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
  rw [show (fun t : ℝ ↦
      t ^ 3 * (t * (2 - t) *
        (2 - (7 / 2 : ℝ) * t + (3 / 4 : ℝ) * t ^ 2 +
          (1 / 4 : ℝ) * t ^ 3 + (1 / 8 : ℝ) * t ^ 4))) =
      polynomialElevenLocal 0 0 0 0 4 (-9) 5 (-1 / 4) 0 (-1 / 8) 0 0 by
    funext t
    unfold polynomialElevenLocal
    ring,
    integral_polynomial_eleven_local]
  norm_num

private theorem integral_monomial_correlation_q03Plus23_five :
    (∫ t : ℝ in 0..2,
      t ^ 5 * intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23 t) =
        416 / 315 := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
  rw [show (fun t : ℝ ↦
      t ^ 5 * (t * (2 - t) *
        (2 - (7 / 2 : ℝ) * t + (3 / 4 : ℝ) * t ^ 2 +
          (1 / 4 : ℝ) * t ^ 3 + (1 / 8 : ℝ) * t ^ 4))) =
      polynomialElevenLocal 0 0 0 0 0 0 4 (-9) 5 (-1 / 4) 0 (-1 / 8) by
    funext t
    unfold polynomialElevenLocal
    ring,
    integral_polynomial_eleven_local]
  norm_num

private theorem integral_monomial_correlation_q03Minus23_one :
    (∫ t : ℝ in 0..2,
      t * intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23 t) = 0 := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
  rw [show (fun t : ℝ ↦
      t * (t * (2 - t) *
        (-(3 / 2 : ℝ) * t + (7 / 4 : ℝ) * t ^ 2 -
          (1 / 4 : ℝ) * t ^ 3 - (1 / 8 : ℝ) * t ^ 4))) =
      polynomialElevenLocal 0 0 0 (-3) 5 (-9 / 4) 0 (1 / 8) 0 0 0 0 by
    funext t
    unfold polynomialElevenLocal
    ring,
    integral_polynomial_eleven_local]
  norm_num

private theorem integral_monomial_correlation_q03Minus23_three :
    (∫ t : ℝ in 0..2,
      t ^ 3 * intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23 t) =
        8 / 35 := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
  rw [show (fun t : ℝ ↦
      t ^ 3 * (t * (2 - t) *
        (-(3 / 2 : ℝ) * t + (7 / 4 : ℝ) * t ^ 2 -
          (1 / 4 : ℝ) * t ^ 3 - (1 / 8 : ℝ) * t ^ 4))) =
      polynomialElevenLocal 0 0 0 0 0 (-3) 5 (-9 / 4) 0 (1 / 8) 0 0 by
    funext t
    unfold polynomialElevenLocal
    ring,
    integral_polynomial_eleven_local]
  norm_num

private theorem integral_monomial_correlation_q03Minus23_five :
    (∫ t : ℝ in 0..2,
      t ^ 5 * intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23 t) =
        32 / 45 := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
  rw [show (fun t : ℝ ↦
      t ^ 5 * (t * (2 - t) *
        (-(3 / 2 : ℝ) * t + (7 / 4 : ℝ) * t ^ 2 -
          (1 / 4 : ℝ) * t ^ 3 - (1 / 8 : ℝ) * t ^ 4))) =
      polynomialElevenLocal 0 0 0 0 0 0 0 (-3) 5 (-9 / 4) 0 (1 / 8) by
    funext t
    unfold polynomialElevenLocal
    ring,
    integral_polynomial_eleven_local]
  norm_num

private theorem integral_odd_model_mul
    (D : ℝ → ℝ) (hD : Continuous D) (d₁ d₃ d₅ : ℝ) :
    (∫ t : ℝ in 0..2, (d₁ * t + d₃ * t ^ 3 + d₅ * t ^ 5) * D t) =
      d₁ * (∫ t : ℝ in 0..2, t * D t) +
        d₃ * (∫ t : ℝ in 0..2, t ^ 3 * D t) +
          d₅ * (∫ t : ℝ in 0..2, t ^ 5 * D t) := by
  rw [show (fun t : ℝ ↦ (d₁ * t + d₃ * t ^ 3 + d₅ * t ^ 5) * D t) =
      fun t ↦ d₁ * (t * D t) +
        (d₃ * (t ^ 3 * D t) + d₅ * (t ^ 5 * D t)) by
    funext t
    ring]
  rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2),
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_const_mul]
  ring

private theorem intrinsicAlternatingPolynomialCorrection_eq_moments
    (q : ℝ → ℝ) (hq : Continuous q) :
    intrinsicAlternatingPolynomialCorrection q =
      (intrinsicAlternatingKernelCoeff1 yoshidaEndpointA - 1 / 10) *
          (∫ t : ℝ in 0..2, t * intrinsicAlternatingCorrelation q t) +
        intrinsicAlternatingKernelCoeff3 yoshidaEndpointA *
          (∫ t : ℝ in 0..2, t ^ 3 * intrinsicAlternatingCorrelation q t) +
        intrinsicAlternatingKernelCoeff5 yoshidaEndpointA *
          (∫ t : ℝ in 0..2, t ^ 5 * intrinsicAlternatingCorrelation q t) := by
  unfold intrinsicAlternatingPolynomialCorrection
  rw [show (fun t : ℝ ↦
      (intrinsicAlternatingKernelPolynomial6 t - t / 10) *
        intrinsicAlternatingCorrelation q t) =
      fun t ↦
        ((intrinsicAlternatingKernelCoeff1 yoshidaEndpointA - 1 / 10) * t +
          intrinsicAlternatingKernelCoeff3 yoshidaEndpointA * t ^ 3 +
          intrinsicAlternatingKernelCoeff5 yoshidaEndpointA * t ^ 5) *
            intrinsicAlternatingCorrelation q t by
    funext t
    rw [intrinsicAlternatingKernelPolynomial6_expansion]
    ring]
  apply integral_odd_model_mul
  unfold intrinsicAlternatingCorrelation
  fun_prop

theorem intrinsicAlternatingPolynomialCorrection_q01Plus21 :
    intrinsicAlternatingPolynomialCorrection intrinsicAlternatingQ01Plus21 =
      (4 / 3 : ℝ) *
          (intrinsicAlternatingKernelCoeff1 yoshidaEndpointA - 1 / 10) +
        (8 / 3 : ℝ) * intrinsicAlternatingKernelCoeff3 yoshidaEndpointA +
        (32 / 5 : ℝ) * intrinsicAlternatingKernelCoeff5 yoshidaEndpointA := by
  rw [intrinsicAlternatingPolynomialCorrection_eq_moments]
  · rw [integral_monomial_correlation_q01Plus21_one,
      integral_monomial_correlation_q01Plus21_three,
      integral_monomial_correlation_q01Plus21_five]
    ring
  · unfold intrinsicAlternatingQ01Plus21
    fun_prop

theorem intrinsicAlternatingPolynomialCorrection_q01Minus21 :
    intrinsicAlternatingPolynomialCorrection intrinsicAlternatingQ01Minus21 =
      (4 / 3 : ℝ) *
          (intrinsicAlternatingKernelCoeff1 yoshidaEndpointA - 1 / 10) +
        (8 / 5 : ℝ) * intrinsicAlternatingKernelCoeff3 yoshidaEndpointA +
        (96 / 35 : ℝ) * intrinsicAlternatingKernelCoeff5 yoshidaEndpointA := by
  rw [intrinsicAlternatingPolynomialCorrection_eq_moments]
  · rw [integral_monomial_correlation_q01Minus21_one,
      integral_monomial_correlation_q01Minus21_three,
      integral_monomial_correlation_q01Minus21_five]
    ring
  · unfold intrinsicAlternatingQ01Minus21
    fun_prop

theorem intrinsicAlternatingPolynomialCorrection_q03Plus23 :
    intrinsicAlternatingPolynomialCorrection intrinsicAlternatingQ03Plus23 =
      (8 / 35 : ℝ) * intrinsicAlternatingKernelCoeff3 yoshidaEndpointA +
        (416 / 315 : ℝ) * intrinsicAlternatingKernelCoeff5 yoshidaEndpointA := by
  rw [intrinsicAlternatingPolynomialCorrection_eq_moments]
  · rw [integral_monomial_correlation_q03Plus23_one,
      integral_monomial_correlation_q03Plus23_three,
      integral_monomial_correlation_q03Plus23_five]
    ring
  · unfold intrinsicAlternatingQ03Plus23
    fun_prop

theorem intrinsicAlternatingPolynomialCorrection_q03Minus23 :
    intrinsicAlternatingPolynomialCorrection intrinsicAlternatingQ03Minus23 =
      (8 / 35 : ℝ) * intrinsicAlternatingKernelCoeff3 yoshidaEndpointA +
        (32 / 45 : ℝ) * intrinsicAlternatingKernelCoeff5 yoshidaEndpointA := by
  rw [intrinsicAlternatingPolynomialCorrection_eq_moments]
  · rw [integral_monomial_correlation_q03Minus23_one,
      integral_monomial_correlation_q03Minus23_three,
      integral_monomial_correlation_q03Minus23_five]
    ring
  · unfold intrinsicAlternatingQ03Minus23
    fun_prop

private theorem measurable_yoshidaRegularKernel_sharp :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem measurable_factorTwoCenteredAntisymmetricRegularWeight_sharp :
    Measurable factorTwoCenteredAntisymmetricRegularWeight := by
  unfold factorTwoCenteredAntisymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).sub
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel_sharp.comp (by fun_prop))).add
        (measurable_yoshidaRegularKernel_sharp.comp (by fun_prop))

private theorem intervalIntegrable_intrinsicAlternatingLinearError_sharp
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦
        (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          t / 10) * C t) volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      t / 10) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 1000 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact ((measurable_const.mul
      measurable_factorTwoCenteredAntisymmetricRegularWeight_sharp).sub
        (measurable_id.div_const 10)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hk :=
      abs_yoshidaEndpointA_mul_factorTwoCenteredAntisymmetricRegularWeight_sub_linear_le_one_thousand
        ht.1.le ht.2
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

private theorem intervalIntegrable_intrinsicAlternatingPolynomialCorrection
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦
        (intrinsicAlternatingKernelPolynomial6 t - t / 10) * C t)
      volume 0 2 := by
  apply Continuous.intervalIntegrable
  · rw [show (fun t : ℝ ↦
        (intrinsicAlternatingKernelPolynomial6 t - t / 10) * C t) =
      fun t ↦
        ((intrinsicAlternatingKernelCoeff1 yoshidaEndpointA - 1 / 10) * t +
          intrinsicAlternatingKernelCoeff3 yoshidaEndpointA * t ^ 3 +
          intrinsicAlternatingKernelCoeff5 yoshidaEndpointA * t ^ 5) * C t by
      funext t
      rw [intrinsicAlternatingKernelPolynomial6_expansion]
      ring]
    fun_prop

/-- The sharp error really is the integral of the residual after subtracting
the common degree-six kernel polynomial. -/
theorem intrinsicAlternatingSharpRegularError_eq_integral
    (q : ℝ → ℝ) (hq : Continuous q) :
    intrinsicAlternatingSharpRegularError q =
      ∫ t : ℝ in 0..2,
        (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          intrinsicAlternatingKernelPolynomial6 t) *
            intrinsicAlternatingCorrelation q t := by
  let C : ℝ → ℝ := intrinsicAlternatingCorrelation q
  have hC : Continuous C := by
    dsimp only [C]
    unfold intrinsicAlternatingCorrelation
    fun_prop
  have hlinear := intervalIntegrable_intrinsicAlternatingLinearError_sharp C hC
  have hpolynomial :=
    intervalIntegrable_intrinsicAlternatingPolynomialCorrection C hC
  unfold intrinsicAlternatingSharpRegularError intrinsicAlternatingRegularError
    intrinsicAlternatingPolynomialCorrection
  rw [← intervalIntegral.integral_sub hlinear hpolynomial]
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only [C]
  ring

/-! ## A global analytic envelope for the sharp residual -/

private def sharpWideCoshUpper8 (u : ℝ) : ℝ :=
  sharpWideCoshPolynomial6 u + (4 / 3 : ℝ) * u ^ 8 / 40320

private def sharpWideSinhDivPolynomial6 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 6 + u ^ 4 / 120 + u ^ 6 / 5040

private def sharpWideSinhDivUpper8 (u : ℝ) : ℝ :=
  sharpWideSinhDivPolynomial6 u + (4 / 3 : ℝ) * u ^ 8 / 362880

private def sharpWideSechPolynomial6 (u : ℝ) : ℝ :=
  1 - u ^ 2 / 2 + 5 * u ^ 4 / 24 - 61 * u ^ 6 / 720

private def sharpWideCschRegularPolynomial5 (u : ℝ) : ℝ :=
  -u / 6 + 7 * u ^ 3 / 360 - 31 * u ^ 5 / 15120

private def sharpWideCschMultiplier6 (u : ℝ) : ℝ :=
  1 + u * sharpWideCschRegularPolynomial5 u

private def sharpWideSechError (u : ℝ) : ℝ :=
  u ^ 8 * (61 * u ^ 4 + 1680 * u ^ 2 + 17820) / 518400

private def sharpWideCschError (u : ℝ) : ℝ :=
  u ^ 7 * (31 * u ^ 4 + 1008 * u ^ 2 + 16212) / 76204800

private theorem sharp_cosh_lt_four_thirds
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    Real.cosh u < (4 / 3 : ℝ) := by
  have huSq : u ^ 2 < (7 / 10 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hu hu0 (by norm_num)
  have hv0 : 0 ≤ u ^ 2 / 2 := by positivity
  have hvQuarter : u ^ 2 / 2 < (1 / 4 : ℝ) := by
    norm_num at huSq ⊢
    nlinarith
  have hv1 : u ^ 2 / 2 < (1 : ℝ) := hvQuarter.trans (by norm_num)
  have hExp : Real.exp (u ^ 2 / 2) ≤ 1 / (1 - u ^ 2 / 2) :=
    Real.exp_bound_div_one_sub_of_interval hv0 hv1
  have hFrac : 1 / (1 - u ^ 2 / 2) < (4 / 3 : ℝ) := by
    rw [div_lt_iff₀ (sub_pos.mpr hv1)]
    nlinarith
  exact (Real.cosh_le_exp_half_sq u).trans_lt (hExp.trans_lt hFrac)

private theorem sharp_wide_cosh_taylor_bounds
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    sharpWideCoshPolynomial6 u ≤ Real.cosh u ∧
      Real.cosh u ≤ sharpWideCoshUpper8 u := by
  rcases eq_or_lt_of_le hu0 with rfl | hupos
  · norm_num [sharpWideCoshPolynomial6, sharpWideCoshUpper8]
  · rcases taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.cosh) (x₀ := 0) (x := u) (n := 7) hupos
        Real.contDiff_cosh.contDiffOn with ⟨w, hw, hTaylor⟩
    have hTaylorEval :
        taylorWithinEval Real.cosh 7 (Icc 0 u) 0 u =
          sharpWideCoshPolynomial6 u := by
      have hder (n : ℕ) :
          iteratedDerivWithin n Real.cosh (Icc 0 u) 0 =
            iteratedDeriv n Real.cosh 0 :=
        Real.iteratedDerivWithin_cosh_Icc n hupos ⟨le_rfl, hu0⟩
      rw [taylor_within_apply]
      simp [hder, Finset.sum_range_succ, sharpWideCoshPolynomial6]
      ring
    rw [hTaylorEval] at hTaylor
    norm_num [Real.iteratedDeriv_even_cosh] at hTaylor
    have hwBound : Real.cosh w < (4 / 3 : ℝ) :=
      sharp_cosh_lt_four_thirds hw.1.le (hw.2.trans hu)
    have hrem0 : 0 ≤ Real.cosh w * u ^ 8 / 40320 := by positivity
    have hremUpper :
        Real.cosh w * u ^ 8 / 40320 ≤
          (4 / 3 : ℝ) * u ^ 8 / 40320 := by
      gcongr
    constructor
    · linarith
    · unfold sharpWideCoshUpper8
      linarith

private theorem sharp_wide_sinh_div_taylor_bounds
    {u : ℝ} (hu0 : 0 < u) (hu : u < (7 / 10 : ℝ)) :
    sharpWideSinhDivPolynomial6 u ≤ Real.sinh u / u ∧
      Real.sinh u / u ≤ sharpWideSinhDivUpper8 u := by
  rcases taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.sinh) (x₀ := 0) (x := u) (n := 8) hu0
      Real.contDiff_sinh.contDiffOn with ⟨w, hw, hTaylor⟩
  have hTaylorEval :
      taylorWithinEval Real.sinh 8 (Icc 0 u) 0 u =
        u + u ^ 3 / 6 + u ^ 5 / 120 + u ^ 7 / 5040 := by
    have hder (n : ℕ) :
        iteratedDerivWithin n Real.sinh (Icc 0 u) 0 =
          iteratedDeriv n Real.sinh 0 :=
      Real.iteratedDerivWithin_sinh_Icc n hu0 ⟨le_rfl, hu0.le⟩
    rw [taylor_within_apply]
    simp [hder, Finset.sum_range_succ]
    ring
  rw [hTaylorEval] at hTaylor
  norm_num [Real.iteratedDeriv_odd_sinh] at hTaylor
  have hdiv :
      Real.sinh u / u - sharpWideSinhDivPolynomial6 u =
        Real.cosh w * u ^ 8 / 362880 := by
    unfold sharpWideSinhDivPolynomial6
    rw [show Real.sinh u / u -
          (1 + u ^ 2 / 6 + u ^ 4 / 120 + u ^ 6 / 5040) =
        (Real.sinh u -
          (u + u ^ 3 / 6 + u ^ 5 / 120 + u ^ 7 / 5040)) / u by
      field_simp [hu0.ne'],
      hTaylor]
    field_simp [hu0.ne']
  have hwBound : Real.cosh w < (4 / 3 : ℝ) :=
    sharp_cosh_lt_four_thirds hw.1.le (hw.2.trans hu)
  have hrem0 : 0 ≤ Real.cosh w * u ^ 8 / 362880 := by positivity
  have hremUpper :
      Real.cosh w * u ^ 8 / 362880 ≤
        (4 / 3 : ℝ) * u ^ 8 / 362880 := by
    gcongr
  constructor
  · linarith
  · unfold sharpWideSinhDivUpper8
    linarith

private theorem sharp_wide_sech_envelope
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    0 ≤ 1 / Real.cosh u - sharpWideSechPolynomial6 u ∧
      1 / Real.cosh u - sharpWideSechPolynomial6 u ≤
        sharpWideSechError u := by
  have hTaylor := sharp_wide_cosh_taylor_bounds hu0 hu
  have huSq : u ^ 2 < (1 / 2 : ℝ) := by
    have h := pow_lt_pow_left₀ hu hu0 (by norm_num : (2 : ℕ) ≠ 0)
    norm_num at h ⊢
    linarith
  have huSix : u ^ 6 < (1 / 2 : ℝ) ^ 3 := by
    have h := pow_lt_pow_left₀ huSq (sq_nonneg u) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [show (u ^ 2) ^ 3 = u ^ 6 by ring] using h
  have hP0 : 0 ≤ sharpWideSechPolynomial6 u := by
    unfold sharpWideSechPolynomial6
    have huFour0 : 0 ≤ u ^ 4 := by positivity
    nlinarith
  have hFactorUpper :
      sharpWideSechPolynomial6 u * sharpWideCoshUpper8 u - 1 =
        -(u ^ 8 *
          (61 * u ^ 6 + 2412 * u ^ 4 + 70920 * u ^ 2 + 747720)) /
            21772800 := by
    unfold sharpWideSechPolynomial6 sharpWideCoshUpper8
      sharpWideCoshPolynomial6
    ring
  have hPCup : sharpWideSechPolynomial6 u * sharpWideCoshUpper8 u ≤ 1 := by
    rw [← sub_nonpos, hFactorUpper]
    have hnonneg : 0 ≤ u ^ 8 *
        (61 * u ^ 6 + 2412 * u ^ 4 + 70920 * u ^ 2 + 747720) := by
      positivity
    nlinarith
  have hPCosh : sharpWideSechPolynomial6 u * Real.cosh u ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTaylor.2 hP0).trans hPCup
  have hLower : 0 ≤ 1 / Real.cosh u - sharpWideSechPolynomial6 u := by
    rw [sub_nonneg, le_div_iff₀ (Real.cosh_pos u)]
    simpa only [one_mul] using hPCosh
  constructor
  · exact hLower
  · have hIdentity :
        1 / Real.cosh u - sharpWideSechPolynomial6 u =
          (1 - sharpWideSechPolynomial6 u * Real.cosh u) / Real.cosh u := by
      field_simp [(Real.cosh_pos u).ne']
    have hNumerator0 :
        0 ≤ 1 - sharpWideSechPolynomial6 u * Real.cosh u := by
      linarith
    have hDivide :
        (1 - sharpWideSechPolynomial6 u * Real.cosh u) / Real.cosh u ≤
          1 - sharpWideSechPolynomial6 u * Real.cosh u :=
      div_le_self hNumerator0 (Real.one_le_cosh u)
    have hPLower :
        sharpWideSechPolynomial6 u * sharpWideCoshPolynomial6 u ≤
          sharpWideSechPolynomial6 u * Real.cosh u :=
      mul_le_mul_of_nonneg_left hTaylor.1 hP0
    have hErrorIdentity :
        1 - sharpWideSechPolynomial6 u * sharpWideCoshPolynomial6 u =
          sharpWideSechError u := by
      unfold sharpWideSechPolynomial6 sharpWideCoshPolynomial6
        sharpWideSechError
      ring
    rw [hIdentity]
    calc
      _ ≤ 1 - sharpWideSechPolynomial6 u * Real.cosh u := hDivide
      _ ≤ 1 - sharpWideSechPolynomial6 u * sharpWideCoshPolynomial6 u := by
        nlinarith
      _ = sharpWideSechError u := hErrorIdentity

private def sharpWideSechLowerError (u : ℝ) : ℝ :=
  (3 / 4 : ℝ) *
    (u ^ 8 *
      (61 * u ^ 6 + 2412 * u ^ 4 + 70920 * u ^ 2 + 747720) /
        21772800)

private theorem sharp_wide_sech_lower_envelope
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    sharpWideSechLowerError u ≤
      1 / Real.cosh u - sharpWideSechPolynomial6 u := by
  have hTaylor := sharp_wide_cosh_taylor_bounds hu0 hu
  have huSq : u ^ 2 < (1 / 2 : ℝ) := by
    have h := pow_lt_pow_left₀ hu hu0 (by norm_num : (2 : ℕ) ≠ 0)
    norm_num at h ⊢
    linarith
  have huSix : u ^ 6 < (1 / 2 : ℝ) ^ 3 := by
    have h := pow_lt_pow_left₀ huSq (sq_nonneg u) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [show (u ^ 2) ^ 3 = u ^ 6 by ring] using h
  have hP0 : 0 ≤ sharpWideSechPolynomial6 u := by
    unfold sharpWideSechPolynomial6
    have huFour0 : 0 ≤ u ^ 4 := by positivity
    nlinarith
  let N : ℝ :=
    u ^ 8 *
      (61 * u ^ 6 + 2412 * u ^ 4 + 70920 * u ^ 2 + 747720) /
        21772800
  have hN0 : 0 ≤ N := by
    dsimp only [N]
    positivity
  have hNIdentity :
      1 - sharpWideSechPolynomial6 u * sharpWideCoshUpper8 u = N := by
    dsimp only [N]
    unfold sharpWideSechPolynomial6 sharpWideCoshUpper8
      sharpWideCoshPolynomial6
    ring
  have hNumeratorLower :
      N ≤ 1 - sharpWideSechPolynomial6 u * Real.cosh u := by
    rw [← hNIdentity]
    have hmul := mul_le_mul_of_nonneg_left hTaylor.2 hP0
    linarith
  have hNumerator0 :
      0 ≤ 1 - sharpWideSechPolynomial6 u * Real.cosh u :=
    hN0.trans hNumeratorLower
  have hrecip : (3 / 4 : ℝ) ≤ 1 / Real.cosh u := by
    rw [le_div_iff₀ (Real.cosh_pos u)]
    nlinarith [sharp_cosh_lt_four_thirds hu0 hu]
  have hIdentity :
      1 / Real.cosh u - sharpWideSechPolynomial6 u =
        (1 - sharpWideSechPolynomial6 u * Real.cosh u) / Real.cosh u := by
    field_simp [(Real.cosh_pos u).ne']
  unfold sharpWideSechLowerError
  dsimp only [N] at hN0 hNumeratorLower ⊢
  rw [hIdentity]
  calc
    _ ≤ (3 / 4 : ℝ) *
        (1 - sharpWideSechPolynomial6 u * Real.cosh u) :=
      mul_le_mul_of_nonneg_left hNumeratorLower (by norm_num)
    _ ≤ (1 / Real.cosh u) *
        (1 - sharpWideSechPolynomial6 u * Real.cosh u) :=
      mul_le_mul_of_nonneg_right hrecip hNumerator0
    _ = _ := by ring

private theorem sharp_wide_csch_envelope
    {u : ℝ} (hu0 : 0 < u) (hu : u < (7 / 10 : ℝ)) :
    0 ≤ 1 / Real.sinh u - 1 / u - sharpWideCschRegularPolynomial5 u ∧
      1 / Real.sinh u - 1 / u - sharpWideCschRegularPolynomial5 u ≤
        sharpWideCschError u := by
  let B : ℝ := Real.sinh u / u
  have hTaylorRaw := sharp_wide_sinh_div_taylor_bounds hu0 hu
  have hTaylor :
      sharpWideSinhDivPolynomial6 u ≤ B ∧ B ≤ sharpWideSinhDivUpper8 u :=
    hTaylorRaw
  have hB1 : (1 : ℝ) ≤ B := by
    dsimp only [B]
    rw [le_div_iff₀ hu0]
    simpa using (Real.self_le_sinh_iff.mpr hu0.le)
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB1
  have huSq : u ^ 2 < (1 / 2 : ℝ) := by
    have h := pow_lt_pow_left₀ hu hu0.le (by norm_num : (2 : ℕ) ≠ 0)
    norm_num at h ⊢
    linarith
  have huSix : u ^ 6 < (1 / 2 : ℝ) ^ 3 := by
    have h := pow_lt_pow_left₀ huSq (sq_nonneg u) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [show (u ^ 2) ^ 3 = u ^ 6 by ring] using h
  have hQ0 : 0 ≤ sharpWideCschMultiplier6 u := by
    unfold sharpWideCschMultiplier6 sharpWideCschRegularPolynomial5
    have huFour0 : 0 ≤ u ^ 4 := by positivity
    nlinarith
  have hFactorUpper :
      sharpWideCschMultiplier6 u * sharpWideSinhDivUpper8 u - 1 =
        -(u ^ 8 *
          (31 * u ^ 6 + 1380 * u ^ 4 + 56952 * u ^ 2 + 860328)) /
            4115059200 := by
    unfold sharpWideCschMultiplier6 sharpWideCschRegularPolynomial5
      sharpWideSinhDivUpper8 sharpWideSinhDivPolynomial6
    ring
  have hQBup : sharpWideCschMultiplier6 u * sharpWideSinhDivUpper8 u ≤ 1 := by
    rw [← sub_nonpos, hFactorUpper]
    have hnonneg : 0 ≤ u ^ 8 *
        (31 * u ^ 6 + 1380 * u ^ 4 + 56952 * u ^ 2 + 860328) := by
      positivity
    nlinarith
  have hQB : sharpWideCschMultiplier6 u * B ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTaylor.2 hQ0).trans hQBup
  have hQleInv : sharpWideCschMultiplier6 u ≤ 1 / B := by
    rw [le_div_iff₀ hBpos]
    simpa only [one_mul] using hQB
  have hSinhPos : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hMainIdentity :
      1 / Real.sinh u - 1 / u - sharpWideCschRegularPolynomial5 u =
        (1 / B - sharpWideCschMultiplier6 u) / u := by
    dsimp only [B]
    unfold sharpWideCschMultiplier6
    field_simp [hu0.ne', hSinhPos.ne']
    ring
  have hLower :
      0 ≤ 1 / Real.sinh u - 1 / u - sharpWideCschRegularPolynomial5 u := by
    rw [hMainIdentity]
    exact div_nonneg (sub_nonneg.mpr hQleInv) hu0.le
  constructor
  · exact hLower
  · have hInvIdentity :
        1 / B - sharpWideCschMultiplier6 u =
          (1 - sharpWideCschMultiplier6 u * B) / B := by
      field_simp [hBpos.ne']
    have hNumerator0 : 0 ≤ 1 - sharpWideCschMultiplier6 u * B := by
      linarith
    have hDivideB :
        (1 - sharpWideCschMultiplier6 u * B) / B ≤
          1 - sharpWideCschMultiplier6 u * B :=
      div_le_self hNumerator0 hB1
    have hQLower :
        sharpWideCschMultiplier6 u * sharpWideSinhDivPolynomial6 u ≤
          sharpWideCschMultiplier6 u * B :=
      mul_le_mul_of_nonneg_left hTaylor.1 hQ0
    have hErrorIdentity :
        1 - sharpWideCschMultiplier6 u * sharpWideSinhDivPolynomial6 u =
          u * sharpWideCschError u := by
      unfold sharpWideCschMultiplier6 sharpWideCschRegularPolynomial5
        sharpWideSinhDivPolynomial6 sharpWideCschError
      ring
    have hInner :
        1 / B - sharpWideCschMultiplier6 u ≤ u * sharpWideCschError u := by
      rw [hInvIdentity]
      calc
        _ ≤ 1 - sharpWideCschMultiplier6 u * B := hDivideB
        _ ≤ 1 - sharpWideCschMultiplier6 u * sharpWideSinhDivPolynomial6 u := by
          linarith
        _ = u * sharpWideCschError u := hErrorIdentity
    rw [hMainIdentity]
    rw [div_le_iff₀ hu0]
    simpa only [div_mul_cancel₀ _ hu0.ne', mul_comm] using hInner

private theorem yoshidaRegularKernel_two_mul_sharp (u : ℝ) (hu : 0 < u) :
    yoshidaRegularKernel (2 * u) =
      (1 / 4 : ℝ) *
        (1 / Real.cosh u + (1 / Real.sinh u - 1 / u)) := by
  unfold yoshidaRegularKernel
  rw [if_neg (mul_ne_zero (by norm_num) hu.ne')]
  rw [show 2 * u / 2 = u by ring, Real.sinh_two_mul,
    ← Real.cosh_add_sinh]
  field_simp [hu.ne', (Real.sinh_pos_iff.mpr hu).ne',
    (Real.cosh_pos u).ne']
  ring

private theorem yoshidaRegularKernelPolynomial6_two_mul_sharp (u : ℝ) :
    yoshidaRegularKernelPolynomial6 (2 * u) =
      (1 / 4 : ℝ) *
        (sharpWideSechPolynomial6 u +
          sharpWideCschRegularPolynomial5 u) := by
  unfold yoshidaRegularKernelPolynomial6 sharpWideSechPolynomial6
    sharpWideCschRegularPolynomial5
  ring

private def sharpWideRegularError (u : ℝ) : ℝ :=
  (1 / 4 : ℝ) * (sharpWideSechError u + sharpWideCschError u)

private theorem yoshidaRegularKernelPolynomial6_sharp_wide_envelope
    {t : ℝ} (ht0 : 0 ≤ t) (htlog : t ≤ 2 * Real.log 2) :
    0 ≤ yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t ∧
      yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t ≤
        sharpWideRegularError (t / 2) := by
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · constructor <;>
      norm_num [yoshidaRegularKernel, yoshidaRegularKernelPolynomial6,
        sharpWideRegularError, sharpWideSechError, sharpWideCschError]
  · let u : ℝ := t / 2
    have hu0 : 0 < u := by
      dsimp only [u]
      linarith
    have hu : u < (7 / 10 : ℝ) := by
      dsimp only [u]
      have hlog := strict_log_two_bounds.2
      linarith
    have hSech := sharp_wide_sech_envelope hu0.le hu
    have hCsch := sharp_wide_csch_envelope hu0 hu
    have htEq : t = 2 * u := by
      dsimp only [u]
      ring
    have hDifference :
        yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t =
          (1 / 4 : ℝ) *
            ((1 / Real.cosh u - sharpWideSechPolynomial6 u) +
              (1 / Real.sinh u - 1 / u -
                sharpWideCschRegularPolynomial5 u)) := by
      rw [htEq, yoshidaRegularKernel_two_mul_sharp u hu0,
        yoshidaRegularKernelPolynomial6_two_mul_sharp]
      ring
    rw [hDifference]
    constructor
    · nlinarith [hSech.1, hCsch.1]
    · unfold sharpWideRegularError
      nlinarith [hSech.2, hCsch.2]

private theorem yoshidaRegularKernelPolynomial6_sharp_wide_lower
    {t : ℝ} (ht0 : 0 ≤ t) (htlog : t ≤ 2 * Real.log 2) :
    (3 / 500 : ℝ) * (t / 2) ^ 8 ≤
      yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t := by
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · norm_num [yoshidaRegularKernel, yoshidaRegularKernelPolynomial6]
  · let u : ℝ := t / 2
    have hu0 : 0 < u := by
      dsimp only [u]
      linarith
    have hu : u < (7 / 10 : ℝ) := by
      dsimp only [u]
      have hlog := strict_log_two_bounds.2
      linarith
    have hSech := sharp_wide_sech_lower_envelope hu0.le hu
    have hCsch := sharp_wide_csch_envelope hu0 hu
    have htEq : t = 2 * u := by
      dsimp only [u]
      ring
    have hDifference :
        yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t =
          (1 / 4 : ℝ) *
            ((1 / Real.cosh u - sharpWideSechPolynomial6 u) +
              (1 / Real.sinh u - 1 / u -
                sharpWideCschRegularPolynomial5 u)) := by
      rw [htEq, yoshidaRegularKernel_two_mul_sharp u hu0,
        yoshidaRegularKernelPolynomial6_two_mul_sharp]
      ring
    have hLowerPolynomial :
        (3 / 500 : ℝ) * u ^ 8 ≤
          (1 / 4 : ℝ) * sharpWideSechLowerError u := by
      have hidentity :
          (1 / 4 : ℝ) * sharpWideSechLowerError u -
              (3 / 500 : ℝ) * u ^ 8 =
            u ^ 8 *
              ((61 / 116121600 : ℝ) * u ^ 6 +
                (67 / 3225600 : ℝ) * u ^ 4 +
                (197 / 322560 : ℝ) * u ^ 2 +
                (3541 / 8064000 : ℝ)) := by
        unfold sharpWideSechLowerError
        ring
      rw [← sub_nonneg, hidentity]
      positivity
    rw [hDifference]
    change (3 / 500 : ℝ) * u ^ 8 ≤
      (1 / 4 : ℝ) *
        ((1 / Real.cosh u - sharpWideSechPolynomial6 u) +
          (1 / Real.sinh u - 1 / u - sharpWideCschRegularPolynomial5 u))
    nlinarith [hSech, hCsch.1]

private theorem sharpWideSechError_le_simple
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (7 / 10 : ℝ)) :
    sharpWideSechError u ≤ (37 / 1000 : ℝ) * u ^ 8 := by
  unfold sharpWideSechError
  have hu2 : u ^ 2 ≤ (7 / 10 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hu0 hu 2
  have hu4 : u ^ 4 ≤ (7 / 10 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hu0 hu 4
  have hu8 : 0 ≤ u ^ 8 := by positivity
  have hcoefficient :
      (61 * u ^ 4 + 1680 * u ^ 2 + 17820) / 518400 ≤
        (37 / 1000 : ℝ) := by
    norm_num at hu2 hu4 ⊢
    nlinarith
  rw [show u ^ 8 * (61 * u ^ 4 + 1680 * u ^ 2 + 17820) / 518400 =
      u ^ 8 * ((61 * u ^ 4 + 1680 * u ^ 2 + 17820) / 518400) by ring]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcoefficient hu8

private theorem sharpWideCschError_le_simple
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (7 / 10 : ℝ)) :
    sharpWideCschError u ≤ (23 / 100000 : ℝ) * u ^ 7 := by
  unfold sharpWideCschError
  have hu2 : u ^ 2 ≤ (7 / 10 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hu0 hu 2
  have hu4 : u ^ 4 ≤ (7 / 10 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hu0 hu 4
  have hu7 : 0 ≤ u ^ 7 := by positivity
  have hcoefficient :
      (31 * u ^ 4 + 1008 * u ^ 2 + 16212) / 76204800 ≤
        (23 / 100000 : ℝ) := by
    norm_num at hu2 hu4 ⊢
    nlinarith
  rw [show u ^ 7 * (31 * u ^ 4 + 1008 * u ^ 2 + 16212) / 76204800 =
      u ^ 7 * ((31 * u ^ 4 + 1008 * u ^ 2 + 16212) / 76204800) by ring]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcoefficient hu7

private theorem sharpWideRegularError_le_simple
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (7 / 10 : ℝ)) :
    sharpWideRegularError u ≤
      (37 / 4000 : ℝ) * u ^ 8 +
        (23 / 400000 : ℝ) * u ^ 7 := by
  unfold sharpWideRegularError
  nlinarith [sharpWideSechError_le_simple hu0 hu,
    sharpWideCschError_le_simple hu0 hu]

private def intrinsicAlternatingResidualLowerMagnitude (t : ℝ) : ℝ :=
  let zp := yoshidaEndpointA * (2 + t) / 2
  let zm := yoshidaEndpointA * (2 - t) / 2
  yoshidaEndpointA *
    ((1 / 15120 : ℝ) * zm ^ 8 +
      (37 / 4000 : ℝ) * zp ^ 8 +
      (23 / 400000 : ℝ) * zp ^ 7)

private def intrinsicAlternatingResidualUpperMagnitude (t : ℝ) : ℝ :=
  let zp := yoshidaEndpointA * (2 + t) / 2
  let zm := yoshidaEndpointA * (2 - t) / 2
  yoshidaEndpointA *
    ((1 / 15120 : ℝ) * zp ^ 8 +
      (37 / 4000 : ℝ) * zm ^ 8 +
      (23 / 400000 : ℝ) * zm ^ 7)

private theorem intrinsicAlternatingResidualMagnitude_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    0 ≤ intrinsicAlternatingResidualLowerMagnitude t ∧
      0 ≤ intrinsicAlternatingResidualUpperMagnitude t := by
  have hplus : 0 ≤ 2 + t := by linarith
  have hminus : 0 ≤ 2 - t := by linarith
  have hzp : 0 ≤ yoshidaEndpointA * (2 + t) / 2 :=
    div_nonneg (mul_nonneg yoshidaEndpointA_pos.le hplus) (by norm_num)
  have hzm : 0 ≤ yoshidaEndpointA * (2 - t) / 2 :=
    div_nonneg (mul_nonneg yoshidaEndpointA_pos.le hminus) (by norm_num)
  unfold intrinsicAlternatingResidualLowerMagnitude
    intrinsicAlternatingResidualUpperMagnitude
  dsimp only
  constructor
  · apply mul_nonneg yoshidaEndpointA_pos.le
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num) (by positivity))
        (mul_nonneg (by norm_num) (by positivity)))
      (mul_nonneg (by norm_num) (pow_nonneg hzp 7))
  · apply mul_nonneg yoshidaEndpointA_pos.le
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num) (by positivity))
        (mul_nonneg (by norm_num) (by positivity)))
      (mul_nonneg (by norm_num) (pow_nonneg hzm 7))

private theorem intrinsicAlternatingKernel_residual_envelope
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    -intrinsicAlternatingResidualLowerMagnitude t ≤
        yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          intrinsicAlternatingKernelPolynomial6 t ∧
      yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          intrinsicAlternatingKernelPolynomial6 t ≤
        intrinsicAlternatingResidualUpperMagnitude t := by
  let up : ℝ := yoshidaEndpointA * (2 + t)
  let um : ℝ := yoshidaEndpointA * (2 - t)
  let zp : ℝ := up / 2
  let zm : ℝ := um / 2
  let ecp : ℝ := Real.cosh zp - sharpWideCoshPolynomial6 zp
  let ecm : ℝ := Real.cosh zm - sharpWideCoshPolynomial6 zm
  let erp : ℝ := yoshidaRegularKernel up -
    yoshidaRegularKernelPolynomial6 up
  let erm : ℝ := yoshidaRegularKernel um -
    yoshidaRegularKernelPolynomial6 um
  have hAupper : yoshidaEndpointA < (347 / 1000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_bounds.2]
  have hup0 : 0 ≤ up := by
    dsimp only [up]
    exact mul_nonneg yoshidaEndpointA_pos.le (by linarith)
  have hum0 : 0 ≤ um := by
    dsimp only [um]
    exact mul_nonneg yoshidaEndpointA_pos.le (by linarith)
  have hupLog : up ≤ 2 * Real.log 2 := by
    dsimp only [up]
    unfold yoshidaEndpointA
    have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    nlinarith
  have humLog : um ≤ 2 * Real.log 2 := by
    dsimp only [um]
    unfold yoshidaEndpointA
    have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    nlinarith
  have hzp0 : 0 ≤ zp := by
    dsimp only [zp]
    positivity
  have hzm0 : 0 ≤ zm := by
    dsimp only [zm]
    positivity
  have hzp : zp < (7 / 10 : ℝ) := by
    dsimp only [zp, up]
    have hplus : 2 + t ≤ 4 := by linarith
    nlinarith [yoshidaEndpointA_pos]
  have hzm : zm < (7 / 10 : ℝ) := by
    dsimp only [zm, um]
    have hminus : 2 - t ≤ 2 := by linarith
    nlinarith [yoshidaEndpointA_pos]
  have hcp := sharp_wide_cosh_taylor_bounds hzp0 hzp
  have hcm := sharp_wide_cosh_taylor_bounds hzm0 hzm
  have hrp := yoshidaRegularKernelPolynomial6_sharp_wide_envelope hup0 hupLog
  have hrm := yoshidaRegularKernelPolynomial6_sharp_wide_envelope hum0 humLog
  have hecp0 : 0 ≤ ecp := by
    dsimp only [ecp]
    linarith [hcp.1]
  have hecm0 : 0 ≤ ecm := by
    dsimp only [ecm]
    linarith [hcm.1]
  have hecp : ecp ≤ (2 / 3 : ℝ) * zp ^ 8 / 20160 := by
    dsimp only [ecp]
    unfold sharpWideCoshUpper8 at hcp
    linarith
  have hecm : ecm ≤ (2 / 3 : ℝ) * zm ^ 8 / 20160 := by
    dsimp only [ecm]
    unfold sharpWideCoshUpper8 at hcm
    linarith
  have herp0 : 0 ≤ erp := by simpa only [erp] using hrp.1
  have herm0 : 0 ≤ erm := by simpa only [erm] using hrm.1
  have herp : erp ≤
      (37 / 4000 : ℝ) * zp ^ 8 + (23 / 400000 : ℝ) * zp ^ 7 := by
    have hsimple := sharpWideRegularError_le_simple hzp0 hzp.le
    dsimp only [erp, zp]
    exact hrp.2.trans (by simpa only [show up / 2 = up / 2 by rfl] using hsimple)
  have herm : erm ≤
      (37 / 4000 : ℝ) * zm ^ 8 + (23 / 400000 : ℝ) * zm ^ 7 := by
    have hsimple := sharpWideRegularError_le_simple hzm0 hzm.le
    dsimp only [erm, zm]
    exact hrm.2.trans (by simpa only [show um / 2 = um / 2 by rfl] using hsimple)
  dsimp only [zp, zm] at hecp hecm herp herm
  have hdiff :
      yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          intrinsicAlternatingKernelPolynomial6 t =
        yoshidaEndpointA * (2 * ecp - 2 * ecm - erp + erm) := by
    dsimp only [factorTwoCenteredAntisymmetricRegularWeight,
      intrinsicAlternatingKernelPolynomial6, up, um, zp, zm,
      ecp, ecm, erp, erm]
    ring
  rw [hdiff]
  unfold intrinsicAlternatingResidualLowerMagnitude
    intrinsicAlternatingResidualUpperMagnitude
  dsimp only [up, um, zp, zm]
  constructor
  · have hinside :
        -((1 / 15120 : ℝ) * (um / 2) ^ 8 +
            ((37 / 4000 : ℝ) * (up / 2) ^ 8 +
              (23 / 400000 : ℝ) * (up / 2) ^ 7)) ≤
          2 * ecp - 2 * ecm - erp + erm := by
      nlinarith
    calc
      _ = yoshidaEndpointA *
          (-((1 / 15120 : ℝ) * (um / 2) ^ 8 +
            ((37 / 4000 : ℝ) * (up / 2) ^ 8 +
              (23 / 400000 : ℝ) * (up / 2) ^ 7))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hinside yoshidaEndpointA_pos.le
  · have hinside :
        2 * ecp - 2 * ecm - erp + erm ≤
          (1 / 15120 : ℝ) * (up / 2) ^ 8 +
            ((37 / 4000 : ℝ) * (um / 2) ^ 8 +
              (23 / 400000 : ℝ) * (um / 2) ^ 7) := by
      nlinarith
    simpa only [up, um, add_assoc] using
      mul_le_mul_of_nonneg_left hinside yoshidaEndpointA_pos.le

private def intrinsicAlternatingRationalLowerMagnitude (t : ℝ) : ℝ :=
  (347 / 1000 : ℝ) *
    ((1 / 15120 : ℝ) * (347 / 2000 : ℝ) ^ 8 * (2 - t) ^ 8 +
      (37 / 4000 : ℝ) * (347 / 2000 : ℝ) ^ 8 * (2 + t) ^ 8 +
      (23 / 400000 : ℝ) * (347 / 2000 : ℝ) ^ 7 * (2 + t) ^ 7)

private def intrinsicAlternatingRationalUpperMagnitude (t : ℝ) : ℝ :=
  (347 / 1000 : ℝ) *
    ((1 / 15120 : ℝ) * (347 / 2000 : ℝ) ^ 8 * (2 + t) ^ 8 +
      (37 / 4000 : ℝ) * (347 / 2000 : ℝ) ^ 8 * (2 - t) ^ 8 +
      (23 / 400000 : ℝ) * (347 / 2000 : ℝ) ^ 7 * (2 - t) ^ 7)

private def intrinsicAlternatingRefinedRationalUpper (t : ℝ) : ℝ :=
  ((1 / 15120 : ℝ) - 3 / 500) *
      (3465735 / 10000000 : ℝ) ^ 9 / 2 ^ 8 * (2 + t) ^ 8 +
    (37 / 4000 : ℝ) *
      (3465737 / 10000000 : ℝ) ^ 9 / 2 ^ 8 * (2 - t) ^ 8 +
    (23 / 400000 : ℝ) *
      (3465737 / 10000000 : ℝ) ^ 8 / 2 ^ 7 * (2 - t) ^ 7

private theorem intrinsicAlternatingKernel_residual_le_refinedRationalUpper
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
        intrinsicAlternatingKernelPolynomial6 t ≤
      intrinsicAlternatingRefinedRationalUpper t := by
  let up : ℝ := yoshidaEndpointA * (2 + t)
  let um : ℝ := yoshidaEndpointA * (2 - t)
  let zp : ℝ := up / 2
  let zm : ℝ := um / 2
  let ecp : ℝ := Real.cosh zp - sharpWideCoshPolynomial6 zp
  let ecm : ℝ := Real.cosh zm - sharpWideCoshPolynomial6 zm
  let erp : ℝ := yoshidaRegularKernel up -
    yoshidaRegularKernelPolynomial6 up
  let erm : ℝ := yoshidaRegularKernel um -
    yoshidaRegularKernelPolynomial6 um
  have hup0 : 0 ≤ up := by
    dsimp only [up]
    exact mul_nonneg yoshidaEndpointA_pos.le (by linarith)
  have hum0 : 0 ≤ um := by
    dsimp only [um]
    exact mul_nonneg yoshidaEndpointA_pos.le (by linarith)
  have hupLog : up ≤ 2 * Real.log 2 := by
    dsimp only [up]
    unfold yoshidaEndpointA
    have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    nlinarith
  have humLog : um ≤ 2 * Real.log 2 := by
    dsimp only [um]
    unfold yoshidaEndpointA
    have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    nlinarith
  have hzp0 : 0 ≤ zp := by dsimp only [zp]; positivity
  have hzm0 : 0 ≤ zm := by dsimp only [zm]; positivity
  have hzp : zp < (7 / 10 : ℝ) := by
    dsimp only [zp, up]
    have hA := strict_log_two_bounds.2
    unfold yoshidaEndpointA
    nlinarith
  have hzm : zm < (7 / 10 : ℝ) := by
    dsimp only [zm, um]
    have hA := strict_log_two_bounds.2
    unfold yoshidaEndpointA
    nlinarith
  have hcp := sharp_wide_cosh_taylor_bounds hzp0 hzp
  have hrm := yoshidaRegularKernelPolynomial6_sharp_wide_envelope hum0 humLog
  have hrmSimple := sharpWideRegularError_le_simple hzm0 hzm.le
  have hrpLower :=
    yoshidaRegularKernelPolynomial6_sharp_wide_lower hup0 hupLog
  have hecm0 : 0 ≤ ecm := by
    dsimp only [ecm]
    exact sub_nonneg.mpr (sharp_wide_cosh_taylor_bounds hzm0 hzm).1
  have hecp : ecp ≤ (1 / 30240 : ℝ) * zp ^ 8 := by
    dsimp only [ecp]
    unfold sharpWideCoshUpper8 at hcp
    linarith
  have herp : (3 / 500 : ℝ) * zp ^ 8 ≤ erp := by
    simpa only [erp, zp] using hrpLower
  have herm : erm ≤
      (37 / 4000 : ℝ) * zm ^ 8 + (23 / 400000 : ℝ) * zm ^ 7 := by
    dsimp only [erm, zm]
    exact hrm.2.trans hrmSimple
  have hdiff :
      yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          intrinsicAlternatingKernelPolynomial6 t =
        yoshidaEndpointA * (2 * ecp - 2 * ecm - erp + erm) := by
    dsimp only [factorTwoCenteredAntisymmetricRegularWeight,
      intrinsicAlternatingKernelPolynomial6, up, um, zp, zm,
      ecp, ecm, erp, erm]
    ring
  have hinside :
      2 * ecp - 2 * ecm - erp + erm ≤
        ((1 / 15120 : ℝ) - 3 / 500) * zp ^ 8 +
          (37 / 4000 : ℝ) * zm ^ 8 +
          (23 / 400000 : ℝ) * zm ^ 7 := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hinside yoshidaEndpointA_pos.le
  have hAL : (3465735 / 10000000 : ℝ) ≤ yoshidaEndpointA := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.1]
  have hAU : yoshidaEndpointA ≤ (3465737 / 10000000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.2]
  have hAL0 : 0 ≤ (3465735 / 10000000 : ℝ) := by norm_num
  have hA0 : 0 ≤ yoshidaEndpointA := yoshidaEndpointA_pos.le
  have hA9L := pow_le_pow_left₀ hAL0 hAL 9
  have hA9U := pow_le_pow_left₀ hA0 hAU 9
  have hA8U := pow_le_pow_left₀ hA0 hAU 8
  have hcneg : ((1 / 15120 : ℝ) - 3 / 500) ≤ 0 := by norm_num
  have hplus8 : 0 ≤ (2 + t) ^ 8 := by positivity
  have hminus8 : 0 ≤ (2 - t) ^ 8 := by positivity
  have hminus7 : 0 ≤ (2 - t) ^ 7 := by
    exact pow_nonneg (by linarith) 7
  have hnegTerm :
      ((1 / 15120 : ℝ) - 3 / 500) * yoshidaEndpointA ^ 9 /
            2 ^ 8 * (2 + t) ^ 8 ≤
        ((1 / 15120 : ℝ) - 3 / 500) *
            (3465735 / 10000000 : ℝ) ^ 9 /
              2 ^ 8 * (2 + t) ^ 8 := by
    have h := mul_le_mul_of_nonpos_left hA9L hcneg
    have hfactor : 0 ≤ (2 + t) ^ 8 / 2 ^ 8 := by positivity
    calc
      _ = (((1 / 15120 : ℝ) - 3 / 500) * yoshidaEndpointA ^ 9) *
          ((2 + t) ^ 8 / 2 ^ 8) := by ring
      _ ≤ (((1 / 15120 : ℝ) - 3 / 500) *
          (3465735 / 10000000 : ℝ) ^ 9) *
            ((2 + t) ^ 8 / 2 ^ 8) :=
        mul_le_mul_of_nonneg_right h hfactor
      _ = _ := by ring
  have hpos8Term :
      (37 / 4000 : ℝ) * yoshidaEndpointA ^ 9 /
            2 ^ 8 * (2 - t) ^ 8 ≤
        (37 / 4000 : ℝ) *
            (3465737 / 10000000 : ℝ) ^ 9 /
              2 ^ 8 * (2 - t) ^ 8 := by
    have h := mul_le_mul_of_nonneg_left hA9U (by norm_num : (0 : ℝ) ≤ 37 / 4000)
    have hfactor : 0 ≤ (2 - t) ^ 8 / 2 ^ 8 := by positivity
    calc
      _ = ((37 / 4000 : ℝ) * yoshidaEndpointA ^ 9) *
          ((2 - t) ^ 8 / 2 ^ 8) := by ring
      _ ≤ ((37 / 4000 : ℝ) *
          (3465737 / 10000000 : ℝ) ^ 9) *
            ((2 - t) ^ 8 / 2 ^ 8) :=
        mul_le_mul_of_nonneg_right h hfactor
      _ = _ := by ring
  have hpos7Term :
      (23 / 400000 : ℝ) * yoshidaEndpointA ^ 8 /
            2 ^ 7 * (2 - t) ^ 7 ≤
        (23 / 400000 : ℝ) *
            (3465737 / 10000000 : ℝ) ^ 8 /
              2 ^ 7 * (2 - t) ^ 7 := by
    have h := mul_le_mul_of_nonneg_left hA8U
      (by norm_num : (0 : ℝ) ≤ 23 / 400000)
    have hfactor : 0 ≤ (2 - t) ^ 7 / 2 ^ 7 := by positivity
    calc
      _ = ((23 / 400000 : ℝ) * yoshidaEndpointA ^ 8) *
          ((2 - t) ^ 7 / 2 ^ 7) := by ring
      _ ≤ ((23 / 400000 : ℝ) *
          (3465737 / 10000000 : ℝ) ^ 8) *
            ((2 - t) ^ 7 / 2 ^ 7) :=
        mul_le_mul_of_nonneg_right h hfactor
      _ = _ := by ring
  rw [hdiff]
  unfold intrinsicAlternatingRefinedRationalUpper
  dsimp only [zp, zm, up, um] at hscaled
  have hpowerIdentity :
      yoshidaEndpointA *
          (((1 / 15120 : ℝ) - 3 / 500) *
              (yoshidaEndpointA * (2 + t) / 2) ^ 8 +
            (37 / 4000 : ℝ) *
              (yoshidaEndpointA * (2 - t) / 2) ^ 8 +
            (23 / 400000 : ℝ) *
              (yoshidaEndpointA * (2 - t) / 2) ^ 7) =
        ((1 / 15120 : ℝ) - 3 / 500) * yoshidaEndpointA ^ 9 /
              2 ^ 8 * (2 + t) ^ 8 +
          (37 / 4000 : ℝ) * yoshidaEndpointA ^ 9 /
              2 ^ 8 * (2 - t) ^ 8 +
          (23 / 400000 : ℝ) * yoshidaEndpointA ^ 8 /
              2 ^ 7 * (2 - t) ^ 7 := by ring
  calc
    _ ≤ yoshidaEndpointA *
        (((1 / 15120 : ℝ) - 3 / 500) *
            (yoshidaEndpointA * (2 + t) / 2) ^ 8 +
          (37 / 4000 : ℝ) *
            (yoshidaEndpointA * (2 - t) / 2) ^ 8 +
          (23 / 400000 : ℝ) *
            (yoshidaEndpointA * (2 - t) / 2) ^ 7) := hscaled
    _ = _ := hpowerIdentity
    _ ≤ _ := by linarith

private theorem intrinsicAlternatingResidualMagnitude_le_rational
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    intrinsicAlternatingResidualLowerMagnitude t ≤
        intrinsicAlternatingRationalLowerMagnitude t ∧
      intrinsicAlternatingResidualUpperMagnitude t ≤
        intrinsicAlternatingRationalUpperMagnitude t := by
  have hA : yoshidaEndpointA ≤ (347 / 1000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_bounds.2]
  have hplus0 : 0 ≤ 2 + t := by linarith
  have hminus0 : 0 ≤ 2 - t := by linarith
  have hzp0 : 0 ≤ yoshidaEndpointA * (2 + t) / 2 :=
    div_nonneg (mul_nonneg yoshidaEndpointA_pos.le hplus0) (by norm_num)
  have hzm0 : 0 ≤ yoshidaEndpointA * (2 - t) / 2 :=
    div_nonneg (mul_nonneg yoshidaEndpointA_pos.le hminus0) (by norm_num)
  have hzp : yoshidaEndpointA * (2 + t) / 2 ≤
      (347 / 2000 : ℝ) * (2 + t) := by
    nlinarith
  have hzm : yoshidaEndpointA * (2 - t) / 2 ≤
      (347 / 2000 : ℝ) * (2 - t) := by
    nlinarith
  have hzp7 := pow_le_pow_left₀ hzp0 hzp 7
  have hzp8 := pow_le_pow_left₀ hzp0 hzp 8
  have hzm7 := pow_le_pow_left₀ hzm0 hzm 7
  have hzm8 := pow_le_pow_left₀ hzm0 hzm 8
  unfold intrinsicAlternatingResidualLowerMagnitude
    intrinsicAlternatingResidualUpperMagnitude
    intrinsicAlternatingRationalLowerMagnitude
    intrinsicAlternatingRationalUpperMagnitude
  dsimp only
  have hplus7 :
      ((347 / 2000 : ℝ) * (2 + t)) ^ 7 =
        (347 / 2000 : ℝ) ^ 7 * (2 + t) ^ 7 := by ring
  have hplus8 :
      ((347 / 2000 : ℝ) * (2 + t)) ^ 8 =
        (347 / 2000 : ℝ) ^ 8 * (2 + t) ^ 8 := by ring
  have hminus7 :
      ((347 / 2000 : ℝ) * (2 - t)) ^ 7 =
        (347 / 2000 : ℝ) ^ 7 * (2 - t) ^ 7 := by ring
  have hminus8 :
      ((347 / 2000 : ℝ) * (2 - t)) ^ 8 =
        (347 / 2000 : ℝ) ^ 8 * (2 - t) ^ 8 := by ring
  rw [hplus7] at hzp7
  rw [hplus8] at hzp8
  rw [hminus7] at hzm7
  rw [hminus8] at hzm8
  have hsumLower :
      (1 / 15120 : ℝ) *
            (yoshidaEndpointA * (2 - t) / 2) ^ 8 +
          (37 / 4000 : ℝ) *
            (yoshidaEndpointA * (2 + t) / 2) ^ 8 +
          (23 / 400000 : ℝ) *
            (yoshidaEndpointA * (2 + t) / 2) ^ 7 ≤
        (1 / 15120 : ℝ) * (347 / 2000 : ℝ) ^ 8 * (2 - t) ^ 8 +
          (37 / 4000 : ℝ) * (347 / 2000 : ℝ) ^ 8 * (2 + t) ^ 8 +
          (23 / 400000 : ℝ) * (347 / 2000 : ℝ) ^ 7 *
            (2 + t) ^ 7 := by
    nlinarith
  have hsumUpper :
      (1 / 15120 : ℝ) *
            (yoshidaEndpointA * (2 + t) / 2) ^ 8 +
          (37 / 4000 : ℝ) *
            (yoshidaEndpointA * (2 - t) / 2) ^ 8 +
          (23 / 400000 : ℝ) *
            (yoshidaEndpointA * (2 - t) / 2) ^ 7 ≤
        (1 / 15120 : ℝ) * (347 / 2000 : ℝ) ^ 8 * (2 + t) ^ 8 +
          (37 / 4000 : ℝ) * (347 / 2000 : ℝ) ^ 8 * (2 - t) ^ 8 +
          (23 / 400000 : ℝ) * (347 / 2000 : ℝ) ^ 7 *
            (2 - t) ^ 7 := by
    nlinarith
  constructor
  · exact mul_le_mul hA hsumLower (by positivity) (by positivity)
  · exact mul_le_mul hA hsumUpper (by positivity) (by positivity)

private theorem integral_rational_lower_q01Plus21 :
    (∫ t : ℝ in 0..2,
      intrinsicAlternatingRationalLowerMagnitude t *
        intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21 t) <
      (99 / 2000000 : ℝ) := by
  unfold intrinsicAlternatingRationalLowerMagnitude
    intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const, integral_pow]
  norm_num

private theorem integral_refined_upper_q01Plus21 :
    (∫ t : ℝ in 0..2,
      intrinsicAlternatingRefinedRationalUpper t *
        intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21 t) <
      (-3 / 100000 : ℝ) := by
  unfold intrinsicAlternatingRefinedRationalUpper
    intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const, integral_pow]
  norm_num

private theorem integral_refined_upper_q01Minus21 :
    (∫ t : ℝ in 0..2,
      intrinsicAlternatingRefinedRationalUpper t *
        intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21 t) <
      (-9 / 500000 : ℝ) := by
  unfold intrinsicAlternatingRefinedRationalUpper
    intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

private theorem integral_rational_upper_q01Plus21 :
    (∫ t : ℝ in 0..2,
      intrinsicAlternatingRationalUpperMagnitude t *
        intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21 t) <
      (1 / 2000000 : ℝ) := by
  unfold intrinsicAlternatingRationalUpperMagnitude
    intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const, integral_pow]
  norm_num

private theorem integral_rational_lower_q01Minus21 :
    (∫ t : ℝ in 0..2,
      intrinsicAlternatingRationalLowerMagnitude t *
        intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21 t) <
      (3 / 100000 : ℝ) := by
  unfold intrinsicAlternatingRationalLowerMagnitude
    intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

private theorem integral_rational_upper_q01Minus21 :
    (∫ t : ℝ in 0..2,
      intrinsicAlternatingRationalUpperMagnitude t *
        intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21 t) <
      (1 / 3000000 : ℝ) := by
  unfold intrinsicAlternatingRationalUpperMagnitude
    intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

private theorem integral_rational_sum_q03Plus23_majorant :
    (∫ t : ℝ in 0..2,
      (intrinsicAlternatingRationalLowerMagnitude t +
        intrinsicAlternatingRationalUpperMagnitude t) *
          (2 * (t * (2 - t)))) < (1 / 12000 : ℝ) := by
  unfold intrinsicAlternatingRationalLowerMagnitude
    intrinsicAlternatingRationalUpperMagnitude
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

private theorem integral_rational_sum_q03Minus23_majorant :
    (∫ t : ℝ in 0..2,
      (intrinsicAlternatingRationalLowerMagnitude t +
        intrinsicAlternatingRationalUpperMagnitude t) *
          (t * (2 - t))) < (1 / 25000 : ℝ) := by
  unfold intrinsicAlternatingRationalLowerMagnitude
    intrinsicAlternatingRationalUpperMagnitude
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

private theorem intervalIntegrable_intrinsicAlternatingSharpResidual
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦
        (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          intrinsicAlternatingKernelPolynomial6 t) * C t) volume 0 2 := by
  have hlinear := intervalIntegrable_intrinsicAlternatingLinearError_sharp C hC
  have hpolynomial :=
    intervalIntegrable_intrinsicAlternatingPolynomialCorrection C hC
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
        intrinsicAlternatingKernelPolynomial6 t) * C t) =
      fun t ↦
        (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          t / 10) * C t -
        (intrinsicAlternatingKernelPolynomial6 t - t / 10) * C t by
    funext t
    ring]
  exact hlinear.sub hpolynomial

private theorem intrinsicAlternatingRationalMagnitude_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    0 ≤ intrinsicAlternatingRationalLowerMagnitude t ∧
      0 ≤ intrinsicAlternatingRationalUpperMagnitude t := by
  have hplus : 0 ≤ 2 + t := by linarith
  have hminus : 0 ≤ 2 - t := by linarith
  unfold intrinsicAlternatingRationalLowerMagnitude
    intrinsicAlternatingRationalUpperMagnitude
  constructor <;> positivity

private theorem intrinsicAlternatingCorrelation_q01Plus21_nonneg_sharp
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    0 ≤ intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21 t := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
  have hfour : 0 ≤ 4 - t ^ 2 := by nlinarith [sq_nonneg (2 - t)]
  rw [show t * (2 - t) * ((1 / 2 : ℝ) * t + (1 / 4 : ℝ) * t ^ 2) =
      (1 / 4 : ℝ) * t ^ 2 * (4 - t ^ 2) by ring]
  positivity

private theorem intrinsicAlternatingCorrelation_q01Minus21_nonneg_sharp
    {t : ℝ} (ht0 : 0 ≤ t) (_ht2 : t ≤ 2) :
    0 ≤ intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21 t := by
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
  rw [show t * (2 - t) *
      (2 - (1 / 2 : ℝ) * t - (1 / 4 : ℝ) * t ^ 2) =
        t * (2 - t) ^ 2 * (1 + t / 4) by ring]
  positivity

private theorem abs_intrinsicAlternatingQ03Plus23_le_two_sharp
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |intrinsicAlternatingQ03Plus23 t| ≤ 2 := by
  let x : ℝ := t / 2
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hx1 : 0 ≤ 1 - x := by dsimp only [x]; linarith
  have hlower : -2 ≤ intrinsicAlternatingQ03Plus23 t := by
    have hdecomp : intrinsicAlternatingQ03Plus23 t + 2 =
        4 * (1 - x) ^ 4 + 9 * x * (1 - x) ^ 3 +
          6 * x ^ 2 * (1 - x) ^ 2 +
          3 * x ^ 3 * (1 - x) + 4 * x ^ 4 := by
      dsimp only [x]
      unfold intrinsicAlternatingQ03Plus23
      ring
    have hsum : 0 ≤
        4 * (1 - x) ^ 4 + 9 * x * (1 - x) ^ 3 +
          6 * x ^ 2 * (1 - x) ^ 2 +
          3 * x ^ 3 * (1 - x) + 4 * x ^ 4 := by positivity
    linarith [hdecomp]
  have hupper : intrinsicAlternatingQ03Plus23 t ≤ 2 := by
    have hdecomp : 2 - intrinsicAlternatingQ03Plus23 t =
        t * (2 - t) * (t ^ 2 / 8 + t / 2 + 7 / 4) := by
      unfold intrinsicAlternatingQ03Plus23
      ring
    have hthird : 0 ≤ t ^ 2 / 8 + t / 2 + 7 / 4 := by
      nlinarith [sq_nonneg t]
    have hnonneg : 0 ≤
        t * (2 - t) * (t ^ 2 / 8 + t / 2 + 7 / 4) :=
      mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht2)) hthird
    linarith [hdecomp]
  exact (abs_le).2 ⟨hlower, hupper⟩

private theorem abs_intrinsicAlternatingQ03Minus23_le_one_sharp
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |intrinsicAlternatingQ03Minus23 t| ≤ 1 := by
  let x : ℝ := t / 2
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hx1 : 0 ≤ 1 - x := by dsimp only [x]; linarith
  have hlower : -1 ≤ intrinsicAlternatingQ03Minus23 t := by
    have hdecomp : intrinsicAlternatingQ03Minus23 t + 1 =
        (1 - x) ^ 4 + x * (1 - x) ^ 3 +
          4 * x ^ 2 * (1 - x) ^ 2 +
          7 * x ^ 3 * (1 - x) + x ^ 4 := by
      dsimp only [x]
      unfold intrinsicAlternatingQ03Minus23
      ring
    have hsum : 0 ≤
        (1 - x) ^ 4 + x * (1 - x) ^ 3 +
          4 * x ^ 2 * (1 - x) ^ 2 +
          7 * x ^ 3 * (1 - x) + x ^ 4 := by positivity
    linarith [hdecomp]
  have hupper : intrinsicAlternatingQ03Minus23 t ≤ 1 := by
    have hdecomp : 1 - intrinsicAlternatingQ03Minus23 t =
        (1 - x) ^ 4 + 7 * x * (1 - x) ^ 3 +
          8 * x ^ 2 * (1 - x) ^ 2 +
          x ^ 3 * (1 - x) + x ^ 4 := by
      dsimp only [x]
      unfold intrinsicAlternatingQ03Minus23
      ring
    have hsum : 0 ≤
        (1 - x) ^ 4 + 7 * x * (1 - x) ^ 3 +
          8 * x ^ 2 * (1 - x) ^ 2 +
          x ^ 3 * (1 - x) + x ^ 4 := by positivity
    linarith [hdecomp]
  exact (abs_le).2 ⟨hlower, hupper⟩

private theorem intrinsicAlternatingSharpRegularError_bounds_of_nonneg
    (q : ℝ → ℝ) (hq : Continuous q)
    (hcorrelation : ∀ t, 0 ≤ t → t ≤ 2 →
      0 ≤ intrinsicAlternatingCorrelation q t)
    (L U : ℝ)
    (hL : (∫ t : ℝ in 0..2,
      intrinsicAlternatingRationalLowerMagnitude t *
        intrinsicAlternatingCorrelation q t) < L)
    (hU : (∫ t : ℝ in 0..2,
      intrinsicAlternatingRationalUpperMagnitude t *
        intrinsicAlternatingCorrelation q t) < U) :
    -L < intrinsicAlternatingSharpRegularError q ∧
      intrinsicAlternatingSharpRegularError q < U := by
  let D : ℝ → ℝ := intrinsicAlternatingCorrelation q
  let R : ℝ → ℝ := fun t ↦
    yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      intrinsicAlternatingKernelPolynomial6 t
  have hD : Continuous D := by
    dsimp only [D]
    unfold intrinsicAlternatingCorrelation
    fun_prop
  have hRI : IntervalIntegrable (fun t ↦ R t * D t) volume 0 2 := by
    dsimp only [R]
    exact intervalIntegrable_intrinsicAlternatingSharpResidual D hD
  have hLowerI : IntervalIntegrable
      (fun t ↦ -intrinsicAlternatingRationalLowerMagnitude t * D t)
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [D]
    unfold intrinsicAlternatingRationalLowerMagnitude
      intrinsicAlternatingCorrelation
    fun_prop
  have hUpperI : IntervalIntegrable
      (fun t ↦ intrinsicAlternatingRationalUpperMagnitude t * D t)
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [D]
    unfold intrinsicAlternatingRationalUpperMagnitude
      intrinsicAlternatingCorrelation
    fun_prop
  have hlowerIntegral :
      (∫ t : ℝ in 0..2,
          -intrinsicAlternatingRationalLowerMagnitude t * D t) ≤
        ∫ t : ℝ in 0..2, R t * D t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hLowerI hRI
    intro t ht
    have hres := intrinsicAlternatingKernel_residual_envelope ht.1 ht.2
    have hrat := intrinsicAlternatingResidualMagnitude_le_rational ht.1 ht.2
    have hD0 : 0 ≤ D t := by
      dsimp only [D]
      exact hcorrelation t ht.1 ht.2
    apply mul_le_mul_of_nonneg_right _ hD0
    dsimp only [R]
    linarith
  have hupperIntegral :
      (∫ t : ℝ in 0..2, R t * D t) ≤
        ∫ t : ℝ in 0..2,
          intrinsicAlternatingRationalUpperMagnitude t * D t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hRI hUpperI
    intro t ht
    have hres := intrinsicAlternatingKernel_residual_envelope ht.1 ht.2
    have hrat := intrinsicAlternatingResidualMagnitude_le_rational ht.1 ht.2
    have hD0 : 0 ≤ D t := by
      dsimp only [D]
      exact hcorrelation t ht.1 ht.2
    apply mul_le_mul_of_nonneg_right _ hD0
    dsimp only [R]
    linarith
  have hnegIntegral :
      (∫ t : ℝ in 0..2,
          -intrinsicAlternatingRationalLowerMagnitude t * D t) =
        -(∫ t : ℝ in 0..2,
          intrinsicAlternatingRationalLowerMagnitude t * D t) := by
    rw [show (fun t : ℝ ↦
        -intrinsicAlternatingRationalLowerMagnitude t * D t) =
      fun t ↦ -(intrinsicAlternatingRationalLowerMagnitude t * D t) by
      funext t
      ring,
      intervalIntegral.integral_neg]
  have herr := intrinsicAlternatingSharpRegularError_eq_integral q hq
  dsimp only [D, R] at hlowerIntegral hupperIntegral hnegIntegral hL hU
  rw [herr]
  constructor <;> linarith

theorem intrinsicAlternatingSharpRegularError_q01Plus21_bounds :
    (-(99 / 2000000) : ℝ) <
        intrinsicAlternatingSharpRegularError intrinsicAlternatingQ01Plus21 ∧
      intrinsicAlternatingSharpRegularError intrinsicAlternatingQ01Plus21 <
        (1 / 2000000 : ℝ) := by
  exact intrinsicAlternatingSharpRegularError_bounds_of_nonneg
    intrinsicAlternatingQ01Plus21
    (by unfold intrinsicAlternatingQ01Plus21; fun_prop)
    (fun _ ht0 ht2 ↦
      intrinsicAlternatingCorrelation_q01Plus21_nonneg_sharp ht0 ht2)
    (99 / 2000000) (1 / 2000000)
    integral_rational_lower_q01Plus21 integral_rational_upper_q01Plus21

theorem intrinsicAlternatingSharpRegularError_q01Minus21_bounds :
    (-(3 / 100000) : ℝ) <
        intrinsicAlternatingSharpRegularError intrinsicAlternatingQ01Minus21 ∧
      intrinsicAlternatingSharpRegularError intrinsicAlternatingQ01Minus21 <
        (1 / 3000000 : ℝ) := by
  exact intrinsicAlternatingSharpRegularError_bounds_of_nonneg
    intrinsicAlternatingQ01Minus21
    (by unfold intrinsicAlternatingQ01Minus21; fun_prop)
    (fun _ ht0 ht2 ↦
      intrinsicAlternatingCorrelation_q01Minus21_nonneg_sharp ht0 ht2)
    (3 / 100000) (1 / 3000000)
    integral_rational_lower_q01Minus21 integral_rational_upper_q01Minus21

private theorem intrinsicAlternatingSharpRegularError_lt_refined_of_nonneg
    (q : ℝ → ℝ) (hq : Continuous q)
    (hcorrelation : ∀ t, 0 ≤ t → t ≤ 2 →
      0 ≤ intrinsicAlternatingCorrelation q t)
    (U : ℝ)
    (hU : (∫ t : ℝ in 0..2,
      intrinsicAlternatingRefinedRationalUpper t *
        intrinsicAlternatingCorrelation q t) < U) :
    intrinsicAlternatingSharpRegularError q < U := by
  let D : ℝ → ℝ := intrinsicAlternatingCorrelation q
  let R : ℝ → ℝ := fun t ↦
    yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      intrinsicAlternatingKernelPolynomial6 t
  have hD : Continuous D := by
    dsimp only [D]
    unfold intrinsicAlternatingCorrelation
    fun_prop
  have hRI : IntervalIntegrable (fun t ↦ R t * D t) volume 0 2 := by
    dsimp only [R]
    exact intervalIntegrable_intrinsicAlternatingSharpResidual D hD
  have hUpperI : IntervalIntegrable
      (fun t ↦ intrinsicAlternatingRefinedRationalUpper t * D t)
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [D]
    unfold intrinsicAlternatingRefinedRationalUpper intrinsicAlternatingCorrelation
    fun_prop
  have hupperIntegral :
      (∫ t : ℝ in 0..2, R t * D t) ≤
        ∫ t : ℝ in 0..2,
          intrinsicAlternatingRefinedRationalUpper t * D t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hRI hUpperI
    intro t ht
    have hres :=
      intrinsicAlternatingKernel_residual_le_refinedRationalUpper ht.1 ht.2
    have hD0 : 0 ≤ D t := by
      dsimp only [D]
      exact hcorrelation t ht.1 ht.2
    apply mul_le_mul_of_nonneg_right _ hD0
    dsimp only [R]
    exact hres
  have herr := intrinsicAlternatingSharpRegularError_eq_integral q hq
  dsimp only [D, R] at hupperIntegral hU
  rw [herr]
  exact hupperIntegral.trans_lt hU

theorem intrinsicAlternatingSharpRegularError_q01Plus21_refined_bounds :
    (-(99 / 2000000) : ℝ) <
        intrinsicAlternatingSharpRegularError intrinsicAlternatingQ01Plus21 ∧
      intrinsicAlternatingSharpRegularError intrinsicAlternatingQ01Plus21 <
        (-3 / 100000 : ℝ) := by
  constructor
  · exact intrinsicAlternatingSharpRegularError_q01Plus21_bounds.1
  · exact intrinsicAlternatingSharpRegularError_lt_refined_of_nonneg
      intrinsicAlternatingQ01Plus21
      (by unfold intrinsicAlternatingQ01Plus21; fun_prop)
      (fun _ ht0 ht2 ↦
        intrinsicAlternatingCorrelation_q01Plus21_nonneg_sharp ht0 ht2)
      (-3 / 100000) integral_refined_upper_q01Plus21

theorem intrinsicAlternatingSharpRegularError_q01Minus21_refined_bounds :
    (-(3 / 100000) : ℝ) <
        intrinsicAlternatingSharpRegularError intrinsicAlternatingQ01Minus21 ∧
      intrinsicAlternatingSharpRegularError intrinsicAlternatingQ01Minus21 <
        (-9 / 500000 : ℝ) := by
  constructor
  · exact intrinsicAlternatingSharpRegularError_q01Minus21_bounds.1
  · exact intrinsicAlternatingSharpRegularError_lt_refined_of_nonneg
      intrinsicAlternatingQ01Minus21
      (by unfold intrinsicAlternatingQ01Minus21; fun_prop)
      (fun _ ht0 ht2 ↦
        intrinsicAlternatingCorrelation_q01Minus21_nonneg_sharp ht0 ht2)
      (-9 / 500000) integral_refined_upper_q01Minus21

private theorem abs_intrinsicAlternatingSharpRegularError_lt_of_abs_q_le
    (q : ℝ → ℝ) (hq : Continuous q) (M B : ℝ)
    (hqbound : ∀ t, 0 ≤ t → t ≤ 2 → |q t| ≤ M)
    (hmajor : (∫ t : ℝ in 0..2,
      (intrinsicAlternatingRationalLowerMagnitude t +
        intrinsicAlternatingRationalUpperMagnitude t) *
          (M * (t * (2 - t)))) < B) :
    |intrinsicAlternatingSharpRegularError q| < B := by
  let D : ℝ → ℝ := intrinsicAlternatingCorrelation q
  let R : ℝ → ℝ := fun t ↦
    yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      intrinsicAlternatingKernelPolynomial6 t
  let G : ℝ → ℝ := fun t ↦
    (intrinsicAlternatingRationalLowerMagnitude t +
      intrinsicAlternatingRationalUpperMagnitude t) *
        (M * (t * (2 - t)))
  have hD : Continuous D := by
    dsimp only [D]
    unfold intrinsicAlternatingCorrelation
    fun_prop
  have hRI : IntervalIntegrable (fun t ↦ R t * D t) volume 0 2 := by
    dsimp only [R]
    exact intervalIntegrable_intrinsicAlternatingSharpResidual D hD
  have hGI : IntervalIntegrable G volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [G]
    unfold intrinsicAlternatingRationalLowerMagnitude
      intrinsicAlternatingRationalUpperMagnitude
    fun_prop
  have hmono :
      (∫ t : ℝ in 0..2, |R t * D t|) ≤ ∫ t : ℝ in 0..2, G t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hRI.abs hGI
    intro t ht
    have hres := intrinsicAlternatingKernel_residual_envelope ht.1 ht.2
    have hrat := intrinsicAlternatingResidualMagnitude_le_rational ht.1 ht.2
    have hrat0 := intrinsicAlternatingRationalMagnitude_nonneg ht.1 ht.2
    have hRabs : |R t| ≤
        intrinsicAlternatingRationalLowerMagnitude t +
          intrinsicAlternatingRationalUpperMagnitude t := by
      rw [abs_le]
      dsimp only [R]
      constructor <;> linarith
    have hcommon0 : 0 ≤ t * (2 - t) :=
      mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
    have hDabs : |D t| ≤ M * (t * (2 - t)) := by
      dsimp only [D]
      unfold intrinsicAlternatingCorrelation
      rw [abs_mul, abs_of_nonneg hcommon0]
      have hq := hqbound t ht.1 ht.2
      nlinarith
    dsimp only [G]
    rw [abs_mul]
    exact mul_le_mul hRabs hDabs (abs_nonneg (D t))
      (add_nonneg hrat0.1 hrat0.2)
  have habs :
      |∫ t : ℝ in 0..2, R t * D t| ≤
        ∫ t : ℝ in 0..2, |R t * D t| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have herr := intrinsicAlternatingSharpRegularError_eq_integral q hq
  dsimp only [G, R, D] at hmono hmajor habs
  rw [herr]
  exact lt_of_le_of_lt (habs.trans hmono) hmajor

/-- A reusable uniform version of the sharp alternating remainder bound.
The degree-six kernel residual is charged once to the complete correlation
polynomial; no entrywise decomposition or interval subdivision is used. -/
theorem abs_intrinsicAlternatingSharpRegularError_lt_of_uniform_q_bound
    (q : ℝ → ℝ) (hq : Continuous q) (M : ℝ) (hM : 0 < M)
    (hqbound : ∀ t, 0 ≤ t → t ≤ 2 → |q t| ≤ M) :
    |intrinsicAlternatingSharpRegularError q| < M / 25000 := by
  apply abs_intrinsicAlternatingSharpRegularError_lt_of_abs_q_le
    q hq M (M / 25000) hqbound
  have hbase := integral_rational_sum_q03Minus23_majorant
  rw [show (fun t : ℝ ↦
      (intrinsicAlternatingRationalLowerMagnitude t +
        intrinsicAlternatingRationalUpperMagnitude t) *
          (M * (t * (2 - t)))) =
    fun t ↦ M *
      ((intrinsicAlternatingRationalLowerMagnitude t +
        intrinsicAlternatingRationalUpperMagnitude t) *
          (t * (2 - t))) by
    funext t
    ring,
    intervalIntegral.integral_const_mul]
  calc
    M * (∫ t : ℝ in 0..2,
        (intrinsicAlternatingRationalLowerMagnitude t +
          intrinsicAlternatingRationalUpperMagnitude t) *
            (t * (2 - t))) < M * (1 / 25000 : ℝ) :=
      mul_lt_mul_of_pos_left hbase hM
    _ = M / 25000 := by ring

theorem abs_intrinsicAlternatingSharpRegularError_q03Plus23_lt :
    |intrinsicAlternatingSharpRegularError intrinsicAlternatingQ03Plus23| <
      (1 / 12000 : ℝ) := by
  apply abs_intrinsicAlternatingSharpRegularError_lt_of_abs_q_le
    intrinsicAlternatingQ03Plus23
    (by unfold intrinsicAlternatingQ03Plus23; fun_prop) 2 (1 / 12000)
    (fun _ ht0 ht2 ↦ abs_intrinsicAlternatingQ03Plus23_le_two_sharp ht0 ht2)
  simpa only [mul_assoc] using integral_rational_sum_q03Plus23_majorant

theorem abs_intrinsicAlternatingSharpRegularError_q03Minus23_lt :
    |intrinsicAlternatingSharpRegularError intrinsicAlternatingQ03Minus23| <
      (1 / 25000 : ℝ) := by
  apply abs_intrinsicAlternatingSharpRegularError_lt_of_abs_q_le
    intrinsicAlternatingQ03Minus23
    (by unfold intrinsicAlternatingQ03Minus23; fun_prop) 1 (1 / 25000)
    (fun _ ht0 ht2 ↦ abs_intrinsicAlternatingQ03Minus23_le_one_sharp ht0 ht2)
  simpa only [one_mul] using integral_rational_sum_q03Minus23_majorant

private theorem intrinsicAlternatingPolynomialCorrection_rational_bounds :
    (-499701 / 1000000000 : ℝ) <
        intrinsicAlternatingPolynomialCorrection intrinsicAlternatingQ01Plus21 ∧
      intrinsicAlternatingPolynomialCorrection intrinsicAlternatingQ01Plus21 <
        (-499699 / 1000000000 : ℝ) ∧
    (-746714 / 1000000000 : ℝ) <
        intrinsicAlternatingPolynomialCorrection intrinsicAlternatingQ01Minus21 ∧
      intrinsicAlternatingPolynomialCorrection intrinsicAlternatingQ01Minus21 <
        (-746711 / 1000000000 : ℝ) ∧
    (55858 / 1000000000 : ℝ) <
        intrinsicAlternatingPolynomialCorrection intrinsicAlternatingQ03Plus23 ∧
      intrinsicAlternatingPolynomialCorrection intrinsicAlternatingQ03Plus23 <
        (55859 / 1000000000 : ℝ) ∧
    (52535 / 1000000000 : ℝ) <
        intrinsicAlternatingPolynomialCorrection intrinsicAlternatingQ03Minus23 ∧
      intrinsicAlternatingPolynomialCorrection intrinsicAlternatingQ03Minus23 <
        (52536 / 1000000000 : ℝ) := by
  let L : ℝ := 34657359027 / 100000000000
  let U : ℝ := 34657359029 / 100000000000
  have hAL : L ≤ yoshidaEndpointA := by
    dsimp only [L]
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.1]
  have hAU : yoshidaEndpointA ≤ U := by
    dsimp only [U]
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.2]
  have hL0 : 0 ≤ L := by norm_num [L]
  have hA0 : 0 ≤ yoshidaEndpointA := yoshidaEndpointA_pos.le
  have hLpow (n : ℕ) : L ^ n ≤ yoshidaEndpointA ^ n :=
    pow_le_pow_left₀ hL0 hAL n
  have hUpow (n : ℕ) : yoshidaEndpointA ^ n ≤ U ^ n :=
    pow_le_pow_left₀ hA0 hAU n
  rw [intrinsicAlternatingPolynomialCorrection_q01Plus21,
    intrinsicAlternatingPolynomialCorrection_q01Minus21,
    intrinsicAlternatingPolynomialCorrection_q03Plus23,
    intrinsicAlternatingPolynomialCorrection_q03Minus23]
  unfold intrinsicAlternatingKernelCoeff1 intrinsicAlternatingKernelCoeff3
    intrinsicAlternatingKernelCoeff5
  have hL2 := hLpow 2
  have hU2 := hUpow 2
  have hL3 := hLpow 3
  have hU3 := hUpow 3
  have hL4 := hLpow 4
  have hU4 := hUpow 4
  have hL5 := hLpow 5
  have hU5 := hUpow 5
  have hL6 := hLpow 6
  have hU6 := hUpow 6
  have hL7 := hLpow 7
  have hU7 := hUpow 7
  norm_num [L, U] at hL2 hU2 hL3 hU3 hL4 hU4 hL5 hU5 hL6 hU6 hL7 hU7 ⊢
  ring_nf at ⊢
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem log_three_div_sqrt_three_sharp_bounds :
    (6342841 / 10000000 : ℝ) < Real.log 3 / Real.sqrt 3 ∧
      Real.log 3 / Real.sqrt 3 < (6342842 / 10000000 : ℝ) := by
  have hlog2 := strict_log_two_fine_bounds
  have hlog32 := strict_log_three_halves_fine_bounds
  have hlog3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    calc
      Real.log 3 = Real.log (2 * (3 / 2 : ℝ)) := by norm_num
      _ = Real.log 2 + Real.log (3 / 2) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  have hsSq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsLower : (17320508 / 10000000 : ℝ) < Real.sqrt 3 := by
    nlinarith
  have hsUpper : Real.sqrt 3 < (17320509 / 10000000 : ℝ) := by
    nlinarith
  rw [lt_div_iff₀ hspos, div_lt_iff₀ hspos, hlog3]
  constructor <;> nlinarith

private theorem intrinsicAlternatingPrimeCorrelation_sharp_bounds :
    (900369 / 1000000 : ℝ) <
        intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
          (factorTwoPrimeShift / yoshidaEndpointA) < (900377 / 1000000 : ℝ) ∧
    (1041871 / 1000000 : ℝ) <
        intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
          (factorTwoPrimeShift / yoshidaEndpointA) < (1041886 / 1000000 : ℝ) ∧
    (-421171 / 1000000 : ℝ) <
        intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
          (factorTwoPrimeShift / yoshidaEndpointA) < (-421168 / 1000000 : ℝ) ∧
    (5704 / 1000000 : ℝ) <
        intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
          (factorTwoPrimeShift / yoshidaEndpointA) < (5713 / 1000000 : ℝ) := by
  let τ : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let L : ℝ := 116992 / 100000
  let U : ℝ := 116993 / 100000
  have hτ := factorTwoPrimeRatio_sharp_bounds
  have hL : L ≤ τ := by dsimp only [L, τ]; exact hτ.1.le
  have hU : τ ≤ U := by dsimp only [U, τ]; exact hτ.2.le
  have hL0 : 0 ≤ L := by norm_num [L]
  have hτ0 : 0 ≤ τ := hL0.trans hL
  have hLn (n : ℕ) : L ^ n ≤ τ ^ n := pow_le_pow_left₀ hL0 hL n
  have hUn (n : ℕ) : τ ^ n ≤ U ^ n := pow_le_pow_left₀ hτ0 hU n
  have hL2 := hLn 2
  have hU2 := hUn 2
  have hL3 := hLn 3
  have hU3 := hUn 3
  have hL4 := hLn 4
  have hU4 := hUn 4
  have hL6 := hLn 6
  have hU6 := hUn 6
  have hp01Lower : (900369 / 1000000 : ℝ) < τ ^ 2 - τ ^ 4 / 4 := by
    norm_num [L, U] at hL2 hU4 ⊢
    nlinarith
  have hp01Upper : τ ^ 2 - τ ^ 4 / 4 < (900377 / 1000000 : ℝ) := by
    norm_num [L, U] at hU2 hL4 ⊢
    nlinarith
  have hm01Lower : (1041871 / 1000000 : ℝ) <
      4 * τ - 3 * τ ^ 2 + τ ^ 4 / 4 := by
    norm_num [L, U] at hL hU2 hL4 ⊢
    nlinarith
  have hm01Upper : 4 * τ - 3 * τ ^ 2 + τ ^ 4 / 4 <
      (1041886 / 1000000 : ℝ) := by
    norm_num [L, U] at hU hL2 hU4 ⊢
    nlinarith
  have hp03Lower : (-421171 / 1000000 : ℝ) <
      4 * τ - 9 * τ ^ 2 + 5 * τ ^ 3 - τ ^ 4 / 4 - τ ^ 6 / 8 := by
    norm_num [L, U] at hL hU2 hL3 hU4 hU6 ⊢
    nlinarith
  have hp03Upper :
      4 * τ - 9 * τ ^ 2 + 5 * τ ^ 3 - τ ^ 4 / 4 - τ ^ 6 / 8 <
        (-421168 / 1000000 : ℝ) := by
    norm_num [L, U] at hU hL2 hU3 hL4 hL6 ⊢
    nlinarith
  have hm03Lower : (5704 / 1000000 : ℝ) <
      -3 * τ ^ 2 + 5 * τ ^ 3 - (9 / 4 : ℝ) * τ ^ 4 + τ ^ 6 / 8 := by
    norm_num [L, U] at hU2 hL3 hU4 hL6 ⊢
    nlinarith
  have hm03Upper :
      -3 * τ ^ 2 + 5 * τ ^ 3 - (9 / 4 : ℝ) * τ ^ 4 + τ ^ 6 / 8 <
        (5713 / 1000000 : ℝ) := by
    norm_num [L, U] at hL2 hU3 hL4 hU6 ⊢
    nlinarith
  dsimp only [τ] at hp01Lower hp01Upper hm01Lower hm01Upper
  dsimp only [τ] at hp03Lower hp03Upper hm03Lower hm03Upper
  unfold intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
    intrinsicAlternatingQ01Minus21 intrinsicAlternatingQ03Plus23
    intrinsicAlternatingQ03Minus23
  constructor
  · convert hp01Lower using 1; ring
  constructor
  · convert hp01Upper using 1; ring
  constructor
  · convert hm01Lower using 1; ring
  constructor
  · convert hm01Upper using 1; ring
  constructor
  · convert hp03Lower using 1; ring
  constructor
  · convert hp03Upper using 1; ring
  constructor
  · convert hm03Lower using 1; ring
  · convert hm03Upper using 1; ring

private theorem intrinsicAlternatingPrimeProduct_sharp_bounds :
    (5710897 / 10000000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
      (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
            (factorTwoPrimeShift / yoshidaEndpointA) < (5710950 / 10000000 : ℝ) ∧
    (6608422 / 10000000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
      (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
            (factorTwoPrimeShift / yoshidaEndpointA) < (6608519 / 10000000 : ℝ) ∧
    (-2671422 / 10000000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
      (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ03Plus23
            (factorTwoPrimeShift / yoshidaEndpointA) < (-2671401 / 10000000 : ℝ) ∧
    (36179 / 10000000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
      (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
            (factorTwoPrimeShift / yoshidaEndpointA) < (36237 / 10000000 : ℝ) := by
  have hb := log_three_div_sqrt_three_sharp_bounds
  have hbpos : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  rcases intrinsicAlternatingPrimeCorrelation_sharp_bounds with
    ⟨hpL, hpU, hmL, hmU, hp3L, hp3U, hm3L, hm3U⟩
  constructor
  · calc
      _ < (6342841 / 10000000 : ℝ) * (900369 / 1000000) := by norm_num
      _ < (Real.log 3 / Real.sqrt 3) * (900369 / 1000000) := by
        exact mul_lt_mul_of_pos_right hb.1 (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hpL hbpos
  constructor
  · calc
      _ < (6342842 / 10000000 : ℝ) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ01Plus21
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hb.2 (by linarith)
      _ < (6342842 / 10000000 : ℝ) * (900377 / 1000000) :=
        mul_lt_mul_of_pos_left hpU (by norm_num)
      _ < _ := by norm_num
  constructor
  · calc
      _ < (6342841 / 10000000 : ℝ) * (1041871 / 1000000) := by norm_num
      _ < (Real.log 3 / Real.sqrt 3) * (1041871 / 1000000) :=
        mul_lt_mul_of_pos_right hb.1 (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hmL hbpos
  constructor
  · calc
      _ < (6342842 / 10000000 : ℝ) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ01Minus21
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hb.2 (by linarith)
      _ < (6342842 / 10000000 : ℝ) * (1041886 / 1000000) :=
        mul_lt_mul_of_pos_left hmU (by norm_num)
      _ < _ := by norm_num
  constructor
  · calc
      _ < (6342842 / 10000000 : ℝ) * (-421171 / 1000000) := by norm_num
      _ < (Real.log 3 / Real.sqrt 3) * (-421171 / 1000000) := by
        exact mul_lt_mul_of_neg_right hb.2 (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hp3L hbpos
  constructor
  · calc
      _ < (Real.log 3 / Real.sqrt 3) * (-421168 / 1000000) :=
        mul_lt_mul_of_pos_left hp3U hbpos
      _ < (6342841 / 10000000 : ℝ) * (-421168 / 1000000) := by
        exact mul_lt_mul_of_neg_right hb.1 (by norm_num)
      _ < _ := by norm_num
  constructor
  · calc
      _ < (6342841 / 10000000 : ℝ) * (5704 / 1000000) := by norm_num
      _ < (Real.log 3 / Real.sqrt 3) * (5704 / 1000000) :=
        mul_lt_mul_of_pos_right hb.1 (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hm3L hbpos
  · calc
      _ < (6342842 / 10000000 : ℝ) *
          intrinsicAlternatingCorrelation intrinsicAlternatingQ03Minus23
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hb.2 (by linarith)
      _ < (6342842 / 10000000 : ℝ) * (5713 / 1000000) :=
        mul_lt_mul_of_pos_left hm3U (by norm_num)
      _ < _ := by norm_num

/-- Structural proof of the four sharp alternating intervals used by the
rational Schur argument. -/
theorem factorTwoIntrinsicAlternatingSharpBounds :
    FactorTwoIntrinsicAlternatingSharpBounds := by
  unfold FactorTwoIntrinsicAlternatingSharpBounds
  rcases intrinsicAlternatingPolynomialCorrection_rational_bounds with
    ⟨hc1pL, hc1pU, hc1mL, hc1mU, hc3pL, hc3pU, hc3mL, hc3mU⟩
  rcases intrinsicAlternatingPrimeProduct_sharp_bounds with
    ⟨hp1pL, hp1pU, hp1mL, hp1mU, hp3pL, hp3pU, hp3mL, hp3mU⟩
  rcases intrinsicAlternatingSharpRegularError_q01Plus21_refined_bounds with
    ⟨he1pL, he1pU⟩
  rcases intrinsicAlternatingSharpRegularError_q01Minus21_refined_bounds with
    ⟨he1mL, he1mU⟩
  have he3p := abs_intrinsicAlternatingSharpRegularError_q03Plus23_lt
  have he3m := abs_intrinsicAlternatingSharpRegularError_q03Minus23_lt
  rw [abs_lt] at he3p he3m
  rcases he3p with ⟨he3pL, he3pU⟩
  rcases he3m with ⟨he3mL, he3mU⟩
  have hlog := strict_log_two_fine_bounds
  have hs1 := intrinsicAlternating01_add_21_eq_sharpModel
  have hd1 := intrinsicAlternating01_sub_21_eq_sharpModel
  have hs3 := intrinsicAlternating03_add_23_eq_sharpModel
  have hd3 := intrinsicAlternating03_sub_23_eq_sharpModel
  unfold intrinsicAlternatingSharpArchModel at hs1 hd1 hs3 hd3
  rw [intrinsicAlternatingArchModel_q01Plus21] at hs1
  rw [intrinsicAlternatingArchModel_q01Minus21] at hd1
  rw [intrinsicAlternatingArchModel_q03Plus23] at hs3
  rw [intrinsicAlternatingArchModel_q03Minus23] at hd3
  constructor
  · linarith only [hs1, he1pL, hc1pL, hp1pU]
  constructor
  · linarith only [hs1, he1pU, hc1pU, hp1pL]
  constructor
  · linarith only [hd1, hlog.1, he1mL, hc1mL, hp1mU]
  constructor
  · linarith only [hd1, hlog.2, he1mU, hc1mU, hp1mL]
  constructor
  · linarith only [hs3, hlog.1, he3pL, hc3pL, hp3pU]
  constructor
  · linarith only [hs3, hlog.2, he3pU, hc3pU, hp3pL]
  constructor
  · linarith only [hd3, hlog.1, he3mL, hc3mL, hp3mU]
  · linarith only [hd3, hlog.2, he3mU, hc3mU, hp3mL]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
