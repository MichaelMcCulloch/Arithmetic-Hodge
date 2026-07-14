import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01MidpointReserve

noncomputable section

open CenteredEndpointCorrelation
open YoshidaConstantBounds
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# A structural midpoint reserve for the Step01 determinant slope

Adding back the diagonal padding in the negative Taylor Gram exposes its
un-padded midpoint.  The reserve below is proved by one monotonicity argument
on rational entry enclosures.  No phase subdivision, sampling, or finite
certificate is used.
-/

/-- Constant entry of the un-padded negative Taylor midpoint. -/
def step01Midpoint00 : ℝ :=
  evenNegativePerturbationTaylor00 + 3 / 4000

/-- Mixed entry of the un-padded negative Taylor midpoint. -/
def step01Midpoint02 : ℝ :=
  evenNegativePerturbationTaylor02

/-- Degree-two entry of the un-padded negative Taylor midpoint. -/
def step01Midpoint22 : ℝ :=
  evenNegativePerturbationTaylor22 + 3 / 20000

/-! ## Exact polynomial moments and midpoint enclosures -/

private theorem step01_integral_polynomialDifference_evenProfile (c d : ℝ) :
    (∫ t : ℝ in 0..2,
      poleFreePolynomialDifference t *
        centeredEndpointCorrelation
          (factorTwoEvenStructuralLowProfile c d) t) =
      evenPositivePolynomialMoment00 * c ^ 2 +
        2 * evenPositivePolynomialMoment02 * c * d +
        evenPositivePolynomialMoment22 * d ^ 2 := by
  have h00 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * evenStructuralCorrelation00 t)
      volume 0 2 :=
    (continuous_poleFreePolynomialDifference.mul
      (by unfold evenStructuralCorrelation00; fun_prop)).intervalIntegrable 0 2
  have h02 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * evenStructuralCorrelation02 t)
      volume 0 2 :=
    (continuous_poleFreePolynomialDifference.mul
      (by unfold evenStructuralCorrelation02; fun_prop)).intervalIntegrable 0 2
  have h22 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * evenStructuralCorrelation22 t)
      volume 0 2 :=
    (continuous_poleFreePolynomialDifference.mul
      (by unfold evenStructuralCorrelation22; fun_prop)).intervalIntegrable 0 2
  simp_rw [centeredEndpointCorrelation_evenStructuralProfile]
  rw [show (fun t : ℝ ↦
      poleFreePolynomialDifference t *
        (c ^ 2 * evenStructuralCorrelation00 t +
          2 * c * d * evenStructuralCorrelation02 t +
          d ^ 2 * evenStructuralCorrelation22 t)) =
      fun t ↦ c ^ 2 *
          (poleFreePolynomialDifference t * evenStructuralCorrelation00 t) +
        (2 * c * d) *
          (poleFreePolynomialDifference t * evenStructuralCorrelation02 t) +
        d ^ 2 *
          (poleFreePolynomialDifference t * evenStructuralCorrelation22 t) by
    funext t
    ring,
    intervalIntegral.integral_add
      ((h00.const_mul (c ^ 2)).add (h02.const_mul (2 * c * d)))
      (h22.const_mul (d ^ 2)),
    intervalIntegral.integral_add (h00.const_mul (c ^ 2))
      (h02.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_polynomialDifference_mul_evenCorrelations.1,
    integral_polynomialDifference_mul_evenCorrelations.2.1,
    integral_polynomialDifference_mul_evenCorrelations.2.2]
  ring

private theorem step01_publicRegularError_expansion (c d : ℝ) :
    evenStructuralRegularError
        (centeredEndpointCorrelation
          (factorTwoEvenStructuralLowProfile c d)) =
      poleFreeAnalyticError
          (centeredEndpointCorrelation
            (factorTwoEvenStructuralLowProfile c d)) +
        evenPositivePolynomialMoment00 * c ^ 2 +
        2 * evenPositivePolynomialMoment02 * c * d +
        evenPositivePolynomialMoment22 * d ^ 2 := by
  rw [evenStructuralRegularError_eq_analytic_add_polynomial
    (centeredEndpointCorrelation (factorTwoEvenStructuralLowProfile c d))
    (continuous_centeredEndpointCorrelation_of_continuous
      (factorTwoEvenStructuralLowProfile c d)
      (continuous_factorTwoEvenStructuralLowProfile c d)),
    step01_integral_polynomialDifference_evenProfile]
  ring

/-- Removing the Taylor padding leaves exactly the negative of the public
kernel-plus-polynomial midpoint used at the positive endpoint. -/
theorem step01Midpoint_eq_kernel_sub_positiveMoment :
    step01Midpoint00 =
        -evenStructuralKernelBase00 - evenPositivePolynomialMoment00 ∧
      step01Midpoint02 =
        -evenStructuralKernelBase02 - evenPositivePolynomialMoment02 ∧
      step01Midpoint22 =
        -evenStructuralKernelBase22 - evenPositivePolynomialMoment22 := by
  constructor
  · have hprivate := evenStructuralRegularError_profile_sharp_expansion 1 0
    have hpublic := step01_publicRegularError_expansion 1 0
    unfold step01Midpoint00 evenNegativePerturbationTaylor00
    norm_num at hprivate hpublic ⊢
    linarith
  constructor
  · have hprivatePlus := evenStructuralRegularError_profile_sharp_expansion 1 1
    have hprivateMinus := evenStructuralRegularError_profile_sharp_expansion 1 (-1)
    have hpublicPlus := step01_publicRegularError_expansion 1 1
    have hpublicMinus := step01_publicRegularError_expansion 1 (-1)
    unfold step01Midpoint02 evenNegativePerturbationTaylor02
    norm_num at hprivatePlus hprivateMinus hpublicPlus hpublicMinus ⊢
    linarith
  · have hprivate := evenStructuralRegularError_profile_sharp_expansion 0 1
    have hpublic := step01_publicRegularError_expansion 0 1
    unfold step01Midpoint22 evenNegativePerturbationTaylor22
    norm_num at hprivate hpublic ⊢
    linarith

private theorem primeRatio_correlation00_midpoint_lower :
    (83007 / 100000 : ℝ) <
      evenStructuralCorrelation00
        (factorTwoPrimeShift / yoshidaEndpointA) := by
  have hratio :
      factorTwoPrimeShift / yoshidaEndpointA < (116993 / 100000 : ℝ) := by
    rw [div_lt_iff₀ yoshidaEndpointA_pos]
    unfold factorTwoPrimeShift yoshidaEndpointA
    have h32 := strict_log_three_halves_kernel_bounds.2
    have h2 := strict_log_two_fine_bounds.1
    nlinarith
  unfold evenStructuralCorrelation00
  linarith

private theorem negativeStructuralBase00_midpoint_lower :
    (34153429 / 150000000 : ℝ) < -evenStructuralKernelBase00 := by
  have hL := strict_log_two_fine_bounds.1
  have ha := log_two_div_sqrt_two_kernel_lower
  have hb := log_three_div_sqrt_three_kernel_bounds.1
  have hC := primeRatio_correlation00_midpoint_lower
  have hbeta : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  have hprod :
      (63427 / 100000 : ℝ) * (83007 / 100000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation00
            (factorTwoPrimeShift / yoshidaEndpointA) := by
    calc
      (63427 / 100000 : ℝ) * (83007 / 100000 : ℝ) <
          (Real.log 3 / Real.sqrt 3) * (83007 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_right hb (by norm_num)
      _ < (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation00
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_left hC hbeta
  unfold evenStructuralKernelBase00
  nlinarith

/-- Sharp lower enclosure for the un-padded midpoint constant entry. -/
theorem step01Midpoint00_gt :
    (227278 / 1000000 : ℝ) < step01Midpoint00 := by
  have hb := negativeStructuralBase00_midpoint_lower
  have hm := evenPositivePolynomialMoment_bounds.2.1
  rw [step01Midpoint_eq_kernel_sub_positiveMoment.1]
  norm_num at hb hm ⊢
  linarith

/-- Sharp upper enclosure for the un-padded midpoint mixed entry. -/
theorem step01Midpoint02_lt :
    step01Midpoint02 < (204844 / 1000000 : ℝ) := by
  have hb := evenSlopeKernel02_bounds.2
  have hm := evenPositivePolynomialMoment_bounds.2.2.1
  rw [step01Midpoint_eq_kernel_sub_positiveMoment.2.1]
  unfold evenSlopeKernel02 at hb
  norm_num at hb hm ⊢
  linarith

/-- Sharp lower enclosure for the un-padded midpoint degree-two entry. -/
theorem step01Midpoint22_gt :
    (188489 / 1000000 : ℝ) < step01Midpoint22 := by
  have hb := evenSlopeKernel22_lower
  have hm := evenPositivePolynomialMoment_bounds.2.2.2.2.2
  rw [step01Midpoint_eq_kernel_sub_positiveMoment.2.2]
  unfold evenSlopeKernel22 at hb
  norm_num at hb hm ⊢
  linarith

/-- Matching upper enclosure for the un-padded midpoint constant entry. -/
theorem step01Midpoint00_lt :
    step01Midpoint00 < (227350 / 1000000 : ℝ) := by
  have ht := evenPositivePerturbationTaylor_ultra_bounds.1
  rw [step01Midpoint_eq_kernel_sub_positiveMoment.1]
  unfold evenPositivePerturbationTaylor00 at ht
  norm_num at ht ⊢
  linarith

/-- Matching lower enclosure for the un-padded midpoint mixed entry. -/
theorem step01Midpoint02_gt :
    (204806 / 1000000 : ℝ) < step01Midpoint02 := by
  have ht := evenPositivePerturbationTaylor_ultra_bounds.2.2.1
  rw [step01Midpoint_eq_kernel_sub_positiveMoment.2.1]
  unfold evenPositivePerturbationTaylor02 at ht
  norm_num at ht ⊢
  linarith

/-- Matching upper enclosure for the un-padded midpoint degree-two entry. -/
theorem step01Midpoint22_lt :
    step01Midpoint22 < (188527 / 1000000 : ℝ) := by
  have ht := evenPositivePerturbationTaylor_ultra_bounds.2.2.2
  rw [step01Midpoint_eq_kernel_sub_positiveMoment.2.2]
  unfold evenPositivePerturbationTaylor22 at ht
  norm_num at ht ⊢
  linarith

private theorem step01Midpoint00_lt_quarter :
    step01Midpoint00 < (1 / 4 : ℝ) :=
  step01Midpoint00_lt.trans (by norm_num)

private theorem step01Midpoint02_pos : 0 < step01Midpoint02 :=
  (by norm_num : (0 : ℝ) < 204806 / 1000000).trans step01Midpoint02_gt

private theorem step01Midpoint22_lt_fifth :
    step01Midpoint22 < (1 / 5 : ℝ) :=
  step01Midpoint22_lt.trans (by norm_num)

/-! ## The single rational reserve -/

/-- Cancellation-preserving `23/5` determinant reserve at a clean Gram
`(a,b,d)` and the un-padded negative Taylor midpoint. -/
def step01MidpointReserve (a b d : ℝ) : ℝ :=
  -23 * (a * d - b ^ 2) +
    33 * (a * step01Midpoint22 + d * step01Midpoint00 -
      2 * b * step01Midpoint02) -
    43 * (step01Midpoint00 * step01Midpoint22 - step01Midpoint02 ^ 2)

/-- The clean entry box and the global midpoint box leave more than
`1/20000` of determinant reserve.  The lower clean bounds are precisely what
makes the two diagonal monotonicities valid. -/
theorem one_div_twenty_thousand_lt_step01MidpointReserve
    {a b d : ℝ}
    (haLower : (3665 / 10000 : ℝ) < a)
    (haUpper : a < (3668 / 10000 : ℝ))
    (hbLower : (3402 / 10000 : ℝ) < b)
    (hdLower : (3269 / 10000 : ℝ) < d)
    (hdUpper : d < (3271 / 10000 : ℝ)) :
    (1 / 20000 : ℝ) < step01MidpointReserve a b d := by
  let A : ℝ := 3668 / 10000
  let B : ℝ := 3402 / 10000
  let D : ℝ := 3271 / 10000
  let U : ℝ := 227278 / 1000000
  let V : ℝ := 204844 / 1000000
  let W : ℝ := 188489 / 1000000
  let F : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
    fun x y z u v w ↦
      -23 * (x * z - y ^ 2) +
        33 * (x * w + z * u - 2 * y * v) - 43 * (u * w - v ^ 2)
  have huLower : U < step01Midpoint00 := by
    simpa only [U] using step01Midpoint00_gt
  have hvUpper : step01Midpoint02 < V := by
    simpa only [V] using step01Midpoint02_lt
  have hwLower : W < step01Midpoint22 := by
    simpa only [W] using step01Midpoint22_gt
  have huUpper : step01Midpoint00 < (1 / 4 : ℝ) :=
    step01Midpoint00_lt_quarter
  have hvPos : 0 < step01Midpoint02 := step01Midpoint02_pos
  have hwUpper : step01Midpoint22 < (1 / 5 : ℝ) :=
    step01Midpoint22_lt_fifth
  have hA : F A b d step01Midpoint00 step01Midpoint02 step01Midpoint22 <
      F a b d step01Midpoint00 step01Midpoint02 step01Midpoint22 := by
    have hcoef : -23 * d + 33 * step01Midpoint22 < 0 := by
      nlinarith
    rw [← sub_pos]
    have hdiff :
        F a b d step01Midpoint00 step01Midpoint02 step01Midpoint22 -
            F A b d step01Midpoint00 step01Midpoint02 step01Midpoint22 =
          (a - A) * (-23 * d + 33 * step01Midpoint22) := by
      dsimp only [F]
      ring
    rw [hdiff]
    exact mul_pos_of_neg_of_neg (by dsimp only [A]; linarith) hcoef
  have hD : F A b D step01Midpoint00 step01Midpoint02 step01Midpoint22 <
      F A b d step01Midpoint00 step01Midpoint02 step01Midpoint22 := by
    have hcoef : -23 * A + 33 * step01Midpoint00 < 0 := by
      dsimp only [A]
      nlinarith
    rw [← sub_pos]
    have hdiff :
        F A b d step01Midpoint00 step01Midpoint02 step01Midpoint22 -
            F A b D step01Midpoint00 step01Midpoint02 step01Midpoint22 =
          (d - D) * (-23 * A + 33 * step01Midpoint00) := by
      dsimp only [F]
      ring
    rw [hdiff]
    exact mul_pos_of_neg_of_neg (by dsimp only [D]; linarith) hcoef
  have hB : F A B D step01Midpoint00 step01Midpoint02 step01Midpoint22 <
      F A b D step01Midpoint00 step01Midpoint02 step01Midpoint22 := by
    have hcoef : 0 < 23 * (b + B) - 66 * step01Midpoint02 := by
      dsimp only [B, V] at hbLower hvUpper ⊢
      nlinarith
    rw [← sub_pos]
    have hdiff :
        F A b D step01Midpoint00 step01Midpoint02 step01Midpoint22 -
            F A B D step01Midpoint00 step01Midpoint02 step01Midpoint22 =
          (b - B) * (23 * (b + B) - 66 * step01Midpoint02) := by
      dsimp only [F]
      ring
    rw [hdiff]
    exact mul_pos (by dsimp only [B]; linarith) hcoef
  have hU : F A B D U step01Midpoint02 step01Midpoint22 <
      F A B D step01Midpoint00 step01Midpoint02 step01Midpoint22 := by
    have hcoef : 0 < 33 * D - 43 * step01Midpoint22 := by
      dsimp only [D]
      nlinarith
    rw [← sub_pos]
    have hdiff :
        F A B D step01Midpoint00 step01Midpoint02 step01Midpoint22 -
            F A B D U step01Midpoint02 step01Midpoint22 =
          (step01Midpoint00 - U) *
            (33 * D - 43 * step01Midpoint22) := by
      dsimp only [F]
      ring
    rw [hdiff]
    exact mul_pos (sub_pos.mpr huLower) hcoef
  have hV : F A B D U V step01Midpoint22 <
      F A B D U step01Midpoint02 step01Midpoint22 := by
    have hcoef : 43 * (step01Midpoint02 + V) - 66 * B < 0 := by
      dsimp only [B, V] at hvUpper ⊢
      nlinarith
    rw [← sub_pos]
    have hdiff :
        F A B D U step01Midpoint02 step01Midpoint22 -
            F A B D U V step01Midpoint22 =
          (step01Midpoint02 - V) *
            (43 * (step01Midpoint02 + V) - 66 * B) := by
      dsimp only [F]
      ring
    rw [hdiff]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hvUpper) hcoef
  have hW : F A B D U V W < F A B D U V step01Midpoint22 := by
    have hcoef : 0 < 33 * A - 43 * U := by
      norm_num [A, U]
    rw [← sub_pos]
    have hdiff :
        F A B D U V step01Midpoint22 - F A B D U V W =
          (step01Midpoint22 - W) * (33 * A - 43 * U) := by
      dsimp only [F]
      ring
    rw [hdiff]
    exact mul_pos (sub_pos.mpr hwLower) hcoef
  have hCorner : (1 / 20000 : ℝ) < F A B D U V W := by
    norm_num [F, A, B, D, U, V, W]
  have hchain := ((((((hCorner.trans hW).trans hV).trans hU).trans hB).trans hD).trans hA)
  simpa only [step01MidpointReserve, F] using hchain

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01MidpointReserve
