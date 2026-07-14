import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlMonotonicity
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep12Step23Positive

noncomputable section

open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaConstantBounds
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowControlMonotonicity
open YoshidaFactorTwoPhaseIntrinsicLowControlsPositive
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddStructuralPerturbation
open YoshidaFactorTwoStructuralConstantBounds

/-!
# Structural positivity of the last intrinsic Bernstein step

The last Bernstein difference has an endpoint interpretation which is much
sharper than bounding its three entries separately.  Its non-adjugate part
is a difference of the two odd endpoint forms, while the complete alternating
penalty recombines as the adjugate form of the negative even endpoint.

No phase sampling, interval subdivision, finite mode enumeration, or
computational enclosure is used below.
-/

private theorem oddStructuralCorrelation11_primeLag_gt :
    (-473 / 2000 : ℝ) <
      oddStructuralCorrelation11
        (factorTwoPrimeShift / yoshidaEndpointA) := by
  let τ : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let b : ℝ := 117 / 100
  have hτ := factorTwoPrimeLag_bounds
  have hτ0 : 0 < τ := by
    dsimp only [τ]
    linarith
  have hb0 : 0 < b := by norm_num [b]
  have hsq : τ ^ 2 < b ^ 2 := by
    have hsum : 0 < b + τ := add_pos hb0 hτ0
    have hlt : τ < b := by simpa only [b, τ] using hτ.2
    have hprod := mul_pos (sub_pos.mpr hlt) hsum
    change 0 < (b - τ) * (b + τ) at hprod
    nlinarith
  have hmix : τ * b < b ^ 2 := by
    have := mul_lt_mul_of_pos_right (by simpa only [b, τ] using hτ.2) hb0
    nlinarith
  have hbracket :
      (τ ^ 2 + τ * b + b ^ 2) / 6 - 1 < 0 := by
    dsimp only [b] at hsq hmix ⊢
    nlinarith
  have hfactor :
      oddStructuralCorrelation11 τ - oddStructuralCorrelation11 b =
        (τ - b) * ((τ ^ 2 + τ * b + b ^ 2) / 6 - 1) := by
    unfold oddStructuralCorrelation11
    ring
  have hprod : 0 <
      (τ - b) * ((τ ^ 2 + τ * b + b ^ 2) / 6 - 1) :=
    mul_pos_of_neg_of_neg (sub_neg.mpr (by simpa only [b, τ] using hτ.2))
      hbracket
  calc
    (-473 / 2000 : ℝ) < oddStructuralCorrelation11 b := by
      norm_num [oddStructuralCorrelation11, b]
    _ < oddStructuralCorrelation11 τ := by
      nlinarith [hfactor, hprod]
    _ = _ := by rfl

/-- The first odd perturbation entry admits the slightly sharper structural
upper bound needed by the endpoint Loewner comparison. -/
theorem factorTwoCenteredSymmetricPerturbation_p1_lt_one_fiftieth :
    factorTwoCenteredSymmetricPerturbation centeredP1 < (1 / 50 : ℝ) := by
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let c11 : ℝ := oddStructuralCorrelation11
    (factorTwoPrimeShift / yoshidaEndpointA)
  have hlag := factorTwoPrimeLag_bounds
  have hlag0 : 0 < factorTwoPrimeShift / yoshidaEndpointA := by linarith
  have hlag1 : 1 < factorTwoPrimeShift / yoshidaEndpointA := by linarith
  have hlag2 : factorTwoPrimeShift / yoshidaEndpointA < 2 := by linarith
  have hcpos : 0 <
      (factorTwoPrimeShift / yoshidaEndpointA) ^ 2 +
        2 * (factorTwoPrimeShift / yoshidaEndpointA) - 2 := by
    have hsquare : 1 < (factorTwoPrimeShift / yoshidaEndpointA) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hlag1)
        (add_pos hlag0 (by norm_num : (0 : ℝ) < 1))]
    linarith
  have hc11neg : c11 < 0 := by
    dsimp only [c11]
    unfold oddStructuralCorrelation11
    have hleft : factorTwoPrimeShift / yoshidaEndpointA - 2 < 0 := by linarith
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hleft hcpos) (by norm_num)
  have hc11Lower : (-473 / 2000 : ℝ) < c11 := by
    simpa only [c11] using oddStructuralCorrelation11_primeLag_gt
  have hβpos : 0 < β := by
    dsimp only [β]
    positivity
  have hβUpper : β < (6343 / 10000 : ℝ) := by
    simpa only [β] using log_three_div_sqrt_three_kernel_bounds.2
  have hprime : -(β * c11) <
      (6343 / 10000 : ℝ) * (473 / 2000) := by
    have hc : -c11 < (473 / 2000 : ℝ) := by linarith
    have hmul := mul_lt_mul hβUpper hc.le (by linarith) (by norm_num)
    nlinarith
  have herr := abs_le.mp
    (abs_oddStructuralRegularError11_le oddStructuralRegularKernelControl)
  have hlog := strict_log_two_fine_bounds.1
  have hdyadic := log_two_div_sqrt_two_kernel_lower
  rw [factorTwoCenteredSymmetricPerturbation_p1_structural_eq]
  change oddStructuralRegularError oddStructuralCorrelation11 - 4 / 375 +
      (2 / 3 - (2 / 3 : ℝ) * Real.log 2) -
      (Real.log 2 / Real.sqrt 2) * (2 / 3) - β * c11 < 1 / 50
  linarith only [herr.2, hlog, hdyadic, hprime]

/-! ## A Loewner comparison between the two odd endpoints -/

private theorem oddEndpointComparison_rationalMatrix_pos :
    0 <
      (3 * (193 / 1125 : ℝ) -
          11 * factorTwoCenteredSymmetricPerturbation centeredP1) *
        (3 * (5951 / 18375 : ℝ) -
          11 * factorTwoCenteredSymmetricPerturbation centeredP3) -
      (3 * (1 / 5 : ℝ) -
          11 * factorTwoCenteredSymmetricPerturbationBilinear
            centeredP1 centeredP3) ^ 2 := by
  rcases oddStructuralLow_perturbation_bounds with
    ⟨⟨_hp11Lower, hp11Upper⟩,
      ⟨⟨hp13Lower, hp13Upper⟩, ⟨_hp33Lower, hp33Upper⟩⟩⟩
  have hp11Sharp := factorTwoCenteredSymmetricPerturbation_p1_lt_one_fiftieth
  let A : ℝ := 3 * (193 / 1125 : ℝ) -
    11 * factorTwoCenteredSymmetricPerturbation centeredP1
  let B : ℝ := 3 * (1 / 5 : ℝ) -
    11 * factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3
  let D : ℝ := 3 * (5951 / 18375 : ℝ) -
    11 * factorTwoCenteredSymmetricPerturbation centeredP3
  have hA : (3 * (193 / 1125 : ℝ) - 11 / 50) < A := by
    dsimp only [A]
    linarith
  have hD : (3 * (5951 / 18375 : ℝ) + 121 / 100) < D := by
    dsimp only [D]
    linarith
  have hB0 : 0 < B := by
    dsimp only [B]
    linarith
  have hB : B < (153 / 200 : ℝ) := by
    dsimp only [B]
    linarith
  have hAD :
      (3 * (193 / 1125 : ℝ) - 11 / 50) *
          (3 * (5951 / 18375 : ℝ) + 121 / 100) < A * D := by
    have hA0 : 0 < (3 * (193 / 1125 : ℝ) - 11 / 50) := by norm_num
    have hD0 : 0 < (3 * (5951 / 18375 : ℝ) + 121 / 100) := by norm_num
    calc
      (3 * (193 / 1125 : ℝ) - 11 / 50) *
          (3 * (5951 / 18375 : ℝ) + 121 / 100) <
          A * (3 * (5951 / 18375 : ℝ) + 121 / 100) :=
        mul_lt_mul_of_pos_right hA hD0
      _ < A * D := mul_lt_mul_of_pos_left hD (by linarith)
  have hBsq : B ^ 2 < (153 / 200 : ℝ) ^ 2 := by
    have hsum : 0 < (153 / 200 : ℝ) + B := add_pos (by norm_num) hB0
    nlinarith [mul_pos (sub_pos.mpr hB) hsum]
  have hmargin : (153 / 200 : ℝ) ^ 2 <
      (3 * (193 / 1125 : ℝ) - 11 / 50) *
        (3 * (5951 / 18375 : ℝ) + 121 / 100) := by
    norm_num
  dsimp only [A, B, D] at hAD hBsq ⊢
  linarith

/-- The positive odd endpoint form is at most `7/4` of the negative endpoint
form in Loewner order.  The proof retains the complete clean quadratic and
uses one `2 x 2` Gram determinant, rather than three control-entry boxes. -/
theorem factorTwoIntrinsicOdd_plus_le_seven_fourths_minus
    (c d : ℝ) :
    factorTwoIntrinsicOddPhaseQuadratic 1 c d ≤
      (7 / 4 : ℝ) * factorTwoIntrinsicOddPhaseQuadratic (-1) c d := by
  let p11 := factorTwoCenteredSymmetricPerturbation centeredP1
  let p13 := factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3
  let p33 := factorTwoCenteredSymmetricPerturbation centeredP3
  have hA : 0 < 3 * (193 / 1125 : ℝ) - 11 * p11 := by
    have hp := factorTwoCenteredSymmetricPerturbation_p1_lt_one_fiftieth
    dsimp only [p11]
    linarith
  have hdet : 0 <
      (3 * (193 / 1125 : ℝ) - 11 * p11) *
          (3 * (5951 / 18375 : ℝ) - 11 * p33) -
        (3 * (1 / 5 : ℝ) - 11 * p13) ^ 2 := by
    simpa only [p11, p13, p33] using oddEndpointComparison_rationalMatrix_pos
  have hmatrix : 0 ≤
      (3 * (193 / 1125 : ℝ) - 11 * p11) * c ^ 2 +
        2 * (3 * (1 / 5 : ℝ) - 11 * p13) * c * d +
        (3 * (5951 / 18375 : ℝ) - 11 * p33) * d ^ 2 := by
    by_cases hne : c ≠ 0 ∨ d ≠ 0
    · exact (real_twoByTwo_quadratic_pos _ _ _ c d hA hdet hne).le
    · push_neg at hne
      rcases hne with ⟨rfl, rfl⟩
      norm_num
  have hclean := oddStructuralLow_clean_rationalGram_le c d
  have hcleanEq := yoshidaEndpointOddLowGram_quadratic c d
  have hpert := factorTwoCenteredSymmetricPerturbation_oddStructuralLow c d
  unfold factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33
  dsimp only [p11, p13, p33] at hmatrix
  rw [hcleanEq] at hclean
  nlinarith

/-! ## Exact endpoint form of the last Bernstein step -/

private theorem factorTwoIntrinsicOddDirection_eq_minus_sub_plus
    (c d : ℝ) :
    factorTwoIntrinsicOddDirectionQuadratic c d =
      factorTwoIntrinsicOddPhaseQuadratic (-1) c d -
        factorTwoIntrinsicOddPhaseQuadratic 1 c d := by
  unfold factorTwoIntrinsicOddDirectionQuadratic
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33
  ring

private theorem factorTwoIntrinsicEvenDet_minus_eq_coefficients :
    factorTwoIntrinsicEvenPhaseDet (-1) =
      factorTwoIntrinsicEvenDetCoefficient0 +
        factorTwoIntrinsicEvenDetCoefficient1 +
        factorTwoIntrinsicEvenDetCoefficient2 := by
  unfold factorTwoIntrinsicEvenPhaseDet
    factorTwoIntrinsicEvenDetCoefficient0
    factorTwoIntrinsicEvenDetCoefficient1
    factorTwoIntrinsicEvenDetCoefficient2
    factorTwoIntrinsicEvenDirection00 factorTwoIntrinsicEvenDirection02
    factorTwoIntrinsicEvenDirection22
    factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22
  unfold factorTwoIntrinsicEvenPhaseDet
  unfold factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22
  ring

private theorem factorTwoIntrinsicAdjugate_sum_eq_minus
    (c d : ℝ) :
    factorTwoIntrinsicAdjugateCoefficient0 c d +
        factorTwoIntrinsicAdjugateCoefficient1 c d =
      factorTwoIntrinsicEvenAdjugateCoupling (-1) c d := by
  unfold factorTwoIntrinsicAdjugateCoefficient0
    factorTwoIntrinsicAdjugateCoefficient1
    factorTwoIntrinsicEvenAdjugateCoupling
    factorTwoIntrinsicEvenDirection00 factorTwoIntrinsicEvenDirection02
    factorTwoIntrinsicEvenDirection22
    factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22
  ring

/-- The alternating part of the last Bernstein step is the complete
adjugate form of the negative even endpoint, hence nonnegative without any
entrywise estimate of the four alternating couplings. -/
theorem factorTwoIntrinsicAdjugate_sum_nonneg (c d : ℝ) :
    0 ≤ factorTwoIntrinsicAdjugateCoefficient0 c d +
      factorTwoIntrinsicAdjugateCoefficient1 c d := by
  rw [factorTwoIntrinsicAdjugate_sum_eq_minus]
  have heven := factorTwoIntrinsicEven_minus_endpoint_kernel_gates
  exact twoByTwo_adjugateQuadratic_nonneg
    (factorTwoStructuralPhaseLow00 (-1))
    (factorTwoStructuralPhaseLow02 (-1))
    (factorTwoStructuralPhaseLow22 (-1))
    (factorTwoIntrinsicAlternatingRow0 c d)
    (factorTwoIntrinsicAlternatingRow2 c d)
    heven.1 (by
      simpa only [factorTwoIntrinsicEvenPhaseDet] using heven.2)

/-- Cancellation-preserving endpoint decomposition of the last Bernstein
difference.  In particular, no alternating entry occurs outside the single
negative-endpoint adjugate Gram. -/
theorem three_mul_factorTwoIntrinsicBoundaryControlStep23_eq_endpoints
    (c d : ℝ) :
    3 * factorTwoIntrinsicBoundaryControlStep23 c d =
      (factorTwoIntrinsicEvenDetCoefficient0 +
          2 * factorTwoIntrinsicEvenDetCoefficient1 +
          3 * factorTwoIntrinsicEvenDetCoefficient2) *
          factorTwoIntrinsicOddPhaseQuadratic (-1) c d -
        factorTwoIntrinsicEvenPhaseDet (-1) *
          factorTwoIntrinsicOddPhaseQuadratic 1 c d +
        factorTwoIntrinsicEvenAdjugateCoupling (-1) c d := by
  rw [three_mul_factorTwoIntrinsicBoundaryControlStep23,
    factorTwoIntrinsicOddDirection_eq_minus_sub_plus,
    factorTwoIntrinsicEvenDet_minus_eq_coefficients,
    ← factorTwoIntrinsicAdjugate_sum_eq_minus]
  ring

/-- The sole even scalar left by the endpoint comparison proof of Step23.
It is a determinant-slope inequality, not a box for any Step23 entry. -/
def EvenStep23DeterminantSlope : Prop :=
  (7 / 4 : ℝ) * factorTwoIntrinsicEvenPhaseDet (-1) ≤
    factorTwoIntrinsicEvenDetCoefficient0 +
      2 * factorTwoIntrinsicEvenDetCoefficient1 +
      3 * factorTwoIntrinsicEvenDetCoefficient2

/-- The exact endpoint slope, together with the proved odd Loewner
comparison, closes the complete last Bernstein step. -/
theorem factorTwoIntrinsicBoundaryControlStep23_nonneg_of_evenSlope
    (hSlope : EvenStep23DeterminantSlope) (c d : ℝ) :
    0 ≤ factorTwoIntrinsicBoundaryControlStep23 c d := by
  let A : ℝ := factorTwoIntrinsicEvenDetCoefficient0 +
    2 * factorTwoIntrinsicEvenDetCoefficient1 +
    3 * factorTwoIntrinsicEvenDetCoefficient2
  let D : ℝ := factorTwoIntrinsicEvenPhaseDet (-1)
  let Oplus : ℝ := factorTwoIntrinsicOddPhaseQuadratic 1 c d
  let Ominus : ℝ := factorTwoIntrinsicOddPhaseQuadratic (-1) c d
  let Jadj : ℝ := factorTwoIntrinsicEvenAdjugateCoupling (-1) c d
  have hD : 0 < D := by
    dsimp only [D]
    exact factorTwoIntrinsicEven_minus_endpoint_kernel_gates.2
  have hOminus : 0 ≤ Ominus := by
    by_cases hne : c ≠ 0 ∨ d ≠ 0
    · have hodd := oddStructuralLow_endpoint_gates
      dsimp only [Ominus]
      exact (real_twoByTwo_quadratic_pos
        (factorTwoIntrinsicOddPhaseLow11 (-1))
        (factorTwoIntrinsicOddPhaseLow13 (-1))
        (factorTwoIntrinsicOddPhaseLow33 (-1)) c d
        hodd.2.2.1 hodd.2.2.2 hne).le
    · push_neg at hne
      rcases hne with ⟨rfl, rfl⟩
      simp [Ominus, factorTwoIntrinsicOddPhaseQuadratic]
  have hOddCompare : Oplus ≤ (7 / 4 : ℝ) * Ominus := by
    simpa only [Oplus, Ominus] using
      factorTwoIntrinsicOdd_plus_le_seven_fourths_minus c d
  have hbase : 0 ≤ A * Ominus - D * Oplus := by
    have hscaledOdd := mul_le_mul_of_nonneg_left hOddCompare hD.le
    have hscaledSlope :
        D * ((7 / 4 : ℝ) * Ominus) ≤ A * Ominus := by
      have hs : (7 / 4 : ℝ) * D ≤ A := by
        simpa only [EvenStep23DeterminantSlope, A, D] using hSlope
      nlinarith [mul_nonneg (sub_nonneg.mpr hs) hOminus]
    nlinarith
  have hJ : 0 ≤ Jadj := by
    dsimp only [Jadj]
    rw [← factorTwoIntrinsicAdjugate_sum_eq_minus]
    exact factorTwoIntrinsicAdjugate_sum_nonneg c d
  have hdecomp :=
    three_mul_factorTwoIntrinsicBoundaryControlStep23_eq_endpoints c d
  dsimp only [A, D, Oplus, Ominus, Jadj] at hbase hJ
  nlinarith

/-- Universal Step23 positivity is reduced to one structural even
determinant-slope comparison. -/
theorem factorTwoIntrinsicBoundaryControlStep23_nonneg_of_evenSlope_all
    (hSlope : EvenStep23DeterminantSlope) :
    ∀ c d : ℝ, 0 ≤ factorTwoIntrinsicBoundaryControlStep23 c d :=
  factorTwoIntrinsicBoundaryControlStep23_nonneg_of_evenSlope hSlope

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep12Step23Positive
