import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep12Structural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep12ResidualPositive

noncomputable section

open YoshidaEndpointEvenStructuralReduction
open YoshidaConstantBounds
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointEvenLowRegular
open YoshidaEndpointEvenProjectedRemainderEnvelopeCoefficients
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowControlStep12Structural
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural positivity of the reduced Step12 residual

The alternating block is expressed in its row sum/difference coordinates.
The fixed shear `c ↦ c + (5/3)d` almost diagonalizes the sole remaining
binary quadratic.  Its three transformed coefficients are controlled by one
box-monotonic argument from the global structural kernel bounds.
-/

def step12CleanAlpha : ℝ :=
  yoshidaEndpointEvenLowGram00 + yoshidaEndpointEvenLowGram22 -
    2 * yoshidaEndpointEvenLowGram02

def step12CleanBeta : ℝ :=
  yoshidaEndpointEvenLowGram22 - yoshidaEndpointEvenLowGram00

def step12CleanGamma : ℝ :=
  yoshidaEndpointEvenLowGram00 + yoshidaEndpointEvenLowGram22 +
    2 * yoshidaEndpointEvenLowGram02

def step12NegativeAlpha : ℝ :=
  evenNegativePerturbation00 + evenNegativePerturbation22 -
    2 * evenNegativePerturbation02

def step12NegativeBeta : ℝ :=
  evenNegativePerturbation22 - evenNegativePerturbation00

def step12NegativeGamma : ℝ :=
  evenNegativePerturbation00 + evenNegativePerturbation22 +
    2 * evenNegativePerturbation02

def step12AlternatingSum1 : ℝ :=
  factorTwoIntrinsicAlternating01 + factorTwoIntrinsicAlternating21

def step12AlternatingDiff1 : ℝ :=
  factorTwoIntrinsicAlternating01 - factorTwoIntrinsicAlternating21

def step12AlternatingSum3 : ℝ :=
  factorTwoIntrinsicAlternating03 + factorTwoIntrinsicAlternating23

def step12AlternatingDiff3 : ℝ :=
  factorTwoIntrinsicAlternating03 - factorTwoIntrinsicAlternating23

def step12ShearedAlternatingSum : ℝ :=
  step12AlternatingSum3 - (5 / 3 : ℝ) * step12AlternatingSum1

def step12ShearedAlternatingDiff : ℝ :=
  step12AlternatingDiff3 - (5 / 3 : ℝ) * step12AlternatingDiff1

def step12Reduced00 : ℝ := step12ReducedResidual 1 0

def step12Reduced03 : ℝ :=
  (step12ReducedResidual 1 1 -
    step12ReducedResidual 1 0 - step12ReducedResidual 0 1) / 2

def step12Reduced33 : ℝ := step12ReducedResidual 0 1

def step12ReducedShear03 : ℝ :=
  step12Reduced03 - (5 / 3 : ℝ) * step12Reduced00

def step12ReducedShear33 : ℝ :=
  step12Reduced33 - (10 / 3 : ℝ) * step12Reduced03 +
    (25 / 9 : ℝ) * step12Reduced00

private theorem mixedDet_eq_sumDifference :
    step12EvenCleanNegativeMixedDet =
      (step12CleanAlpha * step12NegativeGamma +
        step12NegativeAlpha * step12CleanGamma -
        2 * step12CleanBeta * step12NegativeBeta) / 4 := by
  unfold step12EvenCleanNegativeMixedDet step12CleanAlpha step12CleanBeta
    step12CleanGamma step12NegativeAlpha step12NegativeBeta
    step12NegativeGamma
  ring

private theorem determinantDifference_eq_sumDifference :
    3 * step12EvenNegativeDet - step12EvenCleanDet =
      (3 * (step12NegativeAlpha * step12NegativeGamma -
          step12NegativeBeta ^ 2) -
        (step12CleanAlpha * step12CleanGamma -
          step12CleanBeta ^ 2)) / 4 := by
  unfold step12EvenNegativeDet step12EvenCleanDet step12CleanAlpha
    step12CleanBeta step12CleanGamma step12NegativeAlpha
    step12NegativeBeta step12NegativeGamma
  ring

private theorem alternating_rows_eq_sumDifference (c d : ℝ) :
    factorTwoIntrinsicAlternatingRow0 c d =
        ((step12AlternatingSum1 * c + step12AlternatingSum3 * d) +
          (step12AlternatingDiff1 * c + step12AlternatingDiff3 * d)) / 2 ∧
      factorTwoIntrinsicAlternatingRow2 c d =
        ((step12AlternatingSum1 * c + step12AlternatingSum3 * d) -
          (step12AlternatingDiff1 * c + step12AlternatingDiff3 * d)) / 2 := by
  unfold factorTwoIntrinsicAlternatingRow0 factorTwoIntrinsicAlternatingRow2
    step12AlternatingSum1 step12AlternatingDiff1 step12AlternatingSum3
    step12AlternatingDiff3
  constructor <;> ring

private theorem negativeAdjugateCore_eq_sumDifference (c d : ℝ) :
    step12NegativeAdjugateCore c d =
      (step12NegativeAlpha *
          (step12AlternatingSum1 * c + step12AlternatingSum3 * d) ^ 2 +
        2 * step12NegativeBeta *
          (step12AlternatingSum1 * c + step12AlternatingSum3 * d) *
          (step12AlternatingDiff1 * c + step12AlternatingDiff3 * d) +
        step12NegativeGamma *
          (step12AlternatingDiff1 * c + step12AlternatingDiff3 * d) ^ 2) / 4 := by
  rcases alternating_rows_eq_sumDifference c d with ⟨h0, h2⟩
  unfold step12NegativeAdjugateCore step12NegativeAlpha
    step12NegativeBeta step12NegativeGamma
  rw [h0, h2]
  ring

theorem step12ReducedResidual_expansion (c d : ℝ) :
    step12ReducedResidual c d =
      step12Reduced00 * c ^ 2 +
        2 * step12Reduced03 * c * d + step12Reduced33 * d ^ 2 := by
  unfold step12Reduced00 step12Reduced03 step12Reduced33
  unfold step12ReducedResidual step12OddCleanLower
    step12OddPerturbationUpper
  unfold oddPerturbationUpper11 oddPerturbationUpper13
    oddPerturbationUpper33
  unfold step12NegativeAdjugateCore factorTwoIntrinsicAlternatingRow0
    factorTwoIntrinsicAlternatingRow2
  ring

theorem step12ReducedResidual_eq_sheared (c d : ℝ) :
    step12ReducedResidual c d =
      step12Reduced00 * (c + (5 / 3 : ℝ) * d) ^ 2 +
        2 * step12ReducedShear03 * (c + (5 / 3 : ℝ) * d) * d +
        step12ReducedShear33 * d ^ 2 := by
  rw [step12ReducedResidual_expansion]
  unfold step12ReducedShear03 step12ReducedShear33
  ring

/-! ## Coarse clean-coordinate enclosure -/

private theorem log_pi_mul_log_two_gt_7776 :
    (7776 / 10000 : ℝ) < Real.log (Real.pi * Real.log 2) := by
  have hlog := strict_log_two_fine_bounds.1
  have hp1 :
      (3.14159265358979323846 : ℝ) *
          (69314718055 / 100000000000 : ℝ) <
        Real.pi * (69314718055 / 100000000000 : ℝ) :=
    mul_lt_mul_of_pos_right Real.pi_gt_d20 (by norm_num)
  have hp2 :
      Real.pi * (69314718055 / 100000000000 : ℝ) <
        Real.pi * Real.log 2 :=
    mul_lt_mul_of_pos_left hlog Real.pi_pos
  have hprod : (2177 / 1000 : ℝ) < Real.pi * Real.log 2 := by
    calc
      (2177 / 1000 : ℝ) <
          (3.14159265358979323846 : ℝ) *
            (69314718055 / 100000000000 : ℝ) := by norm_num
      _ < Real.pi * (69314718055 / 100000000000 : ℝ) := hp1
      _ < Real.pi * Real.log 2 := hp2
  have hseries := Real.sum_range_le_log_div
    (x := (1177 / 3177 : ℝ)) (by norm_num) (by norm_num) 3
  have hrat : (7776 / 10000 : ℝ) < Real.log (2177 / 1000 : ℝ) := by
    norm_num [Finset.sum_range_succ] at hseries ⊢
    linarith
  exact hrat.trans (Real.strictMonoOn_log (by norm_num)
    (mul_pos Real.pi_pos (Real.log_pos (by norm_num))) hprod)

private theorem yoshidaEndpointScalarMassLoss_gt_13547 :
    (13547 / 10000 : ℝ) < yoshidaEndpointScalarMassLoss := by
  unfold yoshidaEndpointScalarMassLoss
  linarith [strict_euler_gamma_bounds.1, log_pi_mul_log_two_gt_7776]

private theorem intrinsicEven_regularGram22_gt_neg_one_hundredth :
    (-1 / 100 : ℝ) <
      ∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x *
          centeredEvenP2 x := by
  let p : ℝ → ℝ := centeredEvenP2
  have hnorm :=
    norm_yoshidaEndpointRegularQuadratic_centeredEvenP2_lt
  have heq : YoshidaRegularKernelSchur.yoshidaEndpointRegularQuadratic
      (fun x ↦ (centeredEvenP2 x : ℂ)) =
        yoshidaEndpointRegularRealBilinear p p := by
    unfold YoshidaRegularKernelSchur.yoshidaEndpointRegularQuadratic
      yoshidaEndpointRegularRealBilinear yoshidaEndpointA p
    rfl
  rw [heq] at hnorm
  have hreAbs :
      |(yoshidaEndpointRegularRealBilinear p p).re| < (1 / 100 : ℝ) :=
    (Complex.abs_re_le_norm _).trans_lt hnorm
  have hre := (abs_lt.mp hreAbs).1
  have hreg := yoshidaEndpointRegularRealBilinear_eq_integral_representer
    p p (by unfold p centeredEvenP2; fun_prop)
      (by unfold p centeredEvenP2; fun_prop)
  simp only [Complex.add_re] at hreg
  simpa only [p] using (show
      (-1 / 100 : ℝ) <
        ∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter p x * p x by
    nlinarith)

/-- A deliberately coarse structural upper bound for the clean degree-two
entry.  The only regular-kernel input is the global Schur estimate. -/
theorem intrinsicEven_cleanGram22_lt_332_thousandths :
    yoshidaEndpointEvenLowGram22 < (332 / 1000 : ℝ) := by
  have hlog := strict_log_two_fine_bounds.1
  have hmass := yoshidaEndpointScalarMassLoss_gt_13547
  have hreg := intrinsicEven_regularGram22_gt_neg_one_hundredth
  have hAlo : (0 : ℝ) < yoshidaEndpointA := yoshidaEndpointA_pos
  have hAup :
      yoshidaEndpointA < (69314718057 / 200000000000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.2]
  have hregScaled :
      -yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x *
              centeredEvenP2 x) <
        (69314718057 / 200000000000 : ℝ) / 100 := by
    have hmul := mul_lt_mul_of_pos_left hreg hAlo
    nlinarith
  have hC :
      (4012369 / 1000000000 : ℝ) <
          yoshidaEndpointCoshMoment centeredEvenP2 ∧
        yoshidaEndpointCoshMoment centeredEvenP2 <
          (4012371 / 1000000000 : ℝ) :=
    coshMoment_p2_bounds
  have hCpos : 0 < yoshidaEndpointCoshMoment centeredEvenP2 := by
    linarith [hC.1]
  have hCsq :
      yoshidaEndpointCoshMoment centeredEvenP2 ^ 2 <
        (4012371 / 1000000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hC.2 hCpos.le (by norm_num)
  have hhyper :
      2 * yoshidaEndpointA *
          yoshidaEndpointCoshMoment centeredEvenP2 ^ 2 <
        2 * (69314718057 / 200000000000 : ℝ) *
          (4012371 / 1000000000 : ℝ) ^ 2 := by
    have hmul1 := mul_lt_mul_of_pos_right hAup
      (sq_pos_of_pos hCpos)
    have hmul2 := mul_lt_mul_of_pos_left hCsq
      (show (0 : ℝ) < 69314718057 / 200000000000 by norm_num)
    nlinarith [hmul1, hmul2]
  rw [intrinsicEven_cleanGram22_expansion,
    integral_endpointPotential_mul_centeredEvenP2_sq]
  norm_num at hlog hmass hregScaled hhyper ⊢
  linarith

/-! ## Perturbation coordinates from the coupled Taylor--Loewner model -/

private theorem evenPositivePerturbationTaylor_coarse_bounds :
    (-228327 / 1000000 : ℝ) < evenPositivePerturbationTaylor00 ∧
      (-204994 / 1000000 : ℝ) < evenPositivePerturbationTaylor02 ∧
      evenPositivePerturbationTaylor02 < (-204739 / 1000000 : ℝ) ∧
      (-189190 / 1000000 : ℝ) < evenPositivePerturbationTaylor22 := by
  have hb00 := evenStructuralKernelBase00_lower
  have hb02 := evenStructuralKernelBase02_bounds
  have hb22 := evenStructuralKernelBase22_lower
  have hm := evenPositivePolynomialMoment_bounds
  unfold evenPositivePerturbationTaylor00 evenPositivePerturbationTaylor02
    evenPositivePerturbationTaylor22
  constructor
  · norm_num at hb00 hm ⊢
    linarith
  constructor
  · norm_num at hb02 hm ⊢
    linarith
  constructor <;> norm_num at hb02 hb22 hm ⊢ <;> linarith

private theorem step12NegativeCoordinate_bounds :
    (49 / 10000 : ℝ) < step12NegativeAlpha ∧
      step12NegativeAlpha < (201 / 25000 : ℝ) ∧
      (-101 / 2500 : ℝ) < step12NegativeBeta ∧
      step12NegativeBeta < (-373 / 10000 : ℝ) ∧
      (103 / 125 : ℝ) < step12NegativeGamma ∧
      step12NegativeGamma < (2069 / 2500 : ℝ) := by
  have hTaylor := evenPositivePerturbationTaylor_coarse_bounds
  have hLowerAlpha := evenNegativePerturbationSharp_quadratic_le 1 (-1)
  have hLowerGamma := evenNegativePerturbationSharp_quadratic_le 1 1
  have hLower00 := evenNegativePerturbationSharp_quadratic_le 1 0
  have hLower22 := evenNegativePerturbationSharp_quadratic_le 0 1
  rw [← evenNegativePerturbation_profile_eq] at hLowerAlpha
  rw [← evenNegativePerturbation_profile_eq] at hLowerGamma
  rw [← evenNegativePerturbation_profile_eq] at hLower00
  rw [← evenNegativePerturbation_profile_eq] at hLower22
  have hUpperAlpha := evenPositivePerturbationTaylor_quadratic_le 1 (-1)
  have hUpperGamma := evenPositivePerturbationTaylor_quadratic_le 1 1
  have hUpper00 := evenPositivePerturbationTaylor_quadratic_le 1 0
  have hUpper22 := evenPositivePerturbationTaylor_quadratic_le 0 1
  have hProfileAlpha := evenNegativePerturbation_profile_eq 1 (-1)
  have hProfileGamma := evenNegativePerturbation_profile_eq 1 1
  have hProfile00 := evenNegativePerturbation_profile_eq 1 0
  have hProfile22 := evenNegativePerturbation_profile_eq 0 1
  unfold evenNegativePerturbationSharp00 evenNegativePerturbationSharp02
    evenNegativePerturbationSharp22 at hLowerAlpha hLowerGamma hLower00 hLower22
  unfold step12NegativeAlpha step12NegativeBeta step12NegativeGamma
  norm_num at hLowerAlpha hLowerGamma hLower00 hLower22
  norm_num at hUpperAlpha hUpperGamma hUpper00 hUpper22
  norm_num at hProfileAlpha hProfileGamma hProfile00 hProfile22
  norm_num at hTaylor ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem step12CleanCoordinate_bounds :
    (128 / 10000 : ℝ) < step12CleanAlpha ∧
      step12CleanAlpha < (216 / 10000 : ℝ) ∧
      (-431 / 10000 : ℝ) < step12CleanBeta ∧
      step12CleanBeta < (-345 / 10000 : ℝ) ∧
      (13738 / 10000 : ℝ) < step12CleanGamma ∧
      step12CleanGamma < (13826 / 10000 : ℝ) := by
  have h00L := intrinsicEven_cleanGram00_gt
  have h00U := intrinsicEven_cleanGram00_lt_thirtyseven_hundredths
  have h02 := intrinsicEven_cleanGram02_bounds
  have h22L := intrinsicEven_cleanGram22_gt
  have h22U := intrinsicEven_cleanGram22_lt_332_thousandths
  unfold step12CleanAlpha step12CleanBeta step12CleanGamma
  norm_num at h00L h00U h02 h22L h22U ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem step12AlternatingCoordinate_bounds :
    (56168 / 100000 : ℝ) < step12AlternatingSum1 ∧
      step12AlternatingSum1 < (56173 / 100000 : ℝ) ∧
      (1687 / 100000 : ℝ) < step12AlternatingDiff1 ∧
      step12AlternatingDiff1 < (1692 / 100000 : ℝ) ∧
      (-5971 / 15000 : ℝ) < step12ShearedAlternatingSum ∧
      step12ShearedAlternatingSum < (-29833 / 75000 : ℝ) ∧
      (273 / 10000 : ℝ) < step12ShearedAlternatingDiff ∧
      step12ShearedAlternatingDiff < (1661 / 60000 : ℝ) := by
  have h := factorTwoIntrinsicAlternatingSharpBounds
  unfold FactorTwoIntrinsicAlternatingSharpBounds at h
  unfold step12ShearedAlternatingSum step12ShearedAlternatingDiff
    step12AlternatingSum1 step12AlternatingDiff1
    step12AlternatingSum3 step12AlternatingDiff3
  norm_num at h ⊢
  rcases h with ⟨hs1L, hs1U, hd1L, hd1U, hs3L, hs3U, hd3L, hd3U⟩
  constructor
  · exact hs1L
  constructor
  · exact hs1U
  constructor
  · exact hd1L
  constructor
  · exact hd1U
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-! ## The sheared coefficient box -/

private def coordinateMixed
    (ca cb cg qa qb qg : ℝ) : ℝ :=
  (ca * qg + qa * cg - 2 * cb * qb) / 4

private def coordinateDetDifference
    (ca cb cg qa qb qg : ℝ) : ℝ :=
  (3 * (qa * qg - qb ^ 2) - (ca * cg - cb ^ 2)) / 4

private def coordinateAdjugate
    (qa qb qg sx dx sy dy : ℝ) : ℝ :=
  (qa * sx * sy + qb * (sx * dy + dx * sy) + qg * dx * dy) / 4

private def shearClean03 : ℝ :=
  (2001 / 10000) - (5 / 3) * (1777 / 10000)

private def shearPerturbation03 : ℝ :=
  (-10065 / 1000000) - (5 / 3) * (1734 / 100000)

private def shearClean33 : ℝ :=
  (3314 / 10000) - (10 / 3) * (2001 / 10000) +
    (25 / 9) * (1777 / 10000)

private def shearPerturbation33 : ℝ :=
  (-11833 / 100000) - (10 / 3) * (-10065 / 1000000) +
    (25 / 9) * (1734 / 100000)

private def coordinateReduced00
    (ca cb cg qa qb qg s1 d1 : ℝ) : ℝ :=
  coordinateMixed ca cb cg qa qb qg * (1777 / 10000) +
    coordinateDetDifference ca cb cg qa qb qg * (1734 / 100000) -
    coordinateAdjugate qa qb qg s1 d1 s1 d1

private def coordinateReducedShear03
    (ca cb cg qa qb qg s1 d1 u v : ℝ) : ℝ :=
  coordinateMixed ca cb cg qa qb qg *
      shearClean03 +
    coordinateDetDifference ca cb cg qa qb qg *
      shearPerturbation03 -
    coordinateAdjugate qa qb qg s1 d1 u v

private def coordinateReducedShear33
    (ca cb cg qa qb qg u v : ℝ) : ℝ :=
  coordinateMixed ca cb cg qa qb qg *
      shearClean33 +
    coordinateDetDifference ca cb cg qa qb qg *
      shearPerturbation33 -
    coordinateAdjugate qa qb qg u v u v

private theorem step12ReducedCoefficients_eq_coordinates :
    step12Reduced00 = coordinateReduced00
        step12CleanAlpha step12CleanBeta step12CleanGamma
        step12NegativeAlpha step12NegativeBeta step12NegativeGamma
        step12AlternatingSum1 step12AlternatingDiff1 ∧
      step12ReducedShear03 = coordinateReducedShear03
        step12CleanAlpha step12CleanBeta step12CleanGamma
        step12NegativeAlpha step12NegativeBeta step12NegativeGamma
        step12AlternatingSum1 step12AlternatingDiff1
        step12ShearedAlternatingSum step12ShearedAlternatingDiff ∧
      step12ReducedShear33 = coordinateReducedShear33
        step12CleanAlpha step12CleanBeta step12CleanGamma
        step12NegativeAlpha step12NegativeBeta step12NegativeGamma
        step12ShearedAlternatingSum step12ShearedAlternatingDiff := by
  have hM := mixedDet_eq_sumDifference
  have hT := determinantDifference_eq_sumDifference
  have hA10 := negativeAdjugateCore_eq_sumDifference 1 0
  have hA11 := negativeAdjugateCore_eq_sumDifference 1 1
  have hA01 := negativeAdjugateCore_eq_sumDifference 0 1
  unfold step12ReducedShear03 step12ReducedShear33 step12Reduced03
    step12Reduced00 step12Reduced33
    step12ReducedResidual step12OddCleanLower step12OddPerturbationUpper
    oddPerturbationUpper11 oddPerturbationUpper13 oddPerturbationUpper33
  unfold coordinateReduced00 coordinateReducedShear03 coordinateReducedShear33
    coordinateMixed coordinateDetDifference coordinateAdjugate shearClean03
    shearPerturbation03 shearClean33 shearPerturbation33
  rw [hM, hT, hA10, hA11, hA01]
  unfold step12ShearedAlternatingSum step12ShearedAlternatingDiff
  constructor
  · ring
  constructor <;> ring

private theorem coordinateReduced00_gt_of_bounds
    (ca cb cg qa qb qg s d : ℝ)
    (hcaL : (128 / 10000 : ℝ) < ca)
    (hcbL : (-431 / 10000 : ℝ) < cb)
    (hcgL : (13738 / 10000 : ℝ) < cg)
    (hcgU : cg < (13826 / 10000 : ℝ))
    (hqaL : (49 / 10000 : ℝ) < qa)
    (hqaU : qa < (201 / 25000 : ℝ))
    (hqbL : (-101 / 2500 : ℝ) < qb)
    (hqbU : qb < (-373 / 10000 : ℝ))
    (hqgL : (103 / 125 : ℝ) < qg)
    (hqgU : qg < (2069 / 2500 : ℝ))
    (hsL : (56168 / 100000 : ℝ) < s)
    (hsU : s < (56173 / 100000 : ℝ))
    (hdL : (1687 / 100000 : ℝ) < d)
    (hdU : d < (1692 / 100000 : ℝ)) :
    (299 / 1000000 : ℝ) < coordinateReduced00 ca cb cg qa qb qg s d := by
  have hspos : 0 < s := (by norm_num : (0 : ℝ) < 56168 / 100000).trans hsL
  have hdpos : 0 < d := (by norm_num : (0 : ℝ) < 1687 / 100000).trans hdL
  have hsSqL : (56168 / 100000 : ℝ) ^ 2 < s ^ 2 :=
    pow_lt_pow_left₀ hsL (by norm_num) (by norm_num)
  have hdSqU : d ^ 2 < (1692 / 100000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hdU hdpos.le (by norm_num)
  have hsdU : s * d <
      (56173 / 100000 : ℝ) * (1692 / 100000) := by
    calc
      s * d < (56173 / 100000 : ℝ) * d :=
        mul_lt_mul_of_pos_right hsU hdpos
      _ < (56173 / 100000 : ℝ) * (1692 / 100000) :=
        mul_lt_mul_of_pos_left hdU (by norm_num)
  have hfacCa : 0 <
      (1777 / 10000 : ℝ) * qg - (1734 / 100000) * cg := by
    linarith
  have hfacCb : 0 <
      -2 * (1777 / 10000 : ℝ) * qb +
        (1734 / 100000) * (cb + (-431 / 10000)) := by
    linarith
  have hfacCg : 0 <
      (1777 / 10000 : ℝ) * qa -
        (1734 / 100000) * (128 / 10000) := by
    linarith
  have hfacQa :
      (1777 / 10000 : ℝ) * (13738 / 10000) +
          3 * (1734 / 100000) * qg - s ^ 2 < 0 := by
    nlinarith
  have hfacQb : 0 <
      -2 * (1777 / 10000 : ℝ) * (-431 / 10000) -
        3 * (1734 / 100000) * (qb + (-101 / 2500)) - 2 * s * d := by
    nlinarith
  have hfacQg : 0 <
      (1777 / 10000 : ℝ) * (128 / 10000) +
        3 * (1734 / 100000) * (201 / 25000) - d ^ 2 := by
    nlinarith
  have hfacS :
      -(201 / 25000 : ℝ) * (s + 56173 / 100000) -
          2 * (-101 / 2500) * d < 0 := by
    linarith
  have hfacD : 0 <
      -2 * (-101 / 2500 : ℝ) * (56173 / 100000) -
        (103 / 125) * (d + 1687 / 100000) := by
    linarith
  have h1 : coordinateReduced00 (128 / 10000) cb cg qa qb qg s d <
      coordinateReduced00 ca cb cg qa qb qg s d := by
    unfold coordinateReduced00 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hcaL) hfacCa]
  have h2 : coordinateReduced00 (128 / 10000) (-431 / 10000) cg qa qb qg s d <
      coordinateReduced00 (128 / 10000) cb cg qa qb qg s d := by
    unfold coordinateReduced00 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hcbL) hfacCb]
  have h3 : coordinateReduced00 (128 / 10000) (-431 / 10000)
        (13738 / 10000) qa qb qg s d <
      coordinateReduced00 (128 / 10000) (-431 / 10000) cg qa qb qg s d := by
    unfold coordinateReduced00 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hcgL) hfacCg]
  have h4 : coordinateReduced00 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) qb qg s d <
      coordinateReduced00 (128 / 10000) (-431 / 10000)
        (13738 / 10000) qa qb qg s d := by
    unfold coordinateReduced00 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hqaU) (neg_pos.mpr hfacQa)]
  have h5 : coordinateReduced00 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) qg s d <
      coordinateReduced00 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) qb qg s d := by
    unfold coordinateReduced00 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hqbL) hfacQb]
  have h6 : coordinateReduced00 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) (103 / 125) s d <
      coordinateReduced00 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) qg s d := by
    unfold coordinateReduced00 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hqgL) hfacQg]
  have h7 : coordinateReduced00 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) (103 / 125)
          (56173 / 100000) d <
      coordinateReduced00 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) (103 / 125) s d := by
    unfold coordinateReduced00 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hsU) (neg_pos.mpr hfacS)]
  have h8 : coordinateReduced00 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) (103 / 125)
          (56173 / 100000) (1687 / 100000) <
      coordinateReduced00 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) (103 / 125)
          (56173 / 100000) d := by
    unfold coordinateReduced00 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hdL) hfacD]
  have hcorner : (299 / 1000000 : ℝ) <
      coordinateReduced00 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) (103 / 125)
          (56173 / 100000) (1687 / 100000) := by
    norm_num [coordinateReduced00, coordinateMixed, coordinateDetDifference,
      coordinateAdjugate]
  exact hcorner.trans (h8.trans (h7.trans (h6.trans
    (h5.trans (h4.trans (h3.trans (h2.trans h1)))))))

private theorem coordinateReducedShear33_gt_of_bounds
    (ca cb cg qa qb qg u v : ℝ)
    (hcaL : (128 / 10000 : ℝ) < ca)
    (hcbL : (-431 / 10000 : ℝ) < cb)
    (hcbU : cb < (-345 / 10000 : ℝ))
    (hcgL : (13738 / 10000 : ℝ) < cg)
    (hqaL : (49 / 10000 : ℝ) < qa)
    (hqaU : qa < (201 / 25000 : ℝ))
    (hqbL : (-101 / 2500 : ℝ) < qb)
    (hqbU : qb < (-373 / 10000 : ℝ))
    (hqgL : (103 / 125 : ℝ) < qg)
    (huL : (-5971 / 15000 : ℝ) < u)
    (huU : u < (-29833 / 75000 : ℝ))
    (hvL : (273 / 10000 : ℝ) < v)
    (hvU : v < (1661 / 60000 : ℝ)) :
    (23 / 1000000 : ℝ) <
      coordinateReducedShear33 ca cb cg qa qb qg u v := by
  have huNeg : u < 0 := huU.trans (by norm_num)
  have hvPos : 0 < v := (by norm_num : (0 : ℝ) < 273 / 10000).trans hvL
  have huSqL : (-29833 / 75000 : ℝ) ^ 2 < u ^ 2 := by
    have hdiff : 0 < (-29833 / 75000 : ℝ) - u := sub_pos.mpr huU
    have hsum : 0 < -((-29833 / 75000 : ℝ) + u) := by linarith
    nlinarith [mul_pos hdiff hsum]
  have hvSqU : v ^ 2 < (1661 / 60000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hvU hvPos.le (by norm_num)
  have huvNeg : u * v < 0 := mul_neg_of_neg_of_pos huNeg hvPos
  have hfacCa : 0 < shearClean33 * qg - shearPerturbation33 * cg := by
    norm_num [shearClean33, shearPerturbation33] at ⊢
    linarith
  have hfacCb : 0 <
      -2 * shearClean33 * qb +
        shearPerturbation33 * (cb + (-431 / 10000)) := by
    norm_num [shearClean33, shearPerturbation33] at ⊢
    linarith
  have hfacCg : 0 <
      shearClean33 * qa - shearPerturbation33 * (128 / 10000) := by
    norm_num [shearClean33, shearPerturbation33] at ⊢
    linarith
  have hfacQa :
      shearClean33 * (13738 / 10000) +
          3 * shearPerturbation33 * qg - u ^ 2 < 0 := by
    norm_num [shearClean33, shearPerturbation33] at ⊢
    nlinarith
  have hfacQb : 0 <
      -2 * shearClean33 * (-431 / 10000) -
        3 * shearPerturbation33 * (qb + (-101 / 2500)) - 2 * u * v := by
    norm_num [shearClean33, shearPerturbation33] at ⊢
    nlinarith
  have hfacQg : 0 <
      shearClean33 * (128 / 10000) +
        3 * shearPerturbation33 * (201 / 25000) - v ^ 2 := by
    norm_num [shearClean33, shearPerturbation33] at ⊢
    nlinarith
  have hfacU : 0 <
      -(201 / 25000 : ℝ) * (u + (-5971 / 15000)) -
        2 * (-101 / 2500) * v := by
    linarith
  have hfacV :
      -2 * (-101 / 2500 : ℝ) * (-5971 / 15000) -
          (103 / 125) * (v + 1661 / 60000) < 0 := by
    linarith
  have h1 : coordinateReducedShear33 (128 / 10000) cb cg qa qb qg u v <
      coordinateReducedShear33 ca cb cg qa qb qg u v := by
    unfold coordinateReducedShear33 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hcaL) hfacCa]
  have h2 : coordinateReducedShear33 (128 / 10000) (-431 / 10000)
        cg qa qb qg u v <
      coordinateReducedShear33 (128 / 10000) cb cg qa qb qg u v := by
    unfold coordinateReducedShear33 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hcbL) hfacCb]
  have h3 : coordinateReducedShear33 (128 / 10000) (-431 / 10000)
        (13738 / 10000) qa qb qg u v <
      coordinateReducedShear33 (128 / 10000) (-431 / 10000)
        cg qa qb qg u v := by
    unfold coordinateReducedShear33 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hcgL) hfacCg]
  have h4 : coordinateReducedShear33 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) qb qg u v <
      coordinateReducedShear33 (128 / 10000) (-431 / 10000)
        (13738 / 10000) qa qb qg u v := by
    unfold coordinateReducedShear33 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hqaU) (neg_pos.mpr hfacQa)]
  have h5 : coordinateReducedShear33 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) qg u v <
      coordinateReducedShear33 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) qb qg u v := by
    unfold coordinateReducedShear33 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hqbL) hfacQb]
  have h6 : coordinateReducedShear33 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) (103 / 125) u v <
      coordinateReducedShear33 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) qg u v := by
    unfold coordinateReducedShear33 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hqgL) hfacQg]
  have h7 : coordinateReducedShear33 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) (103 / 125)
          (-5971 / 15000) v <
      coordinateReducedShear33 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) (103 / 125) u v := by
    unfold coordinateReducedShear33 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr huL) hfacU]
  have h8 : coordinateReducedShear33 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) (103 / 125)
          (-5971 / 15000) (1661 / 60000) <
      coordinateReducedShear33 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) (103 / 125)
          (-5971 / 15000) v := by
    unfold coordinateReducedShear33 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hvU) (neg_pos.mpr hfacV)]
  have hcorner : (23 / 1000000 : ℝ) <
      coordinateReducedShear33 (128 / 10000) (-431 / 10000)
        (13738 / 10000) (201 / 25000) (-101 / 2500) (103 / 125)
          (-5971 / 15000) (1661 / 60000) := by
    norm_num [coordinateReducedShear33, coordinateMixed,
      coordinateDetDifference, coordinateAdjugate, shearClean33,
      shearPerturbation33]
  exact hcorner.trans (h8.trans (h7.trans (h6.trans
    (h5.trans (h4.trans (h3.trans (h2.trans h1)))))))

set_option maxHeartbeats 800000 in
private theorem coordinateReducedShear03_bounds_of_bounds
    (ca cb cg qa qb qg s d u v : ℝ)
    (hcaL : (128 / 10000 : ℝ) < ca)
    (hcaU : ca < (216 / 10000 : ℝ))
    (hcbL : (-431 / 10000 : ℝ) < cb)
    (hcbU : cb < (-345 / 10000 : ℝ))
    (hcgL : (13738 / 10000 : ℝ) < cg)
    (hcgU : cg < (13826 / 10000 : ℝ))
    (hqaL : (49 / 10000 : ℝ) < qa)
    (hqaU : qa < (201 / 25000 : ℝ))
    (hqbL : (-101 / 2500 : ℝ) < qb)
    (hqbU : qb < (-373 / 10000 : ℝ))
    (hqgL : (103 / 125 : ℝ) < qg)
    (hqgU : qg < (2069 / 2500 : ℝ))
    (hsL : (56168 / 100000 : ℝ) < s)
    (hsU : s < (56173 / 100000 : ℝ))
    (hdL : (1687 / 100000 : ℝ) < d)
    (hdU : d < (1692 / 100000 : ℝ))
    (huL : (-5971 / 15000 : ℝ) < u)
    (huU : u < (-29833 / 75000 : ℝ))
    (hvL : (273 / 10000 : ℝ) < v)
    (hvU : v < (1661 / 60000 : ℝ)) :
    (-76 / 1000000 : ℝ) <
        coordinateReducedShear03 ca cb cg qa qb qg s d u v ∧
      coordinateReducedShear03 ca cb cg qa qb qg s d u v <
        (76 / 1000000 : ℝ) := by
  have hsPos : 0 < s := (by norm_num : (0 : ℝ) < 56168 / 100000).trans hsL
  have hdPos : 0 < d := (by norm_num : (0 : ℝ) < 1687 / 100000).trans hdL
  have huNeg : u < 0 := huU.trans (by norm_num)
  have hvPos : 0 < v := (by norm_num : (0 : ℝ) < 273 / 10000).trans hvL
  have hsuLower :
      (56173 / 100000 : ℝ) * (-5971 / 15000) < s * u := by
    calc
      (56173 / 100000 : ℝ) * (-5971 / 15000) <
          (56173 / 100000 : ℝ) * u :=
        mul_lt_mul_of_pos_left huL (by norm_num)
      _ < s * u := mul_lt_mul_of_neg_right hsU huNeg
  have hsvduPos : 0 < s * v + d * u := by
    have hsv : (56168 / 100000 : ℝ) * (273 / 10000) < s * v := by
      calc
        (56168 / 100000 : ℝ) * (273 / 10000) < s * (273 / 10000) :=
          mul_lt_mul_of_pos_right hsL (by norm_num)
        _ < s * v := mul_lt_mul_of_pos_left hvL hsPos
    have hdu : (1692 / 100000 : ℝ) * (-5971 / 15000) < d * u := by
      calc
        (1692 / 100000 : ℝ) * (-5971 / 15000) <
            (1692 / 100000 : ℝ) * u :=
          mul_lt_mul_of_pos_left huL (by norm_num)
        _ < d * u := mul_lt_mul_of_neg_right hdU huNeg
    nlinarith
  have hfacCa :
      shearClean03 * qg - shearPerturbation03 * cg < 0 := by
    norm_num [shearClean03, shearPerturbation03] at ⊢
    linarith
  have hfacCb :
      -2 * shearClean03 * qb +
          shearPerturbation03 * (cb + (-345 / 10000)) < 0 := by
    norm_num [shearClean03, shearPerturbation03] at ⊢
    linarith
  have hfacQa :
      shearClean03 * cg + 3 * shearPerturbation03 * qg - s * u < 0 := by
    norm_num [shearClean03, shearPerturbation03] at ⊢
    nlinarith
  have hfacCg : 0 <
      shearClean03 * (201 / 25000) -
        shearPerturbation03 * (216 / 10000) := by
    norm_num [shearClean03, shearPerturbation03]
  have hfacQb :
      -2 * shearClean03 * (-345 / 10000) -
          3 * shearPerturbation03 * (qb + (-373 / 10000)) -
          (s * v + d * u) < 0 := by
    norm_num [shearClean03, shearPerturbation03] at ⊢
    nlinarith
  have hfacQg :
      shearClean03 * (216 / 10000) +
          3 * shearPerturbation03 * (201 / 25000) - d * v < 0 := by
    have hdvPos : 0 < d * v := mul_pos hdPos hvPos
    norm_num [shearClean03, shearPerturbation03] at ⊢
    nlinarith
  have hfacS : 0 < -(201 / 25000 : ℝ) * u - (-373 / 10000) * v := by
    nlinarith [mul_neg_of_pos_of_neg
      (show (0 : ℝ) < 201 / 25000 by norm_num) huNeg,
      mul_neg_of_neg_of_pos (show (-373 / 10000 : ℝ) < 0 by norm_num) hvPos]
  have hfacD :
      -(-373 / 10000 : ℝ) * u - (2069 / 2500) * v < 0 := by
    nlinarith [mul_pos_of_neg_of_neg
      (show (-373 / 10000 : ℝ) < 0 by norm_num) huNeg,
      mul_pos (show (0 : ℝ) < 2069 / 2500 by norm_num) hvPos]
  have hfacU :
      -(201 / 25000 : ℝ) * (56168 / 100000) -
          (-373 / 10000) * (1692 / 100000) < 0 := by norm_num
  have hfacV : 0 <
      -(-373 / 10000 : ℝ) * (56168 / 100000) -
        (2069 / 2500) * (1692 / 100000) := by norm_num
  have hlo1 : coordinateReducedShear03 (216 / 10000) cb cg qa qb qg s d u v <
      coordinateReducedShear03 ca cb cg qa qb qg s d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hcaU) (neg_pos.mpr hfacCa)]
  have hlo2 : coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        cg qa qb qg s d u v <
      coordinateReducedShear03 (216 / 10000) cb cg qa qb qg s d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hcbU) (neg_pos.mpr hfacCb)]
  have hlo3 : coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        cg (201 / 25000) qb qg s d u v <
      coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        cg qa qb qg s d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hqaU) (neg_pos.mpr hfacQa)]
  have hlo4 : coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        (13738 / 10000) (201 / 25000) qb qg s d u v <
      coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        cg (201 / 25000) qb qg s d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hcgL) hfacCg]
  have hlo5 : coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        (13738 / 10000) (201 / 25000) (-373 / 10000) qg s d u v <
      coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        (13738 / 10000) (201 / 25000) qb qg s d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hqbU) (neg_pos.mpr hfacQb)]
  have hlo6 : coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        (13738 / 10000) (201 / 25000) (-373 / 10000) (2069 / 2500)
          s d u v <
      coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        (13738 / 10000) (201 / 25000) (-373 / 10000) qg s d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hqgU) (neg_pos.mpr hfacQg)]
  have hlo7 : coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        (13738 / 10000) (201 / 25000) (-373 / 10000) (2069 / 2500)
          (56168 / 100000) d u v <
      coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        (13738 / 10000) (201 / 25000) (-373 / 10000) (2069 / 2500)
          s d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hsL) hfacS]
  have hlo8 : coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        (13738 / 10000) (201 / 25000) (-373 / 10000) (2069 / 2500)
          (56168 / 100000) (1692 / 100000) u v <
      coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        (13738 / 10000) (201 / 25000) (-373 / 10000) (2069 / 2500)
          (56168 / 100000) d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hdU) (neg_pos.mpr hfacD)]
  have hlo9 : coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        (13738 / 10000) (201 / 25000) (-373 / 10000) (2069 / 2500)
          (56168 / 100000) (1692 / 100000) (-29833 / 75000) v <
      coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        (13738 / 10000) (201 / 25000) (-373 / 10000) (2069 / 2500)
          (56168 / 100000) (1692 / 100000) u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr huU) (neg_pos.mpr hfacU)]
  have hlo10 : coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        (13738 / 10000) (201 / 25000) (-373 / 10000) (2069 / 2500)
          (56168 / 100000) (1692 / 100000) (-29833 / 75000)
          (273 / 10000) <
      coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        (13738 / 10000) (201 / 25000) (-373 / 10000) (2069 / 2500)
          (56168 / 100000) (1692 / 100000) (-29833 / 75000) v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hvL) hfacV]
  have hloCorner : (-76 / 1000000 : ℝ) <
      coordinateReducedShear03 (216 / 10000) (-345 / 10000)
        (13738 / 10000) (201 / 25000) (-373 / 10000) (2069 / 2500)
          (56168 / 100000) (1692 / 100000) (-29833 / 75000)
          (273 / 10000) := by
    norm_num [coordinateReducedShear03, coordinateMixed,
      coordinateDetDifference, coordinateAdjugate, shearClean03,
      shearPerturbation03]
  have hlo := hloCorner.trans (hlo10.trans (hlo9.trans (hlo8.trans
    (hlo7.trans (hlo6.trans (hlo5.trans (hlo4.trans
      (hlo3.trans (hlo2.trans hlo1)))))))))
  refine ⟨hlo, ?_⟩
  have hfacCbUpper :
      -2 * shearClean03 * qb +
          shearPerturbation03 * (cb + (-431 / 10000)) < 0 := by
    norm_num [shearClean03, shearPerturbation03] at ⊢
    linarith
  have hfacCgUpper : 0 <
      shearClean03 * (49 / 10000) -
        shearPerturbation03 * (128 / 10000) := by
    norm_num [shearClean03, shearPerturbation03]
  have hfacQbUpper :
      -2 * shearClean03 * (-431 / 10000) -
          3 * shearPerturbation03 * (qb + (-101 / 2500)) -
          (s * v + d * u) < 0 := by
    norm_num [shearClean03, shearPerturbation03] at ⊢
    nlinarith
  have hfacQgUpper :
      shearClean03 * (128 / 10000) +
          3 * shearPerturbation03 * (49 / 10000) - d * v < 0 := by
    have hdvPos : 0 < d * v := mul_pos hdPos hvPos
    norm_num [shearClean03, shearPerturbation03] at ⊢
    nlinarith
  have hfacSUpper : 0 <
      -(49 / 10000 : ℝ) * u - (-101 / 2500) * v := by
    nlinarith [mul_neg_of_pos_of_neg
      (show (0 : ℝ) < 49 / 10000 by norm_num) huNeg,
      mul_neg_of_neg_of_pos (show (-101 / 2500 : ℝ) < 0 by norm_num) hvPos]
  have hfacDUpper :
      -(-101 / 2500 : ℝ) * u - (103 / 125) * v < 0 := by
    nlinarith [mul_pos_of_neg_of_neg
      (show (-101 / 2500 : ℝ) < 0 by norm_num) huNeg,
      mul_pos (show (0 : ℝ) < 103 / 125 by norm_num) hvPos]
  have hfacUUpper :
      -(49 / 10000 : ℝ) * (56173 / 100000) -
          (-101 / 2500) * (1687 / 100000) < 0 := by norm_num
  have hfacVUpper : 0 <
      -(-101 / 2500 : ℝ) * (56173 / 100000) -
        (103 / 125) * (1687 / 100000) := by norm_num
  have hup1 : coordinateReducedShear03 ca cb cg qa qb qg s d u v <
      coordinateReducedShear03 (128 / 10000) cb cg qa qb qg s d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hcaL) (neg_pos.mpr hfacCa)]
  have hup2 : coordinateReducedShear03 (128 / 10000) cb cg qa qb qg s d u v <
      coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        cg qa qb qg s d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hcbL) (neg_pos.mpr hfacCbUpper)]
  have hup3 : coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        cg qa qb qg s d u v <
      coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        cg (49 / 10000) qb qg s d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hqaL) (neg_pos.mpr hfacQa)]
  have hup4 : coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        cg (49 / 10000) qb qg s d u v <
      coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        (13826 / 10000) (49 / 10000) qb qg s d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hcgU) hfacCgUpper]
  have hup5 : coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        (13826 / 10000) (49 / 10000) qb qg s d u v <
      coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        (13826 / 10000) (49 / 10000) (-101 / 2500) qg s d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hqbL) (neg_pos.mpr hfacQbUpper)]
  have hup6 : coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        (13826 / 10000) (49 / 10000) (-101 / 2500) qg s d u v <
      coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        (13826 / 10000) (49 / 10000) (-101 / 2500) (103 / 125)
          s d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hqgL) (neg_pos.mpr hfacQgUpper)]
  have hup7 : coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        (13826 / 10000) (49 / 10000) (-101 / 2500) (103 / 125)
          s d u v <
      coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        (13826 / 10000) (49 / 10000) (-101 / 2500) (103 / 125)
          (56173 / 100000) d u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hsU) hfacSUpper]
  have hup8 : coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        (13826 / 10000) (49 / 10000) (-101 / 2500) (103 / 125)
          (56173 / 100000) d u v <
      coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        (13826 / 10000) (49 / 10000) (-101 / 2500) (103 / 125)
          (56173 / 100000) (1687 / 100000) u v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hdL) (neg_pos.mpr hfacDUpper)]
  have hup9 : coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        (13826 / 10000) (49 / 10000) (-101 / 2500) (103 / 125)
          (56173 / 100000) (1687 / 100000) u v <
      coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        (13826 / 10000) (49 / 10000) (-101 / 2500) (103 / 125)
          (56173 / 100000) (1687 / 100000) (-5971 / 15000) v := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr huL) (neg_pos.mpr hfacUUpper)]
  have hup10 : coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        (13826 / 10000) (49 / 10000) (-101 / 2500) (103 / 125)
          (56173 / 100000) (1687 / 100000) (-5971 / 15000) v <
      coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        (13826 / 10000) (49 / 10000) (-101 / 2500) (103 / 125)
          (56173 / 100000) (1687 / 100000) (-5971 / 15000)
          (1661 / 60000) := by
    unfold coordinateReducedShear03 coordinateMixed coordinateDetDifference
      coordinateAdjugate
    nlinarith only [mul_pos (sub_pos.mpr hvU) hfacVUpper]
  have hupCorner :
      coordinateReducedShear03 (128 / 10000) (-431 / 10000)
        (13826 / 10000) (49 / 10000) (-101 / 2500) (103 / 125)
          (56173 / 100000) (1687 / 100000) (-5971 / 15000)
          (1661 / 60000) < (76 / 1000000 : ℝ) := by
    norm_num [coordinateReducedShear03, coordinateMixed,
      coordinateDetDifference, coordinateAdjugate, shearClean03,
      shearPerturbation03]
  exact hup1.trans (hup2.trans (hup3.trans (hup4.trans
    (hup5.trans (hup6.trans (hup7.trans (hup8.trans
      (hup9.trans (hup10.trans hupCorner)))))))))

theorem step12ReducedCoefficient_bounds :
    (299 / 1000000 : ℝ) < step12Reduced00 ∧
      |step12ReducedShear03| < (76 / 1000000 : ℝ) ∧
      (23 / 1000000 : ℝ) < step12ReducedShear33 := by
  rcases step12CleanCoordinate_bounds with
    ⟨hcaL, hcaU, hcbL, hcbU, hcgL, hcgU⟩
  rcases step12NegativeCoordinate_bounds with
    ⟨hqaL, hqaU, hqbL, hqbU, hqgL, hqgU⟩
  rcases step12AlternatingCoordinate_bounds with
    ⟨hsL, hsU, hdL, hdU, huL, huU, hvL, hvU⟩
  rcases step12ReducedCoefficients_eq_coordinates with ⟨hEqA, hEqB, hEqD⟩
  have hA := coordinateReduced00_gt_of_bounds
    step12CleanAlpha step12CleanBeta step12CleanGamma
    step12NegativeAlpha step12NegativeBeta step12NegativeGamma
    step12AlternatingSum1 step12AlternatingDiff1
    hcaL hcbL hcgL hcgU hqaL hqaU hqbL hqbU hqgL hqgU
    hsL hsU hdL hdU
  have hB := coordinateReducedShear03_bounds_of_bounds
    step12CleanAlpha step12CleanBeta step12CleanGamma
    step12NegativeAlpha step12NegativeBeta step12NegativeGamma
    step12AlternatingSum1 step12AlternatingDiff1
    step12ShearedAlternatingSum step12ShearedAlternatingDiff
    hcaL hcaU hcbL hcbU hcgL hcgU hqaL hqaU hqbL hqbU hqgL hqgU
    hsL hsU hdL hdU huL huU hvL hvU
  have hD := coordinateReducedShear33_gt_of_bounds
    step12CleanAlpha step12CleanBeta step12CleanGamma
    step12NegativeAlpha step12NegativeBeta step12NegativeGamma
    step12ShearedAlternatingSum step12ShearedAlternatingDiff
    hcaL hcbL hcbU hcgL hqaL hqaU hqbL hqbU hqgL
    huL huU hvL hvU
  rw [hEqA, hEqB, hEqD]
  refine ⟨hA, ?_, hD⟩
  rw [abs_lt]
  norm_num at hB ⊢
  exact hB

theorem step12ReducedShear_principal_minors_pos :
    0 < step12Reduced00 ∧
      0 < step12ReducedShear33 ∧
      0 < step12Reduced00 * step12ReducedShear33 -
        step12ReducedShear03 ^ 2 := by
  rcases step12ReducedCoefficient_bounds with ⟨hA, hB, hD⟩
  have hApos : 0 < step12Reduced00 :=
    (by norm_num : (0 : ℝ) < 299 / 1000000).trans hA
  have hDpos : 0 < step12ReducedShear33 :=
    (by norm_num : (0 : ℝ) < 23 / 1000000).trans hD
  have hprod :
      (299 / 1000000 : ℝ) * (23 / 1000000) <
        step12Reduced00 * step12ReducedShear33 :=
    mul_lt_mul hA hD.le (by norm_num) hApos.le
  rcases abs_lt.mp hB with ⟨hBLower, hBUpper⟩
  have hBsq : step12ReducedShear03 ^ 2 <
      (76 / 1000000 : ℝ) ^ 2 := by
    have hmul : 0 <
        ((76 / 1000000 : ℝ) - step12ReducedShear03) *
          ((76 / 1000000 : ℝ) + step12ReducedShear03) :=
      mul_pos (sub_pos.mpr hBUpper) (by linarith)
    nlinarith
  have hrat :
      (76 / 1000000 : ℝ) ^ 2 <
        (299 / 1000000) * (23 / 1000000) := by norm_num
  exact ⟨hApos, hDpos, by nlinarith⟩

/-- The reduced Step12 residual is a single positive-definite sheared
`2 × 2` quadratic. -/
theorem step12ReducedResidual_nonneg (c d : ℝ) :
    0 ≤ step12ReducedResidual c d := by
  rcases step12ReducedShear_principal_minors_pos with ⟨hA, hD, hdet⟩
  have hgates :
      0 ≤ step12Reduced00 ∧
        0 ≤ step12ReducedShear33 ∧
        step12ReducedShear03 ^ 2 ≤
          step12Reduced00 * step12ReducedShear33 :=
    ⟨hA.le, hD.le, by linarith⟩
  have hquad := (real_quadratic_pencil_nonneg_iff
    step12Reduced00 step12ReducedShear33 step12ReducedShear03).mpr hgates
  rw [step12ReducedResidual_eq_sheared]
  exact hquad (c + (5 / 3 : ℝ) * d) d

theorem step12ReducedResidual_nonneg_all :
    ∀ c d : ℝ, 0 ≤ step12ReducedResidual c d :=
  step12ReducedResidual_nonneg

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep12ResidualPositive
