import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedOddShearStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusPositiveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedAlternatingModelsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP1P3ShearCorrelationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusMinorStructural

noncomputable section

open MeasureTheory Real Set
open CenteredEndpointCorrelation
open ThreeByThreeRankOneSchur
open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointEvenTailRepresenter
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp
open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusPositive
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01MidpointReserve
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
open YoshidaFactorTwoPhaseIntrinsicOddP1P3ShearCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotCombinedReserveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedOddShearStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedAlternatingModelsStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural

/-!
# The second negative static Schur gate

The odd basis is changed from `(P₁, P₃)` to `(P₁, P₃ - P₁)`.
This determinant-one shear exposes the small polarized entry without
separating the two alternating columns before their cancellation.
-/

/-- The first fraction-free pivot, named for reuse by the bordered `P₅`
step. -/
def factorTwoIntrinsicSixUnbalancedTMinusShearA : ℝ :=
  factorTwoIntrinsicSixUnbalancedTMinus11

/-- Polarization between `P₁` and the sheared direction `P₃ - P₁`. -/
def factorTwoIntrinsicSixUnbalancedTMinusShearP : ℝ :=
  factorTwoIntrinsicSixUnbalancedTMinus13 -
    factorTwoIntrinsicSixUnbalancedTMinus11

/-- Fraction-free diagonal in the sheared direction `P₃ - P₁`. -/
def factorTwoIntrinsicSixUnbalancedTMinusShearQ : ℝ :=
  factorTwoIntrinsicSixUnbalancedTMinus11 -
    2 * factorTwoIntrinsicSixUnbalancedTMinus13 +
    factorTwoIntrinsicSixUnbalancedTMinus33

theorem factorTwoIntrinsicSixUnbalancedTMinusShearQ_eq_fractionFree :
    factorTwoIntrinsicSixUnbalancedTMinusShearQ =
      factorTwoIntrinsicSixUnbalancedEMinusDet *
          symmetricQuadratic
            factorTwoIntrinsicSixUnbalancedOPlus11
            factorTwoIntrinsicSixUnbalancedOPlus13
            factorTwoIntrinsicSixUnbalancedOPlus15
            factorTwoIntrinsicSixUnbalancedOPlus33
            factorTwoIntrinsicSixUnbalancedOPlus35
            factorTwoIntrinsicSixUnbalancedOPlus55 (-1) 1 0 -
        adjugateQuadratic
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44
          (factorTwoIntrinsicSixUnbalancedKMinus03 -
            factorTwoIntrinsicSixUnbalancedKMinus01)
          (factorTwoIntrinsicSixUnbalancedKMinus23 -
            factorTwoIntrinsicSixUnbalancedKMinus21)
          (factorTwoIntrinsicSixUnbalancedKMinus43 -
            factorTwoIntrinsicSixUnbalancedKMinus41) := by
  have h := factorTwoIntrinsicSixUnbalancedTMinusQuadratic_eq_fractionFree
    (-1) 1 0
  unfold factorTwoIntrinsicSixUnbalancedTMinusShearQ
  simp only [factorTwoIntrinsicSixUnbalancedTMinusQuadratic,
    symmetricQuadratic, mul_zero, add_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h ⊢
  convert h using 1 <;> ring_nf

/-! ## Aligned even coordinates and the bordered shear -/

/-- Strong coordinate of the negative `P₀/P₂` plane. -/
def factorTwoIntrinsicSixUnbalancedEMinusStrong : ℝ :=
  factorTwoIntrinsicSixUnbalancedEMinus00 +
    2 * factorTwoIntrinsicSixUnbalancedEMinus02 +
    factorTwoIntrinsicSixUnbalancedEMinus22

/-- Skew coordinate of the negative `P₀/P₂` plane. -/
def factorTwoIntrinsicSixUnbalancedEMinusSkew : ℝ :=
  factorTwoIntrinsicSixUnbalancedEMinus00 -
    factorTwoIntrinsicSixUnbalancedEMinus22

/-- Weak coordinate of the negative `P₀/P₂` plane. -/
def factorTwoIntrinsicSixUnbalancedEMinusWeak : ℝ :=
  factorTwoIntrinsicSixUnbalancedEMinus00 -
    2 * factorTwoIntrinsicSixUnbalancedEMinus02 +
    factorTwoIntrinsicSixUnbalancedEMinus22

/-- Sum of the two negative-endpoint `P₄` crosses. -/
def factorTwoIntrinsicSixUnbalancedEMinusP4Sum : ℝ :=
  factorTwoIntrinsicSixUnbalancedEMinus04 +
    factorTwoIntrinsicSixUnbalancedEMinus24

/-- Difference of the two negative-endpoint `P₄` crosses. -/
def factorTwoIntrinsicSixUnbalancedEMinusP4Difference : ℝ :=
  factorTwoIntrinsicSixUnbalancedEMinus24 -
    factorTwoIntrinsicSixUnbalancedEMinus04

/-- Determinant of a symmetric three-by-three matrix in the aligned
`P₀/P₂` coordinates. -/
def minusAlignedDeterminant (U K W S T F : ℝ) : ℝ :=
  (F * (U * W - K ^ 2) -
      (W * S ^ 2 + U * T ^ 2 + 2 * K * S * T)) / 4

/-- Polarized adjugate pairing in the same aligned coordinates. -/
def minusAlignedAdjugatePair
    (U K W S T F X Y Z R V H : ℝ) : ℝ :=
  ((F * W - T ^ 2) * X * R +
      (F * U - S ^ 2) * Y * V +
      (-F * K - S * T) * (X * V + Y * R) +
      (-W * S - K * T) * (X * H + Z * R) +
      (K * S + U * T) * (Y * H + Z * V) +
      (U * W - K ^ 2) * Z * H) / 4

/-- Aligned coordinates of the corrected `P₁` cross column. -/
def factorTwoIntrinsicSixUnbalancedKMinusOneSum : ℝ :=
  factorTwoIntrinsicSixUnbalancedKMinus01 +
    factorTwoIntrinsicSixUnbalancedKMinus21

def factorTwoIntrinsicSixUnbalancedKMinusOneDifference : ℝ :=
  factorTwoIntrinsicSixUnbalancedKMinus01 -
    factorTwoIntrinsicSixUnbalancedKMinus21

/-- Aligned coordinates of the sheared `P₃ - P₁` cross column. -/
def factorTwoIntrinsicSixUnbalancedKMinusShearSum : ℝ :=
  (factorTwoIntrinsicSixUnbalancedKMinus03 -
      factorTwoIntrinsicSixUnbalancedKMinus01) +
    (factorTwoIntrinsicSixUnbalancedKMinus23 -
      factorTwoIntrinsicSixUnbalancedKMinus21)

def factorTwoIntrinsicSixUnbalancedKMinusShearDifference : ℝ :=
  (factorTwoIntrinsicSixUnbalancedKMinus03 -
      factorTwoIntrinsicSixUnbalancedKMinus01) -
    (factorTwoIntrinsicSixUnbalancedKMinus23 -
      factorTwoIntrinsicSixUnbalancedKMinus21)

def factorTwoIntrinsicSixUnbalancedKMinusShearTail : ℝ :=
  factorTwoIntrinsicSixUnbalancedKMinus43 -
    factorTwoIntrinsicSixUnbalancedKMinus41

def factorTwoIntrinsicSixUnbalancedOPlusShearCross : ℝ :=
  factorTwoIntrinsicSixUnbalancedOPlus13 -
    factorTwoIntrinsicSixUnbalancedOPlus11

def factorTwoIntrinsicSixUnbalancedOPlusShearDiagonal : ℝ :=
  factorTwoIntrinsicSixUnbalancedOPlus11 -
    2 * factorTwoIntrinsicSixUnbalancedOPlus13 +
    factorTwoIntrinsicSixUnbalancedOPlus33

/-! ## Coupled `P₄/(P₃-P₁)` alternating coordinate -/

/-- The alternating profile is kept as a difference before the regular
kernel estimate is applied.  This is the cancellation needed by the
sheared `P₄` coordinate. -/
def alternatingQ43SubQ41 (t : ℝ) : ℝ :=
  alternatingQ43 t - alternatingQ41 t

theorem intrinsicAlternatingCorrelation_q43SubQ41_eq_sub (t : ℝ) :
    intrinsicAlternatingCorrelation alternatingQ43SubQ41 t =
      intrinsicAlternatingCorrelation alternatingQ43 t -
        intrinsicAlternatingCorrelation alternatingQ41 t := by
  unfold intrinsicAlternatingCorrelation alternatingQ43SubQ41
  ring

/-- Exact structural model for the coupled alternating shear. -/
theorem factorTwoIntrinsicFourP45Cross43_sub_cross41_eq_structuralModel :
    factorTwoIntrinsicFourP45Cross43 -
        factorTwoIntrinsicFourP45Cross41 =
      intrinsicAlternatingRegularError alternatingQ43SubQ41 +
        intrinsicAlternatingArchModel alternatingQ43SubQ41 -
      (Real.log 3 / Real.sqrt 3) *
        intrinsicAlternatingCorrelation alternatingQ43SubQ41
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  rw [factorTwoIntrinsicFourP45Cross43_eq_structuralModel,
    factorTwoIntrinsicFourP45Cross41_eq_structuralModel]
  have hq43 : Continuous alternatingQ43 := by
    unfold alternatingQ43
    fun_prop
  have hq41 : Continuous alternatingQ41 := by
    unfold alternatingQ41
    fun_prop
  rw [show alternatingQ43SubQ41 = alternatingQ43 - alternatingQ41 by
      funext t
      rfl,
    intrinsicAlternatingRegularError_sub alternatingQ43 alternatingQ41
      hq43 hq41,
    intrinsicAlternatingArchModel_sub alternatingQ43 alternatingQ41
      hq43 hq41]
  unfold intrinsicAlternatingCorrelation
  simp only [Pi.sub_apply]
  ring

theorem intrinsicAlternatingCorrelation_q43SubQ41_eq_polynomial (t : ℝ) :
    intrinsicAlternatingCorrelation alternatingQ43SubQ41 t =
      -5 * t ^ 2 + (35 / 3 : ℝ) * t ^ 3 -
        (15 / 2 : ℝ) * t ^ 4 + (25 / 24 : ℝ) * t ^ 6 -
        (5 / 64 : ℝ) * t ^ 8 := by
  unfold intrinsicAlternatingCorrelation alternatingQ43SubQ41
    alternatingQ43 alternatingQ41
  ring

theorem integral_sq_intrinsicAlternatingCorrelation_q43SubQ41 :
    (∫ t : ℝ in 0..2,
      intrinsicAlternatingCorrelation alternatingQ43SubQ41 t ^ 2) =
        (1280 / 35343 : ℝ) := by
  rw [show
      (fun t : ℝ ↦
        intrinsicAlternatingCorrelation alternatingQ43SubQ41 t ^ 2) =
      fun t ↦
        25 * t ^ 4 - (350 / 3 : ℝ) * t ^ 5 +
          (1900 / 9 : ℝ) * t ^ 6 - 175 * t ^ 7 +
          (275 / 6 : ℝ) * t ^ 8 + (875 / 36 : ℝ) * t ^ 9 -
          (475 / 32 : ℝ) * t ^ 10 - (175 / 96 : ℝ) * t ^ 11 +
          (325 / 144 : ℝ) * t ^ 12 - (125 / 768 : ℝ) * t ^ 14 +
          (25 / 4096 : ℝ) * t ^ 16 by
    funext t
    rw [intrinsicAlternatingCorrelation_q43SubQ41_eq_polynomial]
    ring]
  norm_num [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, integral_pow]

/-- A single Cauchy--Schwarz estimate is applied after the `P₃-P₁`
cancellation, rather than to the two columns separately. -/
theorem integral_abs_intrinsicAlternatingCorrelation_q43SubQ41_lt :
    (∫ t : ℝ in 0..2,
      |intrinsicAlternatingCorrelation alternatingQ43SubQ41 t|) <
        (27 / 100 : ℝ) := by
  have hcs := sq_intervalIntegral_mul_le_zero_two
    (fun _ : ℝ ↦ 1)
    (fun t ↦ |intrinsicAlternatingCorrelation alternatingQ43SubQ41 t|)
    continuous_const
    (by
      unfold intrinsicAlternatingCorrelation alternatingQ43SubQ41
        alternatingQ43 alternatingQ41
      fun_prop)
  simp only [one_mul, one_pow, sq_abs] at hcs
  rw [show (∫ _t : ℝ in 0..2, (1 : ℝ)) = 2 by norm_num,
    integral_sq_intrinsicAlternatingCorrelation_q43SubQ41] at hcs
  have hnonneg : 0 ≤ ∫ t : ℝ in 0..2,
      |intrinsicAlternatingCorrelation alternatingQ43SubQ41 t| :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ abs_nonneg _)
  have hrat :
      (2 : ℝ) * (1280 / 35343) < (27 / 100 : ℝ) ^ 2 := by
    norm_num
  nlinarith

theorem abs_intrinsicAlternatingRegularError_q43SubQ41_lt :
    |intrinsicAlternatingRegularError alternatingQ43SubQ41| <
      (27 / 100000 : ℝ) := by
  have hregular := abs_intrinsicAlternatingRegularError_le
    alternatingQ43SubQ41 (by
      unfold alternatingQ43SubQ41 alternatingQ43 alternatingQ41
      fun_prop)
  have hL1 :=
    integral_abs_intrinsicAlternatingCorrelation_q43SubQ41_lt
  calc
    |intrinsicAlternatingRegularError alternatingQ43SubQ41| ≤
        (1 / 1000 : ℝ) *
          (∫ t : ℝ in 0..2,
            |intrinsicAlternatingCorrelation alternatingQ43SubQ41 t|) :=
      hregular
    _ < (1 / 1000 : ℝ) * (27 / 100 : ℝ) :=
      mul_lt_mul_of_pos_left hL1 (by norm_num)
    _ = (27 / 100000 : ℝ) := by norm_num

private theorem integral_inv_two_add_q43SubQ41 :
    (∫ t : ℝ in 0..2, 1 / (2 + t)) = Real.log 2 := by
  let F : ℝ → ℝ := fun t ↦ Real.log (2 + t)
  have hderiv (t : ℝ) (ht : 2 + t ≠ 0) :
      HasDerivAt F (1 / (2 + t)) t := by
    have hadd : HasDerivAt (fun x : ℝ ↦ 2 + x) 1 t := by
      simpa using (hasDerivAt_const t 2).add (hasDerivAt_id t)
    simpa only [F, Function.comp_apply, one_div, mul_one] using
      (Real.hasDerivAt_log ht).comp t hadd
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / (2 + t))
      (uIcc (0 : ℝ) 2) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 2 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have hne : 2 + t ≠ 0 := by linarith [ht'.1]
    exact (continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hderiv t (by
      have ht' : t ∈ Icc (0 : ℝ) 2 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
      linarith [ht'.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num
  rw [show Real.log 4 = 2 * Real.log 2 by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
    ring]
  ring

private theorem intervalIntegrable_inv_two_add_q43SubQ41 :
    IntervalIntegrable (fun t : ℝ ↦ 1 / (2 + t)) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have hne : 2 + t ≠ 0 := by linarith [ht'.1]
  exact (continuousAt_const.div
    (continuousAt_const.add continuousAt_id) hne).continuousWithinAt

theorem intrinsicAlternatingArchModel_q43SubQ41 :
    intrinsicAlternatingArchModel alternatingQ43SubQ41 =
      (-1165 / 18 : ℝ) + (280 / 3 : ℝ) * Real.log 2 := by
  let p : ℝ → ℝ := fun t ↦
    (-140 / 3 : ℝ) + (70 / 3 : ℝ) * t -
      (35 / 3 : ℝ) * t ^ 2 + (49 / 12 : ℝ) * t ^ 3 +
      (7 / 6 : ℝ) * t ^ 4 - (71 / 48 : ℝ) * t ^ 5 +
      (35 / 192 : ℝ) * t ^ 7 - (1 / 128 : ℝ) * t ^ 9
  have hint : intrinsicAlternatingArchModel alternatingQ43SubQ41 =
      ∫ t : ℝ in 0..2,
        p t + (280 / 3 : ℝ) * (1 / (2 + t)) := by
    unfold intrinsicAlternatingArchModel intrinsicAlternatingCorrelation
      alternatingQ43SubQ41 alternatingQ43 alternatingQ41
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have hden : 2 + t ≠ 0 := by linarith [ht.1]
    dsimp only [p]
    field_simp [hden]
    ring
  have hp : IntervalIntegrable p volume 0 2 := by
    exact (by dsimp only [p]; fun_prop : Continuous p).intervalIntegrable 0 2
  rw [hint, intervalIntegral.integral_add hp
      (intervalIntegrable_inv_two_add_q43SubQ41.const_mul (280 / 3)),
    intervalIntegral.integral_const_mul, integral_inv_two_add_q43SubQ41]
  dsimp only [p]
  ring_nf
  repeat' first
    | rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

theorem intrinsicAlternatingCorrelation_q43SubQ41_prime_bounds :
    (18454 / 100000 : ℝ) <
        intrinsicAlternatingCorrelation alternatingQ43SubQ41
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation alternatingQ43SubQ41
          (factorTwoPrimeShift / yoshidaEndpointA) <
        (18455 / 100000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 11699 / 10000
  have htau := factorTwoPrimeRatio_kernel_bounds
  have hy0 : 0 < y := by
    dsimp only [y, tau]
    linarith [htau.1]
  have hyU : y < (1 / 10000 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 : y ^ 2 < (1 / 10000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hyU hy0.le (by norm_num)
  have hy3 : y ^ 3 < (1 / 10000 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hyU hy0.le (by norm_num)
  have hy4 : y ^ 4 < (1 / 10000 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hyU hy0.le (by norm_num)
  have hy5 : y ^ 5 < (1 / 10000 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ hyU hy0.le (by norm_num)
  have hy6 : y ^ 6 < (1 / 10000 : ℝ) ^ 6 :=
    pow_lt_pow_left₀ hyU hy0.le (by norm_num)
  have hy7 : y ^ 7 < (1 / 10000 : ℝ) ^ 7 :=
    pow_lt_pow_left₀ hyU hy0.le (by norm_num)
  have hy8 : y ^ 8 < (1 / 10000 : ℝ) ^ 8 :=
    pow_lt_pow_left₀ hyU hy0.le (by norm_num)
  have hy2n : 0 ≤ y ^ 2 := sq_nonneg y
  have hy3n : 0 ≤ y ^ 3 := by positivity
  have hy4n : 0 ≤ y ^ 4 := by positivity
  have hy5n : 0 ≤ y ^ 5 := by positivity
  have hy6n : 0 ≤ y ^ 6 := by positivity
  have hy7n : 0 ≤ y ^ 7 := by positivity
  have hy8n : 0 ≤ y ^ 8 := by positivity
  have htauy : tau = 11699 / 10000 + y := by
    dsimp only [y]
    ring
  dsimp only [tau] at htauy ⊢
  rw [htauy]
  rw [intrinsicAlternatingCorrelation_q43SubQ41_eq_polynomial]
  ring_nf
  constructor <;>
    nlinarith [hy2, hy3, hy4, hy5, hy6, hy7, hy8,
      hy2n, hy3n, hy4n, hy5n, hy6n, hy7n, hy8n]

/-- Quantitative coupled enclosure for the two `P₄` alternating columns. -/
theorem factorTwoIntrinsicFourP45Cross43_sub_cross41_bounds :
    (-146 / 1000 : ℝ) <
        factorTwoIntrinsicFourP45Cross43 -
          factorTwoIntrinsicFourP45Cross41 ∧
      factorTwoIntrinsicFourP45Cross43 -
          factorTwoIntrinsicFourP45Cross41 < (-145 / 1000 : ℝ) := by
  rw [factorTwoIntrinsicFourP45Cross43_sub_cross41_eq_structuralModel,
    intrinsicAlternatingArchModel_q43SubQ41]
  have herr := abs_lt.mp
    abs_intrinsicAlternatingRegularError_q43SubQ41_lt
  have hcorr := intrinsicAlternatingCorrelation_q43SubQ41_prime_bounds
  have hlog := strict_log_two_fine_bounds
  have hbeta := log_three_div_sqrt_three_kernel_bounds
  have hbeta0 : 0 < Real.log 3 / Real.sqrt 3 := by
    linarith [hbeta.1]
  have hcorr0 : 0 <
      intrinsicAlternatingCorrelation alternatingQ43SubQ41
        (factorTwoPrimeShift / yoshidaEndpointA) := by
    linarith [hcorr.1]
  have hprodLower :
      (63427 / 100000 : ℝ) * (18454 / 100000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation alternatingQ43SubQ41
            (factorTwoPrimeShift / yoshidaEndpointA) := by
    calc
      _ < (Real.log 3 / Real.sqrt 3) * (18454 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hcorr.1 hbeta0
  have hprodUpper :
      (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation alternatingQ43SubQ41
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (6343 / 10000 : ℝ) * (18455 / 100000 : ℝ) := by
    calc
      _ < (6343 / 10000 : ℝ) *
          intrinsicAlternatingCorrelation alternatingQ43SubQ41
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hbeta.2 hcorr0
      _ < _ := mul_lt_mul_of_pos_left hcorr.2 (by norm_num)
  constructor <;>
    nlinarith [herr.1, herr.2, hlog.1, hlog.2,
      hprodLower, hprodUpper]

/-- Tight sheared `P₄` tail bound, retaining the correlation of the two
alternating columns. -/
theorem factorTwoIntrinsicSixUnbalancedKMinusShearTail_bounds :
    (-562 / 10000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedKMinusShearTail ∧
      factorTwoIntrinsicSixUnbalancedKMinusShearTail <
        (-557 / 10000 : ℝ) := by
  have hcross := factorTwoIntrinsicFourP45Cross43_sub_cross41_bounds
  unfold factorTwoIntrinsicSixUnbalancedKMinusShearTail
    factorTwoIntrinsicSixUnbalancedKMinus43
    factorTwoIntrinsicSixUnbalancedKMinus41
  constructor <;> linarith [hcross.1, hcross.2]

theorem factorTwoIntrinsicSixUnbalancedKMinusShearLow_bounds :
    (-6379 / 100000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedKMinusShearSum ∧
      factorTwoIntrinsicSixUnbalancedKMinusShearSum <
        (-3183 / 50000 : ℝ) ∧
      (1269 / 100000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedKMinusShearDifference ∧
      factorTwoIntrinsicSixUnbalancedKMinusShearDifference <
        (2573 / 200000 : ℝ) := by
  rcases factorTwoIntrinsicAlternatingSharpBounds with
    ⟨hs1L, hs1U, hd1L, hd1U, hs3L, hs3U, hd3L, hd3U⟩
  unfold factorTwoIntrinsicSixUnbalancedKMinusShearSum
    factorTwoIntrinsicSixUnbalancedKMinusShearDifference
    factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicSixUnbalancedKMinus03
    factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicSixUnbalancedKMinus23
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-! ## Integrated lower Gram for the two sheared odd directions -/

/-- The integrated pole-free envelope recovers the weak even reserve which
is lost by a pointwise Taylor charge. -/
def factorTwoIntrinsicSixUnbalancedMinorMinusLower00 : ℝ :=
  59347 / 100000

def factorTwoIntrinsicSixUnbalancedMinorMinusLower02 : ℝ :=
  54506 / 100000

def factorTwoIntrinsicSixUnbalancedMinorMinusLower22 : ℝ :=
  51529 / 100000

private def minorEvenNegativePerturbationTaylor00 : ℝ :=
  evenNegativePerturbationTaylor00 + 11 / 20000

private def minorEvenNegativePerturbationTaylor02 : ℝ :=
  evenNegativePerturbationTaylor02

private def minorEvenNegativePerturbationTaylor22 : ℝ :=
  evenNegativePerturbationTaylor22 + 11 / 100000

private theorem minorEvenNegativePerturbationTaylor_quadratic_le
    (c d : ℝ) :
    minorEvenNegativePerturbationTaylor00 * c ^ 2 +
        2 * minorEvenNegativePerturbationTaylor02 * c * d +
        minorEvenNegativePerturbationTaylor22 * d ^ 2 ≤
      -factorTwoCenteredSymmetricPerturbation
        (factorTwoEvenStructuralLowProfile c d) := by
  have herr := abs_poleFreeAnalyticError_profile_refined_le c d
  have herrUpper :
      poleFreeAnalyticError
          (centeredEndpointCorrelation
            (factorTwoEvenStructuralLowProfile c d)) ≤
        (1 / 10000 : ℝ) * (2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2) :=
    (le_abs_self _).trans herr
  rw [factorTwoCenteredSymmetricPerturbation_even_profile_kernel_eq,
    evenStructuralRegularError_profile_sharp_expansion]
  unfold minorEvenNegativePerturbationTaylor00
    minorEvenNegativePerturbationTaylor02
    minorEvenNegativePerturbationTaylor22
    evenNegativePerturbationTaylor00 evenNegativePerturbationTaylor02
    evenNegativePerturbationTaylor22
  nlinarith

private theorem minorNegativeTaylor02_eq_neg_positiveTaylor02 :
    evenNegativePerturbationTaylor02 =
      -evenPositivePerturbationTaylor02 := by
  rw [show evenNegativePerturbationTaylor02 = step01Midpoint02 by rfl,
    step01Midpoint_eq_kernel_sub_positiveMoment.2.1]
  unfold evenPositivePerturbationTaylor02
  ring

private def minorMinusModelDefect00 : ℝ :=
  yoshidaEndpointEvenLowGram00 + minorEvenNegativePerturbationTaylor00 -
    factorTwoIntrinsicSixUnbalancedMinorMinusLower00

private def minorMinusModelDefect02 : ℝ :=
  yoshidaEndpointEvenLowGram02 + minorEvenNegativePerturbationTaylor02 -
    factorTwoIntrinsicSixUnbalancedMinorMinusLower02

private def minorMinusModelDefect22 : ℝ :=
  yoshidaEndpointEvenLowGram22 + minorEvenNegativePerturbationTaylor22 -
    factorTwoIntrinsicSixUnbalancedMinorMinusLower22

private theorem minorMinusModelDefect_bounds :
    (108 / 1000000 : ℝ) < minorMinusModelDefect00 ∧
      |minorMinusModelDefect02| < (51 / 1000000 : ℝ) ∧
      (59 / 1000000 : ℝ) < minorMinusModelDefect22 := by
  have hc00 := intrinsicEven_cleanGram00_gt
  rcases intrinsicEven_cleanGram02_bounds with ⟨hc02L, hc02U⟩
  have hc22 := intrinsicEven_cleanGram22_gt
  have hm00 := step01Midpoint00_gt
  have hm22 := step01Midpoint22_gt
  have hn00 : (227278 / 1000000 : ℝ) - 3 / 4000 <
      evenNegativePerturbationTaylor00 := by
    unfold step01Midpoint00 at hm00
    nlinarith
  have hn22 : (188489 / 1000000 : ℝ) - 3 / 20000 <
      evenNegativePerturbationTaylor22 := by
    unfold step01Midpoint22 at hm22
    nlinarith
  have ht02L := evenPositivePerturbationTaylor_ultra_bounds.2.1
  have ht02U := evenPositivePerturbationTaylor_ultra_bounds.2.2.1
  unfold minorMinusModelDefect00 minorMinusModelDefect02
    minorMinusModelDefect22 minorEvenNegativePerturbationTaylor00
    minorEvenNegativePerturbationTaylor02
    minorEvenNegativePerturbationTaylor22
    factorTwoIntrinsicSixUnbalancedMinorMinusLower00
    factorTwoIntrinsicSixUnbalancedMinorMinusLower02
    factorTwoIntrinsicSixUnbalancedMinorMinusLower22 at ⊢
  rw [minorNegativeTaylor02_eq_neg_positiveTaylor02]
  constructor
  · nlinarith
  constructor
  · rw [abs_lt]
    constructor <;> nlinarith
  · nlinarith

private theorem minorMinusModelDefect_det_pos :
    0 < minorMinusModelDefect00 * minorMinusModelDefect22 -
      minorMinusModelDefect02 ^ 2 := by
  rcases minorMinusModelDefect_bounds with ⟨h00, h02, h22⟩
  have h00pos : 0 < minorMinusModelDefect00 :=
    (by norm_num : (0 : ℝ) < 108 / 1000000).trans h00
  have hprod :
      (108 / 1000000 : ℝ) * (59 / 1000000) <
        minorMinusModelDefect00 * minorMinusModelDefect22 :=
    mul_lt_mul h00 h22.le (by norm_num) h00pos.le
  have h02' := abs_lt.mp h02
  have hsq : minorMinusModelDefect02 ^ 2 <
      (51 / 1000000 : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h02'.2)
      (by linarith : 0 < minorMinusModelDefect02 + 51 / 1000000)]
  have hrat :
      (51 / 1000000 : ℝ) ^ 2 <
        (108 / 1000000) * (59 / 1000000) := by
    norm_num
  nlinarith

private theorem minorMinusModelDefect_quadratic_nonneg (c d : ℝ) :
    0 ≤ minorMinusModelDefect00 * c ^ 2 +
      2 * minorMinusModelDefect02 * c * d +
      minorMinusModelDefect22 * d ^ 2 := by
  by_cases hne : c ≠ 0 ∨ d ≠ 0
  · exact (real_twoByTwo_quadratic_pos _ _ _ c d
      ((by norm_num : (0 : ℝ) < 108 / 1000000).trans
        minorMinusModelDefect_bounds.1)
      minorMinusModelDefect_det_pos hne).le
  · push_neg at hne
    rcases hne with ⟨rfl, rfl⟩
    norm_num

private theorem minorMinusCombinedModel_quadratic_le_exact (c d : ℝ) :
    (yoshidaEndpointEvenLowGram00 +
          minorEvenNegativePerturbationTaylor00) * c ^ 2 +
        2 * (yoshidaEndpointEvenLowGram02 +
          minorEvenNegativePerturbationTaylor02) * c * d +
        (yoshidaEndpointEvenLowGram22 +
          minorEvenNegativePerturbationTaylor22) * d ^ 2 ≤
      factorTwoStructuralPhaseLow00 (-1) * c ^ 2 +
        2 * factorTwoStructuralPhaseLow02 (-1) * c * d +
        factorTwoStructuralPhaseLow22 (-1) * d ^ 2 := by
  have hpert := minorEvenNegativePerturbationTaylor_quadratic_le c d
  have hclean :
      yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) =
        yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * d +
          yoshidaEndpointEvenLowGram22 * d ^ 2 := by
    simpa only [factorTwoEvenStructuralLowProfile] using
      yoshidaEndpointEvenLowGram_quadratic_eq_clean c d
  rw [factorTwoStructuralPhaseLow_endpoint_quadratic, hclean]
  nlinarith

theorem factorTwoIntrinsicSixUnbalancedMinorMinusLowRemainder_nonneg
    (c d : ℝ) :
    0 ≤
      (factorTwoStructuralPhaseLow00 (-1) -
          factorTwoIntrinsicSixUnbalancedMinorMinusLower00) * c ^ 2 +
        2 * (factorTwoStructuralPhaseLow02 (-1) -
          factorTwoIntrinsicSixUnbalancedMinorMinusLower02) * c * d +
        (factorTwoStructuralPhaseLow22 (-1) -
          factorTwoIntrinsicSixUnbalancedMinorMinusLower22) * d ^ 2 := by
  have hdef := minorMinusModelDefect_quadratic_nonneg c d
  have hmodel := minorMinusCombinedModel_quadratic_le_exact c d
  unfold minorMinusModelDefect00 minorMinusModelDefect02
    minorMinusModelDefect22 at hdef
  nlinarith

/-- The rational low-even Gram keeps the genuine `P₄` column. -/
def factorTwoIntrinsicSixUnbalancedMinorMinusEvenLowerQuadratic
    (c0 c2 c4 : ℝ) : ℝ :=
  symmetricQuadratic
    factorTwoIntrinsicSixUnbalancedMinorMinusLower00
    factorTwoIntrinsicSixUnbalancedMinorMinusLower02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedMinorMinusLower22
    factorTwoIntrinsicSixUnbalancedEMinus24
    minusP4Lower c0 c2 c4

theorem factorTwoIntrinsicSixUnbalancedMinorMinusEvenLower_le_exact
    (c0 c2 c4 : ℝ) :
    factorTwoIntrinsicSixUnbalancedMinorMinusEvenLowerQuadratic c0 c2 c4 ≤
      symmetricQuadratic
        factorTwoIntrinsicSixUnbalancedEMinus00
        factorTwoIntrinsicSixUnbalancedEMinus02
        factorTwoIntrinsicSixUnbalancedEMinus04
        factorTwoIntrinsicSixUnbalancedEMinus22
        factorTwoIntrinsicSixUnbalancedEMinus24
        factorTwoIntrinsicSixUnbalancedEMinus44 c0 c2 c4 := by
  have hlow :=
    factorTwoIntrinsicSixUnbalancedMinorMinusLowRemainder_nonneg c0 c2
  have hp4 : minusP4Lower <
      factorTwoIntrinsicSixUnbalancedEMinus44 := by
    simpa only [factorTwoIntrinsicSixUnbalancedEMinus44,
      factorTwoIntrinsicSixP4Diagonal,
      factorTwoEndpointPhaseDiagonal,
      factorTwoIntrinsicP4PhaseDiagonal] using minusP4Lower_lt_exact
  have htail : 0 ≤
      (factorTwoIntrinsicSixUnbalancedEMinus44 - minusP4Lower) * c4 ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hp4.le) (sq_nonneg c4)
  unfold factorTwoIntrinsicSixUnbalancedMinorMinusEvenLowerQuadratic
    symmetricQuadratic factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus22
  nlinarith

/-- Five-dimensional lower form in aligned even coordinates and the odd
basis `(P₁, P₃-P₁)`. -/
def factorTwoIntrinsicSixUnbalancedMinorMinusLowerFiveQuadratic
    (s d p u v : ℝ) : ℝ :=
  factorTwoIntrinsicSixUnbalancedMinorMinusEvenLowerQuadratic
      (s + d) (s - d) p +
    2 * (factorTwoIntrinsicSixUnbalancedKMinusOneSum * s +
      factorTwoIntrinsicSixUnbalancedKMinusOneDifference * d +
      factorTwoIntrinsicSixUnbalancedKMinus41 * p) * u +
    2 * (factorTwoIntrinsicSixUnbalancedKMinusShearSum * s +
      factorTwoIntrinsicSixUnbalancedKMinusShearDifference * d +
      factorTwoIntrinsicSixUnbalancedKMinusShearTail * p) * v +
    intrinsicStaticMinusOddLower (u - v) v

/-- The genuine five-dimensional endpoint form in the original Legendre
coordinates. -/
def factorTwoIntrinsicSixUnbalancedMinorMinusExactFiveQuadratic
    (c0 c2 c4 c1 c3 : ℝ) : ℝ :=
  symmetricQuadratic
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus04
      factorTwoIntrinsicSixUnbalancedEMinus22
      factorTwoIntrinsicSixUnbalancedEMinus24
      factorTwoIntrinsicSixUnbalancedEMinus44 c0 c2 c4 +
    2 * (c0 * factorTwoIntrinsicSixUnbalancedKMinus01 +
      c2 * factorTwoIntrinsicSixUnbalancedKMinus21 +
      c4 * factorTwoIntrinsicSixUnbalancedKMinus41) * c1 +
    2 * (c0 * factorTwoIntrinsicSixUnbalancedKMinus03 +
      c2 * factorTwoIntrinsicSixUnbalancedKMinus23 +
      c4 * factorTwoIntrinsicSixUnbalancedKMinus43) * c3 +
    factorTwoIntrinsicSixUnbalancedOPlus11 * c1 ^ 2 +
    2 * factorTwoIntrinsicSixUnbalancedOPlus13 * c1 * c3 +
    factorTwoIntrinsicSixUnbalancedOPlus33 * c3 ^ 2

theorem factorTwoIntrinsicSixUnbalancedMinorMinusLowerFive_le_exact
    (s d p u v : ℝ) :
    factorTwoIntrinsicSixUnbalancedMinorMinusLowerFiveQuadratic s d p u v ≤
      factorTwoIntrinsicSixUnbalancedMinorMinusExactFiveQuadratic
        (s + d) (s - d) p (u - v) v := by
  have hEven :=
    factorTwoIntrinsicSixUnbalancedMinorMinusEvenLower_le_exact
      (s + d) (s - d) p
  have hOdd := intrinsicStaticMinusOddLower_le (u - v) v
  have hOdd' :
      intrinsicStaticMinusOddLower (u - v) v ≤
        factorTwoIntrinsicSixUnbalancedOPlus11 * (u - v) ^ 2 +
          2 * factorTwoIntrinsicSixUnbalancedOPlus13 * (u - v) * v +
          factorTwoIntrinsicSixUnbalancedOPlus33 * v ^ 2 := by
    simpa only [factorTwoIntrinsicStaticOddQuadratic,
      factorTwoIntrinsicOddPhaseQuadratic,
      factorTwoIntrinsicSixUnbalancedOPlus11,
      factorTwoIntrinsicSixUnbalancedOPlus13,
      factorTwoIntrinsicSixUnbalancedOPlus33, neg_neg, one_mul] using hOdd
  unfold factorTwoIntrinsicSixUnbalancedMinorMinusLowerFiveQuadratic
    factorTwoIntrinsicSixUnbalancedMinorMinusExactFiveQuadratic
    factorTwoIntrinsicSixUnbalancedKMinusOneSum
    factorTwoIntrinsicSixUnbalancedKMinusOneDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearSum
    factorTwoIntrinsicSixUnbalancedKMinusShearDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearTail
  nlinarith

/-! ## Rational congruence certificate -/

private def minusMinorFiveBilinear
    (s d p u v r e q w z : ℝ) : ℝ :=
  (factorTwoIntrinsicSixUnbalancedMinorMinusLower00 +
      2 * factorTwoIntrinsicSixUnbalancedMinorMinusLower02 +
      factorTwoIntrinsicSixUnbalancedMinorMinusLower22) * s * r +
    (factorTwoIntrinsicSixUnbalancedMinorMinusLower00 -
      factorTwoIntrinsicSixUnbalancedMinorMinusLower22) * (s * e + d * r) +
    (factorTwoIntrinsicSixUnbalancedMinorMinusLower00 -
      2 * factorTwoIntrinsicSixUnbalancedMinorMinusLower02 +
      factorTwoIntrinsicSixUnbalancedMinorMinusLower22) * d * e +
    factorTwoIntrinsicSixUnbalancedEMinusP4Sum * (s * q + p * r) -
    factorTwoIntrinsicSixUnbalancedEMinusP4Difference * (d * q + p * e) +
    minusP4Lower * p * q +
    factorTwoIntrinsicSixUnbalancedKMinusOneSum * (s * w + u * r) +
    factorTwoIntrinsicSixUnbalancedKMinusOneDifference * (d * w + u * e) +
    factorTwoIntrinsicSixUnbalancedKMinus41 * (p * w + u * q) +
    factorTwoIntrinsicSixUnbalancedKMinusShearSum * (s * z + v * r) +
    factorTwoIntrinsicSixUnbalancedKMinusShearDifference * (d * z + v * e) +
    factorTwoIntrinsicSixUnbalancedKMinusShearTail * (p * z + v * q) +
    intrinsicStaticMinusOddLower11 * u * w +
    (intrinsicStaticMinusOddLower13 - intrinsicStaticMinusOddLower11) *
      (u * z + v * w) +
    (intrinsicStaticMinusOddLower11 -
      2 * intrinsicStaticMinusOddLower13 +
      intrinsicStaticMinusOddLower33) * v * z

private def minusMinorFiveQuadratic
    (a00 a01 a02 a03 a04 a11 a12 a13 a14 a22 a23 a24 a33 a34 a44
      x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  a00 * x0 ^ 2 + 2 * a01 * x0 * x1 + 2 * a02 * x0 * x2 +
    2 * a03 * x0 * x3 + 2 * a04 * x0 * x4 + a11 * x1 ^ 2 +
    2 * a12 * x1 * x2 + 2 * a13 * x1 * x3 + 2 * a14 * x1 * x4 +
    a22 * x2 ^ 2 + 2 * a23 * x2 * x3 + 2 * a24 * x2 * x4 +
    a33 * x3 ^ 2 + 2 * a34 * x3 * x4 + a44 * x4 ^ 2

private theorem factorTwoIntrinsicSixUnbalancedMinorMinusLowerFive_eq_bilinear
    (s d p u v : ℝ) :
    factorTwoIntrinsicSixUnbalancedMinorMinusLowerFiveQuadratic s d p u v =
      minusMinorFiveBilinear s d p u v s d p u v := by
  unfold factorTwoIntrinsicSixUnbalancedMinorMinusLowerFiveQuadratic
    factorTwoIntrinsicSixUnbalancedMinorMinusEvenLowerQuadratic
    minusMinorFiveBilinear symmetricQuadratic
    factorTwoIntrinsicSixUnbalancedEMinusP4Sum
    factorTwoIntrinsicSixUnbalancedEMinusP4Difference
    factorTwoIntrinsicSixUnbalancedKMinusOneSum
    factorTwoIntrinsicSixUnbalancedKMinusOneDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearSum
    factorTwoIntrinsicSixUnbalancedKMinusShearDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearTail
    intrinsicStaticMinusOddLower
  ring

private def minorMinusT00 : ℝ :=
  minusMinorFiveBilinear 1 0 0 0 0 1 0 0 0 0

private def minorMinusT01 : ℝ :=
  minusMinorFiveBilinear 1 0 0 0 0 (-2 / 15) 0 1 0 0

private def minorMinusT02 : ℝ :=
  minusMinorFiveBilinear 1 0 0 0 0 (-1 / 6) 0 (-4 / 35) 1 0

private def minorMinusT03 : ℝ :=
  minusMinorFiveBilinear 1 0 0 0 0 (-1 / 20) 1 (9 / 50) (-1 / 14) 0

private def minorMinusT04 : ℝ :=
  minusMinorFiveBilinear 1 0 0 0 0 (4 / 25) (-11 / 4) (-3 / 8)
    (7 / 80) 1

private def minorMinusT11 : ℝ :=
  minusMinorFiveBilinear (-2 / 15) 0 1 0 0 (-2 / 15) 0 1 0 0

private def minorMinusT12 : ℝ :=
  minusMinorFiveBilinear (-2 / 15) 0 1 0 0
    (-1 / 6) 0 (-4 / 35) 1 0

private def minorMinusT13 : ℝ :=
  minusMinorFiveBilinear (-2 / 15) 0 1 0 0
    (-1 / 20) 1 (9 / 50) (-1 / 14) 0

private def minorMinusT14 : ℝ :=
  minusMinorFiveBilinear (-2 / 15) 0 1 0 0
    (4 / 25) (-11 / 4) (-3 / 8) (7 / 80) 1

private def minorMinusT22 : ℝ :=
  minusMinorFiveBilinear (-1 / 6) 0 (-4 / 35) 1 0
    (-1 / 6) 0 (-4 / 35) 1 0

private def minorMinusT23 : ℝ :=
  minusMinorFiveBilinear (-1 / 6) 0 (-4 / 35) 1 0
    (-1 / 20) 1 (9 / 50) (-1 / 14) 0

private def minorMinusT24 : ℝ :=
  minusMinorFiveBilinear (-1 / 6) 0 (-4 / 35) 1 0
    (4 / 25) (-11 / 4) (-3 / 8) (7 / 80) 1

private def minorMinusT33 : ℝ :=
  minusMinorFiveBilinear (-1 / 20) 1 (9 / 50) (-1 / 14) 0
    (-1 / 20) 1 (9 / 50) (-1 / 14) 0

private def minorMinusT34 : ℝ :=
  minusMinorFiveBilinear (-1 / 20) 1 (9 / 50) (-1 / 14) 0
    (4 / 25) (-11 / 4) (-3 / 8) (7 / 80) 1

private def minorMinusT44 : ℝ :=
  minusMinorFiveBilinear (4 / 25) (-11 / 4) (-3 / 8) (7 / 80) 1
    (4 / 25) (-11 / 4) (-3 / 8) (7 / 80) 1

set_option maxHeartbeats 800000 in
private theorem minorMinusLowerFive_congruence
    (x0 x1 x2 x3 x4 : ℝ) :
    factorTwoIntrinsicSixUnbalancedMinorMinusLowerFiveQuadratic
        (x0 - (2 / 15 : ℝ) * x1 - (1 / 6 : ℝ) * x2 -
          (1 / 20 : ℝ) * x3 + (4 / 25 : ℝ) * x4)
        (x3 - (11 / 4 : ℝ) * x4)
        (x1 - (4 / 35 : ℝ) * x2 + (9 / 50 : ℝ) * x3 -
          (3 / 8 : ℝ) * x4)
        (x2 - (1 / 14 : ℝ) * x3 + (7 / 80 : ℝ) * x4) x4 =
      minusMinorFiveQuadratic
        minorMinusT00 minorMinusT01 minorMinusT02 minorMinusT03 minorMinusT04
        minorMinusT11 minorMinusT12 minorMinusT13 minorMinusT14
        minorMinusT22 minorMinusT23 minorMinusT24 minorMinusT33 minorMinusT34
        minorMinusT44 x0 x1 x2 x3 x4 := by
  rw [factorTwoIntrinsicSixUnbalancedMinorMinusLowerFive_eq_bilinear]
  unfold minusMinorFiveQuadratic minorMinusT00 minorMinusT01 minorMinusT02
    minorMinusT03 minorMinusT04 minorMinusT11 minorMinusT12 minorMinusT13
    minorMinusT14 minorMinusT22 minorMinusT23 minorMinusT24 minorMinusT33
    minorMinusT34 minorMinusT44 minusMinorFiveBilinear
  ring

private theorem minorMinusTransformed_bounds :
    (2 : ℝ) < minorMinusT00 ∧
      (451 / 1000 : ℝ) < minorMinusT11 ∧
      (23 / 200 : ℝ) < minorMinusT22 ∧
      (21 / 10000 : ℝ) < minorMinusT33 ∧
      (1 / 1000 : ℝ) < minorMinusT44 ∧
      |minorMinusT01| < (1 / 2000 : ℝ) ∧
      |minorMinusT02| < (17 / 10000 : ℝ) ∧
      |minorMinusT03| < (39 / 5000 : ℝ) ∧
      |minorMinusT04| < (9 / 5000 : ℝ) ∧
      |minorMinusT12| < (17 / 20000 : ℝ) ∧
      |minorMinusT13| < (11 / 10000 : ℝ) ∧
      |minorMinusT14| < (1 / 500 : ℝ) ∧
      |minorMinusT23| < (1 / 5000 : ℝ) ∧
      |minorMinusT24| < (1 / 2000 : ℝ) ∧
      |minorMinusT34| < (3 / 8000 : ℝ) := by
  have hP4 := factorTwoIntrinsicP4MinusCross_refined_bounds
  change
    (2927 / 10000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedEMinusP4Sum ∧
      factorTwoIntrinsicSixUnbalancedEMinusP4Sum < 2931 / 10000 ∧
      (662 / 10000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedEMinusP4Difference ∧
      factorTwoIntrinsicSixUnbalancedEMinusP4Difference < 666 / 10000
    at hP4
  rcases hP4 with ⟨hP4sL, hP4sU, hP4dL, hP4dU⟩
  have hOne := factorTwoIntrinsicSixUnbalancedKMinus_firstColumn_bounds
  change
    (20077 / 50000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedKMinusOneSum ∧
      factorTwoIntrinsicSixUnbalancedKMinusOneSum < 80313 / 200000 ∧
      (2747 / 200000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedKMinusOneDifference ∧
      factorTwoIntrinsicSixUnbalancedKMinusOneDifference < 43 / 3125 ∧
      (1043 / 10000 : ℝ) < factorTwoIntrinsicSixUnbalancedKMinus41 ∧
      factorTwoIntrinsicSixUnbalancedKMinus41 < 529 / 5000
    at hOne
  have hShear := factorTwoIntrinsicSixUnbalancedKMinusShearLow_bounds
  have hTail := factorTwoIntrinsicSixUnbalancedKMinusShearTail_bounds
  rcases hOne with ⟨hOneSumL, hOneSumU, hOneDiffL, hOneDiffU,
    hOneTailL, hOneTailU⟩
  rcases hShear with ⟨hShearSumL, hShearSumU,
    hShearDiffL, hShearDiffU⟩
  rcases hTail with ⟨hShearTailL, hShearTailU⟩
  simp only [minorMinusT00, minorMinusT01, minorMinusT02, minorMinusT03,
    minorMinusT04, minorMinusT11, minorMinusT12, minorMinusT13,
    minorMinusT14, minorMinusT22, minorMinusT23, minorMinusT24,
    minorMinusT33, minorMinusT34, minorMinusT44, minusMinorFiveBilinear]
  norm_num [factorTwoIntrinsicSixUnbalancedMinorMinusLower00,
    factorTwoIntrinsicSixUnbalancedMinorMinusLower02,
    factorTwoIntrinsicSixUnbalancedMinorMinusLower22, minusP4Lower,
    intrinsicStaticMinusOddLower11, intrinsicStaticMinusOddLower13,
    intrinsicStaticMinusOddLower33] at ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  · rw [abs_lt]
    constructor <;> linarith

private theorem two_mul_mul_ge_neg_sum_sq_of_abs_lt
    {a b x y : ℝ} (h : |a| < b) :
    -b * (x ^ 2 + y ^ 2) ≤ 2 * a * x * y := by
  have hb : 0 < b := (abs_nonneg a).trans_lt h
  rcases abs_lt.mp h with ⟨haL, haU⟩
  by_cases hxy : 0 ≤ x * y
  · have hmul := mul_le_mul_of_nonneg_right haL.le hxy
    nlinarith [sq_nonneg (x - y)]
  · have hxy' : x * y ≤ 0 := le_of_not_ge hxy
    have hmul := mul_le_mul_of_nonpos_right haU.le hxy'
    nlinarith [sq_nonneg (x + y)]

set_option maxHeartbeats 800000 in
private theorem minorMinusTransformedScaled_reserve_le
    (y0 y1 y2 y3 y4 : ℝ) :
    (8653 / 40000000 : ℝ) * y0 ^ 2 +
        (24687 / 200000000 : ℝ) * y1 ^ 2 +
        (6447 / 200000000 : ℝ) * y2 ^ 2 +
        (6459 / 8000000 : ℝ) * y3 ^ 2 +
        (517 / 800000 : ℝ) * y4 ^ 2 ≤
      minusMinorFiveQuadratic
      minorMinusT00 minorMinusT01 minorMinusT02 minorMinusT03 minorMinusT04
      minorMinusT11 minorMinusT12 minorMinusT13 minorMinusT14
      minorMinusT22 minorMinusT23 minorMinusT24 minorMinusT33 minorMinusT34
      minorMinusT44
      ((1 / 80 : ℝ) * y0) ((1 / 50 : ℝ) * y1)
      ((1 / 50 : ℝ) * y2) ((3 / 4 : ℝ) * y3) y4 := by
  rcases minorMinusTransformed_bounds with
    ⟨h00, h11, h22, h33, h44, h01, h02, h03, h04,
      h12, h13, h14, h23, h24, h34⟩
  have hd0 :
      (2 : ℝ) * ((1 / 80) * y0) ^ 2 ≤
        minorMinusT00 * ((1 / 80) * y0) ^ 2 := by
    exact mul_le_mul_of_nonneg_right h00.le (sq_nonneg _)
  have hd1 :
      (451 / 1000 : ℝ) * ((1 / 50) * y1) ^ 2 ≤
        minorMinusT11 * ((1 / 50) * y1) ^ 2 := by
    exact mul_le_mul_of_nonneg_right h11.le (sq_nonneg _)
  have hd2 :
      (23 / 200 : ℝ) * ((1 / 50) * y2) ^ 2 ≤
        minorMinusT22 * ((1 / 50) * y2) ^ 2 := by
    exact mul_le_mul_of_nonneg_right h22.le (sq_nonneg _)
  have hd3 :
      (21 / 10000 : ℝ) * ((3 / 4) * y3) ^ 2 ≤
        minorMinusT33 * ((3 / 4) * y3) ^ 2 := by
    exact mul_le_mul_of_nonneg_right h33.le (sq_nonneg _)
  have hd4 : (1 / 1000 : ℝ) * y4 ^ 2 ≤ minorMinusT44 * y4 ^ 2 := by
    exact mul_le_mul_of_nonneg_right h44.le (sq_nonneg _)
  have hc01 := two_mul_mul_ge_neg_sum_sq_of_abs_lt h01
    (x := y0) (y := y1)
  have hc02 := two_mul_mul_ge_neg_sum_sq_of_abs_lt h02
    (x := y0) (y := y2)
  have hc03 := two_mul_mul_ge_neg_sum_sq_of_abs_lt h03
    (x := y0) (y := y3)
  have hc04 := two_mul_mul_ge_neg_sum_sq_of_abs_lt h04
    (x := y0) (y := y4)
  have hc12 := two_mul_mul_ge_neg_sum_sq_of_abs_lt h12
    (x := y1) (y := y2)
  have hc13 := two_mul_mul_ge_neg_sum_sq_of_abs_lt h13
    (x := y1) (y := y3)
  have hc14 := two_mul_mul_ge_neg_sum_sq_of_abs_lt h14
    (x := y1) (y := y4)
  have hc23 := two_mul_mul_ge_neg_sum_sq_of_abs_lt h23
    (x := y2) (y := y3)
  have hc24 := two_mul_mul_ge_neg_sum_sq_of_abs_lt h24
    (x := y2) (y := y4)
  have hc34 := two_mul_mul_ge_neg_sum_sq_of_abs_lt h34
    (x := y3) (y := y4)
  unfold minusMinorFiveQuadratic
  nlinarith only [hd0, hd1, hd2, hd3, hd4, hc01, hc02, hc03, hc04,
    hc12, hc13, hc14, hc23, hc24, hc34]

private theorem minorMinusTransformedScaled_pos
    (y0 y1 y2 y3 y4 : ℝ)
    (hne : y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0 ∨ y3 ≠ 0 ∨ y4 ≠ 0) :
    0 < minusMinorFiveQuadratic
      minorMinusT00 minorMinusT01 minorMinusT02 minorMinusT03 minorMinusT04
      minorMinusT11 minorMinusT12 minorMinusT13 minorMinusT14
      minorMinusT22 minorMinusT23 minorMinusT24 minorMinusT33 minorMinusT34
      minorMinusT44
      ((1 / 80 : ℝ) * y0) ((1 / 50 : ℝ) * y1)
      ((1 / 50 : ℝ) * y2) ((3 / 4 : ℝ) * y3) y4 := by
  have hbudget :
      0 < (8653 / 40000000 : ℝ) * y0 ^ 2 +
        (24687 / 200000000 : ℝ) * y1 ^ 2 +
        (6447 / 200000000 : ℝ) * y2 ^ 2 +
        (6459 / 8000000 : ℝ) * y3 ^ 2 +
        (517 / 800000 : ℝ) * y4 ^ 2 := by
    rcases hne with h0 | h1 | h2 | h3 | h4
    all_goals positivity
  exact hbudget.trans_le
    (minorMinusTransformedScaled_reserve_le y0 y1 y2 y3 y4)

/-- The diagonal reserve retained by the rational congruence for the
negative five-dimensional endpoint form. -/
theorem factorTwoIntrinsicSixUnbalancedMinorMinusLowerFive_transformed_reserve
    (x0 x1 x2 x3 x4 : ℝ) :
    (8653 / 6250 : ℝ) * x0 ^ 2 +
        (24687 / 80000 : ℝ) * x1 ^ 2 +
        (6447 / 80000 : ℝ) * x2 ^ 2 +
        (2153 / 1500000 : ℝ) * x3 ^ 2 +
        (517 / 800000 : ℝ) * x4 ^ 2 ≤
      factorTwoIntrinsicSixUnbalancedMinorMinusLowerFiveQuadratic
        (x0 - (2 / 15 : ℝ) * x1 - (1 / 6 : ℝ) * x2 -
          (1 / 20 : ℝ) * x3 + (4 / 25 : ℝ) * x4)
        (x3 - (11 / 4 : ℝ) * x4)
        (x1 - (4 / 35 : ℝ) * x2 + (9 / 50 : ℝ) * x3 -
          (3 / 8 : ℝ) * x4)
        (x2 - (1 / 14 : ℝ) * x3 + (7 / 80 : ℝ) * x4) x4 := by
  rw [minorMinusLowerFive_congruence]
  have h := minorMinusTransformedScaled_reserve_le
    (80 * x0) (50 * x1) (50 * x2) ((4 / 3 : ℝ) * x3) x4
  convert h using 1 <;> ring

private theorem minorMinusTransformed_pos
    (x0 x1 x2 x3 x4 : ℝ)
    (hne : x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0 ∨ x4 ≠ 0) :
    0 < minusMinorFiveQuadratic
      minorMinusT00 minorMinusT01 minorMinusT02 minorMinusT03 minorMinusT04
      minorMinusT11 minorMinusT12 minorMinusT13 minorMinusT14
      minorMinusT22 minorMinusT23 minorMinusT24 minorMinusT33 minorMinusT34
      minorMinusT44 x0 x1 x2 x3 x4 := by
  have hne' :
      (80 * x0 : ℝ) ≠ 0 ∨ (50 * x1 : ℝ) ≠ 0 ∨
        (50 * x2 : ℝ) ≠ 0 ∨ ((4 / 3 : ℝ) * x3) ≠ 0 ∨ x4 ≠ 0 := by
    rcases hne with h0 | h1 | h2 | h3 | h4
    · exact Or.inl (mul_ne_zero (by norm_num) h0)
    · exact Or.inr (Or.inl (mul_ne_zero (by norm_num) h1))
    · exact Or.inr (Or.inr (Or.inl (mul_ne_zero (by norm_num) h2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (mul_ne_zero (by norm_num) h3))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))
  have h := minorMinusTransformedScaled_pos
    (80 * x0) (50 * x1) (50 * x2) ((4 / 3 : ℝ) * x3) x4 hne'
  convert h using 1 ; ring_nf

theorem factorTwoIntrinsicSixUnbalancedMinorMinusLowerFive_pos
    (s d p u v : ℝ)
    (hne : s ≠ 0 ∨ d ≠ 0 ∨ p ≠ 0 ∨ u ≠ 0 ∨ v ≠ 0) :
    0 < factorTwoIntrinsicSixUnbalancedMinorMinusLowerFiveQuadratic
      s d p u v := by
  let x4 : ℝ := v
  let x3 : ℝ := d + (11 / 4 : ℝ) * x4
  let x2 : ℝ := u + (1 / 14 : ℝ) * x3 - (7 / 80 : ℝ) * x4
  let x1 : ℝ := p + (4 / 35 : ℝ) * x2 - (9 / 50 : ℝ) * x3 +
    (3 / 8 : ℝ) * x4
  let x0 : ℝ := s + (2 / 15 : ℝ) * x1 + (1 / 6 : ℝ) * x2 +
    (1 / 20 : ℝ) * x3 - (4 / 25 : ℝ) * x4
  have hneX : x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0 ∨ x4 ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    rcases hzero with ⟨hx0, hx1, hx2, hx3, hx4⟩
    have hv : v = 0 := by simpa only [x4] using hx4
    have hd : d = 0 := by
      dsimp only [x3, x4] at hx3
      nlinarith
    have hu : u = 0 := by
      dsimp only [x2] at hx2
      nlinarith
    have hp : p = 0 := by
      dsimp only [x1] at hx1
      nlinarith
    have hs : s = 0 := by
      dsimp only [x0] at hx0
      nlinarith
    rcases hne with hs' | hd' | hp' | hu' | hv'
    · exact hs' hs
    · exact hd' hd
    · exact hp' hp
    · exact hu' hu
    · exact hv' hv
  have htrans := minorMinusTransformed_pos x0 x1 x2 x3 x4 hneX
  have hcong := minorMinusLowerFive_congruence x0 x1 x2 x3 x4
  have hsMap :
      x0 - (2 / 15 : ℝ) * x1 - (1 / 6 : ℝ) * x2 -
          (1 / 20 : ℝ) * x3 + (4 / 25 : ℝ) * x4 = s := by
    dsimp only [x0]
    ring
  have hdMap : x3 - (11 / 4 : ℝ) * x4 = d := by
    dsimp only [x3]
    ring
  have hpMap :
      x1 - (4 / 35 : ℝ) * x2 + (9 / 50 : ℝ) * x3 -
          (3 / 8 : ℝ) * x4 = p := by
    dsimp only [x1]
    ring
  have huMap :
      x2 - (1 / 14 : ℝ) * x3 + (7 / 80 : ℝ) * x4 = u := by
    dsimp only [x2]
    ring
  rw [hsMap, hdMap, hpMap, huMap] at hcong
  dsimp only [x4] at hcong
  rw [hcong]
  exact htrans

theorem factorTwoIntrinsicSixUnbalancedMinorMinusExactFive_pos
    (c0 c2 c4 c1 c3 : ℝ)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨ c1 ≠ 0 ∨ c3 ≠ 0) :
    0 < factorTwoIntrinsicSixUnbalancedMinorMinusExactFiveQuadratic
      c0 c2 c4 c1 c3 := by
  let s : ℝ := (c0 + c2) / 2
  let d : ℝ := (c0 - c2) / 2
  let u : ℝ := c1 + c3
  have hneAligned : s ≠ 0 ∨ d ≠ 0 ∨ c4 ≠ 0 ∨ u ≠ 0 ∨ c3 ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    rcases hzero with ⟨hs, hd, hp, hu, hv⟩
    have hc0 : c0 = 0 := by
      dsimp only [s, d] at hs hd
      nlinarith
    have hc2 : c2 = 0 := by
      dsimp only [s, d] at hs hd
      nlinarith
    have hc1 : c1 = 0 := by
      dsimp only [u] at hu
      nlinarith
    rcases hne with h0 | h2 | h4 | h1 | h3
    · exact h0 hc0
    · exact h2 hc2
    · exact h4 hp
    · exact h1 hc1
    · exact h3 hv
  have hlow := factorTwoIntrinsicSixUnbalancedMinorMinusLowerFive_pos
    s d c4 u c3 hneAligned
  have hle := factorTwoIntrinsicSixUnbalancedMinorMinusLowerFive_le_exact
    s d c4 u c3
  have hsMap : s + d = c0 := by
    dsimp only [s, d]
    ring
  have hdMap : s - d = c2 := by
    dsimp only [s, d]
    ring
  have huMap : u - c3 = c1 := by
    dsimp only [u]
    ring
  rw [hsMap, hdMap, huMap] at hle
  exact hlow.trans_le hle

private def minorThreeBilinear
    (e00 e02 e04 e22 e24 e44 x0 x2 x4 y0 y2 y4 : ℝ) : ℝ :=
  x0 * (e00 * y0 + e02 * y2 + e04 * y4) +
    x2 * (e02 * y0 + e22 * y2 + e24 * y4) +
    x4 * (e04 * y0 + e24 * y2 + e44 * y4)

private theorem symmetricQuadratic_eq_minorThreeBilinear_self
    (e00 e02 e04 e22 e24 e44 x0 x2 x4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44 x0 x2 x4 =
      minorThreeBilinear e00 e02 e04 e22 e24 e44
        x0 x2 x4 x0 x2 x4 := by
  unfold symmetricQuadratic minorThreeBilinear
  ring_nf

private theorem minorThreeBilinear_adjugateVector
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 x0 x2 x4 : ℝ) :
    minorThreeBilinear e00 e02 e04 e22 e24 e44 x0 x2 x4
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2) =
      symmetricDeterminant e00 e02 e04 e22 e24 e44 *
        (x0 * ell0 + x2 * ell2 + x4 * ell4) := by
  simp only [adjugateVector]
  unfold minorThreeBilinear symmetricDeterminant
  ring_nf

private theorem symmetricQuadratic_adjugateVector_factored
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2) =
      symmetricDeterminant e00 e02 e04 e22 e24 e44 *
        adjugateQuadratic e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 := by
  rw [symmetricQuadratic_eq_minorThreeBilinear_self]
  rw [minorThreeBilinear_adjugateVector]
  simp only [adjugateVector]
  unfold adjugateQuadratic
  ring_nf

private theorem symmetricQuadratic_neg_adjugateVector_factored
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44
        (-adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0)
        (-adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1)
        (-adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2) =
      symmetricDeterminant e00 e02 e04 e22 e24 e44 *
        adjugateQuadratic e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 := by
  rw [show symmetricQuadratic e00 e02 e04 e22 e24 e44
        (-adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0)
        (-adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1)
        (-adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2) =
      symmetricQuadratic e00 e02 e04 e22 e24 e44
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2) by
      unfold symmetricQuadratic
      ring]
  exact symmetricQuadratic_adjugateVector_factored
    e00 e02 e04 e22 e24 e44 ell0 ell2 ell4

private theorem neg_adjugateVector_dot_eq_neg_pair
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 x0 x2 x4 : ℝ) :
    (-adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0) * x0 +
        (-adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1) * x2 +
        (-adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2) * x4 =
      -unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
        x0 x2 x4 ell0 ell2 ell4 := by
  simp only [adjugateVector]
  unfold unbalancedThreeAdjugatePair
  ring_nf

private theorem unbalancedThreeAdjugatePair_first_shear
    (e00 e02 e04 e22 e24 e44 x0 x2 x4 y0 y2 y4 a b : ℝ) :
    unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
        x0 x2 x4
        (-b * x0 + a * y0) (-b * x2 + a * y2) (-b * x4 + a * y4) =
      -b * unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
          x0 x2 x4 x0 x2 x4 +
        a * unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
          x0 x2 x4 y0 y2 y4 := by
  unfold unbalancedThreeAdjugatePair
  ring_nf

private theorem unbalancedThreeAdjugatePair_second_shear
    (e00 e02 e04 e22 e24 e44 x0 x2 x4 y0 y2 y4 a b : ℝ) :
    unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
        y0 y2 y4
        (-b * x0 + a * y0) (-b * x2 + a * y2) (-b * x4 + a * y4) =
      -b * unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
          x0 x2 x4 y0 y2 y4 +
        a * unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
          y0 y2 y4 y0 y2 y4 := by
  unfold unbalancedThreeAdjugatePair
  ring_nf

private theorem adjugateQuadratic_shear
    (e00 e02 e04 e22 e24 e44 x0 x2 x4 y0 y2 y4 a b : ℝ) :
    adjugateQuadratic e00 e02 e04 e22 e24 e44
        (-b * x0 + a * y0) (-b * x2 + a * y2) (-b * x4 + a * y4) =
      b ^ 2 * unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
          x0 x2 x4 x0 x2 x4 -
        2 * a * b * unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
          x0 x2 x4 y0 y2 y4 +
        a ^ 2 * unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
          y0 y2 y4 y0 y2 y4 := by
  unfold adjugateQuadratic unbalancedThreeAdjugatePair
  ring_nf

private theorem fiveQuadratic_two_odd_adjugate_identity
    (e00 e02 e04 e22 e24 e44
      k01 k21 k41 k03 k23 k43 o11 o13 o33 : ℝ) :
    let detE := symmetricDeterminant e00 e02 e04 e22 e24 e44
    let a := detE * o11 -
      unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
        k01 k21 k41 k01 k21 k41
    let b := detE * o13 -
      unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
        k01 k21 k41 k03 k23 k43
    let c := detE * o33 -
      unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
        k03 k23 k43 k03 k23 k43
    let ell0 := -b * k01 + a * k03
    let ell2 := -b * k21 + a * k23
    let ell4 := -b * k41 + a * k43
    let v0 := adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0
    let v2 := adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1
    let v4 := adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2
    symmetricQuadratic e00 e02 e04 e22 e24 e44 (-v0) (-v2) (-v4) +
        2 * ((-v0) * k01 + (-v2) * k21 + (-v4) * k41) *
          (detE * (-b)) +
        2 * ((-v0) * k03 + (-v2) * k23 + (-v4) * k43) *
          (detE * a) +
        o11 * (detE * (-b)) ^ 2 +
        2 * o13 * (detE * (-b)) * (detE * a) +
        o33 * (detE * a) ^ 2 =
      detE * a * (a * c - b ^ 2) := by
  dsimp only
  rw [symmetricQuadratic_neg_adjugateVector_factored]
  rw [neg_adjugateVector_dot_eq_neg_pair,
    neg_adjugateVector_dot_eq_neg_pair,
    adjugateQuadratic_shear,
    unbalancedThreeAdjugatePair_first_shear,
    unbalancedThreeAdjugatePair_second_shear]
  ring

theorem factorTwoIntrinsicSixUnbalancedEMinusDet_eq_aligned :
    factorTwoIntrinsicSixUnbalancedEMinusDet =
      minusAlignedDeterminant
        factorTwoIntrinsicSixUnbalancedEMinusStrong
        factorTwoIntrinsicSixUnbalancedEMinusSkew
        factorTwoIntrinsicSixUnbalancedEMinusWeak
        factorTwoIntrinsicSixUnbalancedEMinusP4Sum
        factorTwoIntrinsicSixUnbalancedEMinusP4Difference
        factorTwoIntrinsicSixUnbalancedEMinus44 := by
  unfold factorTwoIntrinsicSixUnbalancedEMinusDet
    factorTwoIntrinsicSixUnbalancedEMinusStrong
    factorTwoIntrinsicSixUnbalancedEMinusSkew
    factorTwoIntrinsicSixUnbalancedEMinusWeak
    factorTwoIntrinsicSixUnbalancedEMinusP4Sum
    factorTwoIntrinsicSixUnbalancedEMinusP4Difference
    minusAlignedDeterminant symmetricDeterminant
  ring

theorem unbalancedThreeAdjugatePair_eq_minusAligned
    (u0 u2 u4 v0 v2 v4 : ℝ) :
    unbalancedThreeAdjugatePair
        factorTwoIntrinsicSixUnbalancedEMinus00
        factorTwoIntrinsicSixUnbalancedEMinus02
        factorTwoIntrinsicSixUnbalancedEMinus04
        factorTwoIntrinsicSixUnbalancedEMinus22
        factorTwoIntrinsicSixUnbalancedEMinus24
        factorTwoIntrinsicSixUnbalancedEMinus44
        u0 u2 u4 v0 v2 v4 =
      minusAlignedAdjugatePair
        factorTwoIntrinsicSixUnbalancedEMinusStrong
        factorTwoIntrinsicSixUnbalancedEMinusSkew
        factorTwoIntrinsicSixUnbalancedEMinusWeak
        factorTwoIntrinsicSixUnbalancedEMinusP4Sum
        factorTwoIntrinsicSixUnbalancedEMinusP4Difference
        factorTwoIntrinsicSixUnbalancedEMinus44
        (u0 + u2) (u0 - u2) u4 (v0 + v2) (v0 - v2) v4 := by
  unfold factorTwoIntrinsicSixUnbalancedEMinusStrong
    factorTwoIntrinsicSixUnbalancedEMinusSkew
    factorTwoIntrinsicSixUnbalancedEMinusWeak
    factorTwoIntrinsicSixUnbalancedEMinusP4Sum
    factorTwoIntrinsicSixUnbalancedEMinusP4Difference
    minusAlignedAdjugatePair unbalancedThreeAdjugatePair
  ring

/-- Exact aligned formula for the first sheared fraction-free pivot. -/
theorem factorTwoIntrinsicSixUnbalancedTMinusShearA_eq_aligned :
    factorTwoIntrinsicSixUnbalancedTMinusShearA =
      minusAlignedDeterminant
          factorTwoIntrinsicSixUnbalancedEMinusStrong
          factorTwoIntrinsicSixUnbalancedEMinusSkew
          factorTwoIntrinsicSixUnbalancedEMinusWeak
          factorTwoIntrinsicSixUnbalancedEMinusP4Sum
          factorTwoIntrinsicSixUnbalancedEMinusP4Difference
          factorTwoIntrinsicSixUnbalancedEMinus44 *
        factorTwoIntrinsicSixUnbalancedOPlus11 -
      minusAlignedAdjugatePair
          factorTwoIntrinsicSixUnbalancedEMinusStrong
          factorTwoIntrinsicSixUnbalancedEMinusSkew
          factorTwoIntrinsicSixUnbalancedEMinusWeak
          factorTwoIntrinsicSixUnbalancedEMinusP4Sum
          factorTwoIntrinsicSixUnbalancedEMinusP4Difference
          factorTwoIntrinsicSixUnbalancedEMinus44
          factorTwoIntrinsicSixUnbalancedKMinusOneSum
          factorTwoIntrinsicSixUnbalancedKMinusOneDifference
          factorTwoIntrinsicSixUnbalancedKMinus41
          factorTwoIntrinsicSixUnbalancedKMinusOneSum
          factorTwoIntrinsicSixUnbalancedKMinusOneDifference
          factorTwoIntrinsicSixUnbalancedKMinus41 := by
  change factorTwoIntrinsicSixUnbalancedEMinusDet *
      factorTwoIntrinsicSixUnbalancedOPlus11 -
        unbalancedThreeAdjugatePair
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44
          factorTwoIntrinsicSixUnbalancedKMinus01
          factorTwoIntrinsicSixUnbalancedKMinus21
          factorTwoIntrinsicSixUnbalancedKMinus41
          factorTwoIntrinsicSixUnbalancedKMinus01
          factorTwoIntrinsicSixUnbalancedKMinus21
          factorTwoIntrinsicSixUnbalancedKMinus41 = _
  rw [factorTwoIntrinsicSixUnbalancedEMinusDet_eq_aligned,
    unbalancedThreeAdjugatePair_eq_minusAligned]
  unfold factorTwoIntrinsicSixUnbalancedKMinusOneSum
    factorTwoIntrinsicSixUnbalancedKMinusOneDifference
  rfl

/-- Exact aligned polarization formula for `P₁` against `P₃ - P₁`. -/
theorem factorTwoIntrinsicSixUnbalancedTMinusShearP_eq_aligned :
    factorTwoIntrinsicSixUnbalancedTMinusShearP =
      minusAlignedDeterminant
          factorTwoIntrinsicSixUnbalancedEMinusStrong
          factorTwoIntrinsicSixUnbalancedEMinusSkew
          factorTwoIntrinsicSixUnbalancedEMinusWeak
          factorTwoIntrinsicSixUnbalancedEMinusP4Sum
          factorTwoIntrinsicSixUnbalancedEMinusP4Difference
          factorTwoIntrinsicSixUnbalancedEMinus44 *
        factorTwoIntrinsicSixUnbalancedOPlusShearCross -
      minusAlignedAdjugatePair
          factorTwoIntrinsicSixUnbalancedEMinusStrong
          factorTwoIntrinsicSixUnbalancedEMinusSkew
          factorTwoIntrinsicSixUnbalancedEMinusWeak
          factorTwoIntrinsicSixUnbalancedEMinusP4Sum
          factorTwoIntrinsicSixUnbalancedEMinusP4Difference
          factorTwoIntrinsicSixUnbalancedEMinus44
          factorTwoIntrinsicSixUnbalancedKMinusOneSum
          factorTwoIntrinsicSixUnbalancedKMinusOneDifference
          factorTwoIntrinsicSixUnbalancedKMinus41
          factorTwoIntrinsicSixUnbalancedKMinusShearSum
          factorTwoIntrinsicSixUnbalancedKMinusShearDifference
          factorTwoIntrinsicSixUnbalancedKMinusShearTail := by
  change
    (factorTwoIntrinsicSixUnbalancedEMinusDet *
        factorTwoIntrinsicSixUnbalancedOPlus13 -
      unbalancedThreeAdjugatePair
        factorTwoIntrinsicSixUnbalancedEMinus00
        factorTwoIntrinsicSixUnbalancedEMinus02
        factorTwoIntrinsicSixUnbalancedEMinus04
        factorTwoIntrinsicSixUnbalancedEMinus22
        factorTwoIntrinsicSixUnbalancedEMinus24
        factorTwoIntrinsicSixUnbalancedEMinus44
        factorTwoIntrinsicSixUnbalancedKMinus01
        factorTwoIntrinsicSixUnbalancedKMinus21
        factorTwoIntrinsicSixUnbalancedKMinus41
        factorTwoIntrinsicSixUnbalancedKMinus03
        factorTwoIntrinsicSixUnbalancedKMinus23
        factorTwoIntrinsicSixUnbalancedKMinus43) -
      (factorTwoIntrinsicSixUnbalancedEMinusDet *
          factorTwoIntrinsicSixUnbalancedOPlus11 -
        unbalancedThreeAdjugatePair
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44
          factorTwoIntrinsicSixUnbalancedKMinus01
          factorTwoIntrinsicSixUnbalancedKMinus21
          factorTwoIntrinsicSixUnbalancedKMinus41
          factorTwoIntrinsicSixUnbalancedKMinus01
          factorTwoIntrinsicSixUnbalancedKMinus21
          factorTwoIntrinsicSixUnbalancedKMinus41) = _
  rw [factorTwoIntrinsicSixUnbalancedEMinusDet_eq_aligned,
    unbalancedThreeAdjugatePair_eq_minusAligned,
    unbalancedThreeAdjugatePair_eq_minusAligned]
  unfold factorTwoIntrinsicSixUnbalancedKMinusOneSum
    factorTwoIntrinsicSixUnbalancedKMinusOneDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearSum
    factorTwoIntrinsicSixUnbalancedKMinusShearDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearTail
    factorTwoIntrinsicSixUnbalancedOPlusShearCross
    minusAlignedAdjugatePair
  ring

/-- Exact aligned diagonal formula for the sheared direction `P₃ - P₁`. -/
theorem factorTwoIntrinsicSixUnbalancedTMinusShearQ_eq_aligned :
    factorTwoIntrinsicSixUnbalancedTMinusShearQ =
      minusAlignedDeterminant
          factorTwoIntrinsicSixUnbalancedEMinusStrong
          factorTwoIntrinsicSixUnbalancedEMinusSkew
          factorTwoIntrinsicSixUnbalancedEMinusWeak
          factorTwoIntrinsicSixUnbalancedEMinusP4Sum
          factorTwoIntrinsicSixUnbalancedEMinusP4Difference
          factorTwoIntrinsicSixUnbalancedEMinus44 *
        factorTwoIntrinsicSixUnbalancedOPlusShearDiagonal -
      minusAlignedAdjugatePair
          factorTwoIntrinsicSixUnbalancedEMinusStrong
          factorTwoIntrinsicSixUnbalancedEMinusSkew
          factorTwoIntrinsicSixUnbalancedEMinusWeak
          factorTwoIntrinsicSixUnbalancedEMinusP4Sum
          factorTwoIntrinsicSixUnbalancedEMinusP4Difference
          factorTwoIntrinsicSixUnbalancedEMinus44
          factorTwoIntrinsicSixUnbalancedKMinusShearSum
          factorTwoIntrinsicSixUnbalancedKMinusShearDifference
          factorTwoIntrinsicSixUnbalancedKMinusShearTail
          factorTwoIntrinsicSixUnbalancedKMinusShearSum
          factorTwoIntrinsicSixUnbalancedKMinusShearDifference
          factorTwoIntrinsicSixUnbalancedKMinusShearTail := by
  rw [factorTwoIntrinsicSixUnbalancedTMinusShearQ_eq_fractionFree,
    factorTwoIntrinsicSixUnbalancedEMinusDet_eq_aligned]
  rw [show adjugateQuadratic
        factorTwoIntrinsicSixUnbalancedEMinus00
        factorTwoIntrinsicSixUnbalancedEMinus02
        factorTwoIntrinsicSixUnbalancedEMinus04
        factorTwoIntrinsicSixUnbalancedEMinus22
        factorTwoIntrinsicSixUnbalancedEMinus24
        factorTwoIntrinsicSixUnbalancedEMinus44
        (factorTwoIntrinsicSixUnbalancedKMinus03 -
          factorTwoIntrinsicSixUnbalancedKMinus01)
        (factorTwoIntrinsicSixUnbalancedKMinus23 -
          factorTwoIntrinsicSixUnbalancedKMinus21)
        (factorTwoIntrinsicSixUnbalancedKMinus43 -
          factorTwoIntrinsicSixUnbalancedKMinus41) =
      unbalancedThreeAdjugatePair
        factorTwoIntrinsicSixUnbalancedEMinus00
        factorTwoIntrinsicSixUnbalancedEMinus02
        factorTwoIntrinsicSixUnbalancedEMinus04
        factorTwoIntrinsicSixUnbalancedEMinus22
        factorTwoIntrinsicSixUnbalancedEMinus24
        factorTwoIntrinsicSixUnbalancedEMinus44
        (factorTwoIntrinsicSixUnbalancedKMinus03 -
          factorTwoIntrinsicSixUnbalancedKMinus01)
        (factorTwoIntrinsicSixUnbalancedKMinus23 -
          factorTwoIntrinsicSixUnbalancedKMinus21)
        (factorTwoIntrinsicSixUnbalancedKMinus43 -
          factorTwoIntrinsicSixUnbalancedKMinus41)
        (factorTwoIntrinsicSixUnbalancedKMinus03 -
          factorTwoIntrinsicSixUnbalancedKMinus01)
        (factorTwoIntrinsicSixUnbalancedKMinus23 -
          factorTwoIntrinsicSixUnbalancedKMinus21)
        (factorTwoIntrinsicSixUnbalancedKMinus43 -
          factorTwoIntrinsicSixUnbalancedKMinus41) by
      unfold adjugateQuadratic unbalancedThreeAdjugatePair
      ring,
    unbalancedThreeAdjugatePair_eq_minusAligned]
  unfold factorTwoIntrinsicSixUnbalancedKMinusShearSum
    factorTwoIntrinsicSixUnbalancedKMinusShearDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearTail
    factorTwoIntrinsicSixUnbalancedOPlusShearDiagonal symmetricQuadratic
  ring

theorem factorTwoIntrinsicSixUnbalancedTMinusMinor_eq_shear :
    factorTwoIntrinsicSixUnbalancedTMinusMinor =
      factorTwoIntrinsicSixUnbalancedTMinusShearA *
          factorTwoIntrinsicSixUnbalancedTMinusShearQ -
        factorTwoIntrinsicSixUnbalancedTMinusShearP ^ 2 := by
  unfold factorTwoIntrinsicSixUnbalancedTMinusMinor
  rw [leadingMinorTwo_eq_shear
    factorTwoIntrinsicSixUnbalancedTMinus11
    factorTwoIntrinsicSixUnbalancedTMinus13
    factorTwoIntrinsicSixUnbalancedTMinus33 1]
  unfold factorTwoIntrinsicSixUnbalancedTMinusShearA
    factorTwoIntrinsicSixUnbalancedTMinusShearP
    factorTwoIntrinsicSixUnbalancedTMinusShearQ
  ring

/-- The second negative Schur pivot is closed by strict positivity of the
full five-dimensional lower Gram.  The adjugate test vector extracts this
minor as one value of that form. -/
theorem factorTwoIntrinsicSixUnbalancedTMinusMinor_pos :
    0 < factorTwoIntrinsicSixUnbalancedTMinusMinor := by
  let d : ℝ := factorTwoIntrinsicSixUnbalancedEMinusDet
  let a : ℝ := factorTwoIntrinsicSixUnbalancedTMinus11
  let b : ℝ := factorTwoIntrinsicSixUnbalancedTMinus13
  let c : ℝ := factorTwoIntrinsicSixUnbalancedTMinus33
  let ell0 : ℝ := -b * factorTwoIntrinsicSixUnbalancedKMinus01 +
    a * factorTwoIntrinsicSixUnbalancedKMinus03
  let ell2 : ℝ := -b * factorTwoIntrinsicSixUnbalancedKMinus21 +
    a * factorTwoIntrinsicSixUnbalancedKMinus23
  let ell4 : ℝ := -b * factorTwoIntrinsicSixUnbalancedKMinus41 +
    a * factorTwoIntrinsicSixUnbalancedKMinus43
  let v0 : ℝ := adjugateVector
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44 ell0 ell2 ell4 0
  let v2 : ℝ := adjugateVector
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44 ell0 ell2 ell4 1
  let v4 : ℝ := adjugateVector
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44 ell0 ell2 ell4 2
  rcases factorTwoIntrinsicSixUnbalancedEMinus_positive with
    ⟨_he00, _heMinor, hd⟩
  have ha : 0 < a := by
    simpa only [a] using factorTwoIntrinsicSixUnbalancedTMinus11_pos
  have hdeq :
      symmetricDeterminant
        factorTwoIntrinsicSixUnbalancedEMinus00
        factorTwoIntrinsicSixUnbalancedEMinus02
        factorTwoIntrinsicSixUnbalancedEMinus04
        factorTwoIntrinsicSixUnbalancedEMinus22
        factorTwoIntrinsicSixUnbalancedEMinus24
        factorTwoIntrinsicSixUnbalancedEMinus44 = d := by
    rfl
  have haeq :
      d * factorTwoIntrinsicSixUnbalancedOPlus11 -
        unbalancedThreeAdjugatePair
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44
          factorTwoIntrinsicSixUnbalancedKMinus01
          factorTwoIntrinsicSixUnbalancedKMinus21
          factorTwoIntrinsicSixUnbalancedKMinus41
          factorTwoIntrinsicSixUnbalancedKMinus01
          factorTwoIntrinsicSixUnbalancedKMinus21
          factorTwoIntrinsicSixUnbalancedKMinus41 = a := by
    rfl
  have hbeq :
      d * factorTwoIntrinsicSixUnbalancedOPlus13 -
        unbalancedThreeAdjugatePair
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44
          factorTwoIntrinsicSixUnbalancedKMinus01
          factorTwoIntrinsicSixUnbalancedKMinus21
          factorTwoIntrinsicSixUnbalancedKMinus41
          factorTwoIntrinsicSixUnbalancedKMinus03
          factorTwoIntrinsicSixUnbalancedKMinus23
          factorTwoIntrinsicSixUnbalancedKMinus43 = b := by
    rfl
  have hceq :
      d * factorTwoIntrinsicSixUnbalancedOPlus33 -
        unbalancedThreeAdjugatePair
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44
          factorTwoIntrinsicSixUnbalancedKMinus03
          factorTwoIntrinsicSixUnbalancedKMinus23
          factorTwoIntrinsicSixUnbalancedKMinus43
          factorTwoIntrinsicSixUnbalancedKMinus03
          factorTwoIntrinsicSixUnbalancedKMinus23
          factorTwoIntrinsicSixUnbalancedKMinus43 = c := by
    rfl
  have hid0 := fiveQuadratic_two_odd_adjugate_identity
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicSixUnbalancedKMinus41
    factorTwoIntrinsicSixUnbalancedKMinus03
    factorTwoIntrinsicSixUnbalancedKMinus23
    factorTwoIntrinsicSixUnbalancedKMinus43
    factorTwoIntrinsicSixUnbalancedOPlus11
    factorTwoIntrinsicSixUnbalancedOPlus13
    factorTwoIntrinsicSixUnbalancedOPlus33
  dsimp only at hid0
  rw [hdeq, haeq, hbeq, hceq] at hid0
  have hid :
      factorTwoIntrinsicSixUnbalancedMinorMinusExactFiveQuadratic
          (-v0) (-v2) (-v4) (d * (-b)) (d * a) =
        d * a * (a * c - b ^ 2) := by
    dsimp only [v0, v2, v4, ell0, ell2, ell4]
    simpa only [factorTwoIntrinsicSixUnbalancedMinorMinusExactFiveQuadratic]
      using hid0
  have hne :
      -v0 ≠ 0 ∨ -v2 ≠ 0 ∨ -v4 ≠ 0 ∨ d * (-b) ≠ 0 ∨ d * a ≠ 0 :=
    Or.inr (Or.inr (Or.inr (Or.inr
      (mul_ne_zero hd.ne' ha.ne'))))
  have hquad := factorTwoIntrinsicSixUnbalancedMinorMinusExactFive_pos
    (-v0) (-v2) (-v4) (d * (-b)) (d * a) hne
  rw [hid] at hquad
  have hminor : 0 < a * c - b ^ 2 := by
    rcases mul_pos_iff.mp hquad with hpos | hneg
    · exact hpos.2
    · exact False.elim ((not_lt_of_ge (mul_nonneg hd.le ha.le)) hneg.1)
  unfold factorTwoIntrinsicSixUnbalancedTMinusMinor leadingMinorTwo
  simpa only [a, b, c] using hminor

theorem factorTwoIntrinsicSixUnbalancedTMinusShearA_pos :
    0 < factorTwoIntrinsicSixUnbalancedTMinusShearA := by
  simpa only [factorTwoIntrinsicSixUnbalancedTMinusShearA] using
    factorTwoIntrinsicSixUnbalancedTMinus11_pos

theorem factorTwoIntrinsicSixUnbalancedTMinusShearQ_pos :
    0 < factorTwoIntrinsicSixUnbalancedTMinusShearQ := by
  have hminor := factorTwoIntrinsicSixUnbalancedTMinusMinor_pos
  rw [factorTwoIntrinsicSixUnbalancedTMinusMinor_eq_shear] at hminor
  have hA := factorTwoIntrinsicSixUnbalancedTMinusShearA_pos
  nlinarith [sq_nonneg factorTwoIntrinsicSixUnbalancedTMinusShearP]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusMinorStructural
