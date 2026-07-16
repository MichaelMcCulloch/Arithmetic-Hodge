import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusBorderKernelStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusDeterminantStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusBorderH3Structural

noncomputable section

open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PerturbationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingCorrelations
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedAlternatingModelsStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusBorderKernelStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

/-!
# The negative completed-border `H3` row

The row is compiled into one negative-endpoint even profile and one complete
alternating profile before any estimate is made.  Its analytic remainder is
then controlled through a single pair of global Bernstein splits on `[0,2]`.
-/

/-- The complete alternating polynomial attached to the `H3` border row. -/
def minusBorderAlternatingQH3 : ℝ → ℝ := fun t ↦
  plusDetAlternatingQ (19 / 20) (-21 / 20) (9 / 50)
      (44161 / 40320) (-15 / 8) 1 t +
    plusDetAlternatingQ (47 / 2520) (-43 / 1120) (4129 / 156800)
      1 0 0 t

theorem minusBorderAlternatingQH3_polynomial (t : ℝ) :
    minusBorderAlternatingQH3 t =
      (37101707 / 14112000 : ℝ) +
        (19622011 / 18816000) * t +
        (4574277 / 12544000) * t ^ 2 -
        (16674703 / 2688000) * t ^ 3 +
        (23544497 / 5376000) * t ^ 4 -
        (6327 / 12800) * t ^ 5 -
        (6327 / 25600) * t ^ 6 +
        (63 / 3200) * t ^ 7 + (63 / 6400) * t ^ 8 := by
  unfold minusBorderAlternatingQH3 plusDetAlternatingQ alternatingQ41
    alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
  ring

private theorem continuous_minusBorderAlternatingQH3 :
    Continuous minusBorderAlternatingQH3 := by
  unfold minusBorderAlternatingQH3 plusDetAlternatingQ alternatingQ41
    alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
  fun_prop

private theorem minusBorderH3Couplings_eq_sharpModel :
    factorTwoCenteredAlternatingCoupling
        (plusDetAlternatingEvenProfile (19 / 20) (-21 / 20) (9 / 50))
        (plusDetAlternatingOddProfile (44161 / 40320) (-15 / 8) 1) +
      factorTwoCenteredAlternatingCoupling
        (plusDetAlternatingEvenProfile
          (47 / 2520) (-43 / 1120) (4129 / 156800))
        (plusDetAlternatingOddProfile 1 0 0) =
      plusDetAlternatingSharpModel minusBorderAlternatingQH3 := by
  let q : ℝ → ℝ := plusDetAlternatingQ
    (19 / 20) (-21 / 20) (9 / 50) (44161 / 40320) (-15 / 8) 1
  let r : ℝ → ℝ := plusDetAlternatingQ
    (47 / 2520) (-43 / 1120) (4129 / 156800) 1 0 0
  have hq : Continuous q := by
    dsimp only [q]
    unfold plusDetAlternatingQ alternatingQ41 alternatingQ43
      alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  have hr : Continuous r := by
    dsimp only [r]
    unfold plusDetAlternatingQ alternatingQ41 alternatingQ43
      alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  have hmain := plusDetAlternatingCoupling_profile_eq_sharpModel
    (19 / 20) (-21 / 20) (9 / 50) (44161 / 40320) (-15 / 8) 1
  have htail := plusDetAlternatingCoupling_profile_eq_sharpModel
    (47 / 2520) (-43 / 1120) (4129 / 156800) 1 0 0
  have hmain' :
      factorTwoCenteredAlternatingCoupling
          (plusDetAlternatingEvenProfile (19 / 20) (-21 / 20) (9 / 50))
          (plusDetAlternatingOddProfile (44161 / 40320) (-15 / 8) 1) =
        plusDetAlternatingSharpModel q := by
    simpa only [plusDetAlternatingSharpModel] using hmain
  have htail' :
      factorTwoCenteredAlternatingCoupling
          (plusDetAlternatingEvenProfile
            (47 / 2520) (-43 / 1120) (4129 / 156800))
          (plusDetAlternatingOddProfile 1 0 0) =
        plusDetAlternatingSharpModel r := by
    simpa only [plusDetAlternatingSharpModel] using htail
  have hadd := plusDetAlternatingSharpModel_add q r hq hr
  rw [hmain', htail', ← hadd]
  rfl

set_option maxHeartbeats 800000 in
private theorem minusDetH3Core_eq_affineSharpModel :
    minusDetH3Core =
      (-47070178733 / 1411200000000 : ℝ) +
        (-88979 / 224000) * factorTwoIntrinsicFourP45Cross04 (-1) +
        (15483 / 32000) * factorTwoIntrinsicFourP45Cross24 (-1) +
        (1 / 2) * plusDetAlternatingSharpModel
          minusBorderAlternatingQH3 := by
  rw [← minusBorderH3Couplings_eq_sharpModel]
  repeat rw [plusDetAlternatingCoupling_profile_expansion]
  unfold minusDetH3Core minusDetH3
    factorTwoIntrinsicSixUnbalancedEMinusP4Sum
    factorTwoIntrinsicSixUnbalancedEMinusP4Difference
    factorTwoIntrinsicSixUnbalancedKMinusOneSum
    factorTwoIntrinsicSixUnbalancedKMinusOneDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearSum
    factorTwoIntrinsicSixUnbalancedKMinusShearDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearTail
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicSixUnbalancedKMinus03
    factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicSixUnbalancedKMinus23
    factorTwoIntrinsicSixUnbalancedKMinus41
    factorTwoIntrinsicSixUnbalancedKMinus43
  ring

/-- Exact cancellation-preserving structural decomposition of the `H3`
border row. -/
theorem minusDetH3Core_eq_structuralProfile :
    minusDetH3Core =
      minusBorderCompositeCore
          (-47070178733 / 1411200000000)
          (-88979 / 224000) (15483 / 32000)
          (1 / 2) minusBorderAlternatingQH3 +
        plusDetCompositeCleanTransfer (-88979 / 224000) (15483 / 32000) +
        minusBorderCompositeJointError
          (-88979 / 224000) (15483 / 32000)
          (1 / 2) minusBorderAlternatingQH3 := by
  rw [minusDetH3Core_eq_affineSharpModel]
  simpa only [minusBorderCompositeCleanTransfer] using
    minusBorderCompositeSharp_decomposition
      (-47070178733 / 1411200000000)
      (-88979 / 224000) (15483 / 32000)
      (1 / 2) minusBorderAlternatingQH3

/-! ## Global Bernstein splits for the joint analytic remainder -/

private def minusBorderH3PPositive (t : ℝ) : ℝ :=
  (38324033 / 70560000 : ℝ) * plusDetBernstein10B1 t +
    (98716673 / 90720000) * plusDetBernstein10B2 t +
    (322329653 / 211680000) * plusDetBernstein10B3 t +
    (4090984049 / 2963520000) * plusDetBernstein10B4 t +
    (1259347937 / 1778112000) * plusDetBernstein10B5 t +
    (343337153 / 2963520000) * plusDetBernstein10B6 t +
    (16722577 / 423360000) * plusDetBernstein10B7 t +
    (42647783 / 635040000) * plusDetBernstein10B8 t

private def minusBorderH3PNegative (t : ℝ) : ℝ :=
  (110081 / 8820000 : ℝ) * plusDetBernstein10B9 t

private def minusBorderH3MPositive (t : ℝ) : ℝ :=
  (14045993 / 423360000 : ℝ) * plusDetBernstein10B7 t +
    (44177557 / 635040000) * plusDetBernstein10B8 t

private def minusBorderH3MNegative (t : ℝ) : ℝ :=
  (35879381 / 70560000 : ℝ) * plusDetBernstein10B1 t +
    (87709997 / 90720000) * plusDetBernstein10B2 t +
    (155200963 / 105840000) * plusDetBernstein10B3 t +
    (4384843517 / 2963520000) * plusDetBernstein10B4 t +
    (1587092081 / 1778112000) * plusDetBernstein10B5 t +
    (650341949 / 2963520000) * plusDetBernstein10B6 t +
    (391001 / 17640000) * plusDetBernstein10B9 t

private theorem minusBorderH3_jointProfile_splits (t : ℝ) :
    minusBorderCompositeP (-88979 / 224000) (15483 / 32000)
        (1 / 2) minusBorderAlternatingQH3 t =
      minusBorderH3PPositive t - minusBorderH3PNegative t ∧
    minusBorderCompositeM (-88979 / 224000) (15483 / 32000)
        (1 / 2) minusBorderAlternatingQH3 t =
      minusBorderH3MPositive t - minusBorderH3MNegative t := by
  constructor
  · unfold minusBorderCompositeP plusDetCompositeP plusDetCompositeCe
      plusDetCompositeCa intrinsicAlternatingCorrelation
    rw [minusBorderAlternatingQH3_polynomial]
    unfold factorTwoIntrinsicP4Correlation04 factorTwoIntrinsicP4Correlation24
      minusBorderH3PPositive minusBorderH3PNegative plusDetBernstein10B1
      plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
      plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B7
      plusDetBernstein10B8 plusDetBernstein10B9
    ring
  · unfold minusBorderCompositeM plusDetCompositeM plusDetCompositeCe
      plusDetCompositeCa intrinsicAlternatingCorrelation
    rw [minusBorderAlternatingQH3_polynomial]
    unfold factorTwoIntrinsicP4Correlation04 factorTwoIntrinsicP4Correlation24
      minusBorderH3MPositive minusBorderH3MNegative plusDetBernstein10B1
      plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
      plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B7
      plusDetBernstein10B8 plusDetBernstein10B9
    ring

private theorem minusBorderH3_signedProfiles_nonneg
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    0 ≤ minusBorderH3PPositive t ∧ 0 ≤ minusBorderH3PNegative t ∧
      0 ≤ minusBorderH3MPositive t ∧ 0 ≤ minusBorderH3MNegative t := by
  have hx0 : 0 ≤ t / 2 := by linarith [ht.1]
  have hx1 : 0 ≤ 1 - t / 2 := by linarith [ht.2]
  unfold minusBorderH3PPositive minusBorderH3PNegative
    minusBorderH3MPositive minusBorderH3MNegative plusDetBernstein10B1
    plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
    plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B7
    plusDetBernstein10B8 plusDetBernstein10B9
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

set_option maxHeartbeats 4000000 in
private theorem integral_minusBorderH3_rationalAbsoluteMajorant :
    (∫ t : ℝ in 0..2,
      plusDetJointRationalAbsoluteMajorant
        (fun s ↦ minusBorderH3PPositive s + minusBorderH3PNegative s)
        (fun s ↦ minusBorderH3MPositive s + minusBorderH3MNegative s) t) =
      (9046456615791639884979132745290566926186425160276765261 /
        761633489781964800000000000000000000000000000000000000000000 : ℝ) := by
  unfold plusDetJointRationalAbsoluteMajorant plusDetJointRationalA
    minusBorderH3PPositive minusBorderH3PNegative
    minusBorderH3MPositive minusBorderH3MNegative plusDetBernstein10B1
    plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
    plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B7
    plusDetBernstein10B8 plusDetBernstein10B9
  simp_rw [integratedPoleFreeEnvelope_expansion]
  ring_nf
  repeat' rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

private theorem abs_minusBorderH3_jointError_lt :
    |minusBorderCompositeJointError
        (-88979 / 224000) (15483 / 32000)
        (1 / 2) minusBorderAlternatingQH3| < (3 / 250000 : ℝ) := by
  have hq : Continuous minusBorderAlternatingQH3 :=
    continuous_minusBorderAlternatingQH3
  have hPp : Continuous minusBorderH3PPositive := by
    unfold minusBorderH3PPositive plusDetBernstein10B1
      plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
      plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B7
      plusDetBernstein10B8
    fun_prop
  have hNp : Continuous minusBorderH3PNegative := by
    unfold minusBorderH3PNegative plusDetBernstein10B9
    fun_prop
  have hPm : Continuous minusBorderH3MPositive := by
    unfold minusBorderH3MPositive plusDetBernstein10B7 plusDetBernstein10B8
    fun_prop
  have hNm : Continuous minusBorderH3MNegative := by
    unfold minusBorderH3MNegative plusDetBernstein10B1
      plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
      plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B9
    fun_prop
  have habs := abs_plusDetCompositeJointError_le_of_signed_splits
    (-(-88979 / 224000)) (-(15483 / 32000)) (1 / 2)
    minusBorderAlternatingQH3 minusBorderH3PPositive
    minusBorderH3PNegative minusBorderH3MPositive minusBorderH3MNegative
    hq hPp hNp hPm hNm
    (fun t ↦ by
      simpa only [minusBorderCompositeP] using
        (minusBorderH3_jointProfile_splits t).1)
    (fun t ↦ by
      simpa only [minusBorderCompositeM] using
        (minusBorderH3_jointProfile_splits t).2)
    (fun t ht ↦ minusBorderH3_signedProfiles_nonneg ht)
  have habs' :
      |minusBorderCompositeJointError
          (-88979 / 224000) (15483 / 32000)
          (1 / 2) minusBorderAlternatingQH3| ≤
        ∫ t : ℝ in 0..2,
          plusDetJointAbsoluteMajorant
            (fun s ↦ minusBorderH3PPositive s + minusBorderH3PNegative s)
            (fun s ↦ minusBorderH3MPositive s + minusBorderH3MNegative s) t := by
    unfold minusBorderCompositeJointError
    exact habs
  have hrat := integral_plusDetJointAbsoluteMajorant_le_rational
    (fun s ↦ minusBorderH3PPositive s + minusBorderH3PNegative s)
    (fun s ↦ minusBorderH3MPositive s + minusBorderH3MNegative s)
    (hPp.add hNp) (hPm.add hNm) (fun t ht ↦ by
      have h := minusBorderH3_signedProfiles_nonneg ht
      exact ⟨add_nonneg h.1 h.2.1,
        add_nonneg h.2.2.1 h.2.2.2⟩)
  rw [integral_minusBorderH3_rationalAbsoluteMajorant] at hrat
  exact (habs'.trans hrat).trans_lt (by norm_num)

private theorem abs_minusBorderH3_cleanTransfer_lt :
    |plusDetCompositeCleanTransfer
        (-88979 / 224000) (15483 / 32000)| < (1 / 580000 : ℝ) := by
  have h := abs_plusDetCompositeCleanTransfer_lt
    (-88979 / 224000) (15483 / 32000) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

/-! ## Exact archimedean quotient data -/

private def minusBorderAlternatingArchQuotientH3 (t : ℝ) : ℝ :=
  (-1717459337 / 7056000 : ℝ) +
    (1717459337 / 14112000) * t -
    (8001703 / 134400) * t ^ 2 +
    (379953477 / 12544000) * t ^ 3 -
    (1197 / 80) * t ^ 4 +
    (23544497 / 5376000) * t ^ 5 -
    (6327 / 25600) * t ^ 7 + (63 / 6400) * t ^ 9

private theorem minusBorderAlternatingArchDivisionH3
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    t ^ 2 * minusBorderAlternatingQH3 t / (2 + t) =
      minusBorderAlternatingArchQuotientH3 t +
        (1717459337 / 3528000 : ℝ) * (1 / (2 + t)) := by
  have hden : 2 + t ≠ 0 := by linarith [ht.1]
  rw [minusBorderAlternatingQH3_polynomial]
  unfold minusBorderAlternatingArchQuotientH3
  field_simp [hden]
  ring

private theorem integral_minusBorderAlternatingArchQuotientH3 :
    (∫ t : ℝ in 0..2, minusBorderAlternatingArchQuotientH3 t) =
      (-3170071637 / 9408000 : ℝ) := by
  unfold minusBorderAlternatingArchQuotientH3
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  norm_num

private theorem integral_minusBorderAlternatingQH3_moment_one :
    (∫ t : ℝ in 0..2,
      t * intrinsicAlternatingCorrelation minusBorderAlternatingQH3 t) =
        (854099 / 604800 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [minusBorderAlternatingQH3_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_minusBorderAlternatingQH3_moment_three :
    (∫ t : ℝ in 0..2,
      t ^ 3 * intrinsicAlternatingCorrelation minusBorderAlternatingQH3 t) =
        (368491 / 302400 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [minusBorderAlternatingQH3_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_minusBorderAlternatingQH3_moment_five :
    (∫ t : ℝ in 0..2,
      t ^ 5 * intrinsicAlternatingCorrelation minusBorderAlternatingQH3 t) =
        (313946777 / 203742000 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [minusBorderAlternatingQH3_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem minusBorderAlternatingSharpArchModelH3_eq :
    intrinsicAlternatingSharpArchModel minusBorderAlternatingQH3 =
      (-3170071637 / 9408000 : ℝ) +
        (1717459337 / 3528000) * Real.log 2 +
        (854099 / 604800) *
          intrinsicAlternatingKernelCoeff1 yoshidaEndpointA +
        (368491 / 302400) *
          intrinsicAlternatingKernelCoeff3 yoshidaEndpointA +
        (313946777 / 203742000) *
          intrinsicAlternatingKernelCoeff5 yoshidaEndpointA := by
  apply intrinsicAlternatingSharpArchModel_eq_data_plusDet
    minusBorderAlternatingQH3 minusBorderAlternatingArchQuotientH3
    (1717459337 / 3528000) (-3170071637 / 9408000)
    (854099 / 604800) (368491 / 302400) (313946777 / 203742000)
  · exact continuous_minusBorderAlternatingQH3
  · unfold minusBorderAlternatingArchQuotientH3
    fun_prop
  · exact minusBorderAlternatingArchDivisionH3
  · exact integral_minusBorderAlternatingArchQuotientH3
  · exact integral_minusBorderAlternatingQH3_moment_one
  · exact integral_minusBorderAlternatingQH3_moment_three
  · exact integral_minusBorderAlternatingQH3_moment_five

private theorem minusBorderAlternatingSharpArchModelH3_bounds :
    (615159 / 1000000 : ℝ) <
        intrinsicAlternatingSharpArchModel minusBorderAlternatingQH3 ∧
      intrinsicAlternatingSharpArchModel minusBorderAlternatingQH3 <
        (615160 / 1000000 : ℝ) := by
  rw [minusBorderAlternatingSharpArchModelH3_eq]
  unfold intrinsicAlternatingKernelCoeff1 intrinsicAlternatingKernelCoeff3
    intrinsicAlternatingKernelCoeff5 yoshidaEndpointA
  have hlog := strict_log_two_fine_bounds
  have h2 := log_two_pow_fine_bounds_plusDet 2 (by norm_num)
  have h3 := log_two_pow_fine_bounds_plusDet 3 (by norm_num)
  have h4 := log_two_pow_fine_bounds_plusDet 4 (by norm_num)
  have h5 := log_two_pow_fine_bounds_plusDet 5 (by norm_num)
  have h6 := log_two_pow_fine_bounds_plusDet 6 (by norm_num)
  have h7 := log_two_pow_fine_bounds_plusDet 7 (by norm_num)
  constructor <;> nlinarith [hlog.1, hlog.2, h2.1, h2.2, h3.1, h3.2,
    h4.1, h4.2, h5.1, h5.2, h6.1, h6.2, h7.1, h7.2]

/-! ## Retained-prime value and explicit core -/

private theorem minusBorderCompositePH3_polynomial (t : ℝ) :
    minusBorderCompositeP (-88979 / 224000) (15483 / 32000)
        (1 / 2) minusBorderAlternatingQH3 t =
      (38324033 / 14112000 : ℝ) * t +
        (1184117 / 56448000) * t ^ 2 -
        (1131941 / 672000) * t ^ 3 -
        (69963077 / 15052800) * t ^ 4 +
        (874403 / 128000) * t ^ 5 -
        (28859177 / 10752000) * t ^ 6 +
        (15483 / 512000) * t ^ 7 +
        (1467 / 10240) * t ^ 8 - (63 / 12800) * t ^ 10 := by
  rw [(minusBorderH3_jointProfile_splits t).1]
  unfold minusBorderH3PPositive minusBorderH3PNegative
    plusDetBernstein10B1 plusDetBernstein10B2 plusDetBernstein10B3
    plusDetBernstein10B4 plusDetBernstein10B5 plusDetBernstein10B6
    plusDetBernstein10B7 plusDetBernstein10B8 plusDetBernstein10B9
  ring

private theorem minusBorderCompositePH3_tau_bounds :
    (46112303 / 100000000 : ℝ) <
        minusBorderCompositeP (-88979 / 224000) (15483 / 32000)
          (1 / 2) minusBorderAlternatingQH3
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      minusBorderCompositeP (-88979 / 224000) (15483 / 32000)
          (1 / 2) minusBorderAlternatingQH3
          (factorTwoPrimeShift / yoshidaEndpointA) <
        (46112304 / 100000000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 1169925001 / 1000000000
  have htau := factorTwoPrimeRatio_ultrafine_bounds_plusDet
  have hy0 : 0 < y := by
    dsimp only [y, tau]
    linarith [htau.1]
  have hyU : y < (1 / 1000000000 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 := offset_pow_lt_plusDet hy0.le hyU 2 (by norm_num)
  have hy3 := offset_pow_lt_plusDet hy0.le hyU 3 (by norm_num)
  have hy4 := offset_pow_lt_plusDet hy0.le hyU 4 (by norm_num)
  have hy5 := offset_pow_lt_plusDet hy0.le hyU 5 (by norm_num)
  have hy6 := offset_pow_lt_plusDet hy0.le hyU 6 (by norm_num)
  have hy7 := offset_pow_lt_plusDet hy0.le hyU 7 (by norm_num)
  have hy8 := offset_pow_lt_plusDet hy0.le hyU 8 (by norm_num)
  have hy9 := offset_pow_lt_plusDet hy0.le hyU 9 (by norm_num)
  have hy10 := offset_pow_lt_plusDet hy0.le hyU 10 (by norm_num)
  have htauy : tau = 1169925001 / 1000000000 + y := by
    dsimp only [y]
    ring
  dsimp only [tau] at htauy ⊢
  rw [htauy, minusBorderCompositePH3_polynomial]
  ring_nf
  constructor <;> nlinarith [hy2, hy3, hy4, hy5, hy6, hy7, hy8, hy9,
    hy10, sq_nonneg y, pow_nonneg hy0.le 3, pow_nonneg hy0.le 4,
    pow_nonneg hy0.le 5, pow_nonneg hy0.le 6, pow_nonneg hy0.le 7,
    pow_nonneg hy0.le 8, pow_nonneg hy0.le 9, pow_nonneg hy0.le 10]

private theorem minusBorderCompositeCoreH3_bounds :
    (9419 / 1000000 : ℝ) <
        minusBorderCompositeCore (-47070178733 / 1411200000000)
          (-88979 / 224000) (15483 / 32000)
          (1 / 2) minusBorderAlternatingQH3 ∧
      minusBorderCompositeCore (-47070178733 / 1411200000000)
          (-88979 / 224000) (15483 / 32000)
          (1 / 2) minusBorderAlternatingQH3 < (377 / 40000 : ℝ) := by
  have hR04 := minusBorderCompositeR04_bounds
  have hR24 := minusBorderCompositeR24_bounds
  have harch := minusBorderAlternatingSharpArchModelH3_bounds
  have hP := minusBorderCompositePH3_tau_bounds
  have hbeta := log_three_div_sqrt_three_fine_bounds_plusDet
  have hprod := mul_strict_bounds_plusDet hbeta hP
    (by norm_num) (by norm_num)
  unfold minusBorderCompositeCore
  constructor <;> nlinarith [hR04.1, hR04.2, hR24.1, hR24.2,
    harch.1, harch.2, hprod.1, hprod.2]

/-- Structural box for the complete negative-border `H3` core. -/
theorem minusDetH3Core_bounds_structural :
    (47 / 5000 : ℝ) < minusDetH3Core ∧
      minusDetH3Core < (189 / 20000 : ℝ) := by
  have hcore := minusBorderCompositeCoreH3_bounds
  have hclean := abs_lt.mp abs_minusBorderH3_cleanTransfer_lt
  have hjoint := abs_lt.mp abs_minusBorderH3_jointError_lt
  rw [minusDetH3Core_eq_structuralProfile]
  constructor <;> nlinarith [hcore.1, hcore.2, hclean.1, hclean.2,
    hjoint.1, hjoint.2]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusBorderH3Structural
