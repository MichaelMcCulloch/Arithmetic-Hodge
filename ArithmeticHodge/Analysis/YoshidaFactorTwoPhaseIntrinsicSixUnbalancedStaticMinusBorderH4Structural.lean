import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusBorderKernelStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusDeterminantStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusBorderH4Structural

noncomputable section

open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
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
# The complete negative-border `H4` profile

The proof keeps the negative even endpoint and both alternating rank-one
profiles together.  Its analytic error is bounded by one global Bernstein
majorant on `[0,2]`; no correlation is subdivided or sampled.
-/

private def minusBorderH4Q : ℝ → ℝ := fun t ↦
  plusDetAlternatingQ (-259 / 100) (291 / 100) (-3 / 8)
      (44161 / 40320) (-15 / 8) 1 t +
    plusDetAlternatingQ (-47 / 180) (43 / 80) (-4129 / 11200)
      (-73 / 80) 1 0 t

private theorem minusBorderH4Couplings_eq_sharpModel :
    factorTwoCenteredAlternatingCoupling
        (plusDetAlternatingEvenProfile (-259 / 100) (291 / 100) (-3 / 8))
        (plusDetAlternatingOddProfile (44161 / 40320) (-15 / 8) 1) +
      factorTwoCenteredAlternatingCoupling
        (plusDetAlternatingEvenProfile
          (-47 / 180) (43 / 80) (-4129 / 11200))
        (plusDetAlternatingOddProfile (-73 / 80) 1 0) =
      plusDetAlternatingSharpModel minusBorderH4Q := by
  let q : ℝ → ℝ := plusDetAlternatingQ
    (-259 / 100) (291 / 100) (-3 / 8) (44161 / 40320) (-15 / 8) 1
  let r : ℝ → ℝ := plusDetAlternatingQ
    (-47 / 180) (43 / 80) (-4129 / 11200) (-73 / 80) 1 0
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
    (-259 / 100) (291 / 100) (-3 / 8) (44161 / 40320) (-15 / 8) 1
  have htail := plusDetAlternatingCoupling_profile_eq_sharpModel
    (-47 / 180) (43 / 80) (-4129 / 11200) (-73 / 80) 1 0
  have hmain' :
      factorTwoCenteredAlternatingCoupling
          (plusDetAlternatingEvenProfile (-259 / 100) (291 / 100) (-3 / 8))
          (plusDetAlternatingOddProfile (44161 / 40320) (-15 / 8) 1) =
        plusDetAlternatingSharpModel q := by
    simpa only [plusDetAlternatingSharpModel] using hmain
  have htail' :
      factorTwoCenteredAlternatingCoupling
          (plusDetAlternatingEvenProfile
            (-47 / 180) (43 / 80) (-4129 / 11200))
          (plusDetAlternatingOddProfile (-73 / 80) 1 0) =
        plusDetAlternatingSharpModel r := by
    simpa only [plusDetAlternatingSharpModel] using htail
  have hadd := plusDetAlternatingSharpModel_add q r hq hr
  rw [hmain', htail', ← hadd]
  rfl

set_option maxHeartbeats 800000 in
private theorem minusDetH4Core_eq_affineSharpModel :
    minusDetH4Core =
      (30817763257 / 806400000000 : ℝ) +
        (505319 / 480000) * factorTwoIntrinsicFourP45Cross04 (-1) +
        (-1427289 / 1120000) * factorTwoIntrinsicFourP45Cross24 (-1) +
        (1 / 2) * plusDetAlternatingSharpModel minusBorderH4Q := by
  rw [← minusBorderH4Couplings_eq_sharpModel]
  repeat rw [plusDetAlternatingCoupling_profile_expansion]
  unfold minusDetH4Core minusDetH4
    factorTwoIntrinsicSixUnbalancedEMinusP4Sum
    factorTwoIntrinsicSixUnbalancedEMinusP4Difference
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedKMinusOneSum
    factorTwoIntrinsicSixUnbalancedKMinusOneDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearSum
    factorTwoIntrinsicSixUnbalancedKMinusShearDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearTail
    factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicSixUnbalancedKMinus03
    factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicSixUnbalancedKMinus23
    factorTwoIntrinsicSixUnbalancedKMinus41
    factorTwoIntrinsicSixUnbalancedKMinus43
  ring

private theorem minusDetH4Core_composite_decomposition :
    minusDetH4Core =
      minusBorderCompositeCore (30817763257 / 806400000000)
          (505319 / 480000) (-1427289 / 1120000)
          (1 / 2) minusBorderH4Q +
        minusBorderCompositeCleanTransfer
          (505319 / 480000) (-1427289 / 1120000) +
        minusBorderCompositeJointError
          (505319 / 480000) (-1427289 / 1120000)
          (1 / 2) minusBorderH4Q := by
  calc
    minusDetH4Core =
        (30817763257 / 806400000000 : ℝ) +
          (505319 / 480000) * factorTwoIntrinsicFourP45Cross04 (-1) +
          (-1427289 / 1120000) * factorTwoIntrinsicFourP45Cross24 (-1) +
          (1 / 2) * plusDetAlternatingSharpModel minusBorderH4Q :=
      minusDetH4Core_eq_affineSharpModel
    _ = _ := minusBorderCompositeSharp_decomposition _ _ _ _ _

private theorem minusBorderH4Q_polynomial (t : ℝ) :
    minusBorderH4Q t =
      (-7975253 / 1344000 : ℝ) -
        (17267527 / 8064000) * t -
        (7023333 / 1792000) * t ^ 2 +
        (41398393 / 2304000) * t ^ 3 -
        (52587527 / 4608000) * t ^ 4 +
        (210629 / 179200) * t ^ 5 +
        (210629 / 358400) * t ^ 6 -
        (21 / 512) * t ^ 7 - (21 / 1024) * t ^ 8 := by
  unfold minusBorderH4Q plusDetAlternatingQ alternatingQ41
    alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
  ring

/-! ## One global signed Bernstein split -/

private def minusBorderH4PPositive (t : ℝ) : ℝ :=
  (451201 / 11200000 : ℝ) * plusDetBernstein10B9 t

private def minusBorderH4PNegative (t : ℝ) : ℝ :=
  (13788511 / 11200000 : ℝ) * plusDetBernstein10B1 t +
    (1115973797 / 453600000) * plusDetBernstein10B2 t +
    (2180808823 / 604800000) * plusDetBernstein10B3 t +
    (7237052957 / 2116800000) * plusDetBernstein10B4 t +
    (2355841571 / 1270080000) * plusDetBernstein10B5 t +
    (737853359 / 2116800000) * plusDetBernstein10B6 t +
    (9220667 / 120960000) * plusDetBernstein10B7 t +
    (17764627 / 90720000) * plusDetBernstein10B8 t

private def minusBorderH4MPositive (t : ℝ) : ℝ :=
  (38386997 / 33600000 : ℝ) * plusDetBernstein10B1 t +
    (970762193 / 453600000) * plusDetBernstein10B2 t +
    (2089210867 / 604800000) * plusDetBernstein10B3 t +
    (7784377553 / 2116800000) * plusDetBernstein10B4 t +
    (424632917 / 181440000) * plusDetBernstein10B5 t +
    (1320941651 / 2116800000) * plusDetBernstein10B6 t +
    (1624933 / 33600000) * plusDetBernstein10B9 t

private def minusBorderH4MNegative (t : ℝ) : ℝ :=
  (2713133 / 24192000 : ℝ) * plusDetBernstein10B7 t +
    (14851937 / 90720000) * plusDetBernstein10B8 t

private theorem minusBorderH4_jointProfile_splits (t : ℝ) :
    minusBorderCompositeP (505319 / 480000) (-1427289 / 1120000)
        (1 / 2) minusBorderH4Q t =
      minusBorderH4PPositive t - minusBorderH4PNegative t ∧
    minusBorderCompositeM (505319 / 480000) (-1427289 / 1120000)
        (1 / 2) minusBorderH4Q t =
      minusBorderH4MPositive t - minusBorderH4MNegative t := by
  constructor
  · unfold minusBorderCompositeP plusDetCompositeP plusDetCompositeCe
      plusDetCompositeCa intrinsicAlternatingCorrelation
    rw [minusBorderH4Q_polynomial]
    unfold factorTwoIntrinsicP4Correlation04 factorTwoIntrinsicP4Correlation24
      minusBorderH4PPositive minusBorderH4PNegative plusDetBernstein10B1
      plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
      plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B7
      plusDetBernstein10B8 plusDetBernstein10B9
    ring
  · unfold minusBorderCompositeM plusDetCompositeM plusDetCompositeCe
      plusDetCompositeCa intrinsicAlternatingCorrelation
    rw [minusBorderH4Q_polynomial]
    unfold factorTwoIntrinsicP4Correlation04 factorTwoIntrinsicP4Correlation24
      minusBorderH4MPositive minusBorderH4MNegative plusDetBernstein10B1
      plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
      plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B7
      plusDetBernstein10B8 plusDetBernstein10B9
    ring

private theorem minusBorderH4_signedProfiles_nonneg
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    0 ≤ minusBorderH4PPositive t ∧ 0 ≤ minusBorderH4PNegative t ∧
      0 ≤ minusBorderH4MPositive t ∧ 0 ≤ minusBorderH4MNegative t := by
  have hx0 : 0 ≤ t / 2 := by linarith [ht.1]
  have hx1 : 0 ≤ 1 - t / 2 := by linarith [ht.2]
  unfold minusBorderH4PPositive minusBorderH4PNegative
    minusBorderH4MPositive minusBorderH4MNegative plusDetBernstein10B1
    plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
    plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B7
    plusDetBernstein10B8 plusDetBernstein10B9
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

set_option maxHeartbeats 4000000 in
private theorem integral_minusBorderH4_rationalAbsoluteMajorant :
    (∫ t : ℝ in 0..2,
      plusDetJointRationalAbsoluteMajorant
        (fun s ↦ minusBorderH4PPositive s + minusBorderH4PNegative s)
        (fun s ↦ minusBorderH4MPositive s + minusBorderH4MNegative s) t) =
      (274852127703466891426609235531767540493709242858667098783 /
        9180403671479040000000000000000000000000000000000000000000000 : ℝ) := by
  unfold plusDetJointRationalAbsoluteMajorant plusDetJointRationalA
    minusBorderH4PPositive minusBorderH4PNegative
    minusBorderH4MPositive minusBorderH4MNegative plusDetBernstein10B1
    plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
    plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B7
    plusDetBernstein10B8 plusDetBernstein10B9
  simp_rw [integratedPoleFreeEnvelope_expansion]
  ring_nf
  repeat' rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

private theorem abs_minusBorderCompositeJointErrorH4_lt :
    |minusBorderCompositeJointError
        (505319 / 480000) (-1427289 / 1120000)
        (1 / 2) minusBorderH4Q| < (3 / 100000 : ℝ) := by
  have hq : Continuous minusBorderH4Q := by
    unfold minusBorderH4Q plusDetAlternatingQ alternatingQ41
      alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  have hPp : Continuous minusBorderH4PPositive := by
    unfold minusBorderH4PPositive plusDetBernstein10B9
    fun_prop
  have hNp : Continuous minusBorderH4PNegative := by
    unfold minusBorderH4PNegative plusDetBernstein10B1
      plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
      plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B7
      plusDetBernstein10B8
    fun_prop
  have hPm : Continuous minusBorderH4MPositive := by
    unfold minusBorderH4MPositive plusDetBernstein10B1
      plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
      plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B9
    fun_prop
  have hNm : Continuous minusBorderH4MNegative := by
    unfold minusBorderH4MNegative plusDetBernstein10B7
      plusDetBernstein10B8
    fun_prop
  have habs := abs_plusDetCompositeJointError_le_of_signed_splits
    (-(505319 / 480000 : ℝ)) (-(-1427289 / 1120000 : ℝ)) (1 / 2)
    minusBorderH4Q minusBorderH4PPositive minusBorderH4PNegative
    minusBorderH4MPositive minusBorderH4MNegative hq hPp hNp hPm hNm
    (fun t ↦ by
      simpa only [minusBorderCompositeP] using
        (minusBorderH4_jointProfile_splits t).1)
    (fun t ↦ by
      simpa only [minusBorderCompositeM] using
        (minusBorderH4_jointProfile_splits t).2)
    (fun t ht ↦ minusBorderH4_signedProfiles_nonneg ht)
  have habs' :
      |minusBorderCompositeJointError
          (505319 / 480000) (-1427289 / 1120000)
          (1 / 2) minusBorderH4Q| ≤
        ∫ t : ℝ in 0..2,
          plusDetJointAbsoluteMajorant
            (fun s ↦ minusBorderH4PPositive s + minusBorderH4PNegative s)
            (fun s ↦ minusBorderH4MPositive s + minusBorderH4MNegative s) t := by
    unfold minusBorderCompositeJointError
    exact habs
  have hrat := integral_plusDetJointAbsoluteMajorant_le_rational
    (fun s ↦ minusBorderH4PPositive s + minusBorderH4PNegative s)
    (fun s ↦ minusBorderH4MPositive s + minusBorderH4MNegative s)
    (hPp.add hNp) (hPm.add hNm) (fun t ht ↦ by
      have h := minusBorderH4_signedProfiles_nonneg ht
      exact ⟨add_nonneg h.1 h.2.1,
        add_nonneg h.2.2.1 h.2.2.2⟩)
  rw [integral_minusBorderH4_rationalAbsoluteMajorant] at hrat
  exact (habs'.trans hrat).trans_lt (by norm_num)

private theorem abs_minusBorderCompositeCleanTransferH4_lt :
    |minusBorderCompositeCleanTransfer
        (505319 / 480000) (-1427289 / 1120000)| < (1 / 220000 : ℝ) := by
  have h := abs_plusDetCompositeCleanTransfer_lt
    (505319 / 480000) (-1427289 / 1120000) (by norm_num) (by norm_num)
  unfold minusBorderCompositeCleanTransfer
  norm_num at h ⊢
  linarith

/-! ## Exact archimedean evaluation of the complete profile -/

private def minusBorderH4ArchQuotient (t : ℝ) : ℝ :=
  (1385671109 / 2016000 : ℝ) -
    (1385671109 / 4032000) * t +
    (3890701 / 23040) * t ^ 2 -
    (153223653 / 1792000) * t ^ 3 +
    (16317 / 400) * t ^ 4 -
    (52587527 / 4608000) * t ^ 5 +
    (210629 / 358400) * t ^ 7 - (21 / 1024) * t ^ 9

private theorem minusBorderH4ArchDivision
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    t ^ 2 * minusBorderH4Q t / (2 + t) =
      minusBorderH4ArchQuotient t +
        (-1385671109 / 1008000 : ℝ) * (1 / (2 + t)) := by
  have hden : 2 + t ≠ 0 := by linarith [ht.1]
  rw [minusBorderH4Q_polynomial]
  unfold minusBorderH4ArchQuotient
  field_simp [hden]
  ring

private theorem integral_minusBorderH4ArchQuotient :
    (∫ t : ℝ in 0..2, minusBorderH4ArchQuotient t) =
      (3837174433 / 4032000 : ℝ) := by
  unfold minusBorderH4ArchQuotient
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  norm_num

private theorem integral_minusBorderH4Q_moment_one :
    (∫ t : ℝ in 0..2,
      t * intrinsicAlternatingCorrelation minusBorderH4Q t) =
        (-1496717 / 432000 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [minusBorderH4Q_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_minusBorderH4Q_moment_three :
    (∫ t : ℝ in 0..2,
      t ^ 3 * intrinsicAlternatingCorrelation minusBorderH4Q t) =
        (-4618879 / 1512000 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [minusBorderH4Q_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_minusBorderH4Q_moment_five :
    (∫ t : ℝ in 0..2,
      t ^ 5 * intrinsicAlternatingCorrelation minusBorderH4Q t) =
        (-213419519 / 54573750 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [minusBorderH4Q_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem minusBorderH4SharpArchModel_eq :
    intrinsicAlternatingSharpArchModel minusBorderH4Q =
      (3837174433 / 4032000 : ℝ) +
        (-1385671109 / 1008000) * Real.log 2 +
        (-1496717 / 432000) *
          intrinsicAlternatingKernelCoeff1 yoshidaEndpointA +
        (-4618879 / 1512000) *
          intrinsicAlternatingKernelCoeff3 yoshidaEndpointA +
        (-213419519 / 54573750) *
          intrinsicAlternatingKernelCoeff5 yoshidaEndpointA := by
  apply intrinsicAlternatingSharpArchModel_eq_data_plusDet
    minusBorderH4Q minusBorderH4ArchQuotient
    (-1385671109 / 1008000) (3837174433 / 4032000)
    (-1496717 / 432000) (-4618879 / 1512000)
    (-213419519 / 54573750)
  · unfold minusBorderH4Q plusDetAlternatingQ alternatingQ41
      alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  · unfold minusBorderH4ArchQuotient
    fun_prop
  · exact minusBorderH4ArchDivision
  · exact integral_minusBorderH4ArchQuotient
  · exact integral_minusBorderH4Q_moment_one
  · exact integral_minusBorderH4Q_moment_three
  · exact integral_minusBorderH4Q_moment_five

private theorem minusBorderH4SharpArchModel_bounds :
    (-1515316 / 1000000 : ℝ) <
        intrinsicAlternatingSharpArchModel minusBorderH4Q ∧
      intrinsicAlternatingSharpArchModel minusBorderH4Q <
        (-1515315 / 1000000 : ℝ) := by
  rw [minusBorderH4SharpArchModel_eq]
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

private theorem minusBorderCompositePH4_polynomial (t : ℝ) :
    minusBorderCompositeP (505319 / 480000) (-1427289 / 1120000)
        (1 / 2) minusBorderH4Q t =
      (-13788511 / 2240000 : ℝ) * t +
        (63971 / 2880000) * t ^ 2 +
        (49347583 / 40320000) * t ^ 3 +
        (494223713 / 32256000) * t ^ 4 -
        (251040617 / 13440000) * t ^ 5 +
        (443939129 / 64512000) * t ^ 6 -
        (1427289 / 17920000) * t ^ 7 -
        (240029 / 716800) * t ^ 8 + (21 / 2048) * t ^ 10 := by
  rw [(minusBorderH4_jointProfile_splits t).1]
  unfold minusBorderH4PPositive minusBorderH4PNegative
    plusDetBernstein10B1 plusDetBernstein10B2 plusDetBernstein10B3
    plusDetBernstein10B4 plusDetBernstein10B5 plusDetBernstein10B6
    plusDetBernstein10B7 plusDetBernstein10B8 plusDetBernstein10B9
  ring

private theorem minusBorderCompositePH4_tau_bounds :
    (-116547511 / 100000000 : ℝ) <
        minusBorderCompositeP (505319 / 480000) (-1427289 / 1120000)
          (1 / 2) minusBorderH4Q
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      minusBorderCompositeP (505319 / 480000) (-1427289 / 1120000)
          (1 / 2) minusBorderH4Q
          (factorTwoPrimeShift / yoshidaEndpointA) <
        (-116547510 / 100000000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 1169925001 / 1000000000
  have htau := factorTwoPrimeRatio_ultrafine_bounds_plusDet
  have hy0 : 0 < y := by dsimp only [y, tau]; linarith [htau.1]
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
  rw [htauy, minusBorderCompositePH4_polynomial]
  ring_nf
  constructor <;> nlinarith [hy2, hy3, hy4, hy5, hy6, hy7, hy8, hy9,
    hy10, sq_nonneg y, pow_nonneg hy0.le 3, pow_nonneg hy0.le 4,
    pow_nonneg hy0.le 5, pow_nonneg hy0.le 6, pow_nonneg hy0.le 7,
    pow_nonneg hy0.le 8, pow_nonneg hy0.le 9, pow_nonneg hy0.le 10]

private theorem minusBorderCompositeCoreH4_bounds :
    (-52133 / 1000000 : ℝ) <
        minusBorderCompositeCore (30817763257 / 806400000000)
          (505319 / 480000) (-1427289 / 1120000)
          (1 / 2) minusBorderH4Q ∧
      minusBorderCompositeCore (30817763257 / 806400000000)
          (505319 / 480000) (-1427289 / 1120000)
          (1 / 2) minusBorderH4Q < (-52121 / 1000000 : ℝ) := by
  have hR04 := minusBorderCompositeR04_bounds
  have hR24 := minusBorderCompositeR24_bounds
  have harch := minusBorderH4SharpArchModel_bounds
  have hP := minusBorderCompositePH4_tau_bounds
  have hbeta := log_three_div_sqrt_three_fine_bounds_plusDet
  have hnegP :
      (116547510 / 100000000 : ℝ) <
          -minusBorderCompositeP
            (505319 / 480000) (-1427289 / 1120000)
            (1 / 2) minusBorderH4Q
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
        -minusBorderCompositeP
            (505319 / 480000) (-1427289 / 1120000)
            (1 / 2) minusBorderH4Q
            (factorTwoPrimeShift / yoshidaEndpointA) <
          (116547511 / 100000000 : ℝ) := by
    constructor <;> linarith [hP.1, hP.2]
  have hprod := mul_strict_bounds_plusDet hbeta hnegP
    (by norm_num) (by norm_num)
  unfold minusBorderCompositeCore
  constructor <;> nlinarith [hR04.1, hR04.2, hR24.1, hR24.2,
    harch.1, harch.2, hprod.1, hprod.2]

/-- Structural box for the complete negative-border `H4` core. -/
theorem minusDetH4Core_bounds_structural :
    (-6521 / 125000 : ℝ) < minusDetH4Core ∧
      minusDetH4Core < (-26043 / 500000 : ℝ) := by
  have hcore := minusBorderCompositeCoreH4_bounds
  have hclean := abs_lt.mp abs_minusBorderCompositeCleanTransferH4_lt
  have hjoint := abs_lt.mp abs_minusBorderCompositeJointErrorH4_lt
  rw [minusDetH4Core_composite_decomposition]
  constructor <;> nlinarith [hcore.1, hcore.2, hclean.1, hclean.2,
    hjoint.1, hjoint.2]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusBorderH4Structural
