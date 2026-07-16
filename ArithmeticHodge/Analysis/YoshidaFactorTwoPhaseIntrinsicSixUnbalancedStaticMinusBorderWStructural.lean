import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusBorderKernelStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusDeterminantStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusBorderWStructural

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
open YoshidaFactorTwoPhaseIntrinsicOddP5CombinedPositiveProfileStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingCorrelations
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedAlternatingModelsStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusBorderKernelStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

/-!
# The completed negative-border `W` profile

The final diagonal is the tight row.  Its negative even correlation and
alternating correlation are retained as one signed kernel integral; the
positive-endpoint odd `P5` tail is handled separately by its global
whole-profile theorem.
-/

def minusBorderQW : ℝ → ℝ :=
  plusDetAlternatingQ (-47 / 180) (43 / 80) (-4129 / 11200)
    (44161 / 40320) (-15 / 8) 1

theorem minusBorderQW_polynomial (t : ℝ) :
    minusBorderQW t =
      (-7204497499 / 4064256000 : ℝ) -
        (201227653 / 225792000) * t +
        (11401716197 / 2709504000) * t ^ 2 -
        (282208729 / 774144000) * t ^ 3 -
        (3465875929 / 1548288000) * t ^ 4 +
        (1601947 / 2867200) * t ^ 5 +
        (1601947 / 5734400) * t ^ 6 -
        (4129 / 102400) * t ^ 7 -
        (4129 / 204800) * t ^ 8 := by
  unfold minusBorderQW plusDetAlternatingQ alternatingQ41 alternatingQ43
    alternatingQ05 alternatingQ25 alternatingQ45
  ring

private theorem minusBorderW_coupling_eq_sharpModel :
    factorTwoCenteredAlternatingCoupling
        (plusDetAlternatingEvenProfile
          (-47 / 180) (43 / 80) (-4129 / 11200))
        (plusDetAlternatingOddProfile
          (44161 / 40320) (-15 / 8) 1) =
      plusDetAlternatingSharpModel minusBorderQW := by
  simpa only [minusBorderQW, plusDetAlternatingSharpModel] using
    plusDetAlternatingCoupling_profile_eq_sharpModel
      (-47 / 180) (43 / 80) (-4129 / 11200)
      (44161 / 40320) (-15 / 8) 1

theorem minusDetWCore_eq_composite :
    minusDetWCore =
      minusBorderCompositeCore
          (118454644412291 / 406425600000000)
          (194063 / 1008000) (-177547 / 448000) 1 minusBorderQW +
        minusBorderCompositeCleanTransfer
          (194063 / 1008000) (-177547 / 448000) +
        minusBorderCompositeJointError
          (194063 / 1008000) (-177547 / 448000) 1 minusBorderQW := by
  calc
    minusDetWCore =
        (118454644412291 / 406425600000000 : ℝ) +
          (194063 / 1008000) * factorTwoIntrinsicFourP45Cross04 (-1) +
          (-177547 / 448000) * factorTwoIntrinsicFourP45Cross24 (-1) +
          factorTwoCenteredAlternatingCoupling
            (plusDetAlternatingEvenProfile
              (-47 / 180) (43 / 80) (-4129 / 11200))
            (plusDetAlternatingOddProfile
              (44161 / 40320) (-15 / 8) 1) := by
      rw [plusDetAlternatingCoupling_profile_expansion]
      unfold minusDetWCore minusDetW minusP5OddPositiveTail
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
    _ = (118454644412291 / 406425600000000 : ℝ) +
          (194063 / 1008000) * factorTwoIntrinsicFourP45Cross04 (-1) +
          (-177547 / 448000) * factorTwoIntrinsicFourP45Cross24 (-1) +
          plusDetAlternatingSharpModel minusBorderQW := by
      rw [minusBorderW_coupling_eq_sharpModel]
    _ = _ := by
      simpa only [one_mul] using
        minusBorderCompositeSharp_decomposition
          (118454644412291 / 406425600000000)
          (194063 / 1008000) (-177547 / 448000) 1 minusBorderQW

/-! ## Degree-ten signed Bernstein split -/

private def minusBorderWPPositive (t : ℝ) : ℝ :=
  (2069766113 / 6401203200 : ℝ) * plusDetBernstein10B5 t +
    (432302333 / 1066867200) * plusDetBernstein10B6 t +
    (50100971 / 22861440000) * plusDetBernstein10B8 t +
    (331520003 / 10160640000) * plusDetBernstein10B9 t

private def minusBorderWPNegative (t : ℝ) : ℝ :=
  (7618619683 / 10160640000 : ℝ) * plusDetBernstein10B1 t +
    (2388646889 / 1632960000) * plusDetBernstein10B2 t +
    (91529704961 / 60963840000) * plusDetBernstein10B3 t +
    (14263691093 / 21337344000) * plusDetBernstein10B4 t +
    (18189565739 / 60963840000) * plusDetBernstein10B7 t

private def minusBorderWMPositive (t : ℝ) : ℝ :=
  (1358075063 / 2032128000 : ℝ) * plusDetBernstein10B1 t +
    (2245651361 / 1632960000) * plusDetBernstein10B2 t +
    (18499059277 / 12192768000) * plusDetBernstein10B3 t +
    (85652493673 / 106686720000) * plusDetBernstein10B4 t +
    (10781148779 / 60963840000) * plusDetBernstein10B7 t +
    (99344873 / 2032128000) * plusDetBernstein10B9 t

private def minusBorderWMNegative (t : ℝ) : ℝ :=
  (5516711413 / 32006016000 : ℝ) * plusDetBernstein10B5 t +
    (9961625321 / 26671680000) * plusDetBernstein10B6 t +
    (2880282731 / 22861440000) * plusDetBernstein10B8 t

private theorem minusBorderW_jointProfile_splits (t : ℝ) :
    minusBorderCompositeP
        (194063 / 1008000) (-177547 / 448000) 1 minusBorderQW t =
      minusBorderWPPositive t - minusBorderWPNegative t ∧
    minusBorderCompositeM
        (194063 / 1008000) (-177547 / 448000) 1 minusBorderQW t =
      minusBorderWMPositive t - minusBorderWMNegative t := by
  constructor
  · unfold minusBorderCompositeP plusDetCompositeP plusDetCompositeCe
      plusDetCompositeCa intrinsicAlternatingCorrelation
    rw [minusBorderQW_polynomial]
    unfold factorTwoIntrinsicP4Correlation04 factorTwoIntrinsicP4Correlation24
      minusBorderWPPositive minusBorderWPNegative plusDetBernstein10B1
      plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
      plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B7
      plusDetBernstein10B8 plusDetBernstein10B9
    ring
  · unfold minusBorderCompositeM plusDetCompositeM plusDetCompositeCe
      plusDetCompositeCa intrinsicAlternatingCorrelation
    rw [minusBorderQW_polynomial]
    unfold factorTwoIntrinsicP4Correlation04 factorTwoIntrinsicP4Correlation24
      minusBorderWMPositive minusBorderWMNegative plusDetBernstein10B1
      plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
      plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B7
      plusDetBernstein10B8 plusDetBernstein10B9
    ring

private theorem minusBorderW_signedProfiles_nonneg
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    0 ≤ minusBorderWPPositive t ∧ 0 ≤ minusBorderWPNegative t ∧
      0 ≤ minusBorderWMPositive t ∧ 0 ≤ minusBorderWMNegative t := by
  have hx0 : 0 ≤ t / 2 := by linarith [ht.1]
  have hx1 : 0 ≤ 1 - t / 2 := by linarith [ht.2]
  unfold minusBorderWPPositive minusBorderWPNegative minusBorderWMPositive
    minusBorderWMNegative plusDetBernstein10B1 plusDetBernstein10B2
    plusDetBernstein10B3 plusDetBernstein10B4 plusDetBernstein10B5
    plusDetBernstein10B6 plusDetBernstein10B7 plusDetBernstein10B8
    plusDetBernstein10B9
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

set_option maxHeartbeats 4000000 in
private theorem integral_minusBorderW_rationalSignedCost :
    (∫ t : ℝ in 0..2,
      plusDetJointRationalSignedCost minusBorderWPPositive
        minusBorderWPNegative minusBorderWMPositive minusBorderWMNegative t) =
      (585410045620575722092301339042923405944860934608742076924873 /
        138190780386039693312000000000000000000000000000000000000000000000 : ℝ) := by
  unfold plusDetJointRationalSignedCost plusDetJointRationalA
    minusBorderWPPositive minusBorderWPNegative minusBorderWMPositive
    minusBorderWMNegative plusDetBernstein10B1 plusDetBernstein10B2
    plusDetBernstein10B3 plusDetBernstein10B4 plusDetBernstein10B5
    plusDetBernstein10B6 plusDetBernstein10B7 plusDetBernstein10B8
    plusDetBernstein10B9
  simp_rw [jointRegularEnvelope_expansion_plusDet]
  unfold jointCoshEnvelope
  ring_nf
  repeat' rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

private theorem minusBorderCompositeJointErrorW_gt :
    (-1 / 236000 : ℝ) <
      minusBorderCompositeJointError
        (194063 / 1008000) (-177547 / 448000) 1 minusBorderQW := by
  have hq : Continuous minusBorderQW := by
    unfold minusBorderQW plusDetAlternatingQ alternatingQ41 alternatingQ43
      alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  have hPp : Continuous minusBorderWPPositive := by
    unfold minusBorderWPPositive plusDetBernstein10B5 plusDetBernstein10B6
      plusDetBernstein10B8 plusDetBernstein10B9
    fun_prop
  have hNp : Continuous minusBorderWPNegative := by
    unfold minusBorderWPNegative plusDetBernstein10B1 plusDetBernstein10B2
      plusDetBernstein10B3 plusDetBernstein10B4 plusDetBernstein10B7
    fun_prop
  have hPm : Continuous minusBorderWMPositive := by
    unfold minusBorderWMPositive plusDetBernstein10B1 plusDetBernstein10B2
      plusDetBernstein10B3 plusDetBernstein10B4 plusDetBernstein10B7
      plusDetBernstein10B9
    fun_prop
  have hNm : Continuous minusBorderWMNegative := by
    unfold minusBorderWMNegative plusDetBernstein10B5 plusDetBernstein10B6
      plusDetBernstein10B8
    fun_prop
  have hlower := plusDetCompositeJointError_lower_of_signed_splits
    (-(194063 / 1008000 : ℝ)) (-(-177547 / 448000 : ℝ)) 1
    minusBorderQW minusBorderWPPositive minusBorderWPNegative
    minusBorderWMPositive minusBorderWMNegative hq hPp hNp hPm hNm
    (fun t ↦ (minusBorderW_jointProfile_splits t).1)
    (fun t ↦ (minusBorderW_jointProfile_splits t).2)
    (fun t ht ↦ minusBorderW_signedProfiles_nonneg ht)
  have hrat := integral_plusDetJointSignedCost_le_rational
    minusBorderWPPositive minusBorderWPNegative
    minusBorderWMPositive minusBorderWMNegative hPp hNp hPm hNm
    (fun t ht ↦ minusBorderW_signedProfiles_nonneg ht)
  have hneg := (neg_le_neg hrat).trans hlower
  have hcert :
      (∫ t : ℝ in 0..2,
        plusDetJointRationalSignedCost minusBorderWPPositive
          minusBorderWPNegative minusBorderWMPositive minusBorderWMNegative t) <
        (1 / 236000 : ℝ) := by
    rw [integral_minusBorderW_rationalSignedCost]
    norm_num
  unfold minusBorderCompositeJointError
  rw [show (-1 / 236000 : ℝ) = -(1 / 236000) by ring]
  exact (neg_lt_neg hcert).trans_le hneg

private theorem abs_minusBorderCompositeCleanTransferW_lt :
    |minusBorderCompositeCleanTransfer
        (194063 / 1008000) (-177547 / 448000)| < (1 / 980000 : ℝ) := by
  have h := abs_plusDetCompositeCleanTransfer_lt
    (194063 / 1008000) (-177547 / 448000) (by norm_num) (by norm_num)
  unfold minusBorderCompositeCleanTransfer
  norm_num at h ⊢
  linarith

/-! ## Exact archimedean evaluation -/

private def minusBorderWArchQuotient (t : ℝ) : ℝ :=
  (65264027209 / 2032128000 : ℝ) -
    (65264027209 / 4064256000) * t +
    (276473951 / 38707200) * t ^ 2 -
    (10883954203 / 2709504000) * t ^ 3 +
    (329 / 80) * t ^ 4 -
    (3465875929 / 1548288000) * t ^ 5 +
    (1601947 / 5734400) * t ^ 7 -
    (4129 / 204800) * t ^ 9

private theorem minusBorderW_archDivision
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    t ^ 2 * minusBorderQW t / (2 + t) =
      minusBorderWArchQuotient t +
        (-65264027209 / 1016064000 : ℝ) * (1 / (2 + t)) := by
  have hden : 2 + t ≠ 0 := by linarith [ht.1]
  rw [minusBorderQW_polynomial]
  unfold minusBorderWArchQuotient
  field_simp [hden]
  ring

private theorem integral_minusBorderWArchQuotient :
    (∫ t : ℝ in 0..2, minusBorderWArchQuotient t) =
      (15042102403 / 338688000 : ℝ) := by
  unfold minusBorderWArchQuotient
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  norm_num

private theorem integral_minusBorderQW_moment_one :
    (∫ t : ℝ in 0..2,
      t * intrinsicAlternatingCorrelation minusBorderQW t) =
        (-2075567 / 5443200 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [minusBorderQW_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_minusBorderQW_moment_three :
    (∫ t : ℝ in 0..2,
      t ^ 3 * intrinsicAlternatingCorrelation minusBorderQW t) =
        (-2005513 / 10886400 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [minusBorderQW_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_minusBorderQW_moment_five :
    (∫ t : ℝ in 0..2,
      t ^ 5 * intrinsicAlternatingCorrelation minusBorderQW t) =
        (-3552489683 / 29338848000 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [minusBorderQW_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem minusBorderW_sharpArchModel_eq :
    intrinsicAlternatingSharpArchModel minusBorderQW =
      (15042102403 / 338688000 : ℝ) +
        (-65264027209 / 1016064000) * Real.log 2 +
        (-2075567 / 5443200) *
          intrinsicAlternatingKernelCoeff1 yoshidaEndpointA +
        (-2005513 / 10886400) *
          intrinsicAlternatingKernelCoeff3 yoshidaEndpointA +
        (-3552489683 / 29338848000) *
          intrinsicAlternatingKernelCoeff5 yoshidaEndpointA := by
  apply intrinsicAlternatingSharpArchModel_eq_data_plusDet
    minusBorderQW minusBorderWArchQuotient
    (-65264027209 / 1016064000) (15042102403 / 338688000)
    (-2075567 / 5443200) (-2005513 / 10886400)
    (-3552489683 / 29338848000)
  · unfold minusBorderQW plusDetAlternatingQ alternatingQ41 alternatingQ43
      alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  · unfold minusBorderWArchQuotient
    fun_prop
  · exact minusBorderW_archDivision
  · exact integral_minusBorderWArchQuotient
  · exact integral_minusBorderQW_moment_one
  · exact integral_minusBorderQW_moment_three
  · exact integral_minusBorderQW_moment_five

private theorem minusBorderW_sharpArchModel_bounds :
    (-147367 / 1000000 : ℝ) <
        intrinsicAlternatingSharpArchModel minusBorderQW ∧
      intrinsicAlternatingSharpArchModel minusBorderQW <
        (-147366 / 1000000 : ℝ) := by
  rw [minusBorderW_sharpArchModel_eq]
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

/-! ## Retained-prime evaluation and the completed core -/

private theorem minusBorderCompositePW_polynomial (t : ℝ) :
    minusBorderCompositeP
        (194063 / 1008000) (-177547 / 448000) 1 minusBorderQW t =
      (-7618619683 / 2032128000 : ℝ) * t +
        (337092851 / 812851200) * t ^ 2 +
        (264378179 / 27648000) * t ^ 3 -
        (260989303 / 45158400) * t ^ 4 -
        (119229421 / 32256000) * t ^ 5 +
        (5195978689 / 1548288000) * t ^ 6 -
        (177547 / 7168000) * t ^ 7 -
        (412879 / 1146880) * t ^ 8 +
        (4129 / 204800) * t ^ 10 := by
  rw [(minusBorderW_jointProfile_splits t).1]
  unfold minusBorderWPPositive minusBorderWPNegative plusDetBernstein10B1
    plusDetBernstein10B2 plusDetBernstein10B3 plusDetBernstein10B4
    plusDetBernstein10B5 plusDetBernstein10B6 plusDetBernstein10B7
    plusDetBernstein10B8 plusDetBernstein10B9
  ring

private theorem minusBorderCompositePW_tau_bounds :
    (-7073054 / 100000000 : ℝ) <
        minusBorderCompositeP
          (194063 / 1008000) (-177547 / 448000) 1 minusBorderQW
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      minusBorderCompositeP
          (194063 / 1008000) (-177547 / 448000) 1 minusBorderQW
          (factorTwoPrimeShift / yoshidaEndpointA) <
        (-7073053 / 100000000 : ℝ) := by
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
  rw [htauy, minusBorderCompositePW_polynomial]
  ring_nf
  constructor <;> nlinarith [hy2, hy3, hy4, hy5, hy6, hy7, hy8, hy9,
    hy10, sq_nonneg y, pow_nonneg hy0.le 3, pow_nonneg hy0.le 4,
    pow_nonneg hy0.le 5, pow_nonneg hy0.le 6, pow_nonneg hy0.le 7,
    pow_nonneg hy0.le 8, pow_nonneg hy0.le 9, pow_nonneg hy0.le 10]

private theorem minusBorderCompositeCoreW_lower :
    (1463627 / 10000000 : ℝ) <
      minusBorderCompositeCore
        (118454644412291 / 406425600000000)
        (194063 / 1008000) (-177547 / 448000) 1 minusBorderQW := by
  have hR04 := minusBorderCompositeR04_bounds
  have hR24 := minusBorderCompositeR24_bounds
  have harch := minusBorderW_sharpArchModel_bounds
  have hP := minusBorderCompositePW_tau_bounds
  have hbeta := log_three_div_sqrt_three_fine_bounds_plusDet
  have hnegP :
      (7073053 / 100000000 : ℝ) <
          -minusBorderCompositeP
            (194063 / 1008000) (-177547 / 448000) 1 minusBorderQW
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
        -minusBorderCompositeP
            (194063 / 1008000) (-177547 / 448000) 1 minusBorderQW
            (factorTwoPrimeShift / yoshidaEndpointA) <
          (7073054 / 100000000 : ℝ) := by
    constructor <;> linarith [hP.1, hP.2]
  have hprod := mul_strict_bounds_plusDet hbeta hnegP
    (by norm_num) (by norm_num)
  unfold minusBorderCompositeCore
  nlinarith [hR04.1, hR04.2, hR24.1, hR24.2,
    harch.1, harch.2, hprod.1, hprod.2]

/-- Structural lower box for the complete negative-endpoint `W` core. -/
theorem minusDetWCore_lower_structural :
    (146357 / 1000000 : ℝ) < minusDetWCore := by
  have hcore := minusBorderCompositeCoreW_lower
  have hclean := (abs_lt.mp abs_minusBorderCompositeCleanTransferW_lt).1
  have hjoint := minusBorderCompositeJointErrorW_gt
  rw [minusDetWCore_eq_composite]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusBorderWStructural
