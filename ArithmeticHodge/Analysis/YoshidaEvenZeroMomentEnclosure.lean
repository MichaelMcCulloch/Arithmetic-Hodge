import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets
import ArithmeticHodge.Analysis.YoshidaDiagonalAcceleratedSeries
import ArithmeticHodge.Analysis.YoshidaDiagonalMomentEnclosures

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaEvenZeroMomentEnclosure

noncomputable section

open RatInterval
open YoshidaConstantBounds
open YoshidaDiagonalAcceleratedSeries
open YoshidaDiagonalMomentEnclosures
open YoshidaDiagonalSeriesTail
open YoshidaEvenMomentTargets
open YoshidaMomentSeries
open YoshidaOddCorrelationIntegrability
open YoshidaOddGramPrefix
open YoshidaRenormalizedGeometricKernel
open YoshidaSineMomentEnclosures

/-! ## Fine constants needed by the hundred-thousandth-wide zero-mode box -/

private theorem strict_log_four_hundred_bounds :
    (59914645469 / 10000000000 : ℝ) < Real.log 400 ∧
      Real.log 400 < (59914645474 / 10000000000 : ℝ) := by
  have htwo := strict_log_two_fine_bounds
  have hhundred := strict_log_one_hundred_bounds
  have hid : Real.log (400 : ℝ) = 2 * Real.log 2 + Real.log 100 := by
    calc
      Real.log (400 : ℝ) = Real.log ((2 : ℝ) ^ 2 * 100) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 2) + Real.log 100 := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = 2 * Real.log 2 + Real.log 100 := by
        rw [Real.log_pow]
        norm_num
  rw [hid]
  constructor <;> linarith

set_option maxRecDepth 100000 in
private theorem strict_euler_gamma_fine_bounds :
    (577215 / 1000000 : ℝ) < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < (577216 / 1000000 : ℝ) := by
  have hlower := gammaLowerApprox_le_eulerGamma 399
  have hupper := eulerGamma_le_gammaUpperApprox 399
  have hlog := strict_log_four_hundred_bounds
  constructor
  · apply lt_of_lt_of_le ?_ hlower
    simp only [gammaLowerApprox]
    norm_num [harmonic, Finset.sum_range_succ] at ⊢
    linarith [hlog.2]
  · apply lt_of_le_of_lt hupper
    simp only [gammaUpperApprox, gammaLowerApprox]
    norm_num [harmonic, Finset.sum_range_succ] at ⊢
    linarith [hlog.1]

private theorem log_3141592_million_fine_lower :
    (1144729 / 1000000 : ℝ) < Real.log (3141592 / 1000000 : ℝ) := by
  have h := Real.sum_range_le_log_div (x := (267699 / 517699 : ℝ))
    (by norm_num) (by norm_num) 14
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem log_3141593_million_fine_upper :
    Real.log (3141593 / 1000000 : ℝ) < (1144730 / 1000000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (2141593 / 4141593 : ℝ))
    (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem strict_log_pi_fine_bounds :
    (1144729 / 1000000 : ℝ) < Real.log Real.pi ∧
      Real.log Real.pi < (1144730 / 1000000 : ℝ) := by
  constructor
  · have hpi := Real.pi_gt_d6
    have hlog := log_3141592_million_fine_lower
    norm_num at hpi hlog ⊢
    exact hlog.trans (Real.log_lt_log (by norm_num) hpi)
  · have hpi := Real.pi_lt_d6
    have hlog := log_3141593_million_fine_upper
    norm_num at hpi hlog ⊢
    exact (Real.log_lt_log Real.pi_pos hpi).trans hlog

private def zeroGammaInterval : RatInterval :=
  ⟨577215 / 1000000, 577216 / 1000000⟩

private def zeroLogPiInterval : RatInterval :=
  ⟨1144729 / 1000000, 1144730 / 1000000⟩

private theorem zeroGammaInterval_contains :
    zeroGammaInterval.Contains Real.eulerMascheroniConstant := by
  have h := strict_euler_gamma_fine_bounds
  constructor
  · norm_num [zeroGammaInterval, Contains] at h ⊢
    exact h.1.le
  · norm_num [zeroGammaInterval, Contains] at h ⊢
    exact h.2.le

private theorem zeroLogPiInterval_contains :
    zeroLogPiInterval.Contains (Real.log Real.pi) := by
  have h := strict_log_pi_fine_bounds
  constructor
  · norm_num [zeroLogPiInterval, Contains] at h ⊢
    exact h.1.le
  · norm_num [zeroLogPiInterval, Contains] at h ⊢
    exact h.2.le

private def zeroCorrelation (u : ℝ) : ℝ :=
  1 - u / yoshidaLength

private def zeroRemovableD (_u : ℝ) : ℝ :=
  -1 / yoshidaLength

private theorem continuous_zeroCorrelation : Continuous zeroCorrelation := by
  unfold zeroCorrelation
  fun_prop

private theorem continuous_zeroRemovableD : Continuous zeroRemovableD := by
  unfold zeroRemovableD
  fun_prop

private theorem zeroCorrelation_removable (u : ℝ) :
    zeroCorrelation u = 1 + u * zeroRemovableD u := by
  unfold zeroCorrelation zeroRemovableD
  ring

private theorem zero_pairedIntegralInterchange :
    PairedIntegralInterchange yoshidaLength 1 zeroCorrelation := by
  apply pairedIntegralInterchange_of_removable yoshidaLength_pos
    continuous_zeroCorrelation
  · intro u _hu
    exact zeroCorrelation_removable u
  · exact removableMajorantLimit_intervalIntegrable
      continuous_zeroRemovableD 1 yoshidaLength

private theorem zero_stableGeometricIntegrand_intervalIntegrable :
    IntervalIntegrable (stableGeometricIntegrand 1 zeroCorrelation)
      volume 0 yoshidaLength := by
  exact stableGeometricIntegrand_intervalIntegrable_of_removable
    continuous_zeroRemovableD 1 yoshidaLength zeroCorrelation_removable

private theorem zero_negated_geometric_identity :
    -Real.eulerMascheroniConstant -
        ∑' k : ℕ, renormalizedTerm yoshidaLength 1 zeroCorrelation k =
      (∫ u in 0..yoshidaLength,
        -oddKernel u * zeroCorrelation u + 1 / u) -
        (Real.log yoshidaLength + Real.eulerMascheroniConstant + Real.log 2) := by
  simpa only [mul_one] using
    negated_geometric_identity yoshidaLength_pos continuous_zeroCorrelation
      zero_pairedIntegralInterchange
      zero_stableGeometricIntegrand_intervalIntegrable
      (referenceRegularized_intervalIntegrable yoshidaLength)

private theorem zero_renormalized_hasSum :
    HasSum (renormalizedTerm yoshidaLength 1 zeroCorrelation)
      ((∫ u in 0..yoshidaLength,
          stableGeometricIntegrand 1 zeroCorrelation u) +
        (Real.log yoshidaLength + Real.log 2)) := by
  simpa only [mul_one] using
    renormalizedSeries_hasSum_stable yoshidaLength_pos
      continuous_zeroCorrelation zero_pairedIntegralInterchange
      zero_stableGeometricIntegrand_intervalIntegrable
      (referenceRegularized_intervalIntegrable yoshidaLength)

private def zeroRampPrimitive (a u : ℝ) : ℝ :=
  Real.exp (-a * u) *
    (-1 / a + u / (yoshidaLength * a) + 1 / (yoshidaLength * a ^ 2))

private theorem zeroRampPrimitive_hasDerivAt
    {a u : ℝ} (ha : a ≠ 0) :
    HasDerivAt (zeroRampPrimitive a)
      (Real.exp (-a * u) * (1 - u / yoshidaLength)) u := by
  have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (-a * x))
      (-a * Real.exp (-a * u)) u := by
    convert (Real.hasDerivAt_exp (-a * u)).comp u
      ((hasDerivAt_id u).const_mul (-a)) using 1
    ring
  have hlinear : HasDerivAt
      (fun x : ℝ ↦
        -1 / a + x / (yoshidaLength * a) +
          1 / (yoshidaLength * a ^ 2))
      (1 / (yoshidaLength * a)) u := by
    convert ((hasDerivAt_const u (-1 / a)).add
      ((hasDerivAt_id u).div_const (yoshidaLength * a))).add_const
        (1 / (yoshidaLength * a ^ 2)) using 1
    all_goals ring
  unfold zeroRampPrimitive
  convert hexp.mul hlinear using 1
  field_simp [ha, yoshidaLength_pos.ne']
  ring

private theorem integral_exp_neg_mul_zeroCorrelation_eq_ramp
    {a : ℝ} (ha : a ≠ 0) :
    (∫ u in 0..yoshidaLength,
        Real.exp (-a * u) * zeroCorrelation u) =
      diagonalRampClosed yoshidaLength 0 a
        (Real.exp (-a * yoshidaLength)) := by
  have hint : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-a * u) * zeroCorrelation u)
      volume 0 yoshidaLength :=
    Continuous.intervalIntegrable (by
      unfold zeroCorrelation
      fun_prop) 0 yoshidaLength
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _hu ↦ zeroRampPrimitive_hasDerivAt ha) hint
  change (∫ u in 0..yoshidaLength,
    Real.exp (-a * u) * (1 - u / yoshidaLength)) = _
  rw [hfund]
  unfold zeroRampPrimitive diagonalRampClosed
  simp only [mul_zero, Real.exp_zero, zero_div, sub_zero]
  field_simp [ha, yoshidaLength_pos.ne']
  ring

private theorem zero_polar_integral_eq_ramps :
    (∫ u in 0..yoshidaLength,
      2 * (Real.exp (u / 2) + Real.exp (-u / 2)) * zeroCorrelation u) =
      2 * diagonalRampClosed yoshidaLength 0 (-1 / 2) (Real.sqrt 2) +
        2 * diagonalRampClosed yoshidaLength 0 (1 / 2) (Real.sqrt 2)⁻¹ := by
  have hplus : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (u / 2) * zeroCorrelation u)
      volume 0 yoshidaLength :=
    Continuous.intervalIntegrable (by
      unfold zeroCorrelation
      fun_prop) 0 yoshidaLength
  have hminus : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-u / 2) * zeroCorrelation u)
      volume 0 yoshidaLength :=
    Continuous.intervalIntegrable (by
      unfold zeroCorrelation
      fun_prop) 0 yoshidaLength
  rw [show (fun u : ℝ ↦
      2 * (Real.exp (u / 2) + Real.exp (-u / 2)) * zeroCorrelation u) =
      fun u : ℝ ↦ 2 *
        (Real.exp (u / 2) * zeroCorrelation u +
          Real.exp (-u / 2) * zeroCorrelation u) by
    funext u
    ring]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hplus hminus]
  rw [show (fun u : ℝ ↦ Real.exp (u / 2) * zeroCorrelation u) =
      fun u : ℝ ↦ Real.exp (-(-1 / 2 : ℝ) * u) * zeroCorrelation u by
    funext u
    congr 2
    ring]
  rw [show (fun u : ℝ ↦ Real.exp (-u / 2) * zeroCorrelation u) =
      fun u : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * u) * zeroCorrelation u by
    funext u
    congr 2
    ring]
  rw [integral_exp_neg_mul_zeroCorrelation_eq_ramp (by norm_num : (-1 / 2 : ℝ) ≠ 0),
    integral_exp_neg_mul_zeroCorrelation_eq_ramp (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  rw [show -(-1 / 2 : ℝ) * yoshidaLength = yoshidaLength / 2 by ring,
    show -(1 / 2 : ℝ) * yoshidaLength = -yoshidaLength / 2 by ring,
    exp_yoshidaLength_half, exp_neg_yoshidaLength_half]
  ring

private theorem zero_moment_integrand_ae_identity :
    ∀ᵐ u : ℝ ∂volume,
      yoshidaDiagonalMomentIntegrand 0 u =
        2 * (Real.exp (u / 2) + Real.exp (-u / 2)) * zeroCorrelation u +
          (-oddKernel u * zeroCorrelation u + 1 / u) := by
  filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
    simp [ae_iff, measure_singleton]] with u hu
  rw [yoshidaDiagonalMomentIntegrand, yoshidaWeightPlus, if_neg hu]
  simp only [yoshidaKappa, Nat.cast_zero, mul_zero, zero_div, Real.cos_zero,
    Real.sin_zero, zero_mul]
  unfold yoshidaWeight zeroCorrelation oddKernel
  have hden : Real.exp u - Real.exp (-u) ≠ 0 := by
    intro h
    have heq : Real.exp u = Real.exp (-u) := sub_eq_zero.mp h
    exact hu (by linarith [Real.exp_injective heq])
  field_simp [hu, yoshidaLength_pos.ne', hden]
  norm_num
  ring

private def zeroRawTerm (k : ℕ) : ℝ :=
  2 * diagonalRampClosed yoshidaLength 0 (oddRate k)
      ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) -
    1 / (k + 1 : ℕ)

private theorem renormalizedTerm_zeroCorrelation_eq_raw (k : ℕ) :
    renormalizedTerm yoshidaLength 1 zeroCorrelation k = zeroRawTerm k := by
  rw [renormalizedTerm]
  rw [integral_exp_neg_mul_zeroCorrelation_eq_ramp (oddRate_pos k).ne']
  rw [exp_neg_oddRate_mul_length]
  unfold zeroRawTerm
  push_cast
  ring

private theorem summable_zeroRawTerm : Summable zeroRawTerm := by
  exact zero_renormalized_hasSum.summable.congr
    (fun k ↦ renormalizedTerm_zeroCorrelation_eq_raw k)

private theorem yoshidaDiagonalMoment_zero_eq_rawSeries :
    yoshidaDiagonalMoment 0 =
      2 * diagonalRampClosed yoshidaLength 0 (-1 / 2) (Real.sqrt 2) +
        2 * diagonalRampClosed yoshidaLength 0 (1 / 2) (Real.sqrt 2)⁻¹ -
        Real.eulerMascheroniConstant - Real.log Real.pi -
        ∑' k : ℕ, zeroRawTerm k := by
  let P : ℝ → ℝ := fun u ↦
    2 * (Real.exp (u / 2) + Real.exp (-u / 2)) * zeroCorrelation u
  let N : ℝ → ℝ := fun u ↦
    -oddKernel u * zeroCorrelation u + 1 / u
  have hP : IntervalIntegrable P volume 0 yoshidaLength := by
    exact Continuous.intervalIntegrable (by
      dsimp only [P]
      unfold zeroCorrelation
      fun_prop) 0 yoshidaLength
  have hN : IntervalIntegrable N volume 0 yoshidaLength := by
    have h := zero_stableGeometricIntegrand_intervalIntegrable.neg
    apply h.congr
    intro u _hu
    dsimp only [N]
    simp only [Pi.neg_apply]
    unfold stableGeometricIntegrand
    ring
  have hintegral :
      (∫ u in 0..yoshidaLength, yoshidaDiagonalMomentIntegrand 0 u) =
        (∫ u in 0..yoshidaLength, P u) +
          ∫ u in 0..yoshidaLength, N u := by
    calc
      (∫ u in 0..yoshidaLength, yoshidaDiagonalMomentIntegrand 0 u) =
          ∫ u in 0..yoshidaLength, P u + N u := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [zero_moment_integrand_ae_identity] with u hu
        intro _hu
        simpa only [P, N] using hu
      _ = (∫ u in 0..yoshidaLength, P u) +
          ∫ u in 0..yoshidaLength, N u :=
        intervalIntegral.integral_add hP hN
  have hPvalue :
      (∫ u in 0..yoshidaLength, P u) =
        2 * diagonalRampClosed yoshidaLength 0 (-1 / 2) (Real.sqrt 2) +
          2 * diagonalRampClosed yoshidaLength 0 (1 / 2) (Real.sqrt 2)⁻¹ := by
    simpa only [P] using zero_polar_integral_eq_ramps
  have hNvalue := zero_negated_geometric_identity
  have htsum :
      (∑' k : ℕ, renormalizedTerm yoshidaLength 1 zeroCorrelation k) =
        ∑' k : ℕ, zeroRawTerm k := by
    apply tsum_congr
    exact renormalizedTerm_zeroCorrelation_eq_raw
  rw [htsum] at hNvalue
  rw [yoshidaDiagonalMoment, hintegral, hPvalue]
  linarith

private theorem zeroRawTerm_zero :
    zeroRawTerm 0 =
      2 * diagonalRampClosed yoshidaLength 0 (1 / 2) (Real.sqrt 2)⁻¹ - 1 := by
  unfold zeroRawTerm oddRate
  norm_num

private theorem yoshidaDiagonalMoment_zero_eq_positiveRamp_sub_rawTail :
    yoshidaDiagonalMoment 0 =
      2 * diagonalRampClosed yoshidaLength 0 (-1 / 2) (Real.sqrt 2) + 1 -
        Real.eulerMascheroniConstant - Real.log Real.pi -
        ∑' j : ℕ, zeroRawTerm (j + 1) := by
  have hmain := yoshidaDiagonalMoment_zero_eq_rawSeries
  have hsplit := summable_zeroRawTerm.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  rw [zeroRawTerm_zero] at hsplit
  linarith

private def zeroTelescopingTerm (j : ℕ) : ℝ :=
  1 / (j + 1 : ℕ) - 1 / (j + 2 : ℕ)

private def zeroLogTerm (j : ℕ) : ℝ :=
  (1 / 4 : ℝ) ^ (j + 1) / (j + 1 : ℕ)

private def zeroZetaTwoTerm (j : ℕ) : ℝ :=
  1 / (((j + 1 : ℕ) : ℝ) ^ 2)

private def zeroAccelerationRemainder (j : ℕ) : ℝ :=
  zeroTelescopingTerm j - zeroLogTerm j -
    diagonalAccelerationCoefficient * zeroZetaTwoTerm j

private theorem zeroRaw_succ_eq_accelerated_add_remainder (j : ℕ) :
    zeroRawTerm (j + 1) =
      yoshidaDiagonalDyadicPairedCorrection 0 (j + 1) +
        zeroAccelerationRemainder j := by
  unfold zeroRawTerm yoshidaDiagonalDyadicPairedCorrection
    diagonalDyadicPairedCorrection diagonalPairedCorrection
    zeroAccelerationRemainder zeroTelescopingTerm zeroLogTerm
    zeroZetaTwoTerm diagonalAccelerationCoefficient yoshidaKappa oddRate
  push_cast
  rw [one_div_pow]
  ring

private theorem hasSum_zeroTelescopingTerm :
    HasSum zeroTelescopingTerm 1 := by
  have h := (YoshidaShiftedGeometricSeries.hasSum_harmonicShiftCorrection
    (1 : ℝ)).neg
  convert h using 1
  · funext j
    unfold zeroTelescopingTerm
      YoshidaShiftedGeometricSeries.harmonicShiftCorrection
    push_cast
    ring
  · norm_num

private theorem hasSum_zeroLogTerm :
    HasSum zeroLogTerm (-Real.log (3 / 4)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one
    (x := (1 / 4 : ℝ)) (by norm_num)
  have hfun : zeroLogTerm =
      fun j : ℕ ↦ (1 / 4 : ℝ) ^ (j + 1) / (j + 1) := by
    funext j
    unfold zeroLogTerm
    push_cast
    ring
  rw [hfun]
  convert h using 1
  all_goals norm_num

private theorem hasSum_zeroZetaTwoTerm :
    HasSum zeroZetaTwoTerm (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  convert h using 1
  all_goals norm_num [zeroZetaTwoTerm, Nat.add_comm]

private theorem hasSum_zeroAccelerationRemainder :
    HasSum zeroAccelerationRemainder
      (1 + Real.log (3 / 4) -
        diagonalAccelerationCoefficient * (Real.pi ^ 2 / 6)) := by
  have h := (hasSum_zeroTelescopingTerm.sub hasSum_zeroLogTerm).sub
    (hasSum_zeroZetaTwoTerm.mul_left diagonalAccelerationCoefficient)
  convert h using 1
  all_goals ring

private theorem summable_zeroAcceleratedCorrection :
    Summable (fun j : ℕ ↦
      yoshidaDiagonalDyadicPairedCorrection 0 (j + 1)) := by
  let rawTail : ℕ → ℝ := fun j ↦ zeroRawTerm (j + 1)
  have hraw : Summable rawTail := by
    simpa only [rawTail] using
      (summable_nat_add_iff 1).2 summable_zeroRawTerm
  have hdiff : Summable
      (fun j ↦ rawTail j - zeroAccelerationRemainder j) :=
    hraw.sub hasSum_zeroAccelerationRemainder.summable
  apply hdiff.congr
  intro j
  dsimp only [rawTail]
  rw [zeroRaw_succ_eq_accelerated_add_remainder]
  ring

private theorem tsum_zeroRawTail_eq_accelerated_add_constants :
    (∑' j : ℕ, zeroRawTerm (j + 1)) =
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection 0 (j + 1)) +
        1 + Real.log (3 / 4) -
        diagonalAccelerationCoefficient * (Real.pi ^ 2 / 6) := by
  let rawTail : ℕ → ℝ := fun j ↦ zeroRawTerm (j + 1)
  let R : ℝ := 1 + Real.log (3 / 4) -
    diagonalAccelerationCoefficient * (Real.pi ^ 2 / 6)
  have hraw : Summable rawTail := by
    simpa only [rawTail] using
      (summable_nat_add_iff 1).2 summable_zeroRawTerm
  have hrem : HasSum zeroAccelerationRemainder R := by
    simpa only [R] using hasSum_zeroAccelerationRemainder
  have hcorr0 : HasSum
      (fun j ↦ rawTail j - zeroAccelerationRemainder j)
      ((∑' j : ℕ, rawTail j) - R) := hraw.hasSum.sub hrem
  have hcorr : HasSum
      (fun j : ℕ ↦ yoshidaDiagonalDyadicPairedCorrection 0 (j + 1))
      ((∑' j : ℕ, rawTail j) - R) := by
    have hfun :
        (fun j ↦ rawTail j - zeroAccelerationRemainder j) =
          fun j : ℕ ↦ yoshidaDiagonalDyadicPairedCorrection 0 (j + 1) := by
      funext j
      dsimp only [rawTail]
      rw [zeroRaw_succ_eq_accelerated_add_remainder]
      ring
    rw [hfun] at hcorr0
    exact hcorr0
  have heq := hcorr.tsum_eq
  dsimp only [rawTail, R] at heq
  linarith

private theorem neg_log_three_fourths_eq_log_four_thirds :
    -Real.log (3 / 4) = Real.log (4 / 3) := by
  rw [show (4 / 3 : ℝ) = (3 / 4 : ℝ)⁻¹ by norm_num,
    Real.log_inv]

/-- The zero diagonal moment satisfies the same accelerated identity as the
nonzero modes, now proved directly from the linear zero-mode correlation. -/
theorem yoshidaDiagonalMoment_zero_eq_acceleratedSeries :
    yoshidaDiagonalMoment 0 =
      diagonalAcceleratedBase 0 -
        ∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection 0 (j + 1) := by
  have hmoment := yoshidaDiagonalMoment_zero_eq_positiveRamp_sub_rawTail
  have hseries := tsum_zeroRawTail_eq_accelerated_add_constants
  rw [hseries] at hmoment
  rw [diagonalAcceleratedBase, diagonalAccelerationCoefficient, yoshidaKappa]
  rw [diagonalAccelerationCoefficient] at hmoment
  norm_num only [Nat.cast_zero, mul_zero, zero_div, zero_pow]
  rw [← neg_log_three_fourths_eq_log_four_thirds]
  linarith

/-! ## Fine rational enclosure and kernel checkpoint -/

private def zeroDiagonalBaseInterval : RatInterval :=
  pure 2 * diagonalRampInterval 0 (-1 / 2) sqrtTwoInterval -
      zeroGammaInterval - zeroLogPiInterval + logFourThirdsInterval +
    diagonalAInterval * positiveSquare piFineInterval / pure 6

private theorem zeroDiagonalBaseInterval_contains_acceleratedBase :
    zeroDiagonalBaseInterval.Contains (diagonalAcceleratedBase 0) := by
  rw [← diagonalBaseValue_eq_acceleratedBase]
  have hramp := diagonalRampInterval_contains 0 (-1 / 2) sqrtTwoInterval
    (by norm_num) sqrtTwoInterval_contains
  have hramp' : (diagonalRampInterval 0 (-1 / 2) sqrtTwoInterval).Contains
      (diagonalRampClosed yoshidaLength (yoshidaKappa 0 ^ 2) (-1 / 2 : ℝ)
        (Real.sqrt 2)) := by
    convert hramp using 1
    norm_num
  have htwo : (RatInterval.pure (2 : ℚ)).Contains (2 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hsix : (RatInterval.pure (6 : ℚ)).Contains (6 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hpiSq : (positiveSquare piFineInterval).Contains (Real.pi ^ 2) :=
    positiveSquare_contains (by norm_num [piFineInterval]) piFineInterval_contains
  have htail :
      (diagonalAInterval * positiveSquare piFineInterval /
        RatInterval.pure 6).Contains
        (diagonalAValue * Real.pi ^ 2 / 6) :=
    contains_div_of_pos (by norm_num [RatInterval.pure])
      (contains_mul diagonalAInterval_contains hpiSq) hsix
  unfold zeroDiagonalBaseInterval diagonalBaseValue
  exact contains_add
    (contains_add
      (contains_sub
        (contains_sub (contains_mul htwo hramp') zeroGammaInterval_contains)
        zeroLogPiInterval_contains)
      logFourThirdsInterval_contains)
    htail

private def zeroDiagonalSeriesInterval (N : ℕ) : RatInterval :=
  zeroDiagonalBaseInterval - diagonalHeadInterval 0 (N - 1) +
    diagonalTailInterval 0 N

private def zeroCoarseSeriesInterval
    (N : ℕ) (coarseHead : RatInterval) : RatInterval :=
  zeroDiagonalBaseInterval - coarseHead + diagonalTailInterval 0 N

private theorem zeroCorrection_head_add_tail_eq_tsum
    {N : ℕ} (hN : 1 ≤ N) :
    (∑ j ∈ Finset.range (N - 1),
        yoshidaDiagonalDyadicPairedCorrection 0 (1 + j)) +
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection 0 (N + j)) =
        ∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection 0 (j + 1) := by
  have hsplit :=
    summable_zeroAcceleratedCorrection.sum_add_tsum_nat_add (N - 1)
  have hhead :
      (∑ j ∈ Finset.range (N - 1),
          yoshidaDiagonalDyadicPairedCorrection 0 (1 + j)) =
        ∑ j ∈ Finset.range (N - 1),
          yoshidaDiagonalDyadicPairedCorrection 0 (j + 1) := by
    apply Finset.sum_congr rfl
    intro j _hj
    congr 1
    omega
  have htail :
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection 0 (N + j)) =
        ∑' j : ℕ,
          yoshidaDiagonalDyadicPairedCorrection 0 (j + (N - 1) + 1) := by
    apply tsum_congr
    intro j
    congr 1
    omega
  rw [hhead, htail]
  exact hsplit

private theorem diagonalSeriesInterval_zero_contains
    {N : ℕ} (hN : 16 ≤ N) :
    (zeroDiagonalSeriesInterval N).Contains (yoshidaDiagonalMoment 0) := by
  rw [yoshidaDiagonalMoment_zero_eq_acceleratedSeries]
  rw [← zeroCorrection_head_add_tail_eq_tsum (N := N) (by omega)]
  have hbase := zeroDiagonalBaseInterval_contains_acceleratedBase
  have hhead := diagonalHeadInterval_contains 0 (N - 1)
  have htail := diagonalTailInterval_contains_neg_tsum
    (n := 0) (N := N) hN (by omega)
  unfold zeroDiagonalSeriesInterval
  have hcombine := contains_add (contains_sub hbase hhead) htail
  convert hcombine using 1
  all_goals ring

private def zeroModeChunkBox : ℕ → RatInterval
  | 0 => ⟨760824096 / 1000000000, 760824097 / 1000000000⟩
  | 1 => ⟨2407 / 1000000000, 2408 / 1000000000⟩
  | 2 => ⟨447 / 1000000000, 448 / 1000000000⟩
  | 3 => ⟨156 / 1000000000, 157 / 1000000000⟩
  | _ => pure 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem zeroModeChunk_kernel_certificate
    {i : ℕ} (hi : i < 4) :
    IsSubinterval (scheduledChunkInterval 0 4 i) (zeroModeChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
private theorem zeroModeCoarseSeries_kernel_certificate :
    IsSubinterval
      (zeroCoarseSeriesInterval 1024
        (coarseCheckpointHead zeroModeChunkBox 4))
      ⟨18338 / 100000, 18339 / 100000⟩ := by
  decide +kernel

private theorem zeroDiagonalSeriesInterval_sub_coarse
    {N : ℕ} {coarseHead : RatInterval}
    (hhead : IsSubinterval (diagonalHeadInterval 0 (N - 1)) coarseHead) :
    IsSubinterval (zeroDiagonalSeriesInterval N)
      (zeroCoarseSeriesInterval N coarseHead) := by
  exact isSubinterval_add
    (isSubinterval_sub_right zeroDiagonalBaseInterval hhead)
    (isSubinterval_refl _)

private theorem zeroMode_diagonal_certificate :
    IsSubinterval (zeroDiagonalSeriesInterval 1024)
      ⟨18338 / 100000, 18339 / 100000⟩ := by
  apply isSubinterval_trans
    (zeroDiagonalSeriesInterval_sub_coarse
      (diagonalHeadInterval_sub_coarseCheckpoint 0 4 (by norm_num)
        zeroModeChunkBox (fun _ hi ↦ zeroModeChunk_kernel_certificate hi)))
  exact zeroModeCoarseSeries_kernel_certificate

/-- The exact candidate box for the normalized even zero mode contains the
actual analytic diagonal moment. -/
theorem yoshidaEvenDiagonalTarget_zero_contains :
    (yoshidaEvenDiagonalTargets 0).Contains (yoshidaDiagonalMoment 0) := by
  have hseries := diagonalSeriesInterval_zero_contains
    (N := 1024) (by norm_num)
  have htarget :
      (⟨18338 / 100000, 18339 / 100000⟩ : RatInterval).Contains
        (yoshidaDiagonalMoment 0) :=
    contains_of_subinterval zeroMode_diagonal_certificate hseries
  change (⟨18338 / 100000, 18339 / 100000⟩ : RatInterval).Contains
    (yoshidaDiagonalMoment 0)
  exact htarget

end

end ArithmeticHodge.Analysis.YoshidaEvenZeroMomentEnclosure
