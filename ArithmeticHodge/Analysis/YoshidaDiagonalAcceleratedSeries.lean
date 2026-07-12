import ArithmeticHodge.Analysis.YoshidaDiagonalMomentSeries
import ArithmeticHodge.Analysis.YoshidaDiagonalSeriesTail
import ArithmeticHodge.Analysis.YoshidaOddRealSpaceAssembly
import Mathlib.NumberTheory.ZetaValues

set_option autoImplicit false

open MeasureTheory Real
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaDiagonalAcceleratedSeries

noncomputable section

open YoshidaClippedMomentBridge
open YoshidaDiagonalMomentSeries
open YoshidaDiagonalSeriesTail
open YoshidaMomentIntegrability
open YoshidaMomentSeries
open YoshidaOddCorrelationIntegrability
open YoshidaOddGramPrefix
open YoshidaOddRealSpaceAssembly
open YoshidaRenormalizedGeometricKernel
open YoshidaShiftedGeometricSeries

/-!
# Exact accelerated series for Yoshida's diagonal moments

This module cancels the negative-polar k = 0 term, reindexes the remaining
raw diagonal series at k = j + 1, and removes its harmonic, dyadic-logarithmic,
and zeta-two asymptotes. The result is an absolutely summable accelerated
correction series with a closed elementary base.
-/

private def diagonalDyadicRawTerm (n k : ℕ) : ℝ :=
  2 * diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
      (2 * k + 1 / 2) ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) -
    1 / (k + 1 : ℕ)

def diagonalAccelerationCoefficient : ℝ :=
  1 / (2 * yoshidaLength) + 1 / 4

/-- The accelerated Yoshida diagonal correction, indexed from `j = 0` by
the positive series index `k = j + 1`. -/
def diagonalAcceleratedCorrection (n j : ℕ) : ℝ :=
  yoshidaDiagonalDyadicPairedCorrection n (j + 1)

private def rampCosPrimitive (b κ L u : ℝ) : ℝ :=
  (1 - u / L) * Real.exp (b * u) *
      (b * Real.cos (κ * u) + κ * Real.sin (κ * u)) /
        (b ^ 2 + κ ^ 2) +
    Real.exp (b * u) *
      ((b ^ 2 - κ ^ 2) * Real.cos (κ * u) +
        2 * b * κ * Real.sin (κ * u)) /
      (L * (b ^ 2 + κ ^ 2) ^ 2)

private theorem rampCosPrimitive_hasDerivAt
    {b κ L u : ℝ} (hL : L ≠ 0) (hden : b ^ 2 + κ ^ 2 ≠ 0) :
    HasDerivAt (rampCosPrimitive b κ L)
      (Real.exp (b * u) * (1 - u / L) * Real.cos (κ * u)) u := by
  have hbu : HasDerivAt (fun x : ℝ ↦ b * x) b u := by
    simpa using (hasDerivAt_id u).const_mul b
  have hku : HasDerivAt (fun x : ℝ ↦ κ * x) κ u := by
    simpa using (hasDerivAt_id u).const_mul κ
  have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (b * x))
      (Real.exp (b * u) * b) u :=
    Real.hasDerivAt_exp (b * u) |>.comp u hbu
  have hsin : HasDerivAt (fun x : ℝ ↦ Real.sin (κ * x))
      (Real.cos (κ * u) * κ) u :=
    Real.hasDerivAt_sin (κ * u) |>.comp u hku
  have hcos : HasDerivAt (fun x : ℝ ↦ Real.cos (κ * x))
      (-Real.sin (κ * u) * κ) u := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_cos (κ * u) |>.comp u hku)
  have hramp : HasDerivAt (fun x : ℝ ↦ 1 - x / L) (-(1 / L)) u := by
    simpa only [zero_sub] using
      (hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).div_const L)
  have hacos : HasDerivAt
      (fun x : ℝ ↦ b * Real.cos (κ * x) + κ * Real.sin (κ * x))
      (b * (-Real.sin (κ * u) * κ) + κ * (Real.cos (κ * u) * κ)) u :=
    (hcos.const_mul b).add (hsin.const_mul κ)
  have hg : HasDerivAt
      (fun x : ℝ ↦ (b ^ 2 - κ ^ 2) * Real.cos (κ * x) +
        2 * b * κ * Real.sin (κ * x))
      ((b ^ 2 - κ ^ 2) * (-Real.sin (κ * u) * κ) +
        2 * b * κ * (Real.cos (κ * u) * κ)) u :=
    (hcos.const_mul (b ^ 2 - κ ^ 2)).add (hsin.const_mul (2 * b * κ))
  convert ((((hramp.mul hexp).mul hacos).div_const (b ^ 2 + κ ^ 2)).add
    ((hexp.mul hg).div_const (L * (b ^ 2 + κ ^ 2) ^ 2))) using 1
  simp only [Pi.mul_apply]
  field_simp [hL, hden]
  ring

private theorem integral_exp_mul_ramp_cos_periodic
    {b κ L : ℝ} (hL : L ≠ 0) (hden : b ^ 2 + κ ^ 2 ≠ 0)
    (hsin : Real.sin (κ * L) = 0)
    (hcos : Real.cos (κ * L) = 1) :
    (∫ u in 0..L,
        Real.exp (b * u) * (1 - u / L) * Real.cos (κ * u)) =
      ((Real.exp (b * L) - 1 - b * L) * (b ^ 2 - κ ^ 2) -
          2 * b * κ ^ 2 * L) /
        (L * (b ^ 2 + κ ^ 2) ^ 2) := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (rampCosPrimitive b κ L)
        (Real.exp (b * u) * (1 - u / L) * Real.cos (κ * u)) u :=
    fun u _ ↦ rampCosPrimitive_hasDerivAt hL hden
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) 0 L)
  rw [h]
  simp only [rampCosPrimitive, mul_zero, zero_div, sub_zero, Real.exp_zero,
    Real.sin_zero, Real.cos_zero, hsin, hcos]
  field_simp [hL, hden]
  ring

private theorem integral_exp_neg_mul_yoshidaRamp_eq_closed
    {n : ℕ} (hn : n ≠ 0) (a : ℝ) :
    (∫ u in 0..yoshidaLength,
      Real.exp (-a * u) * (1 - u / yoshidaLength) *
        Real.cos (yoshidaKappa n * u)) =
      diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2) a
        (Real.exp (-a * yoshidaLength)) := by
  have hden : (-a) ^ 2 + yoshidaKappa n ^ 2 ≠ 0 := by
    have hk := YoshidaOddCorrelationIntegrability.yoshidaKappa_ne_zero hn
    positivity
  have h := integral_exp_mul_ramp_cos_periodic yoshidaLength_pos.ne' hden
    (yoshida_sin_endpoint n) (yoshida_cos_endpoint n)
    (b := -a)
  rw [diagonalRampClosed]
  convert h using 1
  all_goals ring

private theorem integral_exp_neg_mul_fullDiagonal_eq_ramp_add_sine
    {n : ℕ} (hn : n ≠ 0) (a : ℝ) :
    (∫ u in 0..yoshidaLength,
      Real.exp (-a * u) *
        clippedOddCorrelation yoshidaHalfLength n n u) =
      diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2) a
          (Real.exp (-a * yoshidaLength)) +
        (1 - Real.exp (-a * yoshidaLength)) /
          (yoshidaLength * (a ^ 2 + yoshidaKappa n ^ 2)) := by
  have hk : yoshidaKappa n ≠ 0 :=
    YoshidaOddCorrelationIntegrability.yoshidaKappa_ne_zero hn
  have hden : a ^ 2 + yoshidaKappa n ^ 2 ≠ 0 := by positivity
  have hramp : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-a * u) * (1 - u / yoshidaLength) *
        Real.cos (yoshidaKappa n * u)) volume 0 yoshidaLength :=
    Continuous.intervalIntegrable (by fun_prop) 0 yoshidaLength
  have hsine : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-a * u) * Real.sin (yoshidaKappa n * u) /
        (yoshidaLength * yoshidaKappa n)) volume 0 yoshidaLength :=
    (Continuous.intervalIntegrable (by fun_prop) 0 yoshidaLength).div_const _
  rw [show (fun u : ℝ ↦ Real.exp (-a * u) *
      clippedOddCorrelation yoshidaHalfLength n n u) =
      fun u : ℝ ↦
        Real.exp (-a * u) * (1 - u / yoshidaLength) *
            Real.cos (yoshidaKappa n * u) +
          Real.exp (-a * u) * Real.sin (yoshidaKappa n * u) /
            (yoshidaLength * yoshidaKappa n) by
    funext u
    rw [clippedOddCorrelation_half_diag hn]
    field_simp [yoshidaLength_pos.ne', hk]]
  rw [intervalIntegral.integral_add hramp hsine,
    integral_exp_neg_mul_yoshidaRamp_eq_closed hn a]
  rw [show (∫ u in 0..yoshidaLength,
      Real.exp (-a * u) * Real.sin (yoshidaKappa n * u) /
        (yoshidaLength * yoshidaKappa n)) =
      (∫ u in 0..yoshidaLength,
        Real.exp (-a * u) * Real.sin (yoshidaKappa n * u)) /
          (yoshidaLength * yoshidaKappa n) by
    rw [intervalIntegral.integral_div]]
  rw [YoshidaMomentSeries.integral_exp_neg_mul_sin hden
    (yoshida_sin_endpoint n) (yoshida_cos_endpoint n)]
  field_simp [yoshidaLength_pos.ne', hk, hden]

private theorem oddRealPolar_sub_scaled_sinePolar_eq_closedRamps
    {n : ℕ} (hn : n ≠ 0) :
    oddRealPolarCorrelationValue n n -
        sinePolarValue n / (yoshidaLength * yoshidaKappa n) =
      2 * diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
          (-1 / 2) (Real.sqrt 2) +
        2 * diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
          (1 / 2) (Real.sqrt 2)⁻¹ := by
  have hk : yoshidaKappa n ≠ 0 :=
    YoshidaOddCorrelationIntegrability.yoshidaKappa_ne_zero hn
  have hC : Continuous (clippedOddCorrelation yoshidaHalfLength n n) :=
    continuous_clippedOddCorrelation_diag hn
  have hplus : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (u / 2) *
        clippedOddCorrelation yoshidaHalfLength n n u)
      volume 0 yoshidaLength :=
    Continuous.intervalIntegrable (by fun_prop) 0 yoshidaLength
  have hminus : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-u / 2) *
        clippedOddCorrelation yoshidaHalfLength n n u)
      volume 0 yoshidaLength :=
    Continuous.intervalIntegrable (by fun_prop) 0 yoshidaLength
  rw [oddRealPolarCorrelationValue]
  rw [show (fun u : ℝ ↦
      (Real.exp (u / 2) + Real.exp (-u / 2)) *
        clippedOddCorrelation yoshidaHalfLength n n u) =
      fun u : ℝ ↦
        Real.exp (u / 2) * clippedOddCorrelation yoshidaHalfLength n n u +
        Real.exp (-u / 2) * clippedOddCorrelation yoshidaHalfLength n n u by
    funext u
    ring]
  rw [intervalIntegral.integral_add hplus hminus]
  rw [show (fun u : ℝ ↦ Real.exp (u / 2) *
      clippedOddCorrelation yoshidaHalfLength n n u) =
      fun u : ℝ ↦ Real.exp (-(-1 / 2 : ℝ) * u) *
        clippedOddCorrelation yoshidaHalfLength n n u by
    funext u
    congr 2
    ring]
  rw [show (fun u : ℝ ↦ Real.exp (-u / 2) *
      clippedOddCorrelation yoshidaHalfLength n n u) =
      fun u : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * u) *
        clippedOddCorrelation yoshidaHalfLength n n u by
    funext u
    congr 2
    ring]
  rw [integral_exp_neg_mul_fullDiagonal_eq_ramp_add_sine hn (-1 / 2),
    integral_exp_neg_mul_fullDiagonal_eq_ramp_add_sine hn (1 / 2)]
  rw [show -(-1 / 2 : ℝ) * yoshidaLength = yoshidaLength / 2 by ring,
    show -(1 / 2 : ℝ) * yoshidaLength = -yoshidaLength / 2 by ring,
    exp_yoshidaLength_half, exp_neg_yoshidaLength_half]
  unfold sinePolarValue
  field_simp [yoshidaLength_pos.ne', hk]
  ring

private theorem hasSum_diagonalRenormalized
    {n : ℕ} (hn : n ≠ 0) :
    HasSum
      (renormalizedTerm yoshidaLength 1
        (clippedOddCorrelation yoshidaHalfLength n n))
      ((∫ u in 0..yoshidaLength,
          stableGeometricIntegrand 1
            (clippedOddCorrelation yoshidaHalfLength n n) u) +
        (Real.log yoshidaLength + Real.log 2)) := by
  simpa only [mul_one] using
    renormalizedSeries_hasSum_stable yoshidaLength_pos
      (continuous_clippedOddCorrelation_diag hn)
      (diagonal_pairedIntegralInterchange hn)
      (diagonal_stableGeometricIntegrand_intervalIntegrable hn)
      (referenceRegularized_intervalIntegrable yoshidaLength)

private theorem oddRealDigammaGeometricValue_eq_neg_gamma_sub_tsum_sub_logPi
    {n : ℕ} (hn : n ≠ 0) :
    oddRealDigammaGeometricValue n n =
      -Real.eulerMascheroniConstant -
        ∑' k : ℕ,
          renormalizedTerm yoshidaLength 1
            (clippedOddCorrelation yoshidaHalfLength n n) k -
        Real.log Real.pi := by
  let C : ℝ → ℝ := clippedOddCorrelation yoshidaHalfLength n n
  have hren : HasSum (renormalizedTerm yoshidaLength 1 C)
      ((∫ u in 0..yoshidaLength,
          stableGeometricIntegrand 1 C u) +
        (Real.log yoshidaLength + Real.log 2)) := by
    simpa only [C] using hasSum_diagonalRenormalized hn
  have hindex :
      geometricIntegralTerm yoshidaLength C 0 +
          ∑' k : ℕ, (geometricIntegralTerm yoshidaLength C (k + 1) -
            1 / (k + 1 : ℕ)) =
        ∑' k : ℕ, renormalizedTerm yoshidaLength 1 C k := by
    calc
      geometricIntegralTerm yoshidaLength C 0 +
          ∑' k : ℕ, (geometricIntegralTerm yoshidaLength C (k + 1) -
            1 / (k + 1 : ℕ)) =
          (∫ u in 0..yoshidaLength,
              stableGeometricIntegrand 1 C u) +
            (Real.log yoshidaLength + Real.log 2) :=
        geometricIntegralTerm_zero_add_tsum_shifted_eq hren
      _ = ∑' k : ℕ, renormalizedTerm yoshidaLength 1 C k :=
        hren.tsum_eq.symm
  rw [oddRealDigammaGeometricValue]
  rw [clippedOddCorrelation_half_zero hn hn, if_pos rfl]
  change
    -(geometricIntegralTerm yoshidaLength C 0 +
        Real.eulerMascheroniConstant * 1 +
        ∑' k : ℕ, (geometricIntegralTerm yoshidaLength C (k + 1) -
          ((k + 1 : ℕ) : ℝ)⁻¹ * 1)) - Real.log Real.pi * 1 = _
  have hshift :
      (∑' k : ℕ, (geometricIntegralTerm yoshidaLength C (k + 1) -
        ((k + 1 : ℕ) : ℝ)⁻¹ * 1)) =
      ∑' k : ℕ, (geometricIntegralTerm yoshidaLength C (k + 1) -
        1 / (k + 1 : ℕ)) := by
    apply tsum_congr
    intro k
    push_cast
    ring
  rw [show geometricIntegralTerm yoshidaLength C 0 +
      Real.eulerMascheroniConstant * 1 +
      ∑' k : ℕ, (geometricIntegralTerm yoshidaLength C (k + 1) -
        ((k + 1 : ℕ) : ℝ)⁻¹ * 1) =
      Real.eulerMascheroniConstant +
        (geometricIntegralTerm yoshidaLength C 0 +
          ∑' k : ℕ, (geometricIntegralTerm yoshidaLength C (k + 1) -
            1 / (k + 1 : ℕ))) by
      rw [hshift]
      ring,
    hindex]
  ring

private theorem diagonalOddMomentGram_eq_polar_sub_gamma_sub_tsum_sub_logPi
    {n : ℕ} (hn : n ≠ 0) :
    oddMomentGram yoshidaSineMoment yoshidaDiagonalMoment n n =
      oddRealPolarCorrelationValue n n - Real.eulerMascheroniConstant -
        ∑' k : ℕ,
          renormalizedTerm yoshidaLength 1
            (clippedOddCorrelation yoshidaHalfLength n n) k -
        Real.log Real.pi := by
  have hadmissible := clippedOddAdmissibleRealSpaceGram_diag_eq_oddMomentGram
    hn (yoshidaSineMomentIntegrand_intervalIntegrable hn)
      (yoshidaDiagonalMomentIntegrand_intervalIntegrable n)
  have hassembly := oddRealPolar_add_digamma_eq_admissible hn hn
  rw [oddRealDigammaGeometricValue_eq_neg_gamma_sub_tsum_sub_logPi hn]
    at hassembly
  linarith

private theorem renormalizedDiagonal_sub_scaledSine_eq_raw
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    renormalizedTerm yoshidaLength 1
          (clippedOddCorrelation yoshidaHalfLength n n) k -
        sineCauchyTerm n k / (yoshidaLength * yoshidaKappa n) =
      diagonalDyadicRawTerm n k := by
  have hkappa : yoshidaKappa n ≠ 0 :=
    YoshidaOddCorrelationIntegrability.yoshidaKappa_ne_zero hn
  rw [renormalizedTerm_diagonal_eq hn, sineCauchyTerm,
    exp_neg_oddRate_mul_length]
  unfold diagonalDyadicRawTerm diagonalRampClosed oddRate
  field_simp [yoshidaLength_pos.ne', hkappa]
  ring

private theorem summable_sineCauchyTerm {n : ℕ} (hn : n ≠ 0) :
    Summable (sineCauchyTerm n) := by
  apply (hasSum_sine_geometricIntegrals n).summable.congr
  intro k
  rw [renormalizedTerm_sine_eq hn k, sineCauchyTerm,
    exp_neg_oddRate_mul_length]

private theorem summable_diagonalDyadicRawTerm
    {n : ℕ} (hn : n ≠ 0) :
    Summable (diagonalDyadicRawTerm n) := by
  have hfull := (hasSum_diagonalRenormalized hn).summable
  have hsine := (summable_sineCauchyTerm hn).div_const
    (yoshidaLength * yoshidaKappa n)
  apply (hfull.sub hsine).congr
  intro k
  exact renormalizedDiagonal_sub_scaledSine_eq_raw hn k

private theorem yoshidaDiagonalMoment_eq_closedRamps_sub_rawTsum
    {n : ℕ} (hn : n ≠ 0) :
    yoshidaDiagonalMoment n =
      2 * diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
          (-1 / 2) (Real.sqrt 2) +
        2 * diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
          (1 / 2) (Real.sqrt 2)⁻¹ -
        Real.eulerMascheroniConstant - Real.log Real.pi -
        ∑' k : ℕ, diagonalDyadicRawTerm n k := by
  have hkappa : yoshidaKappa n ≠ 0 :=
    YoshidaOddCorrelationIntegrability.yoshidaKappa_ne_zero hn
  have hLK : yoshidaLength * yoshidaKappa n =
      2 * Real.pi * (n : ℝ) := by
    rw [mul_comm, yoshidaKappa_mul_length]
  have hrelation :=
    yoshidaDiagonalMoment_eq_diagonal_oddMomentGram_sub_sine hn
  rw [← hLK] at hrelation
  rw [diagonalOddMomentGram_eq_polar_sub_gamma_sub_tsum_sub_logPi hn,
    yoshidaSineMoment_eq_explicitCauchySeries hn] at hrelation
  have hfull := (hasSum_diagonalRenormalized hn).summable
  have hsine := (summable_sineCauchyTerm hn).div_const
    (yoshidaLength * yoshidaKappa n)
  have htsum :
      (∑' k : ℕ, diagonalDyadicRawTerm n k) =
        (∑' k : ℕ,
            renormalizedTerm yoshidaLength 1
              (clippedOddCorrelation yoshidaHalfLength n n) k) -
          (∑' k : ℕ, sineCauchyTerm n k) /
            (yoshidaLength * yoshidaKappa n) := by
    calc
      (∑' k : ℕ, diagonalDyadicRawTerm n k) =
          ∑' k : ℕ,
            (renormalizedTerm yoshidaLength 1
                (clippedOddCorrelation yoshidaHalfLength n n) k -
              sineCauchyTerm n k /
                (yoshidaLength * yoshidaKappa n)) := by
        apply tsum_congr
        intro k
        exact (renormalizedDiagonal_sub_scaledSine_eq_raw hn k).symm
      _ = (∑' k : ℕ,
            renormalizedTerm yoshidaLength 1
              (clippedOddCorrelation yoshidaHalfLength n n) k) -
          ∑' k : ℕ, sineCauchyTerm n k /
            (yoshidaLength * yoshidaKappa n) :=
        hfull.tsum_sub hsine
      _ = (∑' k : ℕ,
            renormalizedTerm yoshidaLength 1
              (clippedOddCorrelation yoshidaHalfLength n n) k) -
          (∑' k : ℕ, sineCauchyTerm n k) /
            (yoshidaLength * yoshidaKappa n) := by
        rw [tsum_div_const]
  have hpolar := oddRealPolar_sub_scaled_sinePolar_eq_closedRamps hn
  have hdiv :
      (sinePolarValue n - ∑' k : ℕ, sineCauchyTerm n k) /
          (yoshidaLength * yoshidaKappa n) =
        sinePolarValue n / (yoshidaLength * yoshidaKappa n) -
          (∑' k : ℕ, sineCauchyTerm n k) /
            (yoshidaLength * yoshidaKappa n) := by
    ring
  rw [hdiv] at hrelation
  linarith

private theorem diagonalDyadicRawTerm_zero (n : ℕ) :
    diagonalDyadicRawTerm n 0 =
      2 * diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
        (1 / 2) (Real.sqrt 2)⁻¹ - 1 := by
  unfold diagonalDyadicRawTerm
  norm_num

private theorem yoshidaDiagonalMoment_eq_positiveRamp_add_one_sub_rawTail
    {n : ℕ} (hn : n ≠ 0) :
    yoshidaDiagonalMoment n =
      2 * diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
          (-1 / 2) (Real.sqrt 2) + 1 -
        Real.eulerMascheroniConstant - Real.log Real.pi -
        ∑' j : ℕ, diagonalDyadicRawTerm n (j + 1) := by
  have hmain := yoshidaDiagonalMoment_eq_closedRamps_sub_rawTsum hn
  have hsplit :=
    (summable_diagonalDyadicRawTerm hn).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  rw [diagonalDyadicRawTerm_zero] at hsplit
  linarith

private def diagonalTelescopingTerm (j : ℕ) : ℝ :=
  1 / (j + 1 : ℕ) - 1 / (j + 2 : ℕ)

private def diagonalLogTerm (j : ℕ) : ℝ :=
  (1 / 4 : ℝ) ^ (j + 1) / (j + 1 : ℕ)

private def diagonalZetaTwoTerm (j : ℕ) : ℝ :=
  1 / ((j + 1 : ℕ) : ℝ) ^ 2

private def diagonalAccelerationRemainder (j : ℕ) : ℝ :=
  diagonalTelescopingTerm j - diagonalLogTerm j -
    diagonalAccelerationCoefficient * diagonalZetaTwoTerm j

private theorem diagonalRaw_succ_eq_accelerated_add_remainder (n j : ℕ) :
    diagonalDyadicRawTerm n (j + 1) =
      diagonalAcceleratedCorrection n j +
        diagonalAccelerationRemainder j := by
  unfold diagonalDyadicRawTerm diagonalAcceleratedCorrection
    yoshidaDiagonalDyadicPairedCorrection diagonalDyadicPairedCorrection
    diagonalPairedCorrection diagonalAccelerationRemainder
    diagonalTelescopingTerm diagonalLogTerm diagonalZetaTwoTerm
    diagonalAccelerationCoefficient
  push_cast
  rw [one_div_pow]
  ring

private theorem hasSum_diagonalTelescopingTerm :
    HasSum diagonalTelescopingTerm 1 := by
  have h := (hasSum_harmonicShiftCorrection (1 : ℝ)).neg
  convert h using 1
  · funext j
    unfold diagonalTelescopingTerm harmonicShiftCorrection
    push_cast
    ring
  · norm_num

private theorem hasSum_diagonalLogTerm :
    HasSum diagonalLogTerm (-Real.log (3 / 4)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one
    (x := (1 / 4 : ℝ)) (by norm_num)
  have hfun : diagonalLogTerm =
      fun j : ℕ ↦ (1 / 4 : ℝ) ^ (j + 1) / (j + 1) := by
    funext j
    unfold diagonalLogTerm
    push_cast
    ring
  rw [hfun]
  convert h using 1
  all_goals norm_num

private theorem hasSum_diagonalZetaTwoTerm :
    HasSum diagonalZetaTwoTerm (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  convert h using 1
  all_goals norm_num [diagonalZetaTwoTerm, Nat.add_comm]

private theorem hasSum_diagonalAccelerationRemainder :
    HasSum diagonalAccelerationRemainder
      (1 + Real.log (3 / 4) -
        diagonalAccelerationCoefficient * (Real.pi ^ 2 / 6)) := by
  have h := (hasSum_diagonalTelescopingTerm.sub hasSum_diagonalLogTerm).sub
    (hasSum_diagonalZetaTwoTerm.mul_left diagonalAccelerationCoefficient)
  convert h using 1
  all_goals ring

/-- The shifted accelerated diagonal correction series is summable for every
nonzero Yoshida mode. -/
theorem summable_diagonalAcceleratedCorrection
    {n : ℕ} (hn : n ≠ 0) :
    Summable (diagonalAcceleratedCorrection n) := by
  let rawTail : ℕ → ℝ := fun j ↦ diagonalDyadicRawTerm n (j + 1)
  have hraw : Summable rawTail := by
    simpa only [rawTail] using
      (summable_nat_add_iff 1).2 (summable_diagonalDyadicRawTerm hn)
  have hdiff : Summable
      (fun j ↦ rawTail j - diagonalAccelerationRemainder j) :=
    hraw.sub hasSum_diagonalAccelerationRemainder.summable
  have hfun :
      (fun j ↦ rawTail j - diagonalAccelerationRemainder j) =
        diagonalAcceleratedCorrection n := by
    funext j
    dsimp only [rawTail]
    rw [diagonalRaw_succ_eq_accelerated_add_remainder]
    ring
  rw [hfun] at hdiff
  exact hdiff

private theorem tsum_diagonalRawTail_eq_accelerated_add_constants
    {n : ℕ} (hn : n ≠ 0) :
    (∑' j : ℕ, diagonalDyadicRawTerm n (j + 1)) =
      (∑' j : ℕ, diagonalAcceleratedCorrection n j) +
        1 + Real.log (3 / 4) -
        diagonalAccelerationCoefficient * (Real.pi ^ 2 / 6) := by
  let rawTail : ℕ → ℝ := fun j ↦ diagonalDyadicRawTerm n (j + 1)
  let R : ℝ := 1 + Real.log (3 / 4) -
    diagonalAccelerationCoefficient * (Real.pi ^ 2 / 6)
  have hraw : Summable rawTail := by
    simpa only [rawTail] using
      (summable_nat_add_iff 1).2 (summable_diagonalDyadicRawTerm hn)
  have hrem : HasSum diagonalAccelerationRemainder R := by
    simpa only [R] using hasSum_diagonalAccelerationRemainder
  have hcorr0 : HasSum
      (fun j ↦ rawTail j - diagonalAccelerationRemainder j)
      ((∑' j : ℕ, rawTail j) - R) := hraw.hasSum.sub hrem
  have hcorr : HasSum (diagonalAcceleratedCorrection n)
      ((∑' j : ℕ, rawTail j) - R) := by
    have hfun :
        (fun j ↦ rawTail j - diagonalAccelerationRemainder j) =
          diagonalAcceleratedCorrection n := by
      funext j
      dsimp only [rawTail]
      rw [diagonalRaw_succ_eq_accelerated_add_remainder]
      ring
    rw [hfun] at hcorr0
    exact hcorr0
  have heq := hcorr.tsum_eq
  dsimp only [rawTail, R] at heq
  linarith

def diagonalAcceleratedBase (n : ℕ) : ℝ :=
  2 * diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
      (-1 / 2) (Real.sqrt 2) -
    Real.eulerMascheroniConstant - Real.log Real.pi +
    Real.log (4 / 3) +
    diagonalAccelerationCoefficient * (Real.pi ^ 2 / 6)

private theorem neg_log_three_fourths_eq_log_four_thirds :
    -Real.log (3 / 4) = Real.log (4 / 3) := by
  rw [show (4 / 3 : ℝ) = (3 / 4 : ℝ)⁻¹ by norm_num,
    Real.log_inv]

/-- Exact accelerated identity: the `k = 0` negative polar term is canceled,
the remaining raw series is reindexed at `k = j + 1`, and its harmonic,
dyadic-logarithmic, and zeta-two asymptotes are summed in closed form. -/
theorem yoshidaDiagonalMoment_eq_acceleratedSeries
    {n : ℕ} (hn : n ≠ 0) :
    yoshidaDiagonalMoment n =
      diagonalAcceleratedBase n -
        ∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (j + 1) := by
  have hmoment :=
    yoshidaDiagonalMoment_eq_positiveRamp_add_one_sub_rawTail hn
  have hseries := tsum_diagonalRawTail_eq_accelerated_add_constants hn
  rw [hseries] at hmoment
  simp only [diagonalAcceleratedCorrection] at hmoment
  rw [diagonalAccelerationCoefficient] at hmoment
  rw [diagonalAcceleratedBase, diagonalAccelerationCoefficient]
  rw [← neg_log_three_fourths_eq_log_four_thirds]
  linarith

end

end ArithmeticHodge.Analysis.YoshidaDiagonalAcceleratedSeries
