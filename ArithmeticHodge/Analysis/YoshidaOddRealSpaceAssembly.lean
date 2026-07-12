import ArithmeticHodge.Analysis.YoshidaOddCorrelationFold
import ArithmeticHodge.Analysis.YoshidaOddCorrelationIntegrability
import ArithmeticHodge.Analysis.YoshidaOddPolarCorrelation
import ArithmeticHodge.Analysis.YoshidaShiftedGeometricSeries
import ArithmeticHodge.Analysis.YoshidaClippedMomentBridgeFull
import ArithmeticHodge.Analysis.YoshidaMomentIntegrability

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaOddRealSpaceAssembly

noncomputable section

open ArithmeticHodge.Analysis
open ArithmeticHodge.Analysis.YoshidaClippedMomentBridge
open ArithmeticHodge.Analysis.YoshidaClippedMomentBridgeFull
open ArithmeticHodge.Analysis.YoshidaOddGramPrefix
open ArithmeticHodge.Analysis.YoshidaOddCorrelationFold
open ArithmeticHodge.Analysis.YoshidaOddCorrelationIntegrability
open ArithmeticHodge.Analysis.YoshidaOddPolarCorrelation
open ArithmeticHodge.Analysis.YoshidaOddSpectralBridge
open ArithmeticHodge.Analysis.YoshidaOddIntervalCertificate
open ArithmeticHodge.Analysis.YoshidaMomentIntegrability
open ArithmeticHodge.Analysis.YoshidaRenormalizedGeometricKernel
open ArithmeticHodge.Analysis.YoshidaShiftedGeometricSeries

/-!
# Exact real-space assembly for Yoshida's odd block

This module closes the spectral-to-distribution boundary for every nonzero odd
mode pair.  It identifies the Cauchy values with real Laplace moments, matches
the shifted digamma indexing to the renormalized series, folds the polar terms,
and combines the geometric and regular exponential kernels with the exact
`log L + γ + log 2 + log π` constant.  Consequently the full ten-mode
admissible-distribution bridge and the full clipped/moment bridge are theorems,
not remaining hypotheses.
-/

def oddPolarCorrelationIntegrand (n m : ℕ) (u : ℝ) : ℝ :=
  2 * (Real.exp (u / 2) + Real.exp (-u / 2)) *
    clippedOddCorrelation yoshidaHalfLength n m u

def oddRealPolarCorrelationValue (n m : ℕ) : ℝ :=
  2 * ∫ u : ℝ in 0..yoshidaLength,
    (Real.exp (u / 2) + Real.exp (-u / 2)) *
      clippedOddCorrelation yoshidaHalfLength n m u

theorem negatedGeometric_add_polar_eq_stable_of_ne_zero
    (n m : ℕ) {u : ℝ} (hu : u ≠ 0) :
    (-oddKernel u * clippedOddCorrelation yoshidaHalfLength n m u +
        clippedOddCorrelation yoshidaHalfLength n m 0 / u) +
      oddPolarCorrelationIntegrand n m u =
        clippedOddStableCorrelationIntegrand n m u := by
  rw [clippedOddStableCorrelationIntegrand, oddPolarCorrelationIntegrand,
    yoshidaWeightPlus, if_neg hu, yoshidaWeight, oddKernel]
  ring

theorem integral_negatedGeometric_add_polar_eq_stable (n m : ℕ) :
    (∫ u in 0..yoshidaLength,
      ((-oddKernel u * clippedOddCorrelation yoshidaHalfLength n m u +
          clippedOddCorrelation yoshidaHalfLength n m 0 / u) +
        oddPolarCorrelationIntegrand n m u)) =
      ∫ u in 0..yoshidaLength,
        clippedOddStableCorrelationIntegrand n m u := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
    simp [ae_iff, measure_singleton]] with u hu
  intro _
  exact negatedGeometric_add_polar_eq_stable_of_ne_zero n m hu

theorem oddCauchyCorrelationValue_eq_geometricIntegralTerm
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (k : ℕ) :
    oddCauchyCorrelationValue n m k =
      (geometricIntegralTerm yoshidaLength
        (clippedOddCorrelation yoshidaHalfLength n m) k : ℂ) := by
  simpa only [geometricIntegralTerm, oddRate, Nat.cast_add, Nat.cast_one]
    using oddCauchyCorrelationValue_eq_two_integral_length hn hm k

def oddRealDigammaGeometricValue (n m : ℕ) : ℝ :=
  -(geometricIntegralTerm yoshidaLength
        (clippedOddCorrelation yoshidaHalfLength n m) 0 +
      Real.eulerMascheroniConstant *
        clippedOddCorrelation yoshidaHalfLength n m 0 +
      ∑' k : ℕ,
        (geometricIntegralTerm yoshidaLength
            (clippedOddCorrelation yoshidaHalfLength n m) (k + 1) -
          ((k + 1 : ℕ) : ℝ)⁻¹ *
            clippedOddCorrelation yoshidaHalfLength n m 0)) -
    Real.log Real.pi * clippedOddCorrelation yoshidaHalfLength n m 0

theorem oddDigammaCauchySeriesValue_eq_ofReal
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    oddDigammaCauchySeriesValue n m =
      (oddRealDigammaGeometricValue n m : ℂ) := by
  rw [oddDigammaCauchySeriesValue, oddRealDigammaGeometricValue]
  rw [oddCauchyCorrelationValue_eq_geometricIntegralTerm hn hm 0,
    oddCorrelationZero_eq_clippedOddCorrelation_zero hn hm]
  simp_rw [oddCauchyCorrelationValue_eq_geometricIntegralTerm hn hm]
  push_cast
  ring

theorem oddRealDigammaGeometricValue_eq_negatedKernel
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    oddRealDigammaGeometricValue n m =
      (∫ u in 0..yoshidaLength,
        -oddKernel u * clippedOddCorrelation yoshidaHalfLength n m u +
          clippedOddCorrelation yoshidaHalfLength n m 0 / u) -
      (Real.log yoshidaLength + Real.eulerMascheroniConstant +
        Real.log 2 + Real.log Real.pi) *
          clippedOddCorrelation yoshidaHalfLength n m 0 := by
  let C : ℝ → ℝ := clippedOddCorrelation yoshidaHalfLength n m
  let C0 : ℝ := clippedOddCorrelation yoshidaHalfLength n m 0
  have hren : HasSum (renormalizedTerm yoshidaLength C0 C)
      ((∫ u in 0..yoshidaLength, stableGeometricIntegrand C0 C u) +
        (Real.log yoshidaLength + Real.log 2) * C0) :=
    renormalizedSeries_hasSum_stable yoshidaLength_pos
      (continuous_clippedOddCorrelation hn hm)
      (odd_pairedIntegralInterchange hn hm)
      (odd_stableGeometricIntegrand_intervalIntegrable hn hm)
      (referenceRegularized_intervalIntegrable yoshidaLength)
  have hindex :
      geometricIntegralTerm yoshidaLength C 0 +
          ∑' k : ℕ, (geometricIntegralTerm yoshidaLength C (k + 1) -
            C0 / (k + 1 : ℕ)) =
        ∑' k : ℕ, renormalizedTerm yoshidaLength C0 C k := by
    calc
      geometricIntegralTerm yoshidaLength C 0 +
            ∑' k : ℕ, (geometricIntegralTerm yoshidaLength C (k + 1) -
              C0 / (k + 1 : ℕ)) =
          (∫ u in 0..yoshidaLength, stableGeometricIntegrand C0 C u) +
            (Real.log yoshidaLength + Real.log 2) * C0 :=
        geometricIntegralTerm_zero_add_tsum_shifted_eq hren
      _ = ∑' k : ℕ, renormalizedTerm yoshidaLength C0 C k :=
        hren.tsum_eq.symm
  have hneg := odd_negated_geometric_identity hn hm
  change _ = _ at hneg
  rw [oddRealDigammaGeometricValue]
  change
    -(geometricIntegralTerm yoshidaLength C 0 +
        Real.eulerMascheroniConstant * C0 +
        ∑' k : ℕ, (geometricIntegralTerm yoshidaLength C (k + 1) -
          ((k + 1 : ℕ) : ℝ)⁻¹ * C0)) - Real.log Real.pi * C0 = _
  have hindex' :
      geometricIntegralTerm yoshidaLength C 0 +
          ∑' k : ℕ, (geometricIntegralTerm yoshidaLength C (k + 1) -
            ((k + 1 : ℕ) : ℝ)⁻¹ * C0) =
        ∑' k : ℕ, renormalizedTerm yoshidaLength C0 C k := by
    simpa only [div_eq_mul_inv, mul_comm] using hindex
  rw [show geometricIntegralTerm yoshidaLength C 0 +
      Real.eulerMascheroniConstant * C0 +
      ∑' k : ℕ, (geometricIntegralTerm yoshidaLength C (k + 1) -
        ((k + 1 : ℕ) : ℝ)⁻¹ * C0) =
      Real.eulerMascheroniConstant * C0 +
        (geometricIntegralTerm yoshidaLength C 0 +
          ∑' k : ℕ, (geometricIntegralTerm yoshidaLength C (k + 1) -
            ((k + 1 : ℕ) : ℝ)⁻¹ * C0)) by ring,
    hindex']
  dsimp only [C, C0] at hneg ⊢
  linarith

theorem oddPolarCrossTerm_eq_ofReal
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    star (yoshidaPositivePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
        (yoshidaClippedOddMode yoshidaHalfLength n)) *
        yoshidaNegativePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
          (yoshidaClippedOddMode yoshidaHalfLength m) +
      star (yoshidaNegativePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
        (yoshidaClippedOddMode yoshidaHalfLength n)) *
        yoshidaPositivePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
          (yoshidaClippedOddMode yoshidaHalfLength m) =
      (oddRealPolarCorrelationValue n m : ℂ) := by
  rw [oddPolarCrossTerm_eq_two_integral_correlation hn hm,
    oddRealPolarCorrelationValue]
  push_cast
  congr 1
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro u _
  push_cast
  rfl

theorem oddRealPolar_add_digamma_eq_admissible
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    oddRealPolarCorrelationValue n m +
        oddRealDigammaGeometricValue n m =
      clippedOddAdmissibleRealSpaceGram n m := by
  have hpolarValue : oddRealPolarCorrelationValue n m =
      ∫ u in 0..yoshidaLength, oddPolarCorrelationIntegrand n m u := by
    rw [oddRealPolarCorrelationValue,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    rw [oddPolarCorrelationIntegrand]
    ring
  have hnegInt : IntervalIntegrable
      (fun u : ℝ ↦
        -oddKernel u * clippedOddCorrelation yoshidaHalfLength n m u +
          clippedOddCorrelation yoshidaHalfLength n m 0 / u)
      volume 0 yoshidaLength := by
    apply (odd_stableGeometricIntegrand_intervalIntegrable hn hm).neg.congr
    intro u _
    simp only [Pi.neg_apply]
    unfold stableGeometricIntegrand
    ring
  have hweight : Continuous (fun u : ℝ ↦
      2 * (Real.exp (u / 2) + Real.exp (-u / 2))) := by fun_prop
  have hpolarInt : IntervalIntegrable (oddPolarCorrelationIntegrand n m)
      volume 0 yoshidaLength := by
    simpa only [oddPolarCorrelationIntegrand, Pi.mul_apply] using
      (hweight.mul (continuous_clippedOddCorrelation hn hm)).intervalIntegrable
        (μ := volume) 0 yoshidaLength
  rw [oddRealDigammaGeometricValue_eq_negatedKernel hn hm,
    hpolarValue]
  let N : ℝ := ∫ u in 0..yoshidaLength,
    -oddKernel u * clippedOddCorrelation yoshidaHalfLength n m u +
      clippedOddCorrelation yoshidaHalfLength n m 0 / u
  let P : ℝ := ∫ u in 0..yoshidaLength,
    oddPolarCorrelationIntegrand n m u
  let K : ℝ := Real.log yoshidaLength + Real.eulerMascheroniConstant +
    Real.log 2 + Real.log Real.pi
  change P + (N - K * clippedOddCorrelation yoshidaHalfLength n m 0) = _
  rw [show P + (N - K * clippedOddCorrelation yoshidaHalfLength n m 0) =
      (N + P) - K * clippedOddCorrelation yoshidaHalfLength n m 0 by ring]
  dsimp only [N, P, K]
  rw [← intervalIntegral.integral_add hnegInt hpolarInt]
  rw [integral_negatedGeometric_add_polar_eq_stable]
  rw [clippedOddAdmissibleRealSpaceGram]

theorem yoshidaClippedLocalCriticalPairing_odd_eq_admissible
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    yoshidaClippedLocalCriticalPairing
        yoshidaHalfLength yoshidaHalfLength_pos
        (yoshidaClippedOddMode yoshidaHalfLength n)
        (yoshidaClippedOddMode yoshidaHalfLength m) =
      (clippedOddAdmissibleRealSpaceGram n m : ℂ) := by
  rw [yoshidaClippedLocalCriticalPairing]
  rw [oddPolarCrossTerm_eq_ofReal hn hm]
  rw [normalized_oddCriticalCrossIntegrand_eq_cauchySeries n m]
  rw [oddDigammaCauchySeriesValue_eq_ofReal hn hm]
  rw [← Complex.ofReal_add]
  rw [oddRealPolar_add_digamma_eq_admissible hn hm]

theorem clippedOddFullAdmissibleDistributionBridge :
    ClippedOddFullAdmissibleDistributionBridge := by
  intro i j
  unfold clippedOddFullGram yoshidaClippedOddGram yoshidaClippedOddLowMode
  rw [yoshidaClippedLocalCriticalForm_apply]
  exact yoshidaClippedLocalCriticalPairing_odd_eq_admissible
    (by omega) (by omega)

theorem clippedOddFullMomentBridge : ClippedOddFullMomentBridge :=
  clippedOddFullMomentBridge_of_admissibleDistributionBridge
    clippedOddFullAdmissibleDistributionBridge
    clippedOddFullMomentIntegrable

end


end ArithmeticHodge.Analysis.YoshidaOddRealSpaceAssembly
