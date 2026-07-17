import ArithmeticHodge.Analysis.ShiftedLegendreLogEnergyOrthogonalProjection
import ArithmeticHodge.Analysis.ShiftedLogKernelTriangular
import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineResidualDecompositionStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreLogKernel
open ShiftedLogKernelCrossEnergy
open ShiftedLogKernelTriangular
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointPullbackLipschitz
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseHigherLegendreStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineResidualDecompositionStructural
open YoshidaFactorTwoPhaseP67ResidualAffineCancellationStructural
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural
open YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural

noncomputable section

/-!
# Exact cutoff-nine mixed cancellation core

The finite cutoff-nine profile is a polynomial transported from `[0,1]`.
Its higher residual annihilates every polynomial of degree below nine.  This
module records the three consequences needed before the honest surviving
low--residual aggregate is bounded:

* the raw logarithmic difference energy splits with no cross term;
* the ordinary `L²` cross, and hence the retained zero-lag prime row, vanish;
* the affine alternating regular-kernel model vanishes.

No term with a nonpolynomial weight or a positive correlation lag is removed.
-/

private theorem centeredRawLogEnergy_centeredPolynomialLift_add_tail_of_pairing
    (p : ℝ[X]) (r : ℝ → ℝ)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (hpair : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLogKernel p).eval (t : ℝ)) = 0) :
    centeredRawLogEnergy (centeredPolynomialLift p + r) =
      centeredRawLogEnergy (centeredPolynomialLift p) +
        centeredRawLogEnergy r := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback r (t : ℝ)
  let pfun : unitInterval → ℝ := fun t ↦ p.eval (t : ℝ)
  let g : unitInterval → ℝ := fun t ↦
    centeredPullback (centeredPolynomialLift p + r) (t : ℝ)
  let U : unitInterval × unitInterval → ℝ := fun z ↦
    (f z.1 - f z.2) * unitIntervalRawPolynomialLogKernel p z
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback r hlocal
  have hfEnergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  have hfcont : Continuous f := by
    simpa only [f] using hLip.continuous
  have hf : Integrable f :=
    hfcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpEnergy : Integrable (unitIntervalRawLogEnergyIntegrand pfun) := by
    simpa only [pfun] using
      integrable_unitIntervalRawLogEnergyIntegrand_polynomial p
  have hUInt : Integrable U := by
    simpa only [U] using
      integrable_sub_mul_unitIntervalRawPolynomialLogKernel f hf p
  have hcrossEq :=
    integral_sub_mul_unitIntervalRawPolynomialLogKernel_eq f hf p
  have hUzero : (∫ z, U z) = 0 := by
    rw [hpair] at hcrossEq
    norm_num at hcrossEq
    simpa only [U, f] using hcrossEq
  have hgPoint (t : unitInterval) : g t = pfun t + f t := by
    dsimp only [g, pfun, f, centeredPullback]
    have hm := centeredPullback_centeredPolynomialLift p (t : ℝ)
    unfold centeredPullback at hm
    simp only [Pi.add_apply]
    rw [hm]
  have hpoint (z : unitInterval × unitInterval) :
      unitIntervalRawLogEnergyIntegrand g z =
        unitIntervalRawLogEnergyIntegrand pfun z +
          unitIntervalRawLogEnergyIntegrand f z + 2 * U z := by
    unfold unitIntervalRawLogEnergyIntegrand U
      unitIntervalRawPolynomialLogKernel
    rw [hgPoint z.1, hgPoint z.2]
    dsimp only [pfun]
    ring
  have hcombo : Integrable (fun z : unitInterval × unitInterval ↦
      unitIntervalRawLogEnergyIntegrand pfun z +
        unitIntervalRawLogEnergyIntegrand f z + 2 * U z) :=
    (hpEnergy.add hfEnergy).add (hUInt.const_mul 2)
  have hgEnergy : Integrable (unitIntervalRawLogEnergyIntegrand g) := by
    apply hcombo.congr
    filter_upwards [] with z
    exact (hpoint z).symm
  have hIntegralExpand :
      (∫ z, unitIntervalRawLogEnergyIntegrand pfun z +
          unitIntervalRawLogEnergyIntegrand f z + 2 * U z) =
        (∫ z, unitIntervalRawLogEnergyIntegrand pfun z) +
          (∫ z, unitIntervalRawLogEnergyIntegrand f z) +
            2 * (∫ z, U z) := by
    calc
      _ = (∫ z, unitIntervalRawLogEnergyIntegrand pfun z +
            unitIntervalRawLogEnergyIntegrand f z) + ∫ z, 2 * U z := by
        exact integral_add (hpEnergy.add hfEnergy) (hUInt.const_mul 2)
      _ = ((∫ z, unitIntervalRawLogEnergyIntegrand pfun z) +
            ∫ z, unitIntervalRawLogEnergyIntegrand f z) +
          ∫ z, 2 * U z := by
        rw [integral_add hpEnergy hfEnergy]
      _ = _ := by rw [integral_const_mul]
  have hunitExpand : unitIntervalLogEnergy g =
      unitIntervalLogEnergy pfun + unitIntervalLogEnergy f := by
    unfold unitIntervalLogEnergy
    rw [show (∫ z, unitIntervalRawLogEnergyIntegrand g z) =
        ∫ z, unitIntervalRawLogEnergyIntegrand pfun z +
          unitIntervalRawLogEnergyIntegrand f z + 2 * U z by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hpoint z,
      hIntegralExpand, hUzero]
    ring
  have hbridgeG : unitIntervalLogEnergy g =
      (1 / 4 : ℝ) *
        centeredRawLogEnergy (centeredPolynomialLift p + r) := by
    simpa only [g] using unitIntervalLogEnergy_centeredPullback
      (centeredPolynomialLift p + r) hgEnergy
  have hbridgeP : unitIntervalLogEnergy pfun =
      (1 / 4 : ℝ) * centeredRawLogEnergy (centeredPolynomialLift p) := by
    have hpEnergy' : Integrable (unitIntervalRawLogEnergyIntegrand
        (fun t : unitInterval ↦
          centeredPullback (centeredPolynomialLift p) (t : ℝ))) := by
      apply hpEnergy.congr
      filter_upwards [] with z
      unfold unitIntervalRawLogEnergyIntegrand
      dsimp only [pfun]
      rw [centeredPullback_centeredPolynomialLift,
        centeredPullback_centeredPolynomialLift]
    have hbridge := unitIntervalLogEnergy_centeredPullback
      (centeredPolynomialLift p) hpEnergy'
    rw [show pfun = fun t : unitInterval ↦
        centeredPullback (centeredPolynomialLift p) (t : ℝ) by
      funext t
      exact (centeredPullback_centeredPolynomialLift p (t : ℝ)).symm]
    exact hbridge
  have hbridgeR : unitIntervalLogEnergy f =
      (1 / 4 : ℝ) * centeredRawLogEnergy r := by
    simpa only [f] using unitIntervalLogEnergy_centeredPullback r hfEnergy
  rw [hbridgeG, hbridgeP, hbridgeR] at hunitExpand
  linarith

/-- A cutoff moment gap annihilates the raw logarithmic cross with every
transported polynomial below the cutoff.  The logarithmic operator does not
increase polynomial degree, so this is one structural argument for the whole
finite low block. -/
theorem centeredRawLogEnergy_centeredPolynomialLift_add_tail
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    {k : ℕ} (hlow : centeredLegendreMomentsVanishBelow r k)
    (hpdeg : p.natDegree < k) :
    centeredRawLogEnergy (centeredPolynomialLift p + r) =
      centeredRawLogEnergy (centeredPolynomialLift p) +
        centeredRawLogEnergy r := by
  have hlogdeg : (shiftedLogKernel p).natDegree < k :=
    lt_of_le_of_lt
      (natDegree_le_natDegree (degree_shiftedLogKernel_le p)) hpdeg
  have hpair := integral_centeredPullback_mul_polynomial_eq_zero
    r hr hlow (shiftedLogKernel p) hlogdeg
  exact centeredRawLogEnergy_centeredPolynomialLift_add_tail_of_pairing
    p r hlocal hpair

/-- Ordinary `L²` orthogonality of a transported low polynomial and a
higher residual. -/
theorem intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r)
    {k : ℕ} (hlow : centeredLegendreMomentsVanishBelow r k)
    (hpdeg : p.natDegree < k) :
    (∫ x : ℝ in -1..1, centeredPolynomialLift p x * r x) = 0 := by
  have h := intervalIntegral_mul_shiftedPolynomial_eq_zero
    r hr hlow p hpdeg
  rw [show (fun x : ℝ ↦ centeredPolynomialLift p x * r x) =
      fun x ↦ r x * p.eval ((x + 1) / 2) by
    funext x
    unfold centeredPolynomialLift
    ring]
  exact h

/-- The zeroth centered moment is already part of every nonempty Legendre
moment gap. -/
theorem intervalIntegral_eq_zero_of_momentsVanishBelow
    (r : ℝ → ℝ) (hr : Continuous r) {k : ℕ}
    (hlow : centeredLegendreMomentsVanishBelow r k) (hk : 0 < k) :
    (∫ x : ℝ in -1..1, r x) = 0 := by
  let p : ℝ[X] := 1
  have hpdeg : p.natDegree < k := by
    dsimp only [p]
    simpa using hk
  have h := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    p r hr hlow hpdeg
  simpa only [p, centeredPolynomialLift, Polynomial.eval_one, one_mul]
    using h

/-- The degree-one centered moment is also killed by every gap above one. -/
theorem intervalIntegral_id_mul_eq_zero_of_momentsVanishBelow
    (r : ℝ → ℝ) (hr : Continuous r) {k : ℕ}
    (hlow : centeredLegendreMomentsVanishBelow r k) (hk : 1 < k) :
    (∫ x : ℝ in -1..1, x * r x) = 0 := by
  let p : ℝ[X] := 2 * Polynomial.X - 1
  have hpdeg : p.natDegree < k := by
    dsimp only [p]
    have hp : (2 * Polynomial.X - 1 : ℝ[X]).natDegree ≤ 1 := by
      ring_nf
      compute_degree
    omega
  have h := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    p r hr hlow hpdeg
  rw [show (fun x : ℝ ↦ centeredPolynomialLift p x * r x) =
      fun x ↦ x * r x by
    funext x
    unfold centeredPolynomialLift
    dsimp only [p]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
    ring] at h
  exact h

/-- If the second profile has a moment gap above degree one, then the whole
lag-affine ordered cross row vanishes against an arbitrary continuous first
profile. -/
theorem integral_linear_mul_crossDifference_eq_zero_of_second_momentGap
    (u r : ℝ → ℝ) (hu : Continuous u) (hr : Continuous r)
    {k : ℕ} (hlow : centeredLegendreMomentsVanishBelow r k)
    (hk : 1 < k) :
    (∫ t : ℝ in 0..2,
      t * (factorTwoCenteredCrossCorrelation r u t -
        factorTwoCenteredCrossCorrelation u r t)) = 0 := by
  have hr0 := intervalIntegral_eq_zero_of_momentsVanishBelow
    r hr hlow (by omega)
  have hr1 := intervalIntegral_id_mul_eq_zero_of_momentsVanishBelow
    r hr hlow hk
  rw [integral_linear_mul_crossDifference_eq_moment_determinant
    u r hu hr, hr0, hr1]
  ring

/-- Both alternating low--residual affine rows vanish at once.  This is the
generic cutoff-nine replacement for the separate `P6/P7/P8` wrappers. -/
theorem integral_linear_mul_residualAlternatingCrossSum_eq_zero
    (eLow oLow eR oR : ℝ → ℝ)
    (heLowc : Continuous eLow) (hoLowc : Continuous oLow)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    {k : ℕ}
    (heGap : centeredLegendreMomentsVanishBelow eR k)
    (hoGap : centeredLegendreMomentsVanishBelow oR k)
    (hk : 1 < k) :
    (∫ t : ℝ in 0..2,
      t * factorTwoP67ResidualAlternatingCrossSum
        eLow oLow eR oR t) = 0 := by
  have heRow := integral_linear_mul_crossDifference_eq_zero_of_second_momentGap
    oLow eR hoLowc heRc heGap hk
  have hoRow := integral_linear_mul_crossDifference_eq_zero_of_second_momentGap
    eLow oR heLowc hoRc hoGap hk
  have heInt : IntervalIntegrable (fun t : ℝ ↦
      t * factorTwoP67ResidualAlternatingCrossDifference eR oLow t)
      volume 0 2 := by
    exact (continuous_id.mul
      ((continuous_factorTwoCenteredCrossCorrelation oLow eR hoLowc heRc).sub
        (continuous_factorTwoCenteredCrossCorrelation eR oLow heRc hoLowc))).intervalIntegrable
      0 2
  have hoInt : IntervalIntegrable (fun t : ℝ ↦
      t * factorTwoP67ResidualAlternatingCrossDifference eLow oR t)
      volume 0 2 := by
    exact (continuous_id.mul
      ((continuous_factorTwoCenteredCrossCorrelation oR eLow hoRc heLowc).sub
        (continuous_factorTwoCenteredCrossCorrelation eLow oR heLowc hoRc))).intervalIntegrable
      0 2
  have heRow' : (∫ t : ℝ in 0..2,
      t * factorTwoP67ResidualAlternatingCrossDifference eR oLow t) = 0 := by
    rw [show (fun t : ℝ ↦
        t * factorTwoP67ResidualAlternatingCrossDifference eR oLow t) =
      fun t ↦ -(t *
        (factorTwoCenteredCrossCorrelation eR oLow t -
          factorTwoCenteredCrossCorrelation oLow eR t)) by
      funext t
      unfold factorTwoP67ResidualAlternatingCrossDifference
      ring,
      intervalIntegral.integral_neg, heRow, neg_zero]
  have hoRow' : (∫ t : ℝ in 0..2,
      t * factorTwoP67ResidualAlternatingCrossDifference eLow oR t) = 0 := by
    simpa only [factorTwoP67ResidualAlternatingCrossDifference] using hoRow
  rw [show (fun t : ℝ ↦
      t * factorTwoP67ResidualAlternatingCrossSum eLow oLow eR oR t) =
      fun t ↦
        t * factorTwoP67ResidualAlternatingCrossDifference eLow oR t +
        t * factorTwoP67ResidualAlternatingCrossDifference eR oLow t by
    funext t
    unfold factorTwoP67ResidualAlternatingCrossSum
    ring,
    intervalIntegral.integral_add hoInt heInt, hoRow', heRow', add_zero]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
