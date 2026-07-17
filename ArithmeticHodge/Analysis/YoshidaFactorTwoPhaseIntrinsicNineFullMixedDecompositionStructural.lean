import ArithmeticHodge.Analysis.ShiftedLegendreLogEnergyOrthogonalProjection
import ArithmeticHodge.Analysis.ShiftedLogKernelTriangular
import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineResidualDecompositionStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreBasis
open ShiftedLegendreOrthogonality
open ShiftedLegendreLogKernel
open ShiftedLogKernelCrossEnergy
open ShiftedLogKernelTriangular
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialBound
open YoshidaEndpointPullbackLipschitz
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseHigherLegendreStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicRemainderBound
open YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicNineResidualDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseP678CombinedResidualSchurStructural
open YoshidaFactorTwoPhaseP8StructuralReserve
open YoshidaRegularKernelSchur
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

/-! ## The honest surviving cutoff-nine aggregate -/

/-- The five nonpolynomial families which genuinely survive between a
cutoff-nine low pair and its moment-nine residual pair.  The endpoint
potential, reflected pole, clean regular quadratic, hyperbolic correction,
and retained `p = 3` lag remain in one signed expression.  In particular,
this definition makes no triangle-inequality split between them. -/
def factorTwoIntrinsicNineNonpolynomialMixed
    (eLow oLow eR oR : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ((∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * eLow x * eR x) +
      ∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * oLow x * oR x) -
    (1 / 4 : ℝ) *
      ((∫ t : ℝ in 0..2,
          factorTwoCenteredPhaseCorrelation
              (eLow + eR) (oLow + oR) a (-b) t / (2 - t)) -
        (∫ t : ℝ in 0..2,
          factorTwoCenteredPhaseCorrelation eLow oLow a (-b) t / (2 - t)) -
        ∫ t : ℝ in 0..2,
          factorTwoCenteredPhaseCorrelation eR oR a (-b) t / (2 - t)) -
    (yoshidaEndpointA / 2) *
      ((((yoshidaEndpointRegularQuadratic
            (fun x ↦ (((eLow + eR) x : ℝ) : ℂ))).re -
          (yoshidaEndpointRegularQuadratic
            (fun x ↦ (eLow x : ℂ))).re -
          (yoshidaEndpointRegularQuadratic
            (fun x ↦ (eR x : ℂ))).re) +
        ((yoshidaEndpointRegularQuadratic
            (fun x ↦ (((oLow + oR) x : ℝ) : ℂ))).re -
          (yoshidaEndpointRegularQuadratic
            (fun x ↦ (oLow x : ℂ))).re -
          (yoshidaEndpointRegularQuadratic
            (fun x ↦ (oR x : ℂ))).re))) +
    (1 / 2 : ℝ) *
      ((yoshidaEndpointHyperbolicQuadratic
            (fun x ↦ (((eLow + eR) x : ℝ) : ℂ)) -
          yoshidaEndpointHyperbolicQuadratic (fun x ↦ (eLow x : ℂ)) -
          yoshidaEndpointHyperbolicQuadratic (fun x ↦ (eR x : ℂ))) +
        (yoshidaEndpointHyperbolicQuadratic
            (fun x ↦ (((oLow + oR) x : ℝ) : ℂ)) -
          yoshidaEndpointHyperbolicQuadratic (fun x ↦ (oLow x : ℂ)) -
          yoshidaEndpointHyperbolicQuadratic (fun x ↦ (oR x : ℂ)))) -
    (Real.log 3 / (2 * Real.sqrt 3)) *
      (factorTwoCenteredPhaseCorrelation
          (eLow + eR) (oLow + oR) a b
            (factorTwoPrimeShift / yoshidaEndpointA) -
        factorTwoCenteredPhaseCorrelation eLow oLow a b
          (factorTwoPrimeShift / yoshidaEndpointA) -
        factorTwoCenteredPhaseCorrelation eR oR a b
          (factorTwoPrimeShift / yoshidaEndpointA))

set_option maxHeartbeats 800000 in
/-- For transported low polynomials below the moment cutoff, the complete
endpoint low--residual half-cross is the nonsingular regular half-cross plus
exactly the five-family nonpolynomial aggregate.  The raw logarithmic and
both ordinary `L²` rows have vanished structurally. -/
theorem factorTwoEndpointLowTailMixed_centeredPolynomialLift_eq
    (pE pO : ℝ[X]) (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 9)
    (hoGap : centeredLegendreMomentsVanishBelow oR 9)
    (hpEdeg : pE.natDegree < 9) (hpOdeg : pO.natDegree < 9)
    (a b : ℝ) :
    factorTwoEndpointLowTailMixed
        (centeredPolynomialLift pE) eR
        (centeredPolynomialLift pO) oR a b =
      (1 / 2 : ℝ) * (∫ t : ℝ in 0..2,
        factorTwoP67ResidualSmoothMixedIntegrand
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          eR oR a b t) +
        factorTwoIntrinsicNineNonpolynomialMixed
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          eR oR a b := by
  let eLow : ℝ → ℝ := centeredPolynomialLift pE
  let oLow : ℝ → ℝ := centeredPolynomialLift pO
  have heLowc : Continuous eLow := by
    dsimp only [eLow, centeredPolynomialLift]
    have hp : Continuous (fun x : ℝ ↦ pE.eval x) := by
      rw [continuous_iff_continuousAt]
      intro x
      exact (pE.hasDerivAt x).continuousAt
    exact hp.comp ((continuous_id.add continuous_const).div_const 2)
  have hoLowc : Continuous oLow := by
    dsimp only [oLow, centeredPolynomialLift]
    have hp : Continuous (fun x : ℝ ↦ pO.eval x) := by
      rw [continuous_iff_continuousAt]
      intro x
      exact (pO.hasDerivAt x).continuousAt
    exact hp.comp ((continuous_id.add continuous_const).div_const 2)
  have heRaw := centeredRawLogEnergy_centeredPolynomialLift_add_tail
    pE eR heRc heLocal heGap hpEdeg
  have hoRaw := centeredRawLogEnergy_centeredPolynomialLift_add_tail
    pO oR hoRc hoLocal hoGap hpOdeg
  have heMassZero := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    pE eR heRc heGap hpEdeg
  have hoMassZero := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    pO oR hoRc hoGap hpOdeg
  have hePotential := integral_endpointPotential_add_sq eLow eR heLowc heRc
  have hoPotential := integral_endpointPotential_add_sq oLow oR hoLowc hoRc
  have heMass := integral_add_sq eLow eR heLowc heRc
  have hoMass := integral_add_sq oLow oR hoLowc hoRc
  have hRegular := factorTwoIntrinsicRegularPhaseBlock_add_add_eq
    eLow oLow eR oR heLowc hoLowc heRc hoRc a b
  have hPhase := factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
    eLow eR oLow oR heLowc heRc hoLowc hoRc a b
  have hFull := factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
    (eLow + eR) (oLow + oR) (heLowc.add heRc) (hoLowc.add hoRc) a b
  have hLow := factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
    eLow oLow heLowc hoLowc a b
  have hResidual :=
    factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
      eR oR heRc hoRc a b
  rw [hFull, hLow, hResidual] at hPhase
  unfold factorTwoIntrinsicProtectedBlock factorTwoIntrinsicPotentialEnergy
    factorTwoIntrinsicSignedRemainder factorTwoIntrinsicEnergy at hPhase
  simp only [Pi.add_apply] at hPhase
  unfold factorTwoIntrinsicRegularPhaseBlock at hRegular
  rw [heRaw, hoRaw, hePotential, hoPotential, heMass, hoMass,
    hRegular, heMassZero, hoMassZero] at hPhase
  unfold factorTwoIntrinsicNineNonpolynomialMixed
  dsimp only [eLow, oLow] at hPhase
  simp only [Pi.add_apply] at hPhase ⊢
  ring_nf at hPhase ⊢
  linarith

/-! ## Intrinsic-coordinate specialization -/

/-- The even cutoff-nine intrinsic profile as a unit-interval polynomial. -/
def factorTwoIntrinsicNineEvenPolynomial
    (c0 c2 c4 c6 c8 : ℝ) : ℝ[X] :=
  c0 • shiftedLegendreReal 0 + c2 • shiftedLegendreReal 2 +
    c4 • shiftedLegendreReal 4 + c6 • shiftedLegendreReal 6 +
    c8 • shiftedLegendreReal 8

/-- The odd cutoff-nine intrinsic profile as a unit-interval polynomial.
The signs convert the shifted odd convention to the classical centered
Legendre convention used by the intrinsic coordinates. -/
def factorTwoIntrinsicNineOddPolynomial
    (c1 c3 c5 c7 : ℝ) : ℝ[X] :=
  (-c1) • shiftedLegendreReal 1 + (-c3) • shiftedLegendreReal 3 +
    (-c5) • shiftedLegendreReal 5 + (-c7) • shiftedLegendreReal 7

private theorem shiftedLegendreReal_zero_centered (x : ℝ) :
    (shiftedLegendreReal 0).eval ((x + 1) / 2) = centeredEvenP0 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredEvenP0]

private theorem shiftedLegendreReal_one_centered (x : ℝ) :
    (shiftedLegendreReal 1).eval ((x + 1) / 2) = -centeredP1 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredP1]
  ring

private theorem shiftedLegendreReal_two_centered (x : ℝ) :
    (shiftedLegendreReal 2).eval ((x + 1) / 2) = centeredEvenP2 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredEvenP2]
  ring

private theorem shiftedLegendreReal_three_centered (x : ℝ) :
    (shiftedLegendreReal 3).eval ((x + 1) / 2) = -centeredP3 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredP3]
  ring

private theorem shiftedLegendreReal_four_centered (x : ℝ) :
    (shiftedLegendreReal 4).eval ((x + 1) / 2) =
      factorTwoCenteredP4 x := by
  norm_num [factorTwoCenteredP4, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose]
  ring

private theorem shiftedLegendreReal_five_centered (x : ℝ) :
    (shiftedLegendreReal 5).eval ((x + 1) / 2) =
      -factorTwoCenteredP5 x := by
  norm_num [factorTwoCenteredP5, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose]
  ring

theorem centeredPolynomialLift_intrinsicNineEvenPolynomial
    (c0 c2 c4 c6 c8 : ℝ) :
    centeredPolynomialLift
        (factorTwoIntrinsicNineEvenPolynomial c0 c2 c4 c6 c8) =
      factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8 := by
  funext x
  unfold factorTwoIntrinsicNineEvenPolynomial centeredPolynomialLift
  simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
  rw [shiftedLegendreReal_zero_centered,
    shiftedLegendreReal_two_centered, shiftedLegendreReal_four_centered]
  unfold factorTwoIntrinsicNineEvenProfile factorTwoIntrinsicEightEvenProfile
    factorTwoIntrinsicSixEvenTail factorTwoEvenStructuralLowProfile
    factorTwoCenteredP6 factorTwoCenteredP8
  simp only [Pi.add_apply]

theorem centeredPolynomialLift_intrinsicNineOddPolynomial
    (c1 c3 c5 c7 : ℝ) :
    centeredPolynomialLift
        (factorTwoIntrinsicNineOddPolynomial c1 c3 c5 c7) =
      factorTwoIntrinsicNineOddProfile c1 c3 c5 c7 := by
  funext x
  unfold factorTwoIntrinsicNineOddPolynomial centeredPolynomialLift
  simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
  rw [shiftedLegendreReal_one_centered,
    shiftedLegendreReal_three_centered, shiftedLegendreReal_five_centered]
  unfold factorTwoIntrinsicNineOddProfile factorTwoIntrinsicEightOddProfile
    factorTwoIntrinsicSixOddTail factorTwoOddStructuralLowProfile
    factorTwoCenteredP7
  simp only [Pi.add_apply]
  ring

private theorem factorTwoIntrinsicNineEvenProfile_eq_lower_add_upper
    (c0 c2 c4 c6 c8 : ℝ) :
    factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8 =
      (factorTwoEvenStructuralLowProfile c0 c2 +
          factorTwoIntrinsicSixEvenTail c4) +
        ((c6 • factorTwoCenteredP6) + (c8 • factorTwoCenteredP8)) := by
  funext x
  unfold factorTwoIntrinsicNineEvenProfile factorTwoIntrinsicEightEvenProfile
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem factorTwoIntrinsicNineOddProfile_eq_lower_add_upper
    (c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineOddProfile c1 c3 c5 c7 =
      factorTwoIntrinsicSixOddTail c1 c3 c5 +
        (c7 • factorTwoCenteredP7) := by
  funext x
  unfold factorTwoIntrinsicNineOddProfile factorTwoIntrinsicEightOddProfile
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Exact cutoff-nine production identity in intrinsic coordinates.  The
lower `P0,...,P5` smooth cross remains as one integral, the certified
`P6/P7/P8` border is the existing forward mixed symbol, and every other
genuinely surviving family is retained in `factorTwoIntrinsicNineNonpolynomialMixed`. -/
theorem factorTwoEndpointLowTailMixed_intrinsicNine_eq
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (hoRo : Function.Odd oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 9)
    (hoGap : centeredLegendreMomentsVanishBelow oR 9)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 a b : ℝ) :
    factorTwoEndpointLowTailMixed
        (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8) eR
        (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) oR a b =
      (1 / 2 : ℝ) * (∫ t : ℝ in 0..2,
        factorTwoP67ResidualSmoothMixedIntegrand
          (factorTwoEvenStructuralLowProfile c0 c2 +
            factorTwoIntrinsicSixEvenTail c4)
          (factorTwoIntrinsicSixOddTail c1 c3 c5)
          eR oR a b t) +
        factorTwoP678ResidualCombinedForwardMixed
          eR oR c6 c7 c8 a b +
        factorTwoIntrinsicNineNonpolynomialMixed
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7)
          eR oR a b := by
  let pE : ℝ[X] :=
    factorTwoIntrinsicNineEvenPolynomial c0 c2 c4 c6 c8
  let pO : ℝ[X] :=
    factorTwoIntrinsicNineOddPolynomial c1 c3 c5 c7
  let eLower : ℝ → ℝ :=
    factorTwoEvenStructuralLowProfile c0 c2 +
      factorTwoIntrinsicSixEvenTail c4
  let oLower : ℝ → ℝ := factorTwoIntrinsicSixOddTail c1 c3 c5
  let eUpper : ℝ → ℝ :=
    (c6 • factorTwoCenteredP6) + (c8 • factorTwoCenteredP8)
  let oUpper : ℝ → ℝ := c7 • factorTwoCenteredP7
  have hpEdeg : pE.natDegree < 9 := by
    dsimp only [pE, factorTwoIntrinsicNineEvenPolynomial]
    have hdeg : (c0 • shiftedLegendreReal 0 + c2 • shiftedLegendreReal 2 +
        c4 • shiftedLegendreReal 4 + c6 • shiftedLegendreReal 6 +
        c8 • shiftedLegendreReal 8).natDegree ≤ 8 := by
      compute_degree
    omega
  have hpOdeg : pO.natDegree < 9 := by
    dsimp only [pO, factorTwoIntrinsicNineOddPolynomial]
    have hdeg : ((-c1) • shiftedLegendreReal 1 +
        (-c3) • shiftedLegendreReal 3 +
        (-c5) • shiftedLegendreReal 5 +
        (-c7) • shiftedLegendreReal 7).natDegree ≤ 7 := by
      compute_degree
    omega
  have heLowerc : Continuous eLower := by
    dsimp only [eLower, factorTwoIntrinsicSixEvenTail]
    exact (continuous_factorTwoEvenStructuralLowProfile c0 c2).add
      (continuous_const.mul continuous_factorTwoCenteredP4)
  have hoLowerc : Continuous oLower := by
    dsimp only [oLower, factorTwoIntrinsicSixOddTail]
    exact (continuous_factorTwoOddStructuralLowProfile c1 c3).add
      (continuous_const.mul continuous_factorTwoCenteredP5)
  have heUpperc : Continuous eUpper := by
    dsimp only [eUpper]
    exact (continuous_factorTwoCenteredP6.const_smul c6).add
      (continuous_factorTwoCenteredP8.const_smul c8)
  have hoUpperc : Continuous oUpper := by
    dsimp only [oUpper]
    exact continuous_factorTwoCenteredP7.const_smul c7
  have hBase := factorTwoEndpointLowTailMixed_centeredPolynomialLift_eq
    pE pO eR oR heRc hoRc heLocal hoLocal heGap hoGap
      hpEdeg hpOdeg a b
  have hePoly := centeredPolynomialLift_intrinsicNineEvenPolynomial
    c0 c2 c4 c6 c8
  have hoPoly := centeredPolynomialLift_intrinsicNineOddPolynomial
    c1 c3 c5 c7
  dsimp only [pE, pO] at hBase
  rw [hePoly, hoPoly] at hBase
  have hSplit :=
    integral_factorTwoP67ResidualSmoothMixedIntegrand_add_low_eq
      eLower eUpper oLower oUpper eR oR
      heLowerc heUpperc hoLowerc hoUpperc heRc hoRc a b
  have hUpper := integral_factorTwoP678ResidualSmoothMixedIntegrand_eq
    eR oR heRc hoRc hoRo heGap hoGap c6 c7 c8 a b
  have heProfile := factorTwoIntrinsicNineEvenProfile_eq_lower_add_upper
    c0 c2 c4 c6 c8
  have hoProfile := factorTwoIntrinsicNineOddProfile_eq_lower_add_upper
    c1 c3 c5 c7
  have hMixed :
      (∫ t : ℝ in 0..2,
        factorTwoP67ResidualSmoothMixedIntegrand
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7)
          eR oR a b t) =
        (∫ t : ℝ in 0..2,
          factorTwoP67ResidualSmoothMixedIntegrand
            eLower oLower eR oR a b t) +
          2 * factorTwoP678ResidualCombinedForwardMixed
            eR oR c6 c7 c8 a b := by
    rw [heProfile, hoProfile]
    dsimp only [eLower, eUpper, oLower, oUpper] at hSplit hUpper ⊢
    rw [hSplit, hUpper]
  rw [hMixed] at hBase
  dsimp only [eLower, oLower] at hBase ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
