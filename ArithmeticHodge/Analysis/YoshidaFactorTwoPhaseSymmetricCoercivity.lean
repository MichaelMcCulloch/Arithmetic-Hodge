import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEnvelope
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailCoercivity

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCoercivity

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointSingularCorrelation
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseTailCoercivity

/-!
# The symmetric factor-two phase coordinate

This file isolates the actual one-profile quadratic coordinate.  In
particular, the reflected endpoint pole is kept with its sign; replacing it
by an absolute-value envelope would introduce the logarithmic endpoint
potential and lose the desired mass-only constant.
-/

/-- Exact signed normal form of the symmetric perturbation. -/
theorem symmetricPerturbation_eq_regular_sub_pole_sub_primes
    (w : ℝ → ℝ) (hw : Continuous w) :
    factorTwoCenteredSymmetricPerturbation w =
        yoshidaEndpointA *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredForwardPhaseKernel w 0 1 0 t) +
          (∫ t : ℝ in 0..2,
            factorTwoCenteredReflectedDesingularizedPhaseKernel
              w 0 1 0 t) -
          (1 / 2 : ℝ) *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredPhaseCorrelation w 0 1 0 t / (2 - t)) -
          (Real.log 2 / Real.sqrt 2) *
            (∫ x : ℝ in -1..1, w x ^ 2) -
          (Real.log 3 / Real.sqrt 3) *
            factorTwoCenteredPhaseCorrelation w 0 1 0
              (factorTwoPrimeShift / yoshidaEndpointA) := by
  have h :=
    phase_symmetric_add_alternating_eq_regular_sub_pole_sub_primes
      w 0 hw continuous_zero 1 0
  have hz : factorTwoCenteredSymmetricPerturbation (0 : ℝ → ℝ) = 0 := by
    simp [factorTwoCenteredSymmetricPerturbation,
      centeredEndpointCorrelation]
  simpa [hz] using h

/-- The retained `p = 3` self-correlation is a half-mass contraction.  This
is the one-profile specialization of the complete phase estimate; in
particular it does not discard the fact that the two translated pieces are
disjoint at this lag. -/
theorem two_mul_abs_primeCorrelation_le_energy
    (w : ℝ → ℝ) (hw : Continuous w) :
    2 * |centeredEndpointCorrelation w
        (factorTwoPrimeShift / yoshidaEndpointA)| ≤
      ∫ x : ℝ in -1..1, w x ^ 2 := by
  have h := two_mul_abs_phaseCorrelation_primeShift_le_mass
    w 0 hw continuous_zero 1 0 (by norm_num)
  simpa [factorTwoCenteredPhaseCorrelation,
    centeredEndpointCorrelation] using h

/-- With its exact arithmetic coefficient, the retained prime atom still
costs at most half of the endpoint energy. -/
theorem abs_weighted_primeCorrelation_le_half_energy
    (w : ℝ → ℝ) (hw : Continuous w) :
    |(Real.log 3 / Real.sqrt 3) *
        centeredEndpointCorrelation w
          (factorTwoPrimeShift / yoshidaEndpointA)| ≤
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x ^ 2 := by
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let C : ℝ := centeredEndpointCorrelation w
    (factorTwoPrimeShift / yoshidaEndpointA)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  have hC := two_mul_abs_primeCorrelation_le_energy w hw
  have hcoeff0 : 0 ≤ Real.log 3 / Real.sqrt 3 := by positivity
  have hcoeff1 : Real.log 3 / Real.sqrt 3 < 1 :=
    factorTwoPrimeThreeWeight_lt_one
  change 2 * |C| ≤ E at hC
  rw [abs_mul, abs_of_nonneg hcoeff0]
  change (Real.log 3 / Real.sqrt 3) * |C| ≤ (1 / 2 : ℝ) * E
  nlinarith [abs_nonneg C]

/-- The sharp Carleman half-pole together with the dyadic mass atom uses
strictly less than `13/10` of the full endpoint energy.  Thus their apparent
endpoint singularity alone cannot violate the desired `3/2` bound; the
remaining issue is the joint (not separately normed) interaction with the
retained prime translation. -/
theorem carlemanHalfPole_add_dyadicMass_lt_thirteen_tenths :
    Real.pi / 4 + Real.log 2 / Real.sqrt 2 < (13 / 10 : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtLower : (7 / 5 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hdyadic : Real.log 2 / Real.sqrt 2 < (1 / 2 : ℝ) := by
    rw [div_lt_iff₀ hsqrtPos]
    nlinarith
  have hpi : Real.pi / 4 < (63 / 80 : ℝ) := by
    have := Real.pi_lt_d2
    nlinarith
  nlinarith

/-! ## Reflection fold of the endpoint pole -/

/-- The additive-convolution section seen from the left endpoint.  After
reflection parity, this is exactly the correlation at the opposite-endpoint
lag `2 - t`. -/
def endpointFoldedCorrelation (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ p : ℝ in 0..t, w (-1 + (t - p)) * w (-1 + p)

/-- Even reflection turns the opposite-endpoint correlation into the
positive-sign endpoint convolution. -/
theorem centeredCorrelation_two_sub_eq_endpointFolded_of_even
    {w : ℝ → ℝ} (heven : Function.Even w) (t : ℝ) :
    centeredEndpointCorrelation w (2 - t) =
      endpointFoldedCorrelation w t := by
  unfold centeredEndpointCorrelation endpointFoldedCorrelation
  rw [show 1 - (2 - t) = -1 + t by ring]
  calc
    (∫ x : ℝ in -1..-1 + t, w (2 - t + x) * w x) =
        ∫ p : ℝ in 0..t,
          w (2 - t + (-1 + p)) * w (-1 + p) := by
      convert (intervalIntegral.integral_comp_add_left
        (a := (0 : ℝ)) (b := t)
        (fun x : ℝ ↦ w (2 - t + x) * w x) (-1)).symm using 1;
        ring_nf
    _ = ∫ p : ℝ in 0..t,
          w (-1 + (t - p)) * w (-1 + p) := by
      apply intervalIntegral.integral_congr
      intro p _hp
      change w (2 - t + (-1 + p)) * w (-1 + p) =
        w (-1 + (t - p)) * w (-1 + p)
      rw [show 2 - t + (-1 + p) = -(-1 + (t - p)) by ring,
        heven]

/-- Odd reflection gives the same endpoint convolution with the opposite
sign. -/
theorem centeredCorrelation_two_sub_eq_neg_endpointFolded_of_odd
    {w : ℝ → ℝ} (hodd : Function.Odd w) (t : ℝ) :
    centeredEndpointCorrelation w (2 - t) =
      -endpointFoldedCorrelation w t := by
  unfold centeredEndpointCorrelation endpointFoldedCorrelation
  rw [show 1 - (2 - t) = -1 + t by ring]
  calc
    (∫ x : ℝ in -1..-1 + t, w (2 - t + x) * w x) =
        ∫ p : ℝ in 0..t,
          w (2 - t + (-1 + p)) * w (-1 + p) := by
      convert (intervalIntegral.integral_comp_add_left
        (a := (0 : ℝ)) (b := t)
        (fun x : ℝ ↦ w (2 - t + x) * w x) (-1)).symm using 1;
        ring_nf
    _ = ∫ p : ℝ in 0..t,
          -(w (-1 + (t - p)) * w (-1 + p)) := by
      apply intervalIntegral.integral_congr
      intro p _hp
      change w (2 - t + (-1 + p)) * w (-1 + p) =
        -(w (-1 + (t - p)) * w (-1 + p))
      rw [show 2 - t + (-1 + p) = -(-1 + (t - p)) by ring,
        hodd]
      ring
    _ = -(∫ p : ℝ in 0..t,
          w (-1 + (t - p)) * w (-1 + p)) := by
      rw [← intervalIntegral.integral_neg]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCoercivity
