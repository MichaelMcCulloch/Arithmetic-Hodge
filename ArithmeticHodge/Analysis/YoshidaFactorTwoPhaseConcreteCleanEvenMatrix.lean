import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowMatrix

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open Matrix
open scoped BigOperators ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanEvenMatrix

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaSectionSixAnalytic
open YoshidaWeightedTailBounds

/-!
# Concrete clean endpoint-adapted even low matrix

The endpoint-adapted two-hundred-dimensional even synthesis is pointwise
real and vanishes at both clipped endpoints.  The endpoint-clean bridge
therefore identifies its clean quadratic with the real clipped
local-critical Gram matrix, divided by the endpoint scale.
-/

/-- The concrete `200 × 200` clean matrix on the endpoint-adapted even low
modes. -/
def factorTwoConcreteAdaptedEvenCleanMatrix :
    Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ :=
  fun i j ↦
    (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      (endpointAdaptedEvenLowMode i)
      (endpointAdaptedEvenLowMode j)).re / yoshidaA

/-- Hermitian symmetry of the clipped critical form makes the real clean
matrix symmetric. -/
theorem factorTwoConcreteAdaptedEvenCleanMatrix_isHermitian :
    factorTwoConcreteAdaptedEvenCleanMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos
    (endpointAdaptedEvenLowMode i)
    (endpointAdaptedEvenLowMode j)
  simpa only [factorTwoConcreteAdaptedEvenCleanMatrix, star_trivial] using
    congrArg (fun z : ℂ ↦ z.re / yoshidaA) h

private def factorTwoAdaptedEvenLowSmoothSynthesis
    (e : YoshidaEvenIndex → ℝ) : YoshidaClippedSmooth yoshidaA :=
  ∑ i, ((e i : ℝ) : ℂ) • endpointAdaptedEvenLowMode i

private def factorTwoAdaptedEvenLowPeriodicSynthesis
    (e : YoshidaEvenIndex → ℝ) : YoshidaClippedPeriodicCore yoshidaA :=
  ∑ i, ((e i : ℝ) : ℂ) • endpointAdaptedEvenLowModePeriodicCore i

private theorem factorTwoAdaptedEvenLowSmoothSynthesis_im_zero
    (e : YoshidaEvenIndex → ℝ) (x : ℝ) :
    (factorTwoAdaptedEvenLowSmoothSynthesis e x).im = 0 := by
  classical
  simp only [factorTwoAdaptedEvenLowSmoothSynthesis, Submodule.coe_sum,
    Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [endpointAdaptedEvenLowMode_im_zero]
    ring

private theorem factorTwoAdaptedEvenLowSmoothSynthesis_left_endpoint
    (e : YoshidaEvenIndex → ℝ) :
    factorTwoAdaptedEvenLowSmoothSynthesis e (-yoshidaA) = 0 := by
  classical
  unfold factorTwoAdaptedEvenLowSmoothSynthesis
  simp only [Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  simp only [Submodule.coe_smul, Pi.smul_apply]
  rw [endpointAdaptedEvenLowMode_apply_neg]
  simp

private theorem factorTwoAdaptedEvenLowSmoothSynthesis_right_endpoint
    (e : YoshidaEvenIndex → ℝ) :
    factorTwoAdaptedEvenLowSmoothSynthesis e yoshidaA = 0 := by
  classical
  unfold factorTwoAdaptedEvenLowSmoothSynthesis
  simp only [Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  simp only [Submodule.coe_smul, Pi.smul_apply]
  rw [endpointAdaptedEvenLowMode_apply_pos]
  simp

private theorem factorTwoAdaptedEvenLowPeriodicSynthesis_toSmooth
    (e : YoshidaEvenIndex → ℝ) :
    ((factorTwoAdaptedEvenLowPeriodicSynthesis e :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) =
        factorTwoAdaptedEvenLowSmoothSynthesis e := by
  rfl

private theorem factorTwoAdaptedEvenLowPeriodicSynthesis_centered_re
    (e : YoshidaEvenIndex → ℝ) :
    centeredRescale yoshidaA (fun x ↦
      (((factorTwoAdaptedEvenLowPeriodicSynthesis e :
        YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) x).re) =
      factorTwoAdaptedEvenLowSynthesis e := by
  classical
  funext x
  simp only [factorTwoAdaptedEvenLowPeriodicSynthesis,
    factorTwoAdaptedEvenLowSynthesis,
    factorTwoCenteredAdaptedEvenLowProfile, centeredRescale,
    endpointAdaptedEvenLowModePeriodicCore_toSmooth,
    Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem factorTwoAdaptedEvenLowSmoothSynthesis_centered_re
    (e : YoshidaEvenIndex → ℝ) :
    centeredRescale yoshidaA (fun x ↦
      (factorTwoAdaptedEvenLowSmoothSynthesis e x).re) =
      factorTwoAdaptedEvenLowSynthesis e := by
  rw [← factorTwoAdaptedEvenLowPeriodicSynthesis_toSmooth e]
  exact factorTwoAdaptedEvenLowPeriodicSynthesis_centered_re e

private theorem factorTwoAdaptedEvenLowSmoothSynthesis_critical_value
    (e : YoshidaEvenIndex → ℝ) :
    clippedCriticalFormValue yoshidaA yoshidaA_pos
        (factorTwoAdaptedEvenLowSmoothSynthesis e) =
      ∑ i, ∑ j,
        e i * e j *
          (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (endpointAdaptedEvenLowMode i)
            (endpointAdaptedEvenLowMode j)).re := by
  classical
  simp only [clippedCriticalFormValue,
    factorTwoAdaptedEvenLowSmoothSynthesis, map_sum, map_smul,
    map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Complex.conj_ofReal, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The clean quadratic of the endpoint-adapted real even low synthesis is
exactly the quadratic form of `factorTwoConcreteAdaptedEvenCleanMatrix`. -/
theorem factorTwoConcreteAdaptedEvenCleanMatrix_represents
    (e : YoshidaEvenIndex → ℝ) :
    yoshidaEndpointOddCleanQuadratic
        (factorTwoAdaptedEvenLowSynthesis e) =
      e ⬝ᵥ (factorTwoConcreteAdaptedEvenCleanMatrix *ᵥ e) := by
  let r : YoshidaClippedPeriodicCore
      YoshidaEndpointHyperbolicBound.yoshidaEndpointA :=
    factorTwoAdaptedEvenLowPeriodicSynthesis e
  have hrSmooth :
      ((r : YoshidaClippedPeriodicCore
          YoshidaEndpointHyperbolicBound.yoshidaEndpointA) :
        YoshidaClippedSmooth
          YoshidaEndpointHyperbolicBound.yoshidaEndpointA) =
        factorTwoAdaptedEvenLowSmoothSynthesis e := by
    simpa only [r, YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
      YoshidaWeightedTailBounds.yoshidaA] using
        factorTwoAdaptedEvenLowPeriodicSynthesis_toSmooth e
  have hreal : ∀ x : ℝ,
      (((r : YoshidaClippedPeriodicCore
          YoshidaEndpointHyperbolicBound.yoshidaEndpointA) :
        YoshidaClippedSmooth
          YoshidaEndpointHyperbolicBound.yoshidaEndpointA) x).im = 0 := by
    intro x
    rw [hrSmooth]
    exact factorTwoAdaptedEvenLowSmoothSynthesis_im_zero e x
  have hneg : ((r : YoshidaClippedPeriodicCore
      YoshidaEndpointHyperbolicBound.yoshidaEndpointA) :
      YoshidaClippedSmooth
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA)
        (-YoshidaEndpointHyperbolicBound.yoshidaEndpointA) = 0 := by
    rw [hrSmooth]
    simpa only [YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
      YoshidaWeightedTailBounds.yoshidaA] using
        factorTwoAdaptedEvenLowSmoothSynthesis_left_endpoint e
  have hpos : ((r : YoshidaClippedPeriodicCore
      YoshidaEndpointHyperbolicBound.yoshidaEndpointA) :
      YoshidaClippedSmooth
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA)
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA = 0 := by
    rw [hrSmooth]
    exact factorTwoAdaptedEvenLowSmoothSynthesis_right_endpoint e
  have hbridge :=
    clippedCriticalFormValue_eq_endpoint_mul_clean_of_real_endpoints_zero
      r hreal hneg hpos
  have hcenter :
      centeredRescale YoshidaEndpointHyperbolicBound.yoshidaEndpointA
        (fun x ↦ (factorTwoAdaptedEvenLowSmoothSynthesis e x).re) =
          factorTwoAdaptedEvenLowSynthesis e := by
    simpa only [YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
      YoshidaWeightedTailBounds.yoshidaA] using
        factorTwoAdaptedEvenLowSmoothSynthesis_centered_re e
  have hbridge' :
      clippedCriticalFormValue yoshidaA yoshidaA_pos
          (factorTwoAdaptedEvenLowSmoothSynthesis e) =
        yoshidaA * yoshidaEndpointOddCleanQuadratic
          (factorTwoAdaptedEvenLowSynthesis e) := by
    rw [hrSmooth, hcenter] at hbridge
    simpa only [
      YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
      YoshidaWeightedTailBounds.yoshidaA] using hbridge
  have hvalue := factorTwoAdaptedEvenLowSmoothSynthesis_critical_value e
  rw [hvalue] at hbridge'
  have hmatrix :
      yoshidaA *
          (e ⬝ᵥ (factorTwoConcreteAdaptedEvenCleanMatrix *ᵥ e)) =
        ∑ i, ∑ j,
          e i * e j *
            (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
              (endpointAdaptedEvenLowMode i)
              (endpointAdaptedEvenLowMode j)).re := by
    simp only [dotProduct, mulVec,
      factorTwoConcreteAdaptedEvenCleanMatrix]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    field_simp [yoshidaA_pos.ne']
  nlinarith [yoshidaA_pos]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
