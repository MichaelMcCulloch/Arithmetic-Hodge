import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowMatrix

set_option autoImplicit false
set_option maxRecDepth 100000

open Matrix
open scoped BigOperators ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanOddMatrix

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseOddRealDecomposition
open YoshidaOddModeRegularity
open YoshidaSectionSixAnalytic
open YoshidaWeightedTailBounds

/-!
# Concrete clean odd low matrix

The canonical ten-dimensional odd synthesis is pointwise real and vanishes
at both clipped endpoints.  The endpoint-clean bridge therefore identifies
its clean quadratic with the real clipped local-critical Gram matrix, divided
by the endpoint scale.
-/

/-- The concrete `10 × 10` clean matrix on the canonical odd low modes. -/
def factorTwoConcreteOddCleanMatrix :
    Matrix YoshidaOddIndex YoshidaOddIndex ℝ :=
  fun i j ↦
    (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      (yoshidaClippedOddLowMode yoshidaA i)
      (yoshidaClippedOddLowMode yoshidaA j)).re / yoshidaA

/-- Hermitian symmetry of the clipped critical form makes the real clean
matrix symmetric. -/
theorem factorTwoConcreteOddCleanMatrix_isHermitian :
    factorTwoConcreteOddCleanMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos
    (yoshidaClippedOddLowMode yoshidaA i)
    (yoshidaClippedOddLowMode yoshidaA j)
  simpa only [factorTwoConcreteOddCleanMatrix, star_trivial] using
    congrArg (fun z : ℂ ↦ z.re / yoshidaA) h

private def factorTwoOddLowSmoothSynthesis
    (o : YoshidaOddIndex → ℝ) : YoshidaClippedSmooth yoshidaA :=
  ∑ i, ((o i : ℝ) : ℂ) • yoshidaClippedOddLowMode yoshidaA i

private def factorTwoOddLowPeriodicSynthesis
    (o : YoshidaOddIndex → ℝ) : YoshidaClippedPeriodicCore yoshidaA :=
  ⟨factorTwoOddLowSmoothSynthesis o,
    yoshidaClippedOddLow_sum_mem_periodicCore yoshidaA_pos
      (fun i ↦ ((o i : ℝ) : ℂ))⟩

private theorem factorTwoOddLowSmoothSynthesis_im_zero
    (o : YoshidaOddIndex → ℝ) (x : ℝ) :
    (factorTwoOddLowSmoothSynthesis o x).im = 0 := by
  classical
  simp only [factorTwoOddLowSmoothSynthesis, Submodule.coe_sum,
    Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [oddLowMode_im_zero]
    ring

private theorem factorTwoOddLowSmoothSynthesis_left_endpoint
    (o : YoshidaOddIndex → ℝ) :
    factorTwoOddLowSmoothSynthesis o (-yoshidaA) = 0 := by
  classical
  unfold factorTwoOddLowSmoothSynthesis
  simp only [Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  simp only [Submodule.coe_smul, Pi.smul_apply]
  rw [yoshidaClippedOddLowMode,
    yoshidaClippedOddMode_left_endpoint yoshidaA_pos]
  simp

private theorem factorTwoOddLowSmoothSynthesis_right_endpoint
    (o : YoshidaOddIndex → ℝ) :
    factorTwoOddLowSmoothSynthesis o yoshidaA = 0 := by
  classical
  unfold factorTwoOddLowSmoothSynthesis
  simp only [Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  simp only [Submodule.coe_smul, Pi.smul_apply]
  rw [yoshidaClippedOddLowMode,
    yoshidaClippedOddMode_right_endpoint yoshidaA_pos]
  simp

private theorem factorTwoOddLowPeriodicSynthesis_centered_re
    (o : YoshidaOddIndex → ℝ) :
    centeredRescale yoshidaA (fun x ↦
      (((factorTwoOddLowPeriodicSynthesis o :
        YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) x).re) =
      factorTwoOddLowSynthesis o := by
  classical
  funext x
  simp only [factorTwoOddLowPeriodicSynthesis,
    factorTwoOddLowSmoothSynthesis, factorTwoOddLowSynthesis,
    factorTwoCenteredOddLowProfile, centeredRescale, Submodule.coe_sum,
    Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

private theorem factorTwoOddLowSmoothSynthesis_critical_value
    (o : YoshidaOddIndex → ℝ) :
    clippedCriticalFormValue yoshidaA yoshidaA_pos
        (factorTwoOddLowSmoothSynthesis o) =
      ∑ i, ∑ j,
        o i * o j *
          (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
            (yoshidaClippedOddLowMode yoshidaA i)
            (yoshidaClippedOddLowMode yoshidaA j)).re := by
  classical
  simp only [clippedCriticalFormValue, factorTwoOddLowSmoothSynthesis,
    map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul,
    Complex.conj_ofReal, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The clean quadratic of the canonical real odd low synthesis is exactly
the quadratic form of `factorTwoConcreteOddCleanMatrix`. -/
theorem factorTwoConcreteOddCleanMatrix_represents
    (o : YoshidaOddIndex → ℝ) :
    yoshidaEndpointOddCleanQuadratic (factorTwoOddLowSynthesis o) =
      o ⬝ᵥ (factorTwoConcreteOddCleanMatrix *ᵥ o) := by
  let r := factorTwoOddLowPeriodicSynthesis o
  have hbridge :=
    clippedCriticalFormValue_eq_endpoint_mul_clean_of_real_endpoints_zero
      r
      (factorTwoOddLowSmoothSynthesis_im_zero o)
      (factorTwoOddLowSmoothSynthesis_left_endpoint o)
      (factorTwoOddLowSmoothSynthesis_right_endpoint o)
  dsimp only [r] at hbridge
  have hbridge' :
      clippedCriticalFormValue yoshidaA yoshidaA_pos
          (factorTwoOddLowSmoothSynthesis o) =
        yoshidaA *
          yoshidaEndpointOddCleanQuadratic (factorTwoOddLowSynthesis o) := by
    rw [← factorTwoOddLowPeriodicSynthesis_centered_re]
    simpa only [YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
      YoshidaWeightedTailBounds.yoshidaA] using hbridge
  have hvalue := factorTwoOddLowSmoothSynthesis_critical_value o
  rw [hvalue] at hbridge'
  have hmatrix :
      yoshidaA *
          (o ⬝ᵥ (factorTwoConcreteOddCleanMatrix *ᵥ o)) =
        ∑ i, ∑ j,
          o i * o j *
            (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
              (yoshidaClippedOddLowMode yoshidaA i)
              (yoshidaClippedOddLowMode yoshidaA j)).re := by
    simp only [dotProduct, mulVec, factorTwoConcreteOddCleanMatrix]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    field_simp [yoshidaA_pos.ne']
  nlinarith [yoshidaA_pos]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanOddMatrix
