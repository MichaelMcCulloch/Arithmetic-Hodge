import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenCleanKernelStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenPerturbationKernelStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenEndpointLowerModelStructural

noncomputable section

open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointSingularCorrelation
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenCleanKernelStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenGlobalRemainderStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenPerturbationKernelStructural
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaRegularKernelSchur

/-!
# A structural lower model for the two P6 endpoint signs

Both endpoint signs are reduced to the same exact degree-six data.  The clean
regular-kernel envelope and the pole-free perturbation envelope are each
charged once to the full profile energy.  This theorem is profile-level: the
later `P0/P2/P4/P6` matrix calculation is only an evaluation of this model.
-/

/-- Exact degree-six part of the clean endpoint quadratic. -/
def factorTwoP6EvenCleanPolynomialModel (e : ℝ → ℝ) : ℝ :=
  centeredRawLogEnergy e / 4 +
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * e x ^ 2) -
    yoshidaEndpointScalarMassLoss * (∫ x : ℝ in -1..1, e x ^ 2) -
    yoshidaEndpointA *
      (2 * (∫ t : ℝ in 0..2,
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
          centeredEndpointCorrelation e t)) +
    yoshidaEndpointHyperbolicQuadratic (fun x ↦ (e x : ℂ))

/-- Exact degree-six-plus-poles part of the symmetric perturbation. -/
def factorTwoP6EvenPerturbationPolynomialModel (e : ℝ → ℝ) : ℝ :=
  (∫ t : ℝ in 0..2,
      poleFreeKernelPolynomial6 t * centeredEndpointCorrelation e t) +
    (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t * centeredEndpointCorrelation e t) -
    (Real.log 2 / Real.sqrt 2) * centeredEndpointCorrelation e 0 -
    (Real.log 3 / Real.sqrt 3) * centeredEndpointCorrelation e
      (factorTwoPrimeShift / yoshidaEndpointA)

/-- The combined global energy charge. -/
def factorTwoP6EvenEndpointEnergyCharge (e : ℝ → ℝ) : ℝ :=
  (yoshidaEndpointA / 250000 + 3 / 40000) *
    (∫ x : ℝ in -1..1, e x ^ 2)

/-- Endpoint-plus structural lower model. -/
def factorTwoP6EvenEndpointPlusLowerModel (e : ℝ → ℝ) : ℝ :=
  factorTwoP6EvenCleanPolynomialModel e +
    factorTwoP6EvenPerturbationPolynomialModel e -
    factorTwoP6EvenEndpointEnergyCharge e

/-- Endpoint-minus structural lower model. -/
def factorTwoP6EvenEndpointMinusLowerModel (e : ℝ → ℝ) : ℝ :=
  factorTwoP6EvenCleanPolynomialModel e -
    factorTwoP6EvenPerturbationPolynomialModel e -
    factorTwoP6EvenEndpointEnergyCharge e

private theorem clean_eq_polynomialModel_sub_error
    (e : ℝ → ℝ) (he : Continuous e) :
    yoshidaEndpointOddCleanQuadratic e =
      factorTwoP6EvenCleanPolynomialModel e -
        yoshidaEndpointA *
          oddCleanRegularEnvelopeError (centeredEndpointCorrelation e) := by
  have hregular :=
    re_yoshidaEndpointRegularQuadratic_eq_polynomial6_add_error e he
  unfold yoshidaEndpointOddCleanQuadratic
    factorTwoP6EvenCleanPolynomialModel
  dsimp only
  rw [hregular]
  ring

private theorem perturbation_eq_polynomialModel_add_error
    (e : ℝ → ℝ) (he : Continuous e) :
    factorTwoCenteredSymmetricPerturbation e =
      factorTwoP6EvenPerturbationPolynomialModel e +
        poleFreeAnalyticError (centeredEndpointCorrelation e) := by
  rw [factorTwoCenteredSymmetricPerturbation_eq_globalPolynomialKernel e he]
  unfold factorTwoP6EvenPerturbationPolynomialModel
  ring

/-- The plus endpoint dominates the common global lower model. -/
theorem factorTwoP6EvenEndpointPlusLowerModel_le_phaseDiagonal
    (e : ℝ → ℝ) (he : Continuous e) :
    factorTwoP6EvenEndpointPlusLowerModel e ≤
      factorTwoEndpointPhaseDiagonal e 1 := by
  let E : ℝ := ∫ x : ℝ in -1..1, e x ^ 2
  let cleanError : ℝ :=
    oddCleanRegularEnvelopeError (centeredEndpointCorrelation e)
  let perturbationError : ℝ :=
    poleFreeAnalyticError (centeredEndpointCorrelation e)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (e x))
  have hclean :=
    abs_oddCleanRegularEnvelopeError_centeredEndpointCorrelation_le_energy e he
  have hcleanUpper :
      yoshidaEndpointA * cleanError ≤
        yoshidaEndpointA * ((1 / 250000 : ℝ) * E) := by
    apply mul_le_mul_of_nonneg_left
    · exact (le_abs_self cleanError).trans hclean
    · exact yoshidaEndpointA_pos.le
  have hperturb :=
    poleFreeAnalyticError_centeredEndpointCorrelation_mem_energyInterval e he
  have hperturbLower :
      -(3 / 40000 : ℝ) * E ≤ perturbationError := by
    simpa only [E, perturbationError] using hperturb.1
  rw [factorTwoP6EvenEndpointPlusLowerModel,
    factorTwoEndpointPhaseDiagonal,
    clean_eq_polynomialModel_sub_error e he,
    perturbation_eq_polynomialModel_add_error e he]
  dsimp only [factorTwoP6EvenEndpointEnergyCharge, E, cleanError,
    perturbationError]
  linarith

/-- The minus endpoint dominates the common global lower model. -/
theorem factorTwoP6EvenEndpointMinusLowerModel_le_phaseDiagonal
    (e : ℝ → ℝ) (he : Continuous e) :
    factorTwoP6EvenEndpointMinusLowerModel e ≤
      factorTwoEndpointPhaseDiagonal e (-1) := by
  let E : ℝ := ∫ x : ℝ in -1..1, e x ^ 2
  let cleanError : ℝ :=
    oddCleanRegularEnvelopeError (centeredEndpointCorrelation e)
  let perturbationError : ℝ :=
    poleFreeAnalyticError (centeredEndpointCorrelation e)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (e x))
  have hclean :=
    abs_oddCleanRegularEnvelopeError_centeredEndpointCorrelation_le_energy e he
  have hcleanUpper :
      yoshidaEndpointA * cleanError ≤
        yoshidaEndpointA * ((1 / 250000 : ℝ) * E) := by
    apply mul_le_mul_of_nonneg_left
    · exact (le_abs_self cleanError).trans hclean
    · exact yoshidaEndpointA_pos.le
  have hperturb :=
    poleFreeAnalyticError_centeredEndpointCorrelation_mem_energyInterval e he
  have hperturbUpper :
      perturbationError ≤ (3 / 40000 : ℝ) * E := by
    simpa only [E, perturbationError] using hperturb.2
  rw [factorTwoP6EvenEndpointMinusLowerModel,
    factorTwoEndpointPhaseDiagonal,
    clean_eq_polynomialModel_sub_error e he,
    perturbation_eq_polynomialModel_add_error e he]
  dsimp only [factorTwoP6EvenEndpointEnergyCharge, E, cleanError,
    perturbationError]
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenEndpointLowerModelStructural
