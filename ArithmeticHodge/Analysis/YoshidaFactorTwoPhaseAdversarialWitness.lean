import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseAdversarialWitness

noncomputable section

open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoPhaseFullProfile
open YoshidaRegularKernelSchur

/-!
# Adversarial test of the separated low/tail correction

The exact full-profile decomposition does not make its isolated correction
positive.  This file gives an endpoint-zero odd polynomial for which the
correction is strictly negative after an opposite copy is placed in the
second slot.  It does not claim that these two slots are Fourier-orthogonal,
and therefore does not refute the channel-radius conjecture.  It rules out a
universal proof which simply discards the pure-tail term and asks the
remaining correction to be nonnegative.
-/

theorem yoshidaEndpointOddCleanQuadratic_neg (w : ℝ → ℝ) :
    yoshidaEndpointOddCleanQuadratic (-w) =
      yoshidaEndpointOddCleanQuadratic w := by
  have hraw : centeredRawLogEnergy (-w) = centeredRawLogEnergy w := by
    unfold centeredRawLogEnergy
    apply intervalIntegral.integral_congr
    intro x _hx
    apply intervalIntegral.integral_congr
    intro y _hy
    simp only [Pi.neg_apply]
    congr 1
    ring
  have hregular :
      yoshidaEndpointRegularQuadratic (fun x ↦ ((-w x : ℝ) : ℂ)) =
        yoshidaEndpointRegularQuadratic (fun x ↦ ((w x : ℝ) : ℂ)) := by
    unfold yoshidaEndpointRegularQuadratic
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with p
    push_cast
    simp
  have hhyperbolic :
      yoshidaEndpointHyperbolicQuadratic
          (fun x ↦ ((-w x : ℝ) : ℂ)) =
        yoshidaEndpointHyperbolicQuadratic
          (fun x ↦ ((w x : ℝ) : ℂ)) := by
    unfold yoshidaEndpointHyperbolicQuadratic
    rw [show (fun x : ℝ ↦
        (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * ((-w x : ℝ) : ℂ)) =
          fun x ↦ -((Real.cosh (yoshidaEndpointA * x / 2) : ℂ) *
            ((w x : ℝ) : ℂ)) by
      funext x
      push_cast
      ring,
      show (fun x : ℝ ↦
        (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * ((-w x : ℝ) : ℂ)) =
          fun x ↦ -((Real.sinh (yoshidaEndpointA * x / 2) : ℂ) *
            ((w x : ℝ) : ℂ)) by
      funext x
      push_cast
      ring,
      intervalIntegral.integral_neg, intervalIntegral.integral_neg,
      Complex.normSq_neg, Complex.normSq_neg]
  unfold yoshidaEndpointOddCleanQuadratic
  dsimp only
  simp only [Pi.neg_apply]
  rw [hraw, hregular, hhyperbolic]
  simp only [neg_sq]

@[simp] theorem yoshidaEndpointOddCleanQuadratic_zero :
    yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
  unfold yoshidaEndpointOddCleanQuadratic centeredRawLogEnergy
    yoshidaEndpointRegularQuadratic yoshidaEndpointHyperbolicQuadratic
  simp

theorem factorTwoCenteredCleanPolarization_neg_right (w : ℝ → ℝ) :
    factorTwoCenteredCleanPolarization w (-w) =
      -yoshidaEndpointOddCleanQuadratic w := by
  unfold factorTwoCenteredCleanPolarization
  rw [yoshidaEndpointOddCleanQuadratic_neg]
  have hzero : yoshidaEndpointOddCleanQuadratic (w + -w) = 0 := by
    convert yoshidaEndpointOddCleanQuadratic_zero using 2
    ext x
    simp
  rw [hzero]
  ring

/-- Any strictly positive clean direction makes the legacy separated
low/tail correction negative when an opposite copy is put in the tail slot.
This algebraic obstruction is why a sharp assembly must retain the pure tail
term and use a block-Schur inequality instead of assigning a sign to the
correction alone. -/
theorem lowTailCorrection_neg_of_clean_pos
    (w : ℝ → ℝ)
    (hclean : 0 < yoshidaEndpointOddCleanQuadratic w) :
    factorTwoEndpointLowTailCorrection w (-w) 0 0 0 0 < 0 := by
  unfold factorTwoEndpointLowTailCorrection
  rw [factorTwoCenteredCleanPolarization_neg_right]
  simp only [factorTwoCenteredCleanPolarization,
    yoshidaEndpointOddCleanQuadratic_zero, zero_mul, add_zero, sub_zero,
    zero_div]
  linarith

/-- A polynomial profile which is odd and vanishes at both endpoints. -/
def endpointZeroOddCubic (x : ℝ) : ℝ := x * (1 - x ^ 2)

theorem endpointZeroOddCubic_continuous : Continuous endpointZeroOddCubic := by
  unfold endpointZeroOddCubic
  fun_prop

theorem endpointZeroOddCubic_odd : Function.Odd endpointZeroOddCubic := by
  intro x
  unfold endpointZeroOddCubic
  ring

@[simp] theorem endpointZeroOddCubic_neg_one : endpointZeroOddCubic (-1) = 0 := by
  norm_num [endpointZeroOddCubic]

@[simp] theorem endpointZeroOddCubic_one : endpointZeroOddCubic 1 = 0 := by
  norm_num [endpointZeroOddCubic]

private def endpointZeroOddCubicPullbackPolynomial : Polynomial ℝ :=
  -(Polynomial.C 4 * Polynomial.X) +
    Polynomial.C 12 * Polynomial.X ^ 2 -
    Polynomial.C 8 * Polynomial.X ^ 3

private theorem endpointZeroOddCubic_centeredPullback_eq_eval
    (t : unitInterval) :
    centeredPullback endpointZeroOddCubic (t : ℝ) =
      endpointZeroOddCubicPullbackPolynomial.eval (t : ℝ) := by
  unfold centeredPullback endpointZeroOddCubic
    endpointZeroOddCubicPullbackPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  ring

private theorem endpointZeroOddCubic_memLp :
    MemLp (fun t : unitInterval ↦
      centeredPullback endpointZeroOddCubic (t : ℝ)) 2 := by
  have hfcont : Continuous (fun t : unitInterval ↦
      centeredPullback endpointZeroOddCubic (t : ℝ)) := by
    unfold centeredPullback
    exact endpointZeroOddCubic_continuous.comp (by fun_prop)
  exact hfcont.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem endpointZeroOddCubic_logEnergy_integrable :
    Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦
        centeredPullback endpointZeroOddCubic (t : ℝ))) := by
  have h := integrable_unitIntervalRawLogEnergyIntegrand_polynomial
    endpointZeroOddCubicPullbackPolynomial
  have heq : (fun t : unitInterval ↦
      centeredPullback endpointZeroOddCubic (t : ℝ)) =
        (fun t : unitInterval ↦
          endpointZeroOddCubicPullbackPolynomial.eval (t : ℝ)) := by
    funext t
    exact endpointZeroOddCubic_centeredPullback_eq_eval t
  rw [heq]
  exact h

private theorem endpointZeroOddCubic_sq_integral_pos :
    0 < ∫ x : ℝ in -1..1, endpointZeroOddCubic x ^ 2 := by
  have hcont : Continuous (fun x : ℝ ↦ endpointZeroOddCubic x ^ 2) :=
    endpointZeroOddCubic_continuous.pow 2
  apply intervalIntegral.integral_pos (by norm_num)
  · exact hcont.continuousOn
  · intro x _hx
    exact sq_nonneg _
  · refine ⟨1 / 2, by norm_num, ?_⟩
    norm_num [endpointZeroOddCubic]

theorem endpointZeroOddCubic_clean_pos :
    0 < yoshidaEndpointOddCleanQuadratic endpointZeroOddCubic := by
  have hreserve := yoshidaEndpointOddCleanQuadratic_coercive
    endpointZeroOddCubic endpointZeroOddCubic_continuous
    endpointZeroOddCubic_memLp endpointZeroOddCubic_logEnergy_integrable
    endpointZeroOddCubic_odd
    (intervalIntegrable_endpointPotential_mul_sq endpointZeroOddCubic
      endpointZeroOddCubic_continuous)
  have hmass := endpointZeroOddCubic_sq_integral_pos
  have hgap : 0 < 7 / 5 - yoshidaEndpointOddSharpMassLoss :=
    sub_pos.mpr yoshidaEndpointOddSharpMassLoss_lt_seven_fifths
  have hproduct : 0 < (7 / 5 - yoshidaEndpointOddSharpMassLoss) *
      (∫ x : ℝ in -1..1, endpointZeroOddCubic x ^ 2) :=
    mul_pos hgap hmass
  exact hproduct.trans_le hreserve

/-- The separated low/tail correction is not universally nonnegative, even
for continuous odd inputs which vanish at both endpoints.  The negative
value is exactly the negative clean energy of the explicit cubic profile. -/
theorem endpointZeroOddCubic_lowTailCorrection_neg :
    factorTwoEndpointLowTailCorrection
        endpointZeroOddCubic (-endpointZeroOddCubic) 0 0 0 0 < 0 := by
  exact lowTailCorrection_neg_of_clean_pos
    endpointZeroOddCubic endpointZeroOddCubic_clean_pos

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseAdversarialWitness
