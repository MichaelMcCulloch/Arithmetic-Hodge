import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAffineCancellationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural

open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicRemainderBound
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseP67ResidualAffineCancellationStructural
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural
open YoshidaFactorTwoPhaseTailCoercivity
open YoshidaRegularKernelBound

noncomputable section

/-!
# Exact regular-block decomposition at the `P₆/P₇` border

The low--residual part of the nonsingular phase block has three pieces: the
global analytic kernel errors, polynomial/affine models, and the forward
Hankel pole `1 / (2 + t)`.  The first two model integrals vanish by the
structural moment lemmas, leaving the analytic border and the forward Hankel
operator as the exact mixed normal form.
-/

/-- The two symmetric low--residual correlations. -/
def factorTwoP67ResidualSymmetricCrossSum
    (p₆ p₇ eR oR : ℝ → ℝ) (t : ℝ) : ℝ :=
  factorTwoCenteredCorrelationBilinear p₆ eR t +
    factorTwoCenteredCorrelationBilinear p₇ oR t

/-- The two alternating low--residual ordered cross differences. -/
def factorTwoP67ResidualAlternatingCrossSum
    (p₆ p₇ eR oR : ℝ → ℝ) (t : ℝ) : ℝ :=
  factorTwoP67ResidualAlternatingCrossDifference p₆ oR t +
    factorTwoP67ResidualAlternatingCrossDifference eR p₇ t

/-- The exact forward-Hankel half-cross left after removing the analytic and
polynomial/affine kernel models. -/
def factorTwoP67ResidualForwardHankelMixed
    (p₆ p₇ eR oR : ℝ → ℝ) (a b : ℝ) : ℝ :=
  -(a / 2) * (∫ t : ℝ in 0..2,
      factorTwoP67ResidualSymmetricCrossSum p₆ p₇ eR oR t / (2 + t)) -
    (b / 4) * (∫ t : ℝ in 0..2,
      factorTwoP67ResidualAlternatingCrossSum p₆ p₇ eR oR t / (2 + t))

/-- Pointwise complete mixed integrand of the nonsingular regular phase
block. -/
def factorTwoP67ResidualSmoothMixedIntegrand
    (p₆ p₇ eR oR : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  2 * a * (oddLowPoleFreeKernel t - 1 / (2 * (2 + t))) *
      factorTwoP67ResidualSymmetricCrossSum p₆ p₇ eR oR t +
    b * (yoshidaEndpointA *
          factorTwoCenteredAntisymmetricRegularWeight t -
        1 / (2 * (2 + t))) *
      factorTwoP67ResidualAlternatingCrossSum p₆ p₇ eR oR t

private theorem continuous_factorTwoP67ResidualSymmetricCrossSum
    (p₆ p₇ eR oR : ℝ → ℝ)
    (hp₆c : Continuous p₆) (hp₇c : Continuous p₇)
    (heRc : Continuous eR) (hoRc : Continuous oR) :
    Continuous (factorTwoP67ResidualSymmetricCrossSum p₆ p₇ eR oR) := by
  unfold factorTwoP67ResidualSymmetricCrossSum
    factorTwoCenteredCorrelationBilinear
  exact (((continuous_factorTwoCenteredCrossCorrelation p₆ eR hp₆c heRc).add
      (continuous_factorTwoCenteredCrossCorrelation eR p₆ heRc hp₆c)).div_const 2).add
    (((continuous_factorTwoCenteredCrossCorrelation p₇ oR hp₇c hoRc).add
      (continuous_factorTwoCenteredCrossCorrelation oR p₇ hoRc hp₇c)).div_const 2)

private theorem continuous_factorTwoP67ResidualAlternatingCrossSum
    (p₆ p₇ eR oR : ℝ → ℝ)
    (hp₆c : Continuous p₆) (hp₇c : Continuous p₇)
    (heRc : Continuous eR) (hoRc : Continuous oR) :
    Continuous (factorTwoP67ResidualAlternatingCrossSum p₆ p₇ eR oR) := by
  unfold factorTwoP67ResidualAlternatingCrossSum
    factorTwoP67ResidualAlternatingCrossDifference
  exact ((continuous_factorTwoCenteredCrossCorrelation oR p₆ hoRc hp₆c).sub
      (continuous_factorTwoCenteredCrossCorrelation p₆ oR hp₆c hoRc)).add
    ((continuous_factorTwoCenteredCrossCorrelation p₇ eR hp₇c heRc).sub
      (continuous_factorTwoCenteredCrossCorrelation eR p₇ heRc hp₇c))

private theorem measurable_yoshidaRegularKernel_decomposition :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem measurable_factorTwoCenteredSymmetricRegularWeight_decomposition :
    Measurable factorTwoCenteredSymmetricRegularWeight := by
  unfold factorTwoCenteredSymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).add
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel_decomposition.comp (by fun_prop))).sub
        (measurable_yoshidaRegularKernel_decomposition.comp (by fun_prop))

private theorem measurable_factorTwoCenteredAntisymmetricRegularWeight_decomposition :
    Measurable factorTwoCenteredAntisymmetricRegularWeight := by
  unfold factorTwoCenteredAntisymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).sub
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel_decomposition.comp (by fun_prop))).add
        (measurable_yoshidaRegularKernel_decomposition.comp (by fun_prop))

private theorem intervalIntegrable_poleFreeAnalyticRow
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦ (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t
  let g : ℝ → ℝ := fun t ↦ (3 / 8000 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f, oddLowPoleFreeKernel]
    exact ((measurable_const.mul
      measurable_factorTwoCenteredSymmetricRegularWeight_decomposition).sub
        continuous_poleFreeKernelPolynomial6.measurable).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hk := (abs_poleFreeKernel_sub_polynomial_lt
      (⟨ht.1.le, ht.2⟩ : t ∈ Icc (0 : ℝ) 2)).le
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

private theorem intervalIntegrable_alternatingAnalyticRow
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦
        (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          t / 10) * C t) volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      t / 10) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 1000 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact ((measurable_const.mul
      measurable_factorTwoCenteredAntisymmetricRegularWeight_decomposition).sub
        (measurable_id.div_const 10)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hk :=
      abs_yoshidaEndpointA_mul_factorTwoCenteredAntisymmetricRegularWeight_sub_linear_le_one_thousand
        ht.1.le ht.2
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

private theorem intervalIntegrable_div_two_add
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable (fun t : ℝ ↦ C t / (2 + t)) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  intro t ht
  exact (hC.continuousAt.div
    (by fun_prop : ContinuousAt (fun s : ℝ ↦ 2 + s) t)
    (by linarith [ht.1] : 2 + t ≠ 0)).continuousWithinAt

/-- Exact pointwise polarization of the regular phase integrand.  The only
pole which remains in this nonsingular block is the forward denominator
`2 + t`; the reflected pole has already been absorbed by desingularization. -/
theorem factorTwoIntrinsicRegularPhaseIntegrand_add_add_eq
    (p₆ p₇ eR oR : ℝ → ℝ)
    (hp₆c : Continuous p₆) (hp₇c : Continuous p₇)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (a b : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) :
    factorTwoIntrinsicRegularPhaseIntegrand (p₆ + eR) (p₇ + oR) a b t =
      factorTwoIntrinsicRegularPhaseIntegrand p₆ p₇ a b t +
        factorTwoIntrinsicRegularPhaseIntegrand eR oR a b t +
        factorTwoP67ResidualSmoothMixedIntegrand p₆ p₇ eR oR a b t := by
  have hrefFull := factorTwo_reflectedDesingularizedPhaseKernel_eq_regular
    (p₆ + eR) (p₇ + oR) a b ht2
  have hrefLow := factorTwo_reflectedDesingularizedPhaseKernel_eq_regular
    p₆ p₇ a b ht2
  have hrefTail := factorTwo_reflectedDesingularizedPhaseKernel_eq_regular
    eR oR a b ht2
  unfold factorTwoIntrinsicRegularPhaseIntegrand
  rw [hrefFull, hrefLow, hrefTail]
  unfold factorTwoCenteredForwardPhaseKernel factorTwoCenteredPhaseCorrelation
  rw [centeredEndpointCorrelation_add p₆ eR hp₆c heRc t,
    centeredEndpointCorrelation_add p₇ oR hp₇c hoRc t,
    factorTwoCenteredCrossCorrelation_add_left p₇ oR (p₆ + eR)
      hp₇c hoRc (hp₆c.add heRc) t,
    factorTwoCenteredCrossCorrelation_add_right p₇ p₆ eR
      hp₇c hp₆c heRc t,
    factorTwoCenteredCrossCorrelation_add_right oR p₆ eR
      hoRc hp₆c heRc t,
    factorTwoCenteredCrossCorrelation_add_left p₆ eR (p₇ + oR)
      hp₆c heRc (hp₇c.add hoRc) t,
    factorTwoCenteredCrossCorrelation_add_right p₆ p₇ oR
      hp₆c hp₇c hoRc t,
    factorTwoCenteredCrossCorrelation_add_right eR p₇ oR
      heRc hp₇c hoRc t]
  have hplus : yoshidaEndpointA * (2 + t) ≠ 0 :=
    mul_ne_zero yoshidaEndpointA_pos.ne' (by linarith)
  rw [factorTwoAdjacentSmoothKernel_eq_cosh_sub_regular_sub_pole hplus]
  unfold factorTwoP67ResidualSmoothMixedIntegrand
    factorTwoP67ResidualSymmetricCrossSum
    factorTwoP67ResidualAlternatingCrossSum
    factorTwoP67ResidualAlternatingCrossDifference oddLowPoleFreeKernel
    factorTwoCenteredSymmetricRegularWeight
    factorTwoCenteredAntisymmetricRegularWeight
    factorTwoCenteredReflectedRegularKernel
  have htplus : 2 + t ≠ 0 := by linarith
  field_simp [yoshidaEndpointA_pos.ne', htplus]
  ring

private theorem intervalIntegrable_factorTwoP67ResidualSmoothMixedIntegrand
    (p₆ p₇ eR oR : ℝ → ℝ)
    (hp₆c : Continuous p₆) (hp₇c : Continuous p₇)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (a b : ℝ) :
    IntervalIntegrable
      (factorTwoP67ResidualSmoothMixedIntegrand p₆ p₇ eR oR a b)
      volume 0 2 := by
  let G : ℝ → ℝ :=
    factorTwoIntrinsicRegularPhaseIntegrand (p₆ + eR) (p₇ + oR) a b
  let L : ℝ → ℝ := factorTwoIntrinsicRegularPhaseIntegrand p₆ p₇ a b
  let R : ℝ → ℝ := factorTwoIntrinsicRegularPhaseIntegrand eR oR a b
  have hG : IntervalIntegrable G volume 0 2 := by
    dsimp only [G]
    exact intervalIntegrable_factorTwoIntrinsicRegularPhaseIntegrand
      (p₆ + eR) (p₇ + oR) (hp₆c.add heRc) (hp₇c.add hoRc) a b
  have hL : IntervalIntegrable L volume 0 2 := by
    dsimp only [L]
    exact intervalIntegrable_factorTwoIntrinsicRegularPhaseIntegrand
      p₆ p₇ hp₆c hp₇c a b
  have hR : IntervalIntegrable R volume 0 2 := by
    dsimp only [R]
    exact intervalIntegrable_factorTwoIntrinsicRegularPhaseIntegrand
      eR oR heRc hoRc a b
  apply ((hG.sub hL).sub hR).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    (show ∀ᵐ t : ℝ ∂volume, t ≠ 2 by
      simp [ae_iff, measure_singleton]).filter_mono
        (ae_mono Measure.restrict_le_self)]
      with t ht ht2ne
  have ht' : t ∈ Ioc (0 : ℝ) 2 := by
    simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have hpoint := factorTwoIntrinsicRegularPhaseIntegrand_add_add_eq
    p₆ p₇ eR oR hp₆c hp₇c heRc hoRc a b
    ht'.1.le (lt_of_le_of_ne ht'.2 ht2ne)
  dsimp only [G, L, R]
  rw [hpoint]
  ring

/-- Integrated quadratic polarization of the complete nonsingular regular
block. -/
theorem factorTwoIntrinsicRegularPhaseBlock_add_add_eq
    (p₆ p₇ eR oR : ℝ → ℝ)
    (hp₆c : Continuous p₆) (hp₇c : Continuous p₇)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (a b : ℝ) :
    factorTwoIntrinsicRegularPhaseBlock (p₆ + eR) (p₇ + oR) a b =
      factorTwoIntrinsicRegularPhaseBlock p₆ p₇ a b +
        (∫ t : ℝ in 0..2,
          factorTwoP67ResidualSmoothMixedIntegrand p₆ p₇ eR oR a b t) +
        factorTwoIntrinsicRegularPhaseBlock eR oR a b := by
  let G : ℝ → ℝ :=
    factorTwoIntrinsicRegularPhaseIntegrand (p₆ + eR) (p₇ + oR) a b
  let L : ℝ → ℝ := factorTwoIntrinsicRegularPhaseIntegrand p₆ p₇ a b
  let R : ℝ → ℝ := factorTwoIntrinsicRegularPhaseIntegrand eR oR a b
  let M : ℝ → ℝ :=
    factorTwoP67ResidualSmoothMixedIntegrand p₆ p₇ eR oR a b
  have hL : IntervalIntegrable L volume 0 2 := by
    dsimp only [L]
    exact intervalIntegrable_factorTwoIntrinsicRegularPhaseIntegrand
      p₆ p₇ hp₆c hp₇c a b
  have hR : IntervalIntegrable R volume 0 2 := by
    dsimp only [R]
    exact intervalIntegrable_factorTwoIntrinsicRegularPhaseIntegrand
      eR oR heRc hoRc a b
  have hM : IntervalIntegrable M volume 0 2 := by
    dsimp only [M]
    exact intervalIntegrable_factorTwoP67ResidualSmoothMixedIntegrand
      p₆ p₇ eR oR hp₆c hp₇c heRc hoRc a b
  rw [factorTwoIntrinsicRegularPhaseBlock_eq_integral
      (p₆ + eR) (p₇ + oR) (hp₆c.add heRc) (hp₇c.add hoRc) a b,
    factorTwoIntrinsicRegularPhaseBlock_eq_integral
      p₆ p₇ hp₆c hp₇c a b,
    factorTwoIntrinsicRegularPhaseBlock_eq_integral
      eR oR heRc hoRc a b]
  change (∫ t : ℝ in 0..2, G t) =
    (∫ t : ℝ in 0..2, L t) + (∫ t : ℝ in 0..2, M t) +
      ∫ t : ℝ in 0..2, R t
  calc
    (∫ t : ℝ in 0..2, G t) =
        ∫ t : ℝ in 0..2, (L t + R t) + M t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 2 by
        simp [ae_iff, measure_singleton]] with t ht2ne
      intro ht
      have ht' : t ∈ Ioc (0 : ℝ) 2 := by
        simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
      have hpoint := factorTwoIntrinsicRegularPhaseIntegrand_add_add_eq
        p₆ p₇ eR oR hp₆c hp₇c heRc hoRc a b
        ht'.1.le (lt_of_le_of_ne ht'.2 ht2ne)
      dsimp only [G, L, R, M]
      exact hpoint
    _ = (∫ t : ℝ in 0..2, L t + R t) +
        ∫ t : ℝ in 0..2, M t := by
      rw [intervalIntegral.integral_add (hL.add hR) hM]
    _ = _ := by
      rw [intervalIntegral.integral_add hL hR]
      ring

/-- One symmetric low--residual row is exactly its analytic error plus the
degree-six model and forward pole; the model vanishes under the residual
moment gap. -/
theorem integral_symmetricRegularScalar_mul_correlationBilinear_eq
    (u r : ℝ → ℝ) (hu : Continuous u) (hr : Continuous r)
    {k : ℕ} (hlow : centeredLegendreMomentsVanishBelow r k)
    (hcut : 6 < k) :
    (∫ t : ℝ in 0..2,
      (oddLowPoleFreeKernel t - 1 / (2 * (2 + t))) *
        factorTwoCenteredCorrelationBilinear u r t) =
      factorTwoP67ResidualSymmetricAnalyticBorder u r -
        (1 / 2 : ℝ) * (∫ t : ℝ in 0..2,
          factorTwoCenteredCorrelationBilinear u r t / (2 + t)) := by
  let B : ℝ → ℝ := factorTwoCenteredCorrelationBilinear u r
  have hB : Continuous B := by
    dsimp only [B]
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation u r hu hr).add
      (continuous_factorTwoCenteredCrossCorrelation r u hr hu)).div_const 2
  have hErr : IntervalIntegrable
      (fun t : ℝ ↦
        (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * B t)
      volume 0 2 := intervalIntegrable_poleFreeAnalyticRow B hB
  have hModel : IntervalIntegrable
      (fun t : ℝ ↦ poleFreeKernelPolynomial6 t * B t)
      volume 0 2 :=
    (continuous_poleFreeKernelPolynomial6.mul hB).intervalIntegrable 0 2
  have hDiv : IntervalIntegrable (fun t : ℝ ↦ B t / (2 + t))
      volume 0 2 := intervalIntegrable_div_two_add B hB
  have hPole : IntervalIntegrable
      (fun t : ℝ ↦ (1 / (2 * (2 + t))) * B t) volume 0 2 := by
    apply (hDiv.const_mul (1 / 2 : ℝ)).congr
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) 2 := by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have htplus : 2 + t ≠ 0 := by linarith [ht'.1]
    field_simp [htplus]
  have hModelZero :
      (∫ t : ℝ in 0..2, poleFreeKernelPolynomial6 t * B t) = 0 := by
    dsimp only [B]
    exact integral_poleFreeKernelPolynomial6_mul_correlationBilinear_eq_zero
      u r hu hr hlow hcut
  have hPoleIntegral :
      (∫ t : ℝ in 0..2, (1 / (2 * (2 + t))) * B t) =
        (1 / 2 : ℝ) * (∫ t : ℝ in 0..2, B t / (2 + t)) := by
    calc
      _ = ∫ t : ℝ in 0..2, (1 / 2 : ℝ) * (B t / (2 + t)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 2 := by
          simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
        have htplus : 2 + t ≠ 0 := by linarith [ht'.1]
        field_simp [htplus]
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [show (fun t : ℝ ↦
      (oddLowPoleFreeKernel t - 1 / (2 * (2 + t))) * B t) = fun t ↦
        (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * B t +
          poleFreeKernelPolynomial6 t * B t -
          (1 / (2 * (2 + t))) * B t by
    funext t
    ring,
    intervalIntegral.integral_sub (hErr.add hModel) hPole,
    intervalIntegral.integral_add hErr hModel,
    hModelZero, hPoleIntegral]
  unfold factorTwoP67ResidualSymmetricAnalyticBorder poleFreeAnalyticError
  dsimp only [B]
  ring

/-- Alternating counterpart: an assumed structural affine cancellation
leaves only the analytic error and the same forward denominator. -/
theorem integral_antisymmetricRegularScalar_mul_crossDifference_eq
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (hlinear : (∫ t : ℝ in 0..2,
      t * factorTwoP67ResidualAlternatingCrossDifference e o t) = 0) :
    (∫ t : ℝ in 0..2,
      (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
        1 / (2 * (2 + t))) *
        factorTwoP67ResidualAlternatingCrossDifference e o t) =
      factorTwoP67ResidualAlternatingAnalyticBorder e o -
        (1 / 2 : ℝ) * (∫ t : ℝ in 0..2,
          factorTwoP67ResidualAlternatingCrossDifference e o t / (2 + t)) := by
  let D : ℝ → ℝ := factorTwoP67ResidualAlternatingCrossDifference e o
  have hD : Continuous D := by
    dsimp only [D]
    unfold factorTwoP67ResidualAlternatingCrossDifference
    exact (continuous_factorTwoCenteredCrossCorrelation o e ho he).sub
      (continuous_factorTwoCenteredCrossCorrelation e o he ho)
  have hErr : IntervalIntegrable
      (fun t : ℝ ↦
        (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          t / 10) * D t) volume 0 2 :=
    intervalIntegrable_alternatingAnalyticRow D hD
  have hAffine : IntervalIntegrable (fun t : ℝ ↦ (t / 10) * D t)
      volume 0 2 :=
    ((continuous_id.div_const 10).mul hD).intervalIntegrable 0 2
  have hDiv : IntervalIntegrable (fun t : ℝ ↦ D t / (2 + t))
      volume 0 2 := intervalIntegrable_div_two_add D hD
  have hPole : IntervalIntegrable
      (fun t : ℝ ↦ (1 / (2 * (2 + t))) * D t) volume 0 2 := by
    apply (hDiv.const_mul (1 / 2 : ℝ)).congr
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) 2 := by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have htplus : 2 + t ≠ 0 := by linarith [ht'.1]
    field_simp [htplus]
  have hAffineZero : (∫ t : ℝ in 0..2, (t / 10) * D t) = 0 := by
    calc
      _ = (1 / 10 : ℝ) * (∫ t : ℝ in 0..2, t * D t) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _ht
        ring
      _ = 0 := by
        dsimp only [D]
        rw [hlinear, mul_zero]
  have hPoleIntegral :
      (∫ t : ℝ in 0..2, (1 / (2 * (2 + t))) * D t) =
        (1 / 2 : ℝ) * (∫ t : ℝ in 0..2, D t / (2 + t)) := by
    calc
      _ = ∫ t : ℝ in 0..2, (1 / 2 : ℝ) * (D t / (2 + t)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 2 := by
          simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
        have htplus : 2 + t ≠ 0 := by linarith [ht'.1]
        field_simp [htplus]
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
        1 / (2 * (2 + t))) * D t) = fun t ↦
        (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          t / 10) * D t + (t / 10) * D t -
          (1 / (2 * (2 + t))) * D t by
    funext t
    ring,
    intervalIntegral.integral_sub (hErr.add hAffine) hPole,
    intervalIntegral.integral_add hErr hAffine,
    hAffineZero, hPoleIntegral]
  unfold factorTwoP67ResidualAlternatingAnalyticBorder
  dsimp only [D]
  ring

private theorem intervalIntegrable_symmetricRegularRow
    (u r : ℝ → ℝ) (hu : Continuous u) (hr : Continuous r) :
    IntervalIntegrable (fun t : ℝ ↦
      (oddLowPoleFreeKernel t - 1 / (2 * (2 + t))) *
        factorTwoCenteredCorrelationBilinear u r t) volume 0 2 := by
  let B : ℝ → ℝ := factorTwoCenteredCorrelationBilinear u r
  have hB : Continuous B := by
    dsimp only [B]
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation u r hu hr).add
      (continuous_factorTwoCenteredCrossCorrelation r u hr hu)).div_const 2
  have hErr := intervalIntegrable_poleFreeAnalyticRow B hB
  have hModel : IntervalIntegrable
      (fun t : ℝ ↦ poleFreeKernelPolynomial6 t * B t) volume 0 2 :=
    (continuous_poleFreeKernelPolynomial6.mul hB).intervalIntegrable 0 2
  have hDiv := intervalIntegrable_div_two_add B hB
  have hPole : IntervalIntegrable
      (fun t : ℝ ↦ (1 / (2 * (2 + t))) * B t) volume 0 2 := by
    apply (hDiv.const_mul (1 / 2 : ℝ)).congr
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) 2 := by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have htplus : 2 + t ≠ 0 := by linarith [ht'.1]
    field_simp [htplus]
  apply ((hErr.add hModel).sub hPole).congr
  intro t _ht
  dsimp only [B]
  ring

private theorem intervalIntegrable_antisymmetricRegularRow
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o) :
    IntervalIntegrable (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
        1 / (2 * (2 + t))) *
        factorTwoP67ResidualAlternatingCrossDifference e o t) volume 0 2 := by
  let D : ℝ → ℝ := factorTwoP67ResidualAlternatingCrossDifference e o
  have hD : Continuous D := by
    dsimp only [D]
    unfold factorTwoP67ResidualAlternatingCrossDifference
    exact (continuous_factorTwoCenteredCrossCorrelation o e ho he).sub
      (continuous_factorTwoCenteredCrossCorrelation e o he ho)
  have hErr := intervalIntegrable_alternatingAnalyticRow D hD
  have hAffine : IntervalIntegrable (fun t : ℝ ↦ (t / 10) * D t)
      volume 0 2 :=
    ((continuous_id.div_const 10).mul hD).intervalIntegrable 0 2
  have hDiv := intervalIntegrable_div_two_add D hD
  have hPole : IntervalIntegrable
      (fun t : ℝ ↦ (1 / (2 * (2 + t))) * D t) volume 0 2 := by
    apply (hDiv.const_mul (1 / 2 : ℝ)).congr
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) 2 := by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have htplus : 2 + t ≠ 0 := by linarith [ht'.1]
    field_simp [htplus]
  apply ((hErr.add hAffine).sub hPole).congr
  intro t _ht
  dsimp only [D]
  ring

/-- For arbitrary continuous low profiles, moment-gap cancellation of the
degree-six symmetric model together with the two affine alternating rows
leaves exactly the analytic remainder and forward-Hankel half-cross. -/
theorem integral_factorTwoP67ResidualSmoothMixedIntegrand_eq_of_cancellations
    (eLow oLow eR oR : ℝ → ℝ)
    (heLowc : Continuous eLow) (hoLowc : Continuous oLow)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    {ke ko : ℕ}
    (heGap : centeredLegendreMomentsVanishBelow eR ke)
    (hoGap : centeredLegendreMomentsVanishBelow oR ko)
    (heCut : 6 < ke) (hoCut : 6 < ko)
    (hlinearE : (∫ t : ℝ in 0..2,
      t * factorTwoP67ResidualAlternatingCrossDifference eLow oR t) = 0)
    (hlinearO : (∫ t : ℝ in 0..2,
      t * factorTwoP67ResidualAlternatingCrossDifference eR oLow t) = 0)
    (a b : ℝ) :
    (∫ t : ℝ in 0..2,
      factorTwoP67ResidualSmoothMixedIntegrand
        eLow oLow eR oR a b t) =
      2 * (factorTwoP67ResidualAnalyticMixed
          eLow oLow eR oR a b +
        factorTwoP67ResidualForwardHankelMixed
          eLow oLow eR oR a b) := by
  let S : ℝ → ℝ := fun t ↦
    oddLowPoleFreeKernel t - 1 / (2 * (2 + t))
  let T : ℝ → ℝ := fun t ↦
    yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      1 / (2 * (2 + t))
  let BE : ℝ → ℝ := factorTwoCenteredCorrelationBilinear eLow eR
  let BO : ℝ → ℝ := factorTwoCenteredCorrelationBilinear oLow oR
  let DE : ℝ → ℝ :=
    factorTwoP67ResidualAlternatingCrossDifference eLow oR
  let DO : ℝ → ℝ :=
    factorTwoP67ResidualAlternatingCrossDifference eR oLow
  have hBE : Continuous BE := by
    dsimp only [BE]
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation eLow eR heLowc heRc).add
      (continuous_factorTwoCenteredCrossCorrelation eR eLow heRc heLowc)).div_const 2
  have hBO : Continuous BO := by
    dsimp only [BO]
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation oLow oR hoLowc hoRc).add
      (continuous_factorTwoCenteredCrossCorrelation oR oLow hoRc hoLowc)).div_const 2
  have hDE : Continuous DE := by
    dsimp only [DE]
    unfold factorTwoP67ResidualAlternatingCrossDifference
    exact (continuous_factorTwoCenteredCrossCorrelation oR eLow hoRc heLowc).sub
      (continuous_factorTwoCenteredCrossCorrelation eLow oR heLowc hoRc)
  have hDO : Continuous DO := by
    dsimp only [DO]
    unfold factorTwoP67ResidualAlternatingCrossDifference
    exact (continuous_factorTwoCenteredCrossCorrelation oLow eR hoLowc heRc).sub
      (continuous_factorTwoCenteredCrossCorrelation eR oLow heRc hoLowc)
  have hSE := integral_symmetricRegularScalar_mul_correlationBilinear_eq
    eLow eR heLowc heRc heGap heCut
  have hSO := integral_symmetricRegularScalar_mul_correlationBilinear_eq
    oLow oR hoLowc hoRc hoGap hoCut
  have hAE := integral_antisymmetricRegularScalar_mul_crossDifference_eq
    eLow oR heLowc hoRc hlinearE
  have hAO := integral_antisymmetricRegularScalar_mul_crossDifference_eq
    eR oLow heRc hoLowc hlinearO
  have hSEInt : IntervalIntegrable (fun t : ℝ ↦ S t * BE t)
      volume 0 2 := by
    dsimp only [S, BE]
    exact intervalIntegrable_symmetricRegularRow eLow eR heLowc heRc
  have hSOInt : IntervalIntegrable (fun t : ℝ ↦ S t * BO t)
      volume 0 2 := by
    dsimp only [S, BO]
    exact intervalIntegrable_symmetricRegularRow oLow oR hoLowc hoRc
  have hAEInt : IntervalIntegrable (fun t : ℝ ↦ T t * DE t)
      volume 0 2 := by
    dsimp only [T, DE]
    exact intervalIntegrable_antisymmetricRegularRow eLow oR heLowc hoRc
  have hAOInt : IntervalIntegrable (fun t : ℝ ↦ T t * DO t)
      volume 0 2 := by
    dsimp only [T, DO]
    exact intervalIntegrable_antisymmetricRegularRow eR oLow heRc hoLowc
  have hDivBE := intervalIntegrable_div_two_add BE hBE
  have hDivBO := intervalIntegrable_div_two_add BO hBO
  have hDivDE := intervalIntegrable_div_two_add DE hDE
  have hDivDO := intervalIntegrable_div_two_add DO hDO
  have hSym :
      (∫ t : ℝ in 0..2,
        factorTwoP67ResidualSymmetricCrossSum eLow oLow eR oR t / (2 + t)) =
        (∫ t : ℝ in 0..2, BE t / (2 + t)) +
          ∫ t : ℝ in 0..2, BO t / (2 + t) := by
    rw [show (fun t : ℝ ↦
        factorTwoP67ResidualSymmetricCrossSum eLow oLow eR oR t / (2 + t)) =
      fun t ↦ BE t / (2 + t) + BO t / (2 + t) by
        funext t
        dsimp only [BE, BO]
        unfold factorTwoP67ResidualSymmetricCrossSum
        ring,
      intervalIntegral.integral_add hDivBE hDivBO]
  have hAlt :
      (∫ t : ℝ in 0..2,
        factorTwoP67ResidualAlternatingCrossSum eLow oLow eR oR t / (2 + t)) =
        (∫ t : ℝ in 0..2, DE t / (2 + t)) +
          ∫ t : ℝ in 0..2, DO t / (2 + t) := by
    rw [show (fun t : ℝ ↦
        factorTwoP67ResidualAlternatingCrossSum eLow oLow eR oR t / (2 + t)) =
      fun t ↦ DE t / (2 + t) + DO t / (2 + t) by
        funext t
        dsimp only [DE, DO]
        unfold factorTwoP67ResidualAlternatingCrossSum
        ring,
      intervalIntegral.integral_add hDivDE hDivDO]
  rw [show (fun t : ℝ ↦
      factorTwoP67ResidualSmoothMixedIntegrand eLow oLow eR oR a b t) = fun t ↦
        (2 * a) * (S t * BE t) + (2 * a) * (S t * BO t) +
          b * (T t * DE t) + b * (T t * DO t) by
    funext t
    dsimp only [S, T, BE, BO, DE, DO]
    unfold factorTwoP67ResidualSmoothMixedIntegrand
      factorTwoP67ResidualSymmetricCrossSum
      factorTwoP67ResidualAlternatingCrossSum
    ring,
    intervalIntegral.integral_add
      (((hSEInt.const_mul (2 * a)).add (hSOInt.const_mul (2 * a))).add
        (hAEInt.const_mul b)) (hAOInt.const_mul b),
    intervalIntegral.integral_add
      ((hSEInt.const_mul (2 * a)).add (hSOInt.const_mul (2 * a)))
      (hAEInt.const_mul b),
    intervalIntegral.integral_add
      (hSEInt.const_mul (2 * a)) (hSOInt.const_mul (2 * a))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [hSE, hSO, hAE, hAO]
  change _ = 2 *
    (factorTwoP67ResidualAnalyticMixed eLow oLow eR oR a b +
      factorTwoP67ResidualForwardHankelMixed eLow oLow eR oR a b)
  unfold factorTwoP67ResidualAnalyticMixed
    factorTwoP67ResidualForwardHankelMixed
  rw [hSym, hAlt]
  ring

/-- For the canonical `P₆/P₇` low block, the complete smooth mixed
integral is twice the sum of the analytic half-cross and the forward-Hankel
half-cross.  Both polynomial models have disappeared exactly. -/
theorem integral_factorTwoP67ResidualSmoothMixedIntegrand_eq
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (hoRo : Function.Odd oR)
    (heLow : centeredLegendreMomentsVanishBelow eR 8)
    (hoLow : centeredLegendreMomentsVanishBelow oR 9)
    (c d a b : ℝ) :
    (∫ t : ℝ in 0..2,
      factorTwoP67ResidualSmoothMixedIntegrand
        (c • factorTwoCenteredP6) (d • factorTwoCenteredP7)
        eR oR a b t) =
      2 * (factorTwoP67ResidualAnalyticMixed
          (c • factorTwoCenteredP6) (d • factorTwoCenteredP7)
          eR oR a b +
        factorTwoP67ResidualForwardHankelMixed
          (c • factorTwoCenteredP6) (d • factorTwoCenteredP7)
          eR oR a b) := by
  let p₆ : ℝ → ℝ := c • factorTwoCenteredP6
  let p₇ : ℝ → ℝ := d • factorTwoCenteredP7
  let S : ℝ → ℝ := fun t ↦
    oddLowPoleFreeKernel t - 1 / (2 * (2 + t))
  let T : ℝ → ℝ := fun t ↦
    yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      1 / (2 * (2 + t))
  let B₆ : ℝ → ℝ := factorTwoCenteredCorrelationBilinear p₆ eR
  let B₇ : ℝ → ℝ := factorTwoCenteredCorrelationBilinear p₇ oR
  let D₆ : ℝ → ℝ := factorTwoP67ResidualAlternatingCrossDifference p₆ oR
  let D₇ : ℝ → ℝ := factorTwoP67ResidualAlternatingCrossDifference eR p₇
  have hp₆c : Continuous p₆ := continuous_factorTwoCenteredP6.const_smul c
  have hp₇c : Continuous p₇ := continuous_factorTwoCenteredP7.const_smul d
  have hB₆ : Continuous B₆ := by
    dsimp only [B₆]
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation p₆ eR hp₆c heRc).add
      (continuous_factorTwoCenteredCrossCorrelation eR p₆ heRc hp₆c)).div_const 2
  have hB₇ : Continuous B₇ := by
    dsimp only [B₇]
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation p₇ oR hp₇c hoRc).add
      (continuous_factorTwoCenteredCrossCorrelation oR p₇ hoRc hp₇c)).div_const 2
  have hD₆ : Continuous D₆ := by
    dsimp only [D₆]
    unfold factorTwoP67ResidualAlternatingCrossDifference
    exact (continuous_factorTwoCenteredCrossCorrelation oR p₆ hoRc hp₆c).sub
      (continuous_factorTwoCenteredCrossCorrelation p₆ oR hp₆c hoRc)
  have hD₇ : Continuous D₇ := by
    dsimp only [D₇]
    unfold factorTwoP67ResidualAlternatingCrossDifference
    exact (continuous_factorTwoCenteredCrossCorrelation p₇ eR hp₇c heRc).sub
      (continuous_factorTwoCenteredCrossCorrelation eR p₇ heRc hp₇c)
  have hS₆ := integral_symmetricRegularScalar_mul_correlationBilinear_eq
    p₆ eR hp₆c heRc heLow (by norm_num)
  have hS₇ := integral_symmetricRegularScalar_mul_correlationBilinear_eq
    p₇ oR hp₇c hoRc hoLow (by norm_num)
  have hlinear₆ := integral_linear_mul_P6_oddResidual_crossDifference_eq_zero
    oR hoRc hoRo c
  have hlinear₇ := integral_linear_mul_evenResidual_P7_crossDifference_eq_zero
    eR heRc heLow d
  have hA₆ := integral_antisymmetricRegularScalar_mul_crossDifference_eq
    p₆ oR hp₆c hoRc hlinear₆
  have hA₇ := integral_antisymmetricRegularScalar_mul_crossDifference_eq
    eR p₇ heRc hp₇c hlinear₇
  have hS₆Int : IntervalIntegrable (fun t : ℝ ↦ S t * B₆ t) volume 0 2 := by
    dsimp only [S, B₆]
    exact intervalIntegrable_symmetricRegularRow p₆ eR hp₆c heRc
  have hS₇Int : IntervalIntegrable (fun t : ℝ ↦ S t * B₇ t) volume 0 2 := by
    dsimp only [S, B₇]
    exact intervalIntegrable_symmetricRegularRow p₇ oR hp₇c hoRc
  have hA₆Int : IntervalIntegrable (fun t : ℝ ↦ T t * D₆ t) volume 0 2 := by
    dsimp only [T, D₆]
    exact intervalIntegrable_antisymmetricRegularRow p₆ oR hp₆c hoRc
  have hA₇Int : IntervalIntegrable (fun t : ℝ ↦ T t * D₇ t) volume 0 2 := by
    dsimp only [T, D₇]
    exact intervalIntegrable_antisymmetricRegularRow eR p₇ heRc hp₇c
  have hDivB₆ := intervalIntegrable_div_two_add B₆ hB₆
  have hDivB₇ := intervalIntegrable_div_two_add B₇ hB₇
  have hDivD₆ := intervalIntegrable_div_two_add D₆ hD₆
  have hDivD₇ := intervalIntegrable_div_two_add D₇ hD₇
  have hSymHankel :
      (∫ t : ℝ in 0..2,
        factorTwoP67ResidualSymmetricCrossSum p₆ p₇ eR oR t / (2 + t)) =
        (∫ t : ℝ in 0..2, B₆ t / (2 + t)) +
          ∫ t : ℝ in 0..2, B₇ t / (2 + t) := by
    rw [show (fun t : ℝ ↦
        factorTwoP67ResidualSymmetricCrossSum p₆ p₇ eR oR t / (2 + t)) =
        fun t ↦ B₆ t / (2 + t) + B₇ t / (2 + t) by
      funext t
      dsimp only [B₆, B₇]
      unfold factorTwoP67ResidualSymmetricCrossSum
      ring,
      intervalIntegral.integral_add hDivB₆ hDivB₇]
  have hAltHankel :
      (∫ t : ℝ in 0..2,
        factorTwoP67ResidualAlternatingCrossSum p₆ p₇ eR oR t / (2 + t)) =
        (∫ t : ℝ in 0..2, D₆ t / (2 + t)) +
          ∫ t : ℝ in 0..2, D₇ t / (2 + t) := by
    rw [show (fun t : ℝ ↦
        factorTwoP67ResidualAlternatingCrossSum p₆ p₇ eR oR t / (2 + t)) =
        fun t ↦ D₆ t / (2 + t) + D₇ t / (2 + t) by
      funext t
      dsimp only [D₆, D₇]
      unfold factorTwoP67ResidualAlternatingCrossSum
      ring,
      intervalIntegral.integral_add hDivD₆ hDivD₇]
  rw [show (fun t : ℝ ↦
      factorTwoP67ResidualSmoothMixedIntegrand p₆ p₇ eR oR a b t) = fun t ↦
        (2 * a) * (S t * B₆ t) + (2 * a) * (S t * B₇ t) +
          b * (T t * D₆ t) + b * (T t * D₇ t) by
    funext t
    dsimp only [S, T, B₆, B₇, D₆, D₇]
    unfold factorTwoP67ResidualSmoothMixedIntegrand
      factorTwoP67ResidualSymmetricCrossSum
      factorTwoP67ResidualAlternatingCrossSum
    ring,
    intervalIntegral.integral_add
      (((hS₆Int.const_mul (2 * a)).add (hS₇Int.const_mul (2 * a))).add
        (hA₆Int.const_mul b)) (hA₇Int.const_mul b),
    intervalIntegral.integral_add
      ((hS₆Int.const_mul (2 * a)).add (hS₇Int.const_mul (2 * a)))
      (hA₆Int.const_mul b),
    intervalIntegral.integral_add
      (hS₆Int.const_mul (2 * a)) (hS₇Int.const_mul (2 * a))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [hS₆, hS₇, hA₆, hA₇]
  change _ = 2 *
    (factorTwoP67ResidualAnalyticMixed p₆ p₇ eR oR a b +
      factorTwoP67ResidualForwardHankelMixed p₆ p₇ eR oR a b)
  unfold factorTwoP67ResidualAnalyticMixed
    factorTwoP67ResidualForwardHankelMixed
  rw [hSymHankel, hAltHankel]
  ring

/-- Exact production normal form for the canonical `P₆/P₇` low block
coupled to cutoff-eight/nine residuals. -/
theorem factorTwoIntrinsicRegularPhaseBlock_P67_add_residual_eq
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (hoRo : Function.Odd oR)
    (heLow : centeredLegendreMomentsVanishBelow eR 8)
    (hoLow : centeredLegendreMomentsVanishBelow oR 9)
    (c d a b : ℝ) :
    factorTwoIntrinsicRegularPhaseBlock
        ((c • factorTwoCenteredP6) + eR)
        ((d • factorTwoCenteredP7) + oR) a b =
      factorTwoIntrinsicRegularPhaseBlock
          (c • factorTwoCenteredP6) (d • factorTwoCenteredP7) a b +
        2 * (factorTwoP67ResidualAnalyticMixed
            (c • factorTwoCenteredP6) (d • factorTwoCenteredP7)
            eR oR a b +
          factorTwoP67ResidualForwardHankelMixed
            (c • factorTwoCenteredP6) (d • factorTwoCenteredP7)
            eR oR a b) +
        factorTwoIntrinsicRegularPhaseBlock eR oR a b := by
  rw [factorTwoIntrinsicRegularPhaseBlock_add_add_eq
      (c • factorTwoCenteredP6) (d • factorTwoCenteredP7) eR oR
      (continuous_factorTwoCenteredP6.const_smul c)
      (continuous_factorTwoCenteredP7.const_smul d) heRc hoRc a b,
    integral_factorTwoP67ResidualSmoothMixedIntegrand_eq
      eR oR heRc hoRc hoRo heLow hoLow c d a b]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural
