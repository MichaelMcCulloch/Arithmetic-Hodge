import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP678CombinedResidualSchurStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineResidualDecompositionStructural

open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseHigherLegendreStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicRemainderBound
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseP67ResidualAffineCancellationStructural
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaFactorTwoPhaseP67CombinedForwardSchurStructural
open YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural
open YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural
open YoshidaFactorTwoPhaseP678CombinedResidualSchurStructural
open YoshidaFactorTwoPhaseP8ForwardSchurStructural
open YoshidaFactorTwoPhaseP8StructuralReserve
open YoshidaFactorTwoPhaseOddAffineKernelEstimate

noncomputable section

/-!
# Exact cutoff-nine regular low--residual decomposition

This module identifies the already-certified `P6/P7/P8` residual half-cross
with the mixed term in the actual nonsingular regular phase block.  The
lower `P0,...,P5` rows are deliberately not hidden here: the theorem applies
to the upper low block itself, so a later full-low assembly must retain their
separate cross term.
-/

private theorem integral_factorTwoCenteredP8_eq_zero :
    (∫ x : ℝ in -1..1, factorTwoCenteredP8 x) = 0 := by
  have h := factorTwoCenteredP8_p0_zero
  unfold centeredEvenP0Coefficient at h
  linarith

/-- The affine alternating model vanishes for the `P8`--odd-residual row. -/
theorem integral_linear_mul_P8_oddResidual_crossDifference_eq_zero
    (o : ℝ → ℝ) (hoc : Continuous o) (ho : Function.Odd o)
    (f : ℝ) :
    (∫ t : ℝ in 0..2,
      t * (factorTwoCenteredCrossCorrelation o (f • factorTwoCenteredP8) t -
        factorTwoCenteredCrossCorrelation (f • factorTwoCenteredP8) o t)) = 0 := by
  apply integral_linear_mul_crossDifference_eq_zero_of_mean_zero_odd
    (f • factorTwoCenteredP8) o
    (continuous_factorTwoCenteredP8.const_smul f) hoc
  · rw [show (fun x : ℝ ↦ (f • factorTwoCenteredP8) x) =
        fun x ↦ f * factorTwoCenteredP8 x by rfl,
      intervalIntegral.integral_const_mul,
      integral_factorTwoCenteredP8_eq_zero, mul_zero]
  · exact ho

private theorem intervalIntegrable_smoothMixed
    (pE pO eR oR : ℝ → ℝ)
    (hpEc : Continuous pE) (hpOc : Continuous pO)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (a b : ℝ) :
    IntervalIntegrable
      (factorTwoP67ResidualSmoothMixedIntegrand pE pO eR oR a b)
      volume 0 2 := by
  let G : ℝ → ℝ :=
    factorTwoIntrinsicRegularPhaseIntegrand (pE + eR) (pO + oR) a b
  let L : ℝ → ℝ := factorTwoIntrinsicRegularPhaseIntegrand pE pO a b
  let R : ℝ → ℝ := factorTwoIntrinsicRegularPhaseIntegrand eR oR a b
  have hG : IntervalIntegrable G volume 0 2 := by
    dsimp only [G]
    exact intervalIntegrable_factorTwoIntrinsicRegularPhaseIntegrand
      (pE + eR) (pO + oR) (hpEc.add heRc) (hpOc.add hoRc) a b
  have hL : IntervalIntegrable L volume 0 2 := by
    dsimp only [L]
    exact intervalIntegrable_factorTwoIntrinsicRegularPhaseIntegrand
      pE pO hpEc hpOc a b
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
    pE pO eR oR hpEc hpOc heRc hoRc a b
    ht'.1.le (lt_of_le_of_ne ht'.2 ht2ne)
  dsimp only [G, L, R]
  rw [hpoint]
  ring

private theorem intervalIntegrable_symmetricRegularRow
    (u r : ℝ → ℝ) (hu : Continuous u) (hr : Continuous r) :
    IntervalIntegrable (fun t : ℝ ↦
      (oddLowPoleFreeKernel t - 1 / (2 * (2 + t))) *
        factorTwoCenteredCorrelationBilinear u r t) volume 0 2 := by
  have h := intervalIntegrable_smoothMixed u 0 r 0 hu (by fun_prop)
    hr (by fun_prop) 1 0
  have hhalf := h.const_mul (1 / 2 : ℝ)
  apply hhalf.congr
  intro t _ht
  unfold factorTwoP67ResidualSmoothMixedIntegrand
    factorTwoP67ResidualSymmetricCrossSum
    factorTwoP67ResidualAlternatingCrossSum
    factorTwoP67ResidualAlternatingCrossDifference
    factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation
  simp
  ring

private theorem intervalIntegrable_antisymmetricRegularRow
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o) :
    IntervalIntegrable (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
        1 / (2 * (2 + t))) *
        factorTwoP67ResidualAlternatingCrossDifference e o t)
      volume 0 2 := by
  have h := intervalIntegrable_smoothMixed e 0 0 o he (by fun_prop)
    (by fun_prop) ho 0 1
  apply h.congr
  intro t _ht
  unfold factorTwoP67ResidualSmoothMixedIntegrand
    factorTwoP67ResidualSymmetricCrossSum
    factorTwoP67ResidualAlternatingCrossSum
    factorTwoP67ResidualAlternatingCrossDifference
    factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation
  simp

/-- For the scaled `P8` row, the actual smooth mixed integral is exactly
twice the certified analytic-plus-forward half-cross. -/
theorem integral_factorTwoP8ResidualSmoothMixedIntegrand_eq
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (hoRo : Function.Odd oR)
    (heLow : centeredLegendreMomentsVanishBelow eR 9)
    (f a b : ℝ) :
    (∫ t : ℝ in 0..2,
      factorTwoP67ResidualSmoothMixedIntegrand
        (f • factorTwoCenteredP8) (0 : ℝ → ℝ)
        eR oR a b t) =
      2 * factorTwoP8ResidualCombinedForwardMixed eR oR f a b := by
  let p₈ : ℝ → ℝ := f • factorTwoCenteredP8
  let S : ℝ → ℝ := fun t ↦
    oddLowPoleFreeKernel t - 1 / (2 * (2 + t))
  let T : ℝ → ℝ := fun t ↦
    yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
      1 / (2 * (2 + t))
  let B₈ : ℝ → ℝ := factorTwoCenteredCorrelationBilinear p₈ eR
  let D₈ : ℝ → ℝ := factorTwoP67ResidualAlternatingCrossDifference p₈ oR
  have hp₈c : Continuous p₈ := continuous_factorTwoCenteredP8.const_smul f
  have hS₈ := integral_symmetricRegularScalar_mul_correlationBilinear_eq
    p₈ eR hp₈c heRc heLow (by norm_num)
  have hlinear₈ := integral_linear_mul_P8_oddResidual_crossDifference_eq_zero
    oR hoRc hoRo f
  have hA₈ := integral_antisymmetricRegularScalar_mul_crossDifference_eq
    p₈ oR hp₈c hoRc hlinear₈
  have hS₈Int : IntervalIntegrable (fun t : ℝ ↦ S t * B₈ t) volume 0 2 := by
    dsimp only [S, B₈]
    exact intervalIntegrable_symmetricRegularRow p₈ eR hp₈c heRc
  have hA₈Int : IntervalIntegrable (fun t : ℝ ↦ T t * D₈ t) volume 0 2 := by
    dsimp only [T, D₈]
    exact intervalIntegrable_antisymmetricRegularRow p₈ oR hp₈c hoRc
  rw [show (fun t : ℝ ↦
      factorTwoP67ResidualSmoothMixedIntegrand p₈ (0 : ℝ → ℝ)
        eR oR a b t) = fun t ↦
        (2 * a) * (S t * B₈ t) + b * (T t * D₈ t) by
    funext t
    dsimp only [S, T, B₈, D₈]
    unfold factorTwoP67ResidualSmoothMixedIntegrand
      factorTwoP67ResidualSymmetricCrossSum
      factorTwoP67ResidualAlternatingCrossSum
      factorTwoP67ResidualAlternatingCrossDifference
      factorTwoCenteredCorrelationBilinear
      factorTwoCenteredCrossCorrelation
    simp
    ring,
    intervalIntegral.integral_add
      (hS₈Int.const_mul (2 * a)) (hA₈Int.const_mul b)]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [hS₈, hA₈]
  change _ = 2 * factorTwoP8ResidualCombinedForwardMixed eR oR f a b
  unfold factorTwoP8ResidualCombinedForwardMixed
    factorTwoP67ResidualAnalyticMixed
    factorTwoP67ResidualForwardHankelMixed
    factorTwoP67ResidualSymmetricCrossSum
    factorTwoP67ResidualAlternatingCrossSum
    factorTwoP67ResidualAlternatingCrossDifference
    factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation
  simp [p₈, Pi.smul_apply, smul_eq_mul]
  ring

/-- The exact smooth low--residual integrand is additive in the retained
low pair.  This is the structural step which permits the `P8` row to be
adjoined without re-expanding the already-certified `P6/P7` block. -/
theorem factorTwoP67ResidualSmoothMixedIntegrand_add_low_eq
    (pE qE pO qO eR oR : ℝ → ℝ)
    (hpEc : Continuous pE) (hqEc : Continuous qE)
    (hpOc : Continuous pO) (hqOc : Continuous qO)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (a b t : ℝ) :
    factorTwoP67ResidualSmoothMixedIntegrand
        (pE + qE) (pO + qO) eR oR a b t =
      factorTwoP67ResidualSmoothMixedIntegrand pE pO eR oR a b t +
        factorTwoP67ResidualSmoothMixedIntegrand qE qO eR oR a b t := by
  unfold factorTwoP67ResidualSmoothMixedIntegrand
    factorTwoP67ResidualSymmetricCrossSum
    factorTwoP67ResidualAlternatingCrossSum
    factorTwoP67ResidualAlternatingCrossDifference
    factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_add_left pE qE eR
      hpEc hqEc heRc t,
    factorTwoCenteredCrossCorrelation_add_right eR pE qE
      heRc hpEc hqEc t,
    factorTwoCenteredCrossCorrelation_add_left pO qO oR
      hpOc hqOc hoRc t,
    factorTwoCenteredCrossCorrelation_add_right oR pO qO
      hoRc hpOc hqOc t,
    factorTwoCenteredCrossCorrelation_add_right oR pE qE
      hoRc hpEc hqEc t,
    factorTwoCenteredCrossCorrelation_add_left pE qE oR
      hpEc hqEc hoRc t,
    factorTwoCenteredCrossCorrelation_add_left pO qO eR
      hpOc hqOc heRc t,
    factorTwoCenteredCrossCorrelation_add_right eR pO qO
      heRc hpOc hqOc t]
  ring

theorem integral_factorTwoP67ResidualSmoothMixedIntegrand_add_low_eq
    (pE qE pO qO eR oR : ℝ → ℝ)
    (hpEc : Continuous pE) (hqEc : Continuous qE)
    (hpOc : Continuous pO) (hqOc : Continuous qO)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (a b : ℝ) :
    (∫ t : ℝ in 0..2,
      factorTwoP67ResidualSmoothMixedIntegrand
        (pE + qE) (pO + qO) eR oR a b t) =
      (∫ t : ℝ in 0..2,
        factorTwoP67ResidualSmoothMixedIntegrand pE pO eR oR a b t) +
      ∫ t : ℝ in 0..2,
        factorTwoP67ResidualSmoothMixedIntegrand qE qO eR oR a b t := by
  have hpInt := intervalIntegrable_smoothMixed pE pO eR oR
    hpEc hpOc heRc hoRc a b
  have hqInt := intervalIntegrable_smoothMixed qE qO eR oR
    hqEc hqOc heRc hoRc a b
  rw [show (fun t : ℝ ↦
      factorTwoP67ResidualSmoothMixedIntegrand
        (pE + qE) (pO + qO) eR oR a b t) = fun t ↦
      factorTwoP67ResidualSmoothMixedIntegrand pE pO eR oR a b t +
        factorTwoP67ResidualSmoothMixedIntegrand qE qO eR oR a b t by
    funext t
    exact factorTwoP67ResidualSmoothMixedIntegrand_add_low_eq
      pE qE pO qO eR oR hpEc hqEc hpOc hqOc heRc hoRc a b t,
    intervalIntegral.integral_add hpInt hqInt]

/-- Exact normal form for the complete `P6/P7/P8` smooth mixed integral. -/
theorem integral_factorTwoP678ResidualSmoothMixedIntegrand_eq
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (hoRo : Function.Odd oR)
    (heLow : centeredLegendreMomentsVanishBelow eR 9)
    (hoLow : centeredLegendreMomentsVanishBelow oR 9)
    (c d f a b : ℝ) :
    (∫ t : ℝ in 0..2,
      factorTwoP67ResidualSmoothMixedIntegrand
        ((c • factorTwoCenteredP6) + (f • factorTwoCenteredP8))
        (d • factorTwoCenteredP7) eR oR a b t) =
      2 * factorTwoP678ResidualCombinedForwardMixed eR oR c d f a b := by
  have heLow8 : centeredLegendreMomentsVanishBelow eR 8 := by
    intro n hn
    exact heLow n (by omega)
  rw [show (d • factorTwoCenteredP7 : ℝ → ℝ) =
      (d • factorTwoCenteredP7) + 0 by simp,
    integral_factorTwoP67ResidualSmoothMixedIntegrand_add_low_eq
      (c • factorTwoCenteredP6) (f • factorTwoCenteredP8)
      (d • factorTwoCenteredP7) 0 eR oR
      (continuous_factorTwoCenteredP6.const_smul c)
      (continuous_factorTwoCenteredP8.const_smul f)
      (continuous_factorTwoCenteredP7.const_smul d) (by fun_prop)
      heRc hoRc a b,
    integral_factorTwoP67ResidualSmoothMixedIntegrand_eq
      eR oR heRc hoRc hoRo heLow8 hoLow c d a b,
    integral_factorTwoP8ResidualSmoothMixedIntegrand_eq
      eR oR heRc hoRc hoRo heLow f a b]
  unfold factorTwoP678ResidualCombinedForwardMixed
    factorTwoP67ResidualCombinedForwardMixed
  ring

/-- Exact production decomposition of the actual nonsingular regular phase
block at the cutoff-nine `P6/P7/P8` border. -/
theorem factorTwoIntrinsicRegularPhaseBlock_P678_add_residual_eq
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (hoRo : Function.Odd oR)
    (heLow : centeredLegendreMomentsVanishBelow eR 9)
    (hoLow : centeredLegendreMomentsVanishBelow oR 9)
    (c d f a b : ℝ) :
    factorTwoIntrinsicRegularPhaseBlock
        (((c • factorTwoCenteredP6) + (f • factorTwoCenteredP8)) + eR)
        ((d • factorTwoCenteredP7) + oR) a b =
      factorTwoIntrinsicRegularPhaseBlock
          ((c • factorTwoCenteredP6) + (f • factorTwoCenteredP8))
          (d • factorTwoCenteredP7) a b +
        2 * factorTwoP678ResidualCombinedForwardMixed eR oR c d f a b +
        factorTwoIntrinsicRegularPhaseBlock eR oR a b := by
  rw [factorTwoIntrinsicRegularPhaseBlock_add_add_eq
      ((c • factorTwoCenteredP6) + (f • factorTwoCenteredP8))
      (d • factorTwoCenteredP7) eR oR
      ((continuous_factorTwoCenteredP6.const_smul c).add
        (continuous_factorTwoCenteredP8.const_smul f))
      (continuous_factorTwoCenteredP7.const_smul d) heRc hoRc a b,
    integral_factorTwoP678ResidualSmoothMixedIntegrand_eq
      eR oR heRc hoRc hoRo heLow hoLow c d f a b]

/-- Exact cutoff-nine decomposition with every lower retained row left
visible.  The first mixed integral is precisely the contribution of the
unspecialized lower profiles (in production, the `P0,...,P5` rows); only the
upper `P6/P7/P8` contribution is replaced by the certified residual symbol. -/
theorem factorTwoIntrinsicRegularPhaseBlock_lower_add_P678_add_residual_eq
    (eLower oLower eR oR : ℝ → ℝ)
    (heLowerc : Continuous eLower) (hoLowerc : Continuous oLower)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (hoRo : Function.Odd oR)
    (heLow : centeredLegendreMomentsVanishBelow eR 9)
    (hoLow : centeredLegendreMomentsVanishBelow oR 9)
    (c d f a b : ℝ) :
    factorTwoIntrinsicRegularPhaseBlock
        ((eLower +
          ((c • factorTwoCenteredP6) + (f • factorTwoCenteredP8))) + eR)
        ((oLower + (d • factorTwoCenteredP7)) + oR) a b =
      factorTwoIntrinsicRegularPhaseBlock
          (eLower +
            ((c • factorTwoCenteredP6) + (f • factorTwoCenteredP8)))
          (oLower + (d • factorTwoCenteredP7)) a b +
        (∫ t : ℝ in 0..2,
          factorTwoP67ResidualSmoothMixedIntegrand
            eLower oLower eR oR a b t) +
        2 * factorTwoP678ResidualCombinedForwardMixed eR oR c d f a b +
        factorTwoIntrinsicRegularPhaseBlock eR oR a b := by
  let pE : ℝ → ℝ :=
    (c • factorTwoCenteredP6) + (f • factorTwoCenteredP8)
  let pO : ℝ → ℝ := d • factorTwoCenteredP7
  have hpEc : Continuous pE :=
    (continuous_factorTwoCenteredP6.const_smul c).add
      (continuous_factorTwoCenteredP8.const_smul f)
  have hpOc : Continuous pO := continuous_factorTwoCenteredP7.const_smul d
  rw [factorTwoIntrinsicRegularPhaseBlock_add_add_eq
      (eLower + pE) (oLower + pO) eR oR
      (heLowerc.add hpEc) (hoLowerc.add hpOc) heRc hoRc a b,
    integral_factorTwoP67ResidualSmoothMixedIntegrand_add_low_eq
      eLower pE oLower pO eR oR
      heLowerc hpEc hoLowerc hpOc heRc hoRc a b]
  have hupper := integral_factorTwoP678ResidualSmoothMixedIntegrand_eq
    eR oR heRc hoRc hoRo heLow hoLow c d f a b
  dsimp only [pE, pO] at hupper ⊢
  rw [hupper]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineResidualDecompositionStructural
