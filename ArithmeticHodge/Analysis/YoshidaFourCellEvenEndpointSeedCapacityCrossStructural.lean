import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCutoffEightBridgeStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped Interval

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCapacityCrossStructural

noncomputable section

open ShiftedLegendreCenteredParity
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoFixedLagRepresenterStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenCleanPolynomialGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenProfileCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseIntrinsicNineCanonicalProjectionStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellEvenEndpointCoshSchurStructural
open YoshidaFourCellEvenEndpointSeedCutoffEightBridgeStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEvenZeroCoshCoupledCoreStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural

/-!
# The retained cutoff-eight cross for the endpoint seed

The endpoint seed is `1 - x^2`.  Its projected capacity norm must keep the
cross between the endpoint potential and the fixed prime lag: a separate
Young estimate loses the endpoint determinant.  This file evaluates that
cross structurally, by an exact antiderivative on the sole overlap interval
`[3/5,1]`, and then uses it in the projected capacity norm.
-/

private def seedOverlapPolynomial (x : ℝ) : ℝ :=
  -(39 / 25 : ℝ) + (16 / 5) * x + (14 / 25) * x ^ 2 -
    (16 / 5) * x ^ 3 + x ^ 4

private def seedOverlapQMinus (x : ℝ) : ℝ :=
  (28 / 75 : ℝ) - (89 / 75) * x + (31 / 75) * x ^ 2 +
    (3 / 5) * x ^ 3 - (1 / 5) * x ^ 4

private def seedOverlapRMinus (x : ℝ) : ℝ :=
  (28 / 75 : ℝ) * x - (89 / 150) * x ^ 2 +
    (31 / 225) * x ^ 3 + (3 / 20) * x ^ 4 - (1 / 25) * x ^ 5

private def seedOverlapQPlus (x : ℝ) : ℝ :=
  -(148 / 75 : ℝ) + (31 / 75) * x + (89 / 75) * x ^ 2 -
    x ^ 3 + (1 / 5) * x ^ 4

private def seedOverlapRPlus (x : ℝ) : ℝ :=
  -(148 / 75 : ℝ) * x + (31 / 150) * x ^ 2 +
    (89 / 225) * x ^ 3 - (1 / 4) * x ^ 4 + (1 / 25) * x ^ 5

private def seedOverlapAntiderivativeMinus (x : ℝ) : ℝ :=
  -seedOverlapQMinus x * Real.negMulLog (1 - x) + seedOverlapRMinus x

private def seedOverlapAntiderivativePlus (x : ℝ) : ℝ :=
  ((1 + x) * seedOverlapQPlus x) * Real.log (1 + x) -
    seedOverlapRPlus x

private theorem seedOverlapAntiderivativeMinus_hasDerivAt
    {x : ℝ} (hx : x < 1) :
    HasDerivAt seedOverlapAntiderivativeMinus
      (seedOverlapPolynomial x * Real.log (1 - x)) x := by
  have hne : 1 - x ≠ 0 := by linarith
  have hinner : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1
    all_goals simp
  have hneg := (Real.hasDerivAt_negMulLog hne).comp x hinner
  have hQ : HasDerivAt seedOverlapQMinus
      (-(89 / 75 : ℝ) + 2 * (31 / 75) * x +
        3 * (3 / 5) * x ^ 2 - 4 * (1 / 5) * x ^ 3) x := by
    rw [show seedOverlapQMinus = fun t : ℝ ↦
        (28 / 75 : ℝ) - (89 / 75) * t + (31 / 75) * t ^ 2 +
          (3 / 5) * t ^ 3 - (1 / 5) * t ^ 4 by rfl]
    have h0 := hasDerivAt_const x (28 / 75 : ℝ)
    have h1 := (hasDerivAt_id x).const_mul (89 / 75 : ℝ)
    have h2 := ((hasDerivAt_id x).pow 2).const_mul (31 / 75 : ℝ)
    have h3 := ((hasDerivAt_id x).pow 3).const_mul (3 / 5 : ℝ)
    have h4 := ((hasDerivAt_id x).pow 4).const_mul (1 / 5 : ℝ)
    convert (((h0.sub h1).add h2).add h3).sub h4 using 1
    all_goals simp only [id_eq]
    all_goals ring
  have hR : HasDerivAt seedOverlapRMinus (seedOverlapQMinus x) x := by
    rw [show seedOverlapRMinus = fun t : ℝ ↦
        (28 / 75 : ℝ) * t - (89 / 150) * t ^ 2 +
          (31 / 225) * t ^ 3 + (3 / 20) * t ^ 4 -
            (1 / 25) * t ^ 5 by rfl]
    have h1 := (hasDerivAt_id x).const_mul (28 / 75 : ℝ)
    have h2 := ((hasDerivAt_id x).pow 2).const_mul (89 / 150 : ℝ)
    have h3 := ((hasDerivAt_id x).pow 3).const_mul (31 / 225 : ℝ)
    have h4 := ((hasDerivAt_id x).pow 4).const_mul (3 / 20 : ℝ)
    have h5 := ((hasDerivAt_id x).pow 5).const_mul (1 / 25 : ℝ)
    convert (((h1.sub h2).add h3).add h4).sub h5 using 1
    all_goals simp only [id_eq, seedOverlapQMinus]
    all_goals ring
  have hmain := (hQ.neg.mul hneg).add hR
  convert hmain using 1
  simp only [Real.negMulLog_def, Function.comp_apply, Pi.neg_apply]
  unfold seedOverlapPolynomial seedOverlapQMinus
  field_simp [hne]
  ring

private theorem seedOverlapAntiderivativePlus_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt seedOverlapAntiderivativePlus
      (seedOverlapPolynomial x * Real.log (1 + x)) x := by
  have hne : 1 + x ≠ 0 := by linarith
  have hinner : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 x := by
    convert (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x) using 1
    all_goals simp
  have hlog := (Real.hasDerivAt_log hne).comp x hinner
  have hQ : HasDerivAt seedOverlapQPlus
      ((31 / 75 : ℝ) + 2 * (89 / 75) * x -
        3 * x ^ 2 + 4 * (1 / 5) * x ^ 3) x := by
    rw [show seedOverlapQPlus = fun t : ℝ ↦
        -(148 / 75 : ℝ) + (31 / 75) * t + (89 / 75) * t ^ 2 -
          t ^ 3 + (1 / 5) * t ^ 4 by rfl]
    have h0 := hasDerivAt_const x (-(148 / 75 : ℝ))
    have h1 := (hasDerivAt_id x).const_mul (31 / 75 : ℝ)
    have h2 := ((hasDerivAt_id x).pow 2).const_mul (89 / 75 : ℝ)
    have h3 := (hasDerivAt_id x).pow 3
    have h4 := ((hasDerivAt_id x).pow 4).const_mul (1 / 5 : ℝ)
    convert (((h0.add h1).add h2).sub h3).add h4 using 1
    all_goals simp only [id_eq]
    all_goals ring
  have hB := hinner.mul hQ
  have hR : HasDerivAt seedOverlapRPlus (seedOverlapQPlus x) x := by
    rw [show seedOverlapRPlus = fun t : ℝ ↦
        -(148 / 75 : ℝ) * t + (31 / 150) * t ^ 2 +
          (89 / 225) * t ^ 3 - (1 / 4) * t ^ 4 +
            (1 / 25) * t ^ 5 by rfl]
    have h1 := (hasDerivAt_id x).const_mul (-(148 / 75 : ℝ))
    have h2 := ((hasDerivAt_id x).pow 2).const_mul (31 / 150 : ℝ)
    have h3 := ((hasDerivAt_id x).pow 3).const_mul (89 / 225 : ℝ)
    have h4 := ((hasDerivAt_id x).pow 4).const_mul (1 / 4 : ℝ)
    have h5 := ((hasDerivAt_id x).pow 5).const_mul (1 / 25 : ℝ)
    convert (((h1.add h2).add h3).sub h4).add h5 using 1
    all_goals simp only [id_eq, seedOverlapQPlus]
    all_goals ring
  have hmain := (hB.mul hlog).sub hR
  convert hmain using 1
  simp only [Function.comp_apply, Pi.mul_apply]
  unfold seedOverlapPolynomial seedOverlapQPlus
  field_simp [hne]
  ring

private theorem intervalIntegrable_seedOverlapPolynomial_mul_log_one_sub :
    IntervalIntegrable
      (fun x : ℝ ↦ seedOverlapPolynomial x * Real.log (1 - x))
      volume (3 / 5) 1 := by
  have hlogBase : IntervalIntegrable Real.log volume (2 / 5 : ℝ) 0 :=
    intervalIntegral.intervalIntegrable_log'
  have hlog : IntervalIntegrable (fun x : ℝ ↦ Real.log (1 - x))
      volume (3 / 5) 1 := by
    convert hlogBase.comp_sub_left 1 using 1 <;> norm_num
  have hp : Continuous seedOverlapPolynomial := by
    unfold seedOverlapPolynomial
    fun_prop
  apply (hlog.mul_continuousOn hp.continuousOn).congr
  intro x _hx
  ring

private theorem intervalIntegrable_seedOverlapPolynomial_mul_log_one_add :
    IntervalIntegrable
      (fun x : ℝ ↦ seedOverlapPolynomial x * Real.log (1 + x))
      volume (3 / 5) 1 := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
  have hne : 1 + x ≠ 0 := by linarith [hx.1]
  have harg : ContinuousAt (fun y : ℝ ↦ 1 + y) x := by fun_prop
  have hlog : ContinuousAt (fun y : ℝ ↦ Real.log (1 + y)) x :=
    (Real.continuousAt_log hne).comp harg
  exact ((by
    unfold seedOverlapPolynomial
    fun_prop : ContinuousAt seedOverlapPolynomial x).mul hlog).continuousWithinAt

private theorem integral_seedOverlapPolynomial_mul_log_one_sub :
    (∫ x : ℝ in 3 / 5..1,
      seedOverlapPolynomial x * Real.log (1 - x)) =
      -(20188 / 703125 : ℝ) +
        (1616 / 46875) * Real.log (2 / 5 : ℝ) := by
  have hcont : Continuous seedOverlapAntiderivativeMinus := by
    unfold seedOverlapAntiderivativeMinus seedOverlapQMinus
      seedOverlapRMinus
    fun_prop
  have hInt := intervalIntegrable_seedOverlapPolynomial_mul_log_one_sub
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (3 / 5 : ℝ) ≤ 1) hcont.continuousOn
    (fun x hx ↦ seedOverlapAntiderivativeMinus_hasDerivAt hx.2) hInt]
  unfold seedOverlapAntiderivativeMinus seedOverlapQMinus seedOverlapRMinus
  norm_num [Real.negMulLog_def]
  ring

private theorem integral_seedOverlapPolynomial_mul_log_one_add :
    (∫ x : ℝ in 3 / 5..1,
      seedOverlapPolynomial x * Real.log (1 + x)) =
      (371012 / 703125 : ℝ) - (176 / 75) * Real.log 2 +
        (111616 / 46875) * Real.log (8 / 5 : ℝ) := by
  have hcont : ContinuousOn seedOverlapAntiderivativePlus
      (Icc (3 / 5 : ℝ) 1) := by
    intro x hx
    have hne : 1 + x ≠ 0 := by linarith [hx.1]
    have harg : ContinuousAt (fun y : ℝ ↦ 1 + y) x := by fun_prop
    have hlog : ContinuousAt (fun y : ℝ ↦ Real.log (1 + y)) x :=
      (Real.continuousAt_log hne).comp harg
    have hB : ContinuousAt (fun y : ℝ ↦ (1 + y) * seedOverlapQPlus y) x := by
      unfold seedOverlapQPlus
      fun_prop
    have hR : ContinuousAt seedOverlapRPlus x := by
      unfold seedOverlapRPlus
      fun_prop
    unfold seedOverlapAntiderivativePlus seedOverlapQPlus seedOverlapRPlus
    exact (hB.mul hlog |>.sub hR).continuousWithinAt
  have hInt := intervalIntegrable_seedOverlapPolynomial_mul_log_one_add
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (3 / 5 : ℝ) ≤ 1) hcont
    (fun x hx ↦ seedOverlapAntiderivativePlus_hasDerivAt (by linarith [hx.1]))
    hInt]
  unfold seedOverlapAntiderivativePlus seedOverlapQPlus seedOverlapRPlus
  norm_num
  ring

private theorem log_seed_overlap_identity :
    -(1616 / 46875 : ℝ) * Real.log (2 / 5 : ℝ) +
        (176 / 75) * Real.log 2 -
        (111616 / 46875) * Real.log (8 / 5 : ℝ) =
      (37744 / 15625) * Real.log (5 / 4 : ℝ) := by
  have h2 : Real.log (2 / 5 : ℝ) = Real.log 2 - Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have h8 : Real.log (8 / 5 : ℝ) = 3 * Real.log 2 - Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    have hmul : Real.log (8 : ℝ) = Real.log 2 + Real.log 4 := by
      rw [show (8 : ℝ) = 2 * 4 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hmul, hfour]
    ring
  have h54 : Real.log (5 / 4 : ℝ) = Real.log 5 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [h2, h8, h54]
  ring

/-- Exact logarithmic overlap integral for the endpoint seed and its
translate by `8/5`. -/
theorem neg_integral_seedOverlapPolynomial_mul_log_one_sub_sq :
    -(∫ x : ℝ in 3 / 5..1,
      seedOverlapPolynomial x * Real.log (1 - x ^ 2)) =
      -(350824 / 703125 : ℝ) +
        (37744 / 15625) * Real.log (5 / 4 : ℝ) := by
  have hminus := integral_seedOverlapPolynomial_mul_log_one_sub
  have hplus := integral_seedOverlapPolynomial_mul_log_one_add
  have hIntMinus := intervalIntegrable_seedOverlapPolynomial_mul_log_one_sub
  have hIntPlus := intervalIntegrable_seedOverlapPolynomial_mul_log_one_add
  have hsplit :
      (∫ x : ℝ in 3 / 5..1,
        seedOverlapPolynomial x * Real.log (1 - x ^ 2)) =
      (∫ x : ℝ in 3 / 5..1,
        seedOverlapPolynomial x * Real.log (1 - x)) +
      (∫ x : ℝ in 3 / 5..1,
        seedOverlapPolynomial x * Real.log (1 + x)) := by
    rw [← intervalIntegral.integral_add hIntMinus hIntPlus]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ)] with x hx
    intro hxI
    rw [uIoc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hxI
    have hxlt : x < 1 := lt_of_le_of_ne hxI.2 hx
    have hm : 1 - x ≠ 0 := by linarith
    have hp : 1 + x ≠ 0 := by linarith [hxI.1]
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
      Real.log_mul hm hp]
    ring
  rw [hsplit, hminus, hplus]
  linarith [log_seed_overlap_identity]

/-! ## From the overlap interval to the full fixed-lag cross -/

/-- A continuous extension of the endpoint seed translated onto the two
fixed-lag boundary components. -/
private def endpointSeedFixedLagExtension (x : ℝ) : ℝ :=
  if x ≤ -(3 / 5 : ℝ) then fourCellEvenEndpointCoshSeed (x + 8 / 5)
  else if x ≤ (3 / 5 : ℝ) then 0
  else fourCellEvenEndpointCoshSeed (x - 8 / 5)

private theorem continuous_endpointSeedFixedLagExtension :
    Continuous endpointSeedFixedLagExtension := by
  unfold endpointSeedFixedLagExtension
  apply Continuous.if_le
    (fourCellEvenEndpointCoshSeed_continuous.comp
      (continuous_id.add continuous_const))
    (by
      apply Continuous.if_le continuous_const
        (fourCellEvenEndpointCoshSeed_continuous.comp
          (continuous_id.sub continuous_const))
        continuous_id continuous_const
      intro x hx
      unfold fourCellEvenEndpointCoshSeed
      simp only [Function.comp_apply, id_eq] at hx ⊢
      rw [hx]
      norm_num)
    continuous_id continuous_const
  intro x hx
  unfold fourCellEvenEndpointCoshSeed
  simp only [Function.comp_apply, id_eq] at hx ⊢
  rw [hx]
  norm_num

private theorem even_endpointSeedFixedLagExtension :
    Function.Even endpointSeedFixedLagExtension := by
  intro x
  by_cases hfarLeft : x < -(3 / 5 : ℝ)
  · have hxFirst : x ≤ -(3 / 5 : ℝ) := hfarLeft.le
    have hnegFirst : ¬ -x ≤ -(3 / 5 : ℝ) := by linarith
    have hnegMiddle : ¬ -x ≤ (3 / 5 : ℝ) := by linarith
    unfold endpointSeedFixedLagExtension fourCellEvenEndpointCoshSeed
    rw [if_neg hnegFirst, if_neg hnegMiddle, if_pos hxFirst]
    ring
  · by_cases hleft : x = -(3 / 5 : ℝ)
    · unfold endpointSeedFixedLagExtension fourCellEvenEndpointCoshSeed
      rw [hleft]
      norm_num
    · have hxLeft : -(3 / 5 : ℝ) < x :=
        lt_of_le_of_ne (le_of_not_gt hfarLeft) (Ne.symm hleft)
      by_cases hmiddle : x < (3 / 5 : ℝ)
      · have hxFirst : ¬ x ≤ -(3 / 5 : ℝ) := by linarith
        have hxMiddle : x ≤ (3 / 5 : ℝ) := hmiddle.le
        have hnegFirst : ¬ -x ≤ -(3 / 5 : ℝ) := by linarith
        have hnegMiddle : -x ≤ (3 / 5 : ℝ) := by linarith
        unfold endpointSeedFixedLagExtension
        rw [if_neg hnegFirst, if_pos hnegMiddle,
          if_neg hxFirst, if_pos hxMiddle]
      · by_cases hright : x = (3 / 5 : ℝ)
        · unfold endpointSeedFixedLagExtension fourCellEvenEndpointCoshSeed
          rw [hright]
          norm_num
        · have hxRight : (3 / 5 : ℝ) < x :=
            lt_of_le_of_ne (le_of_not_gt hmiddle) (Ne.symm hright)
          have hxFirst : ¬ x ≤ -(3 / 5 : ℝ) := by linarith
          have hxMiddle : ¬ x ≤ (3 / 5 : ℝ) := by linarith
          have hnegFirst : -x ≤ -(3 / 5 : ℝ) := by linarith
          unfold endpointSeedFixedLagExtension fourCellEvenEndpointCoshSeed
          rw [if_pos hnegFirst, if_neg hxFirst, if_neg hxMiddle]
          ring

private theorem canonicalLegendreCoefficient_eq_centered_pairing
    (w : ℝ → ℝ) (hw : Continuous w) (n : ℕ) (P : ℝ → ℝ)
    (hP : ∀ x : ℝ,
      (shiftedLegendreReal n).eval ((x + 1) / 2) = P x) :
    factorTwoCanonicalLegendreCoefficient w hw n =
      ((2 * (n : ℝ) + 1) / 2) *
        (∫ x : ℝ in -1..1, w x * P x) := by
  have hunit :
      (∫ t : unitInterval,
        centeredPullback w (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) =
      (1 / 2 : ℝ) * (∫ x : ℝ in -1..1, w x * P x) := by
    calc
      _ = ∫ t : ℝ in 0..1,
          centeredPullback w t * (shiftedLegendreReal n).eval t := by
        exact integral_unitInterval_eq_intervalIntegral
          (fun t : ℝ ↦
            centeredPullback w t * (shiftedLegendreReal n).eval t)
      _ = ∫ t : ℝ in 0..1, (fun x : ℝ ↦ w x * P x) (2 * t - 1) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        unfold centeredPullback
        dsimp only
        rw [← hP (2 * t - 1)]
        congr 2
        ring
      _ = _ := integral_comp_two_mul_sub_one (fun x : ℝ ↦ w x * P x)
  unfold factorTwoCanonicalLegendreCoefficient centeredPullbackL2
  rw [shiftedLegendreHilbertBasis_repr_eq
    (fun t : unitInterval ↦ centeredPullback w (t : ℝ))
    (centeredPullback_memLp_two w hw) n, hunit]
  calc
    ‖shiftedLegendreL2 n‖⁻¹ *
          ((1 / 2 : ℝ) * (∫ x : ℝ in -1..1, w x * P x)) *
        ‖shiftedLegendreL2 n‖⁻¹ =
      (‖shiftedLegendreL2 n‖⁻¹ ^ 2 / 2) *
        (∫ x : ℝ in -1..1, w x * P x) := by ring_nf
    _ = _ := by
      rw [inv_norm_shiftedLegendreL2_sq_closed]

private theorem shiftedLegendreReal_zero_centered_seedCross (x : ℝ) :
    (shiftedLegendreReal 0).eval ((x + 1) / 2) = centeredEvenP0 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredEvenP0]

private theorem shiftedLegendreReal_two_centered_seedCross (x : ℝ) :
    (shiftedLegendreReal 2).eval ((x + 1) / 2) = centeredEvenP2 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredEvenP2]
  ring

private theorem shiftedLegendreReal_four_centered_seedCross (x : ℝ) :
    (shiftedLegendreReal 4).eval ((x + 1) / 2) =
      factorTwoCenteredP4 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, factorTwoCenteredP4]
  ring

private theorem shiftedLegendreReal_six_centered_seedCross (x : ℝ) :
    (shiftedLegendreReal 6).eval ((x + 1) / 2) =
      factorTwoCenteredP6 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, factorTwoCenteredP6_eq]
  ring

private theorem fixedLagK_endpointSeed_eq_extension
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoFixedLagK (8 / 5) fourCellEvenEndpointCoshSeed x =
      endpointSeedFixedLagExtension x := by
  by_cases hneg : x ≤ -(3 / 5 : ℝ)
  · have hright : x ∈ Icc (-1 : ℝ) (1 - 8 / 5) := by
      constructor <;> norm_num at hx hneg ⊢ <;> linarith [hx.1, hneg]
    have hleft : x ∉ Icc (-1 + 8 / 5 : ℝ) 1 := by
      intro h
      norm_num at h hneg
      linarith [h.1]
    unfold endpointSeedFixedLagExtension factorTwoFixedLagK
      factorTwoFixedLagRightRepresenter factorTwoFixedLagLeftRepresenter
    rw [if_pos hneg, Set.indicator_of_mem hright,
      Set.indicator_of_notMem hleft]
    ring
  · have hneg' : -(3 / 5 : ℝ) < x := lt_of_not_ge hneg
    by_cases hmid : x ≤ (3 / 5 : ℝ)
    · have hright : x ∉ Icc (-1 : ℝ) (1 - 8 / 5) := by
        intro h
        norm_num at h
        linarith [h.2]
      by_cases heq : x = (3 / 5 : ℝ)
      · have hleft : x ∈ Icc (-1 + 8 / 5 : ℝ) 1 := by
          rw [heq]
          norm_num
        unfold endpointSeedFixedLagExtension factorTwoFixedLagK
          factorTwoFixedLagRightRepresenter factorTwoFixedLagLeftRepresenter
        rw [if_neg hneg, if_pos hmid, Set.indicator_of_notMem hright,
          Set.indicator_of_mem hleft]
        unfold fourCellEvenEndpointCoshSeed
        norm_num [heq]
      · have hleft : x ∉ Icc (-1 + 8 / 5 : ℝ) 1 := by
          intro h
          norm_num at h
          have hxlt : x < 3 / 5 := lt_of_le_of_ne hmid heq
          linarith [h.1]
        unfold endpointSeedFixedLagExtension factorTwoFixedLagK
          factorTwoFixedLagRightRepresenter factorTwoFixedLagLeftRepresenter
        rw [if_neg hneg, if_pos hmid, Set.indicator_of_notMem hright,
          Set.indicator_of_notMem hleft]
        norm_num
    · have hmid' : (3 / 5 : ℝ) < x := lt_of_not_ge hmid
      have hright : x ∉ Icc (-1 : ℝ) (1 - 8 / 5) := by
        intro h
        norm_num at h
        linarith [h.2]
      have hleft : x ∈ Icc (-1 + 8 / 5 : ℝ) 1 := by
        constructor <;> norm_num at hmid' hx ⊢ <;> linarith [hmid', hx.2]
      unfold endpointSeedFixedLagExtension factorTwoFixedLagK
        factorTwoFixedLagRightRepresenter factorTwoFixedLagLeftRepresenter
      rw [if_neg hneg, if_neg hmid, Set.indicator_of_notMem hright,
        Set.indicator_of_mem hleft]
      ring

private theorem intervalIntegrable_endpointPotential_seed_mul_fixedLagK_seed :
    IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x *
        fourCellEvenEndpointCoshSeed x *
          factorTwoFixedLagK (8 / 5) fourCellEvenEndpointCoshSeed x)
      volume (-1) 1 := by
  have hbase := intervalIntegrable_endpointPotential_mul
    (fun x : ℝ ↦ fourCellEvenEndpointCoshSeed x *
      endpointSeedFixedLagExtension x)
    (fourCellEvenEndpointCoshSeed_continuous.mul
      continuous_endpointSeedFixedLagExtension)
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Icc (-1 : ℝ) 1 := by
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    exact ⟨hx.1.le, hx.2⟩
  dsimp only
  rw [fixedLagK_endpointSeed_eq_extension hx']
  ring

/-- The full potential--fixed-lag cross generated by the endpoint seed.  The
support reduction leaves exactly the one structural overlap integral above. -/
theorem integral_endpointPotential_seed_mul_fixedLagK_seed :
    (∫ x : ℝ in -1..1,
      (yoshidaEndpointPotential x * fourCellEvenEndpointCoshSeed x) *
        factorTwoFixedLagK (8 / 5) fourCellEvenEndpointCoshSeed x) =
      -(350824 / 703125 : ℝ) +
        (37744 / 15625) * Real.log (5 / 4 : ℝ) := by
  let K : ℝ → ℝ := factorTwoFixedLagK (8 / 5) fourCellEvenEndpointCoshSeed
  let f : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * fourCellEvenEndpointCoshSeed x * K x
  have hInt : IntervalIntegrable f volume (-1) 1 := by
    simpa only [f, K, mul_assoc] using
      intervalIntegrable_endpointPotential_seed_mul_fixedLagK_seed
  have hseedEven : Function.Even fourCellEvenEndpointCoshSeed :=
    fourCellEvenEndpointCoshSeed_even
  have hKEven : Function.Even K := by
    intro x
    unfold K factorTwoFixedLagK
    rw [factorTwoFixedLagRightRepresenter_neg_of_even hseedEven,
      factorTwoFixedLagLeftRepresenter_neg_of_even hseedEven]
    ring
  have hfEven : Function.Even f := by
    intro x
    dsimp only [f]
    rw [hseedEven x, hKEven x]
    unfold yoshidaEndpointPotential
    rw [neg_sq]
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even f hInt hfEven
  have hzero : (∫ x : ℝ in 0..3 / 5, f x) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (3 / 5 : ℝ)] with x hxne hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    have hxlt : x < 3 / 5 := lt_of_le_of_ne hx.2 hxne
    have hright : x ∉ Icc (-1 : ℝ) (1 - 8 / 5) := by
      intro h
      norm_num at h
      linarith [hx.1, h.2]
    have hleft : x ∉ Icc (-1 + 8 / 5 : ℝ) 1 := by
      intro h
      norm_num at h
      linarith [hxlt, h.1]
    unfold f K factorTwoFixedLagK factorTwoFixedLagRightRepresenter
      factorTwoFixedLagLeftRepresenter
    rw [Set.indicator_of_notMem hright, Set.indicator_of_notMem hleft]
    ring
  have hright :
      (∫ x : ℝ in 3 / 5..1, f x) =
        ∫ x : ℝ in 3 / 5..1,
          yoshidaEndpointPotential x * fourCellEvenEndpointCoshSeed x *
            fourCellEvenEndpointCoshSeed (x - 8 / 5) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    have hrightNot : x ∉ Icc (-1 : ℝ) (1 - 8 / 5) := by
      intro h
      norm_num at h
      linarith [hx.1, h.2]
    have hleftMem : x ∈ Icc (-1 + 8 / 5 : ℝ) 1 := by
      constructor <;> norm_num at hx ⊢ <;> linarith [hx.1, hx.2]
    unfold f K factorTwoFixedLagK factorTwoFixedLagRightRepresenter
      factorTwoFixedLagLeftRepresenter
    rw [Set.indicator_of_notMem hrightNot,
      Set.indicator_of_mem hleftMem, zero_add]
  have hzeroI : IntervalIntegrable f volume 0 (3 / 5) :=
    hInt.mono_set (by
      intro x hx
      norm_num at hx ⊢
      constructor <;> linarith [hx.1, hx.2])
  have hrightI : IntervalIntegrable f volume (3 / 5) 1 :=
    hInt.mono_set (by
      intro x hx
      norm_num at hx ⊢
      constructor <;> linarith [hx.1, hx.2])
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hzeroI hrightI
  rw [hzero, zero_add, hright] at hsplit
  rw [← hsplit] at hfold
  have hoverlap :
      (fun x : ℝ ↦ 2 *
        (yoshidaEndpointPotential x * fourCellEvenEndpointCoshSeed x *
          fourCellEvenEndpointCoshSeed (x - 8 / 5))) =
      fun x ↦ -seedOverlapPolynomial x * Real.log (1 - x ^ 2) := by
    funext x
    unfold yoshidaEndpointPotential fourCellEvenEndpointCoshSeed
      seedOverlapPolynomial
    ring
  change (∫ x : ℝ in -1..1, f x) = _
  rw [hfold, ← intervalIntegral.integral_const_mul, hoverlap]
  rw [show (fun x : ℝ ↦
      -seedOverlapPolynomial x * Real.log (1 - x ^ 2)) =
      fun x ↦ -(seedOverlapPolynomial x * Real.log (1 - x ^ 2)) by
    funext x
    ring,
    intervalIntegral.integral_neg]
  exact neg_integral_seedOverlapPolynomial_mul_log_one_sub_sq

/-! ## The exact low cross removed by the two canonical selectors -/

/-- Polarization of the closed four-mode potential Gram gives the complete
potential row of the endpoint seed without expanding the logarithmic
integral mode by mode. -/
theorem integral_endpointPotential_seed_mul_intrinsicEvenP0246
    (d0 d2 d4 d6 : ℝ) :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * fourCellEvenEndpointCoshSeed x *
        factorTwoIntrinsicEvenP0246Profile d0 d2 d4 d6 x) =
      ((10 / 9 : ℝ) - (4 / 3) * Real.log 2) * d0 +
        (-(32 / 225 : ℝ) + (4 / 15) * Real.log 2) * d2 -
        (1 / 35 : ℝ) * d4 - (1 / 189 : ℝ) * d6 := by
  let s : ℝ → ℝ :=
    factorTwoIntrinsicEvenP0246Profile (2 / 3) (-2 / 3) 0 0
  let q : ℝ → ℝ := factorTwoIntrinsicEvenP0246Profile d0 d2 d4 d6
  let u : ℝ → ℝ :=
    factorTwoIntrinsicEvenP0246Profile (2 / 3 + d0) (-2 / 3 + d2) d4 d6
  have hs : Continuous s := by
    simpa only [s] using
      continuous_factorTwoIntrinsicEvenP0246Profile (2 / 3) (-2 / 3) 0 0
  have hq : Continuous q := by
    simpa only [q] using
      continuous_factorTwoIntrinsicEvenP0246Profile d0 d2 d4 d6
  have hu : u = s + q := by
    funext x
    unfold u s q factorTwoIntrinsicEvenP0246Profile
      factorTwoIntrinsicEvenP024Profile factorTwoEvenStructuralLowProfile
      factorTwoIntrinsicSixEvenTail
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hss := integral_endpointPotential_mul_intrinsicEvenP0246_sq
    (2 / 3) (-2 / 3) 0 0
  have hqq := integral_endpointPotential_mul_intrinsicEvenP0246_sq
    d0 d2 d4 d6
  have huu := integral_endpointPotential_mul_intrinsicEvenP0246_sq
    (2 / 3 + d0) (-2 / 3 + d2) d4 d6
  have hSsq := intervalIntegrable_endpointPotential_mul_sq s hs
  have hQsq := intervalIntegrable_endpointPotential_mul_sq q hq
  have hcross := YoshidaEndpointEvenTailRepresenter.intervalIntegrable_endpointPotential_mul
    s q hs hq
  have hpolar :
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x ^ 2) =
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * s x ^ 2) +
          2 * (∫ x : ℝ in -1..1,
            yoshidaEndpointPotential x * s x * q x) +
          ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * q x ^ 2 := by
    rw [hu, show (fun x : ℝ ↦
        yoshidaEndpointPotential x * (s + q) x ^ 2) =
      fun x ↦ yoshidaEndpointPotential x * s x ^ 2 +
        (2 * (yoshidaEndpointPotential x * s x * q x) +
          yoshidaEndpointPotential x * q x ^ 2) by
      funext x
      simp only [Pi.add_apply]
      ring,
      intervalIntegral.integral_add hSsq
        ((hcross.const_mul 2).add hQsq),
      intervalIntegral.integral_add (hcross.const_mul 2) hQsq,
      intervalIntegral.integral_const_mul]
    ring
  rw [show fourCellEvenEndpointCoshSeed = s by
    simpa only [s] using
      fourCellEvenEndpointCoshSeed_eq_intrinsicEvenP0246Profile]
  change (∫ x : ℝ in -1..1,
    yoshidaEndpointPotential x * s x * q x) = _
  rw [hss] at hpolar
  change (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * q x ^ 2) =
    factorTwoP6EvenPotentialGram d0 d2 d4 d6 at hqq
  rw [hqq] at hpolar
  change (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * u x ^ 2) =
    factorTwoP6EvenPotentialGram
      (2 / 3 + d0) (-2 / 3 + d2) d4 d6 at huu
  rw [huu] at hpolar
  unfold factorTwoP6EvenPotentialGram at hpolar
  linarith

/-- The low potential--fixed-lag cross removed at cutoff eight. -/
theorem integral_endpointPotential_seed_mul_fixedLagSelector :
    (∫ x : ℝ in -1..1,
      (yoshidaEndpointPotential x * fourCellEvenEndpointCoshSeed x) *
        centeredPolynomialLift
          (fourCellEvenP0246CutoffEightFixedLagSelectorPolynomial
            (2 / 3) (-2 / 3) 0 0) x) =
      (32424568 / 369140625 : ℝ) -
        (3232 / 46875) * Real.log 2 := by
  rw [centeredPolynomialLift_cutoffEightFixedLagSelector]
  have h := integral_endpointPotential_seed_mul_intrinsicEvenP0246
    (fourCellEvenP0246CutoffEightFixedLagRow0
      (2 / 3) (-2 / 3) 0 0 / 2)
    (5 * fourCellEvenP0246CutoffEightFixedLagRow2
      (2 / 3) (-2 / 3) 0 0 / 2)
    (9 * fourCellEvenP0246CutoffEightFixedLagRow4
      (2 / 3) (-2 / 3) 0 0 / 2)
    (13 * fourCellEvenP0246CutoffEightFixedLagRow6
      (2 / 3) (-2 / 3) 0 0 / 2)
  simpa only [mul_assoc] using (by
    unfold fourCellEvenP0246CutoffEightFixedLagRow0
      fourCellEvenP0246CutoffEightFixedLagRow2
      fourCellEvenP0246CutoffEightFixedLagRow4
      fourCellEvenP0246CutoffEightFixedLagRow6 at h ⊢
    norm_num at h ⊢
    linarith :
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * fourCellEvenEndpointCoshSeed x *
          factorTwoIntrinsicEvenP0246Profile
            (fourCellEvenP0246CutoffEightFixedLagRow0
              (2 / 3) (-2 / 3) 0 0 / 2)
            (5 * fourCellEvenP0246CutoffEightFixedLagRow2
              (2 / 3) (-2 / 3) 0 0 / 2)
            (9 * fourCellEvenP0246CutoffEightFixedLagRow4
              (2 / 3) (-2 / 3) 0 0 / 2)
            (13 * fourCellEvenP0246CutoffEightFixedLagRow6
              (2 / 3) (-2 / 3) 0 0 / 2) x) =
        (32424568 / 369140625 : ℝ) -
          (3232 / 46875) * Real.log 2)

private theorem integral_fixedLagExtension_mul_P0 :
    (∫ x : ℝ in -1..1,
      endpointSeedFixedLagExtension x * centeredEvenP0 x) =
      fourCellEvenP0246CutoffEightFixedLagRow0
        (2 / 3) (-2 / 3) 0 0 := by
  calc
    _ = ∫ x : ℝ in -1..1,
        factorTwoFixedLagK (8 / 5) fourCellEvenEndpointCoshSeed x *
          centeredEvenP0 x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      dsimp only
      rw [fixedLagK_endpointSeed_eq_extension ⟨hx.1, hx.2⟩]
    _ = _ := by
      have h := integral_fixedLagK_intrinsicEvenP0246_mul_P0
        (2 / 3) (-2 / 3) 0 0
      rw [← fourCellEvenEndpointCoshSeed_eq_intrinsicEvenP0246Profile] at h
      exact h

private theorem integral_fixedLagExtension_mul_P2 :
    (∫ x : ℝ in -1..1,
      endpointSeedFixedLagExtension x * centeredEvenP2 x) =
      fourCellEvenP0246CutoffEightFixedLagRow2
        (2 / 3) (-2 / 3) 0 0 := by
  calc
    _ = ∫ x : ℝ in -1..1,
        factorTwoFixedLagK (8 / 5) fourCellEvenEndpointCoshSeed x *
          centeredEvenP2 x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      dsimp only
      rw [fixedLagK_endpointSeed_eq_extension ⟨hx.1, hx.2⟩]
    _ = _ := by
      have h := integral_fixedLagK_intrinsicEvenP0246_mul_P2
        (2 / 3) (-2 / 3) 0 0
      rw [← fourCellEvenEndpointCoshSeed_eq_intrinsicEvenP0246Profile] at h
      exact h

private theorem integral_fixedLagExtension_mul_P4 :
    (∫ x : ℝ in -1..1,
      endpointSeedFixedLagExtension x * factorTwoCenteredP4 x) =
      fourCellEvenP0246CutoffEightFixedLagRow4
        (2 / 3) (-2 / 3) 0 0 := by
  calc
    _ = ∫ x : ℝ in -1..1,
        factorTwoFixedLagK (8 / 5) fourCellEvenEndpointCoshSeed x *
          factorTwoCenteredP4 x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      dsimp only
      rw [fixedLagK_endpointSeed_eq_extension ⟨hx.1, hx.2⟩]
    _ = _ := by
      have h := integral_fixedLagK_intrinsicEvenP0246_mul_P4
        (2 / 3) (-2 / 3) 0 0
      rw [← fourCellEvenEndpointCoshSeed_eq_intrinsicEvenP0246Profile] at h
      exact h

private theorem integral_fixedLagExtension_mul_P6 :
    (∫ x : ℝ in -1..1,
      endpointSeedFixedLagExtension x * factorTwoCenteredP6 x) =
      fourCellEvenP0246CutoffEightFixedLagRow6
        (2 / 3) (-2 / 3) 0 0 := by
  calc
    _ = ∫ x : ℝ in -1..1,
        factorTwoFixedLagK (8 / 5) fourCellEvenEndpointCoshSeed x *
          factorTwoCenteredP6 x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      dsimp only
      rw [fixedLagK_endpointSeed_eq_extension ⟨hx.1, hx.2⟩]
    _ = _ := by
      have h := integral_fixedLagK_intrinsicEvenP0246_mul_P6
        (2 / 3) (-2 / 3) 0 0
      rw [← fourCellEvenEndpointCoshSeed_eq_intrinsicEvenP0246Profile] at h
      exact h

private theorem centeredLegendreLowProjection_fixedLagExtension_eq_selector :
    centeredLegendreLowProjection endpointSeedFixedLagExtension
        continuous_endpointSeedFixedLagExtension 8 =
      centeredPolynomialLift
        (fourCellEvenP0246CutoffEightFixedLagSelectorPolynomial
          (2 / 3) (-2 / 3) 0 0) := by
  have hc0 : factorTwoCanonicalLegendreCoefficient
      endpointSeedFixedLagExtension continuous_endpointSeedFixedLagExtension 0 =
      fourCellEvenP0246CutoffEightFixedLagRow0
        (2 / 3) (-2 / 3) 0 0 / 2 := by
    rw [canonicalLegendreCoefficient_eq_centered_pairing
      endpointSeedFixedLagExtension continuous_endpointSeedFixedLagExtension
      0 centeredEvenP0 shiftedLegendreReal_zero_centered_seedCross,
      integral_fixedLagExtension_mul_P0]
    ring_nf
  have hc2 : factorTwoCanonicalLegendreCoefficient
      endpointSeedFixedLagExtension continuous_endpointSeedFixedLagExtension 2 =
      5 * fourCellEvenP0246CutoffEightFixedLagRow2
        (2 / 3) (-2 / 3) 0 0 / 2 := by
    rw [canonicalLegendreCoefficient_eq_centered_pairing
      endpointSeedFixedLagExtension continuous_endpointSeedFixedLagExtension
      2 centeredEvenP2 shiftedLegendreReal_two_centered_seedCross,
      integral_fixedLagExtension_mul_P2]
    ring_nf
  have hc4 : factorTwoCanonicalLegendreCoefficient
      endpointSeedFixedLagExtension continuous_endpointSeedFixedLagExtension 4 =
      9 * fourCellEvenP0246CutoffEightFixedLagRow4
        (2 / 3) (-2 / 3) 0 0 / 2 := by
    rw [canonicalLegendreCoefficient_eq_centered_pairing
      endpointSeedFixedLagExtension continuous_endpointSeedFixedLagExtension
      4 factorTwoCenteredP4 shiftedLegendreReal_four_centered_seedCross,
      integral_fixedLagExtension_mul_P4]
    ring_nf
  have hc6 : factorTwoCanonicalLegendreCoefficient
      endpointSeedFixedLagExtension continuous_endpointSeedFixedLagExtension 6 =
      13 * fourCellEvenP0246CutoffEightFixedLagRow6
        (2 / 3) (-2 / 3) 0 0 / 2 := by
    rw [canonicalLegendreCoefficient_eq_centered_pairing
      endpointSeedFixedLagExtension continuous_endpointSeedFixedLagExtension
      6 factorTwoCenteredP6 shiftedLegendreReal_six_centered_seedCross,
      integral_fixedLagExtension_mul_P6]
    ring_nf
  rw [centeredLegendreLowProjection_eight_eq_intrinsicEvenP0246Profile
      endpointSeedFixedLagExtension continuous_endpointSeedFixedLagExtension
      even_endpointSeedFixedLagExtension,
    centeredPolynomialLift_cutoffEightFixedLagSelector,
    hc0, hc2, hc4, hc6]

private def endpointSeedProjectedFixedLagExtension (x : ℝ) : ℝ :=
  endpointSeedFixedLagExtension x -
    centeredPolynomialLift
      (fourCellEvenP0246CutoffEightFixedLagSelectorPolynomial
        (2 / 3) (-2 / 3) 0 0) x

private theorem continuous_endpointSeedProjectedFixedLagExtension :
    Continuous endpointSeedProjectedFixedLagExtension := by
  unfold endpointSeedProjectedFixedLagExtension
  exact continuous_endpointSeedFixedLagExtension.sub (by
    unfold centeredPolynomialLift
    fun_prop)

private theorem endpointSeedProjectedFixedLagExtension_momentsVanishBelow :
    centeredLegendreMomentsVanishBelow
      endpointSeedProjectedFixedLagExtension 8 := by
  have h := centeredLegendreHigherResidual_momentsVanishBelow
    endpointSeedFixedLagExtension continuous_endpointSeedFixedLagExtension 8
  have heq : centeredLegendreHigherResidual endpointSeedFixedLagExtension
      continuous_endpointSeedFixedLagExtension 8 =
      endpointSeedProjectedFixedLagExtension := by
    funext x
    unfold centeredLegendreHigherResidual
      endpointSeedProjectedFixedLagExtension
    rw [centeredLegendreLowProjection_fixedLagExtension_eq_selector]
  rw [heq] at h
  exact h

private theorem projectedFixedLagRepresenter_seed_eq_extension
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    fourCellEvenP0246CutoffEightProjectedFixedLagRepresenter
        (2 / 3) (-2 / 3) 0 0 x =
      endpointSeedProjectedFixedLagExtension x := by
  unfold fourCellEvenP0246CutoffEightProjectedFixedLagRepresenter
    endpointSeedProjectedFixedLagExtension
  rw [← fourCellEvenEndpointCoshSeed_eq_intrinsicEvenP0246Profile,
    fixedLagK_endpointSeed_eq_extension hx]

/-- The potential selector is exactly orthogonal to the projected fixed-lag
tail.  This is the cancellation which permits subtraction of only the one
finite low cross computed above. -/
theorem integral_potentialSelector_mul_projectedFixedLag_seed_eq_zero :
    (∫ x : ℝ in -1..1,
      centeredPolynomialLift
          (fourCellEvenP0246CutoffEightPotentialSelectorPolynomial
            (2 / 3) (-2 / 3) 0 0) x *
        fourCellEvenP0246CutoffEightProjectedFixedLagRepresenter
          (2 / 3) (-2 / 3) 0 0 x) = 0 := by
  let q : ℝ[X] := fourCellEvenP0246CutoffEightPotentialSelectorPolynomial
    (2 / 3) (-2 / 3) 0 0
  have hzero := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    q endpointSeedProjectedFixedLagExtension
      continuous_endpointSeedProjectedFixedLagExtension
      endpointSeedProjectedFixedLagExtension_momentsVanishBelow
      (natDegree_fourCellEvenP0246CutoffEightPotentialSelectorPolynomial_lt_eight
        (2 / 3) (-2 / 3) 0 0)
  calc
    _ = ∫ x : ℝ in -1..1,
        centeredPolynomialLift q x *
          endpointSeedProjectedFixedLagExtension x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      dsimp only
      rw [projectedFixedLagRepresenter_seed_eq_extension
        ⟨hx.1, hx.2⟩]
    _ = 0 := hzero

/-- Exact retained cross between the projected endpoint-potential and
fixed-lag representers for the endpoint seed.  The only transcendental
terms are the full overlap logarithm and the finite low-block logarithm. -/
theorem integral_projectedPotential_mul_projectedFixedLag_seed :
    (∫ x : ℝ in -1..1,
      fourCellEvenP0246CutoffEightProjectedPotentialRepresenter
          (2 / 3) (-2 / 3) 0 0 x *
        fourCellEvenP0246CutoffEightProjectedFixedLagRepresenter
          (2 / 3) (-2 / 3) 0 0 x) =
      -(216607168 / 369140625 : ℝ) +
        (3232 / 46875) * Real.log 2 +
        (37744 / 15625) * Real.log (5 / 4 : ℝ) := by
  let S : ℝ → ℝ := centeredPolynomialLift
    (fourCellEvenP0246CutoffEightPotentialSelectorPolynomial
      (2 / 3) (-2 / 3) 0 0)
  let T : ℝ → ℝ := centeredPolynomialLift
    (fourCellEvenP0246CutoffEightFixedLagSelectorPolynomial
      (2 / 3) (-2 / 3) 0 0)
  let V : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * fourCellEvenEndpointCoshSeed x
  let K : ℝ → ℝ :=
    factorTwoFixedLagK (8 / 5) fourCellEvenEndpointCoshSeed
  let KR : ℝ → ℝ :=
    fourCellEvenP0246CutoffEightProjectedFixedLagRepresenter
      (2 / 3) (-2 / 3) 0 0
  have hVK : IntervalIntegrable (fun x : ℝ ↦ V x * K x)
      volume (-1) 1 := by
    simpa only [V, K, mul_assoc] using
      intervalIntegrable_endpointPotential_seed_mul_fixedLagK_seed
  have hVT : IntervalIntegrable (fun x : ℝ ↦ V x * T x)
      volume (-1) 1 := by
    have h := intervalIntegrable_endpointPotential_mul
      (fun x : ℝ ↦ fourCellEvenEndpointCoshSeed x * T x)
      (fourCellEvenEndpointCoshSeed_continuous.mul (by
        dsimp only [T]
        unfold centeredPolynomialLift
        fun_prop))
    simpa only [V, mul_assoc] using h
  have hVKR : IntervalIntegrable (fun x : ℝ ↦ V x * KR x)
      volume (-1) 1 := by
    apply (hVK.sub hVT).congr
    intro x hx
    have hx' : x ∈ Icc (-1 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      exact ⟨hx.1.le, hx.2⟩
    dsimp only [KR, V, K, T]
    unfold fourCellEvenP0246CutoffEightProjectedFixedLagRepresenter
    rw [← fourCellEvenEndpointCoshSeed_eq_intrinsicEvenP0246Profile]
    ring
  have hSKR : IntervalIntegrable (fun x : ℝ ↦ S x * KR x)
      volume (-1) 1 := by
    have hcontinuous : Continuous
        (fun x : ℝ ↦ S x * endpointSeedProjectedFixedLagExtension x) := by
      apply Continuous.mul
      · dsimp only [S]
        unfold centeredPolynomialLift
        fun_prop
      · exact continuous_endpointSeedProjectedFixedLagExtension
    apply hcontinuous.intervalIntegrable (-1) 1 |>.congr
    intro x hx
    have hx' : x ∈ Icc (-1 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      exact ⟨hx.1.le, hx.2⟩
    dsimp only [KR]
    rw [projectedFixedLagRepresenter_seed_eq_extension hx']
  calc
    _ = ∫ x : ℝ in -1..1,
        V x * KR x - S x * KR x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [V, KR, S]
      rw [projectedPotentialRepresenter_eq_potential_sub_selector,
        ← fourCellEvenEndpointCoshSeed_eq_intrinsicEvenP0246Profile]
      ring
    _ = (∫ x : ℝ in -1..1, V x * KR x) -
        ∫ x : ℝ in -1..1, S x * KR x :=
      intervalIntegral.integral_sub hVKR hSKR
    _ = ∫ x : ℝ in -1..1, V x * KR x := by
      have horth :=
        integral_potentialSelector_mul_projectedFixedLag_seed_eq_zero
      simpa only [S, KR] using (by rw [horth, sub_zero] :
        (∫ x : ℝ in -1..1, V x * KR x) -
            ∫ x : ℝ in -1..1, S x * KR x =
          ∫ x : ℝ in -1..1, V x * KR x)
    _ = ∫ x : ℝ in -1..1, V x * K x - V x * T x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [KR, K, T]
      unfold fourCellEvenP0246CutoffEightProjectedFixedLagRepresenter
      rw [← fourCellEvenEndpointCoshSeed_eq_intrinsicEvenP0246Profile]
      ring
    _ = (∫ x : ℝ in -1..1, V x * K x) -
        ∫ x : ℝ in -1..1, V x * T x :=
      intervalIntegral.integral_sub hVK hVT
    _ = _ := by
      rw [show (∫ x : ℝ in -1..1, V x * K x) =
          -(350824 / 703125 : ℝ) +
            (37744 / 15625) * Real.log (5 / 4 : ℝ) by
        simpa only [V, K] using
          integral_endpointPotential_seed_mul_fixedLagK_seed,
        show (∫ x : ℝ in -1..1, V x * T x) =
          (32424568 / 369140625 : ℝ) -
            (3232 / 46875) * Real.log 2 by
        simpa only [V, T, mul_assoc] using
          integral_endpointPotential_seed_mul_fixedLagSelector]
      ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCapacityCrossStructural
