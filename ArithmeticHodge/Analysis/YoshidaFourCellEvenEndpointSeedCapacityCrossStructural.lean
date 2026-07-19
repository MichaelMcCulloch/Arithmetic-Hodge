import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCutoffEightBridgeStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped Interval

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCapacityCrossStructural

noncomputable section

open YoshidaEndpointPotentialBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoFixedLagRepresenterStructural
open YoshidaFourCellEvenEndpointCoshSchurStructural
open YoshidaFourCellEvenEndpointSeedCutoffEightBridgeStructural
open YoshidaFourCellEvenZeroCoshCoupledCoreStructural
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

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCapacityCrossStructural
