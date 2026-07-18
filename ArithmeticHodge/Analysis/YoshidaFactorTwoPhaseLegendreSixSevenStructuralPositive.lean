import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
import ArithmeticHodge.Analysis.YoshidaEndpointScalarStructuralUpper

set_option autoImplicit false

open Complex MeasureTheory Polynomial Real Set
open scoped BigOperators unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

open ShiftedLegendreCenteredParity
open ShiftedLegendreBasis
open ShiftedLegendreL2Basis
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaConstantBounds
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialExactLowMode
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointScalarStructuralUpper
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
open YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
open YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingCorrelations
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

noncomputable section

/-!
# The structural centered Legendre `P6/P7` phase block

This is the next parity pair after the intrinsic six-mode block.  The two
profiles are defined by transporting the existing shifted-Legendre family,
then normalized by the classical convention `P_n(1) = 1`.  The proof keeps
the endpoint potential and the complete alternating entry intact.  Its only
analytic kernel error is the same global `1/1000` regular-weight error used
for the structural `P4/P5` alternating entries.
-/

/-! ## The transported modes -/

/-- Classical centered Legendre `P6`, transported from the shifted basis. -/
def factorTwoCenteredP6 (x : ℝ) : ℝ :=
  (shiftedLegendreReal 6).eval ((x + 1) / 2)

/-- Classical centered Legendre `P7`.  The shifted convention contributes
the displayed parity sign. -/
def factorTwoCenteredP7 (x : ℝ) : ℝ :=
  -(shiftedLegendreReal 7).eval ((x + 1) / 2)

theorem factorTwoCenteredP6_eq (x : ℝ) :
    factorTwoCenteredP6 x =
      (231 * x ^ 6 - 315 * x ^ 4 + 105 * x ^ 2 - 5) / 16 := by
  unfold factorTwoCenteredP6 shiftedLegendreReal
  simp [Polynomial.shiftedLegendre, Finset.sum_range_succ, Nat.choose]
  ring

theorem factorTwoCenteredP7_eq (x : ℝ) :
    factorTwoCenteredP7 x =
      (429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16 := by
  unfold factorTwoCenteredP7 shiftedLegendreReal
  simp [Polynomial.shiftedLegendre, Finset.sum_range_succ, Nat.choose]
  ring

theorem continuous_factorTwoCenteredP6 : Continuous factorTwoCenteredP6 := by
  rw [show factorTwoCenteredP6 = fun x ↦
      (231 * x ^ 6 - 315 * x ^ 4 + 105 * x ^ 2 - 5) / 16 by
    funext x
    exact factorTwoCenteredP6_eq x]
  fun_prop

theorem continuous_factorTwoCenteredP7 : Continuous factorTwoCenteredP7 := by
  rw [show factorTwoCenteredP7 = fun x ↦
      (429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16 by
    funext x
    exact factorTwoCenteredP7_eq x]
  fun_prop

theorem even_factorTwoCenteredP6 : Function.Even factorTwoCenteredP6 := by
  intro x
  rw [factorTwoCenteredP6_eq, factorTwoCenteredP6_eq]
  ring

theorem odd_factorTwoCenteredP7 : Function.Odd factorTwoCenteredP7 := by
  intro x
  rw [factorTwoCenteredP7_eq, factorTwoCenteredP7_eq]
  ring

theorem locallyLipschitzOn_factorTwoCenteredP6 :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) factorTwoCenteredP6 := by
  have h : ContDiff ℝ 1 factorTwoCenteredP6 := by
    rw [show factorTwoCenteredP6 = fun x ↦
        (231 * x ^ 6 - 315 * x ^ 4 + 105 * x ^ 2 - 5) / 16 by
      funext x
      exact factorTwoCenteredP6_eq x]
    fun_prop
  exact h.locallyLipschitz.locallyLipschitzOn

theorem locallyLipschitzOn_factorTwoCenteredP7 :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) factorTwoCenteredP7 := by
  have h : ContDiff ℝ 1 factorTwoCenteredP7 := by
    rw [show factorTwoCenteredP7 = fun x ↦
        (429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16 by
      funext x
      exact factorTwoCenteredP7_eq x]
    fun_prop
  exact h.locallyLipschitz.locallyLipschitzOn

theorem centeredPullback_factorTwoCenteredP6 (t : ℝ) :
    centeredPullback factorTwoCenteredP6 t =
      (shiftedLegendreReal 6).eval t := by
  unfold centeredPullback factorTwoCenteredP6
  congr 1
  ring

theorem centeredPullback_factorTwoCenteredP7 (t : ℝ) :
    centeredPullback factorTwoCenteredP7 t =
      -(shiftedLegendreReal 7).eval t := by
  unfold centeredPullback factorTwoCenteredP7
  congr 2
  ring

theorem factorTwoCenteredP6_momentsVanishBelow :
    centeredLegendreMomentsVanishBelow factorTwoCenteredP6 6 := by
  intro n hn
  rw [show (fun t : unitInterval ↦
      centeredPullback factorTwoCenteredP6 (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) =
      fun t : unitInterval ↦
        (shiftedLegendreReal 6).eval (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ) by
    funext t
    rw [centeredPullback_factorTwoCenteredP6]]
  change (∫ t : unitInterval,
    (fun x : ℝ ↦ (shiftedLegendreReal 6).eval x *
      (shiftedLegendreReal n).eval x) (t : ℝ)) = 0
  rw [integral_unitInterval_eq_intervalIntegral
    (fun x : ℝ ↦ (shiftedLegendreReal 6).eval x *
      (shiftedLegendreReal n).eval x)]
  exact integral_shiftedLegendreReal_mul_eq_zero (by omega)

theorem factorTwoCenteredP7_momentsVanishBelow :
    centeredLegendreMomentsVanishBelow factorTwoCenteredP7 7 := by
  intro n hn
  rw [show (fun t : unitInterval ↦
      centeredPullback factorTwoCenteredP7 (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) =
      fun t : unitInterval ↦
        -((shiftedLegendreReal 7).eval (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) by
    funext t
    rw [centeredPullback_factorTwoCenteredP7]
    ring]
  rw [integral_neg]
  change -(∫ t : unitInterval,
    (fun x : ℝ ↦ (shiftedLegendreReal 7).eval x *
      (shiftedLegendreReal n).eval x) (t : ℝ)) = 0
  rw [integral_unitInterval_eq_intervalIntegral
      (fun x : ℝ ↦ (shiftedLegendreReal 7).eval x *
        (shiftedLegendreReal n).eval x),
    integral_shiftedLegendreReal_mul_eq_zero (by omega), neg_zero]

/-! ## Exact masses and raw harmonic gaps -/

theorem integral_factorTwoCenteredP6_sq :
    (∫ x : ℝ in -1..1, factorTwoCenteredP6 x ^ 2) = 2 / 13 := by
  rw [show (fun x : ℝ ↦ factorTwoCenteredP6 x ^ 2) = fun x ↦
      ((231 * x ^ 6 - 315 * x ^ 4 + 105 * x ^ 2 - 5) / 16) ^ 2 by
    funext x
    rw [factorTwoCenteredP6_eq]]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num

theorem integral_factorTwoCenteredP7_sq :
    (∫ x : ℝ in -1..1, factorTwoCenteredP7 x ^ 2) = 2 / 15 := by
  rw [show (fun x : ℝ ↦ factorTwoCenteredP7 x ^ 2) = fun x ↦
      ((429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16) ^ 2 by
    funext x
    rw [factorTwoCenteredP7_eq]]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num

theorem factorTwoCenteredP6_energy :
    factorTwoIntrinsicEnergy factorTwoCenteredP6 = 2 / 13 := by
  exact integral_factorTwoCenteredP6_sq

theorem factorTwoCenteredP7_energy :
    factorTwoIntrinsicEnergy factorTwoCenteredP7 = 2 / 15 := by
  exact integral_factorTwoCenteredP7_sq

theorem factorTwoCenteredP6_raw_reserve :
    (harmonic 6 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP6 ≤
      centeredRawLogEnergy factorTwoCenteredP6 / 4 :=
  harmonic_mul_intrinsicEnergy_le_raw_div_four factorTwoCenteredP6
    continuous_factorTwoCenteredP6 locallyLipschitzOn_factorTwoCenteredP6
    6 factorTwoCenteredP6_momentsVanishBelow

theorem factorTwoCenteredP7_raw_reserve :
    (harmonic 7 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP7 ≤
      centeredRawLogEnergy factorTwoCenteredP7 / 4 :=
  harmonic_mul_intrinsicEnergy_le_raw_div_four factorTwoCenteredP7
    continuous_factorTwoCenteredP7 locallyLipschitzOn_factorTwoCenteredP7
    7 factorTwoCenteredP7_momentsVanishBelow

/-! ## Two further exact endpoint-potential moments -/

/-- The logarithmic `1-x` moment is a finite binomial transform of the
standard power--log moment.  The statement remains symbolic in the degree;
only the two final rational specializations are normalized below. -/
private theorem integral_pow_mul_log_one_sub (n : ℕ) :
    (∫ x : ℝ in 0..1, x ^ n * Real.log (1 - x)) =
      ∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℝ) * (-1 : ℝ) ^ k) *
          (-(1 : ℝ) / (k + 1) ^ 2) := by
  let g : ℝ → ℝ := fun y ↦ (1 - y) ^ n * Real.log y
  calc
    (∫ x : ℝ in 0..1, x ^ n * Real.log (1 - x)) =
        ∫ x : ℝ in 0..1, g (1 - x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [g]
      ring
    _ = ∫ x : ℝ in 0..1, g x := by
      simpa only [sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_left (f := g)
          (a := (0 : ℝ)) (b := 1) 1)
    _ = ∫ x : ℝ in 0..1,
        ∑ k ∈ Finset.range (n + 1),
          ((n.choose k : ℝ) * (-1 : ℝ) ^ k) *
            (x ^ k * Real.log x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [g]
      rw [show (1 - x) ^ n =
          ∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℝ) * (-1 : ℝ) ^ k * x ^ k by
        rw [show 1 - x = -x + 1 by ring, add_pow]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [one_pow]
        rw [neg_pow]
        ring]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ k ∈ Finset.range (n + 1),
        ∫ x : ℝ in 0..1,
          ((n.choose k : ℝ) * (-1 : ℝ) ^ k) *
            (x ^ k * Real.log x) := by
      apply intervalIntegral.integral_finset_sum
      intro k hk
      exact (intervalIntegral.intervalIntegrable_log'.continuousOn_mul
        (continuous_pow k).continuousOn).const_mul _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [intervalIntegral.integral_const_mul,
        integral_pow_mul_log_zero_one]
      ring

private theorem integral_twelfth_mul_log_one_sub :
    (∫ x : ℝ in 0..1, x ^ 12 * Real.log (1 - x)) =
      -1145993 / 4684680 := by
  rw [integral_pow_mul_log_one_sub]
  norm_num [Finset.sum_range_succ, Nat.choose]

private theorem integral_fourteenth_mul_log_one_sub :
    (∫ x : ℝ in 0..1, x ^ 14 * Real.log (1 - x)) =
      -1195757 / 5405400 := by
  rw [integral_pow_mul_log_one_sub]
  norm_num [Finset.sum_range_succ, Nat.choose]

private theorem integral_inv_one_add :
    (∫ x : ℝ in 0..1, 1 / (1 + x)) = Real.log 2 := by
  let F : ℝ → ℝ := fun x ↦ Real.log (1 + x)
  have hderiv (x : ℝ) (hx : 1 + x ≠ 0) :
      HasDerivAt F (1 / (1 + x)) x := by
    have hadd : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 x := by
      simpa using (hasDerivAt_const x 1).add (hasDerivAt_id x)
    simpa only [F, Function.comp_apply, one_div, mul_one] using
      (Real.hasDerivAt_log hx).comp x hadd
  have hcont : ContinuousOn (fun x : ℝ ↦ 1 / (1 + x))
      (uIcc (0 : ℝ) 1) := by
    intro x hx
    have hxu : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hne : 1 + x ≠ 0 := by linarith [hxu.1]
    exact (continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ hderiv x (by
      have hxu : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      linarith [hxu.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num

/-- Integration by parts reduces the regular `log (1+x)` moment to one
finite alternating quotient integral. -/
private theorem integral_pow_mul_log_one_add_eq_quotient (n : ℕ) :
    (∫ x : ℝ in 0..1, x ^ n * Real.log (1 + x)) =
      Real.log 2 / (n + 1) -
        (1 / (n + 1 : ℝ)) *
          ∫ x : ℝ in 0..1, x ^ (n + 1) / (1 + x) := by
  let u : ℝ → ℝ := fun x ↦ Real.log (1 + x)
  let u' : ℝ → ℝ := fun x ↦ 1 / (1 + x)
  let v : ℝ → ℝ := fun x ↦ x ^ (n + 1) / (n + 1)
  let v' : ℝ → ℝ := fun x ↦ x ^ n
  have hv (x : ℝ) : HasDerivAt v (v' x) x := by
    dsimp only [v, v']
    convert ((hasDerivAt_id x).pow (n + 1)).div_const (n + 1) using 1
    · simp only [id_eq, Nat.cast_add, Nat.cast_one]
      field_simp
      rw [Nat.add_sub_cancel]
  have huOn : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt u (u' x) x := by
    intro x hx
    have hxu : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hne : 1 + x ≠ 0 := by linarith [hxu.1]
    have hadd : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 x := by
      simpa using (hasDerivAt_const x 1).add (hasDerivAt_id x)
    simpa only [u, u', Function.comp_apply, one_div, mul_one] using
      (Real.hasDerivAt_log hne).comp x hadd
  have hvOn : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt v (v' x) x :=
    fun x _hx ↦ hv x
  have huI : IntervalIntegrable u' volume 0 1 := by
    dsimp only [u']
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hxu : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hne : 1 + x ≠ 0 := by linarith [hxu.1]
    exact (continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hvI : IntervalIntegrable v' volume 0 1 := by
    dsimp only [v']
    exact (continuous_pow n).intervalIntegrable 0 1
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    huOn hvOn huI hvI
  have hleft :
      (∫ x : ℝ in 0..1, u x * v' x) =
        ∫ x : ℝ in 0..1, x ^ n * Real.log (1 + x) := by
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [u, v']
    ring
  rw [hleft] at hparts
  dsimp only [u, u', v, v'] at hparts
  norm_num only [one_pow, zero_pow (Nat.succ_ne_zero n), Nat.cast_add,
    Nat.cast_one, zero_div, mul_zero, Real.log_one, zero_mul, zero_sub] at hparts
  have hfactor :
      (∫ x : ℝ in 0..1,
          1 / (1 + x) * (x ^ (n + 1) / (n + 1))) =
        (1 / (n + 1 : ℝ)) *
          ∫ x : ℝ in 0..1, x ^ (n + 1) / (1 + x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hfactor] at hparts
  convert hparts using 1
  all_goals ring

private theorem integral_pow_thirteen_div_one_add :
    (∫ x : ℝ in 0..1, x ^ 13 / (1 + x)) =
      263111 / 360360 - Real.log 2 := by
  let q : ℕ → ℝ → ℝ := fun k x ↦ (-1 : ℝ) ^ k * x ^ (12 - k)
  have hqI (k : ℕ) : IntervalIntegrable (q k) volume 0 1 := by
    dsimp only [q]
    exact (continuous_const.mul (continuous_pow (12 - k))).intervalIntegrable 0 1
  have hinv : IntervalIntegrable (fun x : ℝ ↦ 1 / (1 + x)) volume 0 1 :=
    by
      apply ContinuousOn.intervalIntegrable
      intro x hx
      have hxu : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      have hne : 1 + x ≠ 0 := by linarith [hxu.1]
      exact (continuousAt_const.div
        (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hsumI : IntervalIntegrable
      (fun x : ℝ ↦ ∑ k ∈ Finset.range 13, q k x) volume 0 1 := by
    exact IntervalIntegrable.sum (Finset.range 13) (fun k _hk ↦ hqI k)
  calc
    (∫ x : ℝ in 0..1, x ^ 13 / (1 + x)) =
        ∫ x : ℝ in 0..1,
          (∑ k ∈ Finset.range 13, q k x) - 1 / (1 + x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxu : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      have hne : 1 + x ≠ 0 := by linarith [hxu.1]
      dsimp only [q]
      norm_num [Finset.sum_range_succ]
      field_simp [hne]
      ring
    _ = (∑ k ∈ Finset.range 13,
          ∫ x : ℝ in 0..1, q k x) -
        ∫ x : ℝ in 0..1, 1 / (1 + x) := by
      rw [intervalIntegral.integral_sub
        hsumI hinv,
        intervalIntegral.integral_finset_sum fun k hk ↦ hqI k]
    _ = 263111 / 360360 - Real.log 2 := by
      rw [integral_inv_one_add]
      dsimp only [q]
      simp_rw [intervalIntegral.integral_const_mul,
        YoshidaEndpointOcticPotential.integral_pow_nat]
      norm_num [Finset.sum_range_succ]

private theorem integral_pow_fifteen_div_one_add :
    (∫ x : ℝ in 0..1, x ^ 15 / (1 + x)) =
      52279 / 72072 - Real.log 2 := by
  let q : ℕ → ℝ → ℝ := fun k x ↦ (-1 : ℝ) ^ k * x ^ (14 - k)
  have hqI (k : ℕ) : IntervalIntegrable (q k) volume 0 1 := by
    dsimp only [q]
    exact (continuous_const.mul (continuous_pow (14 - k))).intervalIntegrable 0 1
  have hinv : IntervalIntegrable (fun x : ℝ ↦ 1 / (1 + x)) volume 0 1 :=
    by
      apply ContinuousOn.intervalIntegrable
      intro x hx
      have hxu : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      have hne : 1 + x ≠ 0 := by linarith [hxu.1]
      exact (continuousAt_const.div
        (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hsumI : IntervalIntegrable
      (fun x : ℝ ↦ ∑ k ∈ Finset.range 15, q k x) volume 0 1 := by
    exact IntervalIntegrable.sum (Finset.range 15) (fun k _hk ↦ hqI k)
  calc
    (∫ x : ℝ in 0..1, x ^ 15 / (1 + x)) =
        ∫ x : ℝ in 0..1,
          (∑ k ∈ Finset.range 15, q k x) - 1 / (1 + x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxu : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      have hne : 1 + x ≠ 0 := by linarith [hxu.1]
      dsimp only [q]
      norm_num [Finset.sum_range_succ]
      field_simp [hne]
      ring
    _ = (∑ k ∈ Finset.range 15,
          ∫ x : ℝ in 0..1, q k x) -
        ∫ x : ℝ in 0..1, 1 / (1 + x) := by
      rw [intervalIntegral.integral_sub
        hsumI hinv,
        intervalIntegral.integral_finset_sum fun k hk ↦ hqI k]
    _ = 52279 / 72072 - Real.log 2 := by
      rw [integral_inv_one_add]
      dsimp only [q]
      simp_rw [intervalIntegral.integral_const_mul,
        YoshidaEndpointOcticPotential.integral_pow_nat]
      norm_num [Finset.sum_range_succ]

private theorem integral_twelfth_mul_log_one_add :
    (∫ x : ℝ in 0..1, x ^ 12 * Real.log (1 + x)) =
      (2 / 13 : ℝ) * Real.log 2 - 263111 / 4684680 := by
  rw [integral_pow_mul_log_one_add_eq_quotient,
    integral_pow_thirteen_div_one_add]
  norm_num
  ring

private theorem integral_fourteenth_mul_log_one_add :
    (∫ x : ℝ in 0..1, x ^ 14 * Real.log (1 + x)) =
      (2 / 15 : ℝ) * Real.log 2 - 52279 / 1081080 := by
  rw [integral_pow_mul_log_one_add_eq_quotient,
    integral_pow_fifteen_div_one_add]
  norm_num
  ring

/-- Folding an even monomial against the endpoint logarithm separates it
into the two one-sided logarithmic moments. -/
private theorem integral_endpointPotential_mul_pow_of_even
    (n : ℕ) (hn : Even n) :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * x ^ n) =
      -((∫ x : ℝ in 0..1, x ^ n * Real.log (1 - x)) +
        ∫ x : ℝ in 0..1, x ^ n * Real.log (1 + x)) := by
  let q : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * x ^ n
  have hqEven : Function.Even q := by
    intro x
    dsimp only [q, yoshidaEndpointPotential]
    rw [hn.neg_pow]
    congr 1
    congr 3
    ring
  let r : ℝ → ℝ := fun x ↦ -(1 / 2 : ℝ) *
    (x ^ n * Real.log (1 - x) + x ^ n * Real.log (1 + x))
  have hpoint : ∀ᵐ x : ℝ ∂volume, q x = r x := by
    filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-1 : ℝ)] with x hx1 hxneg1
    have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    have hadd : 1 + x ≠ 0 := by
      intro h
      apply hxneg1
      linarith
    dsimp only [q, r, yoshidaEndpointPotential]
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
      Real.log_mul hsub hadd]
    ring
  have hsubI : IntervalIntegrable
      (fun x : ℝ ↦ x ^ n * Real.log (1 - x)) volume 0 1 := by
    let g : ℝ → ℝ := fun y ↦ (1 - y) ^ n * Real.log y
    have hg : IntervalIntegrable g volume 0 1 := by
      have hpoly : Continuous (fun y : ℝ ↦ (1 - y) ^ n) := by fun_prop
      have hbase : IntervalIntegrable
          (fun y : ℝ ↦ (1 - y) ^ n * Real.log y) volume 0 1 :=
        (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1))
          |>.continuousOn_mul hpoly.continuousOn
      simpa only [g] using hbase
    have hreflect : IntervalIntegrable (fun x : ℝ ↦ g (1 - x))
        volume 0 1 := by
      simpa only [sub_self, sub_zero] using (hg.comp_sub_left 1).symm
    apply hreflect.congr
    intro x _hx
    dsimp only [g]
    ring
  have haddI : IntervalIntegrable
      (fun x : ℝ ↦ x ^ n * Real.log (1 + x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hxu : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hxne : 1 + x ≠ 0 := by linarith [hxu.1]
    have hlog : ContinuousAt (fun y : ℝ ↦ Real.log (1 + y)) x := by
      exact ((Real.hasDerivAt_log hxne).comp x
        (by simpa using
          (hasDerivAt_const x 1).add (hasDerivAt_id x))).continuousAt
    exact ((continuousAt_id.pow n).mul hlog).continuousWithinAt
  have hrRight : IntervalIntegrable r volume 0 1 := by
    have hsum := hsubI.add haddI
    have hscaled := hsum.const_mul (-(1 / 2 : ℝ))
    simpa only [r] using hscaled
  have hqRight : IntervalIntegrable q volume 0 1 := by
    have hrev : r =ᵐ[volume] q := by
      filter_upwards [hpoint] with x hx
      exact hx.symm
    apply hrRight.congr_ae
    exact hrev.filter_mono (ae_mono Measure.restrict_le_self)
  have hqLeft : IntervalIntegrable q volume (-1) 0 := by
    have hneg : IntervalIntegrable (fun x : ℝ ↦ q (-x)) volume (-1) 0 := by
      simpa only [zero_sub, sub_zero] using (hqRight.comp_sub_left 0).symm
    apply hneg.congr
    intro x _hx
    exact hqEven x
  have hfold : (∫ x : ℝ in -1..1, q x) =
      2 * ∫ x : ℝ in 0..1, q x := by
    have hreflect : (∫ x : ℝ in 0..1, q (-x)) =
        ∫ x : ℝ in -1..0, q x := by
      simpa only [neg_zero] using
        (intervalIntegral.integral_comp_neg
          (f := q) (a := (0 : ℝ)) (b := 1))
    calc
      (∫ x : ℝ in -1..1, q x) =
          (∫ x : ℝ in -1..0, q x) + ∫ x : ℝ in 0..1, q x :=
        (intervalIntegral.integral_add_adjacent_intervals hqLeft hqRight).symm
      _ = (∫ x : ℝ in 0..1, q x) + ∫ x : ℝ in 0..1, q x := by
        congr 1
        rw [← hreflect]
        apply intervalIntegral.integral_congr
        intro x _hx
        exact hqEven x
      _ = _ := by ring
  rw [show (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * x ^ n) =
      ∫ x : ℝ in -1..1, q x by rfl, hfold]
  have hsplit : (∫ x : ℝ in 0..1, q x) =
      -(1 / 2 : ℝ) *
        ((∫ x : ℝ in 0..1, x ^ n * Real.log (1 - x)) +
          ∫ x : ℝ in 0..1, x ^ n * Real.log (1 + x)) := by
    calc
      (∫ x : ℝ in 0..1, q x) =
          ∫ x : ℝ in 0..1,
            -(1 / 2 : ℝ) *
              (x ^ n * Real.log (1 - x) +
                x ^ n * Real.log (1 + x)) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hpoint] with x hx _hxI
        simpa only [r] using hx
      _ = -(1 / 2 : ℝ) *
          ∫ x : ℝ in 0..1,
            (x ^ n * Real.log (1 - x) +
              x ^ n * Real.log (1 + x)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        rw [intervalIntegral.integral_add hsubI haddI]
  rw [hsplit]
  ring

theorem integral_endpointPotential_mul_pow_twelve :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * x ^ 12) =
      176138 / 585585 - (2 / 13 : ℝ) * Real.log 2 := by
  rw [integral_endpointPotential_mul_pow_of_even 12 (by decide),
    integral_twelfth_mul_log_one_sub,
    integral_twelfth_mul_log_one_add]
  ring

theorem integral_endpointPotential_mul_pow_fourteen :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * x ^ 14) =
      182144 / 675675 - (2 / 15 : ℝ) * Real.log 2 := by
  rw [integral_endpointPotential_mul_pow_of_even 14 (by decide),
    integral_fourteenth_mul_log_one_sub,
    integral_fourteenth_mul_log_one_add]
  ring

private theorem intervalIntegrable_endpointPotential_mul_even_pow (n : ℕ) :
    IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ (2 * n))
      volume (-1) 1 := by
  have h := intervalIntegrable_endpointPotential_mul_sq
    (fun x : ℝ ↦ x ^ n) (continuous_id.pow n)
  apply h.congr
  intro x _hx
  ring

/-- Exact endpoint-potential mass on the sixth centered mode. -/
theorem integral_endpointPotential_mul_factorTwoCenteredP6_sq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * factorTwoCenteredP6 x ^ 2) =
        249251 / 1171170 - (2 / 13 : ℝ) * Real.log 2 := by
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * factorTwoCenteredP6 x ^ 2) =
    fun x ↦
      (53361 / 256 : ℝ) * (yoshidaEndpointPotential x * x ^ 12) -
        (72765 / 128 : ℝ) * (yoshidaEndpointPotential x * x ^ 10) +
      (147735 / 256 : ℝ) * (yoshidaEndpointPotential x * x ^ 8) -
        (17115 / 64 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) +
      (14175 / 256 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) -
        (525 / 128 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) +
      (25 / 256 : ℝ) * yoshidaEndpointPotential x by
    funext x
    rw [factorTwoCenteredP6_eq]
    ring]
  have h0 : IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 0
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 1
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 2
  have h6 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 3
  have h8 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 8) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 4
  have h10 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 10) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 5
  have h12 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 12) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 6
  rw [intervalIntegral.integral_add
      (((((h12.const_mul (53361 / 256 : ℝ)).sub
        (h10.const_mul (72765 / 128 : ℝ))).add
        (h8.const_mul (147735 / 256 : ℝ))).sub
        (h6.const_mul (17115 / 64 : ℝ))).add
        (h4.const_mul (14175 / 256 : ℝ)) |>.sub
        (h2.const_mul (525 / 128 : ℝ)))
      (h0.const_mul (25 / 256 : ℝ)),
    intervalIntegral.integral_sub
      (((((h12.const_mul (53361 / 256 : ℝ)).sub
        (h10.const_mul (72765 / 128 : ℝ))).add
        (h8.const_mul (147735 / 256 : ℝ))).sub
        (h6.const_mul (17115 / 64 : ℝ))).add
        (h4.const_mul (14175 / 256 : ℝ)))
      (h2.const_mul (525 / 128 : ℝ)),
    intervalIntegral.integral_add
      ((((h12.const_mul (53361 / 256 : ℝ)).sub
        (h10.const_mul (72765 / 128 : ℝ))).add
        (h8.const_mul (147735 / 256 : ℝ))).sub
        (h6.const_mul (17115 / 64 : ℝ)))
      (h4.const_mul (14175 / 256 : ℝ)),
    intervalIntegral.integral_sub
      (((h12.const_mul (53361 / 256 : ℝ)).sub
        (h10.const_mul (72765 / 128 : ℝ))).add
        (h8.const_mul (147735 / 256 : ℝ)))
      (h6.const_mul (17115 / 64 : ℝ)),
    intervalIntegral.integral_add
      ((h12.const_mul (53361 / 256 : ℝ)).sub
        (h10.const_mul (72765 / 128 : ℝ)))
      (h8.const_mul (147735 / 256 : ℝ)),
    intervalIntegral.integral_sub
      (h12.const_mul (53361 / 256 : ℝ))
      (h10.const_mul (72765 / 128 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_twelve,
    integral_endpointPotential_mul_pow_ten,
    integral_endpointPotential_mul_pow_eight,
    integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq,
    integral_endpointPotential_one]
  ring

/-- Exact endpoint-potential mass on the seventh centered mode. -/
theorem integral_endpointPotential_mul_factorTwoCenteredP7_sq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * factorTwoCenteredP7 x ^ 2) =
        249383 / 1351350 - (2 / 15 : ℝ) * Real.log 2 := by
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * factorTwoCenteredP7 x ^ 2) =
    fun x ↦
      (184041 / 256 : ℝ) * (yoshidaEndpointPotential x * x ^ 14) -
        (297297 / 128 : ℝ) * (yoshidaEndpointPotential x * x ^ 12) +
      (750519 / 256 : ℝ) * (yoshidaEndpointPotential x * x ^ 10) -
        (116655 / 64 : ℝ) * (yoshidaEndpointPotential x * x ^ 8) +
      (147735 / 256 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) -
        (11025 / 128 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) +
      (1225 / 256 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) by
    funext x
    rw [factorTwoCenteredP7_eq]
    ring]
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 1
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 2
  have h6 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 3
  have h8 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 8) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 4
  have h10 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 10) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 5
  have h12 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 12) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 6
  have h14 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 14) volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow 7
  rw [intervalIntegral.integral_add
      (((((h14.const_mul (184041 / 256 : ℝ)).sub
        (h12.const_mul (297297 / 128 : ℝ))).add
        (h10.const_mul (750519 / 256 : ℝ))).sub
        (h8.const_mul (116655 / 64 : ℝ))).add
        (h6.const_mul (147735 / 256 : ℝ)) |>.sub
        (h4.const_mul (11025 / 128 : ℝ)))
      (h2.const_mul (1225 / 256 : ℝ)),
    intervalIntegral.integral_sub
      (((((h14.const_mul (184041 / 256 : ℝ)).sub
        (h12.const_mul (297297 / 128 : ℝ))).add
        (h10.const_mul (750519 / 256 : ℝ))).sub
        (h8.const_mul (116655 / 64 : ℝ))).add
        (h6.const_mul (147735 / 256 : ℝ)))
      (h4.const_mul (11025 / 128 : ℝ)),
    intervalIntegral.integral_add
      ((((h14.const_mul (184041 / 256 : ℝ)).sub
        (h12.const_mul (297297 / 128 : ℝ))).add
        (h10.const_mul (750519 / 256 : ℝ))).sub
        (h8.const_mul (116655 / 64 : ℝ)))
      (h6.const_mul (147735 / 256 : ℝ)),
    intervalIntegral.integral_sub
      (((h14.const_mul (184041 / 256 : ℝ)).sub
        (h12.const_mul (297297 / 128 : ℝ))).add
        (h10.const_mul (750519 / 256 : ℝ)))
      (h8.const_mul (116655 / 64 : ℝ)),
    intervalIntegral.integral_add
      ((h14.const_mul (184041 / 256 : ℝ)).sub
        (h12.const_mul (297297 / 128 : ℝ)))
      (h10.const_mul (750519 / 256 : ℝ)),
    intervalIntegral.integral_sub
      (h14.const_mul (184041 / 256 : ℝ))
      (h12.const_mul (297297 / 128 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_fourteen,
    integral_endpointPotential_mul_pow_twelve,
    integral_endpointPotential_mul_pow_ten,
    integral_endpointPotential_mul_pow_eight,
    integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq]
  ring

theorem factorTwoCenteredP6_potential_ratio :
    factorTwoIntrinsicPotentialEnergy factorTwoCenteredP6 =
      (249251 / 180180 - Real.log 2) *
        factorTwoIntrinsicEnergy factorTwoCenteredP6 := by
  unfold factorTwoIntrinsicPotentialEnergy
  rw [integral_endpointPotential_mul_factorTwoCenteredP6_sq,
    factorTwoCenteredP6_energy]
  ring

theorem factorTwoCenteredP7_potential_ratio :
    factorTwoIntrinsicPotentialEnergy factorTwoCenteredP7 =
      (249383 / 180180 - Real.log 2) *
        factorTwoIntrinsicEnergy factorTwoCenteredP7 := by
  unfold factorTwoIntrinsicPotentialEnergy
  rw [integral_endpointPotential_mul_factorTwoCenteredP7_sq,
    factorTwoCenteredP7_energy]
  ring

/-! ## Uniform diagonal reserves -/

theorem integral_factorTwoCenteredP6 :
    (∫ x : ℝ in -1..1, factorTwoCenteredP6 x) = 0 := by
  rw [show factorTwoCenteredP6 = fun x : ℝ ↦
      (231 * x ^ 6 - 315 * x ^ 4 + 105 * x ^ 2 - 5) / 16 by
    funext x
    exact factorTwoCenteredP6_eq x]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num

theorem factorTwoCenteredP6_p0_zero :
    centeredEvenP0Coefficient factorTwoCenteredP6 = 0 := by
  unfold centeredEvenP0Coefficient
  rw [integral_factorTwoCenteredP6, mul_zero]

private theorem zero_even_p0 :
    centeredEvenP0Coefficient (0 : ℝ → ℝ) = 0 := by
  unfold centeredEvenP0Coefficient
  simp

private theorem zero_locallyLipschitzOn :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) (0 : ℝ → ℝ) := by
  have hdiff : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
  change LocallyLipschitzOn (Icc (-1) 1) (fun _ : ℝ ↦ (0 : ℝ))
  exact hdiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)

private theorem yoshidaEndpointOddCleanQuadratic_zero :
    yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
  have h := yoshidaEndpointOddCleanQuadratic_const_mul (fun _ : ℝ ↦ 1) 0
  norm_num at h
  change yoshidaEndpointOddCleanQuadratic (fun _ : ℝ ↦ 0) = 0
  exact h

private theorem factorTwoCenteredSymmetricPerturbation_zero :
    factorTwoCenteredSymmetricPerturbation (0 : ℝ → ℝ) = 0 := by
  have h := factorTwoCenteredSymmetricPerturbation_smul
    0 (fun _ : ℝ ↦ 1)
  norm_num at h
  exact h

/-- The self-channel phase coefficient of `P6`. -/
def factorTwoP6PhaseDiagonal (a : ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic factorTwoCenteredP6 +
    a * factorTwoCenteredSymmetricPerturbation factorTwoCenteredP6

/-- The self-channel phase coefficient of `P7`. -/
def factorTwoP7PhaseDiagonal (a : ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic factorTwoCenteredP7 +
    a * factorTwoCenteredSymmetricPerturbation factorTwoCenteredP7

theorem phase_P6_zero_eq_diagonal (a b : ℝ) :
    factorTwoEndpointChannelPhase factorTwoCenteredP6 0 a b =
      factorTwoP6PhaseDiagonal a := by
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum factorTwoP6PhaseDiagonal
  rw [yoshidaEndpointOddCleanQuadratic_zero,
    factorTwoCenteredSymmetricPerturbation_zero]
  simp only [add_zero]
  have hAlt : factorTwoCenteredAlternatingCoupling
      factorTwoCenteredP6 (0 : ℝ → ℝ) = 0 := by
    have h := factorTwoCenteredAlternatingCoupling_smul_right
      0 factorTwoCenteredP6 (fun _ : ℝ ↦ 1)
    norm_num at h
    exact h
  rw [hAlt, mul_zero, add_zero]

private theorem phase_zero_P7_eq_diagonal (a b : ℝ) :
    factorTwoEndpointChannelPhase 0 factorTwoCenteredP7 a b =
      factorTwoP7PhaseDiagonal a := by
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum factorTwoP7PhaseDiagonal
  rw [yoshidaEndpointOddCleanQuadratic_zero,
    factorTwoCenteredSymmetricPerturbation_zero]
  simp only [zero_add]
  have hAlt : factorTwoCenteredAlternatingCoupling
      (0 : ℝ → ℝ) factorTwoCenteredP7 = 0 := by
    have h := factorTwoCenteredAlternatingCoupling_smul_left
      0 (fun _ : ℝ ↦ 1) factorTwoCenteredP7
    norm_num at h
    exact h
  rw [hAlt, mul_zero, add_zero]

private theorem dyadic_weight_lt_491_div_1000 :
    Real.log 2 / Real.sqrt 2 < (491 / 1000 : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtLower : (707 / 500 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hlogUpper := Real.log_two_lt_d9
  rw [div_lt_iff₀ hsqrtPos]
  nlinarith

/-- With the alternating coordinate absent, the complete self phase-variable
loss is below `702/1000` on the disk. -/
private theorem projected_self_phase_variable_le_702_div_1000
    (a : ℝ) (ha : a ^ 2 ≤ 1) :
    factorTwoIntrinsicSelfRegularHalfWidth * |a| +
        (Real.log 2 / Real.sqrt 2) * a ≤ 702 / 1000 := by
  let d := factorTwoIntrinsicSelfRegularHalfWidth
  let alpha := Real.log 2 / Real.sqrt 2
  have hlogLower := strict_log_two_fine_bounds.1
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  have hd0 : 0 ≤ d := by
    dsimp only [d]
    unfold factorTwoIntrinsicSelfRegularHalfWidth yoshidaEndpointA
    linarith
  have hdUpper : d < (211 / 1000 : ℝ) := by
    dsimp only [d]
    unfold factorTwoIntrinsicSelfRegularHalfWidth yoshidaEndpointA
    linarith
  have halpha0 : 0 ≤ alpha := by
    dsimp only [alpha]
    positivity
  have halphaUpper : alpha < (491 / 1000 : ℝ) := by
    simpa only [alpha] using dyadic_weight_lt_491_div_1000
  have habs : |a| ≤ 1 := by
    nlinarith [sq_abs a, abs_nonneg a]
  have haAbs : alpha * a ≤ alpha * |a| :=
    mul_le_mul_of_nonneg_left (le_abs_self a) halpha0
  have hsum : d + alpha < (702 / 1000 : ℝ) := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hsum.le (abs_nonneg a)
  dsimp only [d, alpha] at hscaled ⊢
  nlinarith

theorem P6_projected_loss_budget
    (a : ℝ) (ha : a ^ 2 ≤ 1) :
    factorTwoIntrinsicProjectedEvenRemainderLoss a 0 +
        Real.log 2 / 2 + (1 / 20 : ℝ) ≤
      (harmonic 6 : ℝ) +
        (1 / 2 : ℝ) * (249251 / 180180 - Real.log 2) := by
  have hphase := projected_self_phase_variable_le_702_div_1000 a ha
  have hbeta := log_three_div_sqrt_three_kernel_bounds.2
  have hscalar := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hlog : Real.log 2 < (7 / 10 : ℝ) :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  have hlogSmall : Real.log 2 / 64 < (7 / 640 : ℝ) := by linarith
  unfold factorTwoIntrinsicProjectedEvenRemainderLoss
  norm_num [harmonic, Finset.sum_range_succ] at hphase ⊢
  linarith

private theorem P7_projected_loss_budget
    (a : ℝ) (ha : a ^ 2 ≤ 1) :
    factorTwoIntrinsicProjectedOddRemainderLoss a 0 +
        Real.log 2 / 2 + (9 / 50 : ℝ) ≤
      (harmonic 7 : ℝ) +
        (1 / 2 : ℝ) * (249383 / 180180 - Real.log 2) := by
  have hphase := projected_self_phase_variable_le_702_div_1000 a ha
  have hbeta := log_three_div_sqrt_three_kernel_bounds.2
  have hscalar := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hlogLower := six_hundred_ninety_three_div_thousand_lt_log_two
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  have hlogSmall : Real.log 2 / 64 < (7 / 640 : ℝ) := by linarith
  have hsqrt := inv_sqrt_two_lt_one_hundred_seventy_seven_div_two_hundred_fifty
  have hsqrt' : (Real.sqrt 2)⁻¹ < (177 / 250 : ℝ) := by
    simpa only [one_div] using hsqrt
  unfold factorTwoIntrinsicProjectedOddRemainderLoss
    factorTwoIntrinsicProjectedEvenRemainderLoss
  norm_num [harmonic, Finset.sum_range_succ] at hphase ⊢
  linarith

/-- The complete `P6` phase diagonal retains `1/20` of its `L²` mass. -/
theorem one_twentieth_energy_le_P6_phase_diagonal
    (a : ℝ) (ha : a ^ 2 ≤ 1) :
    (1 / 20 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP6 ≤
      factorTwoP6PhaseDiagonal a := by
  have hab : a ^ 2 + (0 : ℝ) ^ 2 ≤ 1 := by simpa using ha
  have hraw := factorTwoCenteredP6_raw_reserve
  have hprotected := raw_add_half_potential_sub_half_logMass_le_protected
    factorTwoCenteredP6 (0 : ℝ → ℝ)
    continuous_factorTwoCenteredP6 (by fun_prop)
    locallyLipschitzOn_factorTwoCenteredP6
    zero_locallyLipschitzOn
    a 0 hab
  have hrem := neg_factorTwoIntrinsicSignedRemainder_le_projected_energy
    factorTwoCenteredP6 (0 : ℝ → ℝ)
    continuous_factorTwoCenteredP6 (by fun_prop)
    even_factorTwoCenteredP6 (by intro x; simp)
    factorTwoCenteredP6_p0_zero a 0 hab
  have hbudget := P6_projected_loss_budget a ha
  have henergy := factorTwoIntrinsicEnergy_nonneg factorTwoCenteredP6
  have hzeroRaw : centeredRawLogEnergy (0 : ℝ → ℝ) = 0 := by
    unfold centeredRawLogEnergy
    simp
  have hzeroPotential :
      factorTwoIntrinsicPotentialEnergy (0 : ℝ → ℝ) = 0 := by
    unfold factorTwoIntrinsicPotentialEnergy
    simp
  have hzeroEnergy : factorTwoIntrinsicEnergy (0 : ℝ → ℝ) = 0 := by
    unfold factorTwoIntrinsicEnergy
    simp
  rw [factorTwoCenteredP6_potential_ratio] at hprotected
  rw [hzeroPotential, hzeroEnergy] at hprotected
  rw [hzeroEnergy] at hrem
  norm_num only [zero_div, add_zero, mul_zero, sub_zero] at hprotected hrem
  have hphase :
      (1 / 20 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP6 ≤
        factorTwoEndpointChannelPhase factorTwoCenteredP6 0 a 0 := by
    rw [factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
      factorTwoCenteredP6 (0 : ℝ → ℝ)
        continuous_factorTwoCenteredP6 (by fun_prop) a 0]
    nlinarith
  rw [phase_P6_zero_eq_diagonal] at hphase
  exact hphase

/-- The complete `P7` phase diagonal retains `9/50` of its `L²` mass. -/
theorem nine_fiftieths_energy_le_P7_phase_diagonal
    (a : ℝ) (ha : a ^ 2 ≤ 1) :
    (9 / 50 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP7 ≤
      factorTwoP7PhaseDiagonal a := by
  have hab : a ^ 2 + (0 : ℝ) ^ 2 ≤ 1 := by simpa using ha
  have hraw := factorTwoCenteredP7_raw_reserve
  have hprotected := raw_add_half_potential_sub_half_logMass_le_protected
    (0 : ℝ → ℝ) factorTwoCenteredP7
    (by fun_prop) continuous_factorTwoCenteredP7
    zero_locallyLipschitzOn
    locallyLipschitzOn_factorTwoCenteredP7 a 0 hab
  have hrem := neg_factorTwoIntrinsicSignedRemainder_le_projected_energy
    (0 : ℝ → ℝ) factorTwoCenteredP7
    (by fun_prop) continuous_factorTwoCenteredP7
    (by intro x; simp) odd_factorTwoCenteredP7
    zero_even_p0 a 0 hab
  have hbudget := P7_projected_loss_budget a ha
  have henergy := factorTwoIntrinsicEnergy_nonneg factorTwoCenteredP7
  have hzeroRaw : centeredRawLogEnergy (0 : ℝ → ℝ) = 0 := by
    unfold centeredRawLogEnergy
    simp
  have hzeroPotential :
      factorTwoIntrinsicPotentialEnergy (0 : ℝ → ℝ) = 0 := by
    unfold factorTwoIntrinsicPotentialEnergy
    simp
  have hzeroEnergy : factorTwoIntrinsicEnergy (0 : ℝ → ℝ) = 0 := by
    unfold factorTwoIntrinsicEnergy
    simp
  rw [factorTwoCenteredP7_potential_ratio] at hprotected
  rw [hzeroPotential, hzeroEnergy] at hprotected
  rw [hzeroEnergy] at hrem
  norm_num only [zero_div, zero_add, mul_zero, add_zero, sub_zero] at hprotected hrem
  have hphase :
      (9 / 50 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP7 ≤
        factorTwoEndpointChannelPhase 0 factorTwoCenteredP7 a 0 := by
    rw [factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
      (0 : ℝ → ℝ) factorTwoCenteredP7
        (by fun_prop) continuous_factorTwoCenteredP7 a 0]
    nlinarith
  rw [phase_zero_P7_eq_diagonal] at hphase
  exact hphase

/-! ## Exact alternating `P6/P7` entry -/

/-- Polynomial remaining after the universal endpoint factor
`t * (2-t)` is removed from the `P6/P7` ordered correlation difference. -/
def alternatingQ67 (t : ℝ) : ℝ :=
  1 - 3 * t - (3 / 2 : ℝ) * t ^ 2 + (25 / 4 : ℝ) * t ^ 3 +
    (25 / 8 : ℝ) * t ^ 4 - (101 / 16 : ℝ) * t ^ 5 -
    (101 / 32 : ℝ) * t ^ 6 + (199 / 64 : ℝ) * t ^ 7 +
    (199 / 128 : ℝ) * t ^ 8 - (93 / 128 : ℝ) * t ^ 9 -
    (93 / 256 : ℝ) * t ^ 10 + (33 / 512 : ℝ) * t ^ 11 +
    (33 / 1024 : ℝ) * t ^ 12

set_option maxHeartbeats 800000 in
/-- Exact correlation factorization.  This is a polynomial identity, not a
sampled or mode-enumerated certificate. -/
theorem crossDifference_p6_p7
    (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation factorTwoCenteredP7 factorTwoCenteredP6 t -
        factorTwoCenteredCrossCorrelation factorTwoCenteredP6 factorTwoCenteredP7 t =
      intrinsicAlternatingCorrelation alternatingQ67 t := by
  unfold factorTwoCenteredCrossCorrelation intrinsicAlternatingCorrelation
    alternatingQ67
  simp_rw [factorTwoCenteredP6_eq, factorTwoCenteredP7_eq]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  repeat rw [integral_id]
  simp only [smul_eq_mul]
  ring

/-- Complete alternating entry of the two new modes. -/
def factorTwoP67Alternating : ℝ :=
  factorTwoCenteredAlternatingCoupling factorTwoCenteredP6 factorTwoCenteredP7

theorem factorTwoP67Alternating_eq_structuralModel :
    factorTwoP67Alternating =
      intrinsicAlternatingRegularError alternatingQ67 +
        intrinsicAlternatingArchModel alternatingQ67 -
      (Real.log 3 / Real.sqrt 3) *
        intrinsicAlternatingCorrelation alternatingQ67
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  unfold factorTwoP67Alternating
  exact factorTwoCenteredAlternatingCoupling_eq_regularError_add_archModel
    factorTwoCenteredP6 factorTwoCenteredP7 alternatingQ67
    (by unfold alternatingQ67; fun_prop) crossDifference_p6_p7

private theorem integral_abs_alternatingCorrelation_le_majorant
    (q : ℝ → ℝ) (hq : Continuous q) :
    (∫ t : ℝ in 0..2, |intrinsicAlternatingCorrelation q t|) ≤
      ∫ t : ℝ in 0..2, t * (2 - t) * (q t ^ 2 + 1) / 2 := by
  let g : ℝ → ℝ := fun t ↦ t * (2 - t) * (q t ^ 2 + 1) / 2
  have hcorr : Continuous (intrinsicAlternatingCorrelation q) := by
    unfold intrinsicAlternatingCorrelation
    fun_prop
  have hg : Continuous g := by
    dsimp only [g]
    fun_prop
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hcorr.abs.intervalIntegrable 0 2) (hg.intervalIntegrable 0 2)
  intro t ht
  have hw : 0 ≤ t * (2 - t) :=
    mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have hqabs : |q t| ≤ (q t ^ 2 + 1) / 2 := by
    nlinarith [sq_nonneg (|q t| - 1), sq_abs (q t)]
  unfold intrinsicAlternatingCorrelation
  rw [abs_mul, abs_of_nonneg hw]
  simpa only [g, div_eq_mul_inv, mul_assoc] using
    (mul_le_mul_of_nonneg_left hqabs hw)

set_option maxHeartbeats 800000 in
private theorem integral_abs_q67_le :
    (∫ t : ℝ in 0..2,
      |intrinsicAlternatingCorrelation alternatingQ67 t|) ≤
        (1135067953 / 1673196525 : ℝ) := by
  calc
    _ ≤ ∫ t : ℝ in 0..2,
        t * (2 - t) * (alternatingQ67 t ^ 2 + 1) / 2 :=
      integral_abs_alternatingCorrelation_le_majorant alternatingQ67
        (by unfold alternatingQ67; fun_prop)
    _ = (1135067953 / 1673196525 : ℝ) := by
      unfold alternatingQ67
      ring_nf
      repeat rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      norm_num

private theorem abs_regularError_q67_lt :
    |intrinsicAlternatingRegularError alternatingQ67| <
      (679 / 1000000 : ℝ) := by
  have h := abs_intrinsicAlternatingRegularError_le alternatingQ67
    (by unfold alternatingQ67; fun_prop)
  calc
    _ ≤ (1 / 1000 : ℝ) *
        (∫ t : ℝ in 0..2,
          |intrinsicAlternatingCorrelation alternatingQ67 t|) := h
    _ ≤ (1 / 1000 : ℝ) * (1135067953 / 1673196525 : ℝ) :=
      mul_le_mul_of_nonneg_left integral_abs_q67_le (by norm_num)
    _ < (679 / 1000000 : ℝ) := by norm_num

private theorem integral_inv_two_add :
    (∫ t : ℝ in 0..2, 1 / (2 + t)) = Real.log 2 := by
  let F : ℝ → ℝ := fun t ↦ Real.log (2 + t)
  have hderiv (t : ℝ) (ht : 2 + t ≠ 0) :
      HasDerivAt F (1 / (2 + t)) t := by
    have hadd : HasDerivAt (fun x : ℝ ↦ 2 + x) 1 t := by
      simpa using (hasDerivAt_const t 2).add (hasDerivAt_id t)
    simpa only [F, Function.comp_apply, one_div, mul_one] using
      (Real.hasDerivAt_log ht).comp t hadd
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / (2 + t))
      (uIcc (0 : ℝ) 2) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 2 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have hne : 2 + t ≠ 0 := by linarith [ht'.1]
    exact (continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hderiv t (by
      have ht' : t ∈ Icc (0 : ℝ) 2 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
      linarith [ht'.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num
  rw [show Real.log 4 = 2 * Real.log 2 by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
    ring]
  ring

private theorem intervalIntegrable_inv_two_add :
    IntervalIntegrable (fun t : ℝ ↦ 1 / (2 + t)) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have hne : 2 + t ≠ 0 := by linarith [ht'.1]
  exact (continuousAt_const.div
    (continuousAt_const.add continuousAt_id) hne).continuousWithinAt

private theorem archModel_q67 :
    intrinsicAlternatingArchModel alternatingQ67 =
      -(289 / 105 : ℝ) + 4 * Real.log 2 := by
  let p : ℝ → ℝ := fun t ↦
    -2 + t + (1 / 5 : ℝ) * t ^ 2 - (11 / 5 : ℝ) * t ^ 3 +
      (181 / 40 : ℝ) * t ^ 5 - (757 / 160 : ℝ) * t ^ 7 +
      (319 / 128 : ℝ) * t ^ 9 - (85 / 128 : ℝ) * t ^ 11 +
      (417 / 5120 : ℝ) * t ^ 13 - (33 / 10240 : ℝ) * t ^ 15
  have hint : intrinsicAlternatingArchModel alternatingQ67 =
      ∫ t : ℝ in 0..2, p t + 4 * (1 / (2 + t)) := by
    unfold intrinsicAlternatingArchModel intrinsicAlternatingCorrelation
      alternatingQ67
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have hden : 2 + t ≠ 0 := by linarith [ht.1]
    dsimp only [p]
    field_simp [hden]
    ring
  have hp : IntervalIntegrable p volume 0 2 := by
    exact (by dsimp only [p]; fun_prop : Continuous p).intervalIntegrable 0 2
  rw [hint, intervalIntegral.integral_add hp
      (intervalIntegrable_inv_two_add.const_mul 4),
    intervalIntegral.integral_const_mul, integral_inv_two_add]
  dsimp only [p]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

private theorem archModel_q67_bounds :
    (202 / 10000 : ℝ) < intrinsicAlternatingArchModel alternatingQ67 ∧
      intrinsicAlternatingArchModel alternatingQ67 < (203 / 10000 : ℝ) := by
  rw [archModel_q67]
  have h := strict_log_two_fine_bounds
  constructor <;> nlinarith [h.1, h.2]

private theorem offset_pow_lt
    {y eps : ℝ} (hy : 0 ≤ y) (hye : y < eps)
    (n : ℕ) (hn : n ≠ 0) :
    y ^ n < eps ^ n :=
  pow_lt_pow_left₀ hye hy hn

set_option maxHeartbeats 1000000 in
private theorem primeCorrelation_q67_bounds :
    (10 / 10000 : ℝ) < intrinsicAlternatingCorrelation alternatingQ67
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation alternatingQ67
        (factorTwoPrimeShift / yoshidaEndpointA) < (11 / 10000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 116992 / 100000
  have htau := factorTwoPrimeRatio_sharp_bounds
  have hy0 : 0 < y := by dsimp only [y, tau]; linarith [htau.1]
  have hyU : y < (1 / 100000 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 := offset_pow_lt hy0.le hyU 2 (by norm_num)
  have hy3 := offset_pow_lt hy0.le hyU 3 (by norm_num)
  have hy4 := offset_pow_lt hy0.le hyU 4 (by norm_num)
  have hy5 := offset_pow_lt hy0.le hyU 5 (by norm_num)
  have hy6 := offset_pow_lt hy0.le hyU 6 (by norm_num)
  have hy7 := offset_pow_lt hy0.le hyU 7 (by norm_num)
  have hy8 := offset_pow_lt hy0.le hyU 8 (by norm_num)
  have hy9 := offset_pow_lt hy0.le hyU 9 (by norm_num)
  have hy10 := offset_pow_lt hy0.le hyU 10 (by norm_num)
  have hy11 := offset_pow_lt hy0.le hyU 11 (by norm_num)
  have hy12 := offset_pow_lt hy0.le hyU 12 (by norm_num)
  have hy13 := offset_pow_lt hy0.le hyU 13 (by norm_num)
  have hy14 := offset_pow_lt hy0.le hyU 14 (by norm_num)
  have htauy : tau = 116992 / 100000 + y := by dsimp only [y]; ring
  dsimp only [tau] at htauy ⊢
  rw [htauy]
  unfold intrinsicAlternatingCorrelation alternatingQ67
  ring_nf
  constructor <;> linarith [hy2, hy3, hy4, hy5, hy6, hy7, hy8,
    hy9, hy10, hy11, hy12, hy13, hy14, sq_nonneg y,
    pow_nonneg hy0.le 3, pow_nonneg hy0.le 4, pow_nonneg hy0.le 5,
    pow_nonneg hy0.le 6, pow_nonneg hy0.le 7, pow_nonneg hy0.le 8,
    pow_nonneg hy0.le 9, pow_nonneg hy0.le 10, pow_nonneg hy0.le 11,
    pow_nonneg hy0.le 12, pow_nonneg hy0.le 13, pow_nonneg hy0.le 14]

/-- Structural box for the complete `P6/P7` alternating entry. -/
theorem factorTwoP67Alternating_bounds :
    (18 / 1000 : ℝ) < factorTwoP67Alternating ∧
      factorTwoP67Alternating < (21 / 1000 : ℝ) := by
  rw [factorTwoP67Alternating_eq_structuralModel]
  have herr := abs_lt.mp abs_regularError_q67_lt
  have harch := archModel_q67_bounds
  have hcorr := primeCorrelation_q67_bounds
  have hbeta := log_three_div_sqrt_three_kernel_bounds
  have hbeta0 : 0 < Real.log 3 / Real.sqrt 3 :=
    (by norm_num : (0 : ℝ) < 63427 / 100000).trans hbeta.1
  have hcorr0 : 0 < intrinsicAlternatingCorrelation alternatingQ67
      (factorTwoPrimeShift / yoshidaEndpointA) :=
    (by norm_num : (0 : ℝ) < 10 / 10000).trans hcorr.1
  have hproductLower :
      (63427 / 100000 : ℝ) * (10 / 10000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation alternatingQ67
            (factorTwoPrimeShift / yoshidaEndpointA) := by
    calc
      _ < (Real.log 3 / Real.sqrt 3) * (10 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hcorr.1 hbeta0
  have hproductUpper :
      (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation alternatingQ67
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (6343 / 10000 : ℝ) * (11 / 10000 : ℝ) := by
    calc
      _ < (6343 / 10000 : ℝ) *
          intrinsicAlternatingCorrelation alternatingQ67
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hbeta.2 hcorr0
      _ < _ := mul_lt_mul_of_pos_left hcorr.2 (by norm_num)
  constructor <;> nlinarith

/-- The alternating entry spends at most `9/400` of the product of the two
mode energies. -/
theorem factorTwoP67Alternating_sq_le_energy_product :
    factorTwoP67Alternating ^ 2 ≤
      (9 / 400 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP6 *
        factorTwoIntrinsicEnergy factorTwoCenteredP7 := by
  have hJ := factorTwoP67Alternating_bounds
  rw [factorTwoCenteredP6_energy, factorTwoCenteredP7_energy]
  nlinarith [sq_nonneg (factorTwoP67Alternating - 21 / 1000)]

/-! ## Exact two-mode expansion and Schur closure -/

theorem factorTwoEndpointChannelPhase_P6_P7_expansion
    (c d a b : ℝ) :
    factorTwoEndpointChannelPhase
        (fun x ↦ c * factorTwoCenteredP6 x)
        (fun x ↦ d * factorTwoCenteredP7 x) a b =
      factorTwoP6PhaseDiagonal a * c ^ 2 +
        b * factorTwoP67Alternating * c * d +
        factorTwoP7PhaseDiagonal a * d ^ 2 := by
  have heSym :
      factorTwoCenteredSymmetricPerturbation
          (fun x ↦ c * factorTwoCenteredP6 x) =
        c ^ 2 * factorTwoCenteredSymmetricPerturbation factorTwoCenteredP6 := by
    simpa [smul_eq_mul] using
      factorTwoCenteredSymmetricPerturbation_smul c factorTwoCenteredP6
  have hoSym :
      factorTwoCenteredSymmetricPerturbation
          (fun x ↦ d * factorTwoCenteredP7 x) =
        d ^ 2 * factorTwoCenteredSymmetricPerturbation factorTwoCenteredP7 := by
    simpa [smul_eq_mul] using
      factorTwoCenteredSymmetricPerturbation_smul d factorTwoCenteredP7
  have hAlt :
      factorTwoCenteredAlternatingCoupling
          (fun x ↦ c * factorTwoCenteredP6 x)
          (fun x ↦ d * factorTwoCenteredP7 x) =
        c * d * factorTwoCenteredAlternatingCoupling
          factorTwoCenteredP6 factorTwoCenteredP7 := by
    change factorTwoCenteredAlternatingCoupling
        (c • factorTwoCenteredP6) (d • factorTwoCenteredP7) = _
    rw [factorTwoCenteredAlternatingCoupling_smul_left,
      factorTwoCenteredAlternatingCoupling_smul_right]
    ring
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum factorTwoP6PhaseDiagonal
    factorTwoP7PhaseDiagonal factorTwoP67Alternating
  rw [yoshidaEndpointOddCleanQuadratic_const_mul,
    yoshidaEndpointOddCleanQuadratic_const_mul, heSym, hoSym, hAlt]
  ring

/-- Complete structural positivity of the standalone `P6/P7` block on the
closed phase disk. -/
theorem factorTwoEndpointChannelPhase_P6_P7_nonnegative
    (c d a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase
      (fun x ↦ c * factorTwoCenteredP6 x)
      (fun x ↦ d * factorTwoCenteredP7 x) a b := by
  have ha : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
  have hb : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  have hD6 := one_twentieth_energy_le_P6_phase_diagonal a ha
  have hD7 := nine_fiftieths_energy_le_P7_phase_diagonal a ha
  have hJ := factorTwoP67Alternating_sq_le_energy_product
  rw [factorTwoCenteredP6_energy] at hD6 hJ
  rw [factorTwoCenteredP7_energy] at hD7 hJ
  have hD6zero : 0 ≤ factorTwoP6PhaseDiagonal a := by
    exact (by norm_num : (0 : ℝ) ≤ (1 / 20) * (2 / 13)).trans hD6
  have hD7zero : 0 ≤ factorTwoP7PhaseDiagonal a := by
    exact (by norm_num : (0 : ℝ) ≤ (9 / 50) * (2 / 15)).trans hD7
  have hprod :
      ((1 / 20 : ℝ) * (2 / 13)) * ((9 / 50 : ℝ) * (2 / 15)) ≤
        factorTwoP6PhaseDiagonal a * factorTwoP7PhaseDiagonal a := by
    exact mul_le_mul hD6 hD7 (by positivity) hD6zero
  have hbJ :
      (b * factorTwoP67Alternating) ^ 2 ≤
        factorTwoP67Alternating ^ 2 := by
    rw [mul_pow]
    have hmul := mul_le_mul_of_nonneg_right hb
      (sq_nonneg factorTwoP67Alternating)
    nlinarith
  have hcoeff :
      (b * factorTwoP67Alternating) ^ 2 ≤
        4 * factorTwoP6PhaseDiagonal a * factorTwoP7PhaseDiagonal a := by
    nlinarith
  let low := factorTwoP6PhaseDiagonal a * c ^ 2
  let tail := factorTwoP7PhaseDiagonal a * d ^ 2
  let mixed := (b * factorTwoP67Alternating * c * d) / 2
  have hlow : 0 ≤ low := by
    dsimp only [low]
    positivity
  have htail : 0 ≤ tail := by
    dsimp only [tail]
    positivity
  have hscaled := mul_le_mul_of_nonneg_right hcoeff
    (mul_nonneg (sq_nonneg c) (sq_nonneg d))
  have hschur : mixed ^ 2 ≤ low * tail := by
    dsimp only [mixed, low, tail]
    nlinarith
  have hnonneg := TwoByTwoSchur.scalar_low_tail_nonneg
    low tail mixed hlow htail hschur
  rw [factorTwoEndpointChannelPhase_P6_P7_expansion]
  dsimp only [low, tail, mixed] at hnonneg
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
