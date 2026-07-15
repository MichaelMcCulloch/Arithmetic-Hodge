import Mathlib.Analysis.SumIntegralComparisons
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveStructural
import ArithmeticHodge.Analysis.ShiftedLegendreOrthogonality
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseArchRankDiskSchur

set_option autoImplicit false

open Filter MeasureTheory Polynomial Real Set
open scoped BigOperators Topology

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveRankStructural

open PolynomialIteratedIntegrationByParts
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaFactorTwoPhaseArchRankDiskSchur
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseRankLimit
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaRenormalizedGeometricKernel
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddSharpMassLoss

noncomputable section

/-!
# Structural all-rank bounds for the first middle Legendre pair

Rodrigues' formula turns the `P₄` and `P₅` hyperbolic moments into
positive Laplace integrals.  A single exponential envelope controls every
rank, and a sum--integral comparison controls the complete infinite family.
No rank cutoff or finite certificate occurs below.
-/

/-! ## Exponential Rodrigues integration by parts -/

/-- Move all polynomial derivatives in Rodrigues' formula onto an
exponential.  The endpoint hypotheses remove every boundary term. -/
private theorem integral_exp_mul_iterate_derivative_eq
    (q : ℝ[X]) (n : ℕ) (lambda : ℝ)
    (hboundary : ∀ m < n,
      (derivative^[m] q).eval 0 = 0 ∧
        (derivative^[m] q).eval 1 = 0) :
    (∫ t : ℝ in 0..1,
        Real.exp (2 * lambda * t) * (derivative^[n] q).eval t) =
      (-2 * lambda) ^ n *
        ∫ t : ℝ in 0..1, Real.exp (2 * lambda * t) * q.eval t := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
      have hboundary' : ∀ m < n,
          (derivative^[m] q).eval 0 = 0 ∧
            (derivative^[m] q).eval 1 = 0 := by
        intro m hm
        exact hboundary m (hm.trans (Nat.lt_succ_self n))
      have hqDeriv (t : ℝ) :
          HasDerivAt (fun y : ℝ ↦ (derivative^[n] q).eval y)
            ((derivative^[n.succ] q).eval t) t := by
        rw [Function.iterate_succ_apply']
        exact (derivative^[n] q).hasDerivAt t
      have hexpDeriv (t : ℝ) :
          HasDerivAt (fun y : ℝ ↦ Real.exp (2 * lambda * y))
            (2 * lambda * Real.exp (2 * lambda * t)) t := by
        convert (Real.hasDerivAt_exp (2 * lambda * t)).comp t
          ((hasDerivAt_id t).const_mul (2 * lambda)) using 1
        all_goals ring
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (u := fun t : ℝ ↦ Real.exp (2 * lambda * t))
        (u' := fun t : ℝ ↦ 2 * lambda * Real.exp (2 * lambda * t))
        (v := fun t : ℝ ↦ (derivative^[n] q).eval t)
        (v' := fun t : ℝ ↦ (derivative^[n.succ] q).eval t)
        (fun t _ ↦ hexpDeriv t) (fun t _ ↦ hqDeriv t)
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
        (Continuous.intervalIntegrable (by
          rw [continuous_iff_continuousAt]
          intro t
          exact (derivative^[n.succ] q).hasDerivAt t |>.continuousAt) 0 1)
      have hb := hboundary n (Nat.lt_succ_self n)
      have hstep :
          (∫ t : ℝ in 0..1,
              Real.exp (2 * lambda * t) *
                (derivative^[n.succ] q).eval t) =
            (-2 * lambda) *
              ∫ t : ℝ in 0..1,
                Real.exp (2 * lambda * t) *
                  (derivative^[n] q).eval t := by
        rw [show (fun t : ℝ ↦
            2 * lambda * Real.exp (2 * lambda * t) *
              (derivative^[n] q).eval t) =
            fun t ↦ (2 * lambda) *
              (Real.exp (2 * lambda * t) *
                (derivative^[n] q).eval t) by
          funext t
          ring,
          intervalIntegral.integral_const_mul] at hibp
        have h := hibp
        simp only [hb.1, hb.2, mul_zero, sub_zero, zero_sub] at h
        convert h using 1
        all_goals ring
      rw [hstep, ih q hboundary']
      rw [pow_succ]
      ring

/-! ## Exact `P₄` and `P₅` Rodrigues moments -/

private theorem factorTwoCenteredP4_affine (t : ℝ) :
    factorTwoCenteredP4 (2 * t - 1) =
      (shiftedLegendreReal 4).eval t := by
  norm_num [factorTwoCenteredP4, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose]
  ring

private theorem factorTwoCenteredP5_affine (t : ℝ) :
    factorTwoCenteredP5 (2 * t - 1) =
      -(shiftedLegendreReal 5).eval t := by
  norm_num [factorTwoCenteredP5, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose]
  ring

/-- Rodrigues integration by parts for an arbitrary shifted Legendre mode.
The public form lets later low-mode arguments reuse the same structural
identity instead of reproving the boundary-term calculation. -/
theorem factorial_mul_integral_exp_shiftedLegendreReal
    (n : ℕ) (lambda : ℝ) :
    (n.factorial : ℝ) *
        (∫ t : ℝ in 0..1,
          Real.exp (2 * lambda * t) * (shiftedLegendreReal n).eval t) =
      (-2 * lambda) ^ n *
        ∫ t : ℝ in 0..1,
          Real.exp (2 * lambda * t) *
            (shiftedLegendreRodriguesBase n).eval t := by
  have h := integral_exp_mul_iterate_derivative_eq
    (shiftedLegendreRodriguesBase n) n lambda
    (fun m hm ↦ shiftedLegendreRodriguesBase_boundary n m hm)
  have heval (t : ℝ) :
      (derivative^[n] (shiftedLegendreRodriguesBase n)).eval t =
        (n.factorial : ℝ) * (shiftedLegendreReal n).eval t := by
    rw [← factorial_mul_shiftedLegendreReal_eq]
    simp
  rw [show (∫ t : ℝ in 0..1,
      Real.exp (2 * lambda * t) *
        (derivative^[n] (shiftedLegendreRodriguesBase n)).eval t) =
      (n.factorial : ℝ) *
        ∫ t : ℝ in 0..1,
          Real.exp (2 * lambda * t) *
            (shiftedLegendreReal n).eval t by
    simp_rw [heval]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring] at h
  exact h

private theorem integral_exp_mul_shiftedLegendreReal_four
    (lambda : ℝ) :
    (∫ t : ℝ in 0..1,
      Real.exp (2 * lambda * t) * (shiftedLegendreReal 4).eval t) =
      (2 * lambda) ^ 4 / 24 *
        ∫ t : ℝ in 0..1,
          Real.exp (2 * lambda * t) * (t ^ 4 * (1 - t) ^ 4) := by
  have h := factorial_mul_integral_exp_shiftedLegendreReal 4 lambda
  have hbase (t : ℝ) :
      (shiftedLegendreRodriguesBase 4).eval t =
        t ^ 4 * (1 - t) ^ 4 := by
    simp [shiftedLegendreRodriguesBase]
  simp_rw [hbase] at h
  norm_num at h
  calc
    _ = (1 / 24 : ℝ) *
        (24 * ∫ t : ℝ in 0..1,
          Real.exp (2 * lambda * t) * (shiftedLegendreReal 4).eval t) := by
      ring
    _ = (1 / 24 : ℝ) *
        ((2 * lambda) ^ 4 *
          ∫ t : ℝ in 0..1,
            Real.exp (2 * lambda * t) * (t ^ 4 * (1 - t) ^ 4)) := by
      rw [h]
    _ = _ := by ring

private theorem integral_exp_mul_shiftedLegendreReal_five
    (lambda : ℝ) :
    (∫ t : ℝ in 0..1,
      Real.exp (2 * lambda * t) * (shiftedLegendreReal 5).eval t) =
      (-2 * lambda) ^ 5 / 120 *
        ∫ t : ℝ in 0..1,
          Real.exp (2 * lambda * t) * (t ^ 5 * (1 - t) ^ 5) := by
  have h := factorial_mul_integral_exp_shiftedLegendreReal 5 lambda
  have hbase (t : ℝ) :
      (shiftedLegendreRodriguesBase 5).eval t =
        t ^ 5 * (1 - t) ^ 5 := by
    simp [shiftedLegendreRodriguesBase]
  simp_rw [hbase] at h
  norm_num at h
  calc
    _ = (1 / 120 : ℝ) *
        (120 * ∫ t : ℝ in 0..1,
          Real.exp (2 * lambda * t) * (shiftedLegendreReal 5).eval t) := by
      ring
    _ = (1 / 120 : ℝ) *
        ((-2 * lambda) ^ 5 *
          ∫ t : ℝ in 0..1,
            Real.exp (2 * lambda * t) * (t ^ 5 * (1 - t) ^ 5)) := by
      rw [show -2 * lambda = -(2 * lambda) by ring]
      rw [h]
    _ = _ := by ring

private theorem centeredCoshMoment_P4_eq_exp (lambda : ℝ) :
    centeredCoshMoment factorTwoCenteredP4 lambda =
      ∫ x : ℝ in -1..1,
        Real.exp (lambda * x) * factorTwoCenteredP4 x := by
  have hzero := centeredSinhMoment_eq_zero_of_even
    even_factorTwoCenteredP4 lambda
  unfold centeredCoshMoment
  calc
    _ = (∫ x : ℝ in -1..1,
          Real.cosh (lambda * x) * factorTwoCenteredP4 x) +
        ∫ x : ℝ in -1..1,
          Real.sinh (lambda * x) * factorTwoCenteredP4 x := by
      rw [show (∫ x : ℝ in -1..1,
          Real.sinh (lambda * x) * factorTwoCenteredP4 x) = 0 by
        exact hzero]
      ring
    _ = ∫ x : ℝ in -1..1,
        (Real.cosh (lambda * x) * factorTwoCenteredP4 x +
          Real.sinh (lambda * x) * factorTwoCenteredP4 x) := by
      rw [intervalIntegral.integral_add]
      · exact Continuous.intervalIntegrable
          ((Real.continuous_cosh.comp (by fun_prop)).mul
            continuous_factorTwoCenteredP4) (-1) 1
      · exact Continuous.intervalIntegrable
          ((Real.continuous_sinh.comp (by fun_prop)).mul
            continuous_factorTwoCenteredP4) (-1) 1
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x _
      change Real.cosh (lambda * x) * factorTwoCenteredP4 x +
        Real.sinh (lambda * x) * factorTwoCenteredP4 x =
          Real.exp (lambda * x) * factorTwoCenteredP4 x
      rw [← add_mul, Real.cosh_add_sinh]

private theorem centeredSinhMoment_P5_eq_exp (lambda : ℝ) :
    centeredSinhMoment factorTwoCenteredP5 lambda =
      ∫ x : ℝ in -1..1,
        Real.exp (lambda * x) * factorTwoCenteredP5 x := by
  have hzero := centeredCoshMoment_eq_zero_of_odd
    odd_factorTwoCenteredP5 lambda
  unfold centeredSinhMoment
  calc
    _ = (∫ x : ℝ in -1..1,
          Real.cosh (lambda * x) * factorTwoCenteredP5 x) +
        ∫ x : ℝ in -1..1,
          Real.sinh (lambda * x) * factorTwoCenteredP5 x := by
      rw [show (∫ x : ℝ in -1..1,
          Real.cosh (lambda * x) * factorTwoCenteredP5 x) = 0 by
        exact hzero]
      ring
    _ = ∫ x : ℝ in -1..1,
        (Real.cosh (lambda * x) * factorTwoCenteredP5 x +
          Real.sinh (lambda * x) * factorTwoCenteredP5 x) := by
      rw [intervalIntegral.integral_add]
      · exact Continuous.intervalIntegrable
          ((Real.continuous_cosh.comp (by fun_prop)).mul
            continuous_factorTwoCenteredP5) (-1) 1
      · exact Continuous.intervalIntegrable
          ((Real.continuous_sinh.comp (by fun_prop)).mul
            continuous_factorTwoCenteredP5) (-1) 1
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x _
      change Real.cosh (lambda * x) * factorTwoCenteredP5 x +
        Real.sinh (lambda * x) * factorTwoCenteredP5 x =
          Real.exp (lambda * x) * factorTwoCenteredP5 x
      rw [← add_mul, Real.cosh_add_sinh]

/-- Exact positive Rodrigues representation of the `P₄` hyperbolic
moment. -/
theorem centeredCoshMoment_P4_rodrigues (lambda : ℝ) :
    centeredCoshMoment factorTwoCenteredP4 lambda =
      2 * Real.exp (-lambda) * ((2 * lambda) ^ 4 / 24) *
        ∫ t : ℝ in 0..1,
          Real.exp (2 * lambda * t) * (t ^ 4 * (1 - t) ^ 4) := by
  rw [centeredCoshMoment_P4_eq_exp]
  have htransport := integral_comp_two_mul_sub_one
    (fun x : ℝ ↦ Real.exp (lambda * x) * factorTwoCenteredP4 x)
  have hunit :
      (∫ t : ℝ in 0..1,
          Real.exp (lambda * (2 * t - 1)) *
            factorTwoCenteredP4 (2 * t - 1)) =
        Real.exp (-lambda) *
          ∫ t : ℝ in 0..1,
            Real.exp (2 * lambda * t) *
              (shiftedLegendreReal 4).eval t := by
    rw [show (fun t : ℝ ↦
        Real.exp (lambda * (2 * t - 1)) *
          factorTwoCenteredP4 (2 * t - 1)) =
        fun t ↦ Real.exp (-lambda) *
          (Real.exp (2 * lambda * t) *
            (shiftedLegendreReal 4).eval t) by
      funext t
      rw [factorTwoCenteredP4_affine]
      rw [show lambda * (2 * t - 1) = -lambda + 2 * lambda * t by ring,
        Real.exp_add]
      ring,
      intervalIntegral.integral_const_mul]
  rw [hunit, integral_exp_mul_shiftedLegendreReal_four] at htransport
  linarith

/-- Exact positive Rodrigues representation of the `P₅` hyperbolic
moment. -/
theorem centeredSinhMoment_P5_rodrigues (lambda : ℝ) :
    centeredSinhMoment factorTwoCenteredP5 lambda =
      2 * Real.exp (-lambda) * ((2 * lambda) ^ 5 / 120) *
        ∫ t : ℝ in 0..1,
          Real.exp (2 * lambda * t) * (t ^ 5 * (1 - t) ^ 5) := by
  rw [centeredSinhMoment_P5_eq_exp]
  have htransport := integral_comp_two_mul_sub_one
    (fun x : ℝ ↦ Real.exp (lambda * x) * factorTwoCenteredP5 x)
  have hunit :
      (∫ t : ℝ in 0..1,
          Real.exp (lambda * (2 * t - 1)) *
            factorTwoCenteredP5 (2 * t - 1)) =
        -Real.exp (-lambda) *
          ∫ t : ℝ in 0..1,
            Real.exp (2 * lambda * t) *
              (shiftedLegendreReal 5).eval t := by
    rw [show (fun t : ℝ ↦
        Real.exp (lambda * (2 * t - 1)) *
          factorTwoCenteredP5 (2 * t - 1)) =
        fun t ↦ -Real.exp (-lambda) *
          (Real.exp (2 * lambda * t) *
            (shiftedLegendreReal 5).eval t) by
      funext t
      rw [factorTwoCenteredP5_affine]
      rw [show lambda * (2 * t - 1) = -lambda + 2 * lambda * t by ring,
        Real.exp_add]
      ring,
      intervalIntegral.integral_const_mul]
  rw [hunit, integral_exp_mul_shiftedLegendreReal_five] at htransport
  linarith

/-! ## A global Laplace envelope -/

private theorem integral_exp_neg_mul_pow_zero (r : ℝ) (hr : 0 < r) :
    (∫ u : ℝ in 0..1, Real.exp (-r * u)) =
      (1 - Real.exp (-r)) / r := by
  have hderiv (u : ℝ) :
      HasDerivAt (fun x : ℝ ↦ -(1 / r) * Real.exp (-r * x))
        (Real.exp (-r * u)) u := by
    convert ((Real.hasDerivAt_exp (-r * u)).comp u
      ((hasDerivAt_id u).const_mul (-r))).const_mul (-(1 / r)) using 1
    all_goals field_simp [hr.ne']
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ hderiv u)
    (Continuous.intervalIntegrable (by fun_prop) 0 1)
  convert h using 1
  simp only [mul_zero, Real.exp_zero, mul_one]
  field_simp [hr.ne']
  ring

private theorem integral_exp_neg_mul_pow_succ
    (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (∫ u : ℝ in 0..1, Real.exp (-r * u) * u ^ (n + 1)) =
      -Real.exp (-r) / r +
        ((n + 1 : ℕ) : ℝ) / r *
          ∫ u : ℝ in 0..1, Real.exp (-r * u) * u ^ n := by
  have hpow (u : ℝ) :
      HasDerivAt (fun x : ℝ ↦ x ^ (n + 1))
        (((n + 1 : ℕ) : ℝ) * u ^ n) u := by
    convert (hasDerivAt_id u).pow (n + 1) using 1
    all_goals simp [Nat.cast_add]
  have hexp (u : ℝ) :
      HasDerivAt (fun x : ℝ ↦ -(1 / r) * Real.exp (-r * x))
        (Real.exp (-r * u)) u := by
    convert ((Real.hasDerivAt_exp (-r * u)).comp u
      ((hasDerivAt_id u).const_mul (-r))).const_mul (-(1 / r)) using 1
    all_goals field_simp [hr.ne']
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ ↦ x ^ (n + 1))
    (u' := fun x : ℝ ↦ ((n + 1 : ℕ) : ℝ) * x ^ n)
    (v := fun x : ℝ ↦ -(1 / r) * Real.exp (-r * x))
    (v' := fun x : ℝ ↦ Real.exp (-r * x))
    (fun u _ ↦ hpow u) (fun u _ ↦ hexp u)
    (Continuous.intervalIntegrable (by fun_prop) 0 1)
    (Continuous.intervalIntegrable (by fun_prop) 0 1)
  rw [show (fun u : ℝ ↦
      ((n + 1 : ℕ) : ℝ) * u ^ n *
        (-(1 / r) * Real.exp (-r * u))) =
      fun u ↦ -(((n + 1 : ℕ) : ℝ) / r) *
        (Real.exp (-r * u) * u ^ n) by
    funext u
    field_simp [hr.ne'],
    intervalIntegral.integral_const_mul] at hibp
  simp only [zero_pow (Nat.succ_ne_zero n), one_pow,
    mul_zero, mul_one, Real.exp_zero] at hibp
  calc
    _ = ∫ u : ℝ in 0..1, u ^ (n + 1) * Real.exp (-r * u) := by
      apply intervalIntegral.integral_congr
      intro u _
      ring
    _ = _ := hibp
    _ = _ := by ring

/-- The elementary Gamma bound needed for the Rodrigues envelope, proved
by integration by parts rather than by evaluating any finite rank family. -/
theorem integral_exp_neg_mul_pow_le
    (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (∫ u : ℝ in 0..1, Real.exp (-r * u) * u ^ n) ≤
      (n.factorial : ℝ) / r ^ (n + 1) := by
  induction n with
  | zero =>
      simp only [mul_one, Nat.factorial_zero, Nat.cast_one, zero_add,
        pow_one, pow_zero]
      rw [integral_exp_neg_mul_pow_zero r hr]
      have hexp : 0 < Real.exp (-r) := Real.exp_pos _
      exact div_le_div_of_nonneg_right (by linarith) hr.le
  | succ n ih =>
      rw [integral_exp_neg_mul_pow_succ r hr n]
      have hdrop :
          -Real.exp (-r) / r ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (Real.exp_pos _).le) hr.le
      calc
        _ ≤ ((n + 1 : ℕ) : ℝ) / r *
            ∫ u : ℝ in 0..1, Real.exp (-r * u) * u ^ n := by
          linarith
        _ ≤ ((n + 1 : ℕ) : ℝ) / r *
            ((n.factorial : ℝ) / r ^ (n + 1)) := by
          exact mul_le_mul_of_nonneg_left ih (by positivity)
        _ = ((n + 1).factorial : ℝ) / r ^ ((n + 1) + 1) := by
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
            pow_succ]
          field_simp [hr.ne']
          ring

/-- The shifted Rodrigues integral has one global exponential envelope. -/
theorem exp_neg_two_mul_rodriguesIntegral_le
    (n : ℕ) (hn : 0 < n) (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    Real.exp (-2 * lambda) *
        (∫ t : ℝ in 0..1,
          Real.exp (2 * lambda * t) * (t ^ n * (1 - t) ^ n)) ≤
      (n.factorial : ℝ) / (2 * lambda + n) ^ (n + 1) := by
  have hweighted :
      Real.exp (-2 * lambda) *
          (∫ t : ℝ in 0..1,
            Real.exp (2 * lambda * t) * (t ^ n * (1 - t) ^ n)) =
        ∫ t : ℝ in 0..1,
          Real.exp (-2 * lambda * (1 - t)) *
            (t ^ n * (1 - t) ^ n) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [← mul_assoc]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hweighted]
  have hmono :
      (∫ t : ℝ in 0..1,
          Real.exp (-2 * lambda * (1 - t)) *
            (t ^ n * (1 - t) ^ n)) ≤
        ∫ t : ℝ in 0..1,
          Real.exp (-(2 * lambda + n) * (1 - t)) *
            (1 - t) ^ n := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num : (0 : ℝ) ≤ 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
    intro t ht
    have ht0 : 0 ≤ t := ht.1.le
    have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    have htExp : t ≤ Real.exp (-(1 - t)) := by
      have h := Real.add_one_le_exp (t - 1)
      convert h using 1 <;> ring
    have hpow : t ^ n ≤ Real.exp (-(1 - t)) ^ n := by
      exact pow_le_pow_left₀ ht0 htExp n
    calc
      _ ≤ Real.exp (-2 * lambda * (1 - t)) *
          (Real.exp (-(1 - t)) ^ n * (1 - t) ^ n) := by
        gcongr
      _ = _ := by
        rw [← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  refine hmono.trans ?_
  let g : ℝ → ℝ := fun u ↦
    Real.exp (-(2 * lambda + n) * u) * u ^ n
  have hreflect :
      (∫ t : ℝ in 0..1,
          Real.exp (-(2 * lambda + n) * (1 - t)) *
            (1 - t) ^ n) =
        ∫ u : ℝ in 0..1,
          Real.exp (-(2 * lambda + n) * u) * u ^ n := by
    simpa only [sub_self, sub_zero, g] using
      (intervalIntegral.integral_comp_sub_left
        (f := g) (a := (0 : ℝ)) (b := 1) 1)
  rw [hreflect]
  apply integral_exp_neg_mul_pow_le
  positivity

/-- The global squared rank profile for `P₄`. -/
def factorTwoP4RankProfile (lambda : ℝ) : ℝ :=
  lambda ^ 8 / (lambda + 2) ^ 10

/-- The global squared rank profile for `P₅`. -/
def factorTwoP5RankProfile (lambda : ℝ) : ℝ :=
  lambda ^ 10 / (lambda + 5 / 2) ^ 12

theorem factorTwoP4RankProfile_eq (lambda : ℝ) :
    factorTwoP4RankProfile lambda = lambda ^ 8 / (lambda + 2) ^ 10 := by
  rfl

theorem factorTwoP5RankProfile_eq (lambda : ℝ) :
    factorTwoP5RankProfile lambda = lambda ^ 10 / (lambda + 5 / 2) ^ 12 := by
  rfl

private theorem hasDerivAt_factorTwoP4RankProfile
    (lambda : ℝ) (hden : lambda + 2 ≠ 0) :
    HasDerivAt factorTwoP4RankProfile
      (2 * lambda ^ 7 * (8 - lambda) / (lambda + 2) ^ 11) lambda := by
  have hnum : HasDerivAt (fun x : ℝ ↦ x ^ 8)
      (8 * lambda ^ 7) lambda := by
    convert (hasDerivAt_id lambda).pow 8 using 1
    all_goals norm_num
  have hden' : HasDerivAt (fun x : ℝ ↦ (x + 2) ^ 10)
      (10 * (lambda + 2) ^ 9) lambda := by
    convert ((hasDerivAt_id lambda).add
      (hasDerivAt_const lambda 2)).pow 10 using 1
    all_goals norm_num
  unfold factorTwoP4RankProfile
  convert hnum.div hden' (pow_ne_zero 10 hden) using 1
  field_simp [hden]
  ring

private theorem hasDerivAt_factorTwoP5RankProfile
    (lambda : ℝ) (hden : lambda + 5 / 2 ≠ 0) :
    HasDerivAt factorTwoP5RankProfile
      (2 * lambda ^ 9 * (25 / 2 - lambda) /
        (lambda + 5 / 2) ^ 13) lambda := by
  have hnum : HasDerivAt (fun x : ℝ ↦ x ^ 10)
      (10 * lambda ^ 9) lambda := by
    convert (hasDerivAt_id lambda).pow 10 using 1
    all_goals norm_num
  have hden' : HasDerivAt (fun x : ℝ ↦ (x + 5 / 2) ^ 12)
      (12 * (lambda + 5 / 2) ^ 11) lambda := by
    convert ((hasDerivAt_id lambda).add
      (hasDerivAt_const lambda (5 / 2))).pow 12 using 1
    all_goals norm_num
  unfold factorTwoP5RankProfile
  convert hnum.div hden' (pow_ne_zero 12 hden) using 1
  field_simp [hden]
  ring

theorem factorTwoP4RankProfile_monotoneOn :
    MonotoneOn factorTwoP4RankProfile (Icc 0 8) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 8)
  · intro x hx
    exact (hasDerivAt_factorTwoP4RankProfile x (by linarith [hx.1]))
      |>.continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_factorTwoP4RankProfile x
      (by linarith [(interior_subset hx).1]))
      |>.differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' := interior_subset hx
    rw [(hasDerivAt_factorTwoP4RankProfile x (by linarith [hx'.1])).deriv]
    have hx0 : 0 ≤ x := hx'.1
    have hden : 0 ≤ (x + 2) ^ 11 := pow_nonneg (by linarith) 11
    have hnum : 0 ≤ 2 * x ^ 7 * (8 - x) := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg hx0 7))
        (by linarith [hx'.2])
    exact div_nonneg hnum hden

theorem factorTwoP4RankProfile_antitoneOn :
    AntitoneOn factorTwoP4RankProfile (Ici 8) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 8)
  · intro x hx
    have hx8 : 8 ≤ x := hx
    exact (hasDerivAt_factorTwoP4RankProfile x (by linarith))
      |>.continuousAt.continuousWithinAt
  · intro x hx
    have hx8 : 8 ≤ x := interior_subset hx
    exact (hasDerivAt_factorTwoP4RankProfile x
      (by linarith))
      |>.differentiableAt.differentiableWithinAt
  · intro x hx
    have hx8 : 8 ≤ x := interior_subset hx
    rw [(hasDerivAt_factorTwoP4RankProfile x (by linarith)).deriv]
    have hden : 0 < x + 2 := by linarith
    have hnum : 2 * x ^ 7 * (8 - x) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)

theorem factorTwoP5RankProfile_monotoneOn :
    MonotoneOn factorTwoP5RankProfile (Icc 0 (25 / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (25 / 2))
  · intro x hx
    exact (hasDerivAt_factorTwoP5RankProfile x (by linarith [hx.1]))
      |>.continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_factorTwoP5RankProfile x
      (by linarith [(interior_subset hx).1]))
      |>.differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' := interior_subset hx
    rw [(hasDerivAt_factorTwoP5RankProfile x (by linarith [hx'.1])).deriv]
    have hx0 : 0 ≤ x := hx'.1
    have hden : 0 ≤ (x + 5 / 2) ^ 13 := pow_nonneg (by linarith) 13
    have hnum : 0 ≤ 2 * x ^ 9 * (25 / 2 - x) := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg hx0 9))
        (by linarith [hx'.2])
    exact div_nonneg hnum hden

theorem factorTwoP5RankProfile_antitoneOn :
    AntitoneOn factorTwoP5RankProfile (Ici (25 / 2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (25 / 2))
  · intro x hx
    have hx25 : 25 / 2 ≤ x := hx
    exact (hasDerivAt_factorTwoP5RankProfile x (by linarith))
      |>.continuousAt.continuousWithinAt
  · intro x hx
    have hx25 : 25 / 2 ≤ x := interior_subset hx
    exact (hasDerivAt_factorTwoP5RankProfile x
      (by linarith))
      |>.differentiableAt.differentiableWithinAt
  · intro x hx
    have hx25 : 25 / 2 ≤ x := interior_subset hx
    rw [(hasDerivAt_factorTwoP5RankProfile x (by linarith)).deriv]
    have hden : 0 < x + 5 / 2 := by linarith
    have hnum : 2 * x ^ 9 * (25 / 2 - x) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)

theorem factorTwoP4RankProfile_le_max
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    factorTwoP4RankProfile lambda ≤ (16384 / 9765625 : ℝ) := by
  have hpeak : factorTwoP4RankProfile 8 =
      (16384 / 9765625 : ℝ) := by
    norm_num [factorTwoP4RankProfile]
  rw [← hpeak]
  by_cases hle : lambda ≤ 8
  · exact factorTwoP4RankProfile_monotoneOn
      ⟨hlambda, hle⟩ ⟨by norm_num, le_rfl⟩ hle
  · have hgt : 8 < lambda := lt_of_not_ge hle
    exact factorTwoP4RankProfile_antitoneOn
      (by norm_num) hgt.le hgt.le

theorem factorTwoP5RankProfile_le_max
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    factorTwoP5RankProfile lambda ≤ (390625 / 544195584 : ℝ) := by
  have hpeak : factorTwoP5RankProfile (25 / 2) =
      (390625 / 544195584 : ℝ) := by
    norm_num [factorTwoP5RankProfile]
  rw [← hpeak]
  by_cases hle : lambda ≤ 25 / 2
  · exact factorTwoP5RankProfile_monotoneOn
      ⟨hlambda, hle⟩ ⟨by norm_num, le_rfl⟩ hle
  · have hgt : 25 / 2 < lambda := lt_of_not_ge hle
    exact factorTwoP5RankProfile_antitoneOn
      (by norm_num) hgt.le hgt.le

theorem exp_neg_mul_centeredCoshMoment_P4_le
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    Real.exp (-lambda) * centeredCoshMoment factorTwoCenteredP4 lambda ≤
      2 * (2 * lambda) ^ 4 / (2 * lambda + 4) ^ 5 := by
  have hI := exp_neg_two_mul_rodriguesIntegral_le 4 (by norm_num)
    lambda hlambda
  norm_num at hI
  rw [show -(2 * lambda) = -2 * lambda by ring] at hI
  rw [centeredCoshMoment_P4_rodrigues]
  calc
    _ = 2 * ((2 * lambda) ^ 4 / 24) *
        (Real.exp (-2 * lambda) *
          ∫ t : ℝ in 0..1,
            Real.exp (2 * lambda * t) * (t ^ 4 * (1 - t) ^ 4)) := by
      rw [show Real.exp (-2 * lambda) =
          Real.exp (-lambda) * Real.exp (-lambda) by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring
    _ ≤ 2 * ((2 * lambda) ^ 4 / 24) *
        ((24 : ℝ) / (2 * lambda + 4) ^ 5) := by
      exact mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by ring

theorem exp_neg_mul_centeredSinhMoment_P5_le
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    Real.exp (-lambda) * centeredSinhMoment factorTwoCenteredP5 lambda ≤
      2 * (2 * lambda) ^ 5 / (2 * lambda + 5) ^ 6 := by
  have hI := exp_neg_two_mul_rodriguesIntegral_le 5 (by norm_num)
    lambda hlambda
  norm_num at hI
  rw [show -(2 * lambda) = -2 * lambda by ring] at hI
  rw [centeredSinhMoment_P5_rodrigues]
  calc
    _ = 2 * ((2 * lambda) ^ 5 / 120) *
        (Real.exp (-2 * lambda) *
          ∫ t : ℝ in 0..1,
            Real.exp (2 * lambda * t) * (t ^ 5 * (1 - t) ^ 5)) := by
      rw [show Real.exp (-2 * lambda) =
          Real.exp (-lambda) * Real.exp (-lambda) by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring
    _ ≤ 2 * ((2 * lambda) ^ 5 / 120) *
        ((120 : ℝ) / (2 * lambda + 5) ^ 6) := by
      exact mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by ring

theorem exp_weighted_centeredCoshMoment_P4_sq_le_profile
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    Real.exp (-2 * lambda) *
        centeredCoshMoment factorTwoCenteredP4 lambda ^ 2 ≤
      factorTwoP4RankProfile lambda := by
  have h := exp_neg_mul_centeredCoshMoment_P4_le lambda hlambda
  have hmoment :
      0 ≤ Real.exp (-lambda) *
        centeredCoshMoment factorTwoCenteredP4 lambda := by
    rw [centeredCoshMoment_P4_rodrigues]
    have hI0 : 0 ≤ ∫ t : ℝ in 0..1,
        Real.exp (2 * lambda * t) * (t ^ 4 * (1 - t) ^ 4) := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
      positivity
    positivity
  have hbound : 0 ≤ 2 * (2 * lambda) ^ 4 /
      (2 * lambda + 4) ^ 5 := by positivity
  have hsq := (sq_le_sq₀ hmoment hbound).2 h
  rw [show (Real.exp (-lambda) *
      centeredCoshMoment factorTwoCenteredP4 lambda) ^ 2 =
      Real.exp (-2 * lambda) *
        centeredCoshMoment factorTwoCenteredP4 lambda ^ 2 by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    ring] at hsq
  calc
    _ ≤ (2 * (2 * lambda) ^ 4 / (2 * lambda + 4) ^ 5) ^ 2 := hsq
    _ = factorTwoP4RankProfile lambda := by
      unfold factorTwoP4RankProfile
      have hden : lambda + 2 ≠ 0 := by positivity
      have hden' : 2 * lambda + 4 ≠ 0 := by positivity
      field_simp [hden, hden']
      ring

theorem exp_weighted_centeredSinhMoment_P5_sq_le_profile
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    Real.exp (-2 * lambda) *
        centeredSinhMoment factorTwoCenteredP5 lambda ^ 2 ≤
      factorTwoP5RankProfile lambda := by
  have h := exp_neg_mul_centeredSinhMoment_P5_le lambda hlambda
  have hmoment :
      0 ≤ Real.exp (-lambda) *
        centeredSinhMoment factorTwoCenteredP5 lambda := by
    rw [centeredSinhMoment_P5_rodrigues]
    have hI0 : 0 ≤ ∫ t : ℝ in 0..1,
        Real.exp (2 * lambda * t) * (t ^ 5 * (1 - t) ^ 5) := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
      positivity
    positivity
  have hbound : 0 ≤ 2 * (2 * lambda) ^ 5 /
      (2 * lambda + 5) ^ 6 := by positivity
  have hsq := (sq_le_sq₀ hmoment hbound).2 h
  rw [show (Real.exp (-lambda) *
      centeredSinhMoment factorTwoCenteredP5 lambda) ^ 2 =
      Real.exp (-2 * lambda) *
        centeredSinhMoment factorTwoCenteredP5 lambda ^ 2 by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    ring] at hsq
  calc
    _ ≤ (2 * (2 * lambda) ^ 5 / (2 * lambda + 5) ^ 6) ^ 2 := hsq
    _ = factorTwoP5RankProfile lambda := by
      unfold factorTwoP5RankProfile
      have hden : lambda + 5 / 2 ≠ 0 := by positivity
      have hden' : 2 * lambda + 5 ≠ 0 := by positivity
      field_simp [hden, hden']

private def factorTwoP4RankPrimitive (x : ℝ) : ℝ :=
  (1 / 18) * (x / (x + 2)) ^ 9

private def factorTwoP5RankPrimitive (x : ℝ) : ℝ :=
  (2 / 55) * ((2 * x) / (2 * x + 5)) ^ 11

private theorem hasDerivAt_factorTwoP4RankPrimitive
    (x : ℝ) (hx : x + 2 ≠ 0) :
    HasDerivAt factorTwoP4RankPrimitive
      (factorTwoP4RankProfile x) x := by
  have hden : HasDerivAt (fun y : ℝ ↦ y + 2) 1 x := by
    simpa only [id_eq] using (hasDerivAt_id x).add_const 2
  have hratio := (hasDerivAt_id x).div hden hx
  have hratio' : HasDerivAt (fun y : ℝ ↦ y / (y + 2))
      (2 / (x + 2) ^ 2) x := by
    convert hratio using 1
    all_goals simp only [id_eq]
    ring
  unfold factorTwoP4RankPrimitive factorTwoP4RankProfile
  convert (hratio'.pow 9).const_mul (1 / 18) using 1
  simp only [div_pow]
  field_simp [hx]
  ring

private theorem hasDerivAt_factorTwoP5RankPrimitive
    (x : ℝ) (hx : x + 5 / 2 ≠ 0) :
    HasDerivAt factorTwoP5RankPrimitive
      (factorTwoP5RankProfile x) x := by
  have htwo : 2 * x + 5 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hnum : HasDerivAt (fun y : ℝ ↦ 2 * y) 2 x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul 2
  have hden : HasDerivAt (fun y : ℝ ↦ 2 * y + 5) 2 x := by
    simpa only using hnum.add_const 5
  have hratio := hnum.div hden htwo
  have hratio' : HasDerivAt (fun y : ℝ ↦ (2 * y) / (2 * y + 5))
      (10 / (2 * x + 5) ^ 2) x := by
    convert hratio using 1
    ring
  unfold factorTwoP5RankPrimitive factorTwoP5RankProfile
  convert (hratio'.pow 11).const_mul (2 / 55) using 1
  simp only [div_pow]
  field_simp [hx, htwo]
  ring

private def factorTwoP4LatticeProfile (t : ℝ) : ℝ :=
  factorTwoP4RankProfile
    (yoshidaEndpointA * (2 * max t 0 + 5 / 2))

private def factorTwoP5LatticeProfile (t : ℝ) : ℝ :=
  factorTwoP5RankProfile
    (yoshidaEndpointA * (2 * max t 0 + 5 / 2))

private theorem continuous_factorTwoP4LatticeProfile :
    Continuous factorTwoP4LatticeProfile := by
  have hmax : Continuous (fun t : ℝ ↦ max t 0) :=
    continuous_id.max continuous_const
  have harg : Continuous
      (fun t : ℝ ↦ yoshidaEndpointA * (2 * max t 0 + 5 / 2)) := by
    fun_prop
  unfold factorTwoP4LatticeProfile factorTwoP4RankProfile
  exact (harg.pow 8).div ((harg.add continuous_const).pow 10)
    (fun t ↦ pow_ne_zero 10 (by
      have hA := yoshidaEndpointA_pos
      have hm : 0 ≤ max t 0 := le_max_right t 0
      positivity))

private theorem continuous_factorTwoP5LatticeProfile :
    Continuous factorTwoP5LatticeProfile := by
  have hmax : Continuous (fun t : ℝ ↦ max t 0) :=
    continuous_id.max continuous_const
  have harg : Continuous
      (fun t : ℝ ↦ yoshidaEndpointA * (2 * max t 0 + 5 / 2)) := by
    fun_prop
  unfold factorTwoP5LatticeProfile factorTwoP5RankProfile
  exact (harg.pow 10).div ((harg.add continuous_const).pow 12)
    (fun t ↦ pow_ne_zero 12 (by
      have hA := yoshidaEndpointA_pos
      have hm : 0 ≤ max t 0 := le_max_right t 0
      positivity))

private theorem factorTwoP4LatticeProfile_nonneg (t : ℝ) :
    0 ≤ factorTwoP4LatticeProfile t := by
  unfold factorTwoP4LatticeProfile factorTwoP4RankProfile
  positivity

private theorem factorTwoP5LatticeProfile_nonneg (t : ℝ) :
    0 ≤ factorTwoP5LatticeProfile t := by
  unfold factorTwoP5LatticeProfile factorTwoP5RankProfile
  positivity

private def factorTwoP4AffineProfile (t : ℝ) : ℝ :=
  factorTwoP4RankProfile
    (yoshidaEndpointA * (2 * t + 5 / 2))

private def factorTwoP5AffineProfile (t : ℝ) : ℝ :=
  factorTwoP5RankProfile
    (yoshidaEndpointA * (2 * t + 5 / 2))

private def factorTwoP4LatticePrimitive (t : ℝ) : ℝ :=
  (1 / (2 * yoshidaEndpointA)) *
    factorTwoP4RankPrimitive
      (yoshidaEndpointA * (2 * t + 5 / 2))

private def factorTwoP5LatticePrimitive (t : ℝ) : ℝ :=
  (1 / (2 * yoshidaEndpointA)) *
    factorTwoP5RankPrimitive
      (yoshidaEndpointA * (2 * t + 5 / 2))

private theorem factorTwoP4RankPrimitive_nonneg
    (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ factorTwoP4RankPrimitive x := by
  unfold factorTwoP4RankPrimitive
  positivity

private theorem factorTwoP4RankPrimitive_le
    (x : ℝ) (hx : 0 ≤ x) :
    factorTwoP4RankPrimitive x ≤ 1 / 18 := by
  have hden : 0 < x + 2 := by linarith
  have hratio0 : 0 ≤ x / (x + 2) := div_nonneg hx hden.le
  have hratio1 : x / (x + 2) ≤ 1 :=
    (div_le_one₀ hden).2 (by linarith)
  have hp := pow_le_one₀ hratio0 hratio1 (n := 9)
  unfold factorTwoP4RankPrimitive
  norm_num at hp ⊢
  linarith

private theorem factorTwoP5RankPrimitive_nonneg
    (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ factorTwoP5RankPrimitive x := by
  unfold factorTwoP5RankPrimitive
  positivity

private theorem factorTwoP5RankPrimitive_le
    (x : ℝ) (hx : 0 ≤ x) :
    factorTwoP5RankPrimitive x ≤ 2 / 55 := by
  have hden : 0 < 2 * x + 5 := by linarith
  have hratio0 : 0 ≤ (2 * x) / (2 * x + 5) :=
    div_nonneg (by positivity) hden.le
  have hratio1 : (2 * x) / (2 * x + 5) ≤ 1 :=
    (div_le_one₀ hden).2 (by linarith)
  have hp := pow_le_one₀ hratio0 hratio1 (n := 11)
  unfold factorTwoP5RankPrimitive
  norm_num at hp ⊢
  linarith

private theorem hasDerivAt_factorTwoP4LatticePrimitive
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt factorTwoP4LatticePrimitive
      (factorTwoP4AffineProfile t) t := by
  have hlinear : HasDerivAt (fun s : ℝ ↦ 2 * s + 5 / 2) 2 t := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul 2).add_const (5 / 2)
  have harg : HasDerivAt
      (fun s : ℝ ↦ yoshidaEndpointA * (2 * s + 5 / 2))
      (2 * yoshidaEndpointA) t := by
    convert hlinear.const_mul yoshidaEndpointA using 1
    ring
  have harg0 : 0 ≤ yoshidaEndpointA * (2 * t + 5 / 2) := by
    exact mul_nonneg yoshidaEndpointA_pos.le (by linarith)
  have houter :=
    (hasDerivAt_factorTwoP4RankPrimitive
      (yoshidaEndpointA * (2 * t + 5 / 2)) (by linarith)).comp t harg
  unfold factorTwoP4LatticePrimitive factorTwoP4AffineProfile
  convert houter.const_mul (1 / (2 * yoshidaEndpointA)) using 1
  field_simp [yoshidaEndpointA_pos.ne']

private theorem hasDerivAt_factorTwoP5LatticePrimitive
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt factorTwoP5LatticePrimitive
      (factorTwoP5AffineProfile t) t := by
  have hlinear : HasDerivAt (fun s : ℝ ↦ 2 * s + 5 / 2) 2 t := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul 2).add_const (5 / 2)
  have harg : HasDerivAt
      (fun s : ℝ ↦ yoshidaEndpointA * (2 * s + 5 / 2))
      (2 * yoshidaEndpointA) t := by
    convert hlinear.const_mul yoshidaEndpointA using 1
    ring
  have harg0 : 0 ≤ yoshidaEndpointA * (2 * t + 5 / 2) := by
    exact mul_nonneg yoshidaEndpointA_pos.le (by linarith)
  have houter :=
    (hasDerivAt_factorTwoP5RankPrimitive
      (yoshidaEndpointA * (2 * t + 5 / 2)) (by linarith)).comp t harg
  unfold factorTwoP5LatticePrimitive factorTwoP5AffineProfile
  convert houter.const_mul (1 / (2 * yoshidaEndpointA)) using 1
  field_simp [yoshidaEndpointA_pos.ne']

private theorem intervalIntegral_factorTwoP4LatticeProfile_le
    (N : ℕ) :
    (∫ t : ℝ in 0..N, factorTwoP4LatticeProfile t) ≤
      1 / (36 * yoshidaEndpointA) := by
  have hN : (0 : ℝ) ≤ N := by positivity
  have huIcc : uIcc (0 : ℝ) (N : ℝ) = Icc (0 : ℝ) (N : ℝ) :=
    uIcc_of_le hN
  have heq : EqOn factorTwoP4LatticeProfile factorTwoP4AffineProfile
      (uIcc (0 : ℝ) (N : ℝ)) := by
    intro t ht
    have ht0 : 0 ≤ t := by
      rw [huIcc] at ht
      exact ht.1
    unfold factorTwoP4LatticeProfile factorTwoP4AffineProfile
    rw [max_eq_left ht0]
  have hintAffine : IntervalIntegrable factorTwoP4AffineProfile volume 0 N :=
    IntervalIntegrable.congr (heq.mono uIoc_subset_uIcc)
      (continuous_factorTwoP4LatticeProfile.intervalIntegrable 0 N)
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_factorTwoP4LatticePrimitive t (by
      rw [huIcc] at ht
      exact ht.1)) hintAffine
  have hargN0 : 0 ≤ yoshidaEndpointA * (2 * (N : ℝ) + 5 / 2) := by
    exact mul_nonneg yoshidaEndpointA_pos.le (by positivity)
  have harg00 : 0 ≤ yoshidaEndpointA * (2 * (0 : ℝ) + 5 / 2) := by
    exact mul_nonneg yoshidaEndpointA_pos.le (by norm_num)
  have hupper := factorTwoP4RankPrimitive_le
    (yoshidaEndpointA * (2 * (N : ℝ) + 5 / 2)) hargN0
  have hlower := factorTwoP4RankPrimitive_nonneg
    (yoshidaEndpointA * (2 * (0 : ℝ) + 5 / 2)) harg00
  have hc : 0 ≤ 1 / (2 * yoshidaEndpointA) :=
    (one_div_pos.mpr (mul_pos (by norm_num) yoshidaEndpointA_pos)).le
  calc
    (∫ t : ℝ in 0..N, factorTwoP4LatticeProfile t) =
        ∫ t : ℝ in 0..N, factorTwoP4AffineProfile t :=
      intervalIntegral.integral_congr heq
    _ = factorTwoP4LatticePrimitive N -
        factorTwoP4LatticePrimitive 0 := hfund
    _ ≤ (1 / (2 * yoshidaEndpointA)) * (1 / 18) -
        (1 / (2 * yoshidaEndpointA)) * 0 := by
      unfold factorTwoP4LatticePrimitive
      exact sub_le_sub
        (mul_le_mul_of_nonneg_left hupper hc)
        (mul_le_mul_of_nonneg_left hlower hc)
    _ = 1 / (36 * yoshidaEndpointA) := by
      field_simp [yoshidaEndpointA_pos.ne']
      norm_num

private theorem intervalIntegral_factorTwoP5LatticeProfile_le
    (N : ℕ) :
    (∫ t : ℝ in 0..N, factorTwoP5LatticeProfile t) ≤
      1 / (55 * yoshidaEndpointA) := by
  have hN : (0 : ℝ) ≤ N := by positivity
  have huIcc : uIcc (0 : ℝ) (N : ℝ) = Icc (0 : ℝ) (N : ℝ) :=
    uIcc_of_le hN
  have heq : EqOn factorTwoP5LatticeProfile factorTwoP5AffineProfile
      (uIcc (0 : ℝ) (N : ℝ)) := by
    intro t ht
    have ht0 : 0 ≤ t := by
      rw [huIcc] at ht
      exact ht.1
    unfold factorTwoP5LatticeProfile factorTwoP5AffineProfile
    rw [max_eq_left ht0]
  have hintAffine : IntervalIntegrable factorTwoP5AffineProfile volume 0 N :=
    IntervalIntegrable.congr (heq.mono uIoc_subset_uIcc)
      (continuous_factorTwoP5LatticeProfile.intervalIntegrable 0 N)
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_factorTwoP5LatticePrimitive t (by
      rw [huIcc] at ht
      exact ht.1)) hintAffine
  have hargN0 : 0 ≤ yoshidaEndpointA * (2 * (N : ℝ) + 5 / 2) := by
    exact mul_nonneg yoshidaEndpointA_pos.le (by positivity)
  have harg00 : 0 ≤ yoshidaEndpointA * (2 * (0 : ℝ) + 5 / 2) := by
    exact mul_nonneg yoshidaEndpointA_pos.le (by norm_num)
  have hupper := factorTwoP5RankPrimitive_le
    (yoshidaEndpointA * (2 * (N : ℝ) + 5 / 2)) hargN0
  have hlower := factorTwoP5RankPrimitive_nonneg
    (yoshidaEndpointA * (2 * (0 : ℝ) + 5 / 2)) harg00
  have hc : 0 ≤ 1 / (2 * yoshidaEndpointA) :=
    (one_div_pos.mpr (mul_pos (by norm_num) yoshidaEndpointA_pos)).le
  calc
    (∫ t : ℝ in 0..N, factorTwoP5LatticeProfile t) =
        ∫ t : ℝ in 0..N, factorTwoP5AffineProfile t :=
      intervalIntegral.integral_congr heq
    _ = factorTwoP5LatticePrimitive N -
        factorTwoP5LatticePrimitive 0 := hfund
    _ ≤ (1 / (2 * yoshidaEndpointA)) * (2 / 55) -
        (1 / (2 * yoshidaEndpointA)) * 0 := by
      unfold factorTwoP5LatticePrimitive
      exact sub_le_sub
        (mul_le_mul_of_nonneg_left hupper hc)
        (mul_le_mul_of_nonneg_left hlower hc)
    _ = 1 / (55 * yoshidaEndpointA) := by
      field_simp [yoshidaEndpointA_pos.ne']
      norm_num

private def factorTwoP4LatticePeak : ℝ :=
  4 / yoshidaEndpointA - 5 / 4

private def factorTwoP5LatticePeak : ℝ :=
  25 / (4 * yoshidaEndpointA) - 5 / 4

private theorem yoshidaEndpointA_le_seven_twentieths :
    yoshidaEndpointA ≤ (7 / 20 : ℝ) := by
  unfold yoshidaEndpointA
  have h := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith

private theorem one_third_le_yoshidaEndpointA :
    (1 / 3 : ℝ) ≤ yoshidaEndpointA := by
  unfold yoshidaEndpointA
  have h := six_hundred_ninety_three_div_thousand_lt_log_two
  norm_num at h ⊢
  linarith

private theorem twenty_five_div_seventy_three_le_yoshidaEndpointA :
    (25 / 73 : ℝ) ≤ yoshidaEndpointA := by
  unfold yoshidaEndpointA
  have h := six_hundred_ninety_three_div_thousand_lt_log_two
  norm_num at h ⊢
  linarith

private theorem factorTwoP4LatticePeak_arg :
    yoshidaEndpointA * (2 * factorTwoP4LatticePeak + 5 / 2) = 8 := by
  unfold factorTwoP4LatticePeak
  field_simp [yoshidaEndpointA_pos.ne']
  ring

private theorem factorTwoP5LatticePeak_arg :
    yoshidaEndpointA * (2 * factorTwoP5LatticePeak + 5 / 2) =
      25 / 2 := by
  unfold factorTwoP5LatticePeak
  field_simp [yoshidaEndpointA_pos.ne']
  ring

private theorem factorTwoP4LatticePeak_mem :
    factorTwoP4LatticePeak ∈ Icc (10 : ℝ) 11 := by
  have hA2 : 0 < 2 * yoshidaEndpointA :=
    mul_pos (by norm_num) yoshidaEndpointA_pos
  have h10arg :
      yoshidaEndpointA * (2 * (10 : ℝ) + 5 / 2) ≤ 8 := by
    nlinarith [yoshidaEndpointA_le_seven_twentieths]
  have h11arg :
      8 ≤ yoshidaEndpointA * (2 * (11 : ℝ) + 5 / 2) := by
    nlinarith [one_third_le_yoshidaEndpointA]
  constructor
  · apply (mul_le_mul_iff_right₀ hA2).mp
    nlinarith [h10arg, factorTwoP4LatticePeak_arg]
  · apply (mul_le_mul_iff_right₀ hA2).mp
    nlinarith [h11arg, factorTwoP4LatticePeak_arg]

private theorem factorTwoP5LatticePeak_mem :
    factorTwoP5LatticePeak ∈ Icc (16 : ℝ) 17 := by
  have hA2 : 0 < 2 * yoshidaEndpointA :=
    mul_pos (by norm_num) yoshidaEndpointA_pos
  have h16arg :
      yoshidaEndpointA * (2 * (16 : ℝ) + 5 / 2) ≤ 25 / 2 := by
    nlinarith [yoshidaEndpointA_le_seven_twentieths]
  have h17arg :
      25 / 2 ≤ yoshidaEndpointA * (2 * (17 : ℝ) + 5 / 2) := by
    nlinarith [twenty_five_div_seventy_three_le_yoshidaEndpointA]
  constructor
  · apply (mul_le_mul_iff_right₀ hA2).mp
    nlinarith [h16arg, factorTwoP5LatticePeak_arg]
  · apply (mul_le_mul_iff_right₀ hA2).mp
    nlinarith [h17arg, factorTwoP5LatticePeak_arg]

private theorem factorTwoP4LatticeProfile_monotoneOn :
    MonotoneOn factorTwoP4LatticeProfile
      (Icc 0 factorTwoP4LatticePeak) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx.1
  have hy0 : 0 ≤ y := hy.1
  have hargxy :
      yoshidaEndpointA * (2 * x + 5 / 2) ≤
        yoshidaEndpointA * (2 * y + 5 / 2) := by
    exact mul_le_mul_of_nonneg_left (by linarith) yoshidaEndpointA_pos.le
  have hargy :
      yoshidaEndpointA * (2 * y + 5 / 2) ≤ 8 := by
    calc
      _ ≤ yoshidaEndpointA * (2 * factorTwoP4LatticePeak + 5 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith [hy.2])
          yoshidaEndpointA_pos.le
      _ = 8 := factorTwoP4LatticePeak_arg
  unfold factorTwoP4LatticeProfile
  rw [max_eq_left hx0, max_eq_left hy0]
  have hargx0 : 0 ≤ yoshidaEndpointA * (2 * x + 5 / 2) :=
    mul_nonneg yoshidaEndpointA_pos.le (by linarith)
  have hargy0 : 0 ≤ yoshidaEndpointA * (2 * y + 5 / 2) :=
    mul_nonneg yoshidaEndpointA_pos.le (by linarith)
  exact factorTwoP4RankProfile_monotoneOn
    ⟨hargx0, hargxy.trans hargy⟩ ⟨hargy0, hargy⟩ hargxy

private theorem factorTwoP4LatticeProfile_antitoneOn :
    AntitoneOn factorTwoP4LatticeProfile
      (Ici factorTwoP4LatticePeak) := by
  intro x hx y hy hxy
  have hcx : factorTwoP4LatticePeak ≤ x := hx
  have hc0 : 0 ≤ factorTwoP4LatticePeak :=
    le_trans (by norm_num) factorTwoP4LatticePeak_mem.1
  have hx0 : 0 ≤ x := hc0.trans hx
  have hy0 : 0 ≤ y := hc0.trans hy
  have hargxy :
      yoshidaEndpointA * (2 * x + 5 / 2) ≤
        yoshidaEndpointA * (2 * y + 5 / 2) := by
    exact mul_le_mul_of_nonneg_left (by linarith) yoshidaEndpointA_pos.le
  have hargx :
      8 ≤ yoshidaEndpointA * (2 * x + 5 / 2) := by
    calc
      8 = yoshidaEndpointA *
          (2 * factorTwoP4LatticePeak + 5 / 2) :=
        factorTwoP4LatticePeak_arg.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hcx])
        yoshidaEndpointA_pos.le
  unfold factorTwoP4LatticeProfile
  rw [max_eq_left hx0, max_eq_left hy0]
  exact factorTwoP4RankProfile_antitoneOn hargx (hargx.trans hargxy) hargxy

private theorem factorTwoP5LatticeProfile_monotoneOn :
    MonotoneOn factorTwoP5LatticeProfile
      (Icc 0 factorTwoP5LatticePeak) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx.1
  have hy0 : 0 ≤ y := hy.1
  have hargxy :
      yoshidaEndpointA * (2 * x + 5 / 2) ≤
        yoshidaEndpointA * (2 * y + 5 / 2) := by
    exact mul_le_mul_of_nonneg_left (by linarith) yoshidaEndpointA_pos.le
  have hargy :
      yoshidaEndpointA * (2 * y + 5 / 2) ≤ 25 / 2 := by
    calc
      _ ≤ yoshidaEndpointA * (2 * factorTwoP5LatticePeak + 5 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith [hy.2])
          yoshidaEndpointA_pos.le
      _ = 25 / 2 := factorTwoP5LatticePeak_arg
  unfold factorTwoP5LatticeProfile
  rw [max_eq_left hx0, max_eq_left hy0]
  have hargx0 : 0 ≤ yoshidaEndpointA * (2 * x + 5 / 2) :=
    mul_nonneg yoshidaEndpointA_pos.le (by linarith)
  have hargy0 : 0 ≤ yoshidaEndpointA * (2 * y + 5 / 2) :=
    mul_nonneg yoshidaEndpointA_pos.le (by linarith)
  exact factorTwoP5RankProfile_monotoneOn
    ⟨hargx0, hargxy.trans hargy⟩ ⟨hargy0, hargy⟩ hargxy

private theorem factorTwoP5LatticeProfile_antitoneOn :
    AntitoneOn factorTwoP5LatticeProfile
      (Ici factorTwoP5LatticePeak) := by
  intro x hx y hy hxy
  have hcx : factorTwoP5LatticePeak ≤ x := hx
  have hc0 : 0 ≤ factorTwoP5LatticePeak :=
    le_trans (by norm_num) factorTwoP5LatticePeak_mem.1
  have hx0 : 0 ≤ x := hc0.trans hx
  have hy0 : 0 ≤ y := hc0.trans hy
  have hargxy :
      yoshidaEndpointA * (2 * x + 5 / 2) ≤
        yoshidaEndpointA * (2 * y + 5 / 2) := by
    exact mul_le_mul_of_nonneg_left (by linarith) yoshidaEndpointA_pos.le
  have hargx :
      25 / 2 ≤ yoshidaEndpointA * (2 * x + 5 / 2) := by
    calc
      25 / 2 = yoshidaEndpointA *
          (2 * factorTwoP5LatticePeak + 5 / 2) :=
        factorTwoP5LatticePeak_arg.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hcx])
        yoshidaEndpointA_pos.le
  unfold factorTwoP5LatticeProfile
  rw [max_eq_left hx0, max_eq_left hy0]
  exact factorTwoP5RankProfile_antitoneOn hargx (hargx.trans hargxy) hargxy

/-- A nonnegative unimodal function sampled on the natural-number lattice is
bounded by its integral plus just one of the two samples bracketing its peak.
This is the structural replacement for any finite rank enumeration. -/
theorem tsum_nat_lattice_le_max_add_integral_of_unimodal
    (g : ℝ → ℝ) (c : ℝ) (k : ℕ) (I : ℝ)
    (hg : Continuous g)
    (h0 : ∀ x : ℝ, 0 ≤ g x)
    (hinc : MonotoneOn g (Icc 0 c))
    (hdec : AntitoneOn g (Ici c))
    (hkc : (k : ℝ) ≤ c)
    (hck : c ≤ (k + 1 : ℕ))
    (hI : ∀ N : ℕ, (∫ x : ℝ in 0..N, g x) ≤ I) :
    (∑' m : ℕ, g m) ≤ max (g k) (g (k + 1)) + I := by
  apply Real.tsum_le_of_sum_range_le (fun n ↦ h0 n)
  intro N
  have hsubset : Finset.range N ⊆ Finset.range (k + 2 + N) :=
    Finset.range_mono (by omega)
  have hsmall :
      (∑ i ∈ Finset.range N, g i) ≤
        ∑ i ∈ Finset.range (k + 2 + N), g i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun i _ _ ↦ h0 i)
  have hleftMono :
      MonotoneOn g (Icc (0 : ℝ) (0 + (k : ℝ))) :=
    hinc.mono (fun x hx ↦ by
      refine ⟨hx.1, ?_⟩
      have hx' : x ≤ (k : ℝ) := by simpa only [zero_add] using hx.2
      exact hx'.trans hkc)
  have hleft :=
    MonotoneOn.sum_le_integral (x₀ := 0) (a := k) hleftMono
  have hleft' :
      (∑ i ∈ Finset.range k, g i) ≤
        ∫ x : ℝ in 0..k, g x := by
    simpa using hleft
  have hrightAnti :
      AntitoneOn g
        (Icc ((k + 1 : ℕ) : ℝ)
          (((k + 1 : ℕ) : ℝ) + (N : ℝ))) :=
    hdec.mono (fun x hx ↦ by exact hck.trans hx.1)
  have hright :=
    AntitoneOn.sum_le_integral
      (x₀ := ((k + 1 : ℕ) : ℝ)) (a := N) hrightAnti
  have hright' :
      (∑ i ∈ Finset.range N, g (k + 2 + i)) ≤
        ∫ x : ℝ in (k + 1 : ℕ)..(k + 1 + N : ℕ), g x := by
    convert hright using 1
    · simp only [Nat.cast_add, Nat.cast_one]
      ring_nf
    · simp only [Nat.cast_add, Nat.cast_one]
  have hcrossPoint :
      ∀ x ∈ Icc (k : ℝ) (k + 1 : ℕ),
        min (g k) (g (k + 1)) ≤ g x := by
    intro x hx
    rcases le_total x c with hxc | hcx
    · apply (min_le_left _ _).trans
      have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast Nat.zero_le k
      exact hinc ⟨hk0, hkc⟩ ⟨hk0.trans hx.1, hxc⟩ hx.1
    · apply (min_le_right _ _).trans
      apply hdec hcx
      · simpa only [Nat.cast_add, Nat.cast_one] using hck
      · simpa only [Nat.cast_add, Nat.cast_one] using hx.2
  have hkcast : (k : ℝ) ≤ (k + 1 : ℕ) := by
    exact_mod_cast Nat.le_succ k
  have hcross :
      min (g k) (g (k + 1)) ≤
        ∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ), g x := by
    calc
      min (g k) (g (k + 1)) =
          ∫ _x : ℝ in (k : ℝ)..(k + 1 : ℕ),
            min (g k) (g (k + 1)) := by simp
      _ ≤ _ := intervalIntegral.integral_mono_on
        hkcast
        (Continuous.intervalIntegrable continuous_const _ _)
        (hg.intervalIntegrable _ _)
        hcrossPoint
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume)
    (hg.intervalIntegrable (0 : ℝ) k)
    (hg.intervalIntegrable (k : ℝ) (k + 1 : ℕ))
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume)
    (hg.intervalIntegrable (0 : ℝ) (k + 1 : ℕ))
    (hg.intervalIntegrable (k + 1 : ℕ) (k + 1 + N : ℕ))
  have hdecomp :
      (∑ i ∈ Finset.range (k + 2 + N), g i) =
        (∑ i ∈ Finset.range k, g i) +
          g k + g (k + 1) +
            ∑ i ∈ Finset.range N, g (k + 2 + i) := by
    rw [show k + 2 + N = (k + 2) + N by omega,
      Finset.sum_range_add, Finset.sum_range_succ,
      Finset.sum_range_succ]
    norm_num only [Nat.cast_add, Nat.cast_one]
  have hpair := max_add_min (g k) (g (k + 1))
  calc
    (∑ i ∈ Finset.range N, g i)
        ≤ ∑ i ∈ Finset.range (k + 2 + N), g i := hsmall
    _ ≤ max (g k) (g (k + 1)) +
          ∫ x : ℝ in 0..(k + 1 + N : ℕ), g x := by
      rw [hdecomp]
      norm_num only [Nat.cast_add, Nat.cast_one] at hleft' hright' hcross hadd1 hadd2 hpair ⊢
      linarith
    _ ≤ max (g k) (g (k + 1)) + I := by
      linarith [hI (k + 1 + N)]

private theorem tsum_factorTwoP4LatticeProfile_le :
    (∑' m : ℕ, factorTwoP4LatticeProfile m) ≤
      (16384 / 9765625 : ℝ) + 1 / (36 * yoshidaEndpointA) := by
  have h := tsum_nat_lattice_le_max_add_integral_of_unimodal
    factorTwoP4LatticeProfile factorTwoP4LatticePeak 10
    (1 / (36 * yoshidaEndpointA))
    continuous_factorTwoP4LatticeProfile
    factorTwoP4LatticeProfile_nonneg
    factorTwoP4LatticeProfile_monotoneOn
    factorTwoP4LatticeProfile_antitoneOn
    factorTwoP4LatticePeak_mem.1
    (by norm_num; exact factorTwoP4LatticePeak_mem.2)
    intervalIntegral_factorTwoP4LatticeProfile_le
  have h10 : factorTwoP4LatticeProfile (10 : ℕ) ≤
      (16384 / 9765625 : ℝ) := by
    unfold factorTwoP4LatticeProfile
    norm_num only [Nat.cast_ofNat, max_eq_left]
    apply factorTwoP4RankProfile_le_max
    exact mul_nonneg yoshidaEndpointA_pos.le (by norm_num)
  have h11 : factorTwoP4LatticeProfile (11 : ℕ) ≤
      (16384 / 9765625 : ℝ) := by
    unfold factorTwoP4LatticeProfile
    norm_num only [Nat.cast_ofNat, max_eq_left]
    apply factorTwoP4RankProfile_le_max
    exact mul_nonneg yoshidaEndpointA_pos.le (by norm_num)
  have hmax : max (factorTwoP4LatticeProfile (10 : ℕ))
      (factorTwoP4LatticeProfile (10 + 1 : ℕ)) ≤
        (16384 / 9765625 : ℝ) := by
    exact max_le h10 (by norm_num at h11 ⊢; exact h11)
  linarith

private theorem tsum_factorTwoP5LatticeProfile_le :
    (∑' m : ℕ, factorTwoP5LatticeProfile m) ≤
      (390625 / 544195584 : ℝ) + 1 / (55 * yoshidaEndpointA) := by
  have h := tsum_nat_lattice_le_max_add_integral_of_unimodal
    factorTwoP5LatticeProfile factorTwoP5LatticePeak 16
    (1 / (55 * yoshidaEndpointA))
    continuous_factorTwoP5LatticeProfile
    factorTwoP5LatticeProfile_nonneg
    factorTwoP5LatticeProfile_monotoneOn
    factorTwoP5LatticeProfile_antitoneOn
    factorTwoP5LatticePeak_mem.1
    (by norm_num; exact factorTwoP5LatticePeak_mem.2)
    intervalIntegral_factorTwoP5LatticeProfile_le
  have h16 : factorTwoP5LatticeProfile (16 : ℕ) ≤
      (390625 / 544195584 : ℝ) := by
    unfold factorTwoP5LatticeProfile
    norm_num only [Nat.cast_ofNat, max_eq_left]
    apply factorTwoP5RankProfile_le_max
    exact mul_nonneg yoshidaEndpointA_pos.le (by norm_num)
  have h17 : factorTwoP5LatticeProfile (17 : ℕ) ≤
      (390625 / 544195584 : ℝ) := by
    unfold factorTwoP5LatticeProfile
    norm_num only [Nat.cast_ofNat, max_eq_left]
    apply factorTwoP5RankProfile_le_max
    exact mul_nonneg yoshidaEndpointA_pos.le (by norm_num)
  have hmax : max (factorTwoP5LatticeProfile (16 : ℕ))
      (factorTwoP5LatticeProfile (16 + 1 : ℕ)) ≤
        (390625 / 544195584 : ℝ) := by
    exact max_le h16 (by norm_num at h17 ⊢; exact h17)
  linarith

private theorem factorTwoP4RankProfile_le_inv_sq
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    factorTwoP4RankProfile lambda ≤ 1 / (lambda + 2) ^ 2 := by
  have hden : 0 < lambda + 2 := by linarith
  have hp : lambda ^ 8 ≤ (lambda + 2) ^ 8 :=
    pow_le_pow_left₀ hlambda (by linarith) 8
  unfold factorTwoP4RankProfile
  rw [div_le_iff₀ (pow_pos hden 10)]
  field_simp [hden.ne']
  nlinarith

private theorem factorTwoP5RankProfile_le_inv_sq
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    factorTwoP5RankProfile lambda ≤ 1 / (lambda + 5 / 2) ^ 2 := by
  have hden : 0 < lambda + 5 / 2 := by linarith
  have hp : lambda ^ 10 ≤ (lambda + 5 / 2) ^ 10 :=
    pow_le_pow_left₀ hlambda (by linarith) 10
  unfold factorTwoP5RankProfile
  rw [div_le_iff₀ (pow_pos hden 12)]
  field_simp [hden.ne']
  nlinarith

private theorem summable_factorTwoLatticeMajorant :
    Summable (fun m : ℕ ↦
      (1 / yoshidaEndpointA ^ 2) * (1 / ((m : ℝ) + 1) ^ 2)) := by
  have hp : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).2 hp
  simpa only [Nat.cast_add, Nat.cast_one] using
    hshift.mul_left (1 / yoshidaEndpointA ^ 2)

private theorem summable_factorTwoP4LatticeProfile :
    Summable (fun m : ℕ ↦ factorTwoP4LatticeProfile m) := by
  refine Summable.of_nonneg_of_le
    (fun m : ℕ ↦ factorTwoP4LatticeProfile_nonneg (m : ℝ)) ?_
    summable_factorTwoLatticeMajorant
  intro m
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hm1 : 0 < (m : ℝ) + 1 := by positivity
  let lambda := yoshidaEndpointA * (2 * (m : ℝ) + 5 / 2)
  have hlambda0 : 0 ≤ lambda := by
    dsimp only [lambda]
    exact mul_nonneg yoshidaEndpointA_pos.le (by positivity)
  have hbase : 0 < yoshidaEndpointA * ((m : ℝ) + 1) :=
    mul_pos yoshidaEndpointA_pos hm1
  have hden : yoshidaEndpointA * ((m : ℝ) + 1) ≤ lambda + 2 := by
    dsimp only [lambda]
    nlinarith [yoshidaEndpointA_pos]
  have hsq := pow_le_pow_left₀ hbase.le hden 2
  have hinv : 1 / (lambda + 2) ^ 2 ≤
      1 / (yoshidaEndpointA * ((m : ℝ) + 1)) ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hbase 2) hsq
  calc
    factorTwoP4LatticeProfile m = factorTwoP4RankProfile lambda := by
      unfold factorTwoP4LatticeProfile
      rw [max_eq_left hm0]
    _ ≤ 1 / (lambda + 2) ^ 2 :=
      factorTwoP4RankProfile_le_inv_sq lambda hlambda0
    _ ≤ 1 / (yoshidaEndpointA * ((m : ℝ) + 1)) ^ 2 := hinv
    _ = (1 / yoshidaEndpointA ^ 2) *
        (1 / ((m : ℝ) + 1) ^ 2) := by
      field_simp [yoshidaEndpointA_pos.ne', hm1.ne']

private theorem summable_factorTwoP5LatticeProfile :
    Summable (fun m : ℕ ↦ factorTwoP5LatticeProfile m) := by
  refine Summable.of_nonneg_of_le
    (fun m : ℕ ↦ factorTwoP5LatticeProfile_nonneg (m : ℝ)) ?_
    summable_factorTwoLatticeMajorant
  intro m
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hm1 : 0 < (m : ℝ) + 1 := by positivity
  let lambda := yoshidaEndpointA * (2 * (m : ℝ) + 5 / 2)
  have hlambda0 : 0 ≤ lambda := by
    dsimp only [lambda]
    exact mul_nonneg yoshidaEndpointA_pos.le (by positivity)
  have hbase : 0 < yoshidaEndpointA * ((m : ℝ) + 1) :=
    mul_pos yoshidaEndpointA_pos hm1
  have hden : yoshidaEndpointA * ((m : ℝ) + 1) ≤
      lambda + 5 / 2 := by
    dsimp only [lambda]
    nlinarith [yoshidaEndpointA_pos]
  have hsq := pow_le_pow_left₀ hbase.le hden 2
  have hinv : 1 / (lambda + 5 / 2) ^ 2 ≤
      1 / (yoshidaEndpointA * ((m : ℝ) + 1)) ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hbase 2) hsq
  calc
    factorTwoP5LatticeProfile m = factorTwoP5RankProfile lambda := by
      unfold factorTwoP5LatticeProfile
      rw [max_eq_left hm0]
    _ ≤ 1 / (lambda + 5 / 2) ^ 2 :=
      factorTwoP5RankProfile_le_inv_sq lambda hlambda0
    _ ≤ 1 / (yoshidaEndpointA * ((m : ℝ) + 1)) ^ 2 := hinv
    _ = (1 / yoshidaEndpointA ^ 2) *
        (1 / ((m : ℝ) + 1) ^ 2) := by
      field_simp [yoshidaEndpointA_pos.ne', hm1.ne']

private theorem factorTwoP4LatticeProfile_nat_eq (m : ℕ) :
    factorTwoP4LatticeProfile m =
      factorTwoP4RankProfile (yoshidaEndpointA * oddRate (m + 1)) := by
  have hm0 : (0 : ℝ) ≤ m := by positivity
  unfold factorTwoP4LatticeProfile oddRate
  rw [max_eq_left hm0]
  congr 1
  push_cast
  ring

private theorem factorTwoP5LatticeProfile_nat_eq (m : ℕ) :
    factorTwoP5LatticeProfile m =
      factorTwoP5RankProfile (yoshidaEndpointA * oddRate (m + 1)) := by
  have hm0 : (0 : ℝ) ≤ m := by positivity
  unfold factorTwoP5LatticeProfile oddRate
  rw [max_eq_left hm0]
  congr 1
  push_cast
  ring

private theorem factorTwoP4RankTailTerm_le_latticeProfile (m : ℕ) :
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        centeredCoshMoment factorTwoCenteredP4
          (yoshidaEndpointA * oddRate (m + 1)) ^ 2 ≤
      factorTwoP4LatticeProfile m := by
  have hlambda : 0 ≤ yoshidaEndpointA * oddRate (m + 1) :=
    mul_nonneg yoshidaEndpointA_pos.le (oddRate_pos (m + 1)).le
  have h := exp_weighted_centeredCoshMoment_P4_sq_le_profile
    (yoshidaEndpointA * oddRate (m + 1)) hlambda
  rw [show -2 * yoshidaEndpointA * oddRate (m + 1) =
      -2 * (yoshidaEndpointA * oddRate (m + 1)) by ring]
  exact h.trans_eq (factorTwoP4LatticeProfile_nat_eq m).symm

private theorem factorTwoP5RankTailTerm_le_latticeProfile (m : ℕ) :
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        centeredSinhMoment factorTwoCenteredP5
          (yoshidaEndpointA * oddRate (m + 1)) ^ 2 ≤
      factorTwoP5LatticeProfile m := by
  have hlambda : 0 ≤ yoshidaEndpointA * oddRate (m + 1) :=
    mul_nonneg yoshidaEndpointA_pos.le (oddRate_pos (m + 1)).le
  have h := exp_weighted_centeredSinhMoment_P5_sq_le_profile
    (yoshidaEndpointA * oddRate (m + 1)) hlambda
  rw [show -2 * yoshidaEndpointA * oddRate (m + 1) =
      -2 * (yoshidaEndpointA * oddRate (m + 1)) by ring]
  exact h.trans_eq (factorTwoP5LatticeProfile_nat_eq m).symm

private theorem factorTwoP4RankTail_le :
    (∑' m : ℕ,
      Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        centeredCoshMoment factorTwoCenteredP4
          (yoshidaEndpointA * oddRate (m + 1)) ^ 2) ≤
      (16384 / 9765625 : ℝ) + 1 / (36 * yoshidaEndpointA) := by
  have hactual :=
    (hasSum_factorTwoCenteredArch_evenRankSquares factorTwoCenteredP4
      continuous_factorTwoCenteredP4 even_factorTwoCenteredP4).summable
  calc
    _ ≤ ∑' m : ℕ, factorTwoP4LatticeProfile m :=
      Summable.tsum_le_tsum factorTwoP4RankTailTerm_le_latticeProfile
        hactual summable_factorTwoP4LatticeProfile
    _ ≤ _ := tsum_factorTwoP4LatticeProfile_le

private theorem factorTwoP5RankTail_le :
    (∑' m : ℕ,
      Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        centeredSinhMoment factorTwoCenteredP5
          (yoshidaEndpointA * oddRate (m + 1)) ^ 2) ≤
      (390625 / 544195584 : ℝ) + 1 / (55 * yoshidaEndpointA) := by
  have hactual :=
    (hasSum_factorTwoCenteredArch_oddRankSquares factorTwoCenteredP5
      continuous_factorTwoCenteredP5 odd_factorTwoCenteredP5).summable
  calc
    _ ≤ ∑' m : ℕ, factorTwoP5LatticeProfile m :=
      Summable.tsum_le_tsum factorTwoP5RankTailTerm_le_latticeProfile
        hactual summable_factorTwoP5LatticeProfile
    _ ≤ _ := tsum_factorTwoP5LatticeProfile_le

private theorem exp_two_mul_yoshidaEndpointA :
    Real.exp (2 * yoshidaEndpointA) = 2 := by
  unfold yoshidaEndpointA
  rw [show 2 * (Real.log 2 / 2) = Real.log 2 by ring]
  exact Real.exp_log (by norm_num)

private theorem factorTwoP4GrowingHead_le :
    Real.exp yoshidaEndpointA *
        centeredCoshMoment factorTwoCenteredP4 (yoshidaEndpointA / 2) ^ 2 ≤
      2 * (16384 / 9765625 : ℝ) := by
  have hweighted := exp_weighted_centeredCoshMoment_P4_sq_le_profile
    (yoshidaEndpointA / 2)
    (div_nonneg yoshidaEndpointA_pos.le (by norm_num))
  have hweighted' :
      Real.exp (-yoshidaEndpointA) *
          centeredCoshMoment factorTwoCenteredP4 (yoshidaEndpointA / 2) ^ 2 ≤
        factorTwoP4RankProfile (yoshidaEndpointA / 2) := by
    simpa only [show -2 * (yoshidaEndpointA / 2) =
      -yoshidaEndpointA by ring] using hweighted
  calc
    Real.exp yoshidaEndpointA *
        centeredCoshMoment factorTwoCenteredP4 (yoshidaEndpointA / 2) ^ 2 =
      2 * (Real.exp (-yoshidaEndpointA) *
        centeredCoshMoment factorTwoCenteredP4 (yoshidaEndpointA / 2) ^ 2) := by
      rw [← exp_two_mul_yoshidaEndpointA, ← mul_assoc, ← Real.exp_add]
      congr 1
      ring
    _ ≤ 2 * factorTwoP4RankProfile (yoshidaEndpointA / 2) :=
      mul_le_mul_of_nonneg_left hweighted' (by norm_num)
    _ ≤ 2 * (16384 / 9765625 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (factorTwoP4RankProfile_le_max _
          (div_nonneg yoshidaEndpointA_pos.le (by norm_num))) (by norm_num)

private theorem factorTwoP5GrowingHead_le :
    Real.exp yoshidaEndpointA *
        centeredSinhMoment factorTwoCenteredP5 (yoshidaEndpointA / 2) ^ 2 ≤
      2 * (390625 / 544195584 : ℝ) := by
  have hweighted := exp_weighted_centeredSinhMoment_P5_sq_le_profile
    (yoshidaEndpointA / 2)
    (div_nonneg yoshidaEndpointA_pos.le (by norm_num))
  have hweighted' :
      Real.exp (-yoshidaEndpointA) *
          centeredSinhMoment factorTwoCenteredP5 (yoshidaEndpointA / 2) ^ 2 ≤
        factorTwoP5RankProfile (yoshidaEndpointA / 2) := by
    simpa only [show -2 * (yoshidaEndpointA / 2) =
      -yoshidaEndpointA by ring] using hweighted
  calc
    Real.exp yoshidaEndpointA *
        centeredSinhMoment factorTwoCenteredP5 (yoshidaEndpointA / 2) ^ 2 =
      2 * (Real.exp (-yoshidaEndpointA) *
        centeredSinhMoment factorTwoCenteredP5 (yoshidaEndpointA / 2) ^ 2) := by
      rw [← exp_two_mul_yoshidaEndpointA, ← mul_assoc, ← Real.exp_add]
      congr 1
      ring
    _ ≤ 2 * factorTwoP5RankProfile (yoshidaEndpointA / 2) :=
      mul_le_mul_of_nonneg_left hweighted' (by norm_num)
    _ ≤ 2 * (390625 / 544195584 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (factorTwoP5RankProfile_le_max _
          (div_nonneg yoshidaEndpointA_pos.le (by norm_num))) (by norm_num)

/-- The complete even `P₄` rank family costs at most three twentieths of
its intrinsic mass.  The proof is uniform over all ranks. -/
theorem factorTwoEvenRankEnergy_P4_le_three_twentieths :
    factorTwoEvenRankEnergy factorTwoCenteredP4 ≤
      (3 / 20 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP4 := by
  have habs : factorTwoEvenRankEnergy factorTwoCenteredP4 ≤ (1 / 30 : ℝ) := by
    unfold factorTwoEvenRankEnergy
    calc
      _ ≤ yoshidaEndpointA *
          (2 * (16384 / 9765625 : ℝ) +
            ((16384 / 9765625 : ℝ) + 1 / (36 * yoshidaEndpointA))) :=
        mul_le_mul_of_nonneg_left
          (add_le_add factorTwoP4GrowingHead_le factorTwoP4RankTail_le)
          yoshidaEndpointA_pos.le
      _ = 1 / 36 + 3 * yoshidaEndpointA * (16384 / 9765625 : ℝ) := by
        field_simp [yoshidaEndpointA_pos.ne']
        ring
      _ ≤ 1 / 30 := by
        nlinarith [yoshidaEndpointA_le_seven_twentieths]
  unfold factorTwoIntrinsicEnergy
  rw [integral_factorTwoCenteredP4_sq]
  norm_num at habs ⊢
  exact habs

/-- The complete odd `P₅` rank family costs at most three twentieths of
its intrinsic mass.  The proof is uniform over all ranks. -/
theorem factorTwoOddRankEnergy_P5_le_three_twentieths :
    factorTwoOddRankEnergy factorTwoCenteredP5 ≤
      (3 / 20 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP5 := by
  have habs : factorTwoOddRankEnergy factorTwoCenteredP5 ≤ (3 / 110 : ℝ) := by
    unfold factorTwoOddRankEnergy
    calc
      _ ≤ yoshidaEndpointA *
          (2 * (390625 / 544195584 : ℝ) +
            ((390625 / 544195584 : ℝ) + 1 / (55 * yoshidaEndpointA))) :=
        mul_le_mul_of_nonneg_left
          (add_le_add factorTwoP5GrowingHead_le factorTwoP5RankTail_le)
          yoshidaEndpointA_pos.le
      _ = 1 / 55 + 3 * yoshidaEndpointA * (390625 / 544195584 : ℝ) := by
        field_simp [yoshidaEndpointA_pos.ne']
        ring
      _ ≤ 3 / 110 := by
        nlinarith [yoshidaEndpointA_le_seven_twentieths]
  unfold factorTwoIntrinsicEnergy
  rw [integral_factorTwoCenteredP5_sq]
  norm_num at habs ⊢
  exact habs

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveRankStructural
