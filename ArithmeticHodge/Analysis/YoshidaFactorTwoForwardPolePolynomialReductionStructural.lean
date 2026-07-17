import ArithmeticHodge.Analysis.ShiftedLogKernelRawPolynomial
import ArithmeticHodge.Analysis.ShiftedLogKernelTriangular
import ArithmeticHodge.Analysis.ShiftedLegendreLogEnergyOrthogonalProjection
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardHankelRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural
import Mathlib.Algebra.Polynomial.Eval.SMul

set_option autoImplicit false

open Finset MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoForwardPolePolynomialReductionStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreLogKernel
open ShiftedLogKernelRawPolynomial
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseP67ForwardHankelRepresenterStructural
open YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural

noncomputable section

/-!
# Polynomial reduction of the forward endpoint pole

In the unit coordinate `s = (x + 1) / 2`, each forward-Hankel half transform
of a transported polynomial is one logarithmic selector plus a polynomial of
no larger degree.  A Legendre moment gap therefore removes the correction
exactly, without enumerating any residual mode.
-/

/-! ## Coefficientwise correction operators -/

/-- Polynomial correction for the right forward transform of `X ^ k`. -/
def forwardPoleRightCorrectionMonomial (k : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range k,
    ((((k - j : ℕ) : ℝ))⁻¹) •
      ((Polynomial.X - Polynomial.C 1) ^ j *
        (Polynomial.C 1 - Polynomial.X ^ (k - j)))

/-- Polynomial correction for the left forward transform of `X ^ k`. -/
def forwardPoleLeftCorrectionMonomial (k : ℕ) : ℝ[X] :=
  -∑ j ∈ Finset.range k,
    ((((k - j : ℕ) : ℝ))⁻¹) •
      ((Polynomial.X + Polynomial.C 1) ^ j *
        Polynomial.X ^ (k - j))

def forwardPoleRightCorrectionMonomialLinear
    (k : ℕ) : ℝ →ₗ[ℝ] ℝ[X] where
  toFun c := c • forwardPoleRightCorrectionMonomial k
  map_add' a b := by rw [add_smul]
  map_smul' a b := by simp [smul_smul]

def forwardPoleLeftCorrectionMonomialLinear
    (k : ℕ) : ℝ →ₗ[ℝ] ℝ[X] where
  toFun c := c • forwardPoleLeftCorrectionMonomial k
  map_add' a b := by rw [add_smul]
  map_smul' a b := by simp [smul_smul]

/-- Right correction, extended coefficientwise to arbitrary polynomials. -/
def forwardPoleRightCorrection : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  Polynomial.lsum forwardPoleRightCorrectionMonomialLinear

/-- Left correction, extended coefficientwise to arbitrary polynomials. -/
def forwardPoleLeftCorrection : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  Polynomial.lsum forwardPoleLeftCorrectionMonomialLinear

/-! ## Exact primitive identities -/

theorem eval_forwardPoleRightCorrectionMonomial (k : ℕ) (s : ℝ) :
    (forwardPoleRightCorrectionMonomial k).eval s =
      ∫ r : ℝ in s..1, monomialDifferenceQuotient k (s - 1) r := by
  rw [integral_monomialDifferenceQuotient]
  unfold forwardPoleRightCorrectionMonomial
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    smul_eq_mul, one_pow, div_eq_mul_inv]
  ring

theorem eval_forwardPoleLeftCorrectionMonomial (k : ℕ) (s : ℝ) :
    (forwardPoleLeftCorrectionMonomial k).eval s =
      -(∫ r : ℝ in 0..s, monomialDifferenceQuotient k (s + 1) r) := by
  rw [integral_monomialDifferenceQuotient]
  unfold forwardPoleLeftCorrectionMonomial
  rw [Polynomial.eval_neg, Polynomial.eval_finset_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hpos : 0 < k - j :=
    Nat.sub_pos_of_lt (Finset.mem_range.mp hj)
  simp only [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    smul_eq_mul, div_eq_mul_inv, zero_pow hpos.ne']
  ring

theorem eval_forwardPoleRightCorrection (p : ℝ[X]) (s : ℝ) :
    (forwardPoleRightCorrection p).eval s =
      ∫ r : ℝ in s..1, polynomialDifferenceQuotient p (s - 1) r := by
  rw [forwardPoleRightCorrection, Polynomial.lsum_apply,
    Polynomial.eval_sum]
  unfold polynomialDifferenceQuotient
  simp only [Polynomial.sum_def]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k _hk
    rw [intervalIntegral.integral_const_mul]
    change (p.coeff k • forwardPoleRightCorrectionMonomial k).eval s =
      p.coeff k *
        ∫ r : ℝ in s..1, monomialDifferenceQuotient k (s - 1) r
    rw [Polynomial.eval_smul,
      eval_forwardPoleRightCorrectionMonomial]
    simp only [smul_eq_mul]
  · intro k _hk
    exact (continuous_const.mul
      (by
        unfold monomialDifferenceQuotient
        fun_prop)).intervalIntegrable s 1

theorem eval_forwardPoleLeftCorrection (p : ℝ[X]) (s : ℝ) :
    (forwardPoleLeftCorrection p).eval s =
      -(∫ r : ℝ in 0..s,
        polynomialDifferenceQuotient p (s + 1) r) := by
  rw [forwardPoleLeftCorrection, Polynomial.lsum_apply,
    Polynomial.eval_sum]
  unfold polynomialDifferenceQuotient
  simp only [Polynomial.sum_def]
  rw [intervalIntegral.integral_finset_sum]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [intervalIntegral.integral_const_mul]
    change (p.coeff k • forwardPoleLeftCorrectionMonomial k).eval s =
      -(p.coeff k *
        ∫ r : ℝ in 0..s, monomialDifferenceQuotient k (s + 1) r)
    rw [Polynomial.eval_smul,
      eval_forwardPoleLeftCorrectionMonomial]
    simp only [smul_eq_mul]
    ring
  · intro k _hk
    exact (continuous_const.mul
      (by
        unfold monomialDifferenceQuotient
        fun_prop)).intervalIntegrable 0 s

/-! ## Affine reciprocal primitives -/

private theorem integral_one_div_one_add_right
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ r : ℝ in s..1, 1 / (1 + r - s)) = Real.log (2 - s) := by
  have hcomp := intervalIntegral.integral_comp_add_left
    (f := fun z : ℝ ↦ 1 / z) (a := s) (b := 1) (1 - s)
  have hpos := integral_one_div_of_pos
    (by norm_num : (0 : ℝ) < 1) (by linarith [hs.2] : 0 < 2 - s)
  calc
    (∫ r : ℝ in s..1, 1 / (1 + r - s)) =
        ∫ z : ℝ in 1..2 - s, 1 / z := by
      rw [show 1 - s + s = 1 by ring,
        show 1 - s + 1 = 2 - s by ring] at hcomp
      rw [show (fun r : ℝ ↦ 1 / (1 + r - s)) =
          fun r : ℝ ↦ 1 / (1 - s + r) by
        funext r
        congr 1
        ring]
      exact hcomp
    _ = Real.log ((2 - s) / 1) := hpos
    _ = Real.log (2 - s) := by rw [div_one]

private theorem integral_one_div_one_add_left
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ r : ℝ in 0..s, 1 / (1 + s - r)) = Real.log (1 + s) := by
  have hcomp := intervalIntegral.integral_comp_sub_left
    (f := fun z : ℝ ↦ 1 / z) (a := (0 : ℝ)) (b := s) (1 + s)
  have hpos := integral_one_div_of_pos
    (by norm_num : (0 : ℝ) < 1) (by linarith [hs.1] : 0 < 1 + s)
  calc
    (∫ r : ℝ in 0..s, 1 / (1 + s - r)) =
        ∫ z : ℝ in 1..1 + s, 1 / z := by
      rw [show 1 + s - s = 1 by ring,
        show 1 + s - 0 = 1 + s by ring] at hcomp
      exact hcomp
    _ = Real.log ((1 + s) / 1) := hpos
    _ = Real.log (1 + s) := by rw [div_one]

private theorem integral_centeredPolynomialLift_forward_right_unit
    (p : ℝ[X]) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ y : ℝ in 2 * s - 1..1,
      centeredPolynomialLift p y / (2 + y - (2 * s - 1))) =
      ∫ r : ℝ in s..1, p.eval r / (1 + r - s) := by
  let f : ℝ → ℝ := fun y ↦
    centeredPolynomialLift p y / (2 + y - (2 * s - 1))
  have hsubst := intervalIntegral.smul_integral_comp_mul_add
    (a := s) (b := 1) f (2 : ℝ) (-1)
  have hsubst' :
      (2 : ℝ) * (∫ r : ℝ in s..1, f (2 * r - 1)) =
        ∫ y : ℝ in 2 * s - 1..1, f y := by
    rw [show (2 : ℝ) * 1 + -1 = 1 by norm_num] at hsubst
    simpa only [smul_eq_mul, sub_eq_add_neg] using hsubst
  change (∫ y : ℝ in 2 * s - 1..1, f y) = _
  rw [← hsubst', ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc s 1 := by
    simpa only [uIcc_of_le hs.2] using hr
  have hden : 1 + r - s ≠ 0 := by
    have : 0 < 1 + r - s := by linarith [hr'.1]
    exact this.ne'
  dsimp only [f, centeredPolynomialLift]
  rw [show ((2 * r - 1) + 1) / 2 = r by ring,
    show 2 + (2 * r - 1) - (2 * s - 1) =
      2 * (1 + r - s) by ring]
  field_simp [hden]

private theorem integral_centeredPolynomialLift_forward_left_unit
    (p : ℝ[X]) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ y : ℝ in -1..2 * s - 1,
      centeredPolynomialLift p y / (2 + (2 * s - 1) - y)) =
      ∫ r : ℝ in 0..s, p.eval r / (1 + s - r) := by
  let f : ℝ → ℝ := fun y ↦
    centeredPolynomialLift p y / (2 + (2 * s - 1) - y)
  have hsubst := intervalIntegral.smul_integral_comp_mul_add
    (a := (0 : ℝ)) (b := s) f (2 : ℝ) (-1)
  have hsubst' :
      (2 : ℝ) * (∫ r : ℝ in 0..s, f (2 * r - 1)) =
        ∫ y : ℝ in -1..2 * s - 1, f y := by
    rw [show (2 : ℝ) * 0 + -1 = -1 by norm_num] at hsubst
    simpa only [smul_eq_mul, sub_eq_add_neg] using hsubst
  change (∫ y : ℝ in -1..2 * s - 1, f y) = _
  rw [← hsubst', ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc (0 : ℝ) s := by
    simpa only [uIcc_of_le hs.1] using hr
  have hden : 1 + s - r ≠ 0 := by
    have : 0 < 1 + s - r := by linarith [hr'.2]
    exact this.ne'
  dsimp only [f, centeredPolynomialLift]
  rw [show ((2 * r - 1) + 1) / 2 = r by ring,
    show 2 + (2 * s - 1) - (2 * r - 1) =
      2 * (1 + s - r) by ring]
  field_simp [hden]

private theorem polynomial_div_forward_right_eq
    (p : ℝ[X]) {s r : ℝ} (hden : 1 + r - s ≠ 0) :
    p.eval r / (1 + r - s) =
      polynomialDifferenceQuotient p (s - 1) r +
        p.eval (s - 1) * (1 / (1 + r - s)) := by
  have hq := sub_mul_polynomialDifferenceQuotient p (s - 1) r
  field_simp [hden]
  nlinarith [hq]

private theorem polynomial_div_forward_left_eq
    (p : ℝ[X]) {s r : ℝ} (hden : 1 + s - r ≠ 0) :
    p.eval r / (1 + s - r) =
      p.eval (s + 1) * (1 / (1 + s - r)) -
        polynomialDifferenceQuotient p (s + 1) r := by
  have hq := sub_mul_polynomialDifferenceQuotient p (s + 1) r
  field_simp [hden]
  nlinarith [hq]

private theorem intervalIntegrable_one_div_one_add_right
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun r : ℝ ↦ 1 / (1 + r - s)) volume s 1 := by
  apply ContinuousOn.intervalIntegrable
  intro r hr
  have hr' : r ∈ Icc s 1 := by
    simpa only [uIcc_of_le hs.2] using hr
  have hden : 1 + r - s ≠ 0 := by
    have : 0 < 1 + r - s := by linarith [hr'.1]
    exact this.ne'
  exact (continuousAt_const.div
    ((continuousAt_const.add continuousAt_id).sub continuousAt_const) hden)
      |>.continuousWithinAt

private theorem intervalIntegrable_one_div_one_add_left
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun r : ℝ ↦ 1 / (1 + s - r)) volume 0 s := by
  apply ContinuousOn.intervalIntegrable
  intro r hr
  have hr' : r ∈ Icc (0 : ℝ) s := by
    simpa only [uIcc_of_le hs.1] using hr
  have hden : 1 + s - r ≠ 0 := by
    have : 0 < 1 + s - r := by linarith [hr'.2]
    exact this.ne'
  exact (continuousAt_const.div
    ((continuousAt_const.add continuousAt_const).sub continuousAt_id) hden)
      |>.continuousWithinAt

/-! ## Endpoint-safe pointwise reductions -/

/-- On the full unit interval, the right forward transform is one logarithmic
selector plus a polynomial correction of no larger degree. -/
theorem forwardPoleRight_centeredPolynomialLift_unit
    (p : ℝ[X]) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    factorTwoForwardHankelRightRepresenter
        (centeredPolynomialLift p) (2 * s - 1) =
      p.eval (s - 1) * Real.log (2 - s) +
        (forwardPoleRightCorrection p).eval s := by
  have hx : 2 * s - 1 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hs.1, hs.2]
  rw [factorTwoForwardHankelRightRepresenter_eq _ hx,
    integral_centeredPolynomialLift_forward_right_unit p hs]
  have hinv := intervalIntegrable_one_div_one_add_right hs
  have hdiff : IntervalIntegrable
      (fun r : ℝ ↦ polynomialDifferenceQuotient p (s - 1) r)
      volume s 1 :=
    (continuous_polynomialDifferenceQuotient p (s - 1)).intervalIntegrable s 1
  have hrewrite :
      (∫ r : ℝ in s..1, p.eval r / (1 + r - s)) =
        ∫ r : ℝ in s..1,
          polynomialDifferenceQuotient p (s - 1) r +
            p.eval (s - 1) * (1 / (1 + r - s)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc s 1 := by
      simpa only [uIcc_of_le hs.2] using hr
    apply polynomial_div_forward_right_eq
    have : 0 < 1 + r - s := by linarith [hr'.1]
    exact this.ne'
  rw [hrewrite,
    intervalIntegral.integral_add hdiff
      (hinv.const_mul (p.eval (s - 1))),
    intervalIntegral.integral_const_mul,
    integral_one_div_one_add_right hs,
    eval_forwardPoleRightCorrection]
  ring

/-- On the full unit interval, the left forward transform is one logarithmic
selector plus a polynomial correction of no larger degree. -/
theorem forwardPoleLeft_centeredPolynomialLift_unit
    (p : ℝ[X]) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    factorTwoForwardHankelLeftRepresenter
        (centeredPolynomialLift p) (2 * s - 1) =
      p.eval (s + 1) * Real.log (1 + s) +
        (forwardPoleLeftCorrection p).eval s := by
  have hx : 2 * s - 1 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hs.1, hs.2]
  rw [factorTwoForwardHankelLeftRepresenter_eq _ hx,
    integral_centeredPolynomialLift_forward_left_unit p hs]
  have hinv := intervalIntegrable_one_div_one_add_left hs
  have hdiff : IntervalIntegrable
      (fun r : ℝ ↦ polynomialDifferenceQuotient p (s + 1) r)
      volume 0 s :=
    (continuous_polynomialDifferenceQuotient p (s + 1)).intervalIntegrable 0 s
  have hrewrite :
      (∫ r : ℝ in 0..s, p.eval r / (1 + s - r)) =
        ∫ r : ℝ in 0..s,
          p.eval (s + 1) * (1 / (1 + s - r)) -
            polynomialDifferenceQuotient p (s + 1) r := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) s := by
      simpa only [uIcc_of_le hs.1] using hr
    apply polynomial_div_forward_left_eq
    have : 0 < 1 + s - r := by linarith [hr'.2]
    exact this.ne'
  rw [hrewrite,
    intervalIntegral.integral_sub
      (hinv.const_mul (p.eval (s + 1))) hdiff,
    intervalIntegral.integral_const_mul,
    integral_one_div_one_add_left hs,
    eval_forwardPoleLeftCorrection]
  ring

theorem forwardPoleRight_centeredPolynomialLift
    (p : ℝ[X]) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelRightRepresenter (centeredPolynomialLift p) x =
      p.eval ((x - 1) / 2) * Real.log ((3 - x) / 2) +
        centeredPolynomialLift (forwardPoleRightCorrection p) x := by
  have hs : (x + 1) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  change factorTwoForwardHankelRightRepresenter
      (centeredPolynomialLift p) x =
    p.eval ((x - 1) / 2) * Real.log ((3 - x) / 2) +
      (forwardPoleRightCorrection p).eval ((x + 1) / 2)
  have h := forwardPoleRight_centeredPolynomialLift_unit p hs
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring,
    show (x + 1) / 2 - 1 = (x - 1) / 2 by ring,
    show 2 - (x + 1) / 2 = (3 - x) / 2 by ring] at h
  exact h

theorem forwardPoleLeft_centeredPolynomialLift
    (p : ℝ[X]) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelLeftRepresenter (centeredPolynomialLift p) x =
      p.eval ((x + 3) / 2) * Real.log ((3 + x) / 2) +
        centeredPolynomialLift (forwardPoleLeftCorrection p) x := by
  have hs : (x + 1) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  change factorTwoForwardHankelLeftRepresenter
      (centeredPolynomialLift p) x =
    p.eval ((x + 3) / 2) * Real.log ((3 + x) / 2) +
      (forwardPoleLeftCorrection p).eval ((x + 1) / 2)
  have h := forwardPoleLeft_centeredPolynomialLift_unit p hs
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring,
    show (x + 1) / 2 + 1 = (x + 3) / 2 by ring,
    show 1 + (x + 1) / 2 = (3 + x) / 2 by ring] at h
  exact h

/-- Polynomial remainder in the symmetric forward representer. -/
def forwardPoleKCorrection (p : ℝ[X]) : ℝ[X] :=
  forwardPoleRightCorrection p + forwardPoleLeftCorrection p

/-- Polynomial remainder in the alternating forward representer. -/
def forwardPoleLCorrection (p : ℝ[X]) : ℝ[X] :=
  forwardPoleRightCorrection p - forwardPoleLeftCorrection p

/-- The two logarithmic selectors surviving in the symmetric channel. -/
def forwardPoleKLogSelector (p : ℝ[X]) (x : ℝ) : ℝ :=
  p.eval ((x - 1) / 2) * Real.log ((3 - x) / 2) +
    p.eval ((x + 3) / 2) * Real.log ((3 + x) / 2)

/-- The logarithmic selectors surviving in the alternating channel. -/
def forwardPoleLLogSelector (p : ℝ[X]) (x : ℝ) : ℝ :=
  p.eval ((x - 1) / 2) * Real.log ((3 - x) / 2) -
    p.eval ((x + 3) / 2) * Real.log ((3 + x) / 2)

theorem forwardPoleK_centeredPolynomialLift
    (p : ℝ[X]) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelK (centeredPolynomialLift p) x =
      forwardPoleKLogSelector p x +
        centeredPolynomialLift (forwardPoleKCorrection p) x := by
  unfold factorTwoForwardHankelK forwardPoleKCorrection
    forwardPoleKLogSelector
  rw [forwardPoleRight_centeredPolynomialLift p hx,
    forwardPoleLeft_centeredPolynomialLift p hx]
  unfold centeredPolynomialLift
  rw [Polynomial.eval_add]
  ring

theorem forwardPoleL_centeredPolynomialLift
    (p : ℝ[X]) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelL (centeredPolynomialLift p) x =
      forwardPoleLLogSelector p x +
        centeredPolynomialLift (forwardPoleLCorrection p) x := by
  unfold factorTwoForwardHankelL forwardPoleLCorrection
    forwardPoleLLogSelector
  rw [forwardPoleRight_centeredPolynomialLift p hx,
    forwardPoleLeft_centeredPolynomialLift p hx]
  unfold centeredPolynomialLift
  rw [Polynomial.eval_sub]
  ring

/-! ## Degree filtration -/

theorem natDegree_forwardPoleRightCorrectionMonomial_le (k : ℕ) :
    (forwardPoleRightCorrectionMonomial k).natDegree ≤ k := by
  unfold forwardPoleRightCorrectionMonomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hjk : j ≤ k := (Finset.mem_range.mp hj).le
  apply (Polynomial.natDegree_smul_le _ _).trans
  refine (Polynomial.natDegree_mul_le_of_le
    (m := j) (n := k - j) ?_ ?_).trans ?_
  · calc
      ((Polynomial.X - Polynomial.C (1 : ℝ)) ^ j).natDegree ≤
          j * (Polynomial.X - Polynomial.C (1 : ℝ)).natDegree :=
        Polynomial.natDegree_pow_le
      _ = j := by rw [Polynomial.natDegree_X_sub_C, mul_one]
  · exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  · omega

theorem natDegree_forwardPoleLeftCorrectionMonomial_le (k : ℕ) :
    (forwardPoleLeftCorrectionMonomial k).natDegree ≤ k := by
  unfold forwardPoleLeftCorrectionMonomial
  rw [Polynomial.natDegree_neg]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hjk : j ≤ k := (Finset.mem_range.mp hj).le
  apply (Polynomial.natDegree_smul_le _ _).trans
  refine (Polynomial.natDegree_mul_le_of_le
    (m := j) (n := k - j) ?_ ?_).trans ?_
  · calc
      ((Polynomial.X + Polynomial.C (1 : ℝ)) ^ j).natDegree ≤
          j * (Polynomial.X + Polynomial.C (1 : ℝ)).natDegree :=
        Polynomial.natDegree_pow_le
      _ = j := by rw [Polynomial.natDegree_X_add_C, mul_one]
  · simp
  · omega

/-- The right correction preserves every polynomial degree filtration. -/
theorem natDegree_forwardPoleRightCorrection_le (p : ℝ[X]) :
    (forwardPoleRightCorrection p).natDegree ≤ p.natDegree := by
  unfold forwardPoleRightCorrection
  rw [Polynomial.lsum_apply, Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  dsimp only [forwardPoleRightCorrectionMonomialLinear]
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((natDegree_forwardPoleRightCorrectionMonomial_le k).trans
      (Polynomial.le_natDegree_of_mem_supp k hk))

/-- The left correction preserves every polynomial degree filtration. -/
theorem natDegree_forwardPoleLeftCorrection_le (p : ℝ[X]) :
    (forwardPoleLeftCorrection p).natDegree ≤ p.natDegree := by
  unfold forwardPoleLeftCorrection
  rw [Polynomial.lsum_apply, Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  dsimp only [forwardPoleLeftCorrectionMonomialLinear]
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((natDegree_forwardPoleLeftCorrectionMonomial_le k).trans
      (Polynomial.le_natDegree_of_mem_supp k hk))

theorem natDegree_forwardPoleKCorrection_le (p : ℝ[X]) :
    (forwardPoleKCorrection p).natDegree ≤ p.natDegree := by
  unfold forwardPoleKCorrection
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (natDegree_forwardPoleRightCorrection_le p)
      (natDegree_forwardPoleLeftCorrection_le p))

theorem natDegree_forwardPoleLCorrection_le (p : ℝ[X]) :
    (forwardPoleLCorrection p).natDegree ≤ p.natDegree := by
  unfold forwardPoleLCorrection
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le (natDegree_forwardPoleRightCorrection_le p)
      (natDegree_forwardPoleLeftCorrection_le p))

theorem natDegree_forwardPoleKCorrection_lt_eleven
    (p : ℝ[X]) (hp : p.natDegree < 11) :
    (forwardPoleKCorrection p).natDegree < 11 :=
  (natDegree_forwardPoleKCorrection_le p).trans_lt hp

theorem natDegree_forwardPoleLCorrection_lt_eleven
    (p : ℝ[X]) (hp : p.natDegree < 11) :
    (forwardPoleLCorrection p).natDegree < 11 :=
  (natDegree_forwardPoleLCorrection_le p).trans_lt hp

theorem degree_forwardPoleRightCorrection_le (p : ℝ[X]) :
    (forwardPoleRightCorrection p).degree ≤ p.degree := by
  by_cases hp : p = 0
  · simp [hp]
  rw [Polynomial.degree_eq_natDegree hp]
  exact Polynomial.degree_le_of_natDegree_le
    (natDegree_forwardPoleRightCorrection_le p)

theorem degree_forwardPoleLeftCorrection_le (p : ℝ[X]) :
    (forwardPoleLeftCorrection p).degree ≤ p.degree := by
  by_cases hp : p = 0
  · simp [hp]
  rw [Polynomial.degree_eq_natDegree hp]
  exact Polynomial.degree_le_of_natDegree_le
    (natDegree_forwardPoleLeftCorrection_le p)

/-! ## Exact moment-gap elimination -/

theorem intervalIntegral_mul_forwardPoleKCorrection_eq_zero
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) {k : ℕ}
    (hlow : centeredLegendreMomentsVanishBelow r k)
    (hp : p.natDegree < k) :
    (∫ x : ℝ in -1..1,
      r x * centeredPolynomialLift (forwardPoleKCorrection p) x) = 0 := by
  unfold centeredPolynomialLift
  exact intervalIntegral_mul_shiftedPolynomial_eq_zero r hr hlow _
    ((natDegree_forwardPoleKCorrection_le p).trans_lt hp)

theorem intervalIntegral_mul_forwardPoleLCorrection_eq_zero
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) {k : ℕ}
    (hlow : centeredLegendreMomentsVanishBelow r k)
    (hp : p.natDegree < k) :
    (∫ x : ℝ in -1..1,
      r x * centeredPolynomialLift (forwardPoleLCorrection p) x) = 0 := by
  unfold centeredPolynomialLift
  exact intervalIntegral_mul_shiftedPolynomial_eq_zero r hr hlow _
    ((natDegree_forwardPoleLCorrection_le p).trans_lt hp)

/-- After a moment gap above `p`, the complete symmetric forward pairing
depends only on the two nonsingular logarithmic selectors. -/
theorem integral_mul_forwardPoleK_centeredPolynomialLift_eq_logSelector
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) {k : ℕ}
    (hlow : centeredLegendreMomentsVanishBelow r k)
    (hp : p.natDegree < k) :
    (∫ x : ℝ in -1..1,
      r x * factorTwoForwardHankelK (centeredPolynomialLift p) x) =
        ∫ x : ℝ in -1..1, r x * forwardPoleKLogSelector p x := by
  have hpcont : Continuous (centeredPolynomialLift p) := by
    unfold centeredPolynomialLift
    fun_prop
  have hfull : IntervalIntegrable
      (fun x : ℝ ↦
        r x * factorTwoForwardHankelK (centeredPolynomialLift p) x)
      volume (-1) 1 :=
    (hr.mul (continuous_factorTwoForwardHankelK
      (centeredPolynomialLift p) hpcont)).intervalIntegrable (-1) 1
  have hpolyCont : Continuous
      (centeredPolynomialLift (forwardPoleKCorrection p)) := by
    unfold centeredPolynomialLift
    fun_prop
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦
        r x * centeredPolynomialLift (forwardPoleKCorrection p) x)
      volume (-1) 1 :=
    (hr.mul hpolyCont).intervalIntegrable (-1) 1
  have hzero := intervalIntegral_mul_forwardPoleKCorrection_eq_zero
    p r hr hlow hp
  symm
  calc
    (∫ x : ℝ in -1..1, r x * forwardPoleKLogSelector p x) =
        ∫ x : ℝ in -1..1,
          r x * factorTwoForwardHankelK (centeredPolynomialLift p) x -
            r x * centeredPolynomialLift (forwardPoleKCorrection p) x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      change r x * forwardPoleKLogSelector p x =
        r x * factorTwoForwardHankelK (centeredPolynomialLift p) x -
          r x * centeredPolynomialLift (forwardPoleKCorrection p) x
      rw [forwardPoleK_centeredPolynomialLift p hx]
      ring
    _ = (∫ x : ℝ in -1..1,
          r x * factorTwoForwardHankelK (centeredPolynomialLift p) x) -
        ∫ x : ℝ in -1..1,
          r x * centeredPolynomialLift (forwardPoleKCorrection p) x :=
      intervalIntegral.integral_sub hfull hpoly
    _ = ∫ x : ℝ in -1..1,
        r x * factorTwoForwardHankelK (centeredPolynomialLift p) x := by
      rw [hzero, sub_zero]

/-- After the same moment gap, the alternating forward pairing depends only
on the signed logarithmic selector pair. -/
theorem integral_mul_forwardPoleL_centeredPolynomialLift_eq_logSelector
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) {k : ℕ}
    (hlow : centeredLegendreMomentsVanishBelow r k)
    (hp : p.natDegree < k) :
    (∫ x : ℝ in -1..1,
      r x * factorTwoForwardHankelL (centeredPolynomialLift p) x) =
        ∫ x : ℝ in -1..1, r x * forwardPoleLLogSelector p x := by
  have hpcont : Continuous (centeredPolynomialLift p) := by
    unfold centeredPolynomialLift
    fun_prop
  have hfull : IntervalIntegrable
      (fun x : ℝ ↦
        r x * factorTwoForwardHankelL (centeredPolynomialLift p) x)
      volume (-1) 1 :=
    (hr.mul (continuous_factorTwoForwardHankelL
      (centeredPolynomialLift p) hpcont)).intervalIntegrable (-1) 1
  have hpolyCont : Continuous
      (centeredPolynomialLift (forwardPoleLCorrection p)) := by
    unfold centeredPolynomialLift
    fun_prop
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦
        r x * centeredPolynomialLift (forwardPoleLCorrection p) x)
      volume (-1) 1 :=
    (hr.mul hpolyCont).intervalIntegrable (-1) 1
  have hzero := intervalIntegral_mul_forwardPoleLCorrection_eq_zero
    p r hr hlow hp
  symm
  calc
    (∫ x : ℝ in -1..1, r x * forwardPoleLLogSelector p x) =
        ∫ x : ℝ in -1..1,
          r x * factorTwoForwardHankelL (centeredPolynomialLift p) x -
            r x * centeredPolynomialLift (forwardPoleLCorrection p) x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      change r x * forwardPoleLLogSelector p x =
        r x * factorTwoForwardHankelL (centeredPolynomialLift p) x -
          r x * centeredPolynomialLift (forwardPoleLCorrection p) x
      rw [forwardPoleL_centeredPolynomialLift p hx]
      ring
    _ = (∫ x : ℝ in -1..1,
          r x * factorTwoForwardHankelL (centeredPolynomialLift p) x) -
        ∫ x : ℝ in -1..1,
          r x * centeredPolynomialLift (forwardPoleLCorrection p) x :=
      intervalIntegral.integral_sub hfull hpoly
    _ = ∫ x : ℝ in -1..1,
        r x * factorTwoForwardHankelL (centeredPolynomialLift p) x := by
      rw [hzero, sub_zero]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoForwardPolePolynomialReductionStructural
