import ArithmeticHodge.Analysis.ShiftedLogKernelRawPolynomial
import ArithmeticHodge.Analysis.ShiftedLogKernelTriangular
import ArithmeticHodge.Analysis.ShiftedLegendreLogEnergyOrthogonalProjection
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoReflectedPoleRepresenterStructural
import Mathlib.Algebra.Polynomial.Eval.SMul

set_option autoImplicit false

open Finset MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoReflectedPolePolynomialReductionStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreLogKernel
open ShiftedLogKernelRawPolynomial
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural
open YoshidaFactorTwoReflectedPoleRepresenterStructural

noncomputable section

/-!
# Polynomial reduction of the reflected endpoint pole

In the unit coordinate `s = (x + 1) / 2`, each reflected-pole half transform
of a transported polynomial is one explicit logarithmic selector plus a
polynomial of no larger degree.  Consequently every correction below a
Legendre moment gap disappears exactly; no residual mode is enumerated.
-/

/-! ## Coefficientwise correction operators -/

/-- Polynomial correction for the right reflected-pole transform of `X ^ k`. -/
def reflectedPoleRightCorrectionMonomial (k : ℕ) : ℝ[X] :=
  -∑ j ∈ Finset.range k,
    ((((k - j : ℕ) : ℝ))⁻¹) •
      ((Polynomial.X + Polynomial.C 1) ^ j *
        (Polynomial.C 1 - Polynomial.X ^ (k - j)))

/-- Polynomial correction for the left reflected-pole transform of `X ^ k`. -/
def reflectedPoleLeftCorrectionMonomial (k : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range k,
    ((((k - j : ℕ) : ℝ))⁻¹) •
      ((Polynomial.X - Polynomial.C 1) ^ j *
        Polynomial.X ^ (k - j))

def reflectedPoleRightCorrectionMonomialLinear
    (k : ℕ) : ℝ →ₗ[ℝ] ℝ[X] where
  toFun c := c • reflectedPoleRightCorrectionMonomial k
  map_add' a b := by rw [add_smul]
  map_smul' a b := by simp [smul_smul]

def reflectedPoleLeftCorrectionMonomialLinear
    (k : ℕ) : ℝ →ₗ[ℝ] ℝ[X] where
  toFun c := c • reflectedPoleLeftCorrectionMonomial k
  map_add' a b := by rw [add_smul]
  map_smul' a b := by simp [smul_smul]

/-- Right correction, extended coefficientwise to arbitrary polynomials. -/
def reflectedPoleRightCorrection : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  Polynomial.lsum reflectedPoleRightCorrectionMonomialLinear

/-- Left correction, extended coefficientwise to arbitrary polynomials. -/
def reflectedPoleLeftCorrection : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  Polynomial.lsum reflectedPoleLeftCorrectionMonomialLinear

/-! ## Exact primitive identities -/

theorem eval_reflectedPoleRightCorrectionMonomial (k : ℕ) (s : ℝ) :
    (reflectedPoleRightCorrectionMonomial k).eval s =
      -(∫ r : ℝ in s..1, monomialDifferenceQuotient k (1 + s) r) := by
  rw [integral_monomialDifferenceQuotient]
  unfold reflectedPoleRightCorrectionMonomial
  rw [Polynomial.eval_neg, Polynomial.eval_finset_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, smul_eq_mul, one_pow, div_eq_mul_inv]
  ring

theorem eval_reflectedPoleLeftCorrectionMonomial (k : ℕ) (s : ℝ) :
    (reflectedPoleLeftCorrectionMonomial k).eval s =
      ∫ r : ℝ in 0..s, monomialDifferenceQuotient k (s - 1) r := by
  rw [integral_monomialDifferenceQuotient]
  unfold reflectedPoleLeftCorrectionMonomial
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hpos : 0 < k - j :=
    Nat.sub_pos_of_lt (Finset.mem_range.mp hj)
  simp only [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, smul_eq_mul, div_eq_mul_inv,
    zero_pow hpos.ne']
  ring

theorem eval_reflectedPoleRightCorrection (p : ℝ[X]) (s : ℝ) :
    (reflectedPoleRightCorrection p).eval s =
      -(∫ r : ℝ in s..1, polynomialDifferenceQuotient p (1 + s) r) := by
  rw [reflectedPoleRightCorrection, Polynomial.lsum_apply,
    Polynomial.eval_sum]
  unfold polynomialDifferenceQuotient
  simp only [Polynomial.sum_def]
  rw [intervalIntegral.integral_finset_sum]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [intervalIntegral.integral_const_mul]
    change (p.coeff k • reflectedPoleRightCorrectionMonomial k).eval s =
      -(p.coeff k *
        ∫ r : ℝ in s..1, monomialDifferenceQuotient k (1 + s) r)
    rw [Polynomial.eval_smul,
      eval_reflectedPoleRightCorrectionMonomial]
    simp only [smul_eq_mul]
    ring
  · intro k _hk
    exact (continuous_const.mul
      (by
        unfold monomialDifferenceQuotient
        fun_prop)).intervalIntegrable s 1

theorem eval_reflectedPoleLeftCorrection (p : ℝ[X]) (s : ℝ) :
    (reflectedPoleLeftCorrection p).eval s =
      ∫ r : ℝ in 0..s, polynomialDifferenceQuotient p (s - 1) r := by
  rw [reflectedPoleLeftCorrection, Polynomial.lsum_apply,
    Polynomial.eval_sum]
  unfold polynomialDifferenceQuotient
  simp only [Polynomial.sum_def]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k _hk
    rw [intervalIntegral.integral_const_mul]
    change (p.coeff k • reflectedPoleLeftCorrectionMonomial k).eval s =
      p.coeff k *
        ∫ r : ℝ in 0..s, monomialDifferenceQuotient k (s - 1) r
    rw [Polynomial.eval_smul,
      eval_reflectedPoleLeftCorrectionMonomial]
    simp only [smul_eq_mul]
  · intro k _hk
    exact (continuous_const.mul
      (by
        unfold monomialDifferenceQuotient
        fun_prop)).intervalIntegrable 0 s

/-! ## Affine reciprocal primitives -/

private theorem integral_one_div_one_add_sub
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    (∫ r : ℝ in s..1, 1 / (1 + s - r)) = -Real.log s := by
  have hcomp := intervalIntegral.integral_comp_sub_left
    (f := fun z : ℝ ↦ 1 / z) (a := s) (b := 1) (1 + s)
  have hpos := integral_one_div_of_pos hs.1
    (by norm_num : (0 : ℝ) < 1)
  calc
    (∫ r : ℝ in s..1, 1 / (1 + s - r)) =
        ∫ z : ℝ in s..1, 1 / z := by
      rw [show 1 + s - 1 = s by ring,
        show 1 + s - s = 1 by ring] at hcomp
      exact hcomp
    _ = Real.log (1 / s) := hpos
    _ = -Real.log s := by
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hs.1.ne']
      simp

private theorem integral_one_div_one_sub_add
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    (∫ r : ℝ in 0..s, 1 / (1 - s + r)) =
      -Real.log (1 - s) := by
  have hcomp := intervalIntegral.integral_comp_add_left
    (f := fun z : ℝ ↦ 1 / z) (a := (0 : ℝ)) (b := s) (1 - s)
  have hpos := integral_one_div_of_pos
    (sub_pos.mpr hs.2) (by norm_num : (0 : ℝ) < 1)
  calc
    (∫ r : ℝ in 0..s, 1 / (1 - s + r)) =
        ∫ z : ℝ in 1 - s..1, 1 / z := by
      rw [show 1 - s + 0 = 1 - s by ring,
        show 1 - s + s = 1 by ring] at hcomp
      exact hcomp
    _ = Real.log (1 / (1 - s)) := hpos
    _ = -Real.log (1 - s) := by
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
        (sub_pos.mpr hs.2).ne']
      simp

private theorem integral_centeredPolynomialLift_reflected_right_unit
    (p : ℝ[X]) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    (∫ y : ℝ in 2 * s - 1..1,
      centeredPolynomialLift p y / (2 - y + (2 * s - 1))) =
      ∫ r : ℝ in s..1, p.eval r / (1 + s - r) := by
  let f : ℝ → ℝ := fun y ↦
    centeredPolynomialLift p y / (2 - y + (2 * s - 1))
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
  have hden : 1 + s - r ≠ 0 := by
    have : 0 < 1 + s - r := by linarith [hs.1, hr'.2]
    exact this.ne'
  dsimp only [f, centeredPolynomialLift]
  rw [show ((2 * r - 1) + 1) / 2 = r by ring,
    show 2 - (2 * r - 1) + (2 * s - 1) =
      2 * (1 + s - r) by ring]
  field_simp [hden]

private theorem integral_centeredPolynomialLift_reflected_left_unit
    (p : ℝ[X]) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    (∫ y : ℝ in -1..2 * s - 1,
      centeredPolynomialLift p y / (2 - (2 * s - 1) + y)) =
      ∫ r : ℝ in 0..s, p.eval r / (1 - s + r) := by
  let f : ℝ → ℝ := fun y ↦
    centeredPolynomialLift p y / (2 - (2 * s - 1) + y)
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
  have hden : 1 - s + r ≠ 0 := by
    have : 0 < 1 - s + r := by linarith [hs.2, hr'.1]
    exact this.ne'
  dsimp only [f, centeredPolynomialLift]
  rw [show ((2 * r - 1) + 1) / 2 = r by ring,
    show 2 - (2 * s - 1) + (2 * r - 1) =
      2 * (1 - s + r) by ring]
  field_simp [hden]

private theorem polynomial_div_reflected_right_eq
    (p : ℝ[X]) {s r : ℝ} (hden : 1 + s - r ≠ 0) :
    p.eval r / (1 + s - r) =
      p.eval (1 + s) * (1 / (1 + s - r)) -
        polynomialDifferenceQuotient p (1 + s) r := by
  have hq := sub_mul_polynomialDifferenceQuotient p (1 + s) r
  field_simp [hden]
  nlinarith [hq]

private theorem polynomial_div_reflected_left_eq
    (p : ℝ[X]) {s r : ℝ} (hden : 1 - s + r ≠ 0) :
    p.eval r / (1 - s + r) =
      p.eval (s - 1) * (1 / (1 - s + r)) +
        polynomialDifferenceQuotient p (s - 1) r := by
  have hq := sub_mul_polynomialDifferenceQuotient p (s - 1) r
  field_simp [hden]
  nlinarith [hq]

private theorem intervalIntegrable_one_div_one_add_sub
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    IntervalIntegrable (fun r : ℝ ↦ 1 / (1 + s - r)) volume s 1 := by
  apply ContinuousOn.intervalIntegrable
  intro r hr
  have hr' : r ∈ Icc s 1 := by
    simpa only [uIcc_of_le hs.2] using hr
  have hden : 1 + s - r ≠ 0 := by
    have : 0 < 1 + s - r := by linarith [hs.1, hr'.2]
    exact this.ne'
  exact (continuousAt_const.div
    ((continuousAt_const.add continuousAt_const).sub continuousAt_id) hden)
      |>.continuousWithinAt

private theorem intervalIntegrable_one_div_one_sub_add
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    IntervalIntegrable (fun r : ℝ ↦ 1 / (1 - s + r)) volume 0 s := by
  apply ContinuousOn.intervalIntegrable
  intro r hr
  have hr' : r ∈ Icc (0 : ℝ) s := by
    simpa only [uIcc_of_le hs.1] using hr
  have hden : 1 - s + r ≠ 0 := by
    have : 0 < 1 - s + r := by linarith [hs.2, hr'.1]
    exact this.ne'
  exact (continuousAt_const.div
    ((continuousAt_const.sub continuousAt_const).add continuousAt_id) hden)
      |>.continuousWithinAt

/-! ## Endpoint-safe pointwise reductions -/

/-- On its sharp nonsingular domain, the right reflected-pole transform is
one logarithmic selector plus a polynomial correction of no larger degree. -/
theorem reflectedPoleRight_centeredPolynomialLift_unit
    (p : ℝ[X]) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    factorTwoReflectedPoleRightRepresenter
        (centeredPolynomialLift p) (2 * s - 1) =
      -p.eval (1 + s) * Real.log s +
        (reflectedPoleRightCorrection p).eval s := by
  have hx : 2 * s - 1 ∈ Ioc (-1 : ℝ) 1 := by
    constructor <;> linarith [hs.1, hs.2]
  unfold factorTwoReflectedPoleRightRepresenter
  rw [Set.indicator_of_mem hx,
    integral_centeredPolynomialLift_reflected_right_unit p hs]
  have hinv := intervalIntegrable_one_div_one_add_sub hs
  have hdiff : IntervalIntegrable
      (fun r : ℝ ↦ polynomialDifferenceQuotient p (1 + s) r)
      volume s 1 :=
    (continuous_polynomialDifferenceQuotient p (1 + s)).intervalIntegrable s 1
  have hrewrite :
      (∫ r : ℝ in s..1, p.eval r / (1 + s - r)) =
        ∫ r : ℝ in s..1,
          p.eval (1 + s) * (1 / (1 + s - r)) -
            polynomialDifferenceQuotient p (1 + s) r := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc s 1 := by
      simpa only [uIcc_of_le hs.2] using hr
    apply polynomial_div_reflected_right_eq
    have : 0 < 1 + s - r := by linarith [hs.1, hr'.2]
    exact this.ne'
  rw [hrewrite,
    intervalIntegral.integral_sub
      (hinv.const_mul (p.eval (1 + s))) hdiff,
    intervalIntegral.integral_const_mul,
    integral_one_div_one_add_sub hs,
    eval_reflectedPoleRightCorrection]
  ring

/-- On its sharp nonsingular domain, the left reflected-pole transform is
one logarithmic selector plus a polynomial correction of no larger degree. -/
theorem reflectedPoleLeft_centeredPolynomialLift_unit
    (p : ℝ[X]) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    factorTwoReflectedPoleLeftRepresenter
        (centeredPolynomialLift p) (2 * s - 1) =
      -p.eval (s - 1) * Real.log (1 - s) +
        (reflectedPoleLeftCorrection p).eval s := by
  have hx : 2 * s - 1 ∈ Ico (-1 : ℝ) 1 := by
    constructor <;> linarith [hs.1, hs.2]
  unfold factorTwoReflectedPoleLeftRepresenter
  rw [Set.indicator_of_mem hx,
    integral_centeredPolynomialLift_reflected_left_unit p hs]
  have hinv := intervalIntegrable_one_div_one_sub_add hs
  have hdiff : IntervalIntegrable
      (fun r : ℝ ↦ polynomialDifferenceQuotient p (s - 1) r)
      volume 0 s :=
    (continuous_polynomialDifferenceQuotient p (s - 1)).intervalIntegrable 0 s
  have hrewrite :
      (∫ r : ℝ in 0..s, p.eval r / (1 - s + r)) =
        ∫ r : ℝ in 0..s,
          p.eval (s - 1) * (1 / (1 - s + r)) +
            polynomialDifferenceQuotient p (s - 1) r := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) s := by
      simpa only [uIcc_of_le hs.1] using hr
    apply polynomial_div_reflected_left_eq
    have : 0 < 1 - s + r := by linarith [hs.2, hr'.1]
    exact this.ne'
  rw [hrewrite,
    intervalIntegral.integral_add
      (hinv.const_mul (p.eval (s - 1))) hdiff,
    intervalIntegral.integral_const_mul,
    integral_one_div_one_sub_add hs,
    eval_reflectedPoleLeftCorrection]
  ring

theorem reflectedPoleRight_centeredPolynomialLift
    (p : ℝ[X]) {x : ℝ} (hx : x ∈ Ioc (-1 : ℝ) 1) :
    factorTwoReflectedPoleRightRepresenter (centeredPolynomialLift p) x =
      -p.eval ((x + 3) / 2) * Real.log ((x + 1) / 2) +
        centeredPolynomialLift (reflectedPoleRightCorrection p) x := by
  have hs : (x + 1) / 2 ∈ Ioc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  change factorTwoReflectedPoleRightRepresenter
      (centeredPolynomialLift p) x =
    -p.eval ((x + 3) / 2) * Real.log ((x + 1) / 2) +
      (reflectedPoleRightCorrection p).eval ((x + 1) / 2)
  have h := reflectedPoleRight_centeredPolynomialLift_unit p hs
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring,
    show 1 + (x + 1) / 2 = (x + 3) / 2 by ring] at h
  exact h

theorem reflectedPoleLeft_centeredPolynomialLift
    (p : ℝ[X]) {x : ℝ} (hx : x ∈ Ico (-1 : ℝ) 1) :
    factorTwoReflectedPoleLeftRepresenter (centeredPolynomialLift p) x =
      -p.eval ((x - 1) / 2) * Real.log ((1 - x) / 2) +
        centeredPolynomialLift (reflectedPoleLeftCorrection p) x := by
  have hs : (x + 1) / 2 ∈ Ico (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  change factorTwoReflectedPoleLeftRepresenter
      (centeredPolynomialLift p) x =
    -p.eval ((x - 1) / 2) * Real.log ((1 - x) / 2) +
      (reflectedPoleLeftCorrection p).eval ((x + 1) / 2)
  have h := reflectedPoleLeft_centeredPolynomialLift_unit p hs
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring,
    show (x + 1) / 2 - 1 = (x - 1) / 2 by ring,
    show 1 - (x + 1) / 2 = (1 - x) / 2 by ring] at h
  exact h

/-- Polynomial remainder in the symmetric reflected-pole representer. -/
def reflectedPoleKCorrection (p : ℝ[X]) : ℝ[X] :=
  reflectedPoleRightCorrection p + reflectedPoleLeftCorrection p

/-- Polynomial remainder in the alternating reflected-pole representer. -/
def reflectedPoleJCorrection (p : ℝ[X]) : ℝ[X] :=
  reflectedPoleRightCorrection p - reflectedPoleLeftCorrection p

/-- The two logarithmic selectors surviving in the symmetric channel. -/
def reflectedPoleKLogSelector (p : ℝ[X]) (x : ℝ) : ℝ :=
  -p.eval ((x + 3) / 2) * Real.log ((x + 1) / 2) -
    p.eval ((x - 1) / 2) * Real.log ((1 - x) / 2)

/-- The logarithmic selectors surviving in the alternating channel. -/
def reflectedPoleJLogSelector (p : ℝ[X]) (x : ℝ) : ℝ :=
  -p.eval ((x + 3) / 2) * Real.log ((x + 1) / 2) +
    p.eval ((x - 1) / 2) * Real.log ((1 - x) / 2)

/-- Interior reduction of the symmetric representer.  The omitted endpoints
are exactly the two null rows excluded by the half-transform definitions. -/
theorem reflectedPoleK_centeredPolynomialLift
    (p : ℝ[X]) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    factorTwoReflectedPoleK (centeredPolynomialLift p) x =
      -p.eval ((x + 3) / 2) * Real.log ((x + 1) / 2) -
        p.eval ((x - 1) / 2) * Real.log ((1 - x) / 2) +
          centeredPolynomialLift (reflectedPoleKCorrection p) x := by
  have hxRight : x ∈ Ioc (-1 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
  have hxLeft : x ∈ Ico (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  unfold factorTwoReflectedPoleK reflectedPoleKCorrection
  rw [reflectedPoleRight_centeredPolynomialLift p hxRight,
    reflectedPoleLeft_centeredPolynomialLift p hxLeft]
  unfold centeredPolynomialLift
  rw [Polynomial.eval_add]
  ring

/-- Interior reduction of the alternating representer, with the left
logarithmic selector carrying the opposite sign. -/
theorem reflectedPoleJ_centeredPolynomialLift
    (p : ℝ[X]) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    factorTwoReflectedPoleJ (centeredPolynomialLift p) x =
      -p.eval ((x + 3) / 2) * Real.log ((x + 1) / 2) +
        p.eval ((x - 1) / 2) * Real.log ((1 - x) / 2) +
          centeredPolynomialLift (reflectedPoleJCorrection p) x := by
  have hxRight : x ∈ Ioc (-1 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
  have hxLeft : x ∈ Ico (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  unfold factorTwoReflectedPoleJ reflectedPoleJCorrection
  rw [reflectedPoleRight_centeredPolynomialLift p hxRight,
    reflectedPoleLeft_centeredPolynomialLift p hxLeft]
  unfold centeredPolynomialLift
  rw [Polynomial.eval_sub]
  ring

/-! ## Degree filtration -/

theorem natDegree_reflectedPoleRightCorrectionMonomial_le (k : ℕ) :
    (reflectedPoleRightCorrectionMonomial k).natDegree ≤ k := by
  unfold reflectedPoleRightCorrectionMonomial
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
  · exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  · omega

theorem natDegree_reflectedPoleLeftCorrectionMonomial_le (k : ℕ) :
    (reflectedPoleLeftCorrectionMonomial k).natDegree ≤ k := by
  unfold reflectedPoleLeftCorrectionMonomial
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
  · simp
  · omega

/-- The right correction preserves every polynomial degree filtration. -/
theorem natDegree_reflectedPoleRightCorrection_le (p : ℝ[X]) :
    (reflectedPoleRightCorrection p).natDegree ≤ p.natDegree := by
  unfold reflectedPoleRightCorrection
  rw [Polynomial.lsum_apply, Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  dsimp only [reflectedPoleRightCorrectionMonomialLinear]
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((natDegree_reflectedPoleRightCorrectionMonomial_le k).trans
      (Polynomial.le_natDegree_of_mem_supp k hk))

/-- The left correction preserves every polynomial degree filtration. -/
theorem natDegree_reflectedPoleLeftCorrection_le (p : ℝ[X]) :
    (reflectedPoleLeftCorrection p).natDegree ≤ p.natDegree := by
  unfold reflectedPoleLeftCorrection
  rw [Polynomial.lsum_apply, Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  dsimp only [reflectedPoleLeftCorrectionMonomialLinear]
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((natDegree_reflectedPoleLeftCorrectionMonomial_le k).trans
      (Polynomial.le_natDegree_of_mem_supp k hk))

theorem natDegree_reflectedPoleKCorrection_le (p : ℝ[X]) :
    (reflectedPoleKCorrection p).natDegree ≤ p.natDegree := by
  unfold reflectedPoleKCorrection
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (natDegree_reflectedPoleRightCorrection_le p)
      (natDegree_reflectedPoleLeftCorrection_le p))

theorem natDegree_reflectedPoleJCorrection_le (p : ℝ[X]) :
    (reflectedPoleJCorrection p).natDegree ≤ p.natDegree := by
  unfold reflectedPoleJCorrection
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le (natDegree_reflectedPoleRightCorrection_le p)
      (natDegree_reflectedPoleLeftCorrection_le p))

theorem natDegree_reflectedPoleKCorrection_lt_eleven
    (p : ℝ[X]) (hp : p.natDegree < 11) :
    (reflectedPoleKCorrection p).natDegree < 11 :=
  (natDegree_reflectedPoleKCorrection_le p).trans_lt hp

theorem natDegree_reflectedPoleJCorrection_lt_eleven
    (p : ℝ[X]) (hp : p.natDegree < 11) :
    (reflectedPoleJCorrection p).natDegree < 11 :=
  (natDegree_reflectedPoleJCorrection_le p).trans_lt hp

theorem degree_reflectedPoleRightCorrection_le (p : ℝ[X]) :
    (reflectedPoleRightCorrection p).degree ≤ p.degree := by
  by_cases hp : p = 0
  · simp [hp]
  rw [Polynomial.degree_eq_natDegree hp]
  exact Polynomial.degree_le_of_natDegree_le
    (natDegree_reflectedPoleRightCorrection_le p)

theorem degree_reflectedPoleLeftCorrection_le (p : ℝ[X]) :
    (reflectedPoleLeftCorrection p).degree ≤ p.degree := by
  by_cases hp : p = 0
  · simp [hp]
  rw [Polynomial.degree_eq_natDegree hp]
  exact Polynomial.degree_le_of_natDegree_le
    (natDegree_reflectedPoleLeftCorrection_le p)

/-! ## Exact moment-gap elimination -/

theorem intervalIntegral_mul_reflectedPoleKCorrection_eq_zero
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) {k : ℕ}
    (hlow : centeredLegendreMomentsVanishBelow r k)
    (hp : p.natDegree < k) :
    (∫ x : ℝ in -1..1,
      r x * centeredPolynomialLift (reflectedPoleKCorrection p) x) = 0 := by
  unfold centeredPolynomialLift
  exact intervalIntegral_mul_shiftedPolynomial_eq_zero r hr hlow _
    ((natDegree_reflectedPoleKCorrection_le p).trans_lt hp)

theorem intervalIntegral_mul_reflectedPoleJCorrection_eq_zero
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) {k : ℕ}
    (hlow : centeredLegendreMomentsVanishBelow r k)
    (hp : p.natDegree < k) :
    (∫ x : ℝ in -1..1,
      r x * centeredPolynomialLift (reflectedPoleJCorrection p) x) = 0 := by
  unfold centeredPolynomialLift
  exact intervalIntegral_mul_shiftedPolynomial_eq_zero r hr hlow _
    ((natDegree_reflectedPoleJCorrection_le p).trans_lt hp)

/-- After a moment gap above `p`, the complete symmetric reflected-pole
pairing depends only on its two logarithmic selectors. -/
theorem integral_mul_reflectedPoleK_centeredPolynomialLift_eq_logSelector
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) {k : ℕ}
    (hlow : centeredLegendreMomentsVanishBelow r k)
    (hp : p.natDegree < k) :
    (∫ x : ℝ in -1..1,
      r x * factorTwoReflectedPoleK (centeredPolynomialLift p) x) =
        ∫ x : ℝ in -1..1, r x * reflectedPoleKLogSelector p x := by
  have hpcont : Continuous (centeredPolynomialLift p) := by
    unfold centeredPolynomialLift
    fun_prop
  have hright :=
    intervalIntegrable_mul_factorTwoReflectedPoleRightRepresenter
      (centeredPolynomialLift p) r hpcont hr
  have hleft :=
    intervalIntegrable_mul_factorTwoReflectedPoleLeftRepresenter
      r (centeredPolynomialLift p) hr hpcont
  have hfull : IntervalIntegrable
      (fun x : ℝ ↦
        r x * factorTwoReflectedPoleK (centeredPolynomialLift p) x)
      volume (-1) 1 := by
    simpa only [factorTwoReflectedPoleK, mul_add] using hright.add hleft
  have hpolyCont : Continuous
      (centeredPolynomialLift (reflectedPoleKCorrection p)) := by
    unfold centeredPolynomialLift
    fun_prop
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦
        r x * centeredPolynomialLift (reflectedPoleKCorrection p) x)
      volume (-1) 1 :=
    (hr.mul hpolyCont).intervalIntegrable (-1) 1
  have hzero := intervalIntegral_mul_reflectedPoleKCorrection_eq_zero
    p r hr hlow hp
  symm
  calc
    (∫ x : ℝ in -1..1, r x * reflectedPoleKLogSelector p x) =
        ∫ x : ℝ in -1..1,
          r x * factorTwoReflectedPoleK (centeredPolynomialLift p) x -
            r x * centeredPolynomialLift (reflectedPoleKCorrection p) x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ)] with x hx1
      intro hx
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      have hxIoo : x ∈ Ioo (-1 : ℝ) 1 :=
        ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
      rw [reflectedPoleK_centeredPolynomialLift p hxIoo]
      unfold reflectedPoleKLogSelector
      ring
    _ = (∫ x : ℝ in -1..1,
          r x * factorTwoReflectedPoleK (centeredPolynomialLift p) x) -
        ∫ x : ℝ in -1..1,
          r x * centeredPolynomialLift (reflectedPoleKCorrection p) x :=
      intervalIntegral.integral_sub hfull hpoly
    _ = ∫ x : ℝ in -1..1,
        r x * factorTwoReflectedPoleK (centeredPolynomialLift p) x := by
      rw [hzero, sub_zero]

/-- After the same moment gap, the complete alternating reflected-pole
pairing depends only on the signed logarithmic selector pair. -/
theorem integral_mul_reflectedPoleJ_centeredPolynomialLift_eq_logSelector
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) {k : ℕ}
    (hlow : centeredLegendreMomentsVanishBelow r k)
    (hp : p.natDegree < k) :
    (∫ x : ℝ in -1..1,
      r x * factorTwoReflectedPoleJ (centeredPolynomialLift p) x) =
        ∫ x : ℝ in -1..1, r x * reflectedPoleJLogSelector p x := by
  have hpcont : Continuous (centeredPolynomialLift p) := by
    unfold centeredPolynomialLift
    fun_prop
  have hright :=
    intervalIntegrable_mul_factorTwoReflectedPoleRightRepresenter
      (centeredPolynomialLift p) r hpcont hr
  have hleft :=
    intervalIntegrable_mul_factorTwoReflectedPoleLeftRepresenter
      r (centeredPolynomialLift p) hr hpcont
  have hfull : IntervalIntegrable
      (fun x : ℝ ↦
        r x * factorTwoReflectedPoleJ (centeredPolynomialLift p) x)
      volume (-1) 1 := by
    simpa only [factorTwoReflectedPoleJ, mul_sub] using hright.sub hleft
  have hpolyCont : Continuous
      (centeredPolynomialLift (reflectedPoleJCorrection p)) := by
    unfold centeredPolynomialLift
    fun_prop
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦
        r x * centeredPolynomialLift (reflectedPoleJCorrection p) x)
      volume (-1) 1 :=
    (hr.mul hpolyCont).intervalIntegrable (-1) 1
  have hzero := intervalIntegral_mul_reflectedPoleJCorrection_eq_zero
    p r hr hlow hp
  symm
  calc
    (∫ x : ℝ in -1..1, r x * reflectedPoleJLogSelector p x) =
        ∫ x : ℝ in -1..1,
          r x * factorTwoReflectedPoleJ (centeredPolynomialLift p) x -
            r x * centeredPolynomialLift (reflectedPoleJCorrection p) x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ)] with x hx1
      intro hx
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      have hxIoo : x ∈ Ioo (-1 : ℝ) 1 :=
        ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
      rw [reflectedPoleJ_centeredPolynomialLift p hxIoo]
      unfold reflectedPoleJLogSelector
      ring
    _ = (∫ x : ℝ in -1..1,
          r x * factorTwoReflectedPoleJ (centeredPolynomialLift p) x) -
        ∫ x : ℝ in -1..1,
          r x * centeredPolynomialLift (reflectedPoleJCorrection p) x :=
      intervalIntegral.integral_sub hfull hpoly
    _ = ∫ x : ℝ in -1..1,
        r x * factorTwoReflectedPoleJ (centeredPolynomialLift p) x := by
      rw [hzero, sub_zero]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoReflectedPolePolynomialReductionStructural
