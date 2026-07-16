import ArithmeticHodge.Analysis.ShiftedLegendreLogKernel
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardHankelRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardReducedRepresenterDerivativesStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural

set_option autoImplicit false

open Finset MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardReducedRepresenterBridgeStructural

open ShiftedLegendreLogKernel
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseP67ForwardHankelRepresenterStructural
open YoshidaFactorTwoPhaseP67ForwardReducedRepresenterDerivativesStructural
open YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural
open YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural

noncomputable section

/-!
# Exact bridge from forward-Hankel representers to the reduced log models

Polynomial division by the affine forward denominator splits each `P₆/P₇`
half-representer into a logarithmic boundary term and a polynomial.  Reflection
then joins the two halves into the reduced `K/L` functions.  The four explicit
correction polynomials all lie below the production moment cutoffs, so they
disappear from the residual pairings structurally.
-/

/-! ## Affine denominator and reflection identities -/

private theorem intervalIntegrable_inv_forwardDenominator_right
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    IntervalIntegrable (fun y : ℝ ↦ 1 / (2 + y - x)) volume x 1 := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  have hy' : y ∈ Icc x 1 := by
    simpa only [uIcc_of_le hx.2] using hy
  have hne : 2 + y - x ≠ 0 := by linarith [hy'.1]
  exact (continuousAt_const.div
    ((continuousAt_const.add continuousAt_id).sub continuousAt_const) hne)
      |>.continuousWithinAt

private theorem integral_inv_forwardDenominator_right
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (∫ y : ℝ in x..1, 1 / (2 + y - x)) =
      Real.log ((3 - x) / 2) := by
  let F : ℝ → ℝ := fun y ↦ Real.log (2 + y - x)
  have hderiv (y : ℝ) (hne : 2 + y - x ≠ 0) :
      HasDerivAt F (1 / (2 + y - x)) y := by
    have haff : HasDerivAt (fun z : ℝ ↦ 2 + z - x) 1 y := by
      simpa using ((hasDerivAt_const y 2).add (hasDerivAt_id y)).sub_const x
    simpa only [F, Function.comp_apply, one_div, mul_one] using
      (Real.hasDerivAt_log hne).comp y haff
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy ↦ hderiv y (by
      have hy' : y ∈ Icc x 1 := by
        simpa only [uIcc_of_le hx.2] using hy
      linarith [hy'.1]))
    (intervalIntegrable_inv_forwardDenominator_right hx)
  rw [hint]
  dsimp only [F]
  rw [show 2 + 1 - x = 3 - x by ring,
    show 2 + x - x = 2 by ring,
    ← Real.log_div (by linarith [hx.2] : 3 - x ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]

private theorem monomial_div_forwardDenominator_eq
    (k : ℕ) {x y : ℝ} (hden : 2 + y - x ≠ 0) :
    y ^ k / (2 + y - x) =
      monomialDifferenceQuotient k (x - 2) y +
        (x - 2) ^ k * (1 / (2 + y - x)) := by
  have hquot :
      (2 + y - x) * monomialDifferenceQuotient k (x - 2) y =
        y ^ k - (x - 2) ^ k := by
    calc
      (2 + y - x) * monomialDifferenceQuotient k (x - 2) y =
          -((x - 2 - y) *
            monomialDifferenceQuotient k (x - 2) y) := by ring
      _ = -((x - 2) ^ k - y ^ k) := by
        rw [sub_mul_monomialDifferenceQuotient]
      _ = y ^ k - (x - 2) ^ k := by ring
  apply (div_eq_iff hden).2
  calc
    y ^ k = (y ^ k - (x - 2) ^ k) + (x - 2) ^ k := by ring
    _ = (monomialDifferenceQuotient k (x - 2) y +
          (x - 2) ^ k * (1 / (2 + y - x))) * (2 + y - x) := by
      rw [← hquot]
      field_simp [hden]

/-- Reflecting a left half-representer gives a right half-representer of the
reflected profile. -/
theorem factorTwoForwardHankelLeftRepresenter_eq_reflectedRight
    (p : ℝ → ℝ) (x : ℝ) :
    factorTwoForwardHankelLeftRepresenter p x =
      factorTwoForwardHankelRightRepresenter (fun y ↦ p (-y)) (-x) := by
  unfold factorTwoForwardHankelLeftRepresenter
    factorTwoForwardHankelRightRepresenter
  calc
    (∫ y : ℝ in -1..x,
        factorTwoForwardHankelLagWeight (x - y) * p y) =
        ∫ y : ℝ in -x..1,
          factorTwoForwardHankelLagWeight (x - -y) * p (-y) := by
      simpa using
        (intervalIntegral.integral_comp_neg
          (f := fun y : ℝ ↦
            factorTwoForwardHankelLagWeight (x - y) * p y)
          (a := -x) (b := 1)).symm
    _ = ∫ y : ℝ in -x..1,
        factorTwoForwardHankelLagWeight (y - -x) * p (-y) := by
      apply intervalIntegral.integral_congr
      intro y _hy
      ring

theorem factorTwoForwardHankelLeftRepresenter_P6_eq_right_neg
    (x : ℝ) :
    factorTwoForwardHankelLeftRepresenter factorTwoCenteredP6 x =
      factorTwoForwardHankelRightRepresenter factorTwoCenteredP6 (-x) := by
  rw [factorTwoForwardHankelLeftRepresenter_eq_reflectedRight]
  congr 1
  funext y
  exact even_factorTwoCenteredP6 y

theorem factorTwoForwardHankelLeftRepresenter_P7_eq_neg_right_neg
    (x : ℝ) :
    factorTwoForwardHankelLeftRepresenter factorTwoCenteredP7 x =
      -factorTwoForwardHankelRightRepresenter factorTwoCenteredP7 (-x) := by
  rw [factorTwoForwardHankelLeftRepresenter_eq_reflectedRight]
  have hreflect : (fun y : ℝ ↦ factorTwoCenteredP7 (-y)) =
      (-1 : ℝ) • factorTwoCenteredP7 := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [odd_factorTwoCenteredP7]
    ring
  rw [hreflect, factorTwoForwardHankelRightRepresenter_smul]
  ring

/-! ## Explicit polynomial corrections -/

/-- Polynomial part of the symmetric `P₆` representer. -/
def factorTwoForwardKP6Correction (x : ℝ) : ℝ :=
  -(11319 / 160 : ℝ) * x ^ 6 -
    (58821 / 32 : ℝ) * x ^ 4 -
    (121821 / 32 : ℝ) * x ^ 2 -
    (82383 / 160 : ℝ)

/-- Polynomial part of the alternating `P₆` representer. -/
def factorTwoForwardLP6Correction (x : ℝ) : ℝ :=
  (5313 / 10 : ℝ) * x ^ 5 +
    (7035 / 2 : ℝ) * x ^ 3 +
    (21819 / 10 : ℝ) * x

/-- Polynomial part of the symmetric `P₇` representer. -/
def factorTwoForwardKP7Correction (x : ℝ) : ℝ :=
  -(155727 / 1120 : ℝ) * x ^ 7 -
    (854667 / 160 : ℝ) * x ^ 5 -
    (628683 / 32 : ℝ) * x ^ 3 -
    (1373909 / 160 : ℝ) * x

/-- Polynomial part of the alternating `P₇` representer. -/
def factorTwoForwardLP7Correction (x : ℝ) : ℝ :=
  (99957 / 80 : ℝ) * x ^ 6 +
    (210771 / 16 : ℝ) * x ^ 4 +
    (1400643 / 80 : ℝ) * x ^ 2 +
    (998647 / 560 : ℝ)

private def centeredCoordinatePolynomial : ℝ[X] :=
  Polynomial.C 2 * Polynomial.X - Polynomial.C 1

def factorTwoForwardKP6CorrectionPolynomial : ℝ[X] :=
  Polynomial.C (-(11319 / 160 : ℝ)) * centeredCoordinatePolynomial ^ 6 +
    Polynomial.C (-(58821 / 32 : ℝ)) * centeredCoordinatePolynomial ^ 4 +
    Polynomial.C (-(121821 / 32 : ℝ)) * centeredCoordinatePolynomial ^ 2 +
    Polynomial.C (-(82383 / 160 : ℝ))

def factorTwoForwardLP6CorrectionPolynomial : ℝ[X] :=
  Polynomial.C (5313 / 10 : ℝ) * centeredCoordinatePolynomial ^ 5 +
    Polynomial.C (7035 / 2 : ℝ) * centeredCoordinatePolynomial ^ 3 +
    Polynomial.C (21819 / 10 : ℝ) * centeredCoordinatePolynomial

def factorTwoForwardKP7CorrectionPolynomial : ℝ[X] :=
  Polynomial.C (-(155727 / 1120 : ℝ)) * centeredCoordinatePolynomial ^ 7 +
    Polynomial.C (-(854667 / 160 : ℝ)) * centeredCoordinatePolynomial ^ 5 +
    Polynomial.C (-(628683 / 32 : ℝ)) * centeredCoordinatePolynomial ^ 3 +
    Polynomial.C (-(1373909 / 160 : ℝ)) * centeredCoordinatePolynomial

def factorTwoForwardLP7CorrectionPolynomial : ℝ[X] :=
  Polynomial.C (99957 / 80 : ℝ) * centeredCoordinatePolynomial ^ 6 +
    Polynomial.C (210771 / 16 : ℝ) * centeredCoordinatePolynomial ^ 4 +
    Polynomial.C (1400643 / 80 : ℝ) * centeredCoordinatePolynomial ^ 2 +
    Polynomial.C (998647 / 560 : ℝ)

@[simp] theorem factorTwoForwardKP6CorrectionPolynomial_eval (x : ℝ) :
    factorTwoForwardKP6CorrectionPolynomial.eval ((x + 1) / 2) =
      factorTwoForwardKP6Correction x := by
  simp only [factorTwoForwardKP6CorrectionPolynomial,
    centeredCoordinatePolynomial, eval_add, eval_sub, eval_mul, eval_C,
    eval_X, eval_pow]
  unfold factorTwoForwardKP6Correction
  ring

@[simp] theorem factorTwoForwardLP6CorrectionPolynomial_eval (x : ℝ) :
    factorTwoForwardLP6CorrectionPolynomial.eval ((x + 1) / 2) =
      factorTwoForwardLP6Correction x := by
  simp only [factorTwoForwardLP6CorrectionPolynomial,
    centeredCoordinatePolynomial, eval_add, eval_sub, eval_mul, eval_C,
    eval_X, eval_pow]
  unfold factorTwoForwardLP6Correction
  ring

@[simp] theorem factorTwoForwardKP7CorrectionPolynomial_eval (x : ℝ) :
    factorTwoForwardKP7CorrectionPolynomial.eval ((x + 1) / 2) =
      factorTwoForwardKP7Correction x := by
  simp only [factorTwoForwardKP7CorrectionPolynomial,
    centeredCoordinatePolynomial, eval_add, eval_sub, eval_mul, eval_C,
    eval_X, eval_pow]
  unfold factorTwoForwardKP7Correction
  ring

@[simp] theorem factorTwoForwardLP7CorrectionPolynomial_eval (x : ℝ) :
    factorTwoForwardLP7CorrectionPolynomial.eval ((x + 1) / 2) =
      factorTwoForwardLP7Correction x := by
  simp only [factorTwoForwardLP7CorrectionPolynomial,
    centeredCoordinatePolynomial, eval_add, eval_sub, eval_mul, eval_C,
    eval_X, eval_pow]
  unfold factorTwoForwardLP7Correction
  ring

theorem factorTwoForwardKP6CorrectionPolynomial_natDegree_lt_eight :
    factorTwoForwardKP6CorrectionPolynomial.natDegree < 8 := by
  unfold factorTwoForwardKP6CorrectionPolynomial centeredCoordinatePolynomial
  compute_degree
  norm_num

theorem factorTwoForwardLP6CorrectionPolynomial_natDegree_lt_nine :
    factorTwoForwardLP6CorrectionPolynomial.natDegree < 9 := by
  unfold factorTwoForwardLP6CorrectionPolynomial centeredCoordinatePolynomial
  compute_degree
  norm_num

theorem factorTwoForwardKP7CorrectionPolynomial_natDegree_lt_nine :
    factorTwoForwardKP7CorrectionPolynomial.natDegree < 9 := by
  unfold factorTwoForwardKP7CorrectionPolynomial centeredCoordinatePolynomial
  compute_degree
  norm_num

theorem factorTwoForwardLP7CorrectionPolynomial_natDegree_lt_eight :
    factorTwoForwardLP7CorrectionPolynomial.natDegree < 8 := by
  unfold factorTwoForwardLP7CorrectionPolynomial centeredCoordinatePolynomial
  compute_degree
  norm_num

/-! ## Exact evaluation of the right halves -/

private def factorTwoForwardP6RightCorrection (x : ℝ) : ℝ :=
  -(11319 / 320 : ℝ) * x ^ 6 +
    (5313 / 20 : ℝ) * x ^ 5 -
    (58821 / 64 : ℝ) * x ^ 4 +
    (7035 / 4 : ℝ) * x ^ 3 -
    (121821 / 64 : ℝ) * x ^ 2 +
    (21819 / 20 : ℝ) * x -
    (82383 / 320 : ℝ)

private def factorTwoForwardP7RightCorrection (x : ℝ) : ℝ :=
  -(155727 / 2240 : ℝ) * x ^ 7 +
    (99957 / 160 : ℝ) * x ^ 6 -
    (854667 / 320 : ℝ) * x ^ 5 +
    (210771 / 32 : ℝ) * x ^ 4 -
    (628683 / 64 : ℝ) * x ^ 3 +
    (1400643 / 160 : ℝ) * x ^ 2 -
    (1373909 / 320 : ℝ) * x +
    (998647 / 1120 : ℝ)

private theorem continuous_monomialDifferenceQuotient_right
    (k : ℕ) (a : ℝ) :
    Continuous (fun y : ℝ ↦ monomialDifferenceQuotient k a y) := by
  unfold monomialDifferenceQuotient
  fun_prop

private theorem factorTwoCenteredP6_div_forwardDenominator
    {x y : ℝ} (hden : 2 + y - x ≠ 0) :
    factorTwoCenteredP6 y / (2 + y - x) =
      (231 / 16 : ℝ) * monomialDifferenceQuotient 6 (x - 2) y +
        (-(315 / 16 : ℝ)) * monomialDifferenceQuotient 4 (x - 2) y +
        (105 / 16 : ℝ) * monomialDifferenceQuotient 2 (x - 2) y +
        factorTwoCenteredP6 (x - 2) * (1 / (2 + y - x)) := by
  calc
    factorTwoCenteredP6 y / (2 + y - x) =
        (231 / 16 : ℝ) * (y ^ 6 / (2 + y - x)) +
          (-(315 / 16 : ℝ)) * (y ^ 4 / (2 + y - x)) +
          (105 / 16 : ℝ) * (y ^ 2 / (2 + y - x)) +
          (-(5 / 16 : ℝ)) * (1 / (2 + y - x)) := by
      rw [factorTwoCenteredP6_eq]
      ring
    _ = (231 / 16 : ℝ) *
          (monomialDifferenceQuotient 6 (x - 2) y +
            (x - 2) ^ 6 * (1 / (2 + y - x))) +
        (-(315 / 16 : ℝ)) *
          (monomialDifferenceQuotient 4 (x - 2) y +
            (x - 2) ^ 4 * (1 / (2 + y - x))) +
        (105 / 16 : ℝ) *
          (monomialDifferenceQuotient 2 (x - 2) y +
            (x - 2) ^ 2 * (1 / (2 + y - x))) +
        (-(5 / 16 : ℝ)) * (1 / (2 + y - x)) := by
      rw [monomial_div_forwardDenominator_eq 6 hden,
        monomial_div_forwardDenominator_eq 4 hden,
        monomial_div_forwardDenominator_eq 2 hden]
    _ = _ := by
      rw [factorTwoCenteredP6_eq]
      ring

private theorem factorTwoCenteredP7_div_forwardDenominator
    {x y : ℝ} (hden : 2 + y - x ≠ 0) :
    factorTwoCenteredP7 y / (2 + y - x) =
      (429 / 16 : ℝ) * monomialDifferenceQuotient 7 (x - 2) y +
        (-(693 / 16 : ℝ)) * monomialDifferenceQuotient 5 (x - 2) y +
        (315 / 16 : ℝ) * monomialDifferenceQuotient 3 (x - 2) y +
        (-(35 / 16 : ℝ)) * monomialDifferenceQuotient 1 (x - 2) y +
        factorTwoCenteredP7 (x - 2) * (1 / (2 + y - x)) := by
  calc
    factorTwoCenteredP7 y / (2 + y - x) =
        (429 / 16 : ℝ) * (y ^ 7 / (2 + y - x)) +
          (-(693 / 16 : ℝ)) * (y ^ 5 / (2 + y - x)) +
          (315 / 16 : ℝ) * (y ^ 3 / (2 + y - x)) +
          (-(35 / 16 : ℝ)) * (y ^ 1 / (2 + y - x)) := by
      rw [factorTwoCenteredP7_eq]
      ring
    _ = (429 / 16 : ℝ) *
          (monomialDifferenceQuotient 7 (x - 2) y +
            (x - 2) ^ 7 * (1 / (2 + y - x))) +
        (-(693 / 16 : ℝ)) *
          (monomialDifferenceQuotient 5 (x - 2) y +
            (x - 2) ^ 5 * (1 / (2 + y - x))) +
        (315 / 16 : ℝ) *
          (monomialDifferenceQuotient 3 (x - 2) y +
            (x - 2) ^ 3 * (1 / (2 + y - x))) +
        (-(35 / 16 : ℝ)) *
          (monomialDifferenceQuotient 1 (x - 2) y +
            (x - 2) * (1 / (2 + y - x))) := by
      rw [monomial_div_forwardDenominator_eq 7 hden,
        monomial_div_forwardDenominator_eq 5 hden,
        monomial_div_forwardDenominator_eq 3 hden,
        monomial_div_forwardDenominator_eq 1 hden]
      ring
    _ = _ := by
      rw [factorTwoCenteredP7_eq]
      ring

private theorem factorTwoForwardHankelRightRepresenter_P6_exact
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelRightRepresenter factorTwoCenteredP6 x =
      factorTwoCenteredP6 (x - 2) * Real.log ((3 - x) / 2) +
        factorTwoForwardP6RightCorrection x := by
  rw [factorTwoForwardHankelRightRepresenter_eq factorTwoCenteredP6 hx]
  have hrewrite :
      (∫ y : ℝ in x..1, factorTwoCenteredP6 y / (2 + y - x)) =
        ∫ y : ℝ in x..1,
          (((231 / 16 : ℝ) * monomialDifferenceQuotient 6 (x - 2) y +
            (-(315 / 16 : ℝ)) * monomialDifferenceQuotient 4 (x - 2) y) +
            (105 / 16 : ℝ) * monomialDifferenceQuotient 2 (x - 2) y) +
            factorTwoCenteredP6 (x - 2) * (1 / (2 + y - x)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : y ∈ Icc x 1 := by
      simpa only [uIcc_of_le hx.2] using hy
    exact factorTwoCenteredP6_div_forwardDenominator (by linarith [hy'.1])
  rw [hrewrite]
  have h6 : IntervalIntegrable
      (fun y : ℝ ↦ monomialDifferenceQuotient 6 (x - 2) y) volume x 1 :=
    (continuous_monomialDifferenceQuotient_right 6 (x - 2))
      |>.intervalIntegrable x 1
  have h4 : IntervalIntegrable
      (fun y : ℝ ↦ monomialDifferenceQuotient 4 (x - 2) y) volume x 1 :=
    (continuous_monomialDifferenceQuotient_right 4 (x - 2))
      |>.intervalIntegrable x 1
  have h2 : IntervalIntegrable
      (fun y : ℝ ↦ monomialDifferenceQuotient 2 (x - 2) y) volume x 1 :=
    (continuous_monomialDifferenceQuotient_right 2 (x - 2))
      |>.intervalIntegrable x 1
  have hinv := intervalIntegrable_inv_forwardDenominator_right hx
  have h64 := (h6.const_mul (231 / 16 : ℝ)).add
    (h4.const_mul (-(315 / 16 : ℝ)))
  have h642 := h64.add (h2.const_mul (105 / 16 : ℝ))
  rw [intervalIntegral.integral_add h642
      (hinv.const_mul (factorTwoCenteredP6 (x - 2))),
    intervalIntegral.integral_add h64 (h2.const_mul (105 / 16 : ℝ)),
    intervalIntegral.integral_add
      (h6.const_mul (231 / 16 : ℝ))
      (h4.const_mul (-(315 / 16 : ℝ)))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_monomialDifferenceQuotient,
    integral_monomialDifferenceQuotient,
    integral_monomialDifferenceQuotient,
    integral_inv_forwardDenominator_right hx]
  norm_num [Finset.sum_range_succ]
  unfold factorTwoForwardP6RightCorrection
  ring

private theorem factorTwoForwardHankelRightRepresenter_P7_exact
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelRightRepresenter factorTwoCenteredP7 x =
      factorTwoCenteredP7 (x - 2) * Real.log ((3 - x) / 2) +
        factorTwoForwardP7RightCorrection x := by
  rw [factorTwoForwardHankelRightRepresenter_eq factorTwoCenteredP7 hx]
  have hrewrite :
      (∫ y : ℝ in x..1, factorTwoCenteredP7 y / (2 + y - x)) =
        ∫ y : ℝ in x..1,
          ((((429 / 16 : ℝ) * monomialDifferenceQuotient 7 (x - 2) y +
            (-(693 / 16 : ℝ)) * monomialDifferenceQuotient 5 (x - 2) y) +
            (315 / 16 : ℝ) * monomialDifferenceQuotient 3 (x - 2) y) +
            (-(35 / 16 : ℝ)) * monomialDifferenceQuotient 1 (x - 2) y) +
            factorTwoCenteredP7 (x - 2) * (1 / (2 + y - x)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : y ∈ Icc x 1 := by
      simpa only [uIcc_of_le hx.2] using hy
    exact factorTwoCenteredP7_div_forwardDenominator (by linarith [hy'.1])
  rw [hrewrite]
  have h7 : IntervalIntegrable
      (fun y : ℝ ↦ monomialDifferenceQuotient 7 (x - 2) y) volume x 1 :=
    (continuous_monomialDifferenceQuotient_right 7 (x - 2))
      |>.intervalIntegrable x 1
  have h5 : IntervalIntegrable
      (fun y : ℝ ↦ monomialDifferenceQuotient 5 (x - 2) y) volume x 1 :=
    (continuous_monomialDifferenceQuotient_right 5 (x - 2))
      |>.intervalIntegrable x 1
  have h3 : IntervalIntegrable
      (fun y : ℝ ↦ monomialDifferenceQuotient 3 (x - 2) y) volume x 1 :=
    (continuous_monomialDifferenceQuotient_right 3 (x - 2))
      |>.intervalIntegrable x 1
  have h1 : IntervalIntegrable
      (fun y : ℝ ↦ monomialDifferenceQuotient 1 (x - 2) y) volume x 1 :=
    (continuous_monomialDifferenceQuotient_right 1 (x - 2))
      |>.intervalIntegrable x 1
  have hinv := intervalIntegrable_inv_forwardDenominator_right hx
  have h75 := (h7.const_mul (429 / 16 : ℝ)).add
    (h5.const_mul (-(693 / 16 : ℝ)))
  have h753 := h75.add (h3.const_mul (315 / 16 : ℝ))
  have h7531 := h753.add (h1.const_mul (-(35 / 16 : ℝ)))
  rw [intervalIntegral.integral_add h7531
      (hinv.const_mul (factorTwoCenteredP7 (x - 2))),
    intervalIntegral.integral_add h753
      (h1.const_mul (-(35 / 16 : ℝ))),
    intervalIntegral.integral_add h75 (h3.const_mul (315 / 16 : ℝ)),
    intervalIntegral.integral_add
      (h7.const_mul (429 / 16 : ℝ))
      (h5.const_mul (-(693 / 16 : ℝ)))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_monomialDifferenceQuotient,
    integral_monomialDifferenceQuotient,
    integral_monomialDifferenceQuotient,
    integral_monomialDifferenceQuotient,
    integral_inv_forwardDenominator_right hx]
  norm_num [Finset.sum_range_succ]
  unfold factorTwoForwardP7RightCorrection
  ring

/-! ## Pointwise `K/L` bridges -/

theorem factorTwoForwardHankelK_P6_eq_reduced
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelK factorTwoCenteredP6 x =
      factorTwoForwardKP6 x + factorTwoForwardKP6Correction x := by
  have hxneg : -x ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hparity : factorTwoCenteredP6 (-x - 2) =
      factorTwoCenteredP6 (x + 2) := by
    rw [show -x - 2 = -(x + 2) by ring, even_factorTwoCenteredP6]
  unfold factorTwoForwardHankelK
  rw [factorTwoForwardHankelRightRepresenter_P6_exact hx,
    factorTwoForwardHankelLeftRepresenter_P6_eq_right_neg,
    factorTwoForwardHankelRightRepresenter_P6_exact hxneg,
    hparity]
  unfold factorTwoForwardKP6
  rw [factorTwoForwardCenteredP6_eq_factorTwoCenteredP6]
  unfold factorTwoForwardP6RightCorrection factorTwoForwardKP6Correction
  ring

theorem factorTwoForwardHankelL_P6_eq_reduced
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelL factorTwoCenteredP6 x =
      factorTwoForwardLP6 x + factorTwoForwardLP6Correction x := by
  have hxneg : -x ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hparity : factorTwoCenteredP6 (-x - 2) =
      factorTwoCenteredP6 (x + 2) := by
    rw [show -x - 2 = -(x + 2) by ring, even_factorTwoCenteredP6]
  unfold factorTwoForwardHankelL
  rw [factorTwoForwardHankelRightRepresenter_P6_exact hx,
    factorTwoForwardHankelLeftRepresenter_P6_eq_right_neg,
    factorTwoForwardHankelRightRepresenter_P6_exact hxneg,
    hparity]
  unfold factorTwoForwardLP6
  rw [factorTwoForwardCenteredP6_eq_factorTwoCenteredP6]
  unfold factorTwoForwardP6RightCorrection factorTwoForwardLP6Correction
  ring

theorem factorTwoForwardHankelK_P7_eq_reduced
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelK factorTwoCenteredP7 x =
      factorTwoForwardKP7 x + factorTwoForwardKP7Correction x := by
  have hxneg : -x ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hparity : factorTwoCenteredP7 (-x - 2) =
      -factorTwoCenteredP7 (x + 2) := by
    rw [show -x - 2 = -(x + 2) by ring, odd_factorTwoCenteredP7]
  unfold factorTwoForwardHankelK
  rw [factorTwoForwardHankelRightRepresenter_P7_exact hx,
    factorTwoForwardHankelLeftRepresenter_P7_eq_neg_right_neg,
    factorTwoForwardHankelRightRepresenter_P7_exact hxneg,
    hparity]
  unfold factorTwoForwardKP7
  rw [factorTwoForwardCenteredP7_eq_factorTwoCenteredP7]
  unfold factorTwoForwardP7RightCorrection factorTwoForwardKP7Correction
  ring

theorem factorTwoForwardHankelL_P7_eq_reduced
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelL factorTwoCenteredP7 x =
      factorTwoForwardLP7 x + factorTwoForwardLP7Correction x := by
  have hxneg : -x ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hparity : factorTwoCenteredP7 (-x - 2) =
      -factorTwoCenteredP7 (x + 2) := by
    rw [show -x - 2 = -(x + 2) by ring, odd_factorTwoCenteredP7]
  unfold factorTwoForwardHankelL
  rw [factorTwoForwardHankelRightRepresenter_P7_exact hx,
    factorTwoForwardHankelLeftRepresenter_P7_eq_neg_right_neg,
    factorTwoForwardHankelRightRepresenter_P7_exact hxneg,
    hparity]
  unfold factorTwoForwardLP7
  rw [factorTwoForwardCenteredP7_eq_factorTwoCenteredP7]
  unfold factorTwoForwardP7RightCorrection factorTwoForwardLP7Correction
  ring

/-! ## Moment-gap cancellation and public pairing bridges -/

private theorem factorTwoForwardKP6CorrectionPolynomial_natDegree_lt_nine :
    factorTwoForwardKP6CorrectionPolynomial.natDegree < 9 :=
  factorTwoForwardKP6CorrectionPolynomial_natDegree_lt_eight.trans (by norm_num)

private theorem factorTwoForwardLP7CorrectionPolynomial_natDegree_lt_nine :
    factorTwoForwardLP7CorrectionPolynomial.natDegree < 9 :=
  factorTwoForwardLP7CorrectionPolynomial_natDegree_lt_eight.trans (by norm_num)

theorem integral_mul_factorTwoForwardKP6Correction_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1, w x * factorTwoForwardKP6Correction x) = 0 := by
  rw [show (fun x : ℝ ↦ w x * factorTwoForwardKP6Correction x) =
      fun x ↦ w x * factorTwoForwardKP6CorrectionPolynomial.eval ((x + 1) / 2) by
    funext x
    rw [factorTwoForwardKP6CorrectionPolynomial_eval]]
  exact intervalIntegral_mul_shiftedPolynomial_eq_zero w hw hlow
    factorTwoForwardKP6CorrectionPolynomial
    factorTwoForwardKP6CorrectionPolynomial_natDegree_lt_nine

theorem integral_mul_factorTwoForwardLP6Correction_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1, w x * factorTwoForwardLP6Correction x) = 0 := by
  rw [show (fun x : ℝ ↦ w x * factorTwoForwardLP6Correction x) =
      fun x ↦ w x * factorTwoForwardLP6CorrectionPolynomial.eval ((x + 1) / 2) by
    funext x
    rw [factorTwoForwardLP6CorrectionPolynomial_eval]]
  exact intervalIntegral_mul_shiftedPolynomial_eq_zero w hw hlow
    factorTwoForwardLP6CorrectionPolynomial
    factorTwoForwardLP6CorrectionPolynomial_natDegree_lt_nine

theorem integral_mul_factorTwoForwardKP7Correction_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1, w x * factorTwoForwardKP7Correction x) = 0 := by
  rw [show (fun x : ℝ ↦ w x * factorTwoForwardKP7Correction x) =
      fun x ↦ w x * factorTwoForwardKP7CorrectionPolynomial.eval ((x + 1) / 2) by
    funext x
    rw [factorTwoForwardKP7CorrectionPolynomial_eval]]
  exact intervalIntegral_mul_shiftedPolynomial_eq_zero w hw hlow
    factorTwoForwardKP7CorrectionPolynomial
    factorTwoForwardKP7CorrectionPolynomial_natDegree_lt_nine

theorem integral_mul_factorTwoForwardLP7Correction_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1, w x * factorTwoForwardLP7Correction x) = 0 := by
  rw [show (fun x : ℝ ↦ w x * factorTwoForwardLP7Correction x) =
      fun x ↦ w x * factorTwoForwardLP7CorrectionPolynomial.eval ((x + 1) / 2) by
    funext x
    rw [factorTwoForwardLP7CorrectionPolynomial_eval]]
  exact intervalIntegral_mul_shiftedPolynomial_eq_zero w hw hlow
    factorTwoForwardLP7CorrectionPolynomial
    factorTwoForwardLP7CorrectionPolynomial_natDegree_lt_nine

theorem integral_mul_factorTwoForwardHankelK_P6_eq_reduced
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1,
      w x * factorTwoForwardHankelK factorTwoCenteredP6 x) =
      ∫ x : ℝ in -1..1, w x * factorTwoForwardKP6 x := by
  have hred : IntervalIntegrable (fun x : ℝ ↦ w x * factorTwoForwardKP6 x)
      volume (-1) 1 :=
    (hw.continuousOn.mul continuousOn_factorTwoForwardKP6)
      |>.intervalIntegrable_of_Icc (by norm_num)
  have hcorr : IntervalIntegrable
      (fun x : ℝ ↦ w x * factorTwoForwardKP6Correction x) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold factorTwoForwardKP6Correction
    fun_prop
  calc
    (∫ x : ℝ in -1..1,
        w x * factorTwoForwardHankelK factorTwoCenteredP6 x) =
        ∫ x : ℝ in -1..1,
          w x * factorTwoForwardKP6 x +
            w x * factorTwoForwardKP6Correction x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (-1 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
      change w x * factorTwoForwardHankelK factorTwoCenteredP6 x =
        w x * factorTwoForwardKP6 x + w x * factorTwoForwardKP6Correction x
      rw [factorTwoForwardHankelK_P6_eq_reduced hx']
      ring
    _ = (∫ x : ℝ in -1..1, w x * factorTwoForwardKP6 x) +
        ∫ x : ℝ in -1..1, w x * factorTwoForwardKP6Correction x := by
      rw [intervalIntegral.integral_add hred hcorr]
    _ = _ := by
      rw [integral_mul_factorTwoForwardKP6Correction_eq_zero w hw hlow,
        add_zero]

theorem integral_mul_factorTwoForwardHankelL_P6_eq_reduced
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1,
      w x * factorTwoForwardHankelL factorTwoCenteredP6 x) =
      ∫ x : ℝ in -1..1, w x * factorTwoForwardLP6 x := by
  have hred : IntervalIntegrable (fun x : ℝ ↦ w x * factorTwoForwardLP6 x)
      volume (-1) 1 :=
    (hw.continuousOn.mul continuousOn_factorTwoForwardLP6)
      |>.intervalIntegrable_of_Icc (by norm_num)
  have hcorr : IntervalIntegrable
      (fun x : ℝ ↦ w x * factorTwoForwardLP6Correction x) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold factorTwoForwardLP6Correction
    fun_prop
  calc
    (∫ x : ℝ in -1..1,
        w x * factorTwoForwardHankelL factorTwoCenteredP6 x) =
        ∫ x : ℝ in -1..1,
          w x * factorTwoForwardLP6 x +
            w x * factorTwoForwardLP6Correction x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (-1 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
      change w x * factorTwoForwardHankelL factorTwoCenteredP6 x =
        w x * factorTwoForwardLP6 x + w x * factorTwoForwardLP6Correction x
      rw [factorTwoForwardHankelL_P6_eq_reduced hx']
      ring
    _ = (∫ x : ℝ in -1..1, w x * factorTwoForwardLP6 x) +
        ∫ x : ℝ in -1..1, w x * factorTwoForwardLP6Correction x := by
      rw [intervalIntegral.integral_add hred hcorr]
    _ = _ := by
      rw [integral_mul_factorTwoForwardLP6Correction_eq_zero w hw hlow,
        add_zero]

theorem integral_mul_factorTwoForwardHankelK_P7_eq_reduced
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1,
      w x * factorTwoForwardHankelK factorTwoCenteredP7 x) =
      ∫ x : ℝ in -1..1, w x * factorTwoForwardKP7 x := by
  have hred : IntervalIntegrable (fun x : ℝ ↦ w x * factorTwoForwardKP7 x)
      volume (-1) 1 :=
    (hw.continuousOn.mul continuousOn_factorTwoForwardKP7)
      |>.intervalIntegrable_of_Icc (by norm_num)
  have hcorr : IntervalIntegrable
      (fun x : ℝ ↦ w x * factorTwoForwardKP7Correction x) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold factorTwoForwardKP7Correction
    fun_prop
  calc
    (∫ x : ℝ in -1..1,
        w x * factorTwoForwardHankelK factorTwoCenteredP7 x) =
        ∫ x : ℝ in -1..1,
          w x * factorTwoForwardKP7 x +
            w x * factorTwoForwardKP7Correction x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (-1 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
      change w x * factorTwoForwardHankelK factorTwoCenteredP7 x =
        w x * factorTwoForwardKP7 x + w x * factorTwoForwardKP7Correction x
      rw [factorTwoForwardHankelK_P7_eq_reduced hx']
      ring
    _ = (∫ x : ℝ in -1..1, w x * factorTwoForwardKP7 x) +
        ∫ x : ℝ in -1..1, w x * factorTwoForwardKP7Correction x := by
      rw [intervalIntegral.integral_add hred hcorr]
    _ = _ := by
      rw [integral_mul_factorTwoForwardKP7Correction_eq_zero w hw hlow,
        add_zero]

theorem integral_mul_factorTwoForwardHankelL_P7_eq_reduced
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1,
      w x * factorTwoForwardHankelL factorTwoCenteredP7 x) =
      ∫ x : ℝ in -1..1, w x * factorTwoForwardLP7 x := by
  have hred : IntervalIntegrable (fun x : ℝ ↦ w x * factorTwoForwardLP7 x)
      volume (-1) 1 :=
    (hw.continuousOn.mul continuousOn_factorTwoForwardLP7)
      |>.intervalIntegrable_of_Icc (by norm_num)
  have hcorr : IntervalIntegrable
      (fun x : ℝ ↦ w x * factorTwoForwardLP7Correction x) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold factorTwoForwardLP7Correction
    fun_prop
  calc
    (∫ x : ℝ in -1..1,
        w x * factorTwoForwardHankelL factorTwoCenteredP7 x) =
        ∫ x : ℝ in -1..1,
          w x * factorTwoForwardLP7 x +
            w x * factorTwoForwardLP7Correction x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (-1 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
      change w x * factorTwoForwardHankelL factorTwoCenteredP7 x =
        w x * factorTwoForwardLP7 x + w x * factorTwoForwardLP7Correction x
      rw [factorTwoForwardHankelL_P7_eq_reduced hx']
      ring
    _ = (∫ x : ℝ in -1..1, w x * factorTwoForwardLP7 x) +
        ∫ x : ℝ in -1..1, w x * factorTwoForwardLP7Correction x := by
      rw [intervalIntegral.integral_add hred hcorr]
    _ = _ := by
      rw [integral_mul_factorTwoForwardLP7Correction_eq_zero w hw hlow,
        add_zero]

/-- The exact forward mixed term depends only on the four reduced logarithmic
representers once both residuals have the production nine-moment gap. -/
theorem factorTwoP67ResidualForwardHankelMixed_scaled_P67_eq_reducedPairings
    (eR oR : ℝ → ℝ) (heR : Continuous eR) (hoR : Continuous oR)
    (heLow : centeredLegendreMomentsVanishBelow eR 9)
    (hoLow : centeredLegendreMomentsVanishBelow oR 9)
    (c d a b : ℝ) :
    factorTwoP67ResidualForwardHankelMixed
        (c • factorTwoCenteredP6) (d • factorTwoCenteredP7)
        eR oR a b =
      -(a * c / 4) * (∫ x : ℝ in -1..1, eR x * factorTwoForwardKP6 x) -
      (a * d / 4) * (∫ x : ℝ in -1..1, oR x * factorTwoForwardKP7 x) +
      (b * c / 4) * (∫ x : ℝ in -1..1, oR x * factorTwoForwardLP6 x) -
      (b * d / 4) * (∫ x : ℝ in -1..1, eR x * factorTwoForwardLP7 x) := by
  rw [factorTwoP67ResidualForwardHankelMixed_scaled_P67_eq_pairings
    eR oR heR hoR c d a b,
    integral_mul_factorTwoForwardHankelK_P6_eq_reduced eR heR heLow,
    integral_mul_factorTwoForwardHankelK_P7_eq_reduced oR hoR hoLow,
    integral_mul_factorTwoForwardHankelL_P6_eq_reduced oR hoR hoLow,
    integral_mul_factorTwoForwardHankelL_P7_eq_reduced eR heR heLow]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardReducedRepresenterBridgeStructural
