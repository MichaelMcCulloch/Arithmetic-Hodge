import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardReducedRepresenterBridgeStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8StructuralReserve

set_option autoImplicit false

open Finset MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8ForwardReducedRepresenterBridgeStructural

open ShiftedLegendreLogKernel
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseP67ForwardHankelRepresenterStructural
open YoshidaFactorTwoPhaseP67ForwardReducedRepresenterBridgeStructural
open YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural
open YoshidaFactorTwoPhaseP8StructuralReserve

noncomputable section

/-!
# Exact bridge from the `P8` forward-Hankel row to reduced log models

Polynomial division by the affine forward denominator splits the right
`P8` half-representer into a logarithmic boundary term and a polynomial.
Even reflection joins the two halves into the reduced symmetric and
alternating representers.  Both correction polynomials have degree below
nine, so a production nine-moment residual annihilates them exactly.
-/

/-! ## Reduced `P8` representers -/

/-- Classical centered Legendre `P8`, in the power basis used by the
forward logarithmic models. -/
def factorTwoForwardCenteredP8 (x : ℝ) : ℝ :=
  (6435 * x ^ 8 - 12012 * x ^ 6 + 6930 * x ^ 4 -
    1260 * x ^ 2 + 35) / 128

theorem factorTwoForwardCenteredP8_eq_factorTwoCenteredP8 :
    factorTwoForwardCenteredP8 = factorTwoCenteredP8 := by
  funext x
  rw [factorTwoCenteredP8_eq]
  rfl

/-- Symmetric reduced forward representer attached to `P8`. -/
def factorTwoForwardKP8 (x : ℝ) : ℝ :=
  factorTwoForwardCenteredP8 (x + 2) * Real.log ((3 + x) / 2) +
    factorTwoForwardCenteredP8 (x - 2) * Real.log ((3 - x) / 2)

/-- Alternating reduced forward representer attached to `P8`. -/
def factorTwoForwardLP8 (x : ℝ) : ℝ :=
  factorTwoForwardCenteredP8 (x - 2) * Real.log ((3 - x) / 2) -
    factorTwoForwardCenteredP8 (x + 2) * Real.log ((3 + x) / 2)

private lemma forward_log_arguments_ne_zero
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (3 + x) / 2 ≠ 0 ∧ (3 - x) / 2 ≠ 0 := by
  rcases hx with ⟨hx0, hx1⟩
  constructor <;> norm_num <;> linarith

private lemma continuousOn_forward_log_plus :
    ContinuousOn (fun x : ℝ ↦ Real.log ((3 + x) / 2))
      (Icc (-1 : ℝ) 1) := by
  apply ContinuousOn.log
  · fun_prop
  · intro x hx
    exact (forward_log_arguments_ne_zero hx).1

private lemma continuousOn_forward_log_minus :
    ContinuousOn (fun x : ℝ ↦ Real.log ((3 - x) / 2))
      (Icc (-1 : ℝ) 1) := by
  apply ContinuousOn.log
  · fun_prop
  · intro x hx
    exact (forward_log_arguments_ne_zero hx).2

theorem continuousOn_factorTwoForwardKP8 :
    ContinuousOn factorTwoForwardKP8 (Icc (-1 : ℝ) 1) := by
  unfold factorTwoForwardKP8
  apply ContinuousOn.add
  · apply ContinuousOn.mul
    · unfold factorTwoForwardCenteredP8
      fun_prop
    · exact continuousOn_forward_log_plus
  · apply ContinuousOn.mul
    · unfold factorTwoForwardCenteredP8
      fun_prop
    · exact continuousOn_forward_log_minus

theorem continuousOn_factorTwoForwardLP8 :
    ContinuousOn factorTwoForwardLP8 (Icc (-1 : ℝ) 1) := by
  unfold factorTwoForwardLP8
  apply ContinuousOn.sub
  · apply ContinuousOn.mul
    · unfold factorTwoForwardCenteredP8
      fun_prop
    · exact continuousOn_forward_log_minus
  · apply ContinuousOn.mul
    · unfold factorTwoForwardCenteredP8
      fun_prop
    · exact continuousOn_forward_log_plus

/-! ## Exact correction polynomials -/

/-- Polynomial part of the symmetric `P8` representer. -/
def factorTwoForwardKP8Correction (x : ℝ) : ℝ :=
  -(979407 / 3584 : ℝ) * x ^ 8 -
    (9351771 / 640 : ℝ) * x ^ 6 -
    (21669483 / 256 : ℝ) * x ^ 4 -
    (10037823 / 128 : ℝ) * x ^ 2 -
    (111766731 / 17920 : ℝ)

/-- Polynomial part of the alternating `P8` representer. -/
def factorTwoForwardLP8Correction (x : ℝ) : ℝ :=
  (1283139 / 448 : ℝ) * x ^ 7 +
    (14165151 / 320 : ℝ) * x ^ 5 +
    (6619107 / 64 : ℝ) * x ^ 3 +
    (75343551 / 2240 : ℝ) * x

private def centeredCoordinatePolynomial : ℝ[X] :=
  Polynomial.C 2 * Polynomial.X - Polynomial.C 1

def factorTwoForwardKP8CorrectionPolynomial : ℝ[X] :=
  Polynomial.C (-(979407 / 3584 : ℝ)) * centeredCoordinatePolynomial ^ 8 +
    Polynomial.C (-(9351771 / 640 : ℝ)) * centeredCoordinatePolynomial ^ 6 +
    Polynomial.C (-(21669483 / 256 : ℝ)) * centeredCoordinatePolynomial ^ 4 +
    Polynomial.C (-(10037823 / 128 : ℝ)) * centeredCoordinatePolynomial ^ 2 +
    Polynomial.C (-(111766731 / 17920 : ℝ))

def factorTwoForwardLP8CorrectionPolynomial : ℝ[X] :=
  Polynomial.C (1283139 / 448 : ℝ) * centeredCoordinatePolynomial ^ 7 +
    Polynomial.C (14165151 / 320 : ℝ) * centeredCoordinatePolynomial ^ 5 +
    Polynomial.C (6619107 / 64 : ℝ) * centeredCoordinatePolynomial ^ 3 +
    Polynomial.C (75343551 / 2240 : ℝ) * centeredCoordinatePolynomial

@[simp] theorem factorTwoForwardKP8CorrectionPolynomial_eval (x : ℝ) :
    factorTwoForwardKP8CorrectionPolynomial.eval ((x + 1) / 2) =
      factorTwoForwardKP8Correction x := by
  simp only [factorTwoForwardKP8CorrectionPolynomial,
    centeredCoordinatePolynomial, eval_add, eval_sub, eval_mul, eval_C,
    eval_X, eval_pow]
  unfold factorTwoForwardKP8Correction
  ring

@[simp] theorem factorTwoForwardLP8CorrectionPolynomial_eval (x : ℝ) :
    factorTwoForwardLP8CorrectionPolynomial.eval ((x + 1) / 2) =
      factorTwoForwardLP8Correction x := by
  simp only [factorTwoForwardLP8CorrectionPolynomial,
    centeredCoordinatePolynomial, eval_add, eval_sub, eval_mul, eval_C,
    eval_X, eval_pow]
  unfold factorTwoForwardLP8Correction
  ring

theorem factorTwoForwardKP8CorrectionPolynomial_natDegree_lt_nine :
    factorTwoForwardKP8CorrectionPolynomial.natDegree < 9 := by
  unfold factorTwoForwardKP8CorrectionPolynomial centeredCoordinatePolynomial
  compute_degree
  norm_num

theorem factorTwoForwardLP8CorrectionPolynomial_natDegree_lt_nine :
    factorTwoForwardLP8CorrectionPolynomial.natDegree < 9 := by
  unfold factorTwoForwardLP8CorrectionPolynomial centeredCoordinatePolynomial
  compute_degree
  norm_num

/-! ## Affine denominator reduction -/

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
          -((x - 2 - y) * monomialDifferenceQuotient k (x - 2) y) := by ring
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

private theorem continuous_monomialDifferenceQuotient_right
    (k : ℕ) (a : ℝ) :
    Continuous (fun y : ℝ ↦ monomialDifferenceQuotient k a y) := by
  unfold monomialDifferenceQuotient
  fun_prop

private theorem factorTwoCenteredP8_div_forwardDenominator
    {x y : ℝ} (hden : 2 + y - x ≠ 0) :
    factorTwoCenteredP8 y / (2 + y - x) =
      (6435 / 128 : ℝ) * monomialDifferenceQuotient 8 (x - 2) y +
        (-(3003 / 32 : ℝ)) * monomialDifferenceQuotient 6 (x - 2) y +
        (3465 / 64 : ℝ) * monomialDifferenceQuotient 4 (x - 2) y +
        (-(315 / 32 : ℝ)) * monomialDifferenceQuotient 2 (x - 2) y +
        factorTwoCenteredP8 (x - 2) * (1 / (2 + y - x)) := by
  calc
    factorTwoCenteredP8 y / (2 + y - x) =
        (6435 / 128 : ℝ) * (y ^ 8 / (2 + y - x)) +
          (-(3003 / 32 : ℝ)) * (y ^ 6 / (2 + y - x)) +
          (3465 / 64 : ℝ) * (y ^ 4 / (2 + y - x)) +
          (-(315 / 32 : ℝ)) * (y ^ 2 / (2 + y - x)) +
          (35 / 128 : ℝ) * (1 / (2 + y - x)) := by
      rw [factorTwoCenteredP8_eq]
      ring
    _ = (6435 / 128 : ℝ) *
          (monomialDifferenceQuotient 8 (x - 2) y +
            (x - 2) ^ 8 * (1 / (2 + y - x))) +
        (-(3003 / 32 : ℝ)) *
          (monomialDifferenceQuotient 6 (x - 2) y +
            (x - 2) ^ 6 * (1 / (2 + y - x))) +
        (3465 / 64 : ℝ) *
          (monomialDifferenceQuotient 4 (x - 2) y +
            (x - 2) ^ 4 * (1 / (2 + y - x))) +
        (-(315 / 32 : ℝ)) *
          (monomialDifferenceQuotient 2 (x - 2) y +
            (x - 2) ^ 2 * (1 / (2 + y - x))) +
        (35 / 128 : ℝ) * (1 / (2 + y - x)) := by
      rw [monomial_div_forwardDenominator_eq 8 hden,
        monomial_div_forwardDenominator_eq 6 hden,
        monomial_div_forwardDenominator_eq 4 hden,
        monomial_div_forwardDenominator_eq 2 hden]
    _ = _ := by
      rw [factorTwoCenteredP8_eq]
      ring

private def factorTwoForwardP8RightCorrection (x : ℝ) : ℝ :=
  -(979407 / 7168 : ℝ) * x ^ 8 +
    (1283139 / 896 : ℝ) * x ^ 7 -
    (9351771 / 1280 : ℝ) * x ^ 6 +
    (14165151 / 640 : ℝ) * x ^ 5 -
    (21669483 / 512 : ℝ) * x ^ 4 +
    (6619107 / 128 : ℝ) * x ^ 3 -
    (10037823 / 256 : ℝ) * x ^ 2 +
    (75343551 / 4480 : ℝ) * x -
    (111766731 / 35840 : ℝ)

private theorem factorTwoForwardHankelRightRepresenter_P8_exact
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelRightRepresenter factorTwoCenteredP8 x =
      factorTwoCenteredP8 (x - 2) * Real.log ((3 - x) / 2) +
        factorTwoForwardP8RightCorrection x := by
  rw [factorTwoForwardHankelRightRepresenter_eq factorTwoCenteredP8 hx]
  have hrewrite :
      (∫ y : ℝ in x..1, factorTwoCenteredP8 y / (2 + y - x)) =
        ∫ y : ℝ in x..1,
          ((((6435 / 128 : ℝ) * monomialDifferenceQuotient 8 (x - 2) y +
            (-(3003 / 32 : ℝ)) * monomialDifferenceQuotient 6 (x - 2) y) +
            (3465 / 64 : ℝ) * monomialDifferenceQuotient 4 (x - 2) y) +
            (-(315 / 32 : ℝ)) * monomialDifferenceQuotient 2 (x - 2) y) +
            factorTwoCenteredP8 (x - 2) * (1 / (2 + y - x)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : y ∈ Icc x 1 := by
      simpa only [uIcc_of_le hx.2] using hy
    exact factorTwoCenteredP8_div_forwardDenominator (by linarith [hy'.1])
  rw [hrewrite]
  have h8 : IntervalIntegrable
      (fun y : ℝ ↦ monomialDifferenceQuotient 8 (x - 2) y) volume x 1 :=
    (continuous_monomialDifferenceQuotient_right 8 (x - 2))
      |>.intervalIntegrable x 1
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
  have h86 := (h8.const_mul (6435 / 128 : ℝ)).add
    (h6.const_mul (-(3003 / 32 : ℝ)))
  have h864 := h86.add (h4.const_mul (3465 / 64 : ℝ))
  have h8642 := h864.add (h2.const_mul (-(315 / 32 : ℝ)))
  rw [intervalIntegral.integral_add h8642
      (hinv.const_mul (factorTwoCenteredP8 (x - 2))),
    intervalIntegral.integral_add h864
      (h2.const_mul (-(315 / 32 : ℝ))),
    intervalIntegral.integral_add h86 (h4.const_mul (3465 / 64 : ℝ)),
    intervalIntegral.integral_add
      (h8.const_mul (6435 / 128 : ℝ))
      (h6.const_mul (-(3003 / 32 : ℝ)))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_monomialDifferenceQuotient,
    integral_monomialDifferenceQuotient,
    integral_monomialDifferenceQuotient,
    integral_monomialDifferenceQuotient,
    integral_inv_forwardDenominator_right hx]
  norm_num [Finset.sum_range_succ]
  unfold factorTwoForwardP8RightCorrection
  ring

/-! ## Pointwise `K/L` bridges -/

private theorem factorTwoForwardHankelLeftRepresenter_P8_eq_right_neg
    (x : ℝ) :
    factorTwoForwardHankelLeftRepresenter factorTwoCenteredP8 x =
      factorTwoForwardHankelRightRepresenter factorTwoCenteredP8 (-x) := by
  rw [factorTwoForwardHankelLeftRepresenter_eq_reflectedRight]
  congr 1
  funext y
  exact even_factorTwoCenteredP8 y

/-- The symmetric `P8` Hankel representer is its reduced logarithmic model
plus an explicit degree-eight correction. -/
theorem factorTwoForwardHankelK_P8_eq_reduced
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelK factorTwoCenteredP8 x =
      factorTwoForwardKP8 x + factorTwoForwardKP8Correction x := by
  have hxneg : -x ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hparity : factorTwoCenteredP8 (-x - 2) =
      factorTwoCenteredP8 (x + 2) := by
    rw [show -x - 2 = -(x + 2) by ring, even_factorTwoCenteredP8]
  unfold factorTwoForwardHankelK
  rw [factorTwoForwardHankelRightRepresenter_P8_exact hx,
    factorTwoForwardHankelLeftRepresenter_P8_eq_right_neg,
    factorTwoForwardHankelRightRepresenter_P8_exact hxneg,
    hparity]
  unfold factorTwoForwardKP8
  rw [factorTwoForwardCenteredP8_eq_factorTwoCenteredP8]
  unfold factorTwoForwardP8RightCorrection factorTwoForwardKP8Correction
  ring

/-- The alternating `P8` Hankel representer is its reduced logarithmic model
plus an explicit degree-seven correction. -/
theorem factorTwoForwardHankelL_P8_eq_reduced
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardHankelL factorTwoCenteredP8 x =
      factorTwoForwardLP8 x + factorTwoForwardLP8Correction x := by
  have hxneg : -x ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hparity : factorTwoCenteredP8 (-x - 2) =
      factorTwoCenteredP8 (x + 2) := by
    rw [show -x - 2 = -(x + 2) by ring, even_factorTwoCenteredP8]
  unfold factorTwoForwardHankelL
  rw [factorTwoForwardHankelRightRepresenter_P8_exact hx,
    factorTwoForwardHankelLeftRepresenter_P8_eq_right_neg,
    factorTwoForwardHankelRightRepresenter_P8_exact hxneg,
    hparity]
  unfold factorTwoForwardLP8
  rw [factorTwoForwardCenteredP8_eq_factorTwoCenteredP8]
  unfold factorTwoForwardP8RightCorrection factorTwoForwardLP8Correction
  ring

/-! ## Moment-gap cancellation and public pairing bridges -/

theorem integral_mul_factorTwoForwardKP8Correction_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1, w x * factorTwoForwardKP8Correction x) = 0 := by
  rw [show (fun x : ℝ ↦ w x * factorTwoForwardKP8Correction x) =
      fun x ↦ w x * factorTwoForwardKP8CorrectionPolynomial.eval ((x + 1) / 2) by
    funext x
    rw [factorTwoForwardKP8CorrectionPolynomial_eval]]
  exact intervalIntegral_mul_shiftedPolynomial_eq_zero w hw hlow
    factorTwoForwardKP8CorrectionPolynomial
    factorTwoForwardKP8CorrectionPolynomial_natDegree_lt_nine

theorem integral_mul_factorTwoForwardLP8Correction_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1, w x * factorTwoForwardLP8Correction x) = 0 := by
  rw [show (fun x : ℝ ↦ w x * factorTwoForwardLP8Correction x) =
      fun x ↦ w x * factorTwoForwardLP8CorrectionPolynomial.eval ((x + 1) / 2) by
    funext x
    rw [factorTwoForwardLP8CorrectionPolynomial_eval]]
  exact intervalIntegral_mul_shiftedPolynomial_eq_zero w hw hlow
    factorTwoForwardLP8CorrectionPolynomial
    factorTwoForwardLP8CorrectionPolynomial_natDegree_lt_nine

/-- Against a nine-moment residual, the symmetric `P8` Hankel pairing is
exactly the reduced logarithmic pairing. -/
theorem integral_mul_factorTwoForwardHankelK_P8_eq_reduced
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1,
      w x * factorTwoForwardHankelK factorTwoCenteredP8 x) =
      ∫ x : ℝ in -1..1, w x * factorTwoForwardKP8 x := by
  have hred : IntervalIntegrable (fun x : ℝ ↦ w x * factorTwoForwardKP8 x)
      volume (-1) 1 :=
    (hw.continuousOn.mul continuousOn_factorTwoForwardKP8)
      |>.intervalIntegrable_of_Icc (by norm_num)
  have hcorr : IntervalIntegrable
      (fun x : ℝ ↦ w x * factorTwoForwardKP8Correction x) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold factorTwoForwardKP8Correction
    fun_prop
  calc
    (∫ x : ℝ in -1..1,
        w x * factorTwoForwardHankelK factorTwoCenteredP8 x) =
        ∫ x : ℝ in -1..1,
          w x * factorTwoForwardKP8 x +
            w x * factorTwoForwardKP8Correction x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (-1 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
      change w x * factorTwoForwardHankelK factorTwoCenteredP8 x =
        w x * factorTwoForwardKP8 x + w x * factorTwoForwardKP8Correction x
      rw [factorTwoForwardHankelK_P8_eq_reduced hx']
      ring
    _ = (∫ x : ℝ in -1..1, w x * factorTwoForwardKP8 x) +
        ∫ x : ℝ in -1..1, w x * factorTwoForwardKP8Correction x := by
      rw [intervalIntegral.integral_add hred hcorr]
    _ = _ := by
      rw [integral_mul_factorTwoForwardKP8Correction_eq_zero w hw hlow,
        add_zero]

/-- Against a nine-moment residual, the alternating `P8` Hankel pairing is
exactly the reduced logarithmic pairing. -/
theorem integral_mul_factorTwoForwardHankelL_P8_eq_reduced
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1,
      w x * factorTwoForwardHankelL factorTwoCenteredP8 x) =
      ∫ x : ℝ in -1..1, w x * factorTwoForwardLP8 x := by
  have hred : IntervalIntegrable (fun x : ℝ ↦ w x * factorTwoForwardLP8 x)
      volume (-1) 1 :=
    (hw.continuousOn.mul continuousOn_factorTwoForwardLP8)
      |>.intervalIntegrable_of_Icc (by norm_num)
  have hcorr : IntervalIntegrable
      (fun x : ℝ ↦ w x * factorTwoForwardLP8Correction x) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold factorTwoForwardLP8Correction
    fun_prop
  calc
    (∫ x : ℝ in -1..1,
        w x * factorTwoForwardHankelL factorTwoCenteredP8 x) =
        ∫ x : ℝ in -1..1,
          w x * factorTwoForwardLP8 x +
            w x * factorTwoForwardLP8Correction x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (-1 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
      change w x * factorTwoForwardHankelL factorTwoCenteredP8 x =
        w x * factorTwoForwardLP8 x + w x * factorTwoForwardLP8Correction x
      rw [factorTwoForwardHankelL_P8_eq_reduced hx']
      ring
    _ = (∫ x : ℝ in -1..1, w x * factorTwoForwardLP8 x) +
        ∫ x : ℝ in -1..1, w x * factorTwoForwardLP8Correction x := by
      rw [intervalIntegral.integral_add hred hcorr]
    _ = _ := by
      rw [integral_mul_factorTwoForwardLP8Correction_eq_zero w hw hlow,
        add_zero]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8ForwardReducedRepresenterBridgeStructural
