import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeGram
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderIntegrable

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeTrueGram

open YoshidaEndpointEvenAtanhReciprocalMajorant
open YoshidaEndpointEvenAtanhReciprocalMoments
open YoshidaEndpointEvenProjectedRemainderEnvelopeCoefficients
open YoshidaEndpointEvenProjectedRemainderEnvelopeGram
open YoshidaEndpointEvenProjectedRemainderEnvelopePolynomials
open YoshidaEndpointEvenProjectedRemainderIntegrable
open YoshidaEndpointEvenProjectedRemainderMoments

noncomputable section

/-- The true shifted constant remainder inherits the explicit polynomial
envelope error after coefficient evaluation. -/
theorem abs_fixedProjectedShiftedRemainder0_sub_explicit_lt
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |fixedProjectedShiftedRemainder0 x -
        shiftedRemainderPolynomial6_0_explicit x| <
      (1 / 720000 : ℝ) := by
  have h := abs_fixedProjectedShiftedRemainder0_sub_polynomial6_lt hx
  rw [fixedProjectedShiftedRemainderPolynomial6_0_eq_explicit hx] at h
  exact h

/-- The true shifted degree-two remainder inherits the explicit polynomial
envelope error after coefficient evaluation. -/
theorem abs_fixedProjectedShiftedRemainder2_sub_explicit_lt
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |fixedProjectedShiftedRemainder2 x -
        shiftedRemainderPolynomial6_2_explicit x| <
      (1 / 1800000 : ℝ) := by
  have h := abs_fixedProjectedShiftedRemainder2_sub_polynomial6_lt hx
  rw [fixedProjectedShiftedRemainderPolynomial6_2_eq_explicit hx] at h
  exact h

private theorem abs_trueGram00_sub_polynomialGram_lt :
    |fixedProjectedPolynomialRemainderGram00 -
        fixedProjectedEnvelopePolynomialGram00| < (1 / 70000 : ℝ) := by
  have htrue :=
    intervalIntegrable_fixedProjectedPolynomialRemainderGram00Integrand
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦ atanhTailWeightReciprocalMajorant x *
        shiftedRemainderPolynomial6_0_explicit x ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial
      shiftedRemainderPolynomial6_0_explicit
    fun_prop
  unfold fixedProjectedPolynomialRemainderGram00
    fixedProjectedEnvelopePolynomialGram00
  rw [← intervalIntegral.integral_sub htrue hpoly, ← Real.norm_eq_abs]
  calc
    ‖∫ x : ℝ in -1..1,
        atanhTailWeightReciprocalMajorant x *
            fixedProjectedShiftedRemainder0 x ^ 2 -
          atanhTailWeightReciprocalMajorant x *
            shiftedRemainderPolynomial6_0_explicit x ^ 2‖ ≤
        ((3 / 2 : ℝ) * (1 / 720000) *
          ((337 / 100 : ℝ) + 1 / 720000)) * |(1 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hU0 := atanhTailWeightReciprocalMajorant_nonneg_on_Icc hxIcc
      have hU := reciprocalMajorant_le_three_halves hxIcc
      have hd := abs_fixedProjectedShiftedRemainder0_sub_explicit_lt hxIcc
      have hP := abs_shiftedRemainderPolynomial6_0_explicit_lt hxIcc
      have hT : |fixedProjectedShiftedRemainder0 x| <
          (1 / 720000 : ℝ) + 337 / 200 := by
        calc
          |fixedProjectedShiftedRemainder0 x| =
              |(fixedProjectedShiftedRemainder0 x -
                  shiftedRemainderPolynomial6_0_explicit x) +
                shiftedRemainderPolynomial6_0_explicit x| := by
            congr 1
            ring
          _ ≤ |fixedProjectedShiftedRemainder0 x -
                shiftedRemainderPolynomial6_0_explicit x| +
              |shiftedRemainderPolynomial6_0_explicit x| := abs_add_le _ _
          _ < (1 / 720000 : ℝ) + 337 / 200 := add_lt_add hd hP
      have hsum :
          |fixedProjectedShiftedRemainder0 x +
              shiftedRemainderPolynomial6_0_explicit x| <
            (337 / 100 : ℝ) + 1 / 720000 := by
        exact (abs_add_le _ _).trans_lt (by
          norm_num at hT hP ⊢
          linarith)
      have hsq :
          |fixedProjectedShiftedRemainder0 x ^ 2 -
              shiftedRemainderPolynomial6_0_explicit x ^ 2| ≤
            (1 / 720000 : ℝ) * ((337 / 100 : ℝ) + 1 / 720000) := by
        rw [sq_sub_sq, abs_mul]
        calc
          |fixedProjectedShiftedRemainder0 x +
                shiftedRemainderPolynomial6_0_explicit x| *
              |fixedProjectedShiftedRemainder0 x -
                shiftedRemainderPolynomial6_0_explicit x| ≤
              ((337 / 100 : ℝ) + 1 / 720000) *
                |fixedProjectedShiftedRemainder0 x -
                  shiftedRemainderPolynomial6_0_explicit x| :=
            mul_le_mul_of_nonneg_right hsum.le (abs_nonneg _)
          _ ≤ ((337 / 100 : ℝ) + 1 / 720000) * (1 / 720000) :=
            mul_le_mul_of_nonneg_left hd.le (by norm_num)
          _ = _ := by ring
      rw [show atanhTailWeightReciprocalMajorant x *
                fixedProjectedShiftedRemainder0 x ^ 2 -
              atanhTailWeightReciprocalMajorant x *
                shiftedRemainderPolynomial6_0_explicit x ^ 2 =
            atanhTailWeightReciprocalMajorant x *
              (fixedProjectedShiftedRemainder0 x ^ 2 -
                shiftedRemainderPolynomial6_0_explicit x ^ 2) by ring,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg hU0]
      calc
        atanhTailWeightReciprocalMajorant x *
            |fixedProjectedShiftedRemainder0 x ^ 2 -
              shiftedRemainderPolynomial6_0_explicit x ^ 2| ≤
            (3 / 2 : ℝ) *
              |fixedProjectedShiftedRemainder0 x ^ 2 -
                shiftedRemainderPolynomial6_0_explicit x ^ 2| := by gcongr
        _ ≤ (3 / 2 : ℝ) *
            ((1 / 720000 : ℝ) * ((337 / 100 : ℝ) + 1 / 720000)) := by
          gcongr
        _ = (3 / 2 : ℝ) * (1 / 720000) *
            ((337 / 100 : ℝ) + 1 / 720000) := by ring
    _ < (1 / 70000 : ℝ) := by norm_num

private theorem abs_trueGram02_sub_polynomialGram_lt :
    |fixedProjectedPolynomialRemainderGram02 -
        fixedProjectedEnvelopePolynomialGram02| < (1 / 80000 : ℝ) := by
  have htrue :=
    intervalIntegrable_fixedProjectedPolynomialRemainderGram02Integrand
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦ atanhTailWeightReciprocalMajorant x *
        shiftedRemainderPolynomial6_0_explicit x *
          shiftedRemainderPolynomial6_2_explicit x) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial
      shiftedRemainderPolynomial6_0_explicit
      shiftedRemainderPolynomial6_2_explicit
    fun_prop
  unfold fixedProjectedPolynomialRemainderGram02
    fixedProjectedEnvelopePolynomialGram02
  rw [← intervalIntegral.integral_sub htrue hpoly, ← Real.norm_eq_abs]
  calc
    ‖∫ x : ℝ in -1..1,
        atanhTailWeightReciprocalMajorant x *
                fixedProjectedShiftedRemainder0 x *
              fixedProjectedShiftedRemainder2 x -
          atanhTailWeightReciprocalMajorant x *
                shiftedRemainderPolynomial6_0_explicit x *
              shiftedRemainderPolynomial6_2_explicit x‖ ≤
        ((3 / 2 : ℝ) *
          ((1 / 720000 : ℝ) * ((223 / 100 : ℝ) + 1 / 1800000) +
            (337 / 200 : ℝ) * (1 / 1800000))) * |(1 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hU0 := atanhTailWeightReciprocalMajorant_nonneg_on_Icc hxIcc
      have hU := reciprocalMajorant_le_three_halves hxIcc
      have hd0 := abs_fixedProjectedShiftedRemainder0_sub_explicit_lt hxIcc
      have hd2 := abs_fixedProjectedShiftedRemainder2_sub_explicit_lt hxIcc
      have hP0 := abs_shiftedRemainderPolynomial6_0_explicit_lt hxIcc
      have hP2 := abs_shiftedRemainderPolynomial6_2_explicit_lt hxIcc
      have hT2 : |fixedProjectedShiftedRemainder2 x| <
          (1 / 1800000 : ℝ) + 223 / 100 := by
        calc
          |fixedProjectedShiftedRemainder2 x| =
              |(fixedProjectedShiftedRemainder2 x -
                  shiftedRemainderPolynomial6_2_explicit x) +
                shiftedRemainderPolynomial6_2_explicit x| := by
            congr 1
            ring
          _ ≤ |fixedProjectedShiftedRemainder2 x -
                shiftedRemainderPolynomial6_2_explicit x| +
              |shiftedRemainderPolynomial6_2_explicit x| := abs_add_le _ _
          _ < (1 / 1800000 : ℝ) + 223 / 100 := add_lt_add hd2 hP2
      have hfirst :
          |(fixedProjectedShiftedRemainder0 x -
              shiftedRemainderPolynomial6_0_explicit x) *
              fixedProjectedShiftedRemainder2 x| ≤
            (1 / 720000 : ℝ) * ((223 / 100 : ℝ) + 1 / 1800000) := by
        rw [abs_mul]
        calc
          |fixedProjectedShiftedRemainder0 x -
                shiftedRemainderPolynomial6_0_explicit x| *
              |fixedProjectedShiftedRemainder2 x| ≤
              (1 / 720000 : ℝ) * |fixedProjectedShiftedRemainder2 x| :=
            mul_le_mul_of_nonneg_right hd0.le (abs_nonneg _)
          _ ≤ (1 / 720000 : ℝ) * ((223 / 100 : ℝ) + 1 / 1800000) :=
            mul_le_mul_of_nonneg_left (by linarith [hT2]) (by norm_num)
      have hsecond :
          |shiftedRemainderPolynomial6_0_explicit x *
              (fixedProjectedShiftedRemainder2 x -
                shiftedRemainderPolynomial6_2_explicit x)| ≤
            (337 / 200 : ℝ) * (1 / 1800000) := by
        rw [abs_mul]
        calc
          |shiftedRemainderPolynomial6_0_explicit x| *
              |fixedProjectedShiftedRemainder2 x -
                shiftedRemainderPolynomial6_2_explicit x| ≤
              (337 / 200 : ℝ) *
                |fixedProjectedShiftedRemainder2 x -
                  shiftedRemainderPolynomial6_2_explicit x| :=
            mul_le_mul_of_nonneg_right hP0.le (abs_nonneg _)
          _ ≤ (337 / 200 : ℝ) * (1 / 1800000) :=
            mul_le_mul_of_nonneg_left hd2.le (by norm_num)
      have hprod :
          |fixedProjectedShiftedRemainder0 x * fixedProjectedShiftedRemainder2 x -
              shiftedRemainderPolynomial6_0_explicit x *
                shiftedRemainderPolynomial6_2_explicit x| ≤
            (1 / 720000 : ℝ) * ((223 / 100 : ℝ) + 1 / 1800000) +
              (337 / 200 : ℝ) * (1 / 1800000) := by
        rw [show fixedProjectedShiftedRemainder0 x *
                fixedProjectedShiftedRemainder2 x -
              shiftedRemainderPolynomial6_0_explicit x *
                shiftedRemainderPolynomial6_2_explicit x =
            (fixedProjectedShiftedRemainder0 x -
                shiftedRemainderPolynomial6_0_explicit x) *
                fixedProjectedShiftedRemainder2 x +
              shiftedRemainderPolynomial6_0_explicit x *
                (fixedProjectedShiftedRemainder2 x -
                  shiftedRemainderPolynomial6_2_explicit x) by ring]
        exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)
      rw [show
          atanhTailWeightReciprocalMajorant x *
                  fixedProjectedShiftedRemainder0 x *
                fixedProjectedShiftedRemainder2 x -
              atanhTailWeightReciprocalMajorant x *
                  shiftedRemainderPolynomial6_0_explicit x *
                shiftedRemainderPolynomial6_2_explicit x =
            atanhTailWeightReciprocalMajorant x *
              (fixedProjectedShiftedRemainder0 x *
                  fixedProjectedShiftedRemainder2 x -
                shiftedRemainderPolynomial6_0_explicit x *
                  shiftedRemainderPolynomial6_2_explicit x) by ring,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg hU0]
      calc
        atanhTailWeightReciprocalMajorant x *
            |fixedProjectedShiftedRemainder0 x *
                  fixedProjectedShiftedRemainder2 x -
                shiftedRemainderPolynomial6_0_explicit x *
                  shiftedRemainderPolynomial6_2_explicit x| ≤
            (3 / 2 : ℝ) *
              |fixedProjectedShiftedRemainder0 x *
                  fixedProjectedShiftedRemainder2 x -
                shiftedRemainderPolynomial6_0_explicit x *
                  shiftedRemainderPolynomial6_2_explicit x| := by gcongr
        _ ≤ (3 / 2 : ℝ) *
            ((1 / 720000 : ℝ) * ((223 / 100 : ℝ) + 1 / 1800000) +
              (337 / 200 : ℝ) * (1 / 1800000)) := by gcongr
    _ < (1 / 80000 : ℝ) := by norm_num

private theorem abs_trueGram22_sub_polynomialGram_lt :
    |fixedProjectedPolynomialRemainderGram22 -
        fixedProjectedEnvelopePolynomialGram22| < (1 / 130000 : ℝ) := by
  have htrue :=
    intervalIntegrable_fixedProjectedPolynomialRemainderGram22Integrand
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦ atanhTailWeightReciprocalMajorant x *
        shiftedRemainderPolynomial6_2_explicit x ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial
      shiftedRemainderPolynomial6_2_explicit
    fun_prop
  unfold fixedProjectedPolynomialRemainderGram22
    fixedProjectedEnvelopePolynomialGram22
  rw [← intervalIntegral.integral_sub htrue hpoly, ← Real.norm_eq_abs]
  calc
    ‖∫ x : ℝ in -1..1,
        atanhTailWeightReciprocalMajorant x *
            fixedProjectedShiftedRemainder2 x ^ 2 -
          atanhTailWeightReciprocalMajorant x *
            shiftedRemainderPolynomial6_2_explicit x ^ 2‖ ≤
        ((3 / 2 : ℝ) * (1 / 1800000) *
          ((223 / 50 : ℝ) + 1 / 1800000)) * |(1 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hU0 := atanhTailWeightReciprocalMajorant_nonneg_on_Icc hxIcc
      have hU := reciprocalMajorant_le_three_halves hxIcc
      have hd := abs_fixedProjectedShiftedRemainder2_sub_explicit_lt hxIcc
      have hP := abs_shiftedRemainderPolynomial6_2_explicit_lt hxIcc
      have hT : |fixedProjectedShiftedRemainder2 x| <
          (1 / 1800000 : ℝ) + 223 / 100 := by
        calc
          |fixedProjectedShiftedRemainder2 x| =
              |(fixedProjectedShiftedRemainder2 x -
                  shiftedRemainderPolynomial6_2_explicit x) +
                shiftedRemainderPolynomial6_2_explicit x| := by
            congr 1
            ring
          _ ≤ |fixedProjectedShiftedRemainder2 x -
                shiftedRemainderPolynomial6_2_explicit x| +
              |shiftedRemainderPolynomial6_2_explicit x| := abs_add_le _ _
          _ < (1 / 1800000 : ℝ) + 223 / 100 := add_lt_add hd hP
      have hsum :
          |fixedProjectedShiftedRemainder2 x +
              shiftedRemainderPolynomial6_2_explicit x| <
            (223 / 50 : ℝ) + 1 / 1800000 := by
        exact (abs_add_le _ _).trans_lt (by
          norm_num at hT hP ⊢
          linarith)
      have hsq :
          |fixedProjectedShiftedRemainder2 x ^ 2 -
              shiftedRemainderPolynomial6_2_explicit x ^ 2| ≤
            (1 / 1800000 : ℝ) * ((223 / 50 : ℝ) + 1 / 1800000) := by
        rw [sq_sub_sq, abs_mul]
        calc
          |fixedProjectedShiftedRemainder2 x +
                shiftedRemainderPolynomial6_2_explicit x| *
              |fixedProjectedShiftedRemainder2 x -
                shiftedRemainderPolynomial6_2_explicit x| ≤
              ((223 / 50 : ℝ) + 1 / 1800000) *
                |fixedProjectedShiftedRemainder2 x -
                  shiftedRemainderPolynomial6_2_explicit x| :=
            mul_le_mul_of_nonneg_right hsum.le (abs_nonneg _)
          _ ≤ ((223 / 50 : ℝ) + 1 / 1800000) * (1 / 1800000) :=
            mul_le_mul_of_nonneg_left hd.le (by norm_num)
          _ = _ := by ring
      rw [show atanhTailWeightReciprocalMajorant x *
                fixedProjectedShiftedRemainder2 x ^ 2 -
              atanhTailWeightReciprocalMajorant x *
                shiftedRemainderPolynomial6_2_explicit x ^ 2 =
            atanhTailWeightReciprocalMajorant x *
              (fixedProjectedShiftedRemainder2 x ^ 2 -
                shiftedRemainderPolynomial6_2_explicit x ^ 2) by ring,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg hU0]
      calc
        atanhTailWeightReciprocalMajorant x *
            |fixedProjectedShiftedRemainder2 x ^ 2 -
              shiftedRemainderPolynomial6_2_explicit x ^ 2| ≤
            (3 / 2 : ℝ) *
              |fixedProjectedShiftedRemainder2 x ^ 2 -
                shiftedRemainderPolynomial6_2_explicit x ^ 2| := by gcongr
        _ ≤ (3 / 2 : ℝ) *
            ((1 / 1800000 : ℝ) * ((223 / 50 : ℝ) + 1 / 1800000)) := by
          gcongr
        _ = (3 / 2 : ℝ) * (1 / 1800000) *
            ((223 / 50 : ℝ) + 1 / 1800000) := by ring
    _ < (1 / 130000 : ℝ) := by norm_num

/-- Upper bound for the true constant polynomial-remainder Gram entry. -/
theorem fixedProjectedPolynomialRemainderGram00_lt :
    fixedProjectedPolynomialRemainderGram00 < (39713 / 20000 : ℝ) := by
  have hp := fixedProjectedEnvelopePolynomialGram00_bounds.2
  have he := (abs_lt.mp abs_trueGram00_sub_polynomialGram_lt).2
  norm_num at hp he ⊢
  linarith

/-- Two-sided bound for the true mixed polynomial-remainder Gram entry. -/
theorem fixedProjectedPolynomialRemainderGram02_bounds :
    (7891 / 25000 : ℝ) < fixedProjectedPolynomialRemainderGram02 ∧
      fixedProjectedPolynomialRemainderGram02 < (1973 / 6250 : ℝ) := by
  have hp := fixedProjectedEnvelopePolynomialGram02_bounds
  have he := abs_lt.mp abs_trueGram02_sub_polynomialGram_lt
  constructor <;> norm_num at hp he ⊢ <;> linarith

/-- Upper bound for the true degree-two polynomial-remainder Gram entry. -/
theorem fixedProjectedPolynomialRemainderGram22_lt :
    fixedProjectedPolynomialRemainderGram22 < (49551 / 100000 : ℝ) := by
  have hp := fixedProjectedEnvelopePolynomialGram22_bounds.2
  have he := (abs_lt.mp abs_trueGram22_sub_polynomialGram_lt).2
  norm_num at hp he ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeTrueGram
