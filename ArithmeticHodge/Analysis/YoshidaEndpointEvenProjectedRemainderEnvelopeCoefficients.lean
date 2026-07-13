import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeMoments

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeCoefficients

open YoshidaConstantBounds
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenProjectedRemainderEnvelopeMoments
open YoshidaEndpointEvenProjectedRemainderEnvelopePolynomials
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound

noncomputable section

private abbrev A : ℝ := yoshidaEndpointA
private abbrev C0 : ℝ := yoshidaEndpointCoshMoment centeredEvenP0
private abbrev C2 : ℝ := yoshidaEndpointCoshMoment centeredEvenP2

/-- Constant coefficient of the constant-basis shifted envelope. -/
def projectedEnvelopeD00 : ℝ :=
  -883 / 480 - A / 2 + A ^ 2 / 48 + A ^ 3 / 48 -
    7 * A ^ 4 / 23040 - A ^ 5 / 768 +
    31 * A ^ 6 / 5806080 + 61 * A ^ 7 / 645120 + 2 * A * C0

/-- Quadratic coefficient of the constant-basis shifted envelope. -/
def projectedEnvelopeD01 : ℝ :=
  -35 / 32 + A ^ 2 / 48 + A ^ 3 / 16 -
    7 * A ^ 4 / 3840 - 5 * A ^ 5 / 384 +
    31 * A ^ 6 / 387072 + 61 * A ^ 7 / 30720 + A ^ 3 * C0 / 4

/-- Quartic coefficient of the constant-basis shifted envelope. -/
def projectedEnvelopeD02 : ℝ :=
  -7 * A ^ 4 / 23040 - 5 * A ^ 5 / 768 +
    31 * A ^ 6 / 387072 + 61 * A ^ 7 / 18432 + A ^ 5 * C0 / 192

/-- Sextic coefficient of the constant-basis shifted envelope. -/
def projectedEnvelopeD03 : ℝ :=
  31 * A ^ 6 / 5806080 + 61 * A ^ 7 / 92160 + A ^ 7 * C0 / 23040

/-- Constant coefficient of the degree-two-basis shifted envelope. -/
def projectedEnvelopeD20 : ℝ :=
  107 / 240 + A ^ 2 / 192 + A ^ 3 / 120 -
    7 * A ^ 4 / 46080 - A ^ 5 / 1344 +
    31 * A ^ 6 / 9289728 + 61 * A ^ 7 / 967680 + 2 * A * C2

/-- Quadratic coefficient of the degree-two-basis shifted envelope. -/
def projectedEnvelopeD21 : ℝ :=
  -71 / 40 - A ^ 2 / 96 - 7 * A ^ 4 / 15360 - A ^ 5 / 192 +
    31 * A ^ 6 / 774144 + 61 * A ^ 7 / 53760 + A ^ 3 * C2 / 4

/-- Quartic coefficient of the degree-two-basis shifted envelope. -/
def projectedEnvelopeD22 : ℝ :=
  A ^ 2 / 192 + 7 * A ^ 4 / 46080 +
    31 * A ^ 6 / 1548288 + 61 * A ^ 7 / 46080 + A ^ 5 * C2 / 192

/-- Sextic coefficient of the degree-two-basis shifted envelope. -/
def projectedEnvelopeD23 : ℝ :=
  -7 * A ^ 4 / 230400 - 31 * A ^ 6 / 11612160 + A ^ 7 * C2 / 23040

/-- Octic coefficient of the degree-two-basis shifted envelope. -/
def projectedEnvelopeD24 : ℝ := 31 * A ^ 6 / 108380160

/-- Coefficient presentation of the constant-basis polynomial envelope. -/
def shiftedRemainderPolynomial6_0_explicit (x : ℝ) : ℝ :=
  projectedEnvelopeD00 + projectedEnvelopeD01 * x ^ 2 +
    projectedEnvelopeD02 * x ^ 4 + projectedEnvelopeD03 * x ^ 6

/-- Coefficient presentation of the degree-two-basis polynomial envelope. -/
def shiftedRemainderPolynomial6_2_explicit (x : ℝ) : ℝ :=
  projectedEnvelopeD20 + projectedEnvelopeD21 * x ^ 2 +
    projectedEnvelopeD22 * x ^ 4 + projectedEnvelopeD23 * x ^ 6 +
    projectedEnvelopeD24 * x ^ 8

/-- The integral-defined constant envelope has the displayed four
coefficients on the endpoint interval. -/
theorem fixedProjectedShiftedRemainderPolynomial6_0_eq_explicit
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    fixedProjectedShiftedRemainderPolynomial6_0 x =
      shiftedRemainderPolynomial6_0_explicit x := by
  unfold fixedProjectedShiftedRemainderPolynomial6_0
    fixedProjectedSmoothRemainderPolynomial6_0
  rw [regularRepresenterPolynomial6_p0_eq hx]
  unfold shiftedRemainderPolynomial6_0_explicit projectedEnvelopeD00
    projectedEnvelopeD01 projectedEnvelopeD02 projectedEnvelopeD03
    regularRepresenterPolynomial6_0_explicit yoshidaEndpointCoshPolynomial6
  dsimp only [C0, A]
  ring

/-- The integral-defined degree-two envelope has the displayed five
coefficients on the endpoint interval. -/
theorem fixedProjectedShiftedRemainderPolynomial6_2_eq_explicit
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    fixedProjectedShiftedRemainderPolynomial6_2 x =
      shiftedRemainderPolynomial6_2_explicit x := by
  unfold fixedProjectedShiftedRemainderPolynomial6_2
    fixedProjectedSmoothRemainderPolynomial6_2
  rw [regularRepresenterPolynomial6_p2_eq hx]
  unfold shiftedRemainderPolynomial6_2_explicit projectedEnvelopeD20
    projectedEnvelopeD21 projectedEnvelopeD22 projectedEnvelopeD23
    projectedEnvelopeD24 regularRepresenterPolynomial6_2_explicit
    yoshidaEndpointCoshPolynomial6
  dsimp only [C2, A]
  ring

private theorem integral_coshPolynomial6_mul_p0 :
    (∫ x : ℝ in -1..1,
        yoshidaEndpointCoshPolynomial6 x * centeredEvenP0 x) =
      2 + A ^ 2 / 12 + A ^ 4 / 960 + A ^ 6 / 161280 := by
  unfold yoshidaEndpointCoshPolynomial6 centeredEvenP0
  rw [show (fun x : ℝ ↦
      (1 + A ^ 2 * x ^ 2 / 8 + A ^ 4 * x ^ 4 / 384 +
        A ^ 6 * x ^ 6 / 46080) * 1) =
      fun x ↦ 1 * x ^ 0 + A ^ 2 / 8 * x ^ 2 + A ^ 4 / 384 * x ^ 4 +
        A ^ 6 / 46080 * x ^ 6 by
    funext x
    ring]
  have h0 : IntervalIntegrable (fun x : ℝ ↦ x ^ 0) volume (-1) 1 :=
    (continuous_id.pow 0).intervalIntegrable (-1) 1
  have h2 : IntervalIntegrable (fun x : ℝ ↦ x ^ 2) volume (-1) 1 :=
    (continuous_id.pow 2).intervalIntegrable (-1) 1
  have h4 : IntervalIntegrable (fun x : ℝ ↦ x ^ 4) volume (-1) 1 :=
    (continuous_id.pow 4).intervalIntegrable (-1) 1
  have h6 : IntervalIntegrable (fun x : ℝ ↦ x ^ 6) volume (-1) 1 :=
    (continuous_id.pow 6).intervalIntegrable (-1) 1
  rw [intervalIntegral.integral_add
      (((h0.const_mul 1).add (h2.const_mul (A ^ 2 / 8))).add
        (h4.const_mul (A ^ 4 / 384)))
      (h6.const_mul (A ^ 6 / 46080)),
    intervalIntegral.integral_add
      ((h0.const_mul 1).add (h2.const_mul (A ^ 2 / 8)))
      (h4.const_mul (A ^ 4 / 384)),
    intervalIntegral.integral_add (h0.const_mul 1)
      (h2.const_mul (A ^ 2 / 8)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_pow, integral_pow, integral_pow, integral_pow]
  norm_num
  ring

private theorem integral_coshPolynomial6_mul_p2 :
    (∫ x : ℝ in -1..1,
        yoshidaEndpointCoshPolynomial6 x * centeredEvenP2 x) =
      A ^ 2 / 30 + A ^ 4 / 1680 + A ^ 6 / 241920 := by
  unfold yoshidaEndpointCoshPolynomial6 centeredEvenP2
  rw [show (fun x : ℝ ↦
      (1 + A ^ 2 * x ^ 2 / 8 + A ^ 4 * x ^ 4 / 384 +
        A ^ 6 * x ^ 6 / 46080) * ((3 * x ^ 2 - 1) / 2)) =
      fun x ↦ (-1 / 2 : ℝ) * x ^ 0 +
        (3 / 2 - A ^ 2 / 16) * x ^ 2 +
        (3 * A ^ 2 / 16 - A ^ 4 / 768) * x ^ 4 +
        (3 * A ^ 4 / 768 - A ^ 6 / 92160) * x ^ 6 +
        (3 * A ^ 6 / 92160) * x ^ 8 by
    funext x
    ring]
  have h0 : IntervalIntegrable (fun x : ℝ ↦ x ^ 0) volume (-1) 1 :=
    (continuous_id.pow 0).intervalIntegrable (-1) 1
  have h2 : IntervalIntegrable (fun x : ℝ ↦ x ^ 2) volume (-1) 1 :=
    (continuous_id.pow 2).intervalIntegrable (-1) 1
  have h4 : IntervalIntegrable (fun x : ℝ ↦ x ^ 4) volume (-1) 1 :=
    (continuous_id.pow 4).intervalIntegrable (-1) 1
  have h6 : IntervalIntegrable (fun x : ℝ ↦ x ^ 6) volume (-1) 1 :=
    (continuous_id.pow 6).intervalIntegrable (-1) 1
  have h8 : IntervalIntegrable (fun x : ℝ ↦ x ^ 8) volume (-1) 1 :=
    (continuous_id.pow 8).intervalIntegrable (-1) 1
  rw [intervalIntegral.integral_add
      ((((h0.const_mul (-1 / 2 : ℝ)).add
        (h2.const_mul (3 / 2 - A ^ 2 / 16))).add
        (h4.const_mul (3 * A ^ 2 / 16 - A ^ 4 / 768))).add
        (h6.const_mul (3 * A ^ 4 / 768 - A ^ 6 / 92160)))
      (h8.const_mul (3 * A ^ 6 / 92160)),
    intervalIntegral.integral_add
      (((h0.const_mul (-1 / 2 : ℝ)).add
        (h2.const_mul (3 / 2 - A ^ 2 / 16))).add
        (h4.const_mul (3 * A ^ 2 / 16 - A ^ 4 / 768)))
      (h6.const_mul (3 * A ^ 4 / 768 - A ^ 6 / 92160)),
    intervalIntegral.integral_add
      ((h0.const_mul (-1 / 2 : ℝ)).add
        (h2.const_mul (3 / 2 - A ^ 2 / 16)))
      (h4.const_mul (3 * A ^ 2 / 16 - A ^ 4 / 768)),
    intervalIntegral.integral_add (h0.const_mul (-1 / 2 : ℝ))
      (h2.const_mul (3 / 2 - A ^ 2 / 16)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_pow, integral_pow, integral_pow, integral_pow, integral_pow]
  norm_num
  ring

private theorem abs_coshMoment_p0_sub_polynomialMoment_lt :
    |C0 - (2 + A ^ 2 / 12 + A ^ 4 / 960 + A ^ 6 / 161280)| <
      (1 / 23000000000 : ℝ) := by
  have hcosh : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (A * x / 2) * centeredEvenP0 x)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredEvenP0
    fun_prop
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointCoshPolynomial6 x * centeredEvenP0 x)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredEvenP0 yoshidaEndpointCoshPolynomial6
    fun_prop
  have hEq :
      C0 - (2 + A ^ 2 / 12 + A ^ 4 / 960 + A ^ 6 / 161280) =
        ∫ x : ℝ in -1..1,
          (Real.cosh (A * x / 2) - yoshidaEndpointCoshPolynomial6 x) *
            centeredEvenP0 x := by
    dsimp only [C0, A]
    unfold yoshidaEndpointCoshMoment
    rw [← integral_coshPolynomial6_mul_p0,
      ← intervalIntegral.integral_sub hcosh hpoly]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hEq, ← Real.norm_eq_abs]
  calc
    ‖∫ x : ℝ in -1..1,
        (Real.cosh (A * x / 2) - yoshidaEndpointCoshPolynomial6 x) *
          centeredEvenP0 x‖ ≤
        (1 / 48000000000 : ℝ) * |(1 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hErr := abs_cosh_sub_yoshidaEndpointCoshPolynomial6_lt hxIcc
      rw [Real.norm_eq_abs, abs_mul]
      unfold centeredEvenP0
      norm_num
      exact hErr.le
    _ < (1 / 23000000000 : ℝ) := by norm_num

private theorem abs_coshMoment_p2_sub_polynomialMoment_lt :
    |C2 - (A ^ 2 / 30 + A ^ 4 / 1680 + A ^ 6 / 241920)| <
      (1 / 23000000000 : ℝ) := by
  have hcosh : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (A * x / 2) * centeredEvenP2 x)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredEvenP2
    fun_prop
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointCoshPolynomial6 x * centeredEvenP2 x)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredEvenP2 yoshidaEndpointCoshPolynomial6
    fun_prop
  have hEq :
      C2 - (A ^ 2 / 30 + A ^ 4 / 1680 + A ^ 6 / 241920) =
        ∫ x : ℝ in -1..1,
          (Real.cosh (A * x / 2) - yoshidaEndpointCoshPolynomial6 x) *
            centeredEvenP2 x := by
    dsimp only [C2, A]
    unfold yoshidaEndpointCoshMoment
    rw [← integral_coshPolynomial6_mul_p2,
      ← intervalIntegral.integral_sub hcosh hpoly]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hEq, ← Real.norm_eq_abs]
  calc
    ‖∫ x : ℝ in -1..1,
        (Real.cosh (A * x / 2) - yoshidaEndpointCoshPolynomial6 x) *
          centeredEvenP2 x‖ ≤
        (1 / 48000000000 : ℝ) * |(1 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hErr := abs_cosh_sub_yoshidaEndpointCoshPolynomial6_lt hxIcc
      have hxProd : 0 ≤ (x + 1) * (1 - x) :=
        mul_nonneg (by linarith [hxIcc.1]) (by linarith [hxIcc.2])
      have hxSq : x ^ 2 ≤ 1 := by nlinarith
      have hP2 : |centeredEvenP2 x| ≤ 1 := by
        unfold centeredEvenP2
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg x]
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |Real.cosh (A * x / 2) - yoshidaEndpointCoshPolynomial6 x| *
            |centeredEvenP2 x| ≤
            (1 / 48000000000 : ℝ) * 1 :=
          mul_le_mul hErr.le hP2 (abs_nonneg _) (by norm_num)
        _ = (1 / 48000000000 : ℝ) := by norm_num
    _ < (1 / 23000000000 : ℝ) := by norm_num

private theorem endpointA_fine_bounds :
    (69314718055 / 200000000000 : ℝ) < A ∧
      A < (69314718057 / 200000000000 : ℝ) := by
  dsimp only [A]
  unfold yoshidaEndpointA
  constructor <;> linarith [strict_log_two_fine_bounds.1,
    strict_log_two_fine_bounds.2]

private theorem endpointA_pow_fine_bounds (n : ℕ) (hn : n ≠ 0) :
    (69314718055 / 200000000000 : ℝ) ^ n < A ^ n ∧
      A ^ n < (69314718057 / 200000000000 : ℝ) ^ n := by
  constructor
  · exact pow_lt_pow_left₀ endpointA_fine_bounds.1 (by norm_num) hn
  · exact pow_lt_pow_left₀ endpointA_fine_bounds.2 yoshidaEndpointA_pos.le hn

/-- Coarse rational enclosure of the constant endpoint cosh moment.  Its
width is intentionally much larger than the Taylor remainder. -/
theorem coshMoment_p0_bounds :
    (2010024476 / 1000000000 : ℝ) < C0 ∧
      C0 < (2010024478 / 1000000000 : ℝ) := by
  rcases endpointA_pow_fine_bounds 2 (by norm_num) with ⟨h2l, h2u⟩
  rcases endpointA_pow_fine_bounds 4 (by norm_num) with ⟨h4l, h4u⟩
  rcases endpointA_pow_fine_bounds 6 (by norm_num) with ⟨h6l, h6u⟩
  rcases abs_lt.mp abs_coshMoment_p0_sub_polynomialMoment_lt with ⟨hErrL, hErrU⟩
  constructor <;> norm_num at h2l h2u h4l h4u h6l h6u hErrL hErrU ⊢ <;>
    linarith

/-- Coarse rational enclosure of the degree-two endpoint cosh moment. -/
theorem coshMoment_p2_bounds :
    (4012369 / 1000000000 : ℝ) < C2 ∧
      C2 < (4012371 / 1000000000 : ℝ) := by
  rcases endpointA_pow_fine_bounds 2 (by norm_num) with ⟨h2l, h2u⟩
  rcases endpointA_pow_fine_bounds 4 (by norm_num) with ⟨h4l, h4u⟩
  rcases endpointA_pow_fine_bounds 6 (by norm_num) with ⟨h6l, h6u⟩
  rcases abs_lt.mp abs_coshMoment_p2_sub_polynomialMoment_lt with ⟨hErrL, hErrU⟩
  constructor <;> norm_num at h2l h2u h4l h4u h6l h6u hErrL hErrU ⊢ <;>
    linarith

private theorem endpointA_pow_mul_coshMoment_p0_bounds
    (n : ℕ) (hn : n ≠ 0) :
    (69314718055 / 200000000000 : ℝ) ^ n * (2010024476 / 1000000000) <
        A ^ n * C0 ∧
      A ^ n * C0 <
        (69314718057 / 200000000000 : ℝ) ^ n * (2010024478 / 1000000000) := by
  rcases endpointA_pow_fine_bounds n hn with ⟨hAl, hAu⟩
  constructor
  · exact mul_lt_mul hAl coshMoment_p0_bounds.1.le (by norm_num)
      (pow_nonneg yoshidaEndpointA_pos.le n)
  · exact mul_lt_mul hAu coshMoment_p0_bounds.2.le
      ((by norm_num : (0 : ℝ) < 2010024476 / 1000000000).trans
        coshMoment_p0_bounds.1)
      (pow_nonneg (by norm_num) n)

private theorem endpointA_pow_mul_coshMoment_p2_bounds
    (n : ℕ) (hn : n ≠ 0) :
    (69314718055 / 200000000000 : ℝ) ^ n * (4012369 / 1000000000) <
        A ^ n * C2 ∧
      A ^ n * C2 <
        (69314718057 / 200000000000 : ℝ) ^ n * (4012371 / 1000000000) := by
  rcases endpointA_pow_fine_bounds n hn with ⟨hAl, hAu⟩
  constructor
  · exact mul_lt_mul hAl coshMoment_p2_bounds.1.le (by norm_num)
      (pow_nonneg yoshidaEndpointA_pos.le n)
  · exact mul_lt_mul hAu coshMoment_p2_bounds.2.le
      ((by norm_num : (0 : ℝ) < 4012369 / 1000000000).trans
        coshMoment_p2_bounds.1)
      (pow_nonneg (by norm_num) n)

/-- Rational box for the constant coefficient of the constant envelope. -/
theorem projectedEnvelopeD00_bounds :
    (-61626855 / 100000000 : ℝ) < projectedEnvelopeD00 ∧
      projectedEnvelopeD00 < (-61626854 / 100000000 : ℝ) := by
  rcases endpointA_fine_bounds with ⟨h1l, h1u⟩
  rcases endpointA_pow_fine_bounds 2 (by norm_num) with ⟨h2l, h2u⟩
  rcases endpointA_pow_fine_bounds 3 (by norm_num) with ⟨h3l, h3u⟩
  rcases endpointA_pow_fine_bounds 4 (by norm_num) with ⟨h4l, h4u⟩
  rcases endpointA_pow_fine_bounds 5 (by norm_num) with ⟨h5l, h5u⟩
  rcases endpointA_pow_fine_bounds 6 (by norm_num) with ⟨h6l, h6u⟩
  rcases endpointA_pow_fine_bounds 7 (by norm_num) with ⟨h7l, h7u⟩
  rcases endpointA_pow_mul_coshMoment_p0_bounds 1 (by norm_num) with
    ⟨hC0l, hC0u⟩
  unfold projectedEnvelopeD00
  constructor <;>
    norm_num at h1l h1u h2l h2u h3l h3u h4l h4u h5l h5u h6l h6u h7l h7u hC0l hC0u ⊢ <;>
    linarith

/-- Rational box for the quadratic coefficient of the constant envelope. -/
theorem projectedEnvelopeD01_bounds :
    (-106781760 / 100000000 : ℝ) < projectedEnvelopeD01 ∧
      projectedEnvelopeD01 < (-106781759 / 100000000 : ℝ) := by
  rcases endpointA_pow_fine_bounds 2 (by norm_num) with ⟨h2l, h2u⟩
  rcases endpointA_pow_fine_bounds 3 (by norm_num) with ⟨h3l, h3u⟩
  rcases endpointA_pow_fine_bounds 4 (by norm_num) with ⟨h4l, h4u⟩
  rcases endpointA_pow_fine_bounds 5 (by norm_num) with ⟨h5l, h5u⟩
  rcases endpointA_pow_fine_bounds 6 (by norm_num) with ⟨h6l, h6u⟩
  rcases endpointA_pow_fine_bounds 7 (by norm_num) with ⟨h7l, h7u⟩
  rcases endpointA_pow_mul_coshMoment_p0_bounds 3 (by norm_num) with
    ⟨hC0l, hC0u⟩
  unfold projectedEnvelopeD01
  constructor <;>
    norm_num at h2l h2u h3l h3u h4l h4u h5l h5u h6l h6u h7l h7u hC0l hC0u ⊢ <;>
    linarith

/-- Rational box for the quartic coefficient of the constant envelope. -/
theorem projectedEnvelopeD02_bounds :
    (1753 / 100000000 : ℝ) < projectedEnvelopeD02 ∧
      projectedEnvelopeD02 < (1754 / 100000000 : ℝ) := by
  rcases endpointA_pow_fine_bounds 4 (by norm_num) with ⟨h4l, h4u⟩
  rcases endpointA_pow_fine_bounds 5 (by norm_num) with ⟨h5l, h5u⟩
  rcases endpointA_pow_fine_bounds 6 (by norm_num) with ⟨h6l, h6u⟩
  rcases endpointA_pow_fine_bounds 7 (by norm_num) with ⟨h7l, h7u⟩
  rcases endpointA_pow_mul_coshMoment_p0_bounds 5 (by norm_num) with
    ⟨hC0l, hC0u⟩
  unfold projectedEnvelopeD02
  constructor <;>
    norm_num at h4l h4u h5l h5u h6l h6u h7l h7u hC0l hC0u ⊢ <;>
    linarith

/-- Rational box for the sextic coefficient of the constant envelope. -/
theorem projectedEnvelopeD03_bounds :
    (45 / 100000000 : ℝ) < projectedEnvelopeD03 ∧
      projectedEnvelopeD03 < (46 / 100000000 : ℝ) := by
  rcases endpointA_pow_fine_bounds 6 (by norm_num) with ⟨h6l, h6u⟩
  rcases endpointA_pow_fine_bounds 7 (by norm_num) with ⟨h7l, h7u⟩
  rcases endpointA_pow_mul_coshMoment_p0_bounds 7 (by norm_num) with
    ⟨hC0l, hC0u⟩
  unfold projectedEnvelopeD03
  constructor <;>
    norm_num at h6l h6u h7l h7u hC0l hC0u ⊢ <;>
    linarith

/-- Rational box for the constant coefficient of the degree-two envelope. -/
theorem projectedEnvelopeD20_bounds :
    (44958111 / 100000000 : ℝ) < projectedEnvelopeD20 ∧
      projectedEnvelopeD20 < (44958112 / 100000000 : ℝ) := by
  rcases endpointA_fine_bounds with ⟨h1l, h1u⟩
  rcases endpointA_pow_fine_bounds 2 (by norm_num) with ⟨h2l, h2u⟩
  rcases endpointA_pow_fine_bounds 3 (by norm_num) with ⟨h3l, h3u⟩
  rcases endpointA_pow_fine_bounds 4 (by norm_num) with ⟨h4l, h4u⟩
  rcases endpointA_pow_fine_bounds 5 (by norm_num) with ⟨h5l, h5u⟩
  rcases endpointA_pow_fine_bounds 6 (by norm_num) with ⟨h6l, h6u⟩
  rcases endpointA_pow_fine_bounds 7 (by norm_num) with ⟨h7l, h7u⟩
  rcases endpointA_pow_mul_coshMoment_p2_bounds 1 (by norm_num) with
    ⟨hC2l, hC2u⟩
  unfold projectedEnvelopeD20
  constructor <;>
    norm_num at h1l h1u h2l h2u h3l h3u h4l h4u h5l h5u h6l h6u h7l h7u hC2l hC2u ⊢ <;>
    linarith

/-- Rational box for the quadratic coefficient of the degree-two envelope. -/
theorem projectedEnvelopeD21_bounds :
    (-177624129 / 100000000 : ℝ) < projectedEnvelopeD21 ∧
      projectedEnvelopeD21 < (-177624128 / 100000000 : ℝ) := by
  rcases endpointA_pow_fine_bounds 2 (by norm_num) with ⟨h2l, h2u⟩
  rcases endpointA_pow_fine_bounds 3 (by norm_num) with ⟨h3l, h3u⟩
  rcases endpointA_pow_fine_bounds 4 (by norm_num) with ⟨h4l, h4u⟩
  rcases endpointA_pow_fine_bounds 5 (by norm_num) with ⟨h5l, h5u⟩
  rcases endpointA_pow_fine_bounds 6 (by norm_num) with ⟨h6l, h6u⟩
  rcases endpointA_pow_fine_bounds 7 (by norm_num) with ⟨h7l, h7u⟩
  rcases endpointA_pow_mul_coshMoment_p2_bounds 3 (by norm_num) with
    ⟨hC2l, hC2u⟩
  unfold projectedEnvelopeD21
  constructor <;>
    norm_num at h2l h2u h3l h3u h4l h4u h5l h5u h6l h6u h7l h7u hC2l hC2u ⊢ <;>
    linarith

/-- Rational box for the quartic coefficient of the degree-two envelope. -/
theorem projectedEnvelopeD22_bounds :
    (62871 / 100000000 : ℝ) < projectedEnvelopeD22 ∧
      projectedEnvelopeD22 < (62872 / 100000000 : ℝ) := by
  rcases endpointA_pow_fine_bounds 2 (by norm_num) with ⟨h2l, h2u⟩
  rcases endpointA_pow_fine_bounds 4 (by norm_num) with ⟨h4l, h4u⟩
  rcases endpointA_pow_fine_bounds 5 (by norm_num) with ⟨h5l, h5u⟩
  rcases endpointA_pow_fine_bounds 6 (by norm_num) with ⟨h6l, h6u⟩
  rcases endpointA_pow_fine_bounds 7 (by norm_num) with ⟨h7l, h7u⟩
  rcases endpointA_pow_mul_coshMoment_p2_bounds 5 (by norm_num) with
    ⟨hC2l, hC2u⟩
  unfold projectedEnvelopeD22
  constructor <;>
    norm_num at h2l h2u h4l h4u h5l h5u h6l h6u h7l h7u hC2l hC2u ⊢ <;>
    linarith

/-- Rational box for the sextic coefficient of the degree-two envelope. -/
theorem projectedEnvelopeD23_bounds :
    (-45 / 100000000 : ℝ) < projectedEnvelopeD23 ∧
      projectedEnvelopeD23 < (-44 / 100000000 : ℝ) := by
  rcases endpointA_pow_fine_bounds 4 (by norm_num) with ⟨h4l, h4u⟩
  rcases endpointA_pow_fine_bounds 6 (by norm_num) with ⟨h6l, h6u⟩
  rcases endpointA_pow_fine_bounds 7 (by norm_num) with ⟨h7l, h7u⟩
  rcases endpointA_pow_mul_coshMoment_p2_bounds 7 (by norm_num) with
    ⟨hC2l, hC2u⟩
  unfold projectedEnvelopeD23
  constructor <;>
    norm_num at h4l h4u h6l h6u h7l h7u hC2l hC2u ⊢ <;>
    linarith

/-- Rational box for the octic coefficient of the degree-two envelope. -/
theorem projectedEnvelopeD24_bounds :
    (0 : ℝ) < projectedEnvelopeD24 ∧
      projectedEnvelopeD24 < (1 / 100000000 : ℝ) := by
  rcases endpointA_pow_fine_bounds 6 (by norm_num) with ⟨h6l, h6u⟩
  unfold projectedEnvelopeD24
  constructor <;> norm_num at h6l h6u ⊢ <;> linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeCoefficients
