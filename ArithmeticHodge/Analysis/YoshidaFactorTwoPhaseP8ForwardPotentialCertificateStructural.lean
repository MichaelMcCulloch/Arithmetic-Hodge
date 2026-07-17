import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8StructuralReserve
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePotentialWeightedMomentGapStructural
import Mathlib.Analysis.Calculus.DSlope

set_option autoImplicit false

open Filter Finset MeasureTheory Polynomial Real Set
open scoped Topology

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8ForwardPotentialCertificateStructural

open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseP8StructuralReserve
open YoshidaFactorTwoPhasePotentialWeightedMomentGapStructural

noncomputable section

/-!
# A potential-charged forward certificate for centered `P8`

The alternating forward representer of centered `P8` vanishes at the
center.  After subtracting one explicit degree-seven polynomial, its quotient
by the centered coordinate has very small `L²([-1,1])` mass.  This file
certifies that mass by a finite logarithmic Taylor polynomial and one uniform
geometric remainder.  No phase points or spectral tail modes are sampled.
-/

/-- Clamp to the centered interval.  It is used only to make the removable
logarithmic quotients globally continuous; it is the identity on `[-1,1]`. -/
def centeredClamp (x : ℝ) : ℝ := max (-1) (min 1 x)

theorem centeredClamp_eq_self {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    centeredClamp x = x := by
  unfold centeredClamp
  rw [min_eq_right hx.2, max_eq_right hx.1]

theorem centeredClamp_mem (x : ℝ) : centeredClamp x ∈ Icc (-1 : ℝ) 1 := by
  unfold centeredClamp
  constructor <;> simp

theorem continuous_centeredClamp : Continuous centeredClamp := by
  unfold centeredClamp
  fun_prop

/-- The nonconstant logarithm on the right side of the centered triangle. -/
def p8LogMinus (x : ℝ) : ℝ := Real.log (1 - x / 3)

/-- The nonconstant logarithm on the left side of the centered triangle. -/
def p8LogPlus (x : ℝ) : ℝ := Real.log (1 + x / 3)

/-- Globally continuous removable quotient of `log (1 - x/3)` by `x`. -/
def p8LogMinusSlope (x : ℝ) : ℝ :=
  dslope p8LogMinus 0 (centeredClamp x)

/-- Globally continuous removable quotient of `log (1 + x/3)` by `x`. -/
def p8LogPlusSlope (x : ℝ) : ℝ :=
  dslope p8LogPlus 0 (centeredClamp x)

private theorem continuousOn_p8LogMinus :
    ContinuousOn p8LogMinus (Icc (-1 : ℝ) 1) := by
  intro x hx
  have hne : 1 - x / 3 ≠ 0 := by linarith [hx.2]
  have hinner : HasDerivAt (fun y : ℝ ↦ 1 - y / 3) (-(1 / 3 : ℝ)) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub
      ((hasDerivAt_id x).div_const 3) using 1
    all_goals norm_num
  simpa only [p8LogMinus] using
    ((Real.hasDerivAt_log hne).comp x hinner).continuousAt.continuousWithinAt

private theorem continuousOn_p8LogPlus :
    ContinuousOn p8LogPlus (Icc (-1 : ℝ) 1) := by
  intro x hx
  have hne : 1 + x / 3 ≠ 0 := by linarith [hx.1]
  have hinner : HasDerivAt (fun y : ℝ ↦ 1 + y / 3) (1 / 3 : ℝ) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add
      ((hasDerivAt_id x).div_const 3) using 1
    all_goals norm_num
  simpa only [p8LogPlus] using
    ((Real.hasDerivAt_log hne).comp x hinner).continuousAt.continuousWithinAt

private theorem differentiableAt_p8LogMinus_zero :
    DifferentiableAt ℝ p8LogMinus 0 := by
  have hinner : HasDerivAt (fun y : ℝ ↦ 1 - y / 3) (-(1 / 3 : ℝ)) 0 := by
    convert (hasDerivAt_const 0 (1 : ℝ)).sub
      ((hasDerivAt_id (0 : ℝ)).div_const 3) using 1
    all_goals norm_num
  have hne : 1 - (0 : ℝ) / 3 ≠ 0 := by norm_num
  simpa only [p8LogMinus] using
    ((Real.hasDerivAt_log hne).comp 0 hinner).differentiableAt

private theorem differentiableAt_p8LogPlus_zero :
    DifferentiableAt ℝ p8LogPlus 0 := by
  have hinner : HasDerivAt (fun y : ℝ ↦ 1 + y / 3) (1 / 3 : ℝ) 0 := by
    convert (hasDerivAt_const 0 (1 : ℝ)).add
      ((hasDerivAt_id (0 : ℝ)).div_const 3) using 1
    all_goals norm_num
  have hne : 1 + (0 : ℝ) / 3 ≠ 0 := by norm_num
  simpa only [p8LogPlus] using
    ((Real.hasDerivAt_log hne).comp 0 hinner).differentiableAt

private theorem centeredIcc_mem_nhds_zero :
    Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := by
  exact mem_of_superset (Ioo_mem_nhds (by norm_num) (by norm_num)) Ioo_subset_Icc_self

private theorem continuousOn_p8LogMinus_dslope :
    ContinuousOn (dslope p8LogMinus 0) (Icc (-1 : ℝ) 1) :=
  (continuousOn_dslope centeredIcc_mem_nhds_zero).2
    ⟨continuousOn_p8LogMinus, differentiableAt_p8LogMinus_zero⟩

private theorem continuousOn_p8LogPlus_dslope :
    ContinuousOn (dslope p8LogPlus 0) (Icc (-1 : ℝ) 1) :=
  (continuousOn_dslope centeredIcc_mem_nhds_zero).2
    ⟨continuousOn_p8LogPlus, differentiableAt_p8LogPlus_zero⟩

theorem continuous_p8LogMinusSlope : Continuous p8LogMinusSlope := by
  rw [← continuousOn_univ]
  exact continuousOn_p8LogMinus_dslope.comp
    continuous_centeredClamp.continuousOn (fun x _hx ↦ centeredClamp_mem x)

theorem continuous_p8LogPlusSlope : Continuous p8LogPlusSlope := by
  rw [← continuousOn_univ]
  exact continuousOn_p8LogPlus_dslope.comp
    continuous_centeredClamp.continuousOn (fun x _hx ↦ centeredClamp_mem x)

/-- The reduced alternating forward logarithmic representer for centered
`P8`.  A separate representer bridge can identify this with the Hankel
integral modulo its degree-seven polynomial correction. -/
def factorTwoForwardLP8 (x : ℝ) : ℝ :=
  factorTwoCenteredP8 (x - 2) * Real.log ((3 - x) / 2) -
    factorTwoCenteredP8 (x + 2) * Real.log ((3 + x) / 2)

/-- Rational odd part of the optimized subtraction polynomial. -/
def factorTwoForwardP8PotentialOddPolynomial (x : ℝ) : ℝ :=
  -(5127402116194 / 1000000000 : ℝ) * x -
    (42189553091957 / 1000000000 : ℝ) * x ^ 3 -
    (26919913472844 / 1000000000 : ℝ) * x ^ 5 -
    (2208895602146 / 1000000000 : ℝ) * x ^ 7

/-- Quotient of the rational odd subtraction polynomial by `x`. -/
def factorTwoForwardP8PotentialOddQuotient (x : ℝ) : ℝ :=
  -(5127402116194 / 1000000000 : ℝ) -
    (42189553091957 / 1000000000 : ℝ) * x ^ 2 -
    (26919913472844 / 1000000000 : ℝ) * x ^ 4 -
    (2208895602146 / 1000000000 : ℝ) * x ^ 6

/-- Full degree-seven subtraction polynomial.  Its transcendental coefficient
is the constant logarithm common to both endpoint factors. -/
def factorTwoForwardP8PotentialPolynomial (x : ℝ) : ℝ :=
  Real.log (3 / 2 : ℝ) *
      (factorTwoCenteredP8 (x - 2) - factorTwoCenteredP8 (x + 2)) +
    factorTwoForwardP8PotentialOddPolynomial x

/-- Continuous quotient left after removing the degree-seven polynomial. -/
def factorTwoForwardP8PotentialQuotient (x : ℝ) : ℝ :=
  factorTwoCenteredP8 (x - 2) * p8LogMinusSlope x -
    factorTwoCenteredP8 (x + 2) * p8LogPlusSlope x -
    factorTwoForwardP8PotentialOddQuotient x

theorem continuous_factorTwoForwardP8PotentialQuotient :
    Continuous factorTwoForwardP8PotentialQuotient := by
  unfold factorTwoForwardP8PotentialQuotient
    factorTwoForwardP8PotentialOddQuotient
  exact (((continuous_factorTwoCenteredP8.comp (by fun_prop)).mul
    continuous_p8LogMinusSlope).sub
      ((continuous_factorTwoCenteredP8.comp (by fun_prop)).mul
        continuous_p8LogPlusSlope)).sub (by fun_prop)

theorem mul_p8LogMinusSlope_eq
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    x * p8LogMinusSlope x = p8LogMinus x := by
  unfold p8LogMinusSlope
  rw [centeredClamp_eq_self hx]
  have h := sub_smul_dslope p8LogMinus 0 x
  simpa only [sub_zero, zero_smul, sub_zero, smul_eq_mul, p8LogMinus,
    zero_div, Real.log_one] using h

theorem mul_p8LogPlusSlope_eq
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    x * p8LogPlusSlope x = p8LogPlus x := by
  unfold p8LogPlusSlope
  rw [centeredClamp_eq_self hx]
  have h := sub_smul_dslope p8LogPlus 0 x
  simpa only [sub_zero, zero_smul, sub_zero, smul_eq_mul, p8LogPlus,
    zero_div, add_zero, Real.log_one] using h

/-- The degree-seven subtraction as a polynomial in the shifted coordinate. -/
def p8CenteredCoordinatePolynomial : ℝ[X] :=
  Polynomial.C 2 * Polynomial.X - Polynomial.C 1

def factorTwoForwardP8PotentialShiftedPolynomial : ℝ[X] :=
  Polynomial.C
      (-(281241 / 4 : ℝ) * Real.log (3 / 2 : ℝ) -
        (5127402116194 / 1000000000 : ℝ)) *
      p8CenteredCoordinatePolynomial +
    Polynomial.C
      (-(604065 / 4 : ℝ) * Real.log (3 / 2 : ℝ) -
        (42189553091957 / 1000000000 : ℝ)) *
      p8CenteredCoordinatePolynomial ^ 3 +
    Polynomial.C
      (-(171171 / 4 : ℝ) * Real.log (3 / 2 : ℝ) -
        (26919913472844 / 1000000000 : ℝ)) *
      p8CenteredCoordinatePolynomial ^ 5 +
    Polynomial.C
      (-(6435 / 4 : ℝ) * Real.log (3 / 2 : ℝ) -
        (2208895602146 / 1000000000 : ℝ)) *
      p8CenteredCoordinatePolynomial ^ 7

@[simp] theorem factorTwoForwardP8PotentialShiftedPolynomial_eval (x : ℝ) :
    factorTwoForwardP8PotentialShiftedPolynomial.eval ((x + 1) / 2) =
      factorTwoForwardP8PotentialPolynomial x := by
  simp only [factorTwoForwardP8PotentialShiftedPolynomial,
    p8CenteredCoordinatePolynomial, eval_add, eval_sub, eval_mul, eval_C,
    eval_X, eval_pow]
  unfold factorTwoForwardP8PotentialPolynomial
    factorTwoForwardP8PotentialOddPolynomial
  rw [factorTwoCenteredP8_eq, factorTwoCenteredP8_eq]
  ring

theorem factorTwoForwardP8PotentialShiftedPolynomial_natDegree_lt_nine :
    factorTwoForwardP8PotentialShiftedPolynomial.natDegree < 9 := by
  unfold factorTwoForwardP8PotentialShiftedPolynomial
    p8CenteredCoordinatePolynomial
  compute_degree
  norm_num

/-- Exact centered-coordinate factorization of the reduced `P8` alternating
representer after the optimized degree-seven subtraction. -/
theorem factorTwoForwardLP8_eq_polynomial_add_centeredFactor
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardLP8 x =
      factorTwoForwardP8PotentialPolynomial x +
        x * factorTwoForwardP8PotentialQuotient x := by
  have hminus :
      Real.log ((3 - x) / 2) =
        Real.log (3 / 2 : ℝ) + p8LogMinus x := by
    rw [show (3 - x) / 2 = (3 / 2 : ℝ) * (1 - x / 3) by ring,
      Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0)
        (by linarith [hx.2] : 1 - x / 3 ≠ 0)]
    rfl
  have hplus :
      Real.log ((3 + x) / 2) =
        Real.log (3 / 2 : ℝ) + p8LogPlus x := by
    rw [show (3 + x) / 2 = (3 / 2 : ℝ) * (1 + x / 3) by ring,
      Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0)
        (by linarith [hx.1] : 1 + x / 3 ≠ 0)]
    rfl
  rw [factorTwoForwardLP8, hminus, hplus,
    factorTwoForwardP8PotentialPolynomial,
    factorTwoForwardP8PotentialQuotient,
    ← mul_p8LogMinusSlope_eq hx, ← mul_p8LogPlusSlope_eq hx]
  unfold factorTwoForwardP8PotentialOddPolynomial
    factorTwoForwardP8PotentialOddQuotient
  ring

/-! ## Sixteen-term logarithmic certificate -/

/-- The first sixteen terms of `log (1-z)`. -/
def p8LogOneSubTaylorSixteen (z : ℝ) : ℝ :=
  -∑ i ∈ Finset.range 16, z ^ (i + 1) / (i + 1 : ℝ)

/-- The quotient polynomial obtained after multiplying the two logarithmic
Taylor polynomials by the shifted copies of `P8` and dividing by `x`. -/
def factorTwoForwardP8TaylorQuotient (x : ℝ) : ℝ :=
  -(984467 / 192 : ℝ) -
    (218705015 / 5184 : ℝ) * x ^ 2 -
    (2093756357 / 77760 : ℝ) * x ^ 4 -
    (2154110897 / 979776 : ℝ) * x ^ 6 -
    (31164787 / 5668704 : ℝ) * x ^ 8 -
    (656359 / 28343520 : ℝ) * x ^ 10 -
    (2853731 / 7295622048 : ℝ) * x ^ 12 -
    (1466741 / 125352051552 : ℝ) * x ^ 14 +
    (12979 / 1989715104 : ℝ) * x ^ 16 +
    (12241 / 229582512 : ℝ) * x ^ 18 +
    (479809 / 16070775840 : ℝ) * x ^ 20 +
    (143 / 76527504 : ℝ) * x ^ 22

/-- Polynomial part against which the true normalized residual is compared. -/
def factorTwoForwardP8TaylorResidual (x : ℝ) : ℝ :=
  factorTwoForwardP8TaylorQuotient x -
    factorTwoForwardP8PotentialOddQuotient x

theorem continuous_factorTwoForwardP8TaylorResidual :
    Continuous factorTwoForwardP8TaylorResidual := by
  unfold factorTwoForwardP8TaylorResidual factorTwoForwardP8TaylorQuotient
    factorTwoForwardP8PotentialOddQuotient
  fun_prop

/-- Exact polynomial identity behind the Taylor quotient. -/
theorem mul_factorTwoForwardP8TaylorQuotient_eq (x : ℝ) :
    x * factorTwoForwardP8TaylorQuotient x =
      factorTwoCenteredP8 (x - 2) * p8LogOneSubTaylorSixteen (x / 3) -
        factorTwoCenteredP8 (x + 2) *
          p8LogOneSubTaylorSixteen (-x / 3) := by
  rw [factorTwoCenteredP8_eq, factorTwoCenteredP8_eq]
  norm_num [p8LogOneSubTaylorSixteen, Finset.sum_range_succ]
  unfold factorTwoForwardP8TaylorQuotient
  ring

/-- Exact squared mass of the rational Taylor residual. -/
theorem integral_factorTwoForwardP8TaylorResidual_sq :
    (∫ x : ℝ in -1..1, factorTwoForwardP8TaylorResidual x ^ 2) =
      (1069555027384167828009128340182327521571616819133 /
        745035282722447088655956436696432500000000000000000 : ℝ) := by
  unfold factorTwoForwardP8TaylorResidual factorTwoForwardP8TaylorQuotient
    factorTwoForwardP8PotentialOddQuotient
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num

/-! ## Uniform analytic remainder -/

/-- A coefficient-triangle bound for centered `P8` on the only translated
interval needed below. -/
private theorem abs_factorTwoCenteredP8_le_of_abs_le_three
    {y : ℝ} (hy : |y| ≤ 3) :
    |factorTwoCenteredP8 y| ≤ (3221843 / 8 : ℝ) := by
  have h2 := pow_le_pow_left₀ (abs_nonneg y) hy 2
  have h4 := pow_le_pow_left₀ (abs_nonneg y) hy 4
  have h6 := pow_le_pow_left₀ (abs_nonneg y) hy 6
  have h8 := pow_le_pow_left₀ (abs_nonneg y) hy 8
  rw [factorTwoCenteredP8_eq, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 128)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 128)).2
  calc
    |6435 * y ^ 8 - 12012 * y ^ 6 + 6930 * y ^ 4 -
        1260 * y ^ 2 + 35| ≤
      |6435 * y ^ 8| + |12012 * y ^ 6| + |6930 * y ^ 4| +
        |1260 * y ^ 2| + |(35 : ℝ)| := by
          calc
            _ ≤ |6435 * y ^ 8 - 12012 * y ^ 6 + 6930 * y ^ 4 -
                  1260 * y ^ 2| + |(35 : ℝ)| := abs_add_le _ _
            _ ≤ (|6435 * y ^ 8 - 12012 * y ^ 6 + 6930 * y ^ 4| +
                  |1260 * y ^ 2|) + |(35 : ℝ)| := by
                    gcongr
                    exact abs_sub _ _
            _ ≤ ((|6435 * y ^ 8 - 12012 * y ^ 6| +
                  |6930 * y ^ 4|) + |1260 * y ^ 2|) + |(35 : ℝ)| := by
                    gcongr
                    exact abs_add_le _ _
            _ ≤ (((|6435 * y ^ 8| + |12012 * y ^ 6|) +
                  |6930 * y ^ 4|) + |1260 * y ^ 2|) + |(35 : ℝ)| := by
                    gcongr
                    exact abs_sub _ _
            _ = _ := by ring
    _ = 6435 * |y| ^ 8 + 12012 * |y| ^ 6 + 6930 * |y| ^ 4 +
        1260 * |y| ^ 2 + 35 := by
          simp only [abs_mul, abs_pow]
          norm_num
    _ ≤ 6435 * 3 ^ 8 + 12012 * 3 ^ 6 + 6930 * 3 ^ 4 +
        1260 * 3 ^ 2 + 35 := by gcongr
    _ = (3221843 / 8 : ℝ) * 128 := by norm_num

private theorem abs_factorTwoCenteredP8_sub_two_le
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |factorTwoCenteredP8 (x - 2)| ≤ (3221843 / 8 : ℝ) := by
  apply abs_factorTwoCenteredP8_le_of_abs_le_three
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

private theorem abs_factorTwoCenteredP8_add_two_le
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |factorTwoCenteredP8 (x + 2)| ≤ (3221843 / 8 : ℝ) := by
  apply abs_factorTwoCenteredP8_le_of_abs_le_three
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

private theorem abs_p8LogMinus_sub_taylorSixteen_le
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |p8LogMinus x - p8LogOneSubTaylorSixteen (x / 3)| ≤
      |x| ^ 17 / (2 * 3 ^ 16) := by
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have hz : |x / 3| < 1 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  have htail := Real.abs_log_sub_add_sum_range_le hz 16
  have hden : (2 / 3 : ℝ) ≤ 1 - |x / 3| := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    norm_num
    linarith
  calc
    |p8LogMinus x - p8LogOneSubTaylorSixteen (x / 3)| =
        |(∑ i ∈ Finset.range 16,
            (x / 3) ^ (i + 1) / (i + 1 : ℝ)) +
          Real.log (1 - x / 3)| := by
            unfold p8LogMinus p8LogOneSubTaylorSixteen
            congr 1
            ring
    _ ≤ |x / 3| ^ (16 + 1) / (1 - |x / 3|) := htail
    _ ≤ |x / 3| ^ 17 / (2 / 3) :=
      div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) 17)
        (by norm_num) hden
    _ = |x| ^ 17 / (2 * 3 ^ 16) := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      norm_num
      ring

private theorem abs_p8LogPlus_sub_taylorSixteen_le
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |p8LogPlus x - p8LogOneSubTaylorSixteen (-x / 3)| ≤
      |x| ^ 17 / (2 * 3 ^ 16) := by
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have hz : |-x / 3| < 1 := by
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  have htail := Real.abs_log_sub_add_sum_range_le hz 16
  have hden : (2 / 3 : ℝ) ≤ 1 - |-x / 3| := by
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    norm_num
    linarith
  calc
    |p8LogPlus x - p8LogOneSubTaylorSixteen (-x / 3)| =
        |(∑ i ∈ Finset.range 16,
            (-x / 3) ^ (i + 1) / (i + 1 : ℝ)) +
          Real.log (1 - (-x / 3))| := by
            unfold p8LogPlus p8LogOneSubTaylorSixteen
            congr 1
            ring
    _ ≤ |-x / 3| ^ (16 + 1) / (1 - |-x / 3|) := htail
    _ ≤ |-x / 3| ^ 17 / (2 / 3) :=
      div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) 17)
        (by norm_num) hden
    _ = |x| ^ 17 / (2 * 3 ^ 16) := by
      rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      norm_num
      ring

private theorem p8LogMinusSlope_eq_div
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    p8LogMinusSlope x = p8LogMinus x / x := by
  unfold p8LogMinusSlope
  rw [centeredClamp_eq_self hx, dslope_of_ne _ hx0, slope_def_field]
  simp only [p8LogMinus, zero_div, sub_zero, Real.log_one]

private theorem p8LogPlusSlope_eq_div
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    p8LogPlusSlope x = p8LogPlus x / x := by
  unfold p8LogPlusSlope
  rw [centeredClamp_eq_self hx, dslope_of_ne _ hx0, slope_def_field]
  simp only [p8LogPlus, zero_div, add_zero, sub_zero, Real.log_one]

private theorem p8LogMinusSlope_zero :
    p8LogMinusSlope 0 = -(1 / 3 : ℝ) := by
  have hinner : HasDerivAt (fun y : ℝ ↦ 1 - y / 3) (-(1 / 3 : ℝ)) 0 := by
    convert (hasDerivAt_const 0 (1 : ℝ)).sub
      ((hasDerivAt_id (0 : ℝ)).div_const 3) using 1
    all_goals norm_num
  have hne : 1 - (0 : ℝ) / 3 ≠ 0 := by norm_num
  have hlog := (Real.hasDerivAt_log hne).comp 0 hinner
  unfold p8LogMinusSlope
  rw [centeredClamp_eq_self (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 1),
    dslope_same]
  simpa only [p8LogMinus, Function.comp_apply, zero_div, sub_zero,
    inv_one, one_mul] using hlog.deriv

private theorem p8LogPlusSlope_zero :
    p8LogPlusSlope 0 = (1 / 3 : ℝ) := by
  have hinner : HasDerivAt (fun y : ℝ ↦ 1 + y / 3) (1 / 3 : ℝ) 0 := by
    convert (hasDerivAt_const 0 (1 : ℝ)).add
      ((hasDerivAt_id (0 : ℝ)).div_const 3) using 1
    all_goals norm_num
  have hne : 1 + (0 : ℝ) / 3 ≠ 0 := by norm_num
  have hlog := (Real.hasDerivAt_log hne).comp 0 hinner
  unfold p8LogPlusSlope
  rw [centeredClamp_eq_self (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 1),
    dslope_same]
  simpa only [p8LogPlus, Function.comp_apply, zero_div, add_zero,
    inv_one, one_mul] using hlog.deriv

private theorem factorTwoForwardP8PotentialQuotient_zero_eq_taylorResidual :
    factorTwoForwardP8PotentialQuotient 0 =
      factorTwoForwardP8TaylorResidual 0 := by
  unfold factorTwoForwardP8PotentialQuotient
    factorTwoForwardP8TaylorResidual factorTwoForwardP8TaylorQuotient
    factorTwoForwardP8PotentialOddQuotient
  rw [p8LogMinusSlope_zero, p8LogPlusSlope_zero,
    factorTwoCenteredP8_eq, factorTwoCenteredP8_eq]
  norm_num

/-- The true normalized residual differs from its exact rational Taylor
polynomial by less than `3221843 / 344373768` everywhere on the interval. -/
theorem abs_factorTwoForwardP8PotentialQuotient_sub_taylorResidual_le
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |factorTwoForwardP8PotentialQuotient x -
        factorTwoForwardP8TaylorResidual x| ≤
      (3221843 / 344373768 : ℝ) := by
  by_cases hx0 : x = 0
  · subst x
    rw [factorTwoForwardP8PotentialQuotient_zero_eq_taylorResidual,
      sub_self, abs_zero]
    norm_num
  · let em : ℝ :=
      p8LogMinus x - p8LogOneSubTaylorSixteen (x / 3)
    let ep : ℝ :=
      p8LogPlus x - p8LogOneSubTaylorSixteen (-x / 3)
    have hm : |em| ≤ |x| ^ 17 / (2 * 3 ^ 16) := by
      simpa only [em] using abs_p8LogMinus_sub_taylorSixteen_le hx
    have hp : |ep| ≤ |x| ^ 17 / (2 * 3 ^ 16) := by
      simpa only [ep] using abs_p8LogPlus_sub_taylorSixteen_le hx
    have hPm := abs_factorTwoCenteredP8_sub_two_le hx
    have hPp := abs_factorTwoCenteredP8_add_two_le hx
    have hnum :
        |factorTwoCenteredP8 (x - 2) * em -
            factorTwoCenteredP8 (x + 2) * ep| ≤
          (3221843 / 8 : ℝ) * |x| ^ 17 / 3 ^ 16 := by
      calc
        _ ≤ |factorTwoCenteredP8 (x - 2)| * |em| +
            |factorTwoCenteredP8 (x + 2)| * |ep| := by
              simpa only [abs_mul] using abs_sub
                (factorTwoCenteredP8 (x - 2) * em)
                (factorTwoCenteredP8 (x + 2) * ep)
        _ ≤ (3221843 / 8 : ℝ) * (|x| ^ 17 / (2 * 3 ^ 16)) +
            (3221843 / 8 : ℝ) * (|x| ^ 17 / (2 * 3 ^ 16)) := by
              gcongr
        _ = (3221843 / 8 : ℝ) * |x| ^ 17 / 3 ^ 16 := by ring
    have heq :
        factorTwoForwardP8PotentialQuotient x -
            factorTwoForwardP8TaylorResidual x =
          (factorTwoCenteredP8 (x - 2) * em -
            factorTwoCenteredP8 (x + 2) * ep) / x := by
      apply (eq_div_iff hx0).2
      unfold factorTwoForwardP8PotentialQuotient
        factorTwoForwardP8TaylorResidual
      rw [p8LogMinusSlope_eq_div hx hx0, p8LogPlusSlope_eq_div hx hx0]
      dsimp only [em, ep]
      have hT := mul_factorTwoForwardP8TaylorQuotient_eq x
      field_simp [hx0]
      ring_nf at hT ⊢
      linarith
    rw [heq, abs_div]
    have hxabsPos : 0 < |x| := abs_pos.mpr hx0
    have hdiv :
        |factorTwoCenteredP8 (x - 2) * em -
            factorTwoCenteredP8 (x + 2) * ep| / |x| ≤
          (3221843 / 8 : ℝ) * |x| ^ 16 / 3 ^ 16 := by
      rw [div_le_iff₀ hxabsPos]
      calc
        _ ≤ (3221843 / 8 : ℝ) * |x| ^ 17 / 3 ^ 16 := hnum
        _ = ((3221843 / 8 : ℝ) * |x| ^ 16 / 3 ^ 16) * |x| := by
          rw [pow_succ]
          ring
    calc
      _ ≤ (3221843 / 8 : ℝ) * |x| ^ 16 / 3 ^ 16 := hdiv
      _ ≤ (3221843 / 8 : ℝ) * 1 / 3 ^ 16 := by
        have hpow := pow_le_pow_left₀ (abs_nonneg x) (abs_le.mpr hx) 16
        norm_num at hpow
        gcongr
      _ = (3221843 / 344373768 : ℝ) := by norm_num

/-! ## Squared mass and the production potential row -/

/-- The optimized normalized `P8` alternating residual has mass at most
`1 / 200`.  The exact rational upper bound produced inside the proof is about
`0.003222`, leaving substantial slack. -/
theorem integral_factorTwoForwardP8PotentialQuotient_sq_le :
    (∫ x : ℝ in -1..1, factorTwoForwardP8PotentialQuotient x ^ 2) ≤
      (1 / 200 : ℝ) := by
  let A : ℝ → ℝ := factorTwoForwardP8TaylorResidual
  let B : ℝ := 3221843 / 344373768
  have hAcont : Continuous A := by
    simpa only [A] using continuous_factorTwoForwardP8TaylorResidual
  have hScont : Continuous factorTwoForwardP8PotentialQuotient :=
    continuous_factorTwoForwardP8PotentialQuotient
  have hleft : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoForwardP8PotentialQuotient x ^ 2)
      volume (-1) 1 := (hScont.pow 2).intervalIntegrable (-1) 1
  have hAterm : IntervalIntegrable
      (fun x : ℝ ↦ (2 : ℝ) * A x ^ 2) volume (-1) 1 :=
    (continuous_const.mul (hAcont.pow 2)).intervalIntegrable (-1) 1
  have hBterm : IntervalIntegrable
      (fun _x : ℝ ↦ (2 : ℝ) * B ^ 2) volume (-1) 1 :=
    continuous_const.intervalIntegrable (-1) 1
  have hright : IntervalIntegrable
      (fun x : ℝ ↦ (2 : ℝ) * A x ^ 2 + 2 * B ^ 2)
      volume (-1) 1 := hAterm.add hBterm
  have hmono :
      (∫ x : ℝ in -1..1, factorTwoForwardP8PotentialQuotient x ^ 2) ≤
        ∫ x : ℝ in -1..1, (2 : ℝ) * A x ^ 2 + 2 * B ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num) hleft hright
    intro x hx
    have herr :=
      abs_factorTwoForwardP8PotentialQuotient_sub_taylorResidual_le hx
    have hB0 : 0 ≤ B := by
      dsimp only [B]
      norm_num
    have hsquare := (sq_le_sq₀ (abs_nonneg _) hB0).2 herr
    rw [sq_abs] at hsquare
    dsimp only [A, B] at hsquare ⊢
    nlinarith [sq_nonneg
      (factorTwoForwardP8PotentialQuotient x -
        2 * factorTwoForwardP8TaylorResidual x)]
  calc
    _ ≤ ∫ x : ℝ in -1..1, (2 : ℝ) * A x ^ 2 + 2 * B ^ 2 := hmono
    _ = 2 *
          (1069555027384167828009128340182327521571616819133 /
            745035282722447088655956436696432500000000000000000 : ℝ) +
        4 * (3221843 / 344373768 : ℝ) ^ 2 := by
      rw [intervalIntegral.integral_add hAterm hBterm,
        intervalIntegral.integral_const_mul,
        show (∫ x : ℝ in -1..1, A x ^ 2) =
            (1069555027384167828009128340182327521571616819133 /
              745035282722447088655956436696432500000000000000000 : ℝ) by
          simpa only [A] using integral_factorTwoForwardP8TaylorResidual_sq,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      dsimp only [B]
      ring
    _ ≤ (1 / 200 : ℝ) := by norm_num

theorem two_mul_integral_factorTwoForwardP8PotentialQuotient_sq_le :
    2 * (∫ x : ℝ in -1..1,
      factorTwoForwardP8PotentialQuotient x ^ 2) ≤ (1 / 100 : ℝ) := by
  nlinarith [integral_factorTwoForwardP8PotentialQuotient_sq_le]

/-- Production endpoint-potential bound for the reduced alternating `P8`
forward row.  The degree-seven part vanishes against a cutoff-nine residual;
the centered zero of the remaining row is charged to endpoint potential. -/
theorem sq_intervalIntegral_mul_factorTwoForwardLP8_le_potential
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlow : centeredLegendreMomentsVanishBelow w 9) :
    (∫ x : ℝ in -1..1, w x * factorTwoForwardLP8 x) ^ 2 ≤
      (1 / 100 : ℝ) * factorTwoIntrinsicPotentialEnergy w := by
  have hfactor : ∀ x ∈ Icc (-1 : ℝ) 1,
      factorTwoForwardLP8 x =
        factorTwoForwardP8PotentialShiftedPolynomial.eval ((x + 1) / 2) +
          x * factorTwoForwardP8PotentialQuotient x := by
    intro x hx
    rw [factorTwoForwardP8PotentialShiftedPolynomial_eval]
    exact factorTwoForwardLP8_eq_polynomial_add_centeredFactor hx
  have h := sq_intervalIntegral_mul_le_potential_of_momentGap_factor
    w factorTwoForwardLP8 factorTwoForwardP8PotentialQuotient
    hw continuous_factorTwoForwardP8PotentialQuotient hlow
    factorTwoForwardP8PotentialShiftedPolynomial
    factorTwoForwardP8PotentialShiftedPolynomial_natDegree_lt_nine
    hfactor (1 / 200 : ℝ) (by norm_num)
    integral_factorTwoForwardP8PotentialQuotient_sq_le
  norm_num at h ⊢
  exact h

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8ForwardPotentialCertificateStructural
