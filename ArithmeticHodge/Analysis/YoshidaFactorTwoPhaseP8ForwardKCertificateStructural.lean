import ArithmeticHodge.Analysis.YoshidaEndpointOcticPotential
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8StructuralReserve
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false

open Finset MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8ForwardKCertificateStructural

open ShiftedLegendreOrthogonality
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseP8StructuralReserve
open YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural

noncomputable section

/-!
# An ordinary `L²` certificate for the reduced forward `P₈` representer

The logarithms are split at `3 / 2` and truncated structurally at order
thirty.  A rational degree-eight polynomial removes the low part.  The
remaining rational polynomial has an exact centered `L²` mass, while
`Real.abs_log_sub_add_sum_range_le` controls the infinite Taylor tail.
-/

/-! ## Reduced representer and its low polynomial -/

/-- Symmetric reduced forward-Hankel representer attached to centered `P₈`. -/
def factorTwoForwardKP8 (x : ℝ) : ℝ :=
  factorTwoCenteredP8 (x + 2) * Real.log ((3 + x) / 2) +
    factorTwoCenteredP8 (x - 2) * Real.log ((3 - x) / 2)

/-- Rational degree-eight correction used after removing the constant
`log (3 / 2)` part. -/
def factorTwoForwardKP8RationalLow (x : ℝ) : ℝ :=
  (-373659 + 22582198479675 * x ^ 2 + 43508342688412 * x ^ 4 +
      10121847247495 * x ^ 6 + 232677450480 * x ^ 8) / 1000000000

private def centeredCoordinatePolynomial : ℝ[X] :=
  Polynomial.C 2 * Polynomial.X - Polynomial.C 1

/-- The full low polynomial, expressed in the shifted coordinate consumed by
the cutoff-nine moment-gap theorem. -/
def factorTwoForwardKP8LowPolynomial : ℝ[X] :=
  let A := centeredCoordinatePolynomial
  Polynomial.C (Real.log (3 / 2)) *
      (Polynomial.C (984467 / 64) +
        Polynomial.C (2203425 / 16) * A ^ 2 +
        Polynomial.C (3246705 / 32) * A ^ 4 +
        Polynomial.C (177177 / 16) * A ^ 6 +
        Polynomial.C (6435 / 64) * A ^ 8) +
    Polynomial.C (-373659 / 1000000000) +
      Polynomial.C (22582198479675 / 1000000000) * A ^ 2 +
      Polynomial.C (43508342688412 / 1000000000) * A ^ 4 +
      Polynomial.C (10121847247495 / 1000000000) * A ^ 6 +
      Polynomial.C (232677450480 / 1000000000) * A ^ 8

@[simp] theorem factorTwoForwardKP8LowPolynomial_eval (x : ℝ) :
    factorTwoForwardKP8LowPolynomial.eval ((x + 1) / 2) =
      Real.log (3 / 2) *
          (factorTwoCenteredP8 (x + 2) + factorTwoCenteredP8 (x - 2)) +
        factorTwoForwardKP8RationalLow x := by
  simp only [factorTwoForwardKP8LowPolynomial, centeredCoordinatePolynomial,
    eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow]
  rw [factorTwoCenteredP8_eq, factorTwoCenteredP8_eq]
  unfold factorTwoForwardKP8RationalLow
  ring

theorem factorTwoForwardKP8LowPolynomial_natDegree_lt_nine :
    factorTwoForwardKP8LowPolynomial.natDegree < 9 := by
  unfold factorTwoForwardKP8LowPolynomial centeredCoordinatePolynomial
  ring_nf
  compute_degree
  norm_num

/-! ## The finite Taylor residual -/

private def forwardLogPlusTaylor30 (x : ℝ) : ℝ :=
  -∑ i ∈ Finset.range 30, (-x / 3) ^ (i + 1) / (i + 1 : ℝ)

private def forwardLogMinusTaylor30 (x : ℝ) : ℝ :=
  -∑ i ∈ Finset.range 30, (x / 3) ^ (i + 1) / (i + 1 : ℝ)

private def factorTwoForwardKP8Truncated (x : ℝ) : ℝ :=
  factorTwoCenteredP8 (x + 2) * forwardLogPlusTaylor30 x +
    factorTwoCenteredP8 (x - 2) * forwardLogMinusTaylor30 x

/-- Exact power-basis residual after subtracting the rational low polynomial. -/
private def factorTwoForwardKP8TruncatedResidual (x : ℝ) : ℝ :=
  373659 / 1000000000 -
    (7390183 / 360000000) * x ^ 2 +
    (7193384939 / 40500000000) * x ^ 4 -
    (232419491813 / 437400000000) * x ^ 6 +
    (5894058470383 / 9185400000000) * x ^ 8 -
    (10071431 / 37791360) * x ^ 10 -
    (12256789 / 4489613568) * x ^ 12 -
    (3581405 / 55712022912) * x ^ 14 -
    (1320893 / 573037949952) * x ^ 16 -
    (1620653 / 15174485713152) * x ^ 18 -
    (16941983 / 2883152285498880) * x ^ 20 -
    (6636937 / 18163859398642944) * x ^ 22 -
    (92855291 / 3731648828635487232) * x ^ 24 -
    (83959189 / 46209087266358556800) * x ^ 26 -
    (8589703 / 61287842058538717440) * x ^ 28 -
    (193632637 / 17138707261369934198400) * x ^ 30 -
    (17392151 / 5095119215568913920) * x ^ 32 -
    (1508309 / 254755960778445696) * x ^ 34 -
    (61066291 / 53498751763473596160) * x ^ 36 -
    (143 / 8784688302705024) * x ^ 38

private theorem continuous_factorTwoForwardKP8TruncatedResidual :
    Continuous factorTwoForwardKP8TruncatedResidual := by
  unfold factorTwoForwardKP8TruncatedResidual
  fun_prop

private theorem factorTwoForwardKP8Truncated_sub_low (x : ℝ) :
    factorTwoForwardKP8Truncated x - factorTwoForwardKP8RationalLow x =
      factorTwoForwardKP8TruncatedResidual x := by
  unfold factorTwoForwardKP8Truncated factorTwoForwardKP8RationalLow
    factorTwoForwardKP8TruncatedResidual forwardLogPlusTaylor30
    forwardLogMinusTaylor30
  rw [factorTwoCenteredP8_eq, factorTwoCenteredP8_eq]
  norm_num [Finset.sum_range_succ]
  ring

/-- The finite rational residual has slightly less than `9 / 40000000`
centered `L²` mass. -/
private theorem integral_factorTwoForwardKP8TruncatedResidual_sq_le :
    (∫ x : ℝ in -1..1, factorTwoForwardKP8TruncatedResidual x ^ 2) ≤
      (9 / 40000000 : ℝ) := by
  unfold factorTwoForwardKP8TruncatedResidual
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

/-! ## Infinite Taylor tail -/

private theorem abs_forwardLogPlus_sub_taylor30_le
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |Real.log (1 + x / 3) - forwardLogPlusTaylor30 x| ≤
      |x| ^ 31 / (2 * 3 ^ 30) := by
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have hz : |-x / 3| < 1 := by
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  have htail := Real.abs_log_sub_add_sum_range_le hz 30
  have hden : (2 / 3 : ℝ) ≤ 1 - |-x / 3| := by
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    norm_num
    linarith
  calc
    |Real.log (1 + x / 3) - forwardLogPlusTaylor30 x| =
        |(∑ i ∈ Finset.range 30,
            (-x / 3) ^ (i + 1) / (i + 1 : ℝ)) +
          Real.log (1 - (-x / 3))| := by
            unfold forwardLogPlusTaylor30
            congr 1
            ring
    _ ≤ |-x / 3| ^ (30 + 1) / (1 - |-x / 3|) := htail
    _ ≤ |-x / 3| ^ 31 / (2 / 3) :=
      div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) 31)
        (by norm_num) hden
    _ = |x| ^ 31 / (2 * 3 ^ 30) := by
      rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      norm_num
      ring

private theorem abs_forwardLogMinus_sub_taylor30_le
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |Real.log (1 - x / 3) - forwardLogMinusTaylor30 x| ≤
      |x| ^ 31 / (2 * 3 ^ 30) := by
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have hz : |x / 3| < 1 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  have htail := Real.abs_log_sub_add_sum_range_le hz 30
  have hden : (2 / 3 : ℝ) ≤ 1 - |x / 3| := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    norm_num
    linarith
  calc
    |Real.log (1 - x / 3) - forwardLogMinusTaylor30 x| =
        |(∑ i ∈ Finset.range 30,
            (x / 3) ^ (i + 1) / (i + 1 : ℝ)) +
          Real.log (1 - x / 3)| := by
            unfold forwardLogMinusTaylor30
            congr 1
            ring
    _ ≤ |x / 3| ^ (30 + 1) / (1 - |x / 3|) := htail
    _ ≤ |x / 3| ^ 31 / (2 / 3) :=
      div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) 31)
        (by norm_num) hden
    _ = |x| ^ 31 / (2 * 3 ^ 30) := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      norm_num
      ring

private theorem abs_factorTwoCenteredP8_le_of_abs_le_three
    {z : ℝ} (hz : |z| ≤ 3) :
    |factorTwoCenteredP8 z| ≤ 3221843 / 8 := by
  have h2 := pow_le_pow_left₀ (abs_nonneg z) hz 2
  have h4 := pow_le_pow_left₀ (abs_nonneg z) hz 4
  have h6 := pow_le_pow_left₀ (abs_nonneg z) hz 6
  have h8 := pow_le_pow_left₀ (abs_nonneg z) hz 8
  rw [factorTwoCenteredP8_eq, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 128)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 128)).2
  calc
    |6435 * z ^ 8 - 12012 * z ^ 6 + 6930 * z ^ 4 -
        1260 * z ^ 2 + 35| ≤
      |6435 * z ^ 8| + |12012 * z ^ 6| + |6930 * z ^ 4| +
        |1260 * z ^ 2| + |(35 : ℝ)| := by
          calc
            _ ≤ |6435 * z ^ 8 - 12012 * z ^ 6 + 6930 * z ^ 4 -
                  1260 * z ^ 2| + |(35 : ℝ)| := abs_add_le _ _
            _ ≤ (|6435 * z ^ 8 - 12012 * z ^ 6 + 6930 * z ^ 4| +
                  |1260 * z ^ 2|) + |(35 : ℝ)| := by
                    gcongr
                    exact abs_sub _ _
            _ ≤ ((|6435 * z ^ 8 - 12012 * z ^ 6| +
                  |6930 * z ^ 4|) + |1260 * z ^ 2|) + |(35 : ℝ)| := by
                    gcongr
                    exact abs_add_le _ _
            _ ≤ (((|6435 * z ^ 8| + |12012 * z ^ 6|) +
                  |6930 * z ^ 4|) + |1260 * z ^ 2|) + |(35 : ℝ)| := by
                    gcongr
                    exact abs_sub _ _
            _ = _ := by ring
    _ = 6435 * |z| ^ 8 + 12012 * |z| ^ 6 + 6930 * |z| ^ 4 +
        1260 * |z| ^ 2 + 35 := by
          simp only [abs_mul, abs_pow]
          norm_num
    _ ≤ 6435 * 3 ^ 8 + 12012 * 3 ^ 6 + 6930 * 3 ^ 4 +
        1260 * 3 ^ 2 + 35 := by gcongr
    _ = (3221843 / 8 : ℝ) * 128 := by norm_num

private def factorTwoForwardKP8TaylorError (x : ℝ) : ℝ :=
  factorTwoCenteredP8 (x + 2) *
      (Real.log (1 + x / 3) - forwardLogPlusTaylor30 x) +
    factorTwoCenteredP8 (x - 2) *
      (Real.log (1 - x / 3) - forwardLogMinusTaylor30 x)

private theorem continuousOn_forwardLogOnePlus :
    ContinuousOn (fun x : ℝ ↦ Real.log (1 + x / 3))
      (Icc (-1 : ℝ) 1) := by
  apply ContinuousOn.log (by fun_prop)
  intro x hx
  nlinarith [hx.1]

private theorem continuousOn_forwardLogOneMinus :
    ContinuousOn (fun x : ℝ ↦ Real.log (1 - x / 3))
      (Icc (-1 : ℝ) 1) := by
  apply ContinuousOn.log (by fun_prop)
  intro x hx
  nlinarith [hx.2]

private theorem continuous_forwardLogPlusTaylor30 :
    Continuous forwardLogPlusTaylor30 := by
  unfold forwardLogPlusTaylor30
  fun_prop

private theorem continuous_forwardLogMinusTaylor30 :
    Continuous forwardLogMinusTaylor30 := by
  unfold forwardLogMinusTaylor30
  fun_prop

private theorem abs_factorTwoForwardKP8TaylorError_le
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |factorTwoForwardKP8TaylorError x| ≤
      (3221843 / 8 : ℝ) * |x| ^ 31 / 3 ^ 30 := by
  have hxplus : |x + 2| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hxminus : |x - 2| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hp := abs_factorTwoCenteredP8_le_of_abs_le_three hxplus
  have hm := abs_factorTwoCenteredP8_le_of_abs_le_three hxminus
  have htp := abs_forwardLogPlus_sub_taylor30_le hx
  have htm := abs_forwardLogMinus_sub_taylor30_le hx
  unfold factorTwoForwardKP8TaylorError
  calc
    _ ≤ |factorTwoCenteredP8 (x + 2)| *
          |Real.log (1 + x / 3) - forwardLogPlusTaylor30 x| +
        |factorTwoCenteredP8 (x - 2)| *
          |Real.log (1 - x / 3) - forwardLogMinusTaylor30 x| := by
            simpa only [abs_mul] using abs_add_le
              (factorTwoCenteredP8 (x + 2) *
                (Real.log (1 + x / 3) - forwardLogPlusTaylor30 x))
              (factorTwoCenteredP8 (x - 2) *
                (Real.log (1 - x / 3) - forwardLogMinusTaylor30 x))
    _ ≤ (3221843 / 8 : ℝ) * (|x| ^ 31 / (2 * 3 ^ 30)) +
        (3221843 / 8 : ℝ) * (|x| ^ 31 / (2 * 3 ^ 30)) := by
          gcongr
    _ = (3221843 / 8 : ℝ) * |x| ^ 31 / 3 ^ 30 := by ring

private theorem continuousOn_factorTwoForwardKP8TaylorError :
    ContinuousOn factorTwoForwardKP8TaylorError (Icc (-1 : ℝ) 1) := by
  unfold factorTwoForwardKP8TaylorError
  exact (((continuous_factorTwoCenteredP8.comp (by fun_prop)).continuousOn).mul
      (continuousOn_forwardLogOnePlus.sub
        continuous_forwardLogPlusTaylor30.continuousOn)).add
    (((continuous_factorTwoCenteredP8.comp (by fun_prop)).continuousOn).mul
      (continuousOn_forwardLogOneMinus.sub
        continuous_forwardLogMinusTaylor30.continuousOn))

/-- The infinite logarithmic tail has less than `10⁻¹⁸` centered `L²`
mass.  Keeping the factor `|x|³¹` is essential here. -/
private theorem integral_factorTwoForwardKP8TaylorError_sq_le :
    (∫ x : ℝ in -1..1, factorTwoForwardKP8TaylorError x ^ 2) ≤
      (1 / 1000000000000000000 : ℝ) := by
  have hmajor : Continuous (fun x : ℝ ↦
      ((3221843 / 8 : ℝ) ^ 2 / 3 ^ 60) * x ^ 62) := by
    fun_prop
  have hmono :
      (∫ x : ℝ in -1..1, factorTwoForwardKP8TaylorError x ^ 2) ≤
        ∫ x : ℝ in -1..1,
          ((3221843 / 8 : ℝ) ^ 2 / 3 ^ 60) * x ^ 62 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (continuousOn_factorTwoForwardKP8TaylorError.pow 2
        |>.intervalIntegrable_of_Icc (by norm_num))
      (hmajor.intervalIntegrable (-1) 1)
    intro x hx
    have h := abs_factorTwoForwardKP8TaylorError_le hx
    have hright : 0 ≤ (3221843 / 8 : ℝ) * |x| ^ 31 / 3 ^ 30 := by
      positivity
    have hsquare := (sq_le_sq₀ (abs_nonneg _) hright).2 h
    rw [sq_abs] at hsquare
    calc
      factorTwoForwardKP8TaylorError x ^ 2 ≤
          ((3221843 / 8 : ℝ) * |x| ^ 31 / 3 ^ 30) ^ 2 := hsquare
      _ = ((3221843 / 8 : ℝ) ^ 2 / 3 ^ 60) * x ^ 62 := by
        rw [div_pow, mul_pow, ← pow_mul, ← pow_mul,
          (by norm_num : Even 62).pow_abs]
        ring
  calc
    _ ≤ ∫ x : ℝ in -1..1,
        ((3221843 / 8 : ℝ) ^ 2 / 3 ^ 60) * x ^ 62 := hmono
    _ = ((3221843 / 8 : ℝ) ^ 2 / 3 ^ 60) *
        (∫ x : ℝ in -1..1, x ^ 62) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ((3221843 / 8 : ℝ) ^ 2 / 3 ^ 60) * (2 / 63) := by
      rw [integral_pow_nat]
      norm_num
    _ ≤ (1 / 1000000000000000000 : ℝ) := by norm_num

/-! ## Assembly -/

private theorem factorTwoForwardKP8_sub_low_eq
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoForwardKP8 x -
        factorTwoForwardKP8LowPolynomial.eval ((x + 1) / 2) =
      factorTwoForwardKP8TruncatedResidual x +
        factorTwoForwardKP8TaylorError x := by
  have hplus :
      Real.log ((3 + x) / 2) =
        Real.log (3 / 2) + Real.log (1 + x / 3) := by
    rw [show (3 + x) / 2 = (3 / 2) * (1 + x / 3) by ring,
      Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0)
        (by nlinarith [hx.1] : (1 + x / 3 : ℝ) ≠ 0)]
  have hminus :
      Real.log ((3 - x) / 2) =
        Real.log (3 / 2) + Real.log (1 - x / 3) := by
    rw [show (3 - x) / 2 = (3 / 2) * (1 - x / 3) by ring,
      Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0)
        (by nlinarith [hx.2] : (1 - x / 3 : ℝ) ≠ 0)]
  rw [factorTwoForwardKP8LowPolynomial_eval,
    show factorTwoForwardKP8 x -
        (Real.log (3 / 2) *
            (factorTwoCenteredP8 (x + 2) + factorTwoCenteredP8 (x - 2)) +
          factorTwoForwardKP8RationalLow x) =
        (factorTwoForwardKP8Truncated x -
            factorTwoForwardKP8RationalLow x) +
          factorTwoForwardKP8TaylorError x by
      unfold factorTwoForwardKP8 factorTwoForwardKP8Truncated
        factorTwoForwardKP8TaylorError
      rw [hplus, hminus]
      ring,
    factorTwoForwardKP8Truncated_sub_low]

private theorem continuousOn_factorTwoForwardKP8 :
    ContinuousOn factorTwoForwardKP8 (Icc (-1 : ℝ) 1) := by
  unfold factorTwoForwardKP8
  have hplus : ContinuousOn (fun x : ℝ ↦ Real.log ((3 + x) / 2))
      (Icc (-1 : ℝ) 1) := by
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    nlinarith [hx.1]
  have hminus : ContinuousOn (fun x : ℝ ↦ Real.log ((3 - x) / 2))
      (Icc (-1 : ℝ) 1) := by
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    nlinarith [hx.2]
  exact (((continuous_factorTwoCenteredP8.comp (by fun_prop)).continuousOn).mul
      hplus).add
    (((continuous_factorTwoCenteredP8.comp (by fun_prop)).continuousOn).mul
      hminus)

/-- Production `L²` certificate for the reduced symmetric `P₈` representer.
The subtractand is a genuine shifted polynomial of degree below nine. -/
theorem integral_factorTwoForwardKP8_sub_lowPolynomial_sq_le :
    (∫ x : ℝ in -1..1,
      (factorTwoForwardKP8 x -
        factorTwoForwardKP8LowPolynomial.eval ((x + 1) / 2)) ^ 2) ≤
      (1 / 4000000 : ℝ) := by
  let R : ℝ → ℝ := factorTwoForwardKP8TruncatedResidual
  let E : ℝ → ℝ := factorTwoForwardKP8TaylorError
  have hRcont : Continuous R := by
    simpa only [R] using continuous_factorTwoForwardKP8TruncatedResidual
  have hEcont : ContinuousOn E (Icc (-1 : ℝ) 1) := by
    simpa only [E] using continuousOn_factorTwoForwardKP8TaylorError
  have hleftCont : ContinuousOn (fun x : ℝ ↦
      (factorTwoForwardKP8 x -
        factorTwoForwardKP8LowPolynomial.eval ((x + 1) / 2)) ^ 2)
      (Icc (-1 : ℝ) 1) := by
    exact (continuousOn_factorTwoForwardKP8.sub (by fun_prop)).pow 2
  have hrightCont : ContinuousOn (fun x : ℝ ↦
      (11 / 10 : ℝ) * R x ^ 2 + 11 * E x ^ 2)
      (Icc (-1 : ℝ) 1) := by
    exact (continuous_const.continuousOn.mul (hRcont.continuousOn.pow 2)).add
      (continuous_const.continuousOn.mul (hEcont.pow 2))
  have hRterm : IntervalIntegrable
      (fun x : ℝ ↦ (11 / 10 : ℝ) * R x ^ 2) volume (-1) 1 :=
    (continuous_const.mul (hRcont.pow 2)).intervalIntegrable (-1) 1
  have hEterm : IntervalIntegrable
      (fun x : ℝ ↦ 11 * E x ^ 2) volume (-1) 1 :=
    (continuous_const.continuousOn.mul (hEcont.pow 2)).intervalIntegrable_of_Icc
      (by norm_num)
  have hmono :
      (∫ x : ℝ in -1..1,
        (factorTwoForwardKP8 x -
          factorTwoForwardKP8LowPolynomial.eval ((x + 1) / 2)) ^ 2) ≤
        ∫ x : ℝ in -1..1,
          ((11 / 10 : ℝ) * R x ^ 2 + 11 * E x ^ 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hleftCont.intervalIntegrable_of_Icc (by norm_num))
      (hrightCont.intervalIntegrable_of_Icc (by norm_num))
    intro x hx
    rw [factorTwoForwardKP8_sub_low_eq hx]
    dsimp only [R, E]
    nlinarith [sq_nonneg
      (factorTwoForwardKP8TruncatedResidual x / 10 -
        factorTwoForwardKP8TaylorError x)]
  calc
    _ ≤ ∫ x : ℝ in -1..1,
        ((11 / 10 : ℝ) * R x ^ 2 + 11 * E x ^ 2) := hmono
    _ = (11 / 10 : ℝ) * (∫ x : ℝ in -1..1, R x ^ 2) +
        11 * (∫ x : ℝ in -1..1, E x ^ 2) := by
      rw [intervalIntegral.integral_add hRterm hEterm,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ ≤ (11 / 10 : ℝ) * (9 / 40000000) +
        11 * (1 / 1000000000000000000) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          integral_factorTwoForwardKP8TruncatedResidual_sq_le (by norm_num)
      · exact mul_le_mul_of_nonneg_left
          integral_factorTwoForwardKP8TaylorError_sq_le (by norm_num)
    _ ≤ (1 / 4000000 : ℝ) := by norm_num

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8ForwardKCertificateStructural
