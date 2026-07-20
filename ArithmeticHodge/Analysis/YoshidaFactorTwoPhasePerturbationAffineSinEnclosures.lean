import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineCosEnclosures
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineSinSeries
import ArithmeticHodge.Analysis.YoshidaSineStructuralWidth

set_option autoImplicit false
set_option maxRecDepth 100000

open Filter MeasureTheory Real Set intervalIntegral
open scoped BigOperators Topology

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineSinEnclosures

noncomputable section

open ArithmeticHodge.Analysis
open CorrectedTrapezoidRemainder
open RatInterval
open YoshidaCauchyTailBounds
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcretePerturbationMoments
open YoshidaFactorTwoPhasePerturbationAffineCosEnclosures
open YoshidaFactorTwoPhasePerturbationAffineSinSeries
open YoshidaFactorTwoPhasePerturbationConstantEnclosures
open YoshidaFactorTwoPhasePerturbationMomentSeries
open YoshidaFactorTwoPrimeTrigEnclosures
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures
open YoshidaSineSeriesTail
open YoshidaSineStructuralWidth

/-!
# Exact enclosures for the factor-two affine sine perturbation

The dyadic coefficient is split as `D = 1 + (D - 1)`.  The defect has a
uniform geometric tail.  For the unweighted part, `U(x,y)` is the negative
derivative of `y / (x^2 + y^2)`.  A shifted first-corrected
Euler--Maclaurin formula therefore gives an exact rational tail enclosure;
its fourth-derivative remainder is bounded by the elementary integrable
majorant `10 y / (t + 1/4)^6`.
-/

/-! ## The shifted derivative-Cauchy tail -/

/-- Continuous quarter-shifted Cauchy profile. -/
def factorTwoAffineSinProfile (y t : ℝ) : ℝ :=
  y / ((t + 1 / 4) ^ 2 + y ^ 2)

def factorTwoAffineSinProfileDeriv (y t : ℝ) : ℝ :=
  -2 * y * (t + 1 / 4) /
    (((t + 1 / 4) ^ 2 + y ^ 2) ^ 2)

def factorTwoAffineSinProfileSecondDeriv (y t : ℝ) : ℝ :=
  2 * y * (3 * (t + 1 / 4) ^ 2 - y ^ 2) /
    (((t + 1 / 4) ^ 2 + y ^ 2) ^ 3)

def factorTwoAffineSinProfileThirdDeriv (y t : ℝ) : ℝ :=
  -24 * y * (t + 1 / 4) * ((t + 1 / 4) ^ 2 - y ^ 2) /
    (((t + 1 / 4) ^ 2 + y ^ 2) ^ 4)

def factorTwoAffineSinProfileFourthDeriv (y t : ℝ) : ℝ :=
  24 * y *
      (5 * (t + 1 / 4) ^ 4 -
        10 * (t + 1 / 4) ^ 2 * y ^ 2 + y ^ 4) /
    (((t + 1 / 4) ^ 2 + y ^ 2) ^ 5)

private theorem hasDerivAt_factorTwoAffineSinProfile
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (factorTwoAffineSinProfile y)
      (factorTwoAffineSinProfileDeriv y t) t := by
  have hu : HasDerivAt (fun s : ℝ ↦ s + 1 / 4) 1 t := by
    simpa using (hasDerivAt_id t).add_const (1 / 4)
  have hden : (t + 1 / 4) ^ 2 + y ^ 2 ≠ 0 := by positivity
  convert (hasDerivAt_const t y).div
    ((hu.pow 2).add_const (y ^ 2)) hden using 1
  unfold factorTwoAffineSinProfileDeriv
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, mul_one,
    zero_mul, zero_sub]
  field_simp [hden]

private theorem hasDerivAt_factorTwoAffineSinProfileDeriv
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (factorTwoAffineSinProfileDeriv y)
      (factorTwoAffineSinProfileSecondDeriv y t) t := by
  have hu : HasDerivAt (fun s : ℝ ↦ s + 1 / 4) 1 t := by
    simpa using (hasDerivAt_id t).add_const (1 / 4)
  have hden : (t + 1 / 4) ^ 2 + y ^ 2 ≠ 0 := by positivity
  convert (((hasDerivAt_const t (-2 * y)).mul hu).div
    (((hu.pow 2).add_const (y ^ 2)).pow 2)
      (pow_ne_zero 2 hden)) using 1
  unfold factorTwoAffineSinProfileSecondDeriv
  simp only [Pi.pow_apply, Pi.mul_apply]
  field_simp [hden]
  ring

private theorem hasDerivAt_factorTwoAffineSinProfileSecondDeriv
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (factorTwoAffineSinProfileSecondDeriv y)
      (factorTwoAffineSinProfileThirdDeriv y t) t := by
  have hu : HasDerivAt (fun s : ℝ ↦ s + 1 / 4) 1 t := by
    simpa using (hasDerivAt_id t).add_const (1 / 4)
  have hden : (t + 1 / 4) ^ 2 + y ^ 2 ≠ 0 := by positivity
  convert ((((hasDerivAt_const t (2 * y)).mul
      (((hasDerivAt_const t 3).mul (hu.pow 2)).sub_const (y ^ 2))).div
        (((hu.pow 2).add_const (y ^ 2)).pow 3)
          (pow_ne_zero 3 hden))) using 1
  unfold factorTwoAffineSinProfileThirdDeriv
  simp only [Pi.pow_apply, Pi.mul_apply]
  field_simp [hden]
  ring

private theorem hasDerivAt_factorTwoAffineSinProfileThirdDeriv
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (factorTwoAffineSinProfileThirdDeriv y)
      (factorTwoAffineSinProfileFourthDeriv y t) t := by
  let u : ℝ → ℝ := fun s ↦ s + 1 / 4
  have hu : HasDerivAt u 1 t := by
    simpa [u] using (hasDerivAt_id t).add_const (1 / 4)
  have hsq : HasDerivAt (fun s ↦ u s ^ 2 - y ^ 2) (2 * u t) t := by
    convert (hu.pow 2).sub_const (y ^ 2) using 1
    ring
  have hprod : HasDerivAt
      (fun s ↦ u s * (u s ^ 2 - y ^ 2))
      (3 * u t ^ 2 - y ^ 2) t := by
    convert hu.mul hsq using 1
    ring
  have hnum : HasDerivAt
      (fun s ↦ -24 * y * (u s * (u s ^ 2 - y ^ 2)))
      (-24 * y * (3 * u t ^ 2 - y ^ 2)) t := by
    simpa using hprod.const_mul (-24 * y)
  have hbase := (hu.pow 2).add_const (y ^ 2)
  have hden : u t ^ 2 + y ^ 2 ≠ 0 := by
    dsimp only [u]
    positivity
  have hpow := hbase.pow 4
  convert hnum.div hpow (pow_ne_zero 4 hden) using 1
  · funext s
    simp only [factorTwoAffineSinProfileThirdDeriv, u, Pi.pow_apply,
      Pi.div_apply]
    ring
  · unfold factorTwoAffineSinProfileFourthDeriv
    dsimp only [u]
    simp only [Pi.pow_apply]
    field_simp [hden]
    ring

private theorem continuous_factorTwoAffineSinProfileFourthDeriv
    {y : ℝ} (hy : y ≠ 0) :
    Continuous (factorTwoAffineSinProfileFourthDeriv y) := by
  unfold factorTwoAffineSinProfileFourthDeriv
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    have hden : 0 < (t + 1 / 4) ^ 2 + y ^ 2 := by positivity
    exact (pow_pos hden 5).ne'

/-- Elementary fourth-derivative majorant. -/
private def factorTwoAffineSinFourthMajorant (y t : ℝ) : ℝ :=
  10 * y / (t + 1 / 4) ^ 6

private def factorTwoAffineSinFourthMajorantPrimitive (y t : ℝ) : ℝ :=
  -2 * y / (t + 1 / 4) ^ 5

private theorem factorTwoAffineSin_fourth_majorized
    {y t : ℝ} (hy : 0 < y) (ht : 0 ≤ t) :
    (1 / 12 : ℝ) * |factorTwoAffineSinProfileFourthDeriv y t| ≤
      factorTwoAffineSinFourthMajorant y t := by
  let u : ℝ := t + 1 / 4
  let D : ℝ := u ^ 2 + y ^ 2
  let P : ℝ := 5 * u ^ 4 - 10 * u ^ 2 * y ^ 2 + y ^ 4
  have hu : 0 < u := by dsimp [u]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hP : |P| ≤ 5 * D ^ 2 := by
    rw [abs_le]
    constructor <;> dsimp [P, D] <;>
      nlinarith [sq_nonneg (u ^ 2), sq_nonneg (y ^ 2),
        mul_nonneg (sq_nonneg u) (sq_nonneg y)]
  have huD : u ^ 2 ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg y]
  have hu6D3 : u ^ 6 ≤ D ^ 3 := by
    have hpow := pow_le_pow_left₀ (sq_nonneg u) huD 3
    nlinarith [hpow]
  unfold factorTwoAffineSinProfileFourthDeriv
    factorTwoAffineSinFourthMajorant
  dsimp only [u, D, P] at hP hD hu hu6D3 ⊢
  rw [abs_div, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24), abs_of_pos hy,
    abs_of_pos (pow_pos hD 5)]
  calc
    (1 / 12 : ℝ) * (24 * y * |P| / D ^ 5) ≤
        (1 / 12 : ℝ) * (24 * y * (5 * D ^ 2) / D ^ 5) := by
      gcongr
    _ = 10 * y / D ^ 3 := by
      field_simp [hD.ne']
      ring
    _ ≤ 10 * y / u ^ 6 := by
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hu 6) hu6D3

private theorem hasDerivAt_factorTwoAffineSinFourthMajorantPrimitive
    {y t : ℝ} (hu : t + 1 / 4 ≠ 0) :
    HasDerivAt (factorTwoAffineSinFourthMajorantPrimitive y)
      (factorTwoAffineSinFourthMajorant y t) t := by
  have hinner : HasDerivAt (fun s : ℝ ↦ s + 1 / 4) 1 t := by
    simpa using (hasDerivAt_id t).add_const (1 / 4)
  have hden := hinner.pow 5
  unfold factorTwoAffineSinFourthMajorantPrimitive
    factorTwoAffineSinFourthMajorant
  convert (hasDerivAt_const t (-2 * y)).div hden
    (pow_ne_zero 5 hu) using 1
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, mul_one,
    zero_mul, zero_sub]
  field_simp [hu]
  ring

private theorem integral_factorTwoAffineSinFourthMajorant
    {y a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, factorTwoAffineSinFourthMajorant y t) =
      factorTwoAffineSinFourthMajorantPrimitive y b -
        factorTwoAffineSinFourthMajorantPrimitive y a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    have ht' : t ∈ Icc a b := by rwa [uIcc_of_le hab] at ht
    exact hasDerivAt_factorTwoAffineSinFourthMajorantPrimitive
      (y := y) (t := t) (by linarith [ht'.1])
  · have hcont : ContinuousOn (factorTwoAffineSinFourthMajorant y) (Icc a b) := by
      intro t ht
      have hden : t + 1 / 4 ≠ 0 := by linarith [ht.1, ha]
      have hbase : ContinuousAt (fun s : ℝ ↦ s + 1 / 4) t :=
        continuousAt_id.add continuousAt_const
      have hpow : ContinuousAt (fun s : ℝ ↦ (s + 1 / 4) ^ 6) t :=
        hbase.pow 6
      unfold factorTwoAffineSinFourthMajorant
      exact (ContinuousAt.div continuousAt_const hpow
        (pow_ne_zero 6 hden)).continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc hab

private def factorTwoAffineSinDerivativeCorrectedError
    (y : ℝ) (N k : ℕ) : ℝ :=
  trapezoidal_error (factorTwoAffineSinProfileDeriv y) 1
      ((N + k : ℕ) + 1) ((N + k : ℕ) + 2) -
    (factorTwoAffineSinProfileSecondDeriv y ((N + k : ℕ) + 2) -
      factorTwoAffineSinProfileSecondDeriv y ((N + k : ℕ) + 1)) / 12

private theorem factorTwoAffineSinDerivativeCorrectedError_abs_le
    {y : ℝ} (hy : 0 < y) (N k : ℕ) :
    |factorTwoAffineSinDerivativeCorrectedError y N k| ≤
      ∫ t in ((N + k : ℕ) + 1)..((N + k : ℕ) + 2),
        factorTwoAffineSinFourthMajorant y t := by
  let a : ℝ := ((N + k : ℕ) : ℝ) + 1
  have hfourInt : IntervalIntegrable
      (factorTwoAffineSinProfileFourthDeriv y) volume a (a + 1) :=
    (continuous_factorTwoAffineSinProfileFourthDeriv hy.ne').intervalIntegrable _ _
  have hid := trapezoidal_error_one_sub_first_eq_integral_third
    (f := factorTwoAffineSinProfileDeriv y)
    (f1 := factorTwoAffineSinProfileSecondDeriv y)
    (f2 := factorTwoAffineSinProfileThirdDeriv y)
    (f3 := factorTwoAffineSinProfileFourthDeriv y)
    (a := a)
    (fun t ↦ hasDerivAt_factorTwoAffineSinProfileDeriv
      (y := y) (t := t) hy.ne')
    (fun t ↦ hasDerivAt_factorTwoAffineSinProfileSecondDeriv
      (y := y) (t := t) hy.ne')
    (fun t ↦ hasDerivAt_factorTwoAffineSinProfileThirdDeriv
      (y := y) (t := t) hy.ne')
    hfourInt
  have hid' : factorTwoAffineSinDerivativeCorrectedError y N k =
      -(∫ t in a..a + 1,
        correctedTrapezoidThirdKernel a t *
          factorTwoAffineSinProfileFourthDeriv y t) := by
    unfold factorTwoAffineSinDerivativeCorrectedError
    dsimp only [a] at hid ⊢
    norm_num only [Nat.cast_add, Nat.cast_one] at hid ⊢
    convert hid using 1 ; ring
  rw [hid', abs_neg]
  have hleftInt : IntervalIntegrable
      (fun t : ℝ ↦
        |correctedTrapezoidThirdKernel a t *
          factorTwoAffineSinProfileFourthDeriv y t|)
      volume a (a + 1) :=
    ((by
        unfold correctedTrapezoidThirdKernel
        fun_prop : Continuous (correctedTrapezoidThirdKernel a)).mul
      (continuous_factorTwoAffineSinProfileFourthDeriv hy.ne')).abs.intervalIntegrable _ _
  have hrightInt : IntervalIntegrable
      (factorTwoAffineSinFourthMajorant y) volume a (a + 1) := by
    have hcont : ContinuousOn (factorTwoAffineSinFourthMajorant y)
        (Icc a (a + 1)) := by
      intro t ht
      have hden : t + 1 / 4 ≠ 0 := by
        dsimp [a] at ht
        linarith [ht.1]
      have hbase : ContinuousAt (fun s : ℝ ↦ s + 1 / 4) t :=
        continuousAt_id.add continuousAt_const
      have hpow : ContinuousAt (fun s : ℝ ↦ (s + 1 / 4) ^ 6) t :=
        hbase.pow 6
      unfold factorTwoAffineSinFourthMajorant
      exact (ContinuousAt.div continuousAt_const hpow
        (pow_ne_zero 6 hden)).continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  calc
    |∫ t in a..a + 1,
        correctedTrapezoidThirdKernel a t *
          factorTwoAffineSinProfileFourthDeriv y t| ≤
        ∫ t in a..a + 1,
          |correctedTrapezoidThirdKernel a t *
            factorTwoAffineSinProfileFourthDeriv y t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in a..a + 1, factorTwoAffineSinFourthMajorant y t := by
      apply intervalIntegral.integral_mono_on (by norm_num) hleftInt hrightInt
      intro t ht
      rw [abs_mul]
      calc
        |correctedTrapezoidThirdKernel a t| *
            |factorTwoAffineSinProfileFourthDeriv y t| ≤
            (1 / 12 : ℝ) *
              |factorTwoAffineSinProfileFourthDeriv y t| :=
          mul_le_mul_of_nonneg_right
            (abs_correctedTrapezoidThirdKernel_le ht) (abs_nonneg _)
        _ ≤ factorTwoAffineSinFourthMajorant y t :=
          factorTwoAffineSin_fourth_majorized hy (by
            dsimp only [a] at ht
            linarith [ht.1])
    _ = ∫ t in ((N + k : ℕ) + 1)..((N + k : ℕ) + 2),
        factorTwoAffineSinFourthMajorant y t := by
      dsimp only [a]
      norm_num only [Nat.cast_add, Nat.cast_one]
      congr 1 ; ring

/-- Exact analytic radius for the shifted derivative tail. -/
def factorTwoAffineSinDerivativeTailRadius (y : ℝ) (N : ℕ) : ℝ :=
  2 * y / (((N : ℝ) + 1 + 1 / 4) ^ 5)

private theorem factorTwoAffineSinDerivativeCorrectedError_sum_abs_le
    {y : ℝ} (hy : 0 < y) (N M : ℕ) :
    |∑ k ∈ Finset.range M,
        factorTwoAffineSinDerivativeCorrectedError y N k| ≤
      factorTwoAffineSinDerivativeTailRadius y N := by
  calc
    |∑ k ∈ Finset.range M,
        factorTwoAffineSinDerivativeCorrectedError y N k| ≤
        ∑ k ∈ Finset.range M,
          |factorTwoAffineSinDerivativeCorrectedError y N k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range M,
        ∫ t in ((N + k : ℕ) + 1)..((N + k : ℕ) + 2),
          factorTwoAffineSinFourthMajorant y t := by
      exact Finset.sum_le_sum fun k _hk ↦
        factorTwoAffineSinDerivativeCorrectedError_abs_le hy N k
    _ = ∑ k ∈ Finset.range M,
        (factorTwoAffineSinFourthMajorantPrimitive y ((N + k : ℕ) + 2) -
          factorTwoAffineSinFourthMajorantPrimitive y ((N + k : ℕ) + 1)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact integral_factorTwoAffineSinFourthMajorant (by positivity) (by norm_num)
    _ = factorTwoAffineSinFourthMajorantPrimitive y ((N + M : ℕ) + 1) -
        factorTwoAffineSinFourthMajorantPrimitive y (N + 1) := by
      convert (Finset.sum_range_sub
        (fun k : ℕ ↦
          factorTwoAffineSinFourthMajorantPrimitive y ((N + k : ℕ) + 1)) M)
        using 1
      all_goals norm_num
      all_goals ring
    _ ≤ factorTwoAffineSinDerivativeTailRadius y N := by
      have hnonpos :
          factorTwoAffineSinFourthMajorantPrimitive y ((N + M : ℕ) + 1) ≤ 0 := by
        unfold factorTwoAffineSinFourthMajorantPrimitive
        apply div_nonpos_of_nonpos_of_nonneg
        · nlinarith [hy.le]
        · positivity
      calc
        factorTwoAffineSinFourthMajorantPrimitive y ((N + M : ℕ) + 1) -
            factorTwoAffineSinFourthMajorantPrimitive y (N + 1) ≤
            0 - factorTwoAffineSinFourthMajorantPrimitive y (N + 1) :=
          sub_le_sub_right hnonpos _
        _ = factorTwoAffineSinDerivativeTailRadius y N := by
          unfold factorTwoAffineSinFourthMajorantPrimitive
            factorTwoAffineSinDerivativeTailRadius
          norm_num only [Nat.cast_add, Nat.cast_one]
          ring

/-! ## Convergence and the infinite-tail formula -/

/-- The unweighted affine-sine kernel, indexed from Cauchy rank `1`. -/
def factorTwoAffineSinUnweightedKernel (n m : ℕ) : ℝ :=
  factorTwoCauchyU (factorTwoCauchyX (m + 1)) (factorTwoMomentY n)

theorem factorTwoAffineSinUnweightedKernel_eq_neg_derivative
    (n m : ℕ) :
    factorTwoAffineSinUnweightedKernel n m =
      -factorTwoAffineSinProfileDeriv (factorTwoMomentY n) (m + 1) := by
  unfold factorTwoAffineSinUnweightedKernel factorTwoCauchyU
    factorTwoCauchyX factorTwoAffineSinProfileDeriv
  push_cast
  ring

private theorem factorTwoCauchyU_abs_le_inv_sq
    {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    |factorTwoCauchyU x y| ≤ 1 / x ^ 2 := by
  let D : ℝ := x ^ 2 + y ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hxy : 2 * x * y ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg (x - y)]
  rw [abs_of_nonneg (by
    unfold factorTwoCauchyU
    exact div_nonneg (by positivity) (by positivity))]
  unfold factorTwoCauchyU
  dsimp only [D] at hD hxy ⊢
  calc
    2 * x * y / D ^ 2 ≤ D / D ^ 2 := by
      exact div_le_div_of_nonneg_right hxy (pow_nonneg hD.le 2)
    _ = 1 / D := by field_simp [hD.ne']
    _ ≤ 1 / x ^ 2 := by
      exact one_div_le_one_div_of_le (sq_pos_of_pos hx)
        (by dsimp [D]; nlinarith [sq_nonneg y])

theorem summable_factorTwoAffineSinUnweightedKernel (n : ℕ) :
    Summable (factorTwoAffineSinUnweightedKernel n) := by
  have hmajor : Summable (fun m : ℕ ↦
      1 / ((((m + 1 : ℕ) : ℝ) ^ 2))) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 h
  apply hmajor.of_norm_bounded
  intro m
  rw [Real.norm_eq_abs]
  have hx : 0 < factorTwoCauchyX (m + 1) := by
    unfold factorTwoCauchyX
    push_cast
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hy : 0 ≤ factorTwoMomentY n := by
    unfold factorTwoMomentY factorTwoNaturalFrequency
    exact div_nonneg
      (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n))
      factorTwoMomentLength_pos.le
  have hU := factorTwoCauchyU_abs_le_inv_sq hx hy
  have hxLower : (((m + 1 : ℕ) : ℝ)) ≤ factorTwoCauchyX (m + 1) := by
    unfold factorTwoCauchyX
    push_cast
    norm_num
  have hsquare := pow_le_pow_left₀ (by positivity :
      (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ)) hxLower 2
  exact hU.trans (one_div_le_one_div_of_le (by positivity) hsquare)

private theorem factorTwoAffineSinProfileSecond_abs_le
    {y t : ℝ} (hy : 0 < y) (ht : 0 ≤ t) :
    |factorTwoAffineSinProfileSecondDeriv y t| ≤
      6 * y / (t + 1 / 4) ^ 4 := by
  let u : ℝ := t + 1 / 4
  let D : ℝ := u ^ 2 + y ^ 2
  let P : ℝ := 3 * u ^ 2 - y ^ 2
  have hu : 0 < u := by dsimp [u]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hP : |P| ≤ 3 * D := by
    rw [abs_le]
    constructor <;> dsimp [P, D] <;>
      nlinarith [sq_nonneg u, sq_nonneg y]
  have hu4D2 : u ^ 4 ≤ D ^ 2 := by
    have huD : u ^ 2 ≤ D := by
      dsimp [D]
      nlinarith [sq_nonneg y]
    have hpow := pow_le_pow_left₀ (sq_nonneg u) huD 2
    nlinarith [hpow]
  unfold factorTwoAffineSinProfileSecondDeriv
  dsimp only [u, D, P] at hP hD hu hu4D2 ⊢
  rw [abs_div, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hy,
    abs_of_pos (pow_pos hD 3)]
  calc
    2 * y * |P| / D ^ 3 ≤ 2 * y * (3 * D) / D ^ 3 := by gcongr
    _ = 6 * y / D ^ 2 := by field_simp [hD.ne']; ring
    _ ≤ 6 * y / u ^ 4 := by
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hu 4) hu4D2

private theorem summable_factorTwoAffineSinProfileTail
    {n : ℕ} (hn : n ≠ 0) (N : ℕ) :
    Summable (fun j : ℕ ↦
      factorTwoAffineSinProfile (factorTwoMomentY n) (N + j + 1)) := by
  have hyEq : factorTwoMomentY n = yoshidaScaledFrequency n := by
    unfold factorTwoMomentY factorTwoNaturalFrequency yoshidaScaledFrequency
      yoshidaKappa
    rw [factorTwoMomentLength_eq_yoshidaLength]
    ring
  have hshift := (summable_nat_add_iff (N + 1)).2
    (summable_sineMainTerm hn)
  apply hshift.congr
  intro j
  unfold factorTwoAffineSinProfile sineMainTerm cauchyTailTerm
  rw [hyEq]
  norm_num only [Nat.cast_add, Nat.cast_one]
  congr 1
  ring

private theorem summable_factorTwoAffineSinDerivativeTail
    (n N : ℕ) :
    Summable (fun j : ℕ ↦
      factorTwoAffineSinProfileDeriv (factorTwoMomentY n) (N + j + 1)) := by
  have hshift := (summable_nat_add_iff N).2
    (summable_factorTwoAffineSinUnweightedKernel n)
  have hneg := hshift.neg
  apply hneg.congr
  intro j
  rw [factorTwoAffineSinUnweightedKernel_eq_neg_derivative]
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

private theorem summable_factorTwoAffineSinSecondDerivativeTail
    {n : ℕ} (hn : n ≠ 0) (N : ℕ) :
    Summable (fun j : ℕ ↦
      factorTwoAffineSinProfileSecondDeriv
        (factorTwoMomentY n) (N + j + 1)) := by
  have hy : 0 < factorTwoMomentY n := by
    unfold factorTwoMomentY factorTwoNaturalFrequency
    exact div_pos (mul_pos Real.pi_pos (by
      exact_mod_cast Nat.pos_of_ne_zero hn)) factorTwoMomentLength_pos
  let C : ℝ := 6 * factorTwoMomentY n
  have hbase : Summable (fun j : ℕ ↦
      1 / ((((j + 1 : ℕ) : ℝ) ^ 4))) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 h
  have hmajor : Summable (fun j : ℕ ↦
      C / ((((j + 1 : ℕ) : ℝ) ^ 4))) := by
    simpa [C, div_eq_mul_inv] using hbase.mul_left (6 * factorTwoMomentY n)
  apply hmajor.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs]
  have ht : (0 : ℝ) ≤ (N + j + 1 : ℕ) := by
    exact_mod_cast Nat.zero_le (N + j + 1)
  have hlocal := factorTwoAffineSinProfileSecond_abs_le hy ht
  have hxLower : (((j + 1 : ℕ) : ℝ)) ≤
      ((N + j + 1 : ℕ) : ℝ) + 1 / 4 := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hpow := pow_le_pow_left₀ (by positivity :
      (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ)) hxLower 4
  calc
    |factorTwoAffineSinProfileSecondDeriv
        (factorTwoMomentY n) (N + j + 1)| ≤
        6 * factorTwoMomentY n /
          (((N + j + 1 : ℕ) : ℝ) + 1 / 4) ^ 4 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hlocal
    _ ≤ C / (((j + 1 : ℕ) : ℝ) ^ 4) := by
      dsimp only [C]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpow

/-- First-corrected Euler--Maclaurin main term for the derivative tail. -/
def factorTwoAffineSinDerivativeTailMain (y : ℝ) (N : ℕ) : ℝ :=
  -factorTwoAffineSinProfile y (N + 1) +
    factorTwoAffineSinProfileDeriv y (N + 1) / 2 -
    factorTwoAffineSinProfileSecondDeriv y (N + 1) / 12

private theorem sum_range_factorTwoAffineSinDerivativeCorrectedError_eq
    {y : ℝ} (hy : y ≠ 0) (N M : ℕ) :
    (∑ k ∈ Finset.range M,
        factorTwoAffineSinDerivativeCorrectedError y N k) =
      (∑ k ∈ Finset.range M,
          factorTwoAffineSinProfileDeriv y (N + k + 1)) -
        factorTwoAffineSinProfileDeriv y (N + 1) / 2 +
        factorTwoAffineSinProfileDeriv y (N + M + 1) / 2 -
        (factorTwoAffineSinProfile y (N + M + 1) -
          factorTwoAffineSinProfile y (N + 1)) -
        (factorTwoAffineSinProfileSecondDeriv y (N + M + 1) -
          factorTwoAffineSinProfileSecondDeriv y (N + 1)) / 12 := by
  have hcont : Continuous (factorTwoAffineSinProfileDeriv y) :=
    continuous_iff_continuousAt.mpr fun t ↦
      (hasDerivAt_factorTwoAffineSinProfileDeriv
        (y := y) (t := t) hy).continuousAt
  have hcell (k : ℕ) :
      trapezoidal_error (factorTwoAffineSinProfileDeriv y) 1
          ((N + k : ℕ) + 1) ((N + k : ℕ) + 2) =
        (factorTwoAffineSinProfileDeriv y ((N + k : ℕ) + 1) +
            factorTwoAffineSinProfileDeriv y ((N + k : ℕ) + 2)) / 2 -
          (factorTwoAffineSinProfile y ((N + k : ℕ) + 2) -
            factorTwoAffineSinProfile y ((N + k : ℕ) + 1)) := by
    have hint :
        (∫ t in ((N + k : ℕ) + 1)..((N + k : ℕ) + 2),
          factorTwoAffineSinProfileDeriv y t) =
            factorTwoAffineSinProfile y ((N + k : ℕ) + 2) -
              factorTwoAffineSinProfile y ((N + k : ℕ) + 1) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t _ht
        exact hasDerivAt_factorTwoAffineSinProfile (y := y) (t := t) hy
      · exact hcont.intervalIntegrable _ _
    rw [trapezoidal_error, trapezoidal_integral_one, hint]
    ring
  have hshift :
      (∑ k ∈ Finset.range M,
        factorTwoAffineSinProfileDeriv y ((N + k : ℕ) + 2)) =
        (∑ k ∈ Finset.range M,
          factorTwoAffineSinProfileDeriv y ((N + k : ℕ) + 1)) -
          factorTwoAffineSinProfileDeriv y (N + 1) +
          factorTwoAffineSinProfileDeriv y (N + M + 1) := by
    calc
      _ = (∑ k ∈ Finset.range (M + 1),
            factorTwoAffineSinProfileDeriv y ((N + k : ℕ) + 1)) -
            factorTwoAffineSinProfileDeriv y (N + 1) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      _ = _ := by
        rw [Finset.sum_range_succ]
        norm_num only [Nat.cast_add, Nat.cast_one]
        ring
  have havg :
      (∑ k ∈ Finset.range M,
        (factorTwoAffineSinProfileDeriv y ((N + k : ℕ) + 1) +
          factorTwoAffineSinProfileDeriv y ((N + k : ℕ) + 2)) / 2) =
        (∑ k ∈ Finset.range M,
          factorTwoAffineSinProfileDeriv y ((N + k : ℕ) + 1)) -
          factorTwoAffineSinProfileDeriv y (N + 1) / 2 +
          factorTwoAffineSinProfileDeriv y (N + M + 1) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hshift]
    ring
  have htelProfile :
      (∑ k ∈ Finset.range M,
        (factorTwoAffineSinProfile y ((N + k : ℕ) + 2) -
          factorTwoAffineSinProfile y ((N + k : ℕ) + 1))) =
        factorTwoAffineSinProfile y (N + M + 1) -
          factorTwoAffineSinProfile y (N + 1) := by
    convert (Finset.sum_range_sub
      (fun k : ℕ ↦ factorTwoAffineSinProfile y ((N + k : ℕ) + 1)) M)
      using 1
    all_goals norm_num
    all_goals ring
  have htrap :
      (∑ k ∈ Finset.range M,
        trapezoidal_error (factorTwoAffineSinProfileDeriv y) 1
          ((N + k : ℕ) + 1) ((N + k : ℕ) + 2)) =
        (∑ k ∈ Finset.range M,
          factorTwoAffineSinProfileDeriv y (N + k + 1)) -
          factorTwoAffineSinProfileDeriv y (N + 1) / 2 +
          factorTwoAffineSinProfileDeriv y (N + M + 1) / 2 -
          (factorTwoAffineSinProfile y (N + M + 1) -
            factorTwoAffineSinProfile y (N + 1)) := by
    calc
      _ = ∑ k ∈ Finset.range M,
          ((factorTwoAffineSinProfileDeriv y ((N + k : ℕ) + 1) +
              factorTwoAffineSinProfileDeriv y ((N + k : ℕ) + 2)) / 2 -
            (factorTwoAffineSinProfile y ((N + k : ℕ) + 2) -
              factorTwoAffineSinProfile y ((N + k : ℕ) + 1))) := by
        apply Finset.sum_congr rfl
        intro k _hk
        exact hcell k
      _ = _ := by
        rw [Finset.sum_sub_distrib, havg, htelProfile]
        norm_num only [Nat.cast_add, Nat.cast_one]
  have htelSecond :
      (∑ k ∈ Finset.range M,
        (factorTwoAffineSinProfileSecondDeriv y ((N + k : ℕ) + 2) -
          factorTwoAffineSinProfileSecondDeriv y ((N + k : ℕ) + 1))) =
        factorTwoAffineSinProfileSecondDeriv y (N + M + 1) -
          factorTwoAffineSinProfileSecondDeriv y (N + 1) := by
    convert (Finset.sum_range_sub
      (fun k : ℕ ↦
        factorTwoAffineSinProfileSecondDeriv y ((N + k : ℕ) + 1)) M)
      using 1
    all_goals norm_num
    all_goals ring
  unfold factorTwoAffineSinDerivativeCorrectedError
  rw [Finset.sum_sub_distrib, htrap, ← Finset.sum_div, htelSecond]

private theorem tendsto_sum_factorTwoAffineSinDerivativeCorrectedError
    {n : ℕ} (hn : n ≠ 0) (N : ℕ) :
    Tendsto
      (fun M : ℕ ↦ ∑ k ∈ Finset.range M,
        factorTwoAffineSinDerivativeCorrectedError
          (factorTwoMomentY n) N k)
      atTop
      (nhds ((∑' j : ℕ,
          factorTwoAffineSinProfileDeriv
            (factorTwoMomentY n) (N + j + 1)) -
        factorTwoAffineSinDerivativeTailMain (factorTwoMomentY n) N)) := by
  have hsum := (summable_factorTwoAffineSinDerivativeTail n N).hasSum.tendsto_sum_nat
  have hderiv :=
    (summable_factorTwoAffineSinDerivativeTail n N).tendsto_atTop_zero
  have hsecond :=
    (summable_factorTwoAffineSinSecondDerivativeTail hn N).tendsto_atTop_zero
  have hprofile :=
    (summable_factorTwoAffineSinProfileTail hn N).tendsto_atTop_zero
  have hderivStart : Tendsto
      (fun _ : ℕ ↦ factorTwoAffineSinProfileDeriv
        (factorTwoMomentY n) (N + 1)) atTop
      (nhds (factorTwoAffineSinProfileDeriv
        (factorTwoMomentY n) (N + 1))) := tendsto_const_nhds
  have hprofileStart : Tendsto
      (fun _ : ℕ ↦ factorTwoAffineSinProfile
        (factorTwoMomentY n) (N + 1)) atTop
      (nhds (factorTwoAffineSinProfile
        (factorTwoMomentY n) (N + 1))) := tendsto_const_nhds
  have hsecondStart : Tendsto
      (fun _ : ℕ ↦ factorTwoAffineSinProfileSecondDeriv
        (factorTwoMomentY n) (N + 1)) atTop
      (nhds (factorTwoAffineSinProfileSecondDeriv
        (factorTwoMomentY n) (N + 1))) := tendsto_const_nhds
  have hlim := ((((hsum.sub (hderivStart.div_const 2)).add
      (hderiv.div_const 2)).sub (hprofile.sub hprofileStart)).sub
      ((hsecond.sub hsecondStart).div_const 12))
  convert hlim using 1
  · funext M
    rw [sum_range_factorTwoAffineSinDerivativeCorrectedError_eq
      (by
        unfold factorTwoMomentY factorTwoNaturalFrequency
        exact (div_pos (mul_pos Real.pi_pos (by
          exact_mod_cast Nat.pos_of_ne_zero hn))
          factorTwoMomentLength_pos).ne') N M]
  · unfold factorTwoAffineSinDerivativeTailMain
    ring

/-- Shifted derivative-series enclosure. -/
theorem factorTwoAffineSinDerivativeTail_sub_main_abs_le
    {n : ℕ} (hn : n ≠ 0) (N : ℕ) :
    |(∑' j : ℕ,
        factorTwoAffineSinProfileDeriv
          (factorTwoMomentY n) (N + j + 1)) -
        factorTwoAffineSinDerivativeTailMain (factorTwoMomentY n) N| ≤
      factorTwoAffineSinDerivativeTailRadius (factorTwoMomentY n) N := by
  have hy : 0 < factorTwoMomentY n := by
    unfold factorTwoMomentY factorTwoNaturalFrequency
    exact div_pos (mul_pos Real.pi_pos (by
      exact_mod_cast Nat.pos_of_ne_zero hn)) factorTwoMomentLength_pos
  have hlim := tendsto_sum_factorTwoAffineSinDerivativeCorrectedError hn N
  exact le_of_tendsto' hlim.abs fun M ↦
    factorTwoAffineSinDerivativeCorrectedError_sum_abs_le hy N M

/-! ## Exact dyadic split and geometric correction -/

def factorTwoAffineSinDyadicCorrection (n m : ℕ) : ℝ :=
  (factorTwoDyadicD (m + 1) - 1) *
    factorTwoAffineSinUnweightedKernel n m

theorem factorTwoAntisymmetricAffineSinDyadicKernel_eq_main_add_correction
    (n m : ℕ) :
    factorTwoAntisymmetricAffineSinDyadicKernel n (m + 1) =
      factorTwoAffineSinUnweightedKernel n m +
        factorTwoAffineSinDyadicCorrection n m := by
  change
    factorTwoDyadicD (m + 1) * factorTwoAffineSinUnweightedKernel n m =
      factorTwoAffineSinUnweightedKernel n m +
        (factorTwoDyadicD (m + 1) - 1) *
          factorTwoAffineSinUnweightedKernel n m
  ring

private theorem factorTwoDyadicQ_nonneg_local (k : ℕ) :
    0 ≤ factorTwoDyadicQ k := by
  unfold factorTwoDyadicQ
  positivity

private theorem factorTwoDyadicQ_le_invFourPow_local (k : ℕ) :
    factorTwoDyadicQ k ≤ (1 / 4 : ℝ) ^ k := by
  have hsqrt : (Real.sqrt 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact Real.one_le_sqrt.mpr (by norm_num)
  unfold factorTwoDyadicQ
  rw [show (1 / 4 : ℝ) ^ k = 1 / (4 : ℝ) ^ k by
    rw [div_pow]
    simp]
  exact div_le_div_of_nonneg_right hsqrt (by positivity)

private theorem factorTwoDyadicQ_le_one_local (k : ℕ) :
    factorTwoDyadicQ k ≤ 1 :=
  (factorTwoDyadicQ_le_invFourPow_local k).trans
    (pow_le_one₀ (by norm_num) (by norm_num))

private theorem factorTwoAffineSinUnweightedKernel_abs_le_one
    (n m : ℕ) :
    |factorTwoAffineSinUnweightedKernel n m| ≤ 1 := by
  have hx : 0 < factorTwoCauchyX (m + 1) := by
    unfold factorTwoCauchyX
    push_cast
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hy : 0 ≤ factorTwoMomentY n := by
    unfold factorTwoMomentY factorTwoNaturalFrequency
    exact div_nonneg
      (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n))
      factorTwoMomentLength_pos.le
  have h := factorTwoCauchyU_abs_le_inv_sq hx hy
  have hxOne : 1 ≤ factorTwoCauchyX (m + 1) := by
    unfold factorTwoCauchyX
    push_cast
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    norm_num
    linarith
  have hinv : 1 / factorTwoCauchyX (m + 1) ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hx)]
    nlinarith
  exact h.trans hinv

private theorem factorTwoAffineSinDyadicCorrection_abs_le_geometric
    (n m : ℕ) :
    |factorTwoAffineSinDyadicCorrection n m| ≤
      2 * (1 / 4 : ℝ) ^ (m + 1) := by
  let q := factorTwoDyadicQ (m + 1)
  have hq0 : 0 ≤ q := factorTwoDyadicQ_nonneg_local (m + 1)
  have hq1 : q ≤ 1 := factorTwoDyadicQ_le_one_local (m + 1)
  have hq4 : q ≤ (1 / 4 : ℝ) ^ (m + 1) :=
    factorTwoDyadicQ_le_invFourPow_local (m + 1)
  have hD : factorTwoDyadicD (m + 1) ≤ 1 := by
    unfold factorTwoDyadicD
    dsimp only [q] at hq0 hq1 ⊢
    nlinarith [sq_nonneg (1 - factorTwoDyadicQ (m + 1))]
  have hdiff : |factorTwoDyadicD (m + 1) - 1| ≤ 2 * q := by
    rw [abs_of_nonpos (sub_nonpos.mpr hD)]
    unfold factorTwoDyadicD
    dsimp only [q] at hq0 hq1 ⊢
    nlinarith [sq_nonneg (factorTwoDyadicQ (m + 1))]
  unfold factorTwoAffineSinDyadicCorrection
  rw [abs_mul]
  calc
    |factorTwoDyadicD (m + 1) - 1| *
        |factorTwoAffineSinUnweightedKernel n m| ≤
        (2 * q) * 1 :=
      mul_le_mul hdiff (factorTwoAffineSinUnweightedKernel_abs_le_one n m)
        (abs_nonneg _) (by positivity)
    _ = 2 * q := by ring
    _ ≤ 2 * (1 / 4 : ℝ) ^ (m + 1) :=
      mul_le_mul_of_nonneg_left hq4 (by norm_num)

theorem summable_factorTwoAffineSinDyadicCorrection (n : ℕ) :
    Summable (factorTwoAffineSinDyadicCorrection n) := by
  let C : ℝ := 2 * (1 / 4 : ℝ)
  have hgeom : Summable (fun m : ℕ ↦ C * (1 / 4 : ℝ) ^ m) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left C
  apply hgeom.of_norm_bounded
  intro m
  rw [Real.norm_eq_abs]
  have h := factorTwoAffineSinDyadicCorrection_abs_le_geometric n m
  rw [pow_succ] at h
  dsimp only [C]
  nlinarith [h]

theorem factorTwoAntisymmetricAffineSinDyadic_tsum_eq_main_add_correction
    (n : ℕ) :
    (∑' m : ℕ,
        factorTwoAntisymmetricAffineSinDyadicKernel n (m + 1)) =
      (∑' m : ℕ, factorTwoAffineSinUnweightedKernel n m) +
        ∑' m : ℕ, factorTwoAffineSinDyadicCorrection n m := by
  rw [← (summable_factorTwoAffineSinUnweightedKernel n).tsum_add
    (summable_factorTwoAffineSinDyadicCorrection n)]
  apply tsum_congr
  exact factorTwoAntisymmetricAffineSinDyadicKernel_eq_main_add_correction n

/-- Uniform geometric absolute-tail control for the dyadic defect. -/
theorem factorTwoAffineSinDyadicCorrection_tail_abs_le
    (n K : ℕ) :
    |(∑' j : ℕ, factorTwoAffineSinDyadicCorrection n (K + j))| ≤
      1 / (4 : ℝ) ^ K := by
  let C : ℝ := 2 * (1 / 4 : ℝ) ^ (K + 1)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hgeom : Summable (fun j : ℕ ↦ C * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left C
  have hcorr : Summable
      (fun j : ℕ ↦ factorTwoAffineSinDyadicCorrection n (K + j)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff K).2
        (summable_factorTwoAffineSinDyadicCorrection n)
  have habs : Summable
      (fun j : ℕ ↦ |factorTwoAffineSinDyadicCorrection n (K + j)|) := by
    simpa only [Real.norm_eq_abs] using hcorr.norm
  have hpoint (j : ℕ) :
      |factorTwoAffineSinDyadicCorrection n (K + j)| ≤
        C * (1 / 4 : ℝ) ^ j := by
    have h := factorTwoAffineSinDyadicCorrection_abs_le_geometric n (K + j)
    rw [show K + j + 1 = (K + 1) + j by omega, pow_add] at h
    simpa only [C, mul_assoc] using h
  have hnorm :
      |(∑' j : ℕ, factorTwoAffineSinDyadicCorrection n (K + j))| ≤
        ∑' j : ℕ, |factorTwoAffineSinDyadicCorrection n (K + j)| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hcorr.norm
  have hsum := habs.tsum_le_tsum hpoint hgeom
  calc
    |(∑' j : ℕ, factorTwoAffineSinDyadicCorrection n (K + j))| ≤
        ∑' j : ℕ, |factorTwoAffineSinDyadicCorrection n (K + j)| := hnorm
    _ ≤ ∑' j : ℕ, C * (1 / 4 : ℝ) ^ j := hsum
    _ = C * (1 - (1 / 4 : ℝ))⁻¹ := by
      rw [tsum_mul_left,
        tsum_geometric_of_norm_lt_one
          (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
    _ ≤ 1 / (4 : ℝ) ^ K := by
      dsimp only [C]
      rw [← one_div_pow]
      rw [pow_succ]
      norm_num
      have hpow : 0 ≤ (1 / 4 : ℝ) ^ K := by positivity
      nlinarith

/-! ## Exact rational kernel and tail intervals -/

private theorem factorTwoAffineSinYInterval_lower_nonneg (n : ℕ) :
    0 ≤ (factorTwoAffineCosYInterval n).lower := by
  change 0 ≤ piFineInterval.lower * n /
    factorTwoPrimeLogTwoInterval.upper
  unfold piFineInterval factorTwoPrimeLogTwoInterval
  positivity

private theorem factorTwoAffineSinDenomInterval_lower_pos (n m : ℕ) :
    0 < (factorTwoAffineCosDenomInterval n m).lower := by
  change 0 < factorTwoAffineCosXQ m ^ 2 +
    (factorTwoAffineCosYInterval n).lower ^ 2
  have hx : 0 < factorTwoAffineCosXQ m := by
    unfold factorTwoAffineCosXQ
    positivity
  positivity

private theorem factorTwoAffineSin_interval_mul_lower_pos
    {I J : RatInterval} (hI : 0 < I.lower) (hJ : 0 < J.lower)
    (hIv : I.Valid) (hJv : J.Valid) :
    0 < (I * J).lower := by
  have hIu : 0 < I.upper := hI.trans_le hIv
  have hJu : 0 < J.upper := hJ.trans_le hJv
  change 0 < min (min (I.lower * J.lower) (I.lower * J.upper))
    (min (I.upper * J.lower) (I.upper * J.upper))
  simp only [lt_min_iff]
  exact ⟨⟨mul_pos hI hJ, mul_pos hI hJu⟩,
    ⟨mul_pos hIu hJ, mul_pos hIu hJu⟩⟩

/-- Direct interval evaluation of the unweighted `U` kernel. -/
def factorTwoAffineSinUnweightedKernelInterval (n m : ℕ) : RatInterval :=
  let x := pure (factorTwoAffineCosXQ m)
  let y := factorTwoAffineCosYInterval n
  let d := factorTwoAffineCosDenomInterval n m
  (pure 2 * x * y) / nonnegSquare d

theorem factorTwoAffineSinUnweightedKernelInterval_contains (n m : ℕ) :
    (factorTwoAffineSinUnweightedKernelInterval n m).Contains
      (factorTwoAffineSinUnweightedKernel n m) := by
  have hy := factorTwoAffineCosYInterval_contains n
  have hy2 := contains_nonnegSquare
    (factorTwoAffineSinYInterval_lower_nonneg n) hy
  have hx : (pure (factorTwoAffineCosXQ m)).Contains
      (factorTwoCauchyX (m + 1)) := by
    convert contains_pure (factorTwoAffineCosXQ m) using 1
    unfold factorTwoAffineCosXQ factorTwoCauchyX
    push_cast
    ring
  have hx2 : (pure (factorTwoAffineCosXQ m ^ 2)).Contains
      (factorTwoCauchyX (m + 1) ^ 2) := by
    convert contains_pure (factorTwoAffineCosXQ m ^ 2) using 1
    unfold factorTwoAffineCosXQ factorTwoCauchyX
    push_cast
    ring
  have hd : (factorTwoAffineCosDenomInterval n m).Contains
      (factorTwoCauchyX (m + 1) ^ 2 + factorTwoMomentY n ^ 2) :=
    contains_add hx2 hy2
  have hd2 := contains_nonnegSquare
    (factorTwoAffineSinDenomInterval_lower_pos n m).le hd
  unfold factorTwoAffineSinUnweightedKernelInterval
    factorTwoAffineSinUnweightedKernel factorTwoCauchyU
  exact contains_div_of_pos (by
      change 0 < (factorTwoAffineCosDenomInterval n m).lower ^ 2
      exact pow_pos (factorTwoAffineSinDenomInterval_lower_pos n m) 2)
    (contains_mul (contains_mul (contains_pure 2) hx) hy) hd2

def factorTwoAffineSinUnweightedHeadInterval
    (n : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | K + 1 => factorTwoAffineSinUnweightedHeadInterval n K +
      factorTwoAffineSinUnweightedKernelInterval n K

theorem factorTwoAffineSinUnweightedHeadInterval_contains (n K : ℕ) :
    (factorTwoAffineSinUnweightedHeadInterval n K).Contains
      (∑ m ∈ Finset.range K, factorTwoAffineSinUnweightedKernel n m) := by
  induction K with
  | zero =>
      norm_num [factorTwoAffineSinUnweightedHeadInterval, Contains,
        RatInterval.pure]
  | succ K ih =>
      rw [Finset.sum_range_succ]
      exact contains_add ih
        (factorTwoAffineSinUnweightedKernelInterval_contains n K)

private def factorTwoAffineSinProfileInterval (n N : ℕ) : RatInterval :=
  factorTwoAffineCosYInterval n / factorTwoAffineCosDenomInterval n N

private def factorTwoAffineSinProfileDerivInterval (n N : ℕ) : RatInterval :=
  let x := pure (factorTwoAffineCosXQ N)
  let y := factorTwoAffineCosYInterval n
  let d := factorTwoAffineCosDenomInterval n N
  (pure (-2) * y * x) / nonnegSquare d

private def factorTwoAffineSinProfileSecondInterval (n N : ℕ) : RatInterval :=
  let x2 := pure (factorTwoAffineCosXQ N ^ 2)
  let y := factorTwoAffineCosYInterval n
  let y2 := nonnegSquare y
  let d := factorTwoAffineCosDenomInterval n N
  (pure 2 * y * (pure 3 * x2 - y2)) / (d * nonnegSquare d)

/-- Rational enclosure of the unweighted `U`-tail main term. -/
def factorTwoAffineSinUnweightedTailMainInterval (n N : ℕ) : RatInterval :=
  factorTwoAffineSinProfileInterval n N -
    factorTwoAffineSinProfileDerivInterval n N / pure 2 +
    factorTwoAffineSinProfileSecondInterval n N / pure 12

private theorem factorTwoAffineSinUnweightedTailMainInterval_contains
    (n N : ℕ) :
    (factorTwoAffineSinUnweightedTailMainInterval n N).Contains
      (-factorTwoAffineSinDerivativeTailMain (factorTwoMomentY n) N) := by
  have hy := factorTwoAffineCosYInterval_contains n
  have hy2 := contains_nonnegSquare
    (factorTwoAffineSinYInterval_lower_nonneg n) hy
  have hx : (pure (factorTwoAffineCosXQ N)).Contains
      (((N : ℝ) + 1 + 1 / 4)) := by
    norm_num [Contains, RatInterval.pure, factorTwoAffineCosXQ]
  have hx2 : (pure (factorTwoAffineCosXQ N ^ 2)).Contains
      (((N : ℝ) + 1 + 1 / 4) ^ 2) := by
    norm_num [Contains, RatInterval.pure, factorTwoAffineCosXQ]
  have hd : (factorTwoAffineCosDenomInterval n N).Contains
      (((N : ℝ) + 1 + 1 / 4) ^ 2 + factorTwoMomentY n ^ 2) :=
    contains_add hx2 hy2
  have hd2 := contains_nonnegSquare
    (factorTwoAffineSinDenomInterval_lower_pos n N).le hd
  have hd3 : (factorTwoAffineCosDenomInterval n N *
      nonnegSquare (factorTwoAffineCosDenomInterval n N)).Contains
        ((((N : ℝ) + 1 + 1 / 4) ^ 2 + factorTwoMomentY n ^ 2) ^ 3) := by
    convert contains_mul hd hd2 using 1
    ring
  have hprofile : (factorTwoAffineSinProfileInterval n N).Contains
      (factorTwoAffineSinProfile (factorTwoMomentY n) (N + 1)) := by
    unfold factorTwoAffineSinProfileInterval factorTwoAffineSinProfile
    exact contains_div_of_pos (factorTwoAffineSinDenomInterval_lower_pos n N)
      hy hd
  have hderiv : (factorTwoAffineSinProfileDerivInterval n N).Contains
      (factorTwoAffineSinProfileDeriv (factorTwoMomentY n) (N + 1)) := by
    unfold factorTwoAffineSinProfileDerivInterval
      factorTwoAffineSinProfileDeriv
    exact contains_div_of_pos (by
        change 0 < (factorTwoAffineCosDenomInterval n N).lower ^ 2
        exact pow_pos (factorTwoAffineSinDenomInterval_lower_pos n N) 2)
      (contains_mul (contains_mul
        (show (RatInterval.pure (-2 : ℚ)).Contains (-2 : ℝ) by
          simpa using contains_pure (-2 : ℚ)) hy) hx) hd2
  have hsecond : (factorTwoAffineSinProfileSecondInterval n N).Contains
      (factorTwoAffineSinProfileSecondDeriv
        (factorTwoMomentY n) (N + 1)) := by
    unfold factorTwoAffineSinProfileSecondInterval
      factorTwoAffineSinProfileSecondDeriv
    exact contains_div_of_pos
      (factorTwoAffineSin_interval_mul_lower_pos
        (factorTwoAffineSinDenomInterval_lower_pos n N)
        (by
          change 0 < (factorTwoAffineCosDenomInterval n N).lower ^ 2
          exact pow_pos (factorTwoAffineSinDenomInterval_lower_pos n N) 2)
        (valid_of_contains hd) (valid_of_contains hd2))
      (contains_mul (contains_mul
        (show (RatInterval.pure (2 : ℚ)).Contains (2 : ℝ) by
          simpa using contains_pure (2 : ℚ)) hy)
        (contains_sub (contains_mul
          (show (RatInterval.pure (3 : ℚ)).Contains (3 : ℝ) by
            simpa using contains_pure (3 : ℚ)) hx2) hy2)) hd3
  unfold factorTwoAffineSinUnweightedTailMainInterval
    factorTwoAffineSinDerivativeTailMain
  have htwo : (RatInterval.pure (2 : ℚ)).Contains (2 : ℝ) := by
    simpa using contains_pure (2 : ℚ)
  have htwelve : (RatInterval.pure (12 : ℚ)).Contains (12 : ℝ) := by
    simpa using contains_pure (12 : ℚ)
  convert contains_add
    (contains_sub hprofile
      (contains_div_of_pos (by norm_num [RatInterval.pure]) hderiv htwo))
    (contains_div_of_pos (by norm_num [RatInterval.pure]) hsecond htwelve)
    using 1
  ring

def factorTwoAffineSinDerivativeTailRadiusQ (n N : ℕ) : ℚ :=
  2 * (factorTwoAffineCosYInterval n).upper /
    (factorTwoAffineCosXQ N ^ 5)

def factorTwoAffineSinUnweightedTailInterval (n N : ℕ) : RatInterval :=
  let r := factorTwoAffineSinDerivativeTailRadiusQ n N
  factorTwoAffineSinUnweightedTailMainInterval n N + ⟨-r, r⟩

private theorem factorTwoAffineSinDerivativeTailRadius_le (n N : ℕ) :
    factorTwoAffineSinDerivativeTailRadius (factorTwoMomentY n) N ≤
      (factorTwoAffineSinDerivativeTailRadiusQ n N : ℝ) := by
  have hy := factorTwoAffineCosYInterval_contains n
  have hden : (0 : ℝ) < ((N : ℝ) + 1 + 1 / 4) ^ 5 := by positivity
  unfold factorTwoAffineSinDerivativeTailRadius
    factorTwoAffineSinDerivativeTailRadiusQ factorTwoAffineCosXQ
  norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow,
    Rat.cast_add, Rat.cast_natCast]
  apply div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hy.2 (by norm_num)) hden.le

theorem factorTwoAffineSinUnweightedTailInterval_contains
    {n : ℕ} (hn : n ≠ 0) (N : ℕ) :
    (factorTwoAffineSinUnweightedTailInterval n N).Contains
      (∑' j : ℕ, factorTwoAffineSinUnweightedKernel n (N + j)) := by
  have herr := factorTwoAffineSinDerivativeTail_sub_main_abs_le hn N
  have hrad := factorTwoAffineSinDerivativeTailRadius_le n N
  have hmain := factorTwoAffineSinUnweightedTailMainInterval_contains n N
  have htailEq :
      (∑' j : ℕ, factorTwoAffineSinUnweightedKernel n (N + j)) =
        -(∑' j : ℕ, factorTwoAffineSinProfileDeriv
          (factorTwoMomentY n) (N + j + 1)) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro j
    rw [factorTwoAffineSinUnweightedKernel_eq_neg_derivative]
    norm_num only [Nat.cast_add]
  let r : ℝ := (factorTwoAffineSinDerivativeTailRadiusQ n N : ℚ)
  have he : -r ≤
        (∑' j : ℕ, factorTwoAffineSinUnweightedKernel n (N + j)) -
          (-factorTwoAffineSinDerivativeTailMain (factorTwoMomentY n) N) ∧
      (∑' j : ℕ, factorTwoAffineSinUnweightedKernel n (N + j)) -
          (-factorTwoAffineSinDerivativeTailMain (factorTwoMomentY n) N) ≤ r := by
    rw [htailEq]
    rw [abs_le] at herr
    constructor <;> dsimp only [r] <;> linarith
  have heI : (⟨-factorTwoAffineSinDerivativeTailRadiusQ n N,
      factorTwoAffineSinDerivativeTailRadiusQ n N⟩ : RatInterval).Contains
        ((∑' j : ℕ, factorTwoAffineSinUnweightedKernel n (N + j)) -
          (-factorTwoAffineSinDerivativeTailMain (factorTwoMomentY n) N)) := by
    simpa only [Contains, Rat.cast_neg] using he
  unfold factorTwoAffineSinUnweightedTailInterval
  have h := contains_add hmain heI
  convert h using 1
  ring

def factorTwoAffineSinUnweightedHeadCount : ℕ := 512

def factorTwoAffineSinUnweightedSeriesInterval (n : ℕ) : RatInterval :=
  factorTwoAffineSinUnweightedHeadInterval n
      factorTwoAffineSinUnweightedHeadCount +
    factorTwoAffineSinUnweightedTailInterval n
      factorTwoAffineSinUnweightedHeadCount

theorem factorTwoAffineSinUnweightedSeriesInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (factorTwoAffineSinUnweightedSeriesInterval n).Contains
      (∑' m : ℕ, factorTwoAffineSinUnweightedKernel n m) := by
  have hsplit :=
    (summable_factorTwoAffineSinUnweightedKernel n).sum_add_tsum_nat_add
      factorTwoAffineSinUnweightedHeadCount
  rw [← hsplit]
  unfold factorTwoAffineSinUnweightedSeriesInterval
  exact contains_add
    (factorTwoAffineSinUnweightedHeadInterval_contains n
      factorTwoAffineSinUnweightedHeadCount)
    (by simpa [Nat.add_comm] using
      (factorTwoAffineSinUnweightedTailInterval_contains hn
        factorTwoAffineSinUnweightedHeadCount))

/-! ## Rational dyadic-correction intervals -/

def factorTwoAffineSinDyadicCorrectionInterval (n m : ℕ) : RatInterval :=
  (factorTwoAffineCosDyadicDInterval (m + 1) - pure 1) *
    factorTwoAffineSinUnweightedKernelInterval n m

theorem factorTwoAffineSinDyadicCorrectionInterval_contains (n m : ℕ) :
    (factorTwoAffineSinDyadicCorrectionInterval n m).Contains
      (factorTwoAffineSinDyadicCorrection n m) := by
  unfold factorTwoAffineSinDyadicCorrectionInterval
    factorTwoAffineSinDyadicCorrection
  exact contains_mul
    (contains_sub (factorTwoAffineCosDyadicDInterval_contains (m + 1))
      (show (RatInterval.pure (1 : ℚ)).Contains (1 : ℝ) by
        simpa using contains_pure (1 : ℚ)))
    (factorTwoAffineSinUnweightedKernelInterval_contains n m)

def factorTwoAffineSinDyadicCorrectionHeadInterval
    (n : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | K + 1 => factorTwoAffineSinDyadicCorrectionHeadInterval n K +
      factorTwoAffineSinDyadicCorrectionInterval n K

theorem factorTwoAffineSinDyadicCorrectionHeadInterval_contains
    (n K : ℕ) :
    (factorTwoAffineSinDyadicCorrectionHeadInterval n K).Contains
      (∑ m ∈ Finset.range K, factorTwoAffineSinDyadicCorrection n m) := by
  induction K with
  | zero =>
      norm_num [factorTwoAffineSinDyadicCorrectionHeadInterval, Contains,
        RatInterval.pure]
  | succ K ih =>
      rw [Finset.sum_range_succ]
      exact contains_add ih
        (factorTwoAffineSinDyadicCorrectionInterval_contains n K)

private def factorTwoAffineSinDyadicCorrectionTailRadiusQ (K : ℕ) : ℚ :=
  1 / (4 : ℚ) ^ K

def factorTwoAffineSinDyadicCorrectionTailInterval (K : ℕ) : RatInterval :=
  let r := factorTwoAffineSinDyadicCorrectionTailRadiusQ K
  ⟨-r, r⟩

theorem factorTwoAffineSinDyadicCorrectionTailInterval_contains
    (n K : ℕ) :
    (factorTwoAffineSinDyadicCorrectionTailInterval K).Contains
      (∑' j : ℕ, factorTwoAffineSinDyadicCorrection n (K + j)) := by
  have h := factorTwoAffineSinDyadicCorrection_tail_abs_le n K
  rw [abs_le] at h
  simpa only [factorTwoAffineSinDyadicCorrectionTailInterval,
    factorTwoAffineSinDyadicCorrectionTailRadiusQ, Contains, Rat.cast_neg,
    Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using h

def factorTwoAffineSinDyadicCorrectionSeriesInterval (n : ℕ) : RatInterval :=
  factorTwoAffineSinDyadicCorrectionHeadInterval n 20 +
    factorTwoAffineSinDyadicCorrectionTailInterval 20

theorem factorTwoAffineSinDyadicCorrectionSeriesInterval_contains (n : ℕ) :
    (factorTwoAffineSinDyadicCorrectionSeriesInterval n).Contains
      (∑' m : ℕ, factorTwoAffineSinDyadicCorrection n m) := by
  have hsplit :=
    (summable_factorTwoAffineSinDyadicCorrection n).sum_add_tsum_nat_add 20
  rw [← hsplit]
  unfold factorTwoAffineSinDyadicCorrectionSeriesInterval
  exact contains_add
    (factorTwoAffineSinDyadicCorrectionHeadInterval_contains n 20)
    (by simpa [Nat.add_comm] using
      (factorTwoAffineSinDyadicCorrectionTailInterval_contains n 20))

/-- Complete accelerated enclosure of the dyadic `U` series. -/
def factorTwoAffineSinDyadicSeriesInterval (n : ℕ) : RatInterval :=
  factorTwoAffineSinUnweightedSeriesInterval n +
    factorTwoAffineSinDyadicCorrectionSeriesInterval n

theorem factorTwoAffineSinDyadicSeriesInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (factorTwoAffineSinDyadicSeriesInterval n).Contains
      (∑' m : ℕ,
        factorTwoAntisymmetricAffineSinDyadicKernel n (m + 1)) := by
  rw [factorTwoAntisymmetricAffineSinDyadic_tsum_eq_main_add_correction]
  exact contains_add
    (factorTwoAffineSinUnweightedSeriesInterval_contains hn)
    (factorTwoAffineSinDyadicCorrectionSeriesInterval_contains n)

/-! ## Complete affine-sine moments -/

/-- Direct rational enclosure of the exceptional `j = 0` `U` kernel. -/
def factorTwoAffineSinInitialKernelInterval (n : ℕ) : RatInterval :=
  let x := pure (1 / 4 : ℚ)
  let x2 := pure ((1 / 4 : ℚ) ^ 2)
  let y := factorTwoAffineCosYInterval n
  let y2 := nonnegSquare y
  let d := x2 + y2
  (pure 2 * x * y) / nonnegSquare d

theorem factorTwoAffineSinInitialKernelInterval_contains (n : ℕ) :
    (factorTwoAffineSinInitialKernelInterval n).Contains
      (factorTwoCauchyU (factorTwoCauchyX 0) (factorTwoMomentY n)) := by
  have hy := factorTwoAffineCosYInterval_contains n
  have hy2 := contains_nonnegSquare
    (factorTwoAffineSinYInterval_lower_nonneg n) hy
  have hx : (pure (1 / 4 : ℚ)).Contains (factorTwoCauchyX 0) := by
    norm_num [Contains, RatInterval.pure, factorTwoCauchyX]
  have hx2 : (pure ((1 / 4 : ℚ) ^ 2)).Contains
      (factorTwoCauchyX 0 ^ 2) := by
    norm_num [Contains, RatInterval.pure, factorTwoCauchyX]
  have hd : (pure ((1 / 4 : ℚ) ^ 2) +
      nonnegSquare (factorTwoAffineCosYInterval n)).Contains
        (factorTwoCauchyX 0 ^ 2 + factorTwoMomentY n ^ 2) :=
    contains_add hx2 hy2
  have hdLower : 0 < (pure ((1 / 4 : ℚ) ^ 2) +
      nonnegSquare (factorTwoAffineCosYInterval n)).lower := by
    change 0 < (1 / 4 : ℚ) ^ 2 +
      (factorTwoAffineCosYInterval n).lower ^ 2
    positivity
  have hd2 := contains_nonnegSquare hdLower.le hd
  unfold factorTwoAffineSinInitialKernelInterval factorTwoCauchyU
  exact contains_div_of_pos (by
      change 0 < (pure ((1 / 4 : ℚ) ^ 2) +
        nonnegSquare (factorTwoAffineCosYInterval n)).lower ^ 2
      exact pow_pos hdLower 2)
    (contains_mul (contains_mul (contains_pure 2) hx) hy) hd2

/-- Positive-mode interval assembled from the growing head, accelerated
dyadic series, and retained-prime affine sine atom. -/
def factorTwoAntisymmetricAffineSinPositiveInterval
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  (factorTwoHeadDefectInterval / factorTwoPrimeLogTwoInterval) *
      factorTwoAffineSinInitialKernelInterval n.1 +
    (pure 1 / factorTwoPrimeLogTwoInterval) *
      factorTwoAffineSinDyadicSeriesInterval n.1 +
    pure 2 * factorTwoPrimeBetaInterval *
      factorTwoPrimeAffineHeightInterval * factorTwoPrimeSinInterval n

theorem factorTwoAntisymmetricAffineSinPositiveInterval_contains
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    (factorTwoAntisymmetricAffineSinPositiveInterval n).Contains
      (factorTwoAntisymmetricAffineSinMoment n.1) := by
  have hheadCoeff :
      (factorTwoHeadDefectInterval /
        factorTwoPrimeLogTwoInterval).Contains
          (factorTwoHeadDefect / factorTwoMomentLength) :=
    contains_div_of_pos (by norm_num [factorTwoPrimeLogTwoInterval])
      factorTwoHeadDefectInterval_contains
      factorTwoPrimeLogTwoInterval_contains
  have hseriesCoeff :
      (pure 1 / factorTwoPrimeLogTwoInterval).Contains
          (1 / factorTwoMomentLength) :=
    contains_div_of_pos (by norm_num [factorTwoPrimeLogTwoInterval])
      (show (RatInterval.pure (1 : ℚ)).Contains (1 : ℝ) by
        simpa using contains_pure (1 : ℚ))
      factorTwoPrimeLogTwoInterval_contains
  have hprime :
      (pure 2 * factorTwoPrimeBetaInterval *
        factorTwoPrimeAffineHeightInterval *
          factorTwoPrimeSinInterval n).Contains
        (2 * (Real.log 3 / Real.sqrt 3) *
          (2 - 2 * factorTwoPrimeShift / factorTwoMomentLength) *
          Real.sin (2 * factorTwoMomentY n.1 * factorTwoPrimeShift)) :=
    contains_mul
      (contains_mul
        (contains_mul (contains_pure 2)
          factorTwoPrimeBetaInterval_contains)
        factorTwoPrimeAffineHeightInterval_contains)
      (factorTwoPrimeSinInterval_contains n)
  rw [factorTwoAntisymmetricAffineSinMoment_eq_dyadicCauchySeries n hn]
  exact contains_add
    (contains_add
      (contains_mul hheadCoeff
        (factorTwoAffineSinInitialKernelInterval_contains n.1))
      (contains_mul hseriesCoeff
        (factorTwoAffineSinDyadicSeriesInterval_contains hn)))
    hprime

@[simp] theorem factorTwoAntisymmetricAffineSinMoment_zero :
    factorTwoAntisymmetricAffineSinMoment 0 = 0 := by
  unfold factorTwoAntisymmetricAffineSinMoment
    factorTwoAntisymmetricPerturbationFunctional factorTwoNaturalFrequency
  simp

/-- Public exact rational enclosure of every canonical affine-sine
perturbation moment.  The zero mode is exact. -/
def factorTwoAntisymmetricAffineSinMomentInterval
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  if n.1 = 0 then RatInterval.pure 0
  else factorTwoAntisymmetricAffineSinPositiveInterval n

theorem factorTwoAntisymmetricAffineSinMomentInterval_contains
    (n : FactorTwoCanonicalEvenIndex) :
    (factorTwoAntisymmetricAffineSinMomentInterval n).Contains
      (factorTwoAntisymmetricAffineSinMoment n.1) := by
  by_cases hn : n.1 = 0
  · simpa [factorTwoAntisymmetricAffineSinMomentInterval, hn,
      factorTwoAntisymmetricAffineSinMoment_zero] using contains_pure (0 : ℚ)
  · simpa [factorTwoAntisymmetricAffineSinMomentInterval, hn] using
      factorTwoAntisymmetricAffineSinPositiveInterval_contains n hn

/-! ## Exact width certificate -/

private theorem factorTwoAffineSinYInterval_valid (n : ℕ) :
    (factorTwoAffineCosYInterval n).Valid := by
  change piFineInterval.lower * n / factorTwoPrimeLogTwoInterval.upper ≤
    piFineInterval.upper * n / factorTwoPrimeLogTwoInterval.lower
  have hn : (0 : ℚ) ≤ n := by positivity
  have hc : piFineInterval.lower / factorTwoPrimeLogTwoInterval.upper ≤
      piFineInterval.upper / factorTwoPrimeLogTwoInterval.lower := by
    norm_num [piFineInterval, factorTwoPrimeLogTwoInterval]
  calc
    piFineInterval.lower * (n : ℚ) /
          factorTwoPrimeLogTwoInterval.upper =
        (piFineInterval.lower / factorTwoPrimeLogTwoInterval.upper) * n := by
      ring
    _ ≤ (piFineInterval.upper / factorTwoPrimeLogTwoInterval.lower) * n :=
      mul_le_mul_of_nonneg_right hc hn
    _ = piFineInterval.upper * (n : ℚ) /
          factorTwoPrimeLogTwoInterval.lower := by ring

private theorem factorTwoAffineSinYInterval_lower_le (n : ℕ) :
    (9 / 2 : ℚ) * n ≤ (factorTwoAffineCosYInterval n).lower := by
  have hn : (0 : ℚ) ≤ n := by positivity
  change (9 / 2 : ℚ) * n ≤
    piFineInterval.lower * n / factorTwoPrimeLogTwoInterval.upper
  have hc : (9 / 2 : ℚ) ≤
      piFineInterval.lower / factorTwoPrimeLogTwoInterval.upper := by
    norm_num [piFineInterval, factorTwoPrimeLogTwoInterval]
  calc
    (9 / 2 : ℚ) * n ≤
        (piFineInterval.lower / factorTwoPrimeLogTwoInterval.upper) * n :=
      mul_le_mul_of_nonneg_right hc hn
    _ = piFineInterval.lower * (n : ℚ) /
          factorTwoPrimeLogTwoInterval.upper := by ring

private theorem factorTwoAffineSinYInterval_upper_le (n : ℕ) :
    (factorTwoAffineCosYInterval n).upper ≤ (5 : ℚ) * n := by
  have hn : (0 : ℚ) ≤ n := by positivity
  change piFineInterval.upper * n / factorTwoPrimeLogTwoInterval.lower ≤
    (5 : ℚ) * n
  have hc : piFineInterval.upper / factorTwoPrimeLogTwoInterval.lower ≤
      (5 : ℚ) := by
    norm_num [piFineInterval, factorTwoPrimeLogTwoInterval]
  calc
    piFineInterval.upper * (n : ℚ) /
          factorTwoPrimeLogTwoInterval.lower =
        (piFineInterval.upper / factorTwoPrimeLogTwoInterval.lower) * n := by
      ring
    _ ≤ (5 : ℚ) * n := mul_le_mul_of_nonneg_right hc hn

private theorem factorTwoAffineSinYInterval_absBound (n : ℕ) :
    (factorTwoAffineCosYInterval n).AbsBound ((5 : ℚ) * n) := by
  constructor
  · exact (neg_nonpos.mpr (by positivity)).trans
      ((by positivity : (0 : ℚ) ≤ (9 / 2 : ℚ) * n).trans
        (factorTwoAffineSinYInterval_lower_le n))
  · exact factorTwoAffineSinYInterval_upper_le n

private theorem factorTwoAffineSinYInterval_width_le (n : ℕ) :
    width (factorTwoAffineCosYInterval n) ≤ (n : ℚ) / 10000000000000 := by
  have hn : (0 : ℚ) ≤ n := by positivity
  change
    piFineInterval.upper * (n : ℚ) / factorTwoPrimeLogTwoInterval.lower -
        piFineInterval.lower * (n : ℚ) /
          factorTwoPrimeLogTwoInterval.upper ≤
      (n : ℚ) / 10000000000000
  have hc :
      piFineInterval.upper / factorTwoPrimeLogTwoInterval.lower -
          piFineInterval.lower / factorTwoPrimeLogTwoInterval.upper ≤
        (1 : ℚ) / 10000000000000 := by
    norm_num [piFineInterval, factorTwoPrimeLogTwoInterval]
  calc
    piFineInterval.upper * (n : ℚ) / factorTwoPrimeLogTwoInterval.lower -
          piFineInterval.lower * (n : ℚ) /
            factorTwoPrimeLogTwoInterval.upper =
        (piFineInterval.upper / factorTwoPrimeLogTwoInterval.lower -
          piFineInterval.lower / factorTwoPrimeLogTwoInterval.upper) * n := by
      ring
    _ ≤ ((1 : ℚ) / 10000000000000) * n :=
      mul_le_mul_of_nonneg_right hc hn
    _ = (n : ℚ) / 10000000000000 := by ring

private theorem factorTwoAffineSinYSqInterval_valid (n : ℕ) :
    (nonnegSquare (factorTwoAffineCosYInterval n)).Valid := by
  change (factorTwoAffineCosYInterval n).lower ^ 2 ≤
    (factorTwoAffineCosYInterval n).upper ^ 2
  exact pow_le_pow_left₀
    ((by positivity : (0 : ℚ) ≤ (9 / 2 : ℚ) * n).trans
      (factorTwoAffineSinYInterval_lower_le n))
    (factorTwoAffineSinYInterval_valid n) 2

private theorem factorTwoAffineSinYSqInterval_absBound (n : ℕ) :
    (nonnegSquare (factorTwoAffineCosYInterval n)).AbsBound
      ((25 : ℚ) * n ^ 2) := by
  have hlo : 0 ≤ (nonnegSquare
      (factorTwoAffineCosYInterval n)).lower := by
    change 0 ≤ (factorTwoAffineCosYInterval n).lower ^ 2
    positivity
  constructor
  · exact (neg_nonpos.mpr (by positivity)).trans hlo
  · change (factorTwoAffineCosYInterval n).upper ^ 2 ≤
      (25 : ℚ) * n ^ 2
    have hu := factorTwoAffineSinYInterval_upper_le n
    have hu0 : 0 ≤ (factorTwoAffineCosYInterval n).upper :=
      ((by positivity : (0 : ℚ) ≤ (9 / 2 : ℚ) * n).trans
        (factorTwoAffineSinYInterval_lower_le n)).trans
        (factorTwoAffineSinYInterval_valid n)
    nlinarith [sq_nonneg ((n : ℚ) * 5 -
      (factorTwoAffineCosYInterval n).upper)]

private theorem factorTwoAffineSinYSqInterval_width_le (n : ℕ) :
    width (nonnegSquare (factorTwoAffineCosYInterval n)) ≤
      (n : ℚ) ^ 2 / 1000000000000 := by
  have hsum :
      (factorTwoAffineCosYInterval n).upper +
          (factorTwoAffineCosYInterval n).lower ≤ (10 : ℚ) * n := by
    calc
      (factorTwoAffineCosYInterval n).upper +
            (factorTwoAffineCosYInterval n).lower ≤
          (factorTwoAffineCosYInterval n).upper +
            (factorTwoAffineCosYInterval n).upper :=
        add_le_add (le_refl _) (factorTwoAffineSinYInterval_valid n)
      _ ≤ (5 : ℚ) * n + 5 * n :=
        add_le_add (factorTwoAffineSinYInterval_upper_le n)
          (factorTwoAffineSinYInterval_upper_le n)
      _ = (10 : ℚ) * n := by ring
  have hwidth := factorTwoAffineSinYInterval_width_le n
  change
    (factorTwoAffineCosYInterval n).upper ^ 2 -
        (factorTwoAffineCosYInterval n).lower ^ 2 ≤
      (n : ℚ) ^ 2 / 1000000000000
  rw [sq_sub_sq]
  calc
    ((factorTwoAffineCosYInterval n).upper +
          (factorTwoAffineCosYInterval n).lower) *
        ((factorTwoAffineCosYInterval n).upper -
          (factorTwoAffineCosYInterval n).lower) ≤
        ((10 : ℚ) * n) * ((n : ℚ) / 10000000000000) := by
      exact mul_le_mul hsum hwidth
        (width_nonneg (factorTwoAffineSinYInterval_valid n)) (by positivity)
    _ = (n : ℚ) ^ 2 / 1000000000000 := by ring

private theorem factorTwoAffineSinDenomInterval_metrics
    (n m : ℕ) :
    let x := factorTwoAffineCosXQ m
    let D := factorTwoAffineCosDenomInterval n m
    let floor := x ^ 2 + ((9 / 2 : ℚ) * n) ^ 2
    D.Valid ∧ D.AbsBound (x ^ 2 + 25 * n ^ 2) ∧
      width D ≤ (n : ℚ) ^ 2 / 1000000000000 ∧
      floor ≤ D.lower := by
  dsimp only
  have hx0 : 0 ≤ factorTwoAffineCosXQ m ^ 2 := by positivity
  have hYsqValid := factorTwoAffineSinYSqInterval_valid n
  have hYsqAbs := factorTwoAffineSinYSqInterval_absBound n
  have hYsqWidth := factorTwoAffineSinYSqInterval_width_le n
  have hfloorSq : ((9 / 2 : ℚ) * n) ^ 2 ≤
      (factorTwoAffineCosYInterval n).lower ^ 2 :=
    pow_le_pow_left₀ (by positivity)
      (factorTwoAffineSinYInterval_lower_le n) 2
  constructor
  · exact valid_add (valid_pure _) hYsqValid
  constructor
  · simpa [factorTwoAffineCosDenomInterval,
      factorTwoAffineCosYSqInterval] using
      (absBound_add (absBound_pure (by
        rw [abs_of_nonneg hx0])) hYsqAbs)
  constructor
  · simpa [factorTwoAffineCosDenomInterval,
      factorTwoAffineCosYSqInterval, width_add, width_pure] using hYsqWidth
  · change factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2 ≤
      factorTwoAffineCosXQ m ^ 2 +
        (factorTwoAffineCosYInterval n).lower ^ 2
    exact add_le_add (le_refl _) hfloorSq

private theorem factorTwoAffineSinFloor_bounds
    {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    let x := factorTwoAffineCosXQ m
    let floor := x ^ 2 + ((9 / 2 : ℚ) * n) ^ 2
    0 < x ∧ 0 < floor ∧
      9 * x * n ≤ floor ∧ 20 * (n : ℚ) ^ 2 ≤ floor ∧
      x ^ 2 + 25 * (n : ℚ) ^ 2 ≤ (5 / 4 : ℚ) * floor := by
  dsimp only
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hx : (0 : ℚ) < factorTwoAffineCosXQ m := by
    unfold factorTwoAffineCosXQ
    positivity
  constructor
  · exact hx
  constructor
  · positivity
  constructor
  · nlinarith [sq_nonneg
      (factorTwoAffineCosXQ m - (9 / 2 : ℚ) * n)]
  constructor
  · nlinarith [sq_nonneg (factorTwoAffineCosXQ m)]
  · nlinarith [sq_nonneg (factorTwoAffineCosXQ m), sq_nonneg (n : ℚ)]

private theorem factorTwoAffineSinNumerator_metrics
    {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    let x := factorTwoAffineCosXQ m
    let A := RatInterval.pure 2 * RatInterval.pure x
    let N := A * factorTwoAffineCosYInterval n
    N.Valid ∧ N.AbsBound (10 * x * n) ∧
      width N ≤ 2 * x * n / 10000000000000 := by
  dsimp only
  have hx : (0 : ℚ) < factorTwoAffineCosXQ m :=
    (factorTwoAffineSinFloor_bounds hn m).1
  have hAvalid :
      (RatInterval.pure 2 * RatInterval.pure (factorTwoAffineCosXQ m)).Valid :=
    valid_mul (valid_pure 2) (valid_pure _)
  have hAabs : (RatInterval.pure 2 *
      RatInterval.pure (factorTwoAffineCosXQ m)).AbsBound
      (2 * factorTwoAffineCosXQ m) := by
    exact absBound_mul (valid_pure 2) (valid_pure _)
      (absBound_pure (by norm_num))
      (absBound_pure (by rw [abs_of_pos hx])) (by norm_num) hx.le
  have hAwidth : width (RatInterval.pure 2 *
      RatInterval.pure (factorTwoAffineCosXQ m)) = 0 := by
    have hw := width_mul_le (valid_pure 2)
      (valid_pure (factorTwoAffineCosXQ m))
      (absBound_pure (by norm_num : |(2 : ℚ)| ≤ 2))
      (absBound_pure (by rw [abs_of_pos hx])) (by norm_num) hx.le
    rw [width_pure, width_pure] at hw
    norm_num at hw
    exact le_antisymm hw (width_nonneg hAvalid)
  have hYvalid := factorTwoAffineSinYInterval_valid n
  have hYabs := factorTwoAffineSinYInterval_absBound n
  have hmul := width_mul_le hAvalid hYvalid hAabs hYabs
    (mul_nonneg (by norm_num) hx.le) (by positivity)
  constructor
  · exact valid_mul hAvalid hYvalid
  constructor
  · convert absBound_mul hAvalid hYvalid hAabs hYabs
      (mul_nonneg (by norm_num) hx.le) (by positivity) using 1 ; ring
  · calc
      width ((RatInterval.pure 2 *
          RatInterval.pure (factorTwoAffineCosXQ m)) *
          factorTwoAffineCosYInterval n) ≤
          (5 * (n : ℚ)) * width
              (RatInterval.pure 2 *
                RatInterval.pure (factorTwoAffineCosXQ m)) +
            (2 * factorTwoAffineCosXQ m) *
              width (factorTwoAffineCosYInterval n) := hmul
      _ = (2 * factorTwoAffineCosXQ m) *
          width (factorTwoAffineCosYInterval n) := by rw [hAwidth]; ring
      _ ≤ (2 * factorTwoAffineCosXQ m) *
          ((n : ℚ) / 10000000000000) :=
        mul_le_mul_of_nonneg_left (factorTwoAffineSinYInterval_width_le n)
          (mul_nonneg (by norm_num) hx.le)
      _ = 2 * factorTwoAffineCosXQ m * n / 10000000000000 := by ring

private theorem factorTwoAffineSinDenomSquare_metrics
    {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    let x := factorTwoAffineCosXQ m
    let floor := x ^ 2 + ((9 / 2 : ℚ) * n) ^ 2
    let D := factorTwoAffineCosDenomInterval n m
    let E := nonnegSquare D
    E.Valid ∧ (floor * floor ≤ E.lower) ∧
      width E ≤ (5 / 2 : ℚ) * floor * n ^ 2 / 1000000000000 := by
  dsimp only
  have hD := factorTwoAffineSinDenomInterval_metrics n m
  have hfloor := factorTwoAffineSinFloor_bounds hn m
  have hDlower0 : 0 ≤ (factorTwoAffineCosDenomInterval n m).lower :=
    hfloor.2.1.le.trans hD.2.2.2
  have hEvalid : (nonnegSquare
      (factorTwoAffineCosDenomInterval n m)).Valid := by
    change (factorTwoAffineCosDenomInterval n m).lower ^ 2 ≤
      (factorTwoAffineCosDenomInterval n m).upper ^ 2
    exact pow_le_pow_left₀ hDlower0 hD.1 2
  have hElower :
      (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) *
          (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) ≤
        (nonnegSquare (factorTwoAffineCosDenomInterval n m)).lower := by
    change
      (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) *
          (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) ≤
        (factorTwoAffineCosDenomInterval n m).lower ^ 2
    simpa only [pow_two] using pow_le_pow_left₀ hfloor.2.1.le
      hD.2.2.2 2
  have hsum :
      (factorTwoAffineCosDenomInterval n m).upper +
          (factorTwoAffineCosDenomInterval n m).lower ≤
        (5 / 2 : ℚ) *
          (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) := by
    calc
      (factorTwoAffineCosDenomInterval n m).upper +
            (factorTwoAffineCosDenomInterval n m).lower ≤
          2 * (factorTwoAffineCosXQ m ^ 2 + 25 * (n : ℚ) ^ 2) := by
        have hu := hD.2.1.2
        have hl := hD.1.trans hu
        simpa only [two_mul] using add_le_add hu hl
      _ ≤ (5 / 2 : ℚ) *
          (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) := by
        nlinarith [hfloor.2.2.2.2]
  constructor
  · exact hEvalid
  constructor
  · exact hElower
  · change
      (factorTwoAffineCosDenomInterval n m).upper ^ 2 -
          (factorTwoAffineCosDenomInterval n m).lower ^ 2 ≤
        (5 / 2 : ℚ) *
          (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) *
            n ^ 2 / 1000000000000
    rw [sq_sub_sq]
    calc
      ((factorTwoAffineCosDenomInterval n m).upper +
          (factorTwoAffineCosDenomInterval n m).lower) *
          ((factorTwoAffineCosDenomInterval n m).upper -
            (factorTwoAffineCosDenomInterval n m).lower) ≤
        ((5 / 2 : ℚ) *
          (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2)) *
            ((n : ℚ) ^ 2 / 1000000000000) := by
        exact mul_le_mul hsum hD.2.2.1 (width_nonneg hD.1) (by positivity)
      _ = (5 / 2 : ℚ) *
          (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) *
            n ^ 2 / 1000000000000 := by ring

private theorem factorTwoAffineSinKernel_width_budget
    {n : ℕ} (hn : 1 ≤ n) {x floor : ℚ}
    (hx : 0 < x) (hfloor : 0 < floor)
    (hxn : 9 * x * n ≤ floor)
    (hnn : 20 * (n : ℚ) ^ 2 ≤ floor) :
    (floor * floor)⁻¹ * (2 * x * n / 10000000000000) +
        (10 * x * n) *
          (((5 / 2 : ℚ) * floor * n ^ 2 / 1000000000000) /
            ((floor * floor) * (floor * floor))) ≤
      (1 : ℚ) / 100000000000000 := by
  have hnQ : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℚ) < n := zero_lt_one.trans_le hnQ
  have hfloorSq : 0 < floor * floor := mul_pos hfloor hfloor
  have hdenOne : 180 * x * (n : ℚ) ^ 3 ≤ floor * floor := by
    calc
      180 * x * (n : ℚ) ^ 3 =
          (9 * x * n) * (20 * (n : ℚ) ^ 2) := by ring
      _ ≤ floor * floor :=
        mul_le_mul hxn hnn (by positivity) hfloor.le
  have hfirst :
      (floor * floor)⁻¹ * (2 * x * n / 10000000000000) ≤
        (1 : ℚ) / 900000000000000 := by
    rw [mul_comm]
    change (2 * x * n / 10000000000000) / (floor * floor) ≤ _
    calc
      (2 * x * n / 10000000000000) / (floor * floor) ≤
          (2 * x * n / 10000000000000) /
            (180 * x * (n : ℚ) ^ 3) := by
        exact div_le_div_of_nonneg_left (by positivity)
          (by positivity) hdenOne
      _ = (1 : ℚ) / (900000000000000 * n ^ 2) := by
        field_simp [hx.ne', hnPos.ne']
        ring
      _ ≤ (1 : ℚ) / 900000000000000 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        nlinarith [sq_nonneg ((n : ℚ) - 1)]
  have hnnSq : (20 * (n : ℚ) ^ 2) ^ 2 ≤ floor ^ 2 :=
    pow_le_pow_left₀ (by positivity) hnn 2
  have hdenTwo : 3600 * x * (n : ℚ) ^ 5 ≤ floor ^ 3 := by
    calc
      3600 * x * (n : ℚ) ^ 5 =
          (9 * x * n) * (20 * (n : ℚ) ^ 2) ^ 2 := by ring
      _ ≤ floor * floor ^ 2 :=
        mul_le_mul hxn hnnSq (by positivity) hfloor.le
      _ = floor ^ 3 := by ring
  have hsecond :
      (10 * x * n) *
          (((5 / 2 : ℚ) * floor * n ^ 2 / 1000000000000) /
            ((floor * floor) * (floor * floor))) ≤
        (1 : ℚ) / 144000000000000 := by
    calc
      (10 * x * n) *
          (((5 / 2 : ℚ) * floor * n ^ 2 / 1000000000000) /
            ((floor * floor) * (floor * floor))) =
          (25 * x * (n : ℚ) ^ 3 / 1000000000000) /
            floor ^ 3 := by
        field_simp [hfloor.ne']
        ring
      _ ≤ (25 * x * (n : ℚ) ^ 3 / 1000000000000) /
          (3600 * x * (n : ℚ) ^ 5) := by
        exact div_le_div_of_nonneg_left (by positivity)
          (by positivity) hdenTwo
      _ = (1 : ℚ) / (144000000000000 * n ^ 2) := by
        field_simp [hx.ne', hnPos.ne']
        ring
      _ ≤ (1 : ℚ) / 144000000000000 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        nlinarith [sq_nonneg ((n : ℚ) - 1)]
  linarith

private theorem factorTwoAffineSinUnweightedKernelInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    width (factorTwoAffineSinUnweightedKernelInterval n m) ≤
      (1 : ℚ) / 100000000000000 := by
  let x := factorTwoAffineCosXQ m
  let floor : ℚ := x ^ 2 + ((9 / 2 : ℚ) * n) ^ 2
  let A := RatInterval.pure 2 * RatInterval.pure x
  let N := A * factorTwoAffineCosYInterval n
  let D := factorTwoAffineCosDenomInterval n m
  let E := nonnegSquare D
  have hfloor := factorTwoAffineSinFloor_bounds hn m
  have hN := factorTwoAffineSinNumerator_metrics hn m
  have hE := factorTwoAffineSinDenomSquare_metrics hn m
  have hNboundNonneg : (0 : ℚ) ≤ 10 * x * n :=
    mul_nonneg (mul_nonneg (by norm_num) hfloor.1.le) (Nat.cast_nonneg n)
  have hdiv := width_div_le_of_lower hN.1 hE.1 hN.2.1
    hNboundNonneg (mul_pos hfloor.2.1 hfloor.2.1) hE.2.1
  have hbudget := factorTwoAffineSinKernel_width_budget hn hfloor.1
    hfloor.2.1 hfloor.2.2.1 hfloor.2.2.2.1
  unfold factorTwoAffineSinUnweightedKernelInterval
  dsimp only [x, floor, A, N, D, E] at hdiv hbudget ⊢
  calc
    width ((RatInterval.pure 2 * RatInterval.pure (factorTwoAffineCosXQ m) *
        factorTwoAffineCosYInterval n) /
        nonnegSquare (factorTwoAffineCosDenomInterval n m)) ≤
      ((factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) *
        (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2))⁻¹ *
          width (RatInterval.pure 2 * RatInterval.pure (factorTwoAffineCosXQ m) *
            factorTwoAffineCosYInterval n) +
        (10 * factorTwoAffineCosXQ m * n) *
          (width (nonnegSquare (factorTwoAffineCosDenomInterval n m)) /
            (((factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) *
                (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2)) *
              ((factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) *
                (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2)))) :=
      hdiv
    _ ≤
      ((factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) *
        (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2))⁻¹ *
          (2 * factorTwoAffineCosXQ m * n / 10000000000000) +
        (10 * factorTwoAffineCosXQ m * n) *
          (((5 / 2 : ℚ) *
              (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) *
                n ^ 2 / 1000000000000) /
            (((factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) *
                (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2)) *
              ((factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2) *
                (factorTwoAffineCosXQ m ^ 2 + ((9 / 2 : ℚ) * n) ^ 2)))) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hN.2.2
          (inv_nonneg.mpr (mul_nonneg hfloor.2.1.le hfloor.2.1.le))
      · exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hE.2.2
            (mul_nonneg (mul_nonneg hfloor.2.1.le hfloor.2.1.le)
              (mul_nonneg hfloor.2.1.le hfloor.2.1.le))) (by positivity)
    _ ≤ (1 : ℚ) / 100000000000000 := hbudget

private theorem factorTwoAffineSinUnweightedHeadInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) :
    width (factorTwoAffineSinUnweightedHeadInterval n 512) ≤
      (1 : ℚ) / 100000000000 := by
  calc
    width (factorTwoAffineSinUnweightedHeadInterval n 512) ≤
        (512 : ℚ) * ((1 : ℚ) / 100000000000000) := by
      apply width_recursive_add_le_const_mul
        (factorTwoAffineSinUnweightedHeadInterval n)
        (factorTwoAffineSinUnweightedKernelInterval n)
      · rfl
      · intro k
        rfl
      · intro k _hk
        exact factorTwoAffineSinUnweightedKernelInterval_width_le hn k
    _ ≤ (1 : ℚ) / 100000000000 := by norm_num

private theorem factorTwoAffineSin_absBound_mono
    {I : RatInterval} {A B : ℚ} (hI : I.AbsBound A) (hAB : A ≤ B) :
    I.AbsBound B := by
  unfold AbsBound at hI ⊢
  constructor <;> linarith [hI.1, hI.2]

private theorem factorTwoAffineSinUnweightedKernelInterval_valid_absBound
    {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    (factorTwoAffineSinUnweightedKernelInterval n m).Valid ∧
      (factorTwoAffineSinUnweightedKernelInterval n m).AbsBound 1 := by
  let x := factorTwoAffineCosXQ m
  let floor : ℚ := x ^ 2 + ((9 / 2 : ℚ) * n) ^ 2
  let A := RatInterval.pure 2 * RatInterval.pure x
  let N := A * factorTwoAffineCosYInterval n
  let D := factorTwoAffineCosDenomInterval n m
  let E := nonnegSquare D
  have hfloor := factorTwoAffineSinFloor_bounds hn m
  have hN := factorTwoAffineSinNumerator_metrics hn m
  have hE := factorTwoAffineSinDenomSquare_metrics hn m
  have hvalid : (N / E).Valid :=
    valid_div_of_pos hN.1 hE.1 (mul_pos hfloor.2.1 hfloor.2.1 |>.trans_le hE.2.1)
  have habs : (N / E).AbsBound
      ((10 * x * n) * (floor * floor)⁻¹) :=
    absBound_div_of_lower hN.1 hE.1 hN.2.1
      (mul_nonneg (mul_nonneg (by norm_num) hfloor.1.le) (Nat.cast_nonneg n))
      (mul_pos hfloor.2.1 hfloor.2.1) hE.2.1
  have hcoeff : (10 * x * n) * (floor * floor)⁻¹ ≤ (1 : ℚ) := by
    have hnOne : (1 : ℚ) ≤ n := by exact_mod_cast hn
    have htwenty : (20 : ℚ) ≤ floor := by
      calc
        (20 : ℚ) ≤ 20 * (n : ℚ) ^ 2 := by nlinarith
        _ ≤ floor := hfloor.2.2.2.1
    have htenFloor : (10 : ℚ) ≤ 9 * floor := by linarith
    have hten : 10 * x * (n : ℚ) ≤ floor * floor := by
      calc
        10 * x * (n : ℚ) = 10 * (x * n) := by ring
        _ ≤ (9 * floor) * (x * n) :=
          mul_le_mul_of_nonneg_right htenFloor
            (mul_nonneg hfloor.1.le (Nat.cast_nonneg n))
        _ = floor * (9 * x * n) := by ring
        _ ≤ floor * floor :=
          mul_le_mul_of_nonneg_left hfloor.2.2.1 hfloor.2.1.le
    rw [mul_inv_le_iff₀ (mul_pos hfloor.2.1 hfloor.2.1)]
    simpa only [one_mul] using hten
  unfold factorTwoAffineSinUnweightedKernelInterval
  dsimp only [x, floor, A, N, D, E] at hvalid habs ⊢
  exact ⟨hvalid, factorTwoAffineSin_absBound_mono habs hcoeff⟩

private theorem factorTwoAffineSinDyadicDefect_metrics (k : ℕ) :
    let D := factorTwoAffineCosDyadicDInterval k
    let E := D - RatInterval.pure 1
    E.Valid ∧ E.AbsBound 2 ∧
      width E ≤ (2 : ℚ) / 1000000000000000 := by
  dsimp only
  have hF := sineDyadicFactor_valid_absBound k
  have hFw := sineDyadicFactor_width_le k
  have hDvalid := valid_mul hF.1 hF.1
  have hDabs := absBound_mul hF.1 hF.1 hF.2 hF.2
    (by norm_num : (0 : ℚ) ≤ 1) (by norm_num : (0 : ℚ) ≤ 1)
  have hDw := width_mul_le hF.1 hF.1 hF.2 hF.2
    (by norm_num : (0 : ℚ) ≤ 1) (by norm_num : (0 : ℚ) ≤ 1)
  simp only [factorTwoAffineCosDyadicDInterval,
    factorTwoAffineCosDyadicQInterval]
  constructor
  · exact valid_sub hDvalid (valid_pure 1)
  constructor
  · exact factorTwoAffineSin_absBound_mono
      (absBound_sub hDabs
        (absBound_pure (q := 1) (B := 1) (by norm_num))) (by norm_num)
  · rw [width_sub, width_pure, add_zero]
    calc
      width ((RatInterval.pure 1 - sqrtTwoInterval⁻¹ /
          RatInterval.pure ((4 : ℚ) ^ k)) *
          (RatInterval.pure 1 - sqrtTwoInterval⁻¹ /
            RatInterval.pure ((4 : ℚ) ^ k))) ≤
          1 * width (RatInterval.pure 1 - sqrtTwoInterval⁻¹ /
              RatInterval.pure ((4 : ℚ) ^ k)) +
            1 * width (RatInterval.pure 1 - sqrtTwoInterval⁻¹ /
              RatInterval.pure ((4 : ℚ) ^ k)) := hDw
      _ ≤ (2 : ℚ) / 1000000000000000 := by linarith

private theorem factorTwoAffineSinDyadicCorrectionInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    width (factorTwoAffineSinDyadicCorrectionInterval n m) ≤
      (22 : ℚ) / 1000000000000000 := by
  have hdef := factorTwoAffineSinDyadicDefect_metrics (m + 1)
  have hker := factorTwoAffineSinUnweightedKernelInterval_valid_absBound hn m
  have hmul := width_mul_le hdef.1 hker.1 hdef.2.1 hker.2
    (by norm_num : (0 : ℚ) ≤ 2) (by norm_num : (0 : ℚ) ≤ 1)
  unfold factorTwoAffineSinDyadicCorrectionInterval
  calc
    width ((factorTwoAffineCosDyadicDInterval (m + 1) - RatInterval.pure 1) *
        factorTwoAffineSinUnweightedKernelInterval n m) ≤
      1 * width (factorTwoAffineCosDyadicDInterval (m + 1) - RatInterval.pure 1) +
        2 * width (factorTwoAffineSinUnweightedKernelInterval n m) := hmul
    _ ≤ 1 * ((2 : ℚ) / 1000000000000000) +
        2 * ((1 : ℚ) / 100000000000000) := by
      gcongr
      · exact hdef.2.2
      · exact factorTwoAffineSinUnweightedKernelInterval_width_le hn m
    _ = (22 : ℚ) / 1000000000000000 := by ring

private theorem factorTwoAffineSinDyadicCorrectionSeriesInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) :
    width (factorTwoAffineSinDyadicCorrectionSeriesInterval n) ≤
      (1 : ℚ) / 400000000000 := by
  have hhead :
      width (factorTwoAffineSinDyadicCorrectionHeadInterval n 20) ≤
        (20 : ℚ) * ((22 : ℚ) / 1000000000000000) := by
    apply width_recursive_add_le_const_mul
      (factorTwoAffineSinDyadicCorrectionHeadInterval n)
      (factorTwoAffineSinDyadicCorrectionInterval n)
    · rfl
    · intro k
      rfl
    · intro k _hk
      exact factorTwoAffineSinDyadicCorrectionInterval_width_le hn k
  have htail : width (factorTwoAffineSinDyadicCorrectionTailInterval 20) =
      (2 : ℚ) / (4 : ℚ) ^ 20 := by
    norm_num [factorTwoAffineSinDyadicCorrectionTailInterval,
      factorTwoAffineSinDyadicCorrectionTailRadiusQ, width]
  unfold factorTwoAffineSinDyadicCorrectionSeriesInterval
  rw [width_add, htail]
  calc
    width (factorTwoAffineSinDyadicCorrectionHeadInterval n 20) +
        2 / (4 : ℚ) ^ 20 ≤
      20 * (22 / 1000000000000000 : ℚ) + 2 / (4 : ℚ) ^ 20 :=
        add_le_add hhead le_rfl
    _ ≤ (1 : ℚ) / 400000000000 := by norm_num

private theorem factorTwoAffineSinTailY_metrics
    {n : ℕ} (hnle : n ≤ 200) :
    (factorTwoAffineCosYInterval n).Valid ∧
      (factorTwoAffineCosYInterval n).AbsBound 1000 ∧
      width (factorTwoAffineCosYInterval n) ≤
        (1 : ℚ) / 50000000000 := by
  have hnQ : (n : ℚ) ≤ 200 := by exact_mod_cast hnle
  constructor
  · exact factorTwoAffineSinYInterval_valid n
  constructor
  · exact factorTwoAffineSin_absBound_mono
      (factorTwoAffineSinYInterval_absBound n) (by linarith)
  · calc
      width (factorTwoAffineCosYInterval n) ≤
          (n : ℚ) / 10000000000000 :=
        factorTwoAffineSinYInterval_width_le n
      _ ≤ (1 : ℚ) / 50000000000 := by linarith

private theorem factorTwoAffineSinTailDenom_metrics
    {n : ℕ} (hnle : n ≤ 200) :
    let D := factorTwoAffineCosDenomInterval n 512
    D.Valid ∧ D.AbsBound 2000000 ∧
      width D ≤ (1 : ℚ) / 25000000 ∧
      (250000 : ℚ) ≤ D.lower := by
  dsimp only
  have hnQ : (n : ℚ) ≤ 200 := by exact_mod_cast hnle
  have hD := factorTwoAffineSinDenomInterval_metrics n 512
  constructor
  · exact hD.1
  constructor
  · exact factorTwoAffineSin_absBound_mono hD.2.1 (by
      norm_num [factorTwoAffineCosXQ]
      nlinarith [sq_nonneg ((n : ℚ) - 200)])
  constructor
  · calc
      width (factorTwoAffineCosDenomInterval n 512) ≤
          (n : ℚ) ^ 2 / 1000000000000 := hD.2.2.1
      _ ≤ (1 : ℚ) / 25000000 := by
        nlinarith [sq_nonneg ((n : ℚ) - 200)]
  · calc
      (250000 : ℚ) ≤
          factorTwoAffineCosXQ 512 ^ 2 := by
        norm_num [factorTwoAffineCosXQ]
      _ ≤ factorTwoAffineCosXQ 512 ^ 2 + ((9 / 2 : ℚ) * n) ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      _ ≤ (factorTwoAffineCosDenomInterval n 512).lower := hD.2.2.2

private theorem factorTwoAffineSinTailDenomSquare_metrics
    {n : ℕ} (hnle : n ≤ 200) :
    let D := factorTwoAffineCosDenomInterval n 512
    let E := nonnegSquare D
    E.Valid ∧ E.AbsBound 4000000000000 ∧
      width E ≤ (4 : ℚ) / 25 ∧
      (62500000000 : ℚ) ≤ E.lower := by
  dsimp only
  have hD := factorTwoAffineSinTailDenom_metrics hnle
  have hDlower0 : 0 ≤ (factorTwoAffineCosDenomInterval n 512).lower :=
    (by norm_num : (0 : ℚ) ≤ 250000).trans hD.2.2.2
  have hEvalid : (nonnegSquare
      (factorTwoAffineCosDenomInterval n 512)).Valid := by
    change (factorTwoAffineCosDenomInterval n 512).lower ^ 2 ≤
      (factorTwoAffineCosDenomInterval n 512).upper ^ 2
    exact pow_le_pow_left₀ hDlower0 hD.1 2
  have hEabs : (nonnegSquare
      (factorTwoAffineCosDenomInterval n 512)).AbsBound 4000000000000 := by
    constructor
    · change -(4000000000000 : ℚ) ≤
        (factorTwoAffineCosDenomInterval n 512).lower ^ 2
      nlinarith [sq_nonneg ((factorTwoAffineCosDenomInterval n 512).lower)]
    · change (factorTwoAffineCosDenomInterval n 512).upper ^ 2 ≤
        (4000000000000 : ℚ)
      have hu0 : 0 ≤ (factorTwoAffineCosDenomInterval n 512).upper :=
        hDlower0.trans hD.1
      have hpow := pow_le_pow_left₀ hu0 hD.2.1.2 2
      norm_num at hpow
      exact hpow
  constructor
  · exact hEvalid
  constructor
  · exact hEabs
  constructor
  · change
      (factorTwoAffineCosDenomInterval n 512).upper ^ 2 -
          (factorTwoAffineCosDenomInterval n 512).lower ^ 2 ≤
        (4 : ℚ) / 25
    rw [sq_sub_sq]
    have hsum :
        (factorTwoAffineCosDenomInterval n 512).upper +
            (factorTwoAffineCosDenomInterval n 512).lower ≤ 4000000 := by
      have hu := hD.2.1.2
      have hl := hD.1.trans hu
      linarith
    calc
      ((factorTwoAffineCosDenomInterval n 512).upper +
          (factorTwoAffineCosDenomInterval n 512).lower) *
          ((factorTwoAffineCosDenomInterval n 512).upper -
            (factorTwoAffineCosDenomInterval n 512).lower) ≤
        (4000000 : ℚ) * (1 / 25000000 : ℚ) := by
          exact mul_le_mul hsum hD.2.2.1 (width_nonneg hD.1) (by norm_num)
      _ = (4 : ℚ) / 25 := by ring
  · change (62500000000 : ℚ) ≤
      (factorTwoAffineCosDenomInterval n 512).lower ^ 2
    nlinarith [hD.2.2.2,
      sq_nonneg ((factorTwoAffineCosDenomInterval n 512).lower - 250000)]

private theorem factorTwoAffineSinTailDenomCube_metrics
    {n : ℕ} (hnle : n ≤ 200) :
    let D := factorTwoAffineCosDenomInterval n 512
    let E := nonnegSquare D
    let F := D * E
    F.Valid ∧ width F ≤ 480000 ∧
      (15625000000000000 : ℚ) ≤ F.lower := by
  dsimp only
  have hD := factorTwoAffineSinTailDenom_metrics hnle
  have hE := factorTwoAffineSinTailDenomSquare_metrics hnle
  have hwidth := width_mul_le hD.1 hE.1 hD.2.1 hE.2.1
    (by norm_num : (0 : ℚ) ≤ 2000000)
    (by norm_num : (0 : ℚ) ≤ 4000000000000)
  constructor
  · exact valid_mul hD.1 hE.1
  constructor
  · calc
      width (factorTwoAffineCosDenomInterval n 512 *
          nonnegSquare (factorTwoAffineCosDenomInterval n 512)) ≤
        4000000000000 *
            width (factorTwoAffineCosDenomInterval n 512) +
          2000000 * width
            (nonnegSquare (factorTwoAffineCosDenomInterval n 512)) := hwidth
      _ ≤ 4000000000000 * (1 / 25000000 : ℚ) +
          2000000 * (4 / 25 : ℚ) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hD.2.2.1 (by norm_num))
          (mul_le_mul_of_nonneg_left hE.2.2.1 (by norm_num))
      _ = (480000 : ℚ) := by norm_num
  · have hDl := hD.2.2.2
    have hDu := hDl.trans hD.1
    have hEl := hE.2.2.2
    have hEu := hEl.trans hE.1
    have hDl0 : 0 ≤ (factorTwoAffineCosDenomInterval n 512).lower :=
      (by norm_num : (0 : ℚ) ≤ 250000).trans hDl
    have hDu0 : 0 ≤ (factorTwoAffineCosDenomInterval n 512).upper :=
      hDl0.trans hD.1
    change (15625000000000000 : ℚ) ≤
      min
        (min
          ((factorTwoAffineCosDenomInterval n 512).lower *
            (nonnegSquare
              (factorTwoAffineCosDenomInterval n 512)).lower)
          ((factorTwoAffineCosDenomInterval n 512).lower *
            (nonnegSquare
              (factorTwoAffineCosDenomInterval n 512)).upper))
        (min
          ((factorTwoAffineCosDenomInterval n 512).upper *
            (nonnegSquare
              (factorTwoAffineCosDenomInterval n 512)).lower)
          ((factorTwoAffineCosDenomInterval n 512).upper *
            (nonnegSquare
              (factorTwoAffineCosDenomInterval n 512)).upper))
    simp only [le_min_iff]
    constructor
    · constructor
      · exact (by norm_num :
          (15625000000000000 : ℚ) = 250000 * 62500000000) ▸
          mul_le_mul hDl hEl (by norm_num) hDl0
      · exact (by norm_num :
          (15625000000000000 : ℚ) = 250000 * 62500000000) ▸
          mul_le_mul hDl hEu (by norm_num) hDl0
    · constructor
      · exact (by norm_num :
          (15625000000000000 : ℚ) = 250000 * 62500000000) ▸
          mul_le_mul hDu hEl (by norm_num) hDu0
      · exact (by norm_num :
          (15625000000000000 : ℚ) = 250000 * 62500000000) ▸
          mul_le_mul hDu hEu (by norm_num) hDu0

private theorem factorTwoAffineSinProfileInterval_width_le
    {n : ℕ} (hnle : n ≤ 200) :
    width (factorTwoAffineSinProfileInterval n 512) ≤
      (1 : ℚ) / 100000000000000 := by
  have hY := factorTwoAffineSinTailY_metrics hnle
  have hD := factorTwoAffineSinTailDenom_metrics hnle
  have hdiv := width_div_le_of_lower hY.1 hD.1 hY.2.1
    (by norm_num : (0 : ℚ) ≤ 1000)
    (by norm_num : (0 : ℚ) < 250000) hD.2.2.2
  unfold factorTwoAffineSinProfileInterval
  calc
    width (factorTwoAffineCosYInterval n /
        factorTwoAffineCosDenomInterval n 512) ≤
      (250000 : ℚ)⁻¹ * width (factorTwoAffineCosYInterval n) +
        1000 * (width (factorTwoAffineCosDenomInterval n 512) /
          (250000 * 250000)) := hdiv
    _ ≤ (250000 : ℚ)⁻¹ * (1 / 50000000000 : ℚ) +
        1000 * ((1 / 25000000 : ℚ) /
          (250000 * 250000)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hY.2.2 (by norm_num)
      · exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hD.2.2.1 (by norm_num)) (by norm_num)
    _ ≤ (1 : ℚ) / 100000000000000 := by norm_num

private theorem factorTwoAffineSinProfileDerivInterval_width_le
    {n : ℕ} (hnle : n ≤ 200) :
    width (factorTwoAffineSinProfileDerivInterval n 512) ≤
      (1 : ℚ) / 100000000000000 := by
  let Y := factorTwoAffineCosYInterval n
  let X := RatInterval.pure (factorTwoAffineCosXQ 512)
  let N := RatInterval.pure (-2) * Y * X
  let E := nonnegSquare (factorTwoAffineCosDenomInterval n 512)
  have hY := factorTwoAffineSinTailY_metrics hnle
  have hE := factorTwoAffineSinTailDenomSquare_metrics hnle
  have hXvalid : X.Valid := valid_pure _
  have hXabs : X.AbsBound 514 := by
    apply absBound_pure
    norm_num [X, factorTwoAffineCosXQ]
  have hNegValid : (RatInterval.pure (-2) * Y).Valid :=
    valid_mul (valid_pure _) hY.1
  have hNegAbs : (RatInterval.pure (-2) * Y).AbsBound 2000 := by
    apply factorTwoAffineSin_absBound_mono
      (absBound_mul (valid_pure (-2)) hY.1
        (absBound_pure (q := -2) (B := 2) (by norm_num)) hY.2.1
        (by norm_num) (by norm_num))
    norm_num
  have hNvalid : N.Valid := valid_mul hNegValid hXvalid
  have hNabsSmall : N.AbsBound (2000 * 514) :=
    absBound_mul hNegValid hXvalid hNegAbs hXabs (by norm_num) (by norm_num)
  have hNabs : N.AbsBound 1100000 :=
    factorTwoAffineSin_absBound_mono hNabsSmall (by norm_num)
  have hNegWidth : width (RatInterval.pure (-2) * Y) ≤
      (2 : ℚ) / 50000000000 := by
    rw [width_pure_mul (-2) hY.1]
    rw [show |(-2 : ℚ)| = 2 by norm_num]
    calc
      2 * width Y ≤ 2 * ((1 : ℚ) / 50000000000) :=
        mul_le_mul_of_nonneg_left hY.2.2 (by norm_num)
      _ = (2 : ℚ) / 50000000000 := by ring
  have hNwidth : width N ≤ (1 : ℚ) / 40000000 := by
    dsimp only [N, X]
    rw [width_mul_pure _ hNegValid]
    rw [abs_of_nonneg (by norm_num [factorTwoAffineCosXQ])]
    calc
      factorTwoAffineCosXQ 512 * width (RatInterval.pure (-2) * Y) ≤
          factorTwoAffineCosXQ 512 * (2 / 50000000000 : ℚ) :=
        mul_le_mul_of_nonneg_left hNegWidth
          (by norm_num [factorTwoAffineCosXQ])
      _ ≤ (1 : ℚ) / 40000000 := by
        norm_num [factorTwoAffineCosXQ]
  have hdiv := width_div_le_of_lower hNvalid hE.1 hNabs
    (by norm_num : (0 : ℚ) ≤ 1100000)
    (by norm_num : (0 : ℚ) < 62500000000) hE.2.2.2
  unfold factorTwoAffineSinProfileDerivInterval
  dsimp only [Y, X, N, E] at hdiv ⊢
  calc
    width ((RatInterval.pure (-2) * factorTwoAffineCosYInterval n *
        RatInterval.pure (factorTwoAffineCosXQ 512)) /
          nonnegSquare (factorTwoAffineCosDenomInterval n 512)) ≤
      (62500000000 : ℚ)⁻¹ *
          width (RatInterval.pure (-2) * factorTwoAffineCosYInterval n *
            RatInterval.pure (factorTwoAffineCosXQ 512)) +
        1100000 *
          (width (nonnegSquare (factorTwoAffineCosDenomInterval n 512)) /
            (62500000000 * 62500000000)) := hdiv
    _ ≤ (62500000000 : ℚ)⁻¹ * (1 / 40000000 : ℚ) +
        1100000 * ((4 / 25 : ℚ) /
          (62500000000 * 62500000000)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hNwidth (by norm_num)
      · exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hE.2.2.1 (by norm_num)) (by norm_num)
    _ ≤ (1 : ℚ) / 100000000000000 := by norm_num

private theorem factorTwoAffineSinProfileSecondNumerator_metrics
    {n : ℕ} (hnle : n ≤ 200) :
    let Y := factorTwoAffineCosYInterval n
    let Y2 := nonnegSquare Y
    let A := RatInterval.pure 3 *
      RatInterval.pure (factorTwoAffineCosXQ 512 ^ 2) - Y2
    let N := RatInterval.pure 2 * Y * A
    N.Valid ∧ N.AbsBound 4000000000 ∧
      width N ≤ (1 : ℚ) / 5000 := by
  dsimp only
  have hY := factorTwoAffineSinTailY_metrics hnle
  have hY2valid := factorTwoAffineSinYSqInterval_valid n
  have hY2absSmall := factorTwoAffineSinYSqInterval_absBound n
  have hnQ : (n : ℚ) ≤ 200 := by exact_mod_cast hnle
  have hY2abs : (nonnegSquare
      (factorTwoAffineCosYInterval n)).AbsBound 1000000 :=
    factorTwoAffineSin_absBound_mono hY2absSmall (by
      nlinarith [sq_nonneg ((n : ℚ) - 200)])
  have hY2width : width (nonnegSquare
      (factorTwoAffineCosYInterval n)) ≤ (1 : ℚ) / 25000000 := by
    calc
      width (nonnegSquare (factorTwoAffineCosYInterval n)) ≤
          (n : ℚ) ^ 2 / 1000000000000 :=
        factorTwoAffineSinYSqInterval_width_le n
      _ ≤ (1 : ℚ) / 25000000 := by
        nlinarith [sq_nonneg ((n : ℚ) - 200)]
  let P := RatInterval.pure 3 *
    RatInterval.pure (factorTwoAffineCosXQ 512 ^ 2)
  have hPvalid : P.Valid := valid_mul (valid_pure 3) (valid_pure _)
  have hPabs : P.AbsBound 800000 := by
    change (RatInterval.pure 3 *
      RatInterval.pure (factorTwoAffineCosXQ 512 ^ 2)).AbsBound 800000
    apply factorTwoAffineSin_absBound_mono
      (absBound_mul (valid_pure 3) (valid_pure _)
        (absBound_pure (q := 3) (B := 3) (by norm_num))
        (absBound_pure (q := factorTwoAffineCosXQ 512 ^ 2)
          (B := factorTwoAffineCosXQ 512 ^ 2) (by
            rw [abs_of_nonneg (sq_nonneg _)]))
        (by norm_num) (sq_nonneg _))
    norm_num [P, factorTwoAffineCosXQ]
  have hAvalid := valid_sub hPvalid hY2valid
  have hAabs : (P - nonnegSquare
      (factorTwoAffineCosYInterval n)).AbsBound 2000000 :=
    factorTwoAffineSin_absBound_mono (absBound_sub hPabs hY2abs) (by norm_num)
  have hAwidth : width (P - nonnegSquare
      (factorTwoAffineCosYInterval n)) ≤ (1 : ℚ) / 25000000 := by
    rw [width_sub]
    have hPw : width P = 0 := by
      dsimp only [P]
      rw [width_pure_mul 3 (valid_pure _), width_pure]
      norm_num
    rw [hPw, zero_add]
    exact hY2width
  have hTwoYValid := valid_mul (valid_pure 2) hY.1
  have hTwoYAbs :
      (RatInterval.pure 2 * factorTwoAffineCosYInterval n).AbsBound 2000 := by
    apply factorTwoAffineSin_absBound_mono
      (absBound_mul (valid_pure 2) hY.1
        (absBound_pure (q := 2) (B := 2) (by norm_num)) hY.2.1
        (by norm_num) (by norm_num))
    norm_num
  have hTwoYWidth :
      width (RatInterval.pure 2 * factorTwoAffineCosYInterval n) ≤
      (1 : ℚ) / 25000000000 := by
    rw [width_pure_mul 2 hY.1]
    rw [show |(2 : ℚ)| = 2 by norm_num]
    calc
      2 * width (factorTwoAffineCosYInterval n) ≤
          2 * ((1 : ℚ) / 50000000000) :=
        mul_le_mul_of_nonneg_left hY.2.2 (by norm_num)
      _ = (1 : ℚ) / 25000000000 := by norm_num
  have hNwidthRaw := width_mul_le hTwoYValid hAvalid hTwoYAbs hAabs
    (by norm_num : (0 : ℚ) ≤ 2000)
    (by norm_num : (0 : ℚ) ≤ 2000000)
  have hNwidth : width ((RatInterval.pure 2 * factorTwoAffineCosYInterval n) *
      (P - nonnegSquare (factorTwoAffineCosYInterval n))) ≤
        (1 : ℚ) / 5000 := by
    calc
      width ((RatInterval.pure 2 * factorTwoAffineCosYInterval n) *
          (P - nonnegSquare (factorTwoAffineCosYInterval n))) ≤
        2000000 * width (RatInterval.pure 2 * factorTwoAffineCosYInterval n) +
          2000 * width (P - nonnegSquare
            (factorTwoAffineCosYInterval n)) := by
        simpa only using hNwidthRaw
      _ ≤ 2000000 * (1 / 25000000000 : ℚ) +
          2000 * (1 / 25000000 : ℚ) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hTwoYWidth (by norm_num))
          (mul_le_mul_of_nonneg_left hAwidth (by norm_num))
      _ ≤ (1 : ℚ) / 5000 := by norm_num
  constructor
  · exact valid_mul (valid_mul (valid_pure 2) hY.1) hAvalid
  constructor
  ·
    convert absBound_mul hTwoYValid hAvalid hTwoYAbs hAabs
      (by norm_num : (0 : ℚ) ≤ 2000)
      (by norm_num : (0 : ℚ) ≤ 2000000) using 1 ;
        norm_num [P]
  · simpa only [P] using hNwidth

private theorem factorTwoAffineSinProfileSecondInterval_width_le
    {n : ℕ} (hnle : n ≤ 200) :
    width (factorTwoAffineSinProfileSecondInterval n 512) ≤
      (1 : ℚ) / 100000000000000 := by
  have hN := factorTwoAffineSinProfileSecondNumerator_metrics hnle
  have hF := factorTwoAffineSinTailDenomCube_metrics hnle
  have hdiv := width_div_le_of_lower hN.1 hF.1 hN.2.1
    (by norm_num : (0 : ℚ) ≤ 4000000000)
    (by norm_num : (0 : ℚ) < 15625000000000000) hF.2.2
  unfold factorTwoAffineSinProfileSecondInterval
  calc
    width ((RatInterval.pure 2 * factorTwoAffineCosYInterval n *
        (RatInterval.pure 3 * RatInterval.pure (factorTwoAffineCosXQ 512 ^ 2) -
          nonnegSquare (factorTwoAffineCosYInterval n))) /
        (factorTwoAffineCosDenomInterval n 512 *
          nonnegSquare (factorTwoAffineCosDenomInterval n 512))) ≤
      (15625000000000000 : ℚ)⁻¹ *
        width (RatInterval.pure 2 * factorTwoAffineCosYInterval n *
          (RatInterval.pure 3 * RatInterval.pure (factorTwoAffineCosXQ 512 ^ 2) -
            nonnegSquare (factorTwoAffineCosYInterval n))) +
      4000000000 *
        (width (factorTwoAffineCosDenomInterval n 512 *
          nonnegSquare (factorTwoAffineCosDenomInterval n 512)) /
            (15625000000000000 * 15625000000000000)) := hdiv
    _ ≤ (15625000000000000 : ℚ)⁻¹ * (1 / 5000 : ℚ) +
      4000000000 * (480000 /
        (15625000000000000 * 15625000000000000) : ℚ) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hN.2.2 (by positivity)
      · exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hF.2.1 (by positivity)) (by norm_num)
    _ ≤ (1 : ℚ) / 100000000000000 := by norm_num

private theorem factorTwoAffineSinUnweightedTailMainInterval_valid
    {n : ℕ} (hnle : n ≤ 200) :
    (factorTwoAffineSinUnweightedTailMainInterval n 512).Valid := by
  have hY := factorTwoAffineSinTailY_metrics hnle
  have hD := factorTwoAffineSinTailDenom_metrics hnle
  have hE := factorTwoAffineSinTailDenomSquare_metrics hnle
  have hF := factorTwoAffineSinTailDenomCube_metrics hnle
  have hProfile : (factorTwoAffineSinProfileInterval n 512).Valid := by
    exact valid_div_of_pos hY.1 hD.1
      ((by norm_num : (0 : ℚ) < 250000).trans_le hD.2.2.2)
  have hDerivNumerator :
      (RatInterval.pure (-2) * factorTwoAffineCosYInterval n *
        RatInterval.pure (factorTwoAffineCosXQ 512)).Valid :=
    valid_mul (valid_mul (valid_pure (-2)) hY.1) (valid_pure _)
  have hDeriv : (factorTwoAffineSinProfileDerivInterval n 512).Valid := by
    unfold factorTwoAffineSinProfileDerivInterval
    exact valid_div_of_pos hDerivNumerator hE.1
      ((by norm_num : (0 : ℚ) < 62500000000).trans_le hE.2.2.2)
  have hSecondNumerator :=
    (factorTwoAffineSinProfileSecondNumerator_metrics hnle).1
  have hSecond : (factorTwoAffineSinProfileSecondInterval n 512).Valid := by
    unfold factorTwoAffineSinProfileSecondInterval
    exact valid_div_of_pos hSecondNumerator hF.1
      ((by norm_num : (0 : ℚ) < 15625000000000000).trans_le hF.2.2)
  unfold factorTwoAffineSinUnweightedTailMainInterval
  exact valid_add
    (valid_sub hProfile (valid_div_of_pos hDeriv (valid_pure 2)
      (by norm_num [RatInterval.pure])))
    (valid_div_of_pos hSecond (valid_pure 12)
      (by norm_num [RatInterval.pure]))

private theorem factorTwoAffineSinUnweightedTailMainInterval_width_le
    {n : ℕ} (hnle : n ≤ 200) :
    width (factorTwoAffineSinUnweightedTailMainInterval n 512) ≤
      (1 : ℚ) / 50000000000000 := by
  have hY := factorTwoAffineSinTailY_metrics hnle
  have hE := factorTwoAffineSinTailDenomSquare_metrics hnle
  have hF := factorTwoAffineSinTailDenomCube_metrics hnle
  have hDerivNumerator :
      (RatInterval.pure (-2) * factorTwoAffineCosYInterval n *
        RatInterval.pure (factorTwoAffineCosXQ 512)).Valid :=
    valid_mul (valid_mul (valid_pure (-2)) hY.1) (valid_pure _)
  have hDeriv : (factorTwoAffineSinProfileDerivInterval n 512).Valid := by
    unfold factorTwoAffineSinProfileDerivInterval
    exact valid_div_of_pos hDerivNumerator hE.1
      ((by norm_num : (0 : ℚ) < 62500000000).trans_le hE.2.2.2)
  have hSecondNumerator :=
    (factorTwoAffineSinProfileSecondNumerator_metrics hnle).1
  have hSecond : (factorTwoAffineSinProfileSecondInterval n 512).Valid := by
    unfold factorTwoAffineSinProfileSecondInterval
    exact valid_div_of_pos hSecondNumerator hF.1
      ((by norm_num : (0 : ℚ) < 15625000000000000).trans_le hF.2.2)
  have hDerivDiv :
      width (factorTwoAffineSinProfileDerivInterval n 512 /
        RatInterval.pure 2) =
        (1 / 2 : ℚ) *
          width (factorTwoAffineSinProfileDerivInterval n 512) := by
    change width (factorTwoAffineSinProfileDerivInterval n 512 *
      RatInterval.pure ((2 : ℚ)⁻¹)) = _
    rw [width_mul_pure _ hDeriv]
    norm_num
  have hSecondDiv :
      width (factorTwoAffineSinProfileSecondInterval n 512 /
        RatInterval.pure 12) =
        (1 / 12 : ℚ) *
          width (factorTwoAffineSinProfileSecondInterval n 512) := by
    change width (factorTwoAffineSinProfileSecondInterval n 512 *
      RatInterval.pure ((12 : ℚ)⁻¹)) = _
    rw [width_mul_pure _ hSecond]
    norm_num
  unfold factorTwoAffineSinUnweightedTailMainInterval
  rw [width_add, width_sub, hDerivDiv, hSecondDiv]
  calc
    width (factorTwoAffineSinProfileInterval n 512) +
        (1 / 2 : ℚ) * width (factorTwoAffineSinProfileDerivInterval n 512) +
      (1 / 12 : ℚ) * width
        (factorTwoAffineSinProfileSecondInterval n 512) ≤
      (1 / 100000000000000 : ℚ) +
        (1 / 2 : ℚ) * (1 / 100000000000000 : ℚ) +
      (1 / 12 : ℚ) * (1 / 100000000000000 : ℚ) := by
        gcongr
        · exact factorTwoAffineSinProfileInterval_width_le hnle
        · exact factorTwoAffineSinProfileDerivInterval_width_le hnle
        · exact factorTwoAffineSinProfileSecondInterval_width_le hnle
    _ ≤ (1 : ℚ) / 50000000000000 := by norm_num

private theorem factorTwoAffineSinDerivativeTailRadius_width_le
    {n : ℕ} (hnle : n ≤ 200) :
    width (⟨-factorTwoAffineSinDerivativeTailRadiusQ n 512,
      factorTwoAffineSinDerivativeTailRadiusQ n 512⟩ : RatInterval) ≤
        (1 : ℚ) / 8000000000 := by
  have hY := factorTwoAffineSinTailY_metrics hnle
  have hu := hY.2.1.2
  unfold factorTwoAffineSinDerivativeTailRadiusQ
  unfold width
  change
    (2 * (factorTwoAffineCosYInterval n).upper /
      factorTwoAffineCosXQ 512 ^ 5) -
      (-(2 * (factorTwoAffineCosYInterval n).upper /
        factorTwoAffineCosXQ 512 ^ 5)) ≤ (1 : ℚ) / 8000000000
  rw [sub_neg_eq_add, show
    2 * (factorTwoAffineCosYInterval n).upper / factorTwoAffineCosXQ 512 ^ 5 +
        2 * (factorTwoAffineCosYInterval n).upper / factorTwoAffineCosXQ 512 ^ 5 =
      2 * (2 * (factorTwoAffineCosYInterval n).upper /
        factorTwoAffineCosXQ 512 ^ 5) by ring]
  calc
    2 * (2 * (factorTwoAffineCosYInterval n).upper /
        factorTwoAffineCosXQ 512 ^ 5) ≤
      2 * (2 * (1000 : ℚ) / factorTwoAffineCosXQ 512 ^ 5) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hu (by norm_num))
          (pow_nonneg (by norm_num [factorTwoAffineCosXQ]) 5)
    _ ≤ (1 : ℚ) / 8000000000 := by
      norm_num [factorTwoAffineCosXQ]

private theorem factorTwoAffineSinUnweightedTailInterval_width_le
    {n : ℕ} (hnle : n ≤ 200) :
    width (factorTwoAffineSinUnweightedTailInterval n 512) ≤
      (1 : ℚ) / 7000000000 := by
  unfold factorTwoAffineSinUnweightedTailInterval
  rw [width_add]
  calc
    width (factorTwoAffineSinUnweightedTailMainInterval n 512) +
        width (⟨-factorTwoAffineSinDerivativeTailRadiusQ n 512,
          factorTwoAffineSinDerivativeTailRadiusQ n 512⟩ : RatInterval) ≤
      (1 / 50000000000000 : ℚ) + 1 / 8000000000 :=
        add_le_add
          (factorTwoAffineSinUnweightedTailMainInterval_width_le hnle)
          (factorTwoAffineSinDerivativeTailRadius_width_le hnle)
    _ ≤ (1 : ℚ) / 7000000000 := by norm_num

private theorem factorTwoAffineSinUnweightedSeriesInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) (hnle : n ≤ 200) :
    width (factorTwoAffineSinUnweightedSeriesInterval n) ≤
      (1 : ℚ) / 6000000000 := by
  unfold factorTwoAffineSinUnweightedSeriesInterval
    factorTwoAffineSinUnweightedHeadCount
  rw [width_add]
  calc
    width (factorTwoAffineSinUnweightedHeadInterval n 512) +
        width (factorTwoAffineSinUnweightedTailInterval n 512) ≤
      (1 / 100000000000 : ℚ) + 1 / 7000000000 :=
        add_le_add (factorTwoAffineSinUnweightedHeadInterval_width_le hn)
          (factorTwoAffineSinUnweightedTailInterval_width_le hnle)
    _ ≤ (1 : ℚ) / 6000000000 := by norm_num

private theorem factorTwoAffineSinDyadicSeriesInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) (hnle : n ≤ 200) :
    width (factorTwoAffineSinDyadicSeriesInterval n) ≤
      (1 : ℚ) / 5000000000 := by
  unfold factorTwoAffineSinDyadicSeriesInterval
  rw [width_add]
  calc
    width (factorTwoAffineSinUnweightedSeriesInterval n) +
        width (factorTwoAffineSinDyadicCorrectionSeriesInterval n) ≤
      (1 / 6000000000 : ℚ) + 1 / 400000000000 :=
        add_le_add (factorTwoAffineSinUnweightedSeriesInterval_width_le hn hnle)
          (factorTwoAffineSinDyadicCorrectionSeriesInterval_width_le hn)
    _ ≤ (1 : ℚ) / 5000000000 := by norm_num

private theorem factorTwoAffineSinInitialKernelInterval_metrics
    {n : ℕ} (hn : 1 ≤ n) :
    (factorTwoAffineSinInitialKernelInterval n).Valid ∧
      (factorTwoAffineSinInitialKernelInterval n).AbsBound 1 ∧
      width (factorTwoAffineSinInitialKernelInterval n) ≤
        (1 : ℚ) / 100000000000000 := by
  let x : ℚ := 1 / 4
  let Y := factorTwoAffineCosYInterval n
  let Y2 := nonnegSquare Y
  let A := RatInterval.pure 2 * RatInterval.pure x
  let N := A * Y
  let D := RatInterval.pure (x ^ 2) + Y2
  let E := nonnegSquare D
  let floor : ℚ := x ^ 2 + ((9 / 2 : ℚ) * n) ^ 2
  have hx : (0 : ℚ) < x := by norm_num [x]
  have hnQ : (0 : ℚ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hfloor : 0 < floor := by dsimp only [floor]; positivity
  have hxn : 9 * x * (n : ℚ) ≤ floor := by
    dsimp only [floor]
    nlinarith [sq_nonneg (x - (9 / 2 : ℚ) * n)]
  have hnn : 20 * (n : ℚ) ^ 2 ≤ floor := by
    dsimp only [floor]
    nlinarith [sq_nonneg x, sq_nonneg (n : ℚ)]
  have hBfloor : x ^ 2 + 25 * (n : ℚ) ^ 2 ≤
      (5 / 4 : ℚ) * floor := by
    dsimp only [floor]
    nlinarith [sq_nonneg x, sq_nonneg (n : ℚ)]
  have hYvalid := factorTwoAffineSinYInterval_valid n
  have hYabs := factorTwoAffineSinYInterval_absBound n
  have hY2valid := factorTwoAffineSinYSqInterval_valid n
  have hY2abs := factorTwoAffineSinYSqInterval_absBound n
  have hAvalid : A.Valid := valid_mul (valid_pure 2) (valid_pure x)
  have hAabs : A.AbsBound (2 * x) := by
    exact absBound_mul (valid_pure 2) (valid_pure x)
      (absBound_pure (by norm_num)) (absBound_pure (by rw [abs_of_pos hx]))
      (by norm_num) hx.le
  have hAwidth : width A = 0 := by
    dsimp only [A]
    rw [width_pure_mul 2 (valid_pure x), width_pure]
    norm_num
  have hNvalid : N.Valid := valid_mul hAvalid hYvalid
  have hNabs : N.AbsBound (10 * x * n) := by
    convert absBound_mul hAvalid hYvalid hAabs hYabs
      (mul_nonneg (by norm_num) hx.le) (by positivity) using 1 ; ring
  have hNwidth : width N ≤ 2 * x * n / 10000000000000 := by
    have hw := width_mul_le hAvalid hYvalid hAabs hYabs
      (mul_nonneg (by norm_num) hx.le) (by positivity)
    calc
      width N ≤ (5 * (n : ℚ)) * width A +
          (2 * x) * width Y := hw
      _ = (2 * x) * width Y := by rw [hAwidth]; ring
      _ ≤ (2 * x) * ((n : ℚ) / 10000000000000) :=
        mul_le_mul_of_nonneg_left (factorTwoAffineSinYInterval_width_le n)
          (mul_nonneg (by norm_num) hx.le)
      _ = 2 * x * n / 10000000000000 := by ring
  have hDvalid : D.Valid := valid_add (valid_pure _) hY2valid
  have hDabs : D.AbsBound (x ^ 2 + 25 * (n : ℚ) ^ 2) := by
    simpa only [D, Y2] using absBound_add
      (absBound_pure (by rw [abs_of_nonneg (sq_nonneg x)])) hY2abs
  have hDwidth : width D ≤ (n : ℚ) ^ 2 / 1000000000000 := by
    dsimp only [D, Y2]
    rw [width_add, width_pure, zero_add]
    exact factorTwoAffineSinYSqInterval_width_le n
  have hDlower : floor ≤ D.lower := by
    dsimp only [floor, D, Y2]
    change x ^ 2 + ((9 / 2 : ℚ) * n) ^ 2 ≤
      x ^ 2 + (factorTwoAffineCosYInterval n).lower ^ 2
    exact add_le_add (le_refl _)
      (pow_le_pow_left₀ (by positivity)
        (factorTwoAffineSinYInterval_lower_le n) 2)
  have hDlower0 : 0 ≤ D.lower := hfloor.le.trans hDlower
  have hEvalid : E.Valid := by
    dsimp only [E]
    change D.lower ^ 2 ≤ D.upper ^ 2
    exact pow_le_pow_left₀ hDlower0 hDvalid 2
  have hElower : floor * floor ≤ E.lower := by
    dsimp only [E]
    change floor * floor ≤ D.lower ^ 2
    simpa only [pow_two] using pow_le_pow_left₀ hfloor.le hDlower 2
  have hEwidth : width E ≤
      (5 / 2 : ℚ) * floor * n ^ 2 / 1000000000000 := by
    have hsum : D.upper + D.lower ≤ (5 / 2 : ℚ) * floor := by
      have hu := hDabs.2
      have hl := hDvalid.trans hu
      calc
        D.upper + D.lower ≤
            (x ^ 2 + 25 * (n : ℚ) ^ 2) +
              (x ^ 2 + 25 * (n : ℚ) ^ 2) := add_le_add hu hl
        _ ≤ (5 / 4 : ℚ) * floor + (5 / 4 : ℚ) * floor :=
          add_le_add hBfloor hBfloor
        _ = (5 / 2 : ℚ) * floor := by ring
    dsimp only [E]
    change D.upper ^ 2 - D.lower ^ 2 ≤ _
    rw [sq_sub_sq]
    calc
      (D.upper + D.lower) * (D.upper - D.lower) ≤
          ((5 / 2 : ℚ) * floor) *
            ((n : ℚ) ^ 2 / 1000000000000) := by
        exact mul_le_mul hsum hDwidth (width_nonneg hDvalid) (by positivity)
      _ = (5 / 2 : ℚ) * floor * n ^ 2 / 1000000000000 := by ring
  have hvalid : (N / E).Valid := valid_div_of_pos hNvalid hEvalid
    ((mul_pos hfloor hfloor).trans_le hElower)
  have habsSmall : (N / E).AbsBound
      ((10 * x * n) * (floor * floor)⁻¹) :=
    absBound_div_of_lower hNvalid hEvalid hNabs (by positivity)
      (mul_pos hfloor hfloor) hElower
  have hten : 10 * x * (n : ℚ) ≤ floor * floor := by
    have hnOne : (1 : ℚ) ≤ n := by exact_mod_cast hn
    have htwenty : (20 : ℚ) ≤ floor := by
      calc
        (20 : ℚ) ≤ 20 * (n : ℚ) ^ 2 := by
          nlinarith
        _ ≤ floor := hnn
    have htenFloor : (10 : ℚ) ≤ 9 * floor := by linarith
    calc
      10 * x * (n : ℚ) = 10 * (x * n) := by ring
      _ ≤ (9 * floor) * (x * n) :=
        mul_le_mul_of_nonneg_right htenFloor (by positivity)
      _ = floor * (9 * x * n) := by ring
      _ ≤ floor * floor := mul_le_mul_of_nonneg_left hxn hfloor.le
  have habs : (N / E).AbsBound 1 := by
    apply factorTwoAffineSin_absBound_mono habsSmall
    rw [mul_inv_le_iff₀ (mul_pos hfloor hfloor)]
    simpa only [one_mul] using hten
  have hdiv := width_div_le_of_lower hNvalid hEvalid hNabs (by positivity)
    (mul_pos hfloor hfloor) hElower
  have hwidth : width (N / E) ≤ (1 : ℚ) / 100000000000000 := by
    calc
      width (N / E) ≤ (floor * floor)⁻¹ * width N +
          (10 * x * n) *
            (width E / ((floor * floor) * (floor * floor))) := hdiv
      _ ≤ (floor * floor)⁻¹ *
            (2 * x * n / 10000000000000) +
          (10 * x * n) *
            (((5 / 2 : ℚ) * floor * n ^ 2 / 1000000000000) /
              ((floor * floor) * (floor * floor))) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hNwidth
            (inv_nonneg.mpr (mul_nonneg hfloor.le hfloor.le))
        · exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hEwidth
              (mul_nonneg (mul_nonneg hfloor.le hfloor.le)
                (mul_nonneg hfloor.le hfloor.le))) (by positivity)
      _ ≤ (1 : ℚ) / 100000000000000 :=
        factorTwoAffineSinKernel_width_budget hn hx hfloor hxn hnn
  simpa only [factorTwoAffineSinInitialKernelInterval, x, Y, Y2, A, N, D, E]
    using ⟨hvalid, habs, hwidth⟩

private theorem factorTwoAffineSinUnweightedHeadInterval_absBound
    {n : ℕ} (hn : 1 ≤ n) (K : ℕ) :
    (factorTwoAffineSinUnweightedHeadInterval n K).AbsBound K := by
  induction K with
  | zero =>
      norm_num [factorTwoAffineSinUnweightedHeadInterval, AbsBound,
        RatInterval.pure]
  | succ K ih =>
      rw [factorTwoAffineSinUnweightedHeadInterval]
      have hterm :=
        (factorTwoAffineSinUnweightedKernelInterval_valid_absBound hn K).2
      convert absBound_add ih hterm using 1
      push_cast
      ring

private theorem factorTwoAffineSinUnweightedTailInterval_absBound
    {n : ℕ} (hnle : n ≤ 200) :
    (factorTwoAffineSinUnweightedTailInterval n 512).AbsBound 4 := by
  have hY := factorTwoAffineSinTailY_metrics hnle
  have hD := factorTwoAffineSinTailDenom_metrics hnle
  have hE := factorTwoAffineSinTailDenomSquare_metrics hnle
  have hF := factorTwoAffineSinTailDenomCube_metrics hnle
  have hProfileSmall : (factorTwoAffineSinProfileInterval n 512).AbsBound
      (1000 * (250000 : ℚ)⁻¹) := by
    unfold factorTwoAffineSinProfileInterval
    exact absBound_div_of_lower hY.1 hD.1 hY.2.1 (by norm_num)
      (by norm_num) hD.2.2.2
  have hProfile : (factorTwoAffineSinProfileInterval n 512).AbsBound 1 :=
    factorTwoAffineSin_absBound_mono hProfileSmall (by norm_num)
  let Y := factorTwoAffineCosYInterval n
  let X := RatInterval.pure (factorTwoAffineCosXQ 512)
  let N := RatInterval.pure (-2) * Y * X
  have hXvalid : X.Valid := valid_pure _
  have hXabs : X.AbsBound 514 := by
    apply absBound_pure
    norm_num [X, factorTwoAffineCosXQ]
  have hNegValid : (RatInterval.pure (-2) * Y).Valid :=
    valid_mul (valid_pure _) hY.1
  have hNegAbs : (RatInterval.pure (-2) * Y).AbsBound 2000 := by
    apply factorTwoAffineSin_absBound_mono
      (absBound_mul (valid_pure (-2)) hY.1
        (absBound_pure (q := -2) (B := 2) (by norm_num)) hY.2.1
        (by norm_num) (by norm_num))
    norm_num
  have hNvalid : N.Valid := valid_mul hNegValid hXvalid
  have hNabs : N.AbsBound 1100000 := by
    exact factorTwoAffineSin_absBound_mono
      (absBound_mul hNegValid hXvalid hNegAbs hXabs (by norm_num) (by norm_num))
      (by norm_num)
  have hDerivSmall : (factorTwoAffineSinProfileDerivInterval n 512).AbsBound
      (1100000 * (62500000000 : ℚ)⁻¹) := by
    unfold factorTwoAffineSinProfileDerivInterval
    dsimp only [Y, X, N] at hNvalid hNabs ⊢
    exact absBound_div_of_lower hNvalid hE.1 hNabs (by norm_num)
      (by norm_num) hE.2.2.2
  have hDeriv : (factorTwoAffineSinProfileDerivInterval n 512).AbsBound 1 :=
    factorTwoAffineSin_absBound_mono hDerivSmall (by norm_num)
  have hSecondNumerator := factorTwoAffineSinProfileSecondNumerator_metrics hnle
  have hSecondSmall : (factorTwoAffineSinProfileSecondInterval n 512).AbsBound
      (4000000000 * (15625000000000000 : ℚ)⁻¹) := by
    unfold factorTwoAffineSinProfileSecondInterval
    exact absBound_div_of_lower hSecondNumerator.1 hF.1 hSecondNumerator.2.1
      (by norm_num) (by norm_num) hF.2.2
  have hSecond : (factorTwoAffineSinProfileSecondInterval n 512).AbsBound 1 :=
    factorTwoAffineSin_absBound_mono hSecondSmall (by norm_num)
  have hDerivValid : (factorTwoAffineSinProfileDerivInterval n 512).Valid := by
    unfold factorTwoAffineSinProfileDerivInterval
    dsimp only [Y, X, N] at hNvalid ⊢
    exact valid_div_of_pos hNvalid hE.1
      ((by norm_num : (0 : ℚ) < 62500000000).trans_le hE.2.2.2)
  have hSecondValid : (factorTwoAffineSinProfileSecondInterval n 512).Valid := by
    unfold factorTwoAffineSinProfileSecondInterval
    exact valid_div_of_pos hSecondNumerator.1 hF.1
      ((by norm_num : (0 : ℚ) < 15625000000000000).trans_le hF.2.2)
  have hDerivDiv :
      (factorTwoAffineSinProfileDerivInterval n 512 /
        RatInterval.pure 2).AbsBound 1 := by
    apply factorTwoAffineSin_absBound_mono
      (absBound_div_of_lower (B := 1) (m := 2) hDerivValid
        (valid_pure 2) hDeriv (by norm_num)
        (by norm_num) (by norm_num [RatInterval.pure]))
    norm_num
  have hSecondDiv :
      (factorTwoAffineSinProfileSecondInterval n 512 /
        RatInterval.pure 12).AbsBound 1 := by
    apply factorTwoAffineSin_absBound_mono
      (absBound_div_of_lower (B := 1) (m := 12) hSecondValid
        (valid_pure 12) hSecond (by norm_num)
        (by norm_num) (by norm_num [RatInterval.pure]))
    norm_num
  have hMain : (factorTwoAffineSinUnweightedTailMainInterval n 512).AbsBound 3 := by
    unfold factorTwoAffineSinUnweightedTailMainInterval
    convert absBound_add (absBound_sub hProfile hDerivDiv) hSecondDiv using 1 ;
      norm_num
  have hr : factorTwoAffineSinDerivativeTailRadiusQ n 512 ≤ (1 : ℚ) := by
    unfold factorTwoAffineSinDerivativeTailRadiusQ
    calc
      2 * (factorTwoAffineCosYInterval n).upper /
          factorTwoAffineCosXQ 512 ^ 5 ≤
        2 * (1000 : ℚ) / factorTwoAffineCosXQ 512 ^ 5 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hY.2.1.2 (by norm_num))
          (pow_nonneg (by norm_num [factorTwoAffineCosXQ]) 5)
      _ ≤ (1 : ℚ) := by norm_num [factorTwoAffineCosXQ]
  have hr0 : 0 ≤ factorTwoAffineSinDerivativeTailRadiusQ n 512 := by
    unfold factorTwoAffineSinDerivativeTailRadiusQ
    have hy0 : 0 ≤ (factorTwoAffineCosYInterval n).upper :=
      ((by positivity : (0 : ℚ) ≤ (9 / 2 : ℚ) * n).trans
        (factorTwoAffineSinYInterval_lower_le n)).trans hY.1
    exact div_nonneg (mul_nonneg (by norm_num) hy0)
      (pow_nonneg (by norm_num [factorTwoAffineCosXQ]) 5)
  have hRadius :
      (⟨-factorTwoAffineSinDerivativeTailRadiusQ n 512,
        factorTwoAffineSinDerivativeTailRadiusQ n 512⟩ : RatInterval).AbsBound 1 := by
    unfold AbsBound
    constructor <;> linarith
  unfold factorTwoAffineSinUnweightedTailInterval
  convert absBound_add hMain hRadius using 1 ; norm_num

private theorem factorTwoAffineSinDyadicCorrectionHeadInterval_absBound
    {n : ℕ} (hn : 1 ≤ n) (K : ℕ) :
    (factorTwoAffineSinDyadicCorrectionHeadInterval n K).AbsBound (2 * K) := by
  induction K with
  | zero =>
      norm_num [factorTwoAffineSinDyadicCorrectionHeadInterval, AbsBound,
        RatInterval.pure]
  | succ K ih =>
      rw [factorTwoAffineSinDyadicCorrectionHeadInterval]
      have hdef := factorTwoAffineSinDyadicDefect_metrics (K + 1)
      have hker := factorTwoAffineSinUnweightedKernelInterval_valid_absBound hn K
      have hterm : (factorTwoAffineSinDyadicCorrectionInterval n K).AbsBound 2 := by
        unfold factorTwoAffineSinDyadicCorrectionInterval
        convert absBound_mul hdef.1 hker.1 hdef.2.1 hker.2
          (by norm_num) (by norm_num) using 1 ; norm_num
      convert absBound_add ih hterm using 1
      push_cast
      ring

private theorem factorTwoAffineSinDyadicCorrectionSeriesInterval_absBound
    {n : ℕ} (hn : 1 ≤ n) :
    (factorTwoAffineSinDyadicCorrectionSeriesInterval n).AbsBound 41 := by
  have hhead := factorTwoAffineSinDyadicCorrectionHeadInterval_absBound hn 20
  have htail : (factorTwoAffineSinDyadicCorrectionTailInterval 20).AbsBound 1 := by
    norm_num [factorTwoAffineSinDyadicCorrectionTailInterval,
      factorTwoAffineSinDyadicCorrectionTailRadiusQ, AbsBound]
  unfold factorTwoAffineSinDyadicCorrectionSeriesInterval
  exact factorTwoAffineSin_absBound_mono (absBound_add hhead htail) (by norm_num)

private theorem factorTwoAffineSinDyadicSeriesInterval_absBound
    {n : ℕ} (hn : 1 ≤ n) (hnle : n ≤ 200) :
    (factorTwoAffineSinDyadicSeriesInterval n).AbsBound 600 := by
  have hhead := factorTwoAffineSinUnweightedHeadInterval_absBound hn 512
  have htail := factorTwoAffineSinUnweightedTailInterval_absBound hnle
  have hunweighted : (factorTwoAffineSinUnweightedSeriesInterval n).AbsBound 516 := by
    unfold factorTwoAffineSinUnweightedSeriesInterval
      factorTwoAffineSinUnweightedHeadCount
    convert absBound_add hhead htail using 1 ; norm_num
  have hcorrection := factorTwoAffineSinDyadicCorrectionSeriesInterval_absBound hn
  unfold factorTwoAffineSinDyadicSeriesInterval
  exact factorTwoAffineSin_absBound_mono
    (absBound_add hunweighted hcorrection) (by norm_num)

private theorem factorTwoAffineSin_mul_lower_eq_of_nonneg
    {I J : RatInterval} (hI : I.Valid) (hJ : J.Valid)
    (hI0 : 0 ≤ I.lower) (hJ0 : 0 ≤ J.lower) :
    (I * J).lower = I.lower * J.lower := by
  have hIu0 : 0 ≤ I.upper := hI0.trans hI
  have hJu0 : 0 ≤ J.upper := hJ0.trans hJ
  change min (min (I.lower * J.lower) (I.lower * J.upper))
      (min (I.upper * J.lower) (I.upper * J.upper)) =
    I.lower * J.lower
  apply le_antisymm
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · apply le_min
    · exact le_min le_rfl (mul_le_mul_of_nonneg_left hJ hI0)
    · exact le_min (mul_le_mul_of_nonneg_right hI hJ0)
        (mul_le_mul hI hJ hJ0 hIu0)

private theorem factorTwoAffineSin_mul_upper_eq_of_nonneg
    {I J : RatInterval} (hI : I.Valid) (hJ : J.Valid)
    (hI0 : 0 ≤ I.lower) (hJ0 : 0 ≤ J.lower) :
    (I * J).upper = I.upper * J.upper := by
  have hIu0 : 0 ≤ I.upper := hI0.trans hI
  have hJu0 : 0 ≤ J.upper := hJ0.trans hJ
  change max (max (I.lower * J.lower) (I.lower * J.upper))
      (max (I.upper * J.lower) (I.upper * J.upper)) =
    I.upper * J.upper
  apply le_antisymm
  · apply max_le
    · exact max_le (mul_le_mul hI hJ hJ0 hIu0)
        (mul_le_mul_of_nonneg_right hI hJu0)
    · exact max_le (mul_le_mul_of_nonneg_left hJ hIu0) le_rfl
  · exact (le_max_right _ _).trans (le_max_right _ _)

private structure FactorTwoAffineSinConstantMetrics where
  logValid : factorTwoPrimeLogTwoInterval.Valid
  logAbs : factorTwoPrimeLogTwoInterval.AbsBound 1
  logWidth : width factorTwoPrimeLogTwoInterval ≤ (1 : ℚ) / 100000000000000
  headValid : factorTwoHeadDefectInterval.Valid
  headAbs : factorTwoHeadDefectInterval.AbsBound 1
  headWidth : width factorTwoHeadDefectInterval ≤ (1 : ℚ) / 100000000000000
  betaValid : factorTwoPrimeBetaInterval.Valid
  betaAbs : factorTwoPrimeBetaInterval.AbsBound 1
  betaWidth : width factorTwoPrimeBetaInterval ≤ (1 : ℚ) / 10000000000000
  heightValid : factorTwoPrimeAffineHeightInterval.Valid
  heightAbs : factorTwoPrimeAffineHeightInterval.AbsBound 1
  heightWidth : width factorTwoPrimeAffineHeightInterval ≤
    (1 : ℚ) / 1000000000000

private theorem factorTwoAffineSinConstantInterval_metrics :
    FactorTwoAffineSinConstantMetrics := by
  have hwidth := factorTwoPerturbationConstantIntervals_width_le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact valid_of_contains factorTwoPrimeLogTwoInterval_contains
  · norm_num [AbsBound, factorTwoPrimeLogTwoInterval]
  · norm_num [width, factorTwoPrimeLogTwoInterval]
  · exact valid_of_contains factorTwoHeadDefectInterval_contains
  · let F := sqrtTwoInterval - RatInterval.pure 1
    have hsValid : sqrtTwoInterval.Valid :=
      valid_of_contains sqrtTwoInterval_contains
    have hFvalid : F.Valid := valid_sub hsValid (valid_pure 1)
    have hFabs : F.AbsBound 1 := by
      unfold AbsBound
      change -(1 : ℚ) ≤ sqrtTwoInterval.lower - 1 ∧
        sqrtTwoInterval.upper - 1 ≤ 1
      norm_num [sqrtTwoInterval]
    simpa only [factorTwoHeadDefectInterval, F, one_mul] using
      absBound_mul hFvalid hFvalid hFabs hFabs (by norm_num) (by norm_num)
  · exact hwidth.2.2
  · exact valid_of_contains factorTwoPrimeBetaInterval_contains
  · have hLogValid : factorTwoPrimeLogThreeInterval.Valid :=
      valid_of_contains factorTwoPrimeLogThreeInterval_contains
    have hLogTwoAbs : factorTwoPrimeLogTwoInterval.AbsBound 1 := by
      norm_num [factorTwoPrimeLogTwoInterval, AbsBound]
    have hShiftAbs : factorTwoPrimeShiftInterval.AbsBound (1 / 2 : ℚ) := by
      norm_num [factorTwoPrimeShiftInterval, AbsBound]
    have hLogAbs : factorTwoPrimeLogThreeInterval.AbsBound (3 / 2 : ℚ) := by
      unfold factorTwoPrimeLogThreeInterval
      exact factorTwoAffineSin_absBound_mono
        (absBound_add hLogTwoAbs hShiftAbs) (by norm_num)
    have hSqrtValid : factorTwoPrimeSqrtThreeInterval.Valid :=
      valid_of_contains factorTwoPrimeSqrtThreeInterval_contains
    have hSqrtFloor : (3 / 2 : ℚ) ≤
        factorTwoPrimeSqrtThreeInterval.lower := by
      norm_num [factorTwoPrimeSqrtThreeInterval]
    have hraw := absBound_div_of_lower hLogValid hSqrtValid hLogAbs
      (by norm_num) (by norm_num : (0 : ℚ) < 3 / 2) hSqrtFloor
    apply factorTwoAffineSin_absBound_mono hraw
    norm_num
  · exact hwidth.1
  · exact valid_of_contains factorTwoPrimeAffineHeightInterval_contains
  · let Num := RatInterval.pure 2 * factorTwoPrimeShiftInterval
    let Den := factorTwoPrimeLogTwoInterval
    let R := Num / Den
    have hShiftValid : factorTwoPrimeShiftInterval.Valid :=
      valid_of_contains factorTwoPrimeShiftInterval_contains
    have hTwoLower : 0 ≤ (RatInterval.pure (2 : ℚ)).lower := by
      change (0 : ℚ) ≤ 2
      norm_num
    have hShiftLower : 0 ≤ factorTwoPrimeShiftInterval.lower := by
      norm_num [factorTwoPrimeShiftInterval]
    have hNumValid : Num.Valid := valid_mul (valid_pure 2) hShiftValid
    have hNumLower : 0 ≤ Num.lower := by
      dsimp only [Num]
      exact mul_lower_nonneg_of_nonneg hTwoLower hShiftLower
        (valid_pure 2) hShiftValid
    have hDenValid : Den.Valid :=
      valid_of_contains factorTwoPrimeLogTwoInterval_contains
    have hDenPos : 0 < Den.lower := by
      dsimp only [Den]
      norm_num [factorTwoPrimeLogTwoInterval]
    have hInvValid : Den⁻¹.Valid := valid_inv_of_pos hDenValid hDenPos
    have hInvLower : 0 ≤ Den⁻¹.lower := by
      change 0 ≤ Den.upper⁻¹
      exact inv_nonneg.mpr (hDenPos.le.trans hDenValid)
    have hRvalid : R.Valid := valid_div_of_pos hNumValid hDenValid hDenPos
    have hRlowerEq : R.lower = Num.lower * Den.upper⁻¹ := by
      change (Num * Den⁻¹).lower = Num.lower * Den⁻¹.lower
      exact factorTwoAffineSin_mul_lower_eq_of_nonneg hNumValid hInvValid
        hNumLower hInvLower
    have hRupperEq : R.upper = Num.upper * Den.lower⁻¹ := by
      change (Num * Den⁻¹).upper = Num.upper * Den⁻¹.upper
      exact factorTwoAffineSin_mul_upper_eq_of_nonneg hNumValid hInvValid
        hNumLower hInvLower
    have hNumLowerEq : Num.lower =
        2 * factorTwoPrimeShiftInterval.lower := by
      exact factorTwoAffineSin_mul_lower_eq_of_nonneg (valid_pure 2) hShiftValid
        hTwoLower hShiftLower
    have hNumUpperEq : Num.upper =
        2 * factorTwoPrimeShiftInterval.upper := by
      exact factorTwoAffineSin_mul_upper_eq_of_nonneg (valid_pure 2) hShiftValid
        hTwoLower hShiftLower
    have hRlower : (1 : ℚ) ≤ R.lower := by
      rw [hRlowerEq, hNumLowerEq]
      dsimp only [Den]
      norm_num [factorTwoPrimeShiftInterval, factorTwoPrimeLogTwoInterval]
    have hRupper : R.upper ≤ (2 : ℚ) := by
      rw [hRupperEq, hNumUpperEq]
      dsimp only [Den]
      norm_num [factorTwoPrimeShiftInterval, factorTwoPrimeLogTwoInterval]
    unfold AbsBound
    change -(1 : ℚ) ≤ (RatInterval.pure 2 - R).lower ∧
      (RatInterval.pure 2 - R).upper ≤ 1
    change -(1 : ℚ) ≤ 2 - R.upper ∧ 2 - R.lower ≤ 1
    constructor <;> linarith
  · exact hwidth.2.1

private theorem factorTwoAffineSinPrimeSinInterval_metrics
    (n : FactorTwoCanonicalEvenIndex) :
    (factorTwoPrimeSinInterval n).Valid ∧
      (factorTwoPrimeSinInterval n).AbsBound 2 ∧
      width (factorTwoPrimeSinInterval n) ≤ (1 : ℚ) / 10000000000 := by
  have hcontains := factorTwoPrimeSinInterval_contains n
  have hvalid := valid_of_contains hcontains
  have hwidth := factorTwoPrimeSinInterval_width_le n
  have hs := abs_sin_le_one
    (2 * factorTwoMomentY n.1 * factorTwoPrimeShift)
  have hwOne : width (factorTwoPrimeSinInterval n) ≤ (1 : ℚ) :=
    hwidth.trans (by norm_num)
  have hwReal :
      (((width (factorTwoPrimeSinInterval n) : ℚ) : ℝ)) ≤ 1 := by
    exact_mod_cast hwOne
  have hlReal : (-2 : ℝ) ≤ (factorTwoPrimeSinInterval n).lower := by
    unfold Contains at hcontains
    unfold width at hwReal
    rw [abs_le] at hs
    norm_num only [Rat.cast_sub] at hwReal
    linarith [hcontains.2, hs.1]
  have huReal : ((factorTwoPrimeSinInterval n).upper : ℝ) ≤ 2 := by
    unfold Contains at hcontains
    unfold width at hwReal
    rw [abs_le] at hs
    norm_num only [Rat.cast_sub] at hwReal
    linarith [hcontains.1, hs.2]
  constructor
  · exact hvalid
  constructor
  · unfold AbsBound
    constructor
    · exact_mod_cast hlReal
    · exact_mod_cast huReal
  · exact hwidth

private theorem factorTwoAffineSinHeadCoefficient_metrics :
    let C := factorTwoHeadDefectInterval / factorTwoPrimeLogTwoInterval
    C.Valid ∧ C.AbsBound 2 ∧
      width C ≤ (1 : ℚ) / 10000000000000 := by
  dsimp only
  have h := factorTwoAffineSinConstantInterval_metrics
  have hvalid := valid_div_of_pos h.headValid h.logValid
    (by norm_num [factorTwoPrimeLogTwoInterval])
  have habsSmall := absBound_div_of_lower h.headValid h.logValid h.headAbs
    (by norm_num : (0 : ℚ) ≤ 1) (by norm_num : (0 : ℚ) < 3 / 5)
    (by norm_num [factorTwoPrimeLogTwoInterval])
  have hwidth := width_div_le_of_lower h.headValid h.logValid h.headAbs
    (by norm_num : (0 : ℚ) ≤ 1) (by norm_num : (0 : ℚ) < 3 / 5)
    (by norm_num [factorTwoPrimeLogTwoInterval])
  constructor
  · exact hvalid
  constructor
  · exact factorTwoAffineSin_absBound_mono habsSmall (by norm_num)
  · calc
      width (factorTwoHeadDefectInterval / factorTwoPrimeLogTwoInterval) ≤
        (3 / 5 : ℚ)⁻¹ * width factorTwoHeadDefectInterval +
          1 * (width factorTwoPrimeLogTwoInterval / ((3 / 5) * (3 / 5))) :=
        hwidth
      _ ≤ (3 / 5 : ℚ)⁻¹ * (1 / 100000000000000 : ℚ) +
          1 * ((1 / 100000000000000 : ℚ) / ((3 / 5) * (3 / 5))) := by
        gcongr
        · exact h.headWidth
        · exact h.logWidth
      _ ≤ (1 : ℚ) / 10000000000000 := by norm_num

private theorem factorTwoAffineSinSeriesCoefficient_metrics :
    let C := RatInterval.pure 1 / factorTwoPrimeLogTwoInterval
    C.Valid ∧ C.AbsBound 2 ∧
      width C ≤ (3 : ℚ) / 100000000000000 := by
  dsimp only
  have h := factorTwoAffineSinConstantInterval_metrics
  have hvalid := valid_div_of_pos (valid_pure 1) h.logValid
    (by norm_num [factorTwoPrimeLogTwoInterval])
  have habsSmall := absBound_div_of_lower (valid_pure 1) h.logValid
    (absBound_pure (by norm_num)) (by norm_num : (0 : ℚ) ≤ 1)
    (by norm_num : (0 : ℚ) < 3 / 5)
    (by norm_num [factorTwoPrimeLogTwoInterval])
  have hwidth := width_div_le_of_lower (valid_pure 1) h.logValid
    (absBound_pure (by norm_num)) (by norm_num : (0 : ℚ) ≤ 1)
    (by norm_num : (0 : ℚ) < 3 / 5)
    (by norm_num [factorTwoPrimeLogTwoInterval])
  constructor
  · exact hvalid
  constructor
  · exact factorTwoAffineSin_absBound_mono habsSmall (by norm_num)
  · calc
      width (RatInterval.pure 1 / factorTwoPrimeLogTwoInterval) ≤
        (3 / 5 : ℚ)⁻¹ * width (RatInterval.pure 1) +
          1 * (width factorTwoPrimeLogTwoInterval / ((3 / 5) * (3 / 5))) :=
        hwidth
      _ ≤ (3 / 5 : ℚ)⁻¹ * 0 +
          1 * ((1 / 100000000000000 : ℚ) / ((3 / 5) * (3 / 5))) := by
        rw [width_pure]
        gcongr
        exact h.logWidth
      _ ≤ (3 : ℚ) / 100000000000000 := by norm_num

private theorem factorTwoAffineSinPrimeTerm_width_le
    (n : FactorTwoCanonicalEvenIndex) :
    width (RatInterval.pure 2 * factorTwoPrimeBetaInterval *
      factorTwoPrimeAffineHeightInterval * factorTwoPrimeSinInterval n) ≤
        (1 : ℚ) / 4000000000 := by
  have h := factorTwoAffineSinConstantInterval_metrics
  have hSin := factorTwoAffineSinPrimeSinInterval_metrics n
  have hTwoBetaValid := valid_mul (valid_pure 2) h.betaValid
  have hTwoBetaAbs :
      (RatInterval.pure 2 * factorTwoPrimeBetaInterval).AbsBound 2 := by
    apply factorTwoAffineSin_absBound_mono
      (absBound_mul (valid_pure 2) h.betaValid
        (absBound_pure (q := 2) (B := 2) (by norm_num)) h.betaAbs
        (by norm_num) (by norm_num))
    norm_num
  have hTwoBetaWidth :
      width (RatInterval.pure 2 * factorTwoPrimeBetaInterval) ≤
      (2 : ℚ) / 10000000000000 := by
    rw [width_pure_mul 2 h.betaValid]
    rw [show |(2 : ℚ)| = 2 by norm_num]
    linarith [h.betaWidth]
  have hCoeffValid := valid_mul hTwoBetaValid h.heightValid
  have hCoeffAbs : (RatInterval.pure 2 * factorTwoPrimeBetaInterval *
      factorTwoPrimeAffineHeightInterval).AbsBound 2 := by
    convert absBound_mul hTwoBetaValid h.heightValid hTwoBetaAbs h.heightAbs
      (by norm_num) (by norm_num) using 1 ; norm_num
  have hCoeffWidthRaw := width_mul_le hTwoBetaValid
    h.heightValid hTwoBetaAbs h.heightAbs
    (by norm_num : (0 : ℚ) ≤ 2) (by norm_num : (0 : ℚ) ≤ 1)
  have hCoeffWidth : width (RatInterval.pure 2 * factorTwoPrimeBetaInterval *
      factorTwoPrimeAffineHeightInterval) ≤
      (22 : ℚ) / 10000000000000 := by
    calc
      width (RatInterval.pure 2 * factorTwoPrimeBetaInterval *
          factorTwoPrimeAffineHeightInterval) ≤
        1 * width (RatInterval.pure 2 * factorTwoPrimeBetaInterval) +
          2 * width factorTwoPrimeAffineHeightInterval := hCoeffWidthRaw
      _ ≤ 1 * (2 / 10000000000000 : ℚ) +
          2 * (1 / 1000000000000 : ℚ) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hTwoBetaWidth (by norm_num))
          (mul_le_mul_of_nonneg_left h.heightWidth (by norm_num))
      _ = (22 : ℚ) / 10000000000000 := by ring
  have hmul := width_mul_le hCoeffValid hSin.1 hCoeffAbs hSin.2.1
    (by norm_num : (0 : ℚ) ≤ 2) (by norm_num : (0 : ℚ) ≤ 2)
  calc
    width (RatInterval.pure 2 * factorTwoPrimeBetaInterval *
        factorTwoPrimeAffineHeightInterval * factorTwoPrimeSinInterval n) ≤
      2 * width (RatInterval.pure 2 * factorTwoPrimeBetaInterval *
        factorTwoPrimeAffineHeightInterval) +
      2 * width (factorTwoPrimeSinInterval n) := hmul
    _ ≤ 2 * (22 / 10000000000000 : ℚ) +
        2 * (1 / 10000000000 : ℚ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hCoeffWidth (by norm_num))
        (mul_le_mul_of_nonneg_left hSin.2.2 (by norm_num))
    _ ≤ (1 : ℚ) / 4000000000 := by norm_num

private theorem factorTwoAntisymmetricAffineSinPositiveInterval_width_le
    (n : FactorTwoCanonicalEvenIndex) (hn0 : n.1 ≠ 0) :
    width (factorTwoAntisymmetricAffineSinPositiveInterval n) ≤
      (1 : ℚ) / 1000000000 := by
  have hn : 1 ≤ n.1 := Nat.one_le_iff_ne_zero.mpr hn0
  have hnle : n.1 ≤ 200 := by omega
  have hHeadCoeff := factorTwoAffineSinHeadCoefficient_metrics
  have hInitial := factorTwoAffineSinInitialKernelInterval_metrics hn
  have hHeadMul := width_mul_le hHeadCoeff.1 hInitial.1
    hHeadCoeff.2.1 hInitial.2.1 (by norm_num) (by norm_num)
  have hHeadWidth : width
      ((factorTwoHeadDefectInterval / factorTwoPrimeLogTwoInterval) *
        factorTwoAffineSinInitialKernelInterval n.1) ≤
      (1 : ℚ) / 1000000000000 := by
    calc
      width ((factorTwoHeadDefectInterval / factorTwoPrimeLogTwoInterval) *
          factorTwoAffineSinInitialKernelInterval n.1) ≤
        1 * width
            (factorTwoHeadDefectInterval / factorTwoPrimeLogTwoInterval) +
          2 * width (factorTwoAffineSinInitialKernelInterval n.1) := hHeadMul
      _ ≤ 1 * (1 / 10000000000000 : ℚ) +
          2 * (1 / 100000000000000 : ℚ) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hHeadCoeff.2.2 (by norm_num))
          (mul_le_mul_of_nonneg_left hInitial.2.2 (by norm_num))
      _ ≤ (1 : ℚ) / 1000000000000 := by norm_num
  have hSeriesCoeff := factorTwoAffineSinSeriesCoefficient_metrics
  have hSeriesValid : (factorTwoAffineSinDyadicSeriesInterval n.1).Valid :=
    valid_of_contains (factorTwoAffineSinDyadicSeriesInterval_contains hn0)
  have hSeriesAbs := factorTwoAffineSinDyadicSeriesInterval_absBound hn hnle
  have hSeriesWidth := factorTwoAffineSinDyadicSeriesInterval_width_le hn hnle
  have hSeriesMul := width_mul_le hSeriesCoeff.1 hSeriesValid
    hSeriesCoeff.2.1 hSeriesAbs (by norm_num) (by norm_num)
  have hSeriesTermWidth : width
      ((RatInterval.pure 1 / factorTwoPrimeLogTwoInterval) *
        factorTwoAffineSinDyadicSeriesInterval n.1) ≤
      (1 : ℚ) / 2000000000 := by
    calc
      width ((RatInterval.pure 1 / factorTwoPrimeLogTwoInterval) *
          factorTwoAffineSinDyadicSeriesInterval n.1) ≤
        600 * width (RatInterval.pure 1 / factorTwoPrimeLogTwoInterval) +
          2 * width (factorTwoAffineSinDyadicSeriesInterval n.1) := hSeriesMul
      _ ≤ 600 * (3 / 100000000000000 : ℚ) +
          2 * (1 / 5000000000 : ℚ) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hSeriesCoeff.2.2 (by norm_num))
          (mul_le_mul_of_nonneg_left hSeriesWidth (by norm_num))
      _ ≤ (1 : ℚ) / 2000000000 := by norm_num
  unfold factorTwoAntisymmetricAffineSinPositiveInterval
  rw [width_add, width_add]
  calc
    width ((factorTwoHeadDefectInterval / factorTwoPrimeLogTwoInterval) *
        factorTwoAffineSinInitialKernelInterval n.1) +
      width ((RatInterval.pure 1 / factorTwoPrimeLogTwoInterval) *
        factorTwoAffineSinDyadicSeriesInterval n.1) +
      width (RatInterval.pure 2 * factorTwoPrimeBetaInterval *
        factorTwoPrimeAffineHeightInterval * factorTwoPrimeSinInterval n) ≤
      (1 / 1000000000000 : ℚ) + 1 / 2000000000 + 1 / 4000000000 :=
        add_le_add
          (add_le_add hHeadWidth hSeriesTermWidth)
          (factorTwoAffineSinPrimeTerm_width_le n)
    _ ≤ (1 : ℚ) / 1000000000 := by norm_num

theorem factorTwoAntisymmetricAffineSinMomentIntervals_width_le :
    ∀ n : FactorTwoCanonicalEvenIndex,
      width (factorTwoAntisymmetricAffineSinMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  intro n
  by_cases hn : n.1 = 0
  · simp [factorTwoAntisymmetricAffineSinMomentInterval, hn, width_pure]
  · simpa [factorTwoAntisymmetricAffineSinMomentInterval, hn] using
      factorTwoAntisymmetricAffineSinPositiveInterval_width_le n hn

theorem factorTwoAntisymmetricAffineSinMomentInterval_width_le
    (n : FactorTwoCanonicalEvenIndex) :
    width (factorTwoAntisymmetricAffineSinMomentInterval n) ≤
      (1 / 1000000000 : ℚ) :=
  factorTwoAntisymmetricAffineSinMomentIntervals_width_le n

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineSinEnclosures
