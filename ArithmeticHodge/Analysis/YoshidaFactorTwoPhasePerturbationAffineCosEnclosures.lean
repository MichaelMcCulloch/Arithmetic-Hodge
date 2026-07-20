import ArithmeticHodge.Analysis.RationalIntervalWidth
import ArithmeticHodge.Analysis.YoshidaDiagonalUniformDerivativeBound
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineCosSeries
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationConstantEnclosures
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option maxRecDepth 100000

open Filter MeasureTheory Real Set intervalIntegral
open scoped BigOperators Topology

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineCosEnclosures

noncomputable section

open ArithmeticHodge.Analysis
open CorrectedTrapezoidRemainder
open DigammaTrapezoid
open RatInterval
open YoshidaDiagonalDigammaHighBound
open YoshidaDiagonalUniformDerivativeBound
open YoshidaDiagonalUniformIdentity
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcretePerturbationMoments
open YoshidaFactorTwoPhasePerturbationAffineCosSeries
open YoshidaFactorTwoPhasePerturbationConstantEnclosures
open YoshidaFactorTwoPhasePerturbationMomentSeries
open YoshidaFactorTwoPrimeTrigEnclosures
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures

/-!
# Exact enclosures for the factor-two affine cosine perturbation

The signed derivative-Cauchy series is split into its unweighted derivative
kernel and an exponentially small dyadic correction.  A shifted corrected
trapezoid formula encloses the former with a fourth-order tail radius; the
latter is handled by a short exact head and a geometric absolute tail.
-/

/-! ## A shifted corrected-trapezoid enclosure -/

/-- Corrected Euler--Maclaurin main term for the derivative tail beginning
with `diagonalHighProfileDeriv y (N + 1)`. -/
def factorTwoAffineCosDerivativeTailMain (y : ℝ) (N : ℕ) : ℝ :=
  -diagonalHighProfile y (N + 1) +
    diagonalHighProfileDeriv y (N + 1) / 2 -
    diagonalHighProfileSecondDeriv y (N + 1) / 12

/-- Exact analytic radius for the shifted derivative tail. -/
def factorTwoAffineCosDerivativeTailRadius (y : ℝ) (N : ℕ) : ℝ :=
  5 / (2 * ((((N : ℝ) + 1 + 1 / 4) ^ 2 + y ^ 2) ^ 2))

private def affineCosDerivativeCorrectedError
    (y : ℝ) (N k : ℕ) : ℝ :=
  trapezoidal_error (diagonalHighProfileDeriv y) 1
      ((N + k : ℕ) + 1) ((N + k : ℕ) + 2) -
    (diagonalHighProfileSecondDeriv y ((N + k : ℕ) + 2) -
      diagonalHighProfileSecondDeriv y ((N + k : ℕ) + 1)) / 12

private def affineCosFourthMajorant (y t : ℝ) : ℝ :=
  10 * (t + 1 / 4) / (((t + 1 / 4) ^ 2 + y ^ 2) ^ 3)

private def affineCosFourthMajorantPrimitive (y t : ℝ) : ℝ :=
  (-5 : ℝ) / (2 * (((t + 1 / 4) ^ 2 + y ^ 2) ^ 2))

private theorem hasDerivAt_diagonalHighProfile_local
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (diagonalHighProfile y)
      (diagonalHighProfileDeriv y t) t := by
  have hu : HasDerivAt (fun s : ℝ ↦ s + 1 / 4) 1 t := by
    simpa using (hasDerivAt_id t).add_const (1 / 4)
  have h := (hasDerivAt_reciprocalRealPart
    (y := y) (u := t + 1 / 4) hy).comp t hu
  change HasDerivAt
    (reciprocalRealPart y ∘ fun s : ℝ ↦ s + 1 / 4)
    (reciprocalRealPartDeriv y (t + 1 / 4)) t
  simpa only [mul_one] using h

private theorem continuous_diagonalHighProfileFourthDeriv_local
    {y : ℝ} (hy : y ≠ 0) :
    Continuous (diagonalHighProfileFourthDeriv y) := by
  unfold diagonalHighProfileFourthDeriv
  dsimp only
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    have hden : 0 < (t + 1 / 4) ^ 2 + y ^ 2 := by positivity
    exact (pow_pos hden 5).ne'

private theorem affineCos_one_div_twelve_mul_abs_fourth_le_majorant
    {y t : ℝ} (hy : 0 < y) (ht : 0 ≤ t) :
    (1 / 12 : ℝ) * |diagonalHighProfileFourthDeriv y t| ≤
      affineCosFourthMajorant y t := by
  let u : ℝ := t + 1 / 4
  let D : ℝ := u ^ 2 + y ^ 2
  let Q : ℝ := u ^ 4 - 10 * u ^ 2 * y ^ 2 + 5 * y ^ 4
  have hu : 0 < u := by dsimp [u]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hQ : |Q| ≤ 5 * D ^ 2 := by
    have hraw : |Q| ≤
        u ^ 4 + 10 * u ^ 2 * y ^ 2 + 5 * y ^ 4 := by
      rw [abs_le]
      constructor <;> dsimp [Q] <;>
        nlinarith [sq_nonneg (u ^ 2), sq_nonneg (y ^ 2),
          mul_nonneg (sq_nonneg u) (sq_nonneg y)]
    have hexpand :
        5 * D ^ 2 =
          5 * u ^ 4 + 10 * u ^ 2 * y ^ 2 + 5 * y ^ 4 := by
      dsimp [D]
      ring_nf
    rw [hexpand]
    nlinarith [hraw, pow_nonneg hu.le 4]
  unfold diagonalHighProfileFourthDeriv affineCosFourthMajorant
  dsimp only
  change (1 / 12 : ℝ) * |24 * u * Q / D ^ 5| ≤ 10 * u / D ^ 3
  rw [abs_div, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24), abs_of_pos hu,
    abs_of_pos (pow_pos hD 5)]
  calc
    (1 / 12 : ℝ) * (24 * u * |Q| / D ^ 5) ≤
        (1 / 12 : ℝ) * (24 * u * (5 * D ^ 2) / D ^ 5) := by
      gcongr
    _ = 10 * u / D ^ 3 := by
      field_simp [hD.ne']
      ring_nf

private theorem hasDerivAt_affineCosFourthMajorantPrimitive
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (affineCosFourthMajorantPrimitive y)
      (affineCosFourthMajorant y t) t := by
  let u : ℝ → ℝ := fun s ↦ s + 1 / 4
  let D : ℝ → ℝ := fun s ↦ u s ^ 2 + y ^ 2
  have hu : HasDerivAt u 1 t := by
    simpa [u] using (hasDerivAt_id t).add_const (1 / 4)
  have hD : HasDerivAt D (2 * u t) t := by
    dsimp only [D]
    convert (hu.pow 2).add_const (y ^ 2) using 1
    all_goals ring_nf
  have hden : 2 * (D t) ^ 2 ≠ 0 := by
    have hDpos : 0 < D t := by dsimp [D, u]; positivity
    positivity
  have hDne : (t + 1 / 4) ^ 2 + y ^ 2 ≠ 0 := by positivity
  have hdenDeriv : HasDerivAt (fun s ↦ 2 * (D s) ^ 2)
      (8 * u t * D t) t := by
    convert (hD.pow 2).const_mul 2 using 1
    all_goals ring_nf
  unfold affineCosFourthMajorantPrimitive affineCosFourthMajorant
  dsimp only [u, D] at hden hdenDeriv ⊢
  convert (hasDerivAt_const t (-5 : ℝ)).div hdenDeriv hden using 1
  field_simp [hDne]
  ring_nf

private theorem integral_affineCosFourthMajorant
    {y a b : ℝ} (hy : y ≠ 0) (hab : a ≤ b) :
    (∫ t in a..b, affineCosFourthMajorant y t) =
      affineCosFourthMajorantPrimitive y b -
        affineCosFourthMajorantPrimitive y a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _ht
    exact hasDerivAt_affineCosFourthMajorantPrimitive hy
  · have hcont : Continuous (affineCosFourthMajorant y) := by
      unfold affineCosFourthMajorant
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro t
        have hden : 0 < (t + 1 / 4) ^ 2 + y ^ 2 := by positivity
        exact (pow_pos hden 3).ne'
    exact hcont.continuousOn.intervalIntegrable_of_Icc hab

private theorem affineCosDerivativeCorrectedError_abs_le
    {y : ℝ} (hy : 0 < y) (N k : ℕ) :
    |affineCosDerivativeCorrectedError y N k| ≤
      ∫ t in ((N + k : ℕ) + 1)..((N + k : ℕ) + 2),
        affineCosFourthMajorant y t := by
  let a : ℝ := ((N + k : ℕ) : ℝ) + 1
  have hfourInt : IntervalIntegrable (diagonalHighProfileFourthDeriv y)
      volume a (a + 1) :=
    (continuous_diagonalHighProfileFourthDeriv_local hy.ne').intervalIntegrable _ _
  have hid := trapezoidal_error_one_sub_first_eq_integral_third
    (f := diagonalHighProfileDeriv y)
    (f1 := diagonalHighProfileSecondDeriv y)
    (f2 := diagonalHighProfileThirdDeriv y)
    (f3 := diagonalHighProfileFourthDeriv y)
    (a := a)
    (fun t ↦ hasDerivAt_diagonalHighProfileDeriv hy.ne')
    (fun t ↦ hasDerivAt_diagonalHighProfileSecondDeriv hy.ne')
    (fun t ↦ hasDerivAt_diagonalHighProfileThirdDeriv hy.ne')
    hfourInt
  have hid' : affineCosDerivativeCorrectedError y N k =
      -(∫ t in a..a + 1,
        correctedTrapezoidThirdKernel a t *
          diagonalHighProfileFourthDeriv y t) := by
    unfold affineCosDerivativeCorrectedError
    dsimp only [a] at hid ⊢
    norm_num only [Nat.cast_add, Nat.cast_one] at hid ⊢
    convert hid using 1
    all_goals ring_nf
  rw [hid', abs_neg]
  have hkernel : Continuous (correctedTrapezoidThirdKernel a) := by
    unfold correctedTrapezoidThirdKernel
    fun_prop
  have hleftInt : IntervalIntegrable
      (fun t : ℝ ↦
        |correctedTrapezoidThirdKernel a t *
          diagonalHighProfileFourthDeriv y t|)
      volume a (a + 1) :=
    (hkernel.mul
      (continuous_diagonalHighProfileFourthDeriv_local hy.ne')).abs.intervalIntegrable _ _
  have hmajorantInt : IntervalIntegrable (affineCosFourthMajorant y)
      volume a (a + 1) := by
    have hcont : Continuous (affineCosFourthMajorant y) := by
      unfold affineCosFourthMajorant
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro t
        have hden : 0 < (t + 1 / 4) ^ 2 + y ^ 2 := by positivity
        exact (pow_pos hden 3).ne'
    exact hcont.intervalIntegrable _ _
  calc
    |∫ t in a..a + 1,
        correctedTrapezoidThirdKernel a t *
          diagonalHighProfileFourthDeriv y t| ≤
        ∫ t in a..a + 1,
          |correctedTrapezoidThirdKernel a t *
            diagonalHighProfileFourthDeriv y t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in a..a + 1, affineCosFourthMajorant y t := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        hleftInt hmajorantInt
      intro t ht
      rw [abs_mul]
      calc
        |correctedTrapezoidThirdKernel a t| *
            |diagonalHighProfileFourthDeriv y t| ≤
            (1 / 12 : ℝ) * |diagonalHighProfileFourthDeriv y t| :=
          mul_le_mul_of_nonneg_right
            (abs_correctedTrapezoidThirdKernel_le ht) (abs_nonneg _)
        _ ≤ affineCosFourthMajorant y t :=
          affineCos_one_div_twelve_mul_abs_fourth_le_majorant hy (by
            dsimp only [a] at ht
            linarith [ht.1])
    _ = ∫ t in ((N + k : ℕ) + 1)..((N + k : ℕ) + 2),
        affineCosFourthMajorant y t := by
      dsimp only [a]
      norm_num only [Nat.cast_add, Nat.cast_one]
      congr 1
      all_goals ring_nf

private theorem affineCosDerivativeCorrectedError_sum_abs_le
    {y : ℝ} (hy : 0 < y) (N M : ℕ) :
    |∑ k ∈ Finset.range M, affineCosDerivativeCorrectedError y N k| ≤
      factorTwoAffineCosDerivativeTailRadius y N := by
  calc
    |∑ k ∈ Finset.range M, affineCosDerivativeCorrectedError y N k| ≤
        ∑ k ∈ Finset.range M,
          |affineCosDerivativeCorrectedError y N k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range M,
        ∫ t in ((N + k : ℕ) + 1)..((N + k : ℕ) + 2),
          affineCosFourthMajorant y t := by
      exact Finset.sum_le_sum fun k _hk ↦
        affineCosDerivativeCorrectedError_abs_le hy N k
    _ = ∑ k ∈ Finset.range M,
        (affineCosFourthMajorantPrimitive y ((N + k : ℕ) + 2) -
          affineCosFourthMajorantPrimitive y ((N + k : ℕ) + 1)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact integral_affineCosFourthMajorant hy.ne' (by norm_num)
    _ = affineCosFourthMajorantPrimitive y ((N + M : ℕ) + 1) -
        affineCosFourthMajorantPrimitive y (N + 1) := by
      convert (Finset.sum_range_sub
        (fun k : ℕ ↦
          affineCosFourthMajorantPrimitive y ((N + k : ℕ) + 1)) M) using 1
      all_goals norm_num
      all_goals ring_nf
    _ ≤ factorTwoAffineCosDerivativeTailRadius y N := by
      have hnonpos :
          affineCosFourthMajorantPrimitive y ((N + M : ℕ) + 1) ≤ 0 := by
        unfold affineCosFourthMajorantPrimitive
        exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
      calc
        affineCosFourthMajorantPrimitive y ((N + M : ℕ) + 1) -
            affineCosFourthMajorantPrimitive y (N + 1) ≤
            0 - affineCosFourthMajorantPrimitive y (N + 1) :=
          sub_le_sub_right hnonpos _
        _ = factorTwoAffineCosDerivativeTailRadius y N := by
          unfold affineCosFourthMajorantPrimitive
            factorTwoAffineCosDerivativeTailRadius
          norm_num only [Nat.cast_add, Nat.cast_one]
          ring_nf

private theorem diagonalHighProfileSecondDeriv_abs_le_local
    (y : ℝ) (j : ℕ) :
    |diagonalHighProfileSecondDeriv y (j + 1)| ≤
      6 / (((j : ℝ) + 1) ^ 3) := by
  let k : ℝ := (j : ℝ) + 1
  let u : ℝ := k + 1 / 4
  let D : ℝ := u ^ 2 + y ^ 2
  have hk : 0 < k := by dsimp [k]; positivity
  have hu : 0 < u := by dsimp [u]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hpoly : |u ^ 2 - 3 * y ^ 2| ≤ 3 * D := by
    rw [abs_le]
    constructor <;> dsimp [D] <;> nlinarith [sq_nonneg u, sq_nonneg y]
  have huD : u ^ 2 ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg y]
  have hDsqRaw := pow_le_pow_left₀ (sq_nonneg u) huD 2
  have hDsq : u ^ 4 ≤ D ^ 2 := by nlinarith [hDsqRaw]
  have hku : k ≤ u := by dsimp [u]; norm_num
  unfold diagonalHighProfileSecondDeriv
  dsimp only
  change |2 * u * (u ^ 2 - 3 * y ^ 2) / D ^ 3| ≤ 6 / k ^ 3
  rw [abs_div, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hu,
    abs_of_pos (pow_pos hD 3)]
  calc
    2 * u * |u ^ 2 - 3 * y ^ 2| / D ^ 3 ≤
        2 * u * (3 * D) / D ^ 3 := by gcongr
    _ = 6 * u / D ^ 2 := by
      field_simp [hD.ne']
      ring_nf
    _ ≤ 6 / u ^ 3 := by
      rw [div_le_div_iff₀ (pow_pos hD 2) (pow_pos hu 3)]
      nlinarith [hDsq]
    _ ≤ 6 / k ^ 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (pow_pos hk 3)
      exact pow_le_pow_left₀ hk.le hku 3

private theorem summable_affineCosDerivativeTail (y : ℝ) (N : ℕ) :
    Summable (fun j : ℕ ↦
      diagonalHighProfileDeriv y (N + j + 1)) := by
  have hmajor : Summable (fun j : ℕ ↦
      1 / ((((j + 1 : ℕ) : ℝ) ^ 2))) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 h
  have hall : Summable (fun j : ℕ ↦
      diagonalHighProfileDeriv y (j + 1)) := by
    apply hmajor.of_norm_bounded
    intro j
    rw [Real.norm_eq_abs]
    exact diagonalHighProfileDeriv_abs_le y j
  have hshift := (summable_nat_add_iff N).2 hall
  apply hshift.congr
  intro j
  norm_num only [Nat.cast_add, Nat.cast_one]
  congr 1
  ring

private theorem summable_affineCosSecondDerivativeTail (y : ℝ) (N : ℕ) :
    Summable (fun j : ℕ ↦
      diagonalHighProfileSecondDeriv y (N + j + 1)) := by
  have hbase : Summable (fun j : ℕ ↦
      1 / ((((j + 1 : ℕ) : ℝ) ^ 3))) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 h
  have hmajor : Summable (fun j : ℕ ↦
      6 / ((((j + 1 : ℕ) : ℝ) ^ 3))) := by
    simpa [div_eq_mul_inv] using hbase.mul_left (6 : ℝ)
  have hall : Summable (fun j : ℕ ↦
      diagonalHighProfileSecondDeriv y (j + 1)) := by
    apply hmajor.of_norm_bounded
    intro j
    rw [Real.norm_eq_abs]
    simpa only [Nat.cast_add, Nat.cast_one] using
      diagonalHighProfileSecondDeriv_abs_le_local y j
  have hshift := (summable_nat_add_iff N).2 hall
  apply hshift.congr
  intro j
  norm_num only [Nat.cast_add, Nat.cast_one]
  congr 1
  ring

private theorem tendsto_affineCosProfileTail (y : ℝ) (N : ℕ) :
    Tendsto (fun M : ℕ ↦ diagonalHighProfile y (N + M + 1))
      atTop (nhds 0) := by
  have hbase := tendsto_shiftedReciprocalRealPart_nat (1 / 4) y
  have hprofile : Tendsto (fun M : ℕ ↦ diagonalHighProfile y M)
      atTop (nhds 0) := by
    simpa [diagonalHighProfile, shiftedReciprocalRealPart, add_comm] using hbase
  convert hprofile.comp (tendsto_add_atTop_nat (N + 1)) using 1
  funext M
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  ring_nf

private theorem sum_range_affineCosDerivativeCorrectedError_eq
    {y : ℝ} (hy : y ≠ 0) (N M : ℕ) :
    (∑ k ∈ Finset.range M, affineCosDerivativeCorrectedError y N k) =
      (∑ k ∈ Finset.range M,
          diagonalHighProfileDeriv y (N + k + 1)) -
        diagonalHighProfileDeriv y (N + 1) / 2 +
        diagonalHighProfileDeriv y (N + M + 1) / 2 -
        (diagonalHighProfile y (N + M + 1) -
          diagonalHighProfile y (N + 1)) -
        (diagonalHighProfileSecondDeriv y (N + M + 1) -
          diagonalHighProfileSecondDeriv y (N + 1)) / 12 := by
  have hcont : Continuous (diagonalHighProfileDeriv y) :=
    continuous_iff_continuousAt.mpr fun t ↦
      (hasDerivAt_diagonalHighProfileDeriv (y := y) (t := t) hy).continuousAt
  have hcell (k : ℕ) :
      trapezoidal_error (diagonalHighProfileDeriv y) 1
          ((N + k : ℕ) + 1) ((N + k : ℕ) + 2) =
        (diagonalHighProfileDeriv y ((N + k : ℕ) + 1) +
            diagonalHighProfileDeriv y ((N + k : ℕ) + 2)) / 2 -
          (diagonalHighProfile y ((N + k : ℕ) + 2) -
            diagonalHighProfile y ((N + k : ℕ) + 1)) := by
    have hint :
        (∫ t in ((N + k : ℕ) + 1)..((N + k : ℕ) + 2),
          diagonalHighProfileDeriv y t) =
            diagonalHighProfile y ((N + k : ℕ) + 2) -
              diagonalHighProfile y ((N + k : ℕ) + 1) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t _ht
        exact hasDerivAt_diagonalHighProfile_local hy
      · exact hcont.intervalIntegrable _ _
    rw [trapezoidal_error, trapezoidal_integral_one, hint]
    ring_nf
  have hshift :
      (∑ k ∈ Finset.range M,
        diagonalHighProfileDeriv y ((N + k : ℕ) + 2)) =
        (∑ k ∈ Finset.range M,
          diagonalHighProfileDeriv y ((N + k : ℕ) + 1)) -
          diagonalHighProfileDeriv y (N + 1) +
          diagonalHighProfileDeriv y (N + M + 1) := by
    calc
      (∑ k ∈ Finset.range M,
          diagonalHighProfileDeriv y ((N + k : ℕ) + 2)) =
          (∑ k ∈ Finset.range (M + 1),
            diagonalHighProfileDeriv y ((N + k : ℕ) + 1)) -
            diagonalHighProfileDeriv y (N + 1) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_add, Nat.cast_one]
        ring_nf
      _ = (∑ k ∈ Finset.range M,
            diagonalHighProfileDeriv y ((N + k : ℕ) + 1)) -
            diagonalHighProfileDeriv y (N + 1) +
            diagonalHighProfileDeriv y (N + M + 1) := by
        rw [Finset.sum_range_succ]
        norm_num only [Nat.cast_add, Nat.cast_one]
        ring_nf
  have havg :
      (∑ k ∈ Finset.range M,
        (diagonalHighProfileDeriv y ((N + k : ℕ) + 1) +
          diagonalHighProfileDeriv y ((N + k : ℕ) + 2)) / 2) =
        (∑ k ∈ Finset.range M,
          diagonalHighProfileDeriv y ((N + k : ℕ) + 1)) -
          diagonalHighProfileDeriv y (N + 1) / 2 +
          diagonalHighProfileDeriv y (N + M + 1) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hshift]
    ring_nf
  have htelProfile :
      (∑ k ∈ Finset.range M,
        (diagonalHighProfile y ((N + k : ℕ) + 2) -
          diagonalHighProfile y ((N + k : ℕ) + 1))) =
        diagonalHighProfile y (N + M + 1) -
          diagonalHighProfile y (N + 1) := by
    convert (Finset.sum_range_sub
      (fun k : ℕ ↦ diagonalHighProfile y ((N + k : ℕ) + 1)) M) using 1
    all_goals norm_num
    all_goals ring_nf
  have htrap :
      (∑ k ∈ Finset.range M,
        trapezoidal_error (diagonalHighProfileDeriv y) 1
          ((N + k : ℕ) + 1) ((N + k : ℕ) + 2)) =
        (∑ k ∈ Finset.range M,
          diagonalHighProfileDeriv y (N + k + 1)) -
          diagonalHighProfileDeriv y (N + 1) / 2 +
          diagonalHighProfileDeriv y (N + M + 1) / 2 -
          (diagonalHighProfile y (N + M + 1) -
            diagonalHighProfile y (N + 1)) := by
    calc
      (∑ k ∈ Finset.range M,
          trapezoidal_error (diagonalHighProfileDeriv y) 1
            ((N + k : ℕ) + 1) ((N + k : ℕ) + 2)) =
          ∑ k ∈ Finset.range M,
            ((diagonalHighProfileDeriv y ((N + k : ℕ) + 1) +
                diagonalHighProfileDeriv y ((N + k : ℕ) + 2)) / 2 -
              (diagonalHighProfile y ((N + k : ℕ) + 2) -
                diagonalHighProfile y ((N + k : ℕ) + 1))) := by
        apply Finset.sum_congr rfl
        intro k _hk
        exact hcell k
      _ = (∑ k ∈ Finset.range M,
            (diagonalHighProfileDeriv y ((N + k : ℕ) + 1) +
              diagonalHighProfileDeriv y ((N + k : ℕ) + 2)) / 2) -
            ∑ k ∈ Finset.range M,
              (diagonalHighProfile y ((N + k : ℕ) + 2) -
                diagonalHighProfile y ((N + k : ℕ) + 1)) := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by
        rw [havg, htelProfile]
        norm_num only [Nat.cast_add, Nat.cast_one]
  have htelSecond :
      (∑ k ∈ Finset.range M,
        (diagonalHighProfileSecondDeriv y ((N + k : ℕ) + 2) -
          diagonalHighProfileSecondDeriv y ((N + k : ℕ) + 1))) =
        diagonalHighProfileSecondDeriv y (N + M + 1) -
          diagonalHighProfileSecondDeriv y (N + 1) := by
    convert (Finset.sum_range_sub
      (fun k : ℕ ↦
        diagonalHighProfileSecondDeriv y ((N + k : ℕ) + 1)) M) using 1
    all_goals norm_num
    all_goals ring_nf
  unfold affineCosDerivativeCorrectedError
  rw [Finset.sum_sub_distrib, htrap, ← Finset.sum_div, htelSecond]

private theorem tendsto_sum_affineCosDerivativeCorrectedError
    {y : ℝ} (hy : 0 < y) (N : ℕ) :
    Tendsto
      (fun M : ℕ ↦
        ∑ k ∈ Finset.range M, affineCosDerivativeCorrectedError y N k)
      atTop
      (nhds ((∑' j : ℕ, diagonalHighProfileDeriv y (N + j + 1)) -
        factorTwoAffineCosDerivativeTailMain y N)) := by
  have hsum := (summable_affineCosDerivativeTail y N).hasSum.tendsto_sum_nat
  have hderiv := (summable_affineCosDerivativeTail y N).tendsto_atTop_zero
  have hsecond :=
    (summable_affineCosSecondDerivativeTail y N).tendsto_atTop_zero
  have hprofile := tendsto_affineCosProfileTail y N
  have hderivStart : Tendsto
      (fun _ : ℕ ↦ diagonalHighProfileDeriv y (N + 1)) atTop
      (nhds (diagonalHighProfileDeriv y (N + 1))) := tendsto_const_nhds
  have hprofileStart : Tendsto
      (fun _ : ℕ ↦ diagonalHighProfile y (N + 1)) atTop
      (nhds (diagonalHighProfile y (N + 1))) := tendsto_const_nhds
  have hsecondStart : Tendsto
      (fun _ : ℕ ↦ diagonalHighProfileSecondDeriv y (N + 1)) atTop
      (nhds (diagonalHighProfileSecondDeriv y (N + 1))) := tendsto_const_nhds
  have hlim := ((((hsum.sub (hderivStart.div_const 2)).add
      (hderiv.div_const 2)).sub (hprofile.sub hprofileStart)).sub
      ((hsecond.sub hsecondStart).div_const 12))
  convert hlim using 1
  · funext M
    rw [sum_range_affineCosDerivativeCorrectedError_eq hy.ne' N M]
  · unfold factorTwoAffineCosDerivativeTailMain
    ring_nf

/-- Shifted derivative-series enclosure.  This is the reusable accelerated
tail certificate used below. -/
theorem factorTwoAffineCosDerivativeTail_sub_main_abs_le
    {y : ℝ} (hy : 0 < y) (N : ℕ) :
    |(∑' j : ℕ, diagonalHighProfileDeriv y (N + j + 1)) -
        factorTwoAffineCosDerivativeTailMain y N| ≤
      factorTwoAffineCosDerivativeTailRadius y N := by
  have hlim := tendsto_sum_affineCosDerivativeCorrectedError hy N
  exact le_of_tendsto' hlim.abs fun M ↦
    affineCosDerivativeCorrectedError_sum_abs_le hy N M

/-! ## Zero-mode reciprocal-square tail -/

def factorTwoAffineCosInvSqTailTerm (x : ℝ) (j : ℕ) : ℝ :=
  1 / (x + j) ^ 2

def factorTwoAffineCosInvSqTailLowerPotential (x : ℝ) : ℝ :=
  x⁻¹ + (x⁻¹) ^ 2 / 2 + (x⁻¹) ^ 3 / 6 - (x⁻¹) ^ 5 / 30

def factorTwoAffineCosInvSqTailUpperPotential (x : ℝ) : ℝ :=
  x⁻¹ + (x⁻¹) ^ 2 / 2 + (x⁻¹) ^ 3 / 6

private theorem affineCosInvSq_lowerPotential_sub_succ_le
    {x : ℝ} (hx : 1 ≤ x) :
    factorTwoAffineCosInvSqTailLowerPotential x -
        factorTwoAffineCosInvSqTailLowerPotential (x + 1) ≤
      1 / x ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx1 : 0 < x + 1 := by positivity
  unfold factorTwoAffineCosInvSqTailLowerPotential
  field_simp [hx0.ne', hx1.ne']
  nlinarith [sq_nonneg x, sq_nonneg (x + 1)]

private theorem affineCosInvSq_le_upperPotential_sub_succ
    {x : ℝ} (hx : 1 ≤ x) :
    1 / x ^ 2 ≤
      factorTwoAffineCosInvSqTailUpperPotential x -
        factorTwoAffineCosInvSqTailUpperPotential (x + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx1 : 0 < x + 1 := by positivity
  unfold factorTwoAffineCosInvSqTailUpperPotential
  field_simp [hx0.ne', hx1.ne']
  nlinarith [sq_nonneg x, sq_nonneg (x + 1)]

private theorem summable_affineCosInvSqTailTerm
    {x : ℝ} (hx : 1 ≤ x) :
    Summable (factorTwoAffineCosInvSqTailTerm x) := by
  have hs := (Real.summable_one_div_nat_add_rpow x (2 : ℝ)).2 (by norm_num)
  apply hs.congr
  intro j
  rw [factorTwoAffineCosInvSqTailTerm,
    abs_of_pos (by positivity : 0 < (j : ℝ) + x), Real.rpow_two]
  congr 2
  ring

private theorem tendsto_affineCosInvSqTailPotential
    (x : ℝ) (lower : Bool) :
    Tendsto
      (fun j : ℕ ↦ if lower then
        factorTwoAffineCosInvSqTailLowerPotential (x + j)
      else factorTwoAffineCosInvSqTailUpperPotential (x + j))
      atTop (nhds 0) := by
  have htop : Tendsto (fun j : ℕ ↦ x + (j : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv : Tendsto (fun j : ℕ ↦ (x + (j : ℝ))⁻¹)
      atTop (nhds 0) := by
    simpa only [one_div] using htop.const_div_atTop 1
  cases lower
  · simp only [Bool.false_eq_true, if_false,
      factorTwoAffineCosInvSqTailUpperPotential]
    simpa using (hinv.add ((hinv.pow 2).div_const 2)).add
      ((hinv.pow 3).div_const 6)
  · simp only [if_true, factorTwoAffineCosInvSqTailLowerPotential]
    simpa using (((hinv.add ((hinv.pow 2).div_const 2)).add
      ((hinv.pow 3).div_const 6)).sub ((hinv.pow 5).div_const 30))

private theorem affineCos_tsum_bounds_of_telescope
    {f lower upper : ℕ → ℝ}
    (hs : Summable f)
    (hlower : ∀ k, lower k - lower (k + 1) ≤ f k)
    (hupper : ∀ k, f k ≤ upper k - upper (k + 1))
    (hlowerLim : Tendsto lower atTop (nhds 0))
    (hupperLim : Tendsto upper atTop (nhds 0)) :
    lower 0 ≤ ∑' k, f k ∧ (∑' k, f k) ≤ upper 0 := by
  have hpartialLower (N : ℕ) :
      lower 0 - lower N ≤ ∑ k ∈ Finset.range N, f k := by
    rw [← Finset.sum_range_sub' lower]
    exact Finset.sum_le_sum fun k _ ↦ hlower k
  have hpartialUpper (N : ℕ) :
      (∑ k ∈ Finset.range N, f k) ≤ upper 0 - upper N := by
    rw [← Finset.sum_range_sub' upper]
    exact Finset.sum_le_sum fun k _ ↦ hupper k
  have hpartial := hs.hasSum.tendsto_sum_nat
  have hlowerLimit : Tendsto (fun N ↦ lower 0 - lower N)
      atTop (nhds (lower 0)) := by
    simpa using tendsto_const_nhds.sub hlowerLim
  have hupperLimit : Tendsto (fun N ↦ upper 0 - upper N)
      atTop (nhds (upper 0)) := by
    simpa using tendsto_const_nhds.sub hupperLim
  exact ⟨le_of_tendsto_of_tendsto hlowerLimit hpartial
      (Filter.Eventually.of_forall hpartialLower),
    le_of_tendsto_of_tendsto hpartial hupperLimit
      (Filter.Eventually.of_forall hpartialUpper)⟩

/-- Fifth-order rational enclosure of the zero-mode inverse-square tail. -/
theorem factorTwoAffineCosInvSqTail_tsum_bounds
    {x : ℝ} (hx : 1 ≤ x) :
    factorTwoAffineCosInvSqTailLowerPotential x ≤
        ∑' j : ℕ, factorTwoAffineCosInvSqTailTerm x j ∧
      (∑' j : ℕ, factorTwoAffineCosInvSqTailTerm x j) ≤
        factorTwoAffineCosInvSqTailUpperPotential x := by
  simpa using affineCos_tsum_bounds_of_telescope
    (summable_affineCosInvSqTailTerm hx)
    (fun j ↦ by
      simpa only [factorTwoAffineCosInvSqTailTerm, Nat.cast_add,
        Nat.cast_one, Nat.cast_zero, add_zero, add_assoc] using
        affineCosInvSq_lowerPotential_sub_succ_le
          (show 1 ≤ x + (j : ℝ) by
            exact hx.trans (le_add_of_nonneg_right (Nat.cast_nonneg j))))
    (fun j ↦ by
      simpa only [factorTwoAffineCosInvSqTailTerm, Nat.cast_add,
        Nat.cast_one, Nat.cast_zero, add_zero, add_assoc] using
        affineCosInvSq_le_upperPotential_sub_succ
          (show 1 ≤ x + (j : ℝ) by
            exact hx.trans (le_add_of_nonneg_right (Nat.cast_nonneg j))))
    (tendsto_affineCosInvSqTailPotential x true)
    (tendsto_affineCosInvSqTailPotential x false)

/-! ## Exact main/correction split -/

def factorTwoAffineCosUnweightedKernel (n m : ℕ) : ℝ :=
  factorTwoCauchyT (factorTwoCauchyX (m + 1)) (factorTwoMomentY n)

def factorTwoAffineCosDyadicCorrection (n m : ℕ) : ℝ :=
  (factorTwoDyadicD (m + 1) - 1) *
    factorTwoAffineCosUnweightedKernel n m

theorem factorTwoMomentY_eq_diagonalY (n : ℕ) :
    factorTwoMomentY n = YoshidaDiagonalUniformIdentity.yoshidaY n := by
  unfold factorTwoMomentY YoshidaDiagonalUniformIdentity.yoshidaY
    factorTwoNaturalFrequency yoshidaKappa
  rw [factorTwoMomentLength_eq_yoshidaLength]
  ring

theorem factorTwoAffineCosUnweightedKernel_eq_neg_derivative
    (n m : ℕ) :
    factorTwoAffineCosUnweightedKernel n m =
      -diagonalHighProfileDeriv
        (YoshidaDiagonalUniformIdentity.yoshidaY n) (m + 1) := by
  rw [← factorTwoMomentY_eq_diagonalY]
  unfold factorTwoAffineCosUnweightedKernel factorTwoCauchyT
    factorTwoCauchyX diagonalHighProfileDeriv reciprocalRealPartDeriv
  push_cast
  ring

theorem summable_factorTwoAffineCosUnweightedKernel (n : ℕ) :
    Summable (factorTwoAffineCosUnweightedKernel n) := by
  have h := (summable_diagonalHighDerivativeTerm n).neg
  apply h.congr
  intro m
  rw [factorTwoAffineCosUnweightedKernel_eq_neg_derivative]
  rfl

theorem factorTwoSymmetricAffineCosDyadicKernel_eq_main_add_correction
    (n m : ℕ) :
    factorTwoSymmetricAffineCosDyadicKernel n (m + 1) =
      factorTwoAffineCosUnweightedKernel n m +
        factorTwoAffineCosDyadicCorrection n m := by
  change factorTwoDyadicD (m + 1) *
      factorTwoAffineCosUnweightedKernel n m =
    factorTwoAffineCosUnweightedKernel n m +
      (factorTwoDyadicD (m + 1) - 1) *
        factorTwoAffineCosUnweightedKernel n m
  ring

theorem summable_factorTwoAffineCosDyadicCorrection (n : ℕ) :
    Summable (factorTwoAffineCosDyadicCorrection n) := by
  have hkernel : Summable
      (fun m : ℕ ↦ factorTwoSymmetricAffineCosDyadicKernel n (m + 1)) :=
    Summable.of_norm (summable_norm_factorTwoSymmetricAffineCosDyadicKernel n)
  have hmain := summable_factorTwoAffineCosUnweightedKernel n
  apply hkernel.sub hmain |>.congr
  intro m
  rw [factorTwoSymmetricAffineCosDyadicKernel_eq_main_add_correction]
  ring

/-- Exact accelerated split of the signed dyadic kernel series. -/
theorem factorTwoSymmetricAffineCosDyadic_tsum_eq_main_add_correction
    (n : ℕ) :
    (∑' m : ℕ, factorTwoSymmetricAffineCosDyadicKernel n (m + 1)) =
      (∑' m : ℕ, factorTwoAffineCosUnweightedKernel n m) +
        ∑' m : ℕ, factorTwoAffineCosDyadicCorrection n m := by
  rw [← (summable_factorTwoAffineCosUnweightedKernel n).tsum_add
    (summable_factorTwoAffineCosDyadicCorrection n)]
  apply tsum_congr
  exact factorTwoSymmetricAffineCosDyadicKernel_eq_main_add_correction n

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
    factorTwoDyadicQ k ≤ 1 := by
  exact (factorTwoDyadicQ_le_invFourPow_local k).trans
    (pow_le_one₀ (by norm_num) (by norm_num))

private theorem factorTwoAffineCosUnweightedKernel_abs_le_one (n m : ℕ) :
    |factorTwoAffineCosUnweightedKernel n m| ≤ 1 := by
  have hx : 0 < factorTwoCauchyX (m + 1) := by
    unfold factorTwoCauchyX
    positivity
  have h := factorTwoCauchyT_abs_le_inv_sq
    (y := factorTwoMomentY n) hx
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

private theorem factorTwoAffineCosDyadicCorrection_abs_le_geometric
    (n m : ℕ) :
    |factorTwoAffineCosDyadicCorrection n m| ≤
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
  have hD0 : 0 ≤ factorTwoDyadicD (m + 1) := by
    unfold factorTwoDyadicD
    positivity
  have hdiff : |factorTwoDyadicD (m + 1) - 1| ≤ 2 * q := by
    rw [abs_of_nonpos (sub_nonpos.mpr hD)]
    unfold factorTwoDyadicD
    dsimp only [q] at hq0 hq1 ⊢
    nlinarith [sq_nonneg (factorTwoDyadicQ (m + 1))]
  unfold factorTwoAffineCosDyadicCorrection
  rw [abs_mul]
  calc
    |factorTwoDyadicD (m + 1) - 1| *
        |factorTwoAffineCosUnweightedKernel n m| ≤
        (2 * q) * 1 :=
      mul_le_mul hdiff (factorTwoAffineCosUnweightedKernel_abs_le_one n m)
        (abs_nonneg _) (by positivity)
    _ = 2 * q := by ring
    _ ≤ 2 * (1 / 4 : ℝ) ^ (m + 1) :=
      mul_le_mul_of_nonneg_left hq4 (by norm_num)

/-- Uniform geometric absolute-tail control for the signed dyadic
correction. -/
theorem factorTwoAffineCosDyadicCorrection_tail_abs_le
    (n K : ℕ) :
    |(∑' j : ℕ, factorTwoAffineCosDyadicCorrection n (K + j))| ≤
      1 / (4 : ℝ) ^ K := by
  let C : ℝ := 2 * (1 / 4 : ℝ) ^ (K + 1)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hgeom : Summable (fun j : ℕ ↦ C * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left C
  have hcorr : Summable
      (fun j : ℕ ↦ factorTwoAffineCosDyadicCorrection n (K + j)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff K).2
        (summable_factorTwoAffineCosDyadicCorrection n)
  have habs : Summable
      (fun j : ℕ ↦ |factorTwoAffineCosDyadicCorrection n (K + j)|) := by
    simpa only [Real.norm_eq_abs] using hcorr.norm
  have hpoint (j : ℕ) :
      |factorTwoAffineCosDyadicCorrection n (K + j)| ≤
        C * (1 / 4 : ℝ) ^ j := by
    have h := factorTwoAffineCosDyadicCorrection_abs_le_geometric n (K + j)
    rw [show K + j + 1 = (K + 1) + j by omega, pow_add] at h
    simpa only [C, mul_assoc] using h
  have hnorm :
      |(∑' j : ℕ, factorTwoAffineCosDyadicCorrection n (K + j))| ≤
        ∑' j : ℕ, |factorTwoAffineCosDyadicCorrection n (K + j)| := by
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm hcorr.norm
  have hsum := habs.tsum_le_tsum hpoint hgeom
  calc
    |(∑' j : ℕ, factorTwoAffineCosDyadicCorrection n (K + j))| ≤
        ∑' j : ℕ, |factorTwoAffineCosDyadicCorrection n (K + j)| := hnorm
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

/-! ## Rational interval kernels -/

/-- Fine rational enclosure of `factorTwoMomentY n`. -/
def factorTwoAffineCosYInterval (n : ℕ) : RatInterval :=
  ⟨piFineInterval.lower * n / factorTwoPrimeLogTwoInterval.upper,
    piFineInterval.upper * n / factorTwoPrimeLogTwoInterval.lower⟩

theorem factorTwoAffineCosYInterval_contains (n : ℕ) :
    (factorTwoAffineCosYInterval n).Contains (factorTwoMomentY n) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnum0 : 0 ≤ Real.pi * (n : ℝ) :=
    mul_nonneg Real.pi_pos.le hn0
  have hnumLo : (piFineInterval.lower : ℝ) * (n : ℝ) ≤
      Real.pi * (n : ℝ) :=
    mul_le_mul_of_nonneg_right piFineInterval_contains.1 hn0
  have hnumHi : Real.pi * (n : ℝ) ≤
      (piFineInterval.upper : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right piFineInterval_contains.2 hn0
  have hlogLowerPos :
      (0 : ℝ) < factorTwoPrimeLogTwoInterval.lower := by
    norm_num [factorTwoPrimeLogTwoInterval]
  have hlogUpper : factorTwoMomentLength ≤
      (factorTwoPrimeLogTwoInterval.upper : ℝ) :=
    factorTwoPrimeLogTwoInterval_contains.2
  have hlogLower :
      (factorTwoPrimeLogTwoInterval.lower : ℝ) ≤ factorTwoMomentLength :=
    factorTwoPrimeLogTwoInterval_contains.1
  unfold factorTwoAffineCosYInterval factorTwoMomentY
  constructor
  · norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
    unfold factorTwoNaturalFrequency
    exact div_le_div₀ hnum0 hnumLo factorTwoMomentLength_pos hlogUpper
  · norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
    unfold factorTwoNaturalFrequency
    exact div_le_div₀
      (mul_nonneg (by
        exact_mod_cast (show (0 : ℚ) ≤ piFineInterval.upper by
          norm_num [piFineInterval])) hn0)
      hnumHi hlogLowerPos hlogLower

private theorem factorTwoAffineCosYInterval_lower_nonneg (n : ℕ) :
    0 ≤ (factorTwoAffineCosYInterval n).lower := by
  change 0 ≤ piFineInterval.lower * n / factorTwoPrimeLogTwoInterval.upper
  unfold piFineInterval factorTwoPrimeLogTwoInterval
  positivity

private theorem factorTwoAffineCosYInterval_lower_pos
    {n : ℕ} (hn : n ≠ 0) :
    0 < (factorTwoAffineCosYInterval n).lower := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  change 0 < piFineInterval.lower * n / factorTwoPrimeLogTwoInterval.upper
  unfold piFineInterval factorTwoPrimeLogTwoInterval
  positivity

def factorTwoAffineCosXQ (m : ℕ) : ℚ := m + 1 + 1 / 4

def factorTwoAffineCosYSqInterval (n : ℕ) : RatInterval :=
  nonnegSquare (factorTwoAffineCosYInterval n)

def factorTwoAffineCosDenomInterval (n m : ℕ) : RatInterval :=
  pure (factorTwoAffineCosXQ m ^ 2) + factorTwoAffineCosYSqInterval n

private theorem factorTwoAffineCosDenomInterval_lower_pos (n m : ℕ) :
    0 < (factorTwoAffineCosDenomInterval n m).lower := by
  change 0 < factorTwoAffineCosXQ m ^ 2 +
    (factorTwoAffineCosYInterval n).lower ^ 2
  have hx : 0 < factorTwoAffineCosXQ m := by
    unfold factorTwoAffineCosXQ
    positivity
  positivity

private theorem factorTwoAffineCos_interval_mul_lower_pos
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

/-- Direct exact interval evaluation of the unweighted signed `T` kernel. -/
def factorTwoAffineCosUnweightedKernelInterval (n m : ℕ) : RatInterval :=
  let x2 := pure (factorTwoAffineCosXQ m ^ 2)
  let y2 := factorTwoAffineCosYSqInterval n
  let d := x2 + y2
  (x2 - y2) / nonnegSquare d

theorem factorTwoAffineCosUnweightedKernelInterval_contains (n m : ℕ) :
    (factorTwoAffineCosUnweightedKernelInterval n m).Contains
      (factorTwoAffineCosUnweightedKernel n m) := by
  have hy := factorTwoAffineCosYInterval_contains n
  have hy2 := contains_nonnegSquare
    (factorTwoAffineCosYInterval_lower_nonneg n) hy
  have hx : (pure (factorTwoAffineCosXQ m ^ 2)).Contains
      (factorTwoCauchyX (m + 1) ^ 2) := by
    convert contains_pure (factorTwoAffineCosXQ m ^ 2) using 1
    unfold factorTwoAffineCosXQ factorTwoCauchyX
    push_cast
    ring
  have hd : (factorTwoAffineCosDenomInterval n m).Contains
      (factorTwoCauchyX (m + 1) ^ 2 + factorTwoMomentY n ^ 2) :=
    contains_add hx hy2
  have hd2 := contains_nonnegSquare
    (factorTwoAffineCosDenomInterval_lower_pos n m).le hd
  unfold factorTwoAffineCosUnweightedKernelInterval
  dsimp only
  unfold factorTwoAffineCosUnweightedKernel factorTwoCauchyT
  have hquot := contains_div_of_pos (by
      change 0 < (factorTwoAffineCosDenomInterval n m).lower ^ 2
      exact pow_pos (factorTwoAffineCosDenomInterval_lower_pos n m) 2)
    (contains_sub hx hy2) hd2
  simpa only [factorTwoAffineCosDenomInterval,
    factorTwoAffineCosYSqInterval] using hquot

def factorTwoAffineCosUnweightedHeadInterval
    (n : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | K + 1 => factorTwoAffineCosUnweightedHeadInterval n K +
      factorTwoAffineCosUnweightedKernelInterval n K

theorem factorTwoAffineCosUnweightedHeadInterval_contains (n K : ℕ) :
    (factorTwoAffineCosUnweightedHeadInterval n K).Contains
      (∑ m ∈ Finset.range K, factorTwoAffineCosUnweightedKernel n m) := by
  induction K with
  | zero =>
      norm_num [factorTwoAffineCosUnweightedHeadInterval, Contains,
        RatInterval.pure]
  | succ K ih =>
      rw [Finset.sum_range_succ]
      exact contains_add ih
        (factorTwoAffineCosUnweightedKernelInterval_contains n K)

private def factorTwoAffineCosDerivativeProfileInterval
    (n N : ℕ) : RatInterval :=
  let u := pure ((N : ℚ) + 1 + 1 / 4)
  u / factorTwoAffineCosDenomInterval n N

private def factorTwoAffineCosDerivativeDerivInterval
    (n N : ℕ) : RatInterval :=
  let u2 := pure (((N : ℚ) + 1 + 1 / 4) ^ 2)
  let y2 := factorTwoAffineCosYSqInterval n
  let d := factorTwoAffineCosDenomInterval n N
  (y2 - u2) / nonnegSquare d

private def factorTwoAffineCosDerivativeSecondInterval
    (n N : ℕ) : RatInterval :=
  let u := pure ((N : ℚ) + 1 + 1 / 4)
  let u2 := pure (((N : ℚ) + 1 + 1 / 4) ^ 2)
  let y2 := factorTwoAffineCosYSqInterval n
  let d := factorTwoAffineCosDenomInterval n N
  (pure 2 * u * (u2 - pure 3 * y2)) / (d * nonnegSquare d)

/-- Rational enclosure of the unweighted `T`-tail main term (the negative
of `factorTwoAffineCosDerivativeTailMain`). -/
def factorTwoAffineCosUnweightedTailMainInterval (n N : ℕ) : RatInterval :=
  factorTwoAffineCosDerivativeProfileInterval n N -
    factorTwoAffineCosDerivativeDerivInterval n N / pure 2 +
    factorTwoAffineCosDerivativeSecondInterval n N / pure 12

private theorem factorTwoAffineCosUnweightedTailMainInterval_contains
    (n N : ℕ) :
    (factorTwoAffineCosUnweightedTailMainInterval n N).Contains
      (-factorTwoAffineCosDerivativeTailMain (factorTwoMomentY n) N) := by
  have hy := factorTwoAffineCosYInterval_contains n
  have hy2 := contains_nonnegSquare
    (factorTwoAffineCosYInterval_lower_nonneg n) hy
  have hu : (pure ((N : ℚ) + 1 + 1 / 4)).Contains
      ((N : ℝ) + 1 + 1 / 4) := by
    norm_num [Contains, RatInterval.pure]
  have hu2 : (pure (((N : ℚ) + 1 + 1 / 4) ^ 2)).Contains
      (((N : ℝ) + 1 + 1 / 4) ^ 2) := by
    norm_num [Contains, RatInterval.pure]
  have hd : (factorTwoAffineCosDenomInterval n N).Contains
      (((N : ℝ) + 1 + 1 / 4) ^ 2 + factorTwoMomentY n ^ 2) := by
    unfold factorTwoAffineCosDenomInterval factorTwoAffineCosXQ
      factorTwoAffineCosYSqInterval
    exact contains_add hu2 hy2
  have hd2 := contains_nonnegSquare
    (factorTwoAffineCosDenomInterval_lower_pos n N).le hd
  have hd3 : (factorTwoAffineCosDenomInterval n N *
      nonnegSquare (factorTwoAffineCosDenomInterval n N)).Contains
        ((((N : ℝ) + 1 + 1 / 4) ^ 2 + factorTwoMomentY n ^ 2) ^ 3) := by
    convert contains_mul hd hd2 using 1
    ring
  have hprofile : (factorTwoAffineCosDerivativeProfileInterval n N).Contains
      (diagonalHighProfile (factorTwoMomentY n) (N + 1)) := by
    unfold factorTwoAffineCosDerivativeProfileInterval diagonalHighProfile
      reciprocalRealPart
    exact contains_div_of_pos (factorTwoAffineCosDenomInterval_lower_pos n N)
      hu hd
  have hderiv : (factorTwoAffineCosDerivativeDerivInterval n N).Contains
      (diagonalHighProfileDeriv (factorTwoMomentY n) (N + 1)) := by
    unfold factorTwoAffineCosDerivativeDerivInterval diagonalHighProfileDeriv
      reciprocalRealPartDeriv
    exact contains_div_of_pos (by
        change 0 < (factorTwoAffineCosDenomInterval n N).lower ^ 2
        exact pow_pos (factorTwoAffineCosDenomInterval_lower_pos n N) 2)
      (contains_sub hy2 hu2) hd2
  have hsecond : (factorTwoAffineCosDerivativeSecondInterval n N).Contains
      (diagonalHighProfileSecondDeriv (factorTwoMomentY n) (N + 1)) := by
    unfold factorTwoAffineCosDerivativeSecondInterval
      diagonalHighProfileSecondDeriv
    exact contains_div_of_pos (factorTwoAffineCos_interval_mul_lower_pos
        (factorTwoAffineCosDenomInterval_lower_pos n N)
        (by
          change 0 < (factorTwoAffineCosDenomInterval n N).lower ^ 2
          exact pow_pos (factorTwoAffineCosDenomInterval_lower_pos n N) 2)
        (valid_of_contains hd) (valid_of_contains hd2))
      (contains_mul (contains_mul (contains_pure 2) hu)
        (contains_sub hu2 (contains_mul (contains_pure 3) hy2))) hd3
  unfold factorTwoAffineCosUnweightedTailMainInterval
    factorTwoAffineCosDerivativeTailMain
  have htwo : (RatInterval.pure (2 : ℚ)).Contains (2 : ℝ) :=
    contains_pure 2
  have htwelve : (RatInterval.pure (12 : ℚ)).Contains (12 : ℝ) :=
    contains_pure 12
  convert contains_add
    (contains_sub hprofile
      (contains_div_of_pos (by norm_num [RatInterval.pure]) hderiv htwo))
    (contains_div_of_pos (by norm_num [RatInterval.pure]) hsecond htwelve) using 1
  ring

/-- Rational upper radius for the shifted corrected-trapezoid tail. -/
def factorTwoAffineCosDerivativeTailRadiusQ (n N : ℕ) : ℚ :=
  5 / (2 * (factorTwoAffineCosDenomInterval n N).lower ^ 2)

def factorTwoAffineCosUnweightedTailInterval (n N : ℕ) : RatInterval :=
  let r := factorTwoAffineCosDerivativeTailRadiusQ n N
  factorTwoAffineCosUnweightedTailMainInterval n N + ⟨-r, r⟩

private theorem factorTwoAffineCosDerivativeTailRadius_le
    (n N : ℕ) :
    factorTwoAffineCosDerivativeTailRadius (factorTwoMomentY n) N ≤
      (factorTwoAffineCosDerivativeTailRadiusQ n N : ℝ) := by
  have hd := factorTwoAffineCosDenomInterval_lower_pos n N
  have hmem : (factorTwoAffineCosDenomInterval n N).Contains
      (((N : ℝ) + 1 + 1 / 4) ^ 2 + factorTwoMomentY n ^ 2) := by
    have hy := factorTwoAffineCosYInterval_contains n
    have hy2 := contains_nonnegSquare
      (factorTwoAffineCosYInterval_lower_nonneg n) hy
    have hu2 : (pure (((N : ℚ) + 1 + 1 / 4) ^ 2)).Contains
        (((N : ℝ) + 1 + 1 / 4) ^ 2) := by
      norm_num [Contains, RatInterval.pure]
    unfold factorTwoAffineCosDenomInterval factorTwoAffineCosXQ
      factorTwoAffineCosYSqInterval
    exact contains_add hu2 hy2
  have hrealPos : 0 <
      ((N : ℝ) + 1 + 1 / 4) ^ 2 + factorTwoMomentY n ^ 2 := by
    positivity
  have hsq := pow_le_pow_left₀
    (show (0 : ℝ) ≤ (factorTwoAffineCosDenomInterval n N).lower by
      exact_mod_cast hd.le)
    hmem.1 2
  unfold factorTwoAffineCosDerivativeTailRadius
    factorTwoAffineCosDerivativeTailRadiusQ
  norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow]
  apply div_le_div_of_nonneg_left (by norm_num)
    (mul_pos (by norm_num) (pow_pos (by exact_mod_cast hd) 2))
  nlinarith

theorem factorTwoAffineCosUnweightedTailInterval_contains
    {n : ℕ} (hn : n ≠ 0) (N : ℕ) :
    (factorTwoAffineCosUnweightedTailInterval n N).Contains
      (∑' j : ℕ, factorTwoAffineCosUnweightedKernel n (N + j)) := by
  have hy : 0 < factorTwoMomentY n := by
    unfold factorTwoMomentY factorTwoNaturalFrequency
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    exact div_pos (mul_pos Real.pi_pos hnpos) factorTwoMomentLength_pos
  have herr := factorTwoAffineCosDerivativeTail_sub_main_abs_le hy N
  have hrad := factorTwoAffineCosDerivativeTailRadius_le n N
  have hmain := factorTwoAffineCosUnweightedTailMainInterval_contains n N
  have htailEq :
      (∑' j : ℕ, factorTwoAffineCosUnweightedKernel n (N + j)) =
        -(∑' j : ℕ,
          diagonalHighProfileDeriv (factorTwoMomentY n) (N + j + 1)) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro j
    rw [factorTwoAffineCosUnweightedKernel_eq_neg_derivative]
    rw [← factorTwoMomentY_eq_diagonalY]
    congr 2
    norm_num only [Nat.cast_add, Nat.cast_one]
  let r : ℝ := (factorTwoAffineCosDerivativeTailRadiusQ n N : ℚ)
  have he : -r ≤
        (∑' j : ℕ, factorTwoAffineCosUnweightedKernel n (N + j)) -
          (-factorTwoAffineCosDerivativeTailMain (factorTwoMomentY n) N) ∧
      (∑' j : ℕ, factorTwoAffineCosUnweightedKernel n (N + j)) -
          (-factorTwoAffineCosDerivativeTailMain (factorTwoMomentY n) N) ≤ r := by
    rw [htailEq]
    rw [abs_le] at herr
    constructor <;> dsimp only [r] <;> linarith
  have heI : (⟨-factorTwoAffineCosDerivativeTailRadiusQ n N,
      factorTwoAffineCosDerivativeTailRadiusQ n N⟩ : RatInterval).Contains
        ((∑' j : ℕ, factorTwoAffineCosUnweightedKernel n (N + j)) -
          (-factorTwoAffineCosDerivativeTailMain (factorTwoMomentY n) N)) := by
    simpa only [Contains, Rat.cast_neg] using he
  unfold factorTwoAffineCosUnweightedTailInterval
  have h := contains_add hmain heI
  convert h using 1
  ring

/-! ## Complete unweighted series enclosures -/

private def factorTwoAffineCosInvSqTailLowerQ (K : ℕ) : ℚ :=
  let x := factorTwoAffineCosXQ K
  x⁻¹ + (x⁻¹) ^ 2 / 2 + (x⁻¹) ^ 3 / 6 - (x⁻¹) ^ 5 / 30

private def factorTwoAffineCosInvSqTailUpperQ (K : ℕ) : ℚ :=
  let x := factorTwoAffineCosXQ K
  x⁻¹ + (x⁻¹) ^ 2 / 2 + (x⁻¹) ^ 3 / 6

/-- Fifth-order rational enclosure of the zero-mode reciprocal-square tail. -/
def factorTwoAffineCosZeroTailInterval (K : ℕ) : RatInterval :=
  ⟨factorTwoAffineCosInvSqTailLowerQ K,
    factorTwoAffineCosInvSqTailUpperQ K⟩

theorem factorTwoAffineCosZeroTailInterval_contains (K : ℕ) :
    (factorTwoAffineCosZeroTailInterval K).Contains
      (∑' j : ℕ, factorTwoAffineCosUnweightedKernel 0 (K + j)) := by
  let x : ℝ := factorTwoAffineCosXQ K
  have hx : 1 ≤ x := by
    dsimp only [x]
    unfold factorTwoAffineCosXQ
    push_cast
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    norm_num
    linarith
  have hb := factorTwoAffineCosInvSqTail_tsum_bounds hx
  have hterms :
      (∑' j : ℕ, factorTwoAffineCosUnweightedKernel 0 (K + j)) =
        ∑' j : ℕ, factorTwoAffineCosInvSqTailTerm x j := by
    apply tsum_congr
    intro j
    have hy0 : factorTwoMomentY 0 = 0 := by
      unfold factorTwoMomentY factorTwoNaturalFrequency
      norm_num
    have hxj : factorTwoCauchyX (K + j + 1) = x + j := by
      unfold factorTwoCauchyX
      dsimp only [x]
      unfold factorTwoAffineCosXQ
      push_cast
      ring
    unfold factorTwoAffineCosUnweightedKernel
    rw [hy0, hxj]
    unfold factorTwoCauchyT factorTwoAffineCosInvSqTailTerm
    have hpos : 0 < x + (j : ℝ) := by positivity
    field_simp [hpos.ne']
    ring
  rw [hterms]
  unfold factorTwoAffineCosZeroTailInterval Contains
  constructor
  · convert hb.1 using 1
    norm_num [factorTwoAffineCosInvSqTailLowerQ,
      factorTwoAffineCosInvSqTailLowerPotential, x]
  · convert hb.2 using 1
    norm_num [factorTwoAffineCosInvSqTailUpperQ,
      factorTwoAffineCosInvSqTailUpperPotential, x]

/-- Mode-dependent head length for the slowly convergent signed main series.
The zero mode uses its exact reciprocal-square tail, low positive modes use a
long shifted Euler--Maclaurin head, and high modes need no explicit head. -/
def factorTwoAffineCosUnweightedHeadCount (n : ℕ) : ℕ :=
  if n = 0 then 48 else if n < 70 then 384 else 0

def factorTwoAffineCosUnweightedSeriesInterval (n : ℕ) : RatInterval :=
  let K := factorTwoAffineCosUnweightedHeadCount n
  factorTwoAffineCosUnweightedHeadInterval n K +
    if n = 0 then factorTwoAffineCosZeroTailInterval K
    else factorTwoAffineCosUnweightedTailInterval n K

theorem factorTwoAffineCosUnweightedSeriesInterval_contains (n : ℕ) :
    (factorTwoAffineCosUnweightedSeriesInterval n).Contains
      (∑' m : ℕ, factorTwoAffineCosUnweightedKernel n m) := by
  let K := factorTwoAffineCosUnweightedHeadCount n
  have hsplit :=
    (summable_factorTwoAffineCosUnweightedKernel n).sum_add_tsum_nat_add K
  rw [← hsplit]
  unfold factorTwoAffineCosUnweightedSeriesInterval
  dsimp only [K]
  by_cases hn : n = 0
  · subst n
    simp only [if_pos]
    exact contains_add
      (factorTwoAffineCosUnweightedHeadInterval_contains 0
        (factorTwoAffineCosUnweightedHeadCount 0))
      (by simpa [Nat.add_comm] using
        (factorTwoAffineCosZeroTailInterval_contains
          (factorTwoAffineCosUnweightedHeadCount 0)))
  · simp only [hn, if_false]
    exact contains_add
      (factorTwoAffineCosUnweightedHeadInterval_contains n
        (factorTwoAffineCosUnweightedHeadCount n))
      (by simpa [Nat.add_comm] using
        (factorTwoAffineCosUnweightedTailInterval_contains hn
          (factorTwoAffineCosUnweightedHeadCount n)))

/-! ## Geometric dyadic-correction enclosures -/

/-- Exact rational interval for the dyadic factor
`q_k = (sqrt 2)^{-1} / 4^k`. -/
def factorTwoAffineCosDyadicQInterval (k : ℕ) : RatInterval :=
  sqrtTwoInterval⁻¹ / pure ((4 : ℚ) ^ k)

theorem factorTwoAffineCosDyadicQInterval_contains (k : ℕ) :
    (factorTwoAffineCosDyadicQInterval k).Contains
      (factorTwoDyadicQ k) := by
  have hsInv := contains_inv_of_pos (I := sqrtTwoInterval)
    (x := Real.sqrt 2) (by norm_num [sqrtTwoInterval])
      sqrtTwoInterval_contains
  have hpow : (pure ((4 : ℚ) ^ k)).Contains ((4 : ℝ) ^ k) := by
    simpa using contains_pure ((4 : ℚ) ^ k)
  exact contains_div_of_pos (by
    change 0 < (4 : ℚ) ^ k
    positivity) hsInv hpow

def factorTwoAffineCosDyadicDInterval (k : ℕ) : RatInterval :=
  let oneSubQ := pure 1 - factorTwoAffineCosDyadicQInterval k
  oneSubQ * oneSubQ

theorem factorTwoAffineCosDyadicDInterval_contains (k : ℕ) :
    (factorTwoAffineCosDyadicDInterval k).Contains
      (factorTwoDyadicD k) := by
  have hone : (pure (1 : ℚ)).Contains (1 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hsub : (pure 1 - factorTwoAffineCosDyadicQInterval k).Contains
      ((1 : ℝ) - factorTwoDyadicQ k) :=
    contains_sub hone
      (factorTwoAffineCosDyadicQInterval_contains k)
  unfold factorTwoAffineCosDyadicDInterval factorTwoDyadicD
  rw [pow_two]
  exact contains_mul hsub hsub

def factorTwoAffineCosDyadicCorrectionInterval (n m : ℕ) : RatInterval :=
  (factorTwoAffineCosDyadicDInterval (m + 1) - pure 1) *
    factorTwoAffineCosUnweightedKernelInterval n m

theorem factorTwoAffineCosDyadicCorrectionInterval_contains (n m : ℕ) :
    (factorTwoAffineCosDyadicCorrectionInterval n m).Contains
      (factorTwoAffineCosDyadicCorrection n m) := by
  have hone : (pure (1 : ℚ)).Contains (1 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  unfold factorTwoAffineCosDyadicCorrectionInterval
    factorTwoAffineCosDyadicCorrection
  exact contains_mul
    (contains_sub (factorTwoAffineCosDyadicDInterval_contains (m + 1))
      hone)
    (factorTwoAffineCosUnweightedKernelInterval_contains n m)

def factorTwoAffineCosDyadicCorrectionHeadInterval
    (n : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | K + 1 => factorTwoAffineCosDyadicCorrectionHeadInterval n K +
      factorTwoAffineCosDyadicCorrectionInterval n K

theorem factorTwoAffineCosDyadicCorrectionHeadInterval_contains
    (n K : ℕ) :
    (factorTwoAffineCosDyadicCorrectionHeadInterval n K).Contains
      (∑ m ∈ Finset.range K, factorTwoAffineCosDyadicCorrection n m) := by
  induction K with
  | zero =>
      norm_num [factorTwoAffineCosDyadicCorrectionHeadInterval, Contains,
        RatInterval.pure]
  | succ K ih =>
      rw [Finset.sum_range_succ]
      exact contains_add ih
        (factorTwoAffineCosDyadicCorrectionInterval_contains n K)

private def factorTwoAffineCosDyadicCorrectionTailRadiusQ (K : ℕ) : ℚ :=
  1 / (4 : ℚ) ^ K

def factorTwoAffineCosDyadicCorrectionTailInterval (K : ℕ) : RatInterval :=
  let r := factorTwoAffineCosDyadicCorrectionTailRadiusQ K
  ⟨-r, r⟩

theorem factorTwoAffineCosDyadicCorrectionTailInterval_contains
    (n K : ℕ) :
    (factorTwoAffineCosDyadicCorrectionTailInterval K).Contains
      (∑' j : ℕ, factorTwoAffineCosDyadicCorrection n (K + j)) := by
  have h := factorTwoAffineCosDyadicCorrection_tail_abs_le n K
  rw [abs_le] at h
  simpa only [factorTwoAffineCosDyadicCorrectionTailInterval,
    factorTwoAffineCosDyadicCorrectionTailRadiusQ, Contains, Rat.cast_neg,
    Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using h

def factorTwoAffineCosDyadicCorrectionSeriesInterval (n : ℕ) : RatInterval :=
  factorTwoAffineCosDyadicCorrectionHeadInterval n 20 +
    factorTwoAffineCosDyadicCorrectionTailInterval 20

theorem factorTwoAffineCosDyadicCorrectionSeriesInterval_contains (n : ℕ) :
    (factorTwoAffineCosDyadicCorrectionSeriesInterval n).Contains
      (∑' m : ℕ, factorTwoAffineCosDyadicCorrection n m) := by
  have hsplit :=
    (summable_factorTwoAffineCosDyadicCorrection n).sum_add_tsum_nat_add 20
  rw [← hsplit]
  unfold factorTwoAffineCosDyadicCorrectionSeriesInterval
  exact contains_add
    (factorTwoAffineCosDyadicCorrectionHeadInterval_contains n 20)
    (by simpa [Nat.add_comm] using
      (factorTwoAffineCosDyadicCorrectionTailInterval_contains n 20))

/-- Complete accelerated enclosure of the signed dyadic Cauchy series. -/
def factorTwoAffineCosDyadicSeriesInterval (n : ℕ) : RatInterval :=
  factorTwoAffineCosUnweightedSeriesInterval n +
    factorTwoAffineCosDyadicCorrectionSeriesInterval n

theorem factorTwoAffineCosDyadicSeriesInterval_contains (n : ℕ) :
    (factorTwoAffineCosDyadicSeriesInterval n).Contains
      (∑' m : ℕ,
        factorTwoSymmetricAffineCosDyadicKernel n (m + 1)) := by
  rw [factorTwoSymmetricAffineCosDyadic_tsum_eq_main_add_correction]
  exact contains_add
    (factorTwoAffineCosUnweightedSeriesInterval_contains n)
    (factorTwoAffineCosDyadicCorrectionSeriesInterval_contains n)

/-! ## Full affine-cosine moments -/

/-- Direct rational enclosure of the exceptional `j = 0` Cauchy kernel. -/
def factorTwoAffineCosInitialKernelInterval (n : ℕ) : RatInterval :=
  let x2 := pure ((1 / 4 : ℚ) ^ 2)
  let y2 := factorTwoAffineCosYSqInterval n
  let d := x2 + y2
  (x2 - y2) / nonnegSquare d

theorem factorTwoAffineCosInitialKernelInterval_contains (n : ℕ) :
    (factorTwoAffineCosInitialKernelInterval n).Contains
      (factorTwoCauchyT (factorTwoCauchyX 0) (factorTwoMomentY n)) := by
  have hy := factorTwoAffineCosYInterval_contains n
  have hy2 := contains_nonnegSquare
    (factorTwoAffineCosYInterval_lower_nonneg n) hy
  have hx : (pure ((1 / 4 : ℚ) ^ 2)).Contains
      (factorTwoCauchyX 0 ^ 2) := by
    norm_num [Contains, RatInterval.pure, factorTwoCauchyX]
  have hd : (pure ((1 / 4 : ℚ) ^ 2) +
      factorTwoAffineCosYSqInterval n).Contains
        (factorTwoCauchyX 0 ^ 2 + factorTwoMomentY n ^ 2) :=
    contains_add hx hy2
  have hdLower : 0 < (pure ((1 / 4 : ℚ) ^ 2) +
      factorTwoAffineCosYSqInterval n).lower := by
    change 0 < (1 / 4 : ℚ) ^ 2 +
      (factorTwoAffineCosYInterval n).lower ^ 2
    positivity
  have hd2 := contains_nonnegSquare hdLower.le hd
  unfold factorTwoAffineCosInitialKernelInterval factorTwoCauchyT
  exact contains_div_of_pos (by
      change 0 < (pure ((1 / 4 : ℚ) ^ 2) +
        factorTwoAffineCosYSqInterval n).lower ^ 2
      exact pow_pos hdLower 2)
    (contains_sub hx hy2) hd2

/-- The exact zero phase is represented by a point interval; positive modes
use the public prime-phase cosine enclosure. -/
def factorTwoAffineCosPrimeCosInterval
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  if n.1 = 0 then pure 1 else factorTwoPrimeCosInterval n

theorem factorTwoAffineCosPrimeCosInterval_contains
    (n : FactorTwoCanonicalEvenIndex) :
    (factorTwoAffineCosPrimeCosInterval n).Contains
      (Real.cos (2 * factorTwoMomentY n.1 * factorTwoPrimeShift)) := by
  by_cases hn : n.1 = 0
  · rw [factorTwoAffineCosPrimeCosInterval, if_pos hn]
    rw [hn]
    norm_num [factorTwoMomentY, factorTwoNaturalFrequency, Contains,
      RatInterval.pure]
  · rw [factorTwoAffineCosPrimeCosInterval, if_neg hn]
    exact factorTwoPrimeCosInterval_contains n

private def factorTwoAffineCosTwoLengthInterval : RatInterval :=
  pure 2 * factorTwoPrimeLogTwoInterval

private theorem factorTwoAffineCosTwoLengthInterval_contains :
    factorTwoAffineCosTwoLengthInterval.Contains
      (2 * factorTwoMomentLength) := by
  exact contains_mul (contains_pure 2)
    factorTwoPrimeLogTwoInterval_contains

private theorem factorTwoAffineCosTwoLengthInterval_lower_pos :
    0 < factorTwoAffineCosTwoLengthInterval.lower := by
  apply factorTwoAffineCos_interval_mul_lower_pos
  · norm_num [RatInterval.pure]
  · norm_num [factorTwoPrimeLogTwoInterval]
  · exact valid_of_contains (contains_pure 2)
  · exact valid_of_contains factorTwoPrimeLogTwoInterval_contains

/-- Public exact rational enclosure of every canonical affine-cosine
perturbation moment, including the zero mode. -/
def factorTwoSymmetricAffineCosMomentInterval
    (n : FactorTwoCanonicalEvenIndex) : RatInterval :=
  (factorTwoHeadDefectInterval / factorTwoAffineCosTwoLengthInterval) *
      factorTwoAffineCosInitialKernelInterval n.1 -
    (pure 1 / factorTwoAffineCosTwoLengthInterval) *
      factorTwoAffineCosDyadicSeriesInterval n.1 -
    (pure 2 * factorTwoPrimeLogTwoInterval) / sqrtTwoInterval -
    factorTwoPrimeBetaInterval * factorTwoPrimeAffineHeightInterval *
      factorTwoAffineCosPrimeCosInterval n

theorem factorTwoSymmetricAffineCosMomentInterval_contains
    (n : FactorTwoCanonicalEvenIndex) :
    (factorTwoSymmetricAffineCosMomentInterval n).Contains
      (factorTwoSymmetricAffineCosMoment n.1) := by
  have htwo : (pure (2 : ℚ)).Contains (2 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hone : (pure (1 : ℚ)).Contains (1 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hheadCoeff :
      (factorTwoHeadDefectInterval /
        factorTwoAffineCosTwoLengthInterval).Contains
          (factorTwoHeadDefect / (2 * factorTwoMomentLength)) :=
    contains_div_of_pos factorTwoAffineCosTwoLengthInterval_lower_pos
      factorTwoHeadDefectInterval_contains
      factorTwoAffineCosTwoLengthInterval_contains
  have hseriesCoeff :
      (pure 1 / factorTwoAffineCosTwoLengthInterval).Contains
          (1 / (2 * factorTwoMomentLength)) :=
    contains_div_of_pos factorTwoAffineCosTwoLengthInterval_lower_pos
      hone factorTwoAffineCosTwoLengthInterval_contains
  have hbase :
      ((pure 2 * factorTwoPrimeLogTwoInterval) /
        sqrtTwoInterval).Contains
          (2 * factorTwoMomentLength / Real.sqrt 2) :=
    contains_div_of_pos (by norm_num [sqrtTwoInterval])
      (contains_mul htwo factorTwoPrimeLogTwoInterval_contains)
      sqrtTwoInterval_contains
  have hprime :
      (factorTwoPrimeBetaInterval * factorTwoPrimeAffineHeightInterval *
        factorTwoAffineCosPrimeCosInterval n).Contains
          ((Real.log 3 / Real.sqrt 3) *
            (2 - 2 * factorTwoPrimeShift / factorTwoMomentLength) *
              Real.cos (2 * factorTwoMomentY n.1 * factorTwoPrimeShift)) :=
    contains_mul
      (contains_mul factorTwoPrimeBetaInterval_contains
        factorTwoPrimeAffineHeightInterval_contains)
      (factorTwoAffineCosPrimeCosInterval_contains n)
  rw [factorTwoSymmetricAffineCosMoment_eq_dyadicCauchySeries n]
  exact contains_sub
    (contains_sub
      (contains_sub
        (contains_mul hheadCoeff
          (factorTwoAffineCosInitialKernelInterval_contains n.1))
        (contains_mul hseriesCoeff
          (factorTwoAffineCosDyadicSeriesInterval_contains n.1)))
      hbase)
    hprime

/-! ## Exact width certificate -/

/-! The certificate below is intentionally uniform in the mode.  Its only
case distinction is the analytic head schedule (`0`, low positive, or high),
not a traversal of the 201 canonical indices. -/

private theorem affineCos_absBound_mono
    {I : RatInterval} {A B : ℚ} (hI : I.AbsBound A) (hAB : A ≤ B) :
    I.AbsBound B := by
  unfold AbsBound at hI ⊢
  constructor <;> linarith [hI.1, hI.2]

private theorem affineCosYInterval_valid (n : ℕ) :
    (factorTwoAffineCosYInterval n).Valid :=
  valid_of_contains (factorTwoAffineCosYInterval_contains n)

private theorem affineCosYInterval_lower_growth (n : ℕ) :
    (453 / 100 : ℚ) * n ≤ (factorTwoAffineCosYInterval n).lower := by
  have hn : (0 : ℚ) ≤ n := by positivity
  change (453 / 100 : ℚ) * (n : ℚ) ≤
    piFineInterval.lower * (n : ℚ) /
      factorTwoPrimeLogTwoInterval.upper
  have hslope : (453 / 100 : ℚ) ≤
      piFineInterval.lower / factorTwoPrimeLogTwoInterval.upper := by
    norm_num [piFineInterval, factorTwoPrimeLogTwoInterval]
  calc
    (453 / 100 : ℚ) * (n : ℚ) ≤
        (piFineInterval.lower / factorTwoPrimeLogTwoInterval.upper) * n :=
      mul_le_mul_of_nonneg_right hslope hn
    _ = piFineInterval.lower * (n : ℚ) /
        factorTwoPrimeLogTwoInterval.upper := by ring

private theorem affineCosYInterval_upper_growth (n : ℕ) :
    (factorTwoAffineCosYInterval n).upper ≤ (91 / 20 : ℚ) * n := by
  have hn : (0 : ℚ) ≤ n := by positivity
  change piFineInterval.upper * (n : ℚ) /
      factorTwoPrimeLogTwoInterval.lower ≤ (91 / 20 : ℚ) * (n : ℚ)
  have hslope : piFineInterval.upper / factorTwoPrimeLogTwoInterval.lower ≤
      (91 / 20 : ℚ) := by
    norm_num [piFineInterval, factorTwoPrimeLogTwoInterval]
  calc
    piFineInterval.upper * (n : ℚ) /
        factorTwoPrimeLogTwoInterval.lower =
      (piFineInterval.upper / factorTwoPrimeLogTwoInterval.lower) * n := by
        ring
    _ ≤ (91 / 20 : ℚ) * n :=
      mul_le_mul_of_nonneg_right hslope hn

private theorem affineCosYInterval_width_le (n : ℕ) :
    width (factorTwoAffineCosYInterval n) ≤ (n : ℚ) / 10000000000000 := by
  have hn : (0 : ℚ) ≤ n := by positivity
  change
    piFineInterval.upper * (n : ℚ) /
          factorTwoPrimeLogTwoInterval.lower -
        piFineInterval.lower * (n : ℚ) /
          factorTwoPrimeLogTwoInterval.upper ≤
      (n : ℚ) / 10000000000000
  have hslope :
      piFineInterval.upper / factorTwoPrimeLogTwoInterval.lower -
          piFineInterval.lower / factorTwoPrimeLogTwoInterval.upper ≤
        (1 : ℚ) / 10000000000000 := by
    norm_num [piFineInterval, factorTwoPrimeLogTwoInterval]
  calc
    piFineInterval.upper * (n : ℚ) /
          factorTwoPrimeLogTwoInterval.lower -
        piFineInterval.lower * (n : ℚ) /
          factorTwoPrimeLogTwoInterval.upper =
      (piFineInterval.upper / factorTwoPrimeLogTwoInterval.lower -
          piFineInterval.lower / factorTwoPrimeLogTwoInterval.upper) * n := by
        ring
    _ ≤ ((1 : ℚ) / 10000000000000) * n :=
      mul_le_mul_of_nonneg_right hslope hn
    _ = (n : ℚ) / 10000000000000 := by ring

private theorem affineCosYSqInterval_valid (n : ℕ) :
    (factorTwoAffineCosYSqInterval n).Valid := by
  change (factorTwoAffineCosYInterval n).lower ^ 2 ≤
    (factorTwoAffineCosYInterval n).upper ^ 2
  exact pow_le_pow_left₀ (factorTwoAffineCosYInterval_lower_nonneg n)
    (affineCosYInterval_valid n) 2

private theorem affineCosYSqInterval_width_le (n : ℕ) :
    width (factorTwoAffineCosYSqInterval n) ≤
      (n : ℚ) ^ 2 / 1000000000000 := by
  have hn : (0 : ℚ) ≤ n := by positivity
  have hsum :
      (factorTwoAffineCosYInterval n).upper +
          (factorTwoAffineCosYInterval n).lower ≤
        (91 / 10 : ℚ) * n := by
    calc
      (factorTwoAffineCosYInterval n).upper +
          (factorTwoAffineCosYInterval n).lower ≤
        (factorTwoAffineCosYInterval n).upper +
          (factorTwoAffineCosYInterval n).upper := by
            simpa only [add_comm] using
              (add_le_add_left (affineCosYInterval_valid n)
                (factorTwoAffineCosYInterval n).upper)
      _ ≤ (91 / 20 : ℚ) * n + (91 / 20 : ℚ) * n :=
        add_le_add (affineCosYInterval_upper_growth n)
          (affineCosYInterval_upper_growth n)
      _ = (91 / 10 : ℚ) * n := by ring
  have hw := affineCosYInterval_width_le n
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
      ((91 / 10 : ℚ) * n) * ((n : ℚ) / 10000000000000) := by
        exact mul_le_mul hsum hw (width_nonneg (affineCosYInterval_valid n))
          (by positivity)
    _ ≤ (n : ℚ) ^ 2 / 1000000000000 := by nlinarith

private theorem affineCos_kernelExpression_metrics
    (n : ℕ) (x2 : ℚ) (hx2 : (1 / 16 : ℚ) ≤ x2) :
    let S := factorTwoAffineCosYSqInterval n
    let D := pure x2 + S
    let N := pure x2 - S
    (N / nonnegSquare D).Valid ∧
      (N / nonnegSquare D).AbsBound 24 ∧
      width (N / nonnegSquare D) ≤ (1 / 10000000000000 : ℚ) := by
  dsimp only
  let S := factorTwoAffineCosYSqInterval n
  let D := pure x2 + S
  let N := pure x2 - S
  let d := D.lower
  have hn0 : (0 : ℚ) ≤ n := by positivity
  have hSvalid : S.Valid := by
    simpa only [S] using affineCosYSqInterval_valid n
  have hDvalid : D.Valid := valid_add (valid_pure x2) hSvalid
  have hNvalid : N.Valid := valid_sub (valid_pure x2) hSvalid
  have hYgrowth := affineCosYInterval_lower_growth n
  have hYsqGrowth : (20 : ℚ) * (n : ℚ) ^ 2 ≤ S.lower := by
    dsimp only [S, factorTwoAffineCosYSqInterval, nonnegSquare]
    have hsquare := pow_le_pow_left₀ (by positivity :
        (0 : ℚ) ≤ (453 / 100 : ℚ) * n) hYgrowth 2
    nlinarith
  have hdFloor : (1 / 16 : ℚ) + 20 * (n : ℚ) ^ 2 ≤ d := by
    change (1 / 16 : ℚ) + 20 * (n : ℚ) ^ 2 ≤ x2 + S.lower
    linarith
  have hdpos : 0 < d := by
    apply lt_of_lt_of_le (show (0 : ℚ) < 1 / 16 + 20 * (n : ℚ) ^ 2 by
      nlinarith [sq_nonneg (n : ℚ)])
    exact hdFloor
  have hwS : width S ≤ (n : ℚ) ^ 2 / 1000000000000 := by
    simpa only [S] using affineCosYSqInterval_width_le n
  have hwSnonneg : 0 ≤ width S := width_nonneg hSvalid
  have hwS_le_half_d : width S ≤ d / 2 := by
    have hnBound : (n : ℚ) ^ 2 / 1000000000000 ≤
        ((1 / 16 : ℚ) + 20 * (n : ℚ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (n : ℚ)]
    exact hwS.trans (hnBound.trans (div_le_div_of_nonneg_right hdFloor
      (by norm_num)))
  have hDupper : D.upper ≤ (3 / 2 : ℚ) * d := by
    have hwidthEq : D.upper - D.lower = width S := by
      change (x2 + S.upper) - (x2 + S.lower) = width S
      unfold width
      ring
    dsimp only [d]
    linarith
  have hDabs : D.AbsBound ((3 / 2 : ℚ) * d) := by
    constructor
    · exact (neg_nonpos.mpr (by positivity)).trans (by
        dsimp only [d] at hdpos
        exact hdpos.le)
    · exact hDupper
  have hNabs : N.AbsBound ((3 / 2 : ℚ) * d) := by
    unfold AbsBound
    change -((3 / 2 : ℚ) * (x2 + S.lower)) ≤ x2 - S.upper ∧
      x2 - S.lower ≤ (3 / 2 : ℚ) * (x2 + S.lower)
    have hSupper : x2 + S.upper ≤
        (3 / 2 : ℚ) * (x2 + S.lower) := by
      simpa only [D, d, RatInterval.add, RatInterval.pure] using hDupper
    constructor
    · linarith [hx2]
    · have hSnonneg : 0 ≤ S.lower := by
        dsimp only [S, factorTwoAffineCosYSqInterval, nonnegSquare]
        positivity
      linarith [hx2]
  have hDsqValid : (nonnegSquare D).Valid := by
    change D.lower ^ 2 ≤ D.upper ^ 2
    exact pow_le_pow_left₀ hdpos.le hDvalid 2
  have hDsqAbs : (nonnegSquare D).AbsBound
      ((9 / 4 : ℚ) * d ^ 2) := by
    unfold AbsBound
    change -((9 / 4 : ℚ) * d ^ 2) ≤ D.lower ^ 2 ∧
      D.upper ^ 2 ≤ (9 / 4 : ℚ) * d ^ 2
    constructor
    · nlinarith [sq_nonneg d]
    · have hDupperNonneg : 0 ≤ D.upper := hdpos.le.trans hDvalid
      have hsquare := pow_le_pow_left₀ hDupperNonneg hDupper 2
      nlinarith
  have hDsqWidth : width (nonnegSquare D) ≤
      (5 / 2 : ℚ) * d * width S := by
    have hsum : D.upper + D.lower ≤ (5 / 2 : ℚ) * d := by
      dsimp only [d]
      linarith
    have hwD : width D = width S := by
      dsimp only [D]
      rw [width_add, width_pure, zero_add]
    change D.upper ^ 2 - D.lower ^ 2 ≤
      (5 / 2 : ℚ) * d * width S
    rw [sq_sub_sq, ← width]
    rw [hwD]
    exact mul_le_mul_of_nonneg_right hsum hwSnonneg
  have hDsqLower : (nonnegSquare D).lower = d ^ 2 := by
    rfl
  have hquotValid : (N / nonnegSquare D).Valid := by
    apply valid_div_of_pos hNvalid hDsqValid
    rw [hDsqLower]
    positivity
  have hquotAbsRaw : (N / nonnegSquare D).AbsBound
      (((3 / 2 : ℚ) * d) * (d ^ 2)⁻¹) := by
    apply absBound_div_of_lower hNvalid hDsqValid hNabs
      (by positivity) (pow_pos hdpos 2)
    rw [hDsqLower]
  have hquotAbs : (N / nonnegSquare D).AbsBound 24 := by
    apply affineCos_absBound_mono hquotAbsRaw
    have hdfloorSmall : (1 / 16 : ℚ) ≤ d := by linarith [hdFloor]
    have hinv : d⁻¹ ≤ (16 : ℚ) := by
      have h := (inv_le_inv₀ hdpos (by norm_num : (0 : ℚ) < 1 / 16)).2
        hdfloorSmall
      norm_num at h ⊢
      exact h
    calc
      ((3 / 2 : ℚ) * d) * (d ^ 2)⁻¹ = (3 / 2 : ℚ) * d⁻¹ := by
        field_simp [hdpos.ne']
      _ ≤ (3 / 2 : ℚ) * 16 :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 24 := by norm_num
  have hwidthRaw := width_div_le_of_lower hNvalid hDsqValid hNabs
    (by positivity : (0 : ℚ) ≤ (3 / 2 : ℚ) * d) (pow_pos hdpos 2)
    (show d ^ 2 ≤ (nonnegSquare D).lower by rw [hDsqLower])
  have hwN : width N = width S := by
    dsimp only [N]
    rw [width_sub, width_pure, zero_add]
  have hwidthFormula : width (N / nonnegSquare D) ≤
      (19 / 4 : ℚ) * width S / d ^ 2 := by
    calc
      width (N / nonnegSquare D) ≤
          (d ^ 2)⁻¹ * width N +
            ((3 / 2 : ℚ) * d) *
              (width (nonnegSquare D) / (d ^ 2 * d ^ 2)) := by
        simpa only [hDsqLower] using hwidthRaw
      _ ≤ (d ^ 2)⁻¹ * width S +
          ((3 / 2 : ℚ) * d) *
            (((5 / 2 : ℚ) * d * width S) / (d ^ 2 * d ^ 2)) := by
        rw [hwN]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hDsqWidth (by positivity))
          (by positivity))
      _ = (19 / 4 : ℚ) * width S / d ^ 2 := by
        field_simp [hdpos.ne']
        ring
  have hwidth : width (N / nonnegSquare D) ≤
      (1 / 10000000000000 : ℚ) := by
    by_cases hn : n = 0
    · subst n
      have hwZero : width S = 0 := by
        dsimp only [S, factorTwoAffineCosYSqInterval,
          factorTwoAffineCosYInterval, nonnegSquare, width]
        norm_num
      rw [hwZero] at hwidthFormula
      norm_num at hwidthFormula
      exact hwidthFormula.trans (by norm_num)
    · have hnq : (1 : ℚ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hd20 : (20 : ℚ) * (n : ℚ) ^ 2 ≤ d := by
        linarith [hdFloor]
      have hd20sq := pow_le_pow_left₀ (by positivity :
          (0 : ℚ) ≤ 20 * (n : ℚ) ^ 2) hd20 2
      calc
        width (N / nonnegSquare D) ≤
            (19 / 4 : ℚ) * width S / d ^ 2 := hwidthFormula
        _ ≤ (19 / 4 : ℚ) *
            ((n : ℚ) ^ 2 / 1000000000000) / d ^ 2 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hwS (by norm_num)) (by positivity)
        _ ≤ (1 / 10000000000000 : ℚ) := by
          rw [div_le_iff₀ (pow_pos hdpos 2)]
          calc
            (19 / 4 : ℚ) * ((n : ℚ) ^ 2 / 1000000000000) ≤
                (1 / 10000000000000 : ℚ) *
                  (20 * (n : ℚ) ^ 2) ^ 2 := by
              nlinarith [sq_nonneg ((n : ℚ) ^ 2 - 1)]
            _ ≤ (1 / 10000000000000 : ℚ) * d ^ 2 :=
              mul_le_mul_of_nonneg_left hd20sq (by norm_num)
  exact ⟨hquotValid, hquotAbs, hwidth⟩

private theorem affineCosUnweightedKernelInterval_metrics (n m : ℕ) :
    (factorTwoAffineCosUnweightedKernelInterval n m).Valid ∧
      (factorTwoAffineCosUnweightedKernelInterval n m).AbsBound 24 ∧
      width (factorTwoAffineCosUnweightedKernelInterval n m) ≤
        (1 / 10000000000000 : ℚ) := by
  have hx : (1 / 16 : ℚ) ≤ factorTwoAffineCosXQ m ^ 2 := by
    have hxq : (5 / 4 : ℚ) ≤ factorTwoAffineCosXQ m := by
      unfold factorTwoAffineCosXQ
      have hm : (0 : ℚ) ≤ m := by positivity
      linarith
    nlinarith [sq_nonneg (factorTwoAffineCosXQ m - 5 / 4)]
  simpa only [factorTwoAffineCosUnweightedKernelInterval,
    factorTwoAffineCosYSqInterval, factorTwoAffineCosDenomInterval] using
      (affineCos_kernelExpression_metrics n
        (factorTwoAffineCosXQ m ^ 2) hx)

private theorem affineCosInitialKernelInterval_metrics (n : ℕ) :
    (factorTwoAffineCosInitialKernelInterval n).Valid ∧
      (factorTwoAffineCosInitialKernelInterval n).AbsBound 24 ∧
      width (factorTwoAffineCosInitialKernelInterval n) ≤
        (1 / 10000000000000 : ℚ) := by
  simpa only [factorTwoAffineCosInitialKernelInterval] using
    (affineCos_kernelExpression_metrics n ((1 / 4 : ℚ) ^ 2) (by norm_num))

private theorem affineCosUnweightedHeadInterval_valid (n K : ℕ) :
    (factorTwoAffineCosUnweightedHeadInterval n K).Valid := by
  induction K with
  | zero => exact valid_pure 0
  | succ K ih =>
      exact valid_add ih (affineCosUnweightedKernelInterval_metrics n K).1

private theorem affineCosUnweightedHeadInterval_absBound (n K : ℕ) :
    (factorTwoAffineCosUnweightedHeadInterval n K).AbsBound
      ((K : ℚ) * 24) := by
  induction K with
  | zero =>
      simpa only [Nat.cast_zero, zero_mul] using
        (absBound_pure (q := (0 : ℚ)) (B := 0) (by norm_num))
  | succ K ih =>
      have h := absBound_add ih
        (affineCosUnweightedKernelInterval_metrics n K).2.1
      rw [factorTwoAffineCosUnweightedHeadInterval]
      rw [show (((K + 1 : ℕ) : ℚ) * 24) = (K : ℚ) * 24 + 24 by
        push_cast
        ring]
      exact h

private theorem affineCosUnweightedHeadInterval_width_le (n K : ℕ) :
    width (factorTwoAffineCosUnweightedHeadInterval n K) ≤
      (K : ℚ) / 10000000000000 := by
  have h := width_recursive_add_le_const_mul
    (factorTwoAffineCosUnweightedHeadInterval n)
    (factorTwoAffineCosUnweightedKernelInterval n)
    (by rfl) (by intro k; rfl) K
    (fun k _hk ↦ (affineCosUnweightedKernelInterval_metrics n k).2.2)
  simpa [div_eq_mul_inv] using h

private theorem affineCos_mul_lower_eq_of_nonneg
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
    · exact le_min (le_rfl)
        (mul_le_mul_of_nonneg_left hJ hI0)
    · exact le_min (mul_le_mul_of_nonneg_right hI hJ0)
        (mul_le_mul hI hJ hJ0 hIu0)

private theorem affineCos_mul_upper_eq_of_nonneg
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

private theorem affineCosTailMainInterval_metrics
    {n N : ℕ} (hn200 : n ≤ 200)
    (hden : (100000 : ℚ) ≤ (factorTwoAffineCosDenomInterval n N).lower) :
    (factorTwoAffineCosUnweightedTailMainInterval n N).Valid ∧
      (factorTwoAffineCosUnweightedTailMainInterval n N).AbsBound 2 ∧
      width (factorTwoAffineCosUnweightedTailMainInterval n N) ≤
        (2 / 1000000000000 : ℚ) := by
  let S := factorTwoAffineCosYSqInterval n
  let u : ℚ := (N : ℚ) + 1 + 1 / 4
  let U := pure u
  let U2 := pure (u ^ 2)
  let D := pure (u ^ 2) + S
  let D2 := nonnegSquare D
  let P := U / D
  let E := (S - U2) / D2
  let A := U2 - pure 3 * S
  let F := (pure 2 * U * A) / (D * D2)
  let d := D.lower
  have hnq : (n : ℚ) ≤ 200 := by exact_mod_cast hn200
  have hSvalid : S.Valid := by
    simpa only [S] using affineCosYSqInterval_valid n
  have hwS : width S ≤ (1 / 25000000 : ℚ) := by
    calc
      width S ≤ (n : ℚ) ^ 2 / 1000000000000 := by
        simpa only [S] using affineCosYSqInterval_width_le n
      _ ≤ (1 / 25000000 : ℚ) := by nlinarith [sq_nonneg (n : ℚ)]
  have hwS0 : 0 ≤ width S := width_nonneg hSvalid
  have hDdef : D = factorTwoAffineCosDenomInterval n N := by
    rfl
  have hd100 : (100000 : ℚ) ≤ d := by
    simpa only [d, hDdef] using hden
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd100
  have hDvalid : D.Valid := valid_add (valid_pure _) hSvalid
  have hwD : width D = width S := by
    dsimp only [D]
    rw [width_add, width_pure, zero_add]
  have hDupper : D.upper ≤ (3 / 2 : ℚ) * d := by
    have hwidthEq : D.upper - D.lower = width S := by
      rw [← width, hwD]
    have hwSmall : width S ≤ d / 2 := by
      linarith [hwS]
    dsimp only [d]
    linarith
  have hDabs : D.AbsBound ((3 / 2 : ℚ) * d) := by
    constructor
    · exact (neg_nonpos.mpr (by positivity)).trans hdpos.le
    · exact hDupper
  have hSabs : S.AbsBound ((3 / 2 : ℚ) * d) := by
    have hSlower : 0 ≤ S.lower := by
      dsimp only [S, factorTwoAffineCosYSqInterval, nonnegSquare]
      positivity
    constructor
    · exact (neg_nonpos.mpr (by positivity)).trans hSlower
    · have hSu : S.upper ≤ D.upper := by
        dsimp only [D]
        change S.upper ≤ u ^ 2 + S.upper
        exact le_add_of_nonneg_left (sq_nonneg u)
      exact hSu.trans hDupper
  have hD2valid : D2.Valid := by
    change D.lower ^ 2 ≤ D.upper ^ 2
    exact pow_le_pow_left₀ hdpos.le hDvalid 2
  have hD2lower : D2.lower = d ^ 2 := by rfl
  have hD2abs : D2.AbsBound ((9 / 4 : ℚ) * d ^ 2) := by
    unfold AbsBound
    change -((9 / 4 : ℚ) * d ^ 2) ≤ D.lower ^ 2 ∧
      D.upper ^ 2 ≤ (9 / 4 : ℚ) * d ^ 2
    constructor
    · nlinarith [sq_nonneg d]
    · have hu0 : 0 ≤ D.upper := hdpos.le.trans hDvalid
      have hsquare := pow_le_pow_left₀ hu0 hDupper 2
      nlinarith
  have hD2width : width D2 ≤ (5 / 2 : ℚ) * d * width S := by
    have hsum : D.upper + D.lower ≤ (5 / 2 : ℚ) * d := by
      dsimp only [d]
      linarith
    change D.upper ^ 2 - D.lower ^ 2 ≤
      (5 / 2 : ℚ) * d * width S
    rw [sq_sub_sq, ← width, hwD]
    exact mul_le_mul_of_nonneg_right hsum hwS0
  have huPos : 0 < u := by
    dsimp only [u]
    positivity
  have hu2le : u ^ 2 ≤ d := by
    have hSlower : 0 ≤ S.lower := by
      dsimp only [S, factorTwoAffineCosYSqInterval, nonnegSquare]
      positivity
    change u ^ 2 ≤ (RatInterval.pure (u ^ 2) + S).lower
    simpa only [RatInterval.add, RatInterval.pure] using
      le_add_of_nonneg_right hSlower
  have hule : u ≤ d := by
    have huOne : 1 ≤ u := by
      dsimp only [u]
      have hN : (0 : ℚ) ≤ N := by positivity
      linarith
    nlinarith [sq_nonneg (u - 1)]
  have hUvalid : U.Valid := valid_pure u
  have hUabs : U.AbsBound u := absBound_pure (abs_of_pos huPos).le
  have hPvalid : P.Valid := valid_div_of_pos hUvalid hDvalid hdpos
  have hPabsRaw : P.AbsBound (u * d⁻¹) := by
    simpa only [P] using absBound_div_of_lower hUvalid hDvalid hUabs
      huPos.le hdpos (show d ≤ D.lower by rfl)
  have hPabs : P.AbsBound 1 := by
    apply affineCos_absBound_mono hPabsRaw
    calc
      u * d⁻¹ ≤ d * d⁻¹ :=
        mul_le_mul_of_nonneg_right hule (inv_nonneg.mpr hdpos.le)
      _ = 1 := by field_simp [hdpos.ne']
  have hInvD : d⁻¹ ≤ (100000 : ℚ)⁻¹ :=
    (inv_le_inv₀ hdpos (by norm_num)).2 hd100
  have hInvD2 : (d ^ 2)⁻¹ ≤ ((100000 : ℚ) ^ 2)⁻¹ :=
    (inv_le_inv₀ (pow_pos hdpos 2) (by norm_num)).2
      (pow_le_pow_left₀ (by norm_num) hd100 2)
  have hPwidth : width P ≤ (1 / 2000000000000 : ℚ) := by
    have hraw := width_div_le_of_lower hUvalid hDvalid hUabs huPos.le
      hdpos (show d ≤ D.lower by rfl)
    have hwU : width U = 0 := width_pure u
    calc
      width P ≤ d⁻¹ * width U + u * (width D / (d * d)) := by
        simpa only [P] using hraw
      _ = u * (width S / (d * d)) := by rw [hwU, hwD]; ring
      _ ≤ d * ((1 / 25000000 : ℚ) / (d * d)) := by
        exact mul_le_mul hule
          (div_le_div_of_nonneg_right hwS (by positivity))
          (by positivity) hdpos.le
      _ = (1 / 25000000 : ℚ) * d⁻¹ := by
        field_simp [hdpos.ne']
      _ ≤ (1 / 25000000 : ℚ) * (100000 : ℚ)⁻¹ :=
        mul_le_mul_of_nonneg_left hInvD (by norm_num)
      _ ≤ (1 / 2000000000000 : ℚ) := by norm_num
  have hEinnerValid : (S - U2).Valid := valid_sub hSvalid (valid_pure _)
  have hEinnerAbs : (S - U2).AbsBound ((5 / 2 : ℚ) * d) := by
    have hU2abs : U2.AbsBound d :=
      affineCos_absBound_mono
        (absBound_pure (show |u ^ 2| ≤ u ^ 2 by rw [abs_of_nonneg]; positivity))
        hu2le
    have h := absBound_sub hSabs hU2abs
    have heq : (3 / 2 : ℚ) * d + d = (5 / 2 : ℚ) * d := by ring
    rw [← heq]
    exact h
  have hEvalid : E.Valid := by
    apply valid_div_of_pos hEinnerValid hD2valid
    rw [hD2lower]
    positivity
  have hEabsRaw : E.AbsBound
      (((5 / 2 : ℚ) * d) * (d ^ 2)⁻¹) := by
    apply absBound_div_of_lower hEinnerValid hD2valid hEinnerAbs
      (by positivity) (pow_pos hdpos 2)
    rw [hD2lower]
  have hEabs : E.AbsBound 1 := by
    apply affineCos_absBound_mono hEabsRaw
    calc
      ((5 / 2 : ℚ) * d) * (d ^ 2)⁻¹ = (5 / 2 : ℚ) * d⁻¹ := by
        field_simp [hdpos.ne']
      _ ≤ (5 / 2 : ℚ) * (100000 : ℚ)⁻¹ :=
        mul_le_mul_of_nonneg_left hInvD (by norm_num)
      _ ≤ 1 := by norm_num
  have hEwidth : width E ≤ (1 / 1000000000000 : ℚ) := by
    have hraw := width_div_le_of_lower hEinnerValid hD2valid hEinnerAbs
      (by positivity : (0 : ℚ) ≤ (5 / 2 : ℚ) * d) (pow_pos hdpos 2)
      (show d ^ 2 ≤ D2.lower by rw [hD2lower])
    have hwInner : width (S - U2) = width S := by
      dsimp only [U2]
      rw [width_sub, width_pure, add_zero]
    calc
      width E ≤ (d ^ 2)⁻¹ * width (S - U2) +
          ((5 / 2 : ℚ) * d) * (width D2 / (d ^ 2 * d ^ 2)) := by
        simpa only [E, hD2lower] using hraw
      _ ≤ (d ^ 2)⁻¹ * width S +
          ((5 / 2 : ℚ) * d) *
            (((5 / 2 : ℚ) * d * width S) / (d ^ 2 * d ^ 2)) := by
        rw [hwInner]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hD2width (by positivity))
          (by positivity))
      _ = (29 / 4 : ℚ) * width S / d ^ 2 := by
        field_simp [hdpos.ne']
        ring
      _ ≤ (29 / 4 : ℚ) * (1 / 25000000 : ℚ) *
          ((100000 : ℚ) ^ 2)⁻¹ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hwS (by norm_num)) hInvD2
          (inv_nonneg.mpr (sq_nonneg d)) (by norm_num)
      _ ≤ (1 / 1000000000000 : ℚ) := by norm_num
  have hAvalid : A.Valid := valid_sub (valid_pure _)
    (valid_mul (valid_pure 3) hSvalid)
  have hAabs : A.AbsBound ((11 / 2 : ℚ) * d) := by
    have h3Sabs : (RatInterval.pure 3 * S).AbsBound
        ((9 / 2 : ℚ) * d) := by
      have h := absBound_mul (valid_pure 3) hSvalid
        (absBound_pure (q := (3 : ℚ)) (B := 3) (by norm_num)) hSabs
        (by norm_num) (by positivity : (0 : ℚ) ≤ (3 / 2 : ℚ) * d)
      have heq : (3 : ℚ) * ((3 / 2 : ℚ) * d) = (9 / 2 : ℚ) * d := by
        ring
      rw [← heq]
      exact h
    have hU2abs : U2.AbsBound d :=
      affineCos_absBound_mono
        (absBound_pure (show |u ^ 2| ≤ u ^ 2 by rw [abs_of_nonneg]; positivity))
        hu2le
    have h := absBound_sub hU2abs h3Sabs
    have heq : d + (9 / 2 : ℚ) * d = (11 / 2 : ℚ) * d := by ring
    rw [← heq]
    simpa only [A] using h
  have hNumValid : (RatInterval.pure 2 * U * A).Valid :=
    valid_mul (valid_mul (valid_pure 2) hUvalid) hAvalid
  have hNumAbs : (RatInterval.pure 2 * U * A).AbsBound
      (11 * d ^ 2) := by
    have h2Uabs : (RatInterval.pure 2 * U).AbsBound (2 * d) := by
      have h := absBound_mul (valid_pure 2) hUvalid
        (absBound_pure (q := (2 : ℚ)) (B := 2) (by norm_num)) hUabs
        (by norm_num) huPos.le
      exact affineCos_absBound_mono h (by nlinarith)
    have h := absBound_mul (valid_mul (valid_pure 2) hUvalid) hAvalid
      h2Uabs hAabs (by positivity) (by positivity)
    have heq : (2 * d) * ((11 / 2 : ℚ) * d) = 11 * d ^ 2 := by ring
    rw [← heq]
    exact h
  have hNumWidth : width (RatInterval.pure 2 * U * A) ≤
      11 * d * width S := by
    have h3Swidth : width (RatInterval.pure 3 * S) = 3 * width S := by
      rw [width_pure_mul 3 hSvalid, abs_of_nonneg (by norm_num)]
    have hAwidth : width A = 3 * width S := by
      dsimp only [A, U2]
      rw [width_sub, width_pure, zero_add, h3Swidth]
    have h2Uvalid : (RatInterval.pure 2 * U).Valid :=
      valid_mul (valid_pure 2) hUvalid
    have h2Uwidth : width (RatInterval.pure 2 * U) = 0 := by
      rw [width_pure_mul 2 hUvalid, width_pure, mul_zero]
    have hmul := width_mul_le h2Uvalid hAvalid
      (affineCos_absBound_mono
        (absBound_mul (valid_pure 2) hUvalid
          (absBound_pure (q := (2 : ℚ)) (B := 2) (by norm_num)) hUabs
          (by norm_num) huPos.le) (by nlinarith : 2 * u ≤ 2 * d))
      hAabs (by positivity : (0 : ℚ) ≤ 2 * d)
      (by positivity : (0 : ℚ) ≤ (11 / 2 : ℚ) * d)
    calc
      width (RatInterval.pure 2 * U * A) ≤
          ((11 / 2 : ℚ) * d) * width (RatInterval.pure 2 * U) +
            (2 * d) * width A := hmul
      _ = 6 * d * width S := by rw [h2Uwidth, hAwidth]; ring
      _ ≤ 11 * d * width S := by
        have hdw : 0 ≤ d * width S := mul_nonneg hdpos.le hwS0
        linarith
  have hDenValid : (D * D2).Valid := valid_mul hDvalid hD2valid
  have hDenLower : (D * D2).lower = d ^ 3 := by
    rw [affineCos_mul_lower_eq_of_nonneg hDvalid hD2valid hdpos.le (by
      rw [hD2lower]
      positivity), hD2lower]
    ring
  have hDenAbs : (D * D2).AbsBound ((27 / 8 : ℚ) * d ^ 3) := by
    have h := absBound_mul hDvalid hD2valid hDabs hD2abs
      (by positivity : (0 : ℚ) ≤ (3 / 2 : ℚ) * d)
      (by positivity : (0 : ℚ) ≤ (9 / 4 : ℚ) * d ^ 2)
    convert h using 1
    ring
  have hDenWidth : width (D * D2) ≤ 6 * d ^ 2 * width S := by
    have h := width_mul_le hDvalid hD2valid hDabs hD2abs
      (by positivity : (0 : ℚ) ≤ (3 / 2 : ℚ) * d)
      (by positivity : (0 : ℚ) ≤ (9 / 4 : ℚ) * d ^ 2)
    calc
      width (D * D2) ≤
          ((9 / 4 : ℚ) * d ^ 2) * width D +
            ((3 / 2 : ℚ) * d) * width D2 := h
      _ ≤ ((9 / 4 : ℚ) * d ^ 2) * width S +
          ((3 / 2 : ℚ) * d) * ((5 / 2 : ℚ) * d * width S) := by
        rw [hwD]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hD2width (by positivity))
      _ = 6 * d ^ 2 * width S := by ring
  have hFvalid : F.Valid := by
    apply valid_div_of_pos hNumValid hDenValid
    rw [hDenLower]
    positivity
  have hFabsRaw : F.AbsBound ((11 * d ^ 2) * (d ^ 3)⁻¹) := by
    apply absBound_div_of_lower hNumValid hDenValid hNumAbs
      (by positivity) (pow_pos hdpos 3)
    rw [hDenLower]
  have hFabs : F.AbsBound 1 := by
    apply affineCos_absBound_mono hFabsRaw
    calc
      (11 * d ^ 2) * (d ^ 3)⁻¹ = 11 * d⁻¹ := by
        field_simp [hdpos.ne']
      _ ≤ 11 * (100000 : ℚ)⁻¹ :=
        mul_le_mul_of_nonneg_left hInvD (by norm_num)
      _ ≤ 1 := by norm_num
  have hFwidth : width F ≤ (1 / 1000000000000 : ℚ) := by
    have hraw := width_div_le_of_lower hNumValid hDenValid hNumAbs
      (by positivity : (0 : ℚ) ≤ 11 * d ^ 2) (pow_pos hdpos 3)
      (show d ^ 3 ≤ (D * D2).lower by rw [hDenLower])
    calc
      width F ≤ (d ^ 3)⁻¹ * width (RatInterval.pure 2 * U * A) +
          (11 * d ^ 2) * (width (D * D2) / (d ^ 3 * d ^ 3)) := by
        simpa only [F, hDenLower] using hraw
      _ ≤ (d ^ 3)⁻¹ * (11 * d * width S) +
          (11 * d ^ 2) *
            ((6 * d ^ 2 * width S) / (d ^ 3 * d ^ 3)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hNumWidth (by positivity))
          (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hDenWidth (by positivity))
            (by positivity))
      _ = 77 * width S / d ^ 2 := by
        field_simp [hdpos.ne']
        ring
      _ ≤ 77 * (1 / 25000000 : ℚ) * ((100000 : ℚ) ^ 2)⁻¹ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hwS (by norm_num)) hInvD2
          (inv_nonneg.mpr (sq_nonneg d)) (by norm_num)
      _ ≤ (1 / 1000000000000 : ℚ) := by norm_num
  have hTwoValid : (RatInterval.pure (2 : ℚ)).Valid := valid_pure 2
  have hTwelveValid : (RatInterval.pure (12 : ℚ)).Valid := valid_pure 12
  have hEhalfValid : (E / RatInterval.pure 2).Valid :=
    valid_div_of_pos hEvalid hTwoValid (by norm_num [RatInterval.pure])
  have hFtwelfthValid : (F / RatInterval.pure 12).Valid :=
    valid_div_of_pos hFvalid hTwelveValid (by norm_num [RatInterval.pure])
  have hEhalfAbs : (E / RatInterval.pure 2).AbsBound (1 / 2 : ℚ) := by
    simpa using absBound_div_of_lower hEvalid hTwoValid hEabs (by norm_num)
      (by norm_num : (0 : ℚ) < 2) (by norm_num [RatInterval.pure])
  have hFtwelfthAbs : (F / RatInterval.pure 12).AbsBound
      (1 / 12 : ℚ) := by
    simpa using absBound_div_of_lower hFvalid hTwelveValid hFabs (by norm_num)
      (by norm_num : (0 : ℚ) < 12) (by norm_num [RatInterval.pure])
  have hTailValid :
      (P - E / RatInterval.pure 2 + F / RatInterval.pure 12).Valid :=
    valid_add (valid_sub hPvalid hEhalfValid) hFtwelfthValid
  have hTailAbs :
      (P - E / RatInterval.pure 2 + F / RatInterval.pure 12).AbsBound 2 := by
    apply affineCos_absBound_mono
      (absBound_add (absBound_sub hPabs hEhalfAbs) hFtwelfthAbs)
    norm_num
  have hEhalfWidth : width (E / RatInterval.pure 2) =
      (1 / 2 : ℚ) * width E := by
    change width (E * (RatInterval.pure (2 : ℚ))⁻¹) = _
    rw [show (RatInterval.pure (2 : ℚ))⁻¹ =
        RatInterval.pure ((2 : ℚ)⁻¹) by rfl,
      width_mul_pure _ hEvalid]
    norm_num
  have hFtwelfthWidth : width (F / RatInterval.pure 12) =
      (1 / 12 : ℚ) * width F := by
    change width (F * (RatInterval.pure (12 : ℚ))⁻¹) = _
    rw [show (RatInterval.pure (12 : ℚ))⁻¹ =
        RatInterval.pure ((12 : ℚ)⁻¹) by rfl,
      width_mul_pure _ hFvalid]
    norm_num
  have hTailWidth :
      width (P - E / RatInterval.pure 2 + F / RatInterval.pure 12) ≤
      (2 / 1000000000000 : ℚ) := by
    rw [width_add, width_sub, hEhalfWidth, hFtwelfthWidth]
    calc
      width P + (1 / 2 : ℚ) * width E + (1 / 12 : ℚ) * width F ≤
          (1 / 2000000000000 : ℚ) +
            (1 / 2 : ℚ) * (1 / 1000000000000 : ℚ) +
            (1 / 12 : ℚ) * (1 / 1000000000000 : ℚ) :=
        add_le_add (add_le_add hPwidth
          (mul_le_mul_of_nonneg_left hEwidth (by norm_num)))
          (mul_le_mul_of_nonneg_left hFwidth (by norm_num))
      _ ≤ (2 / 1000000000000 : ℚ) := by norm_num
  simpa only [factorTwoAffineCosUnweightedTailMainInterval,
    factorTwoAffineCosDerivativeProfileInterval,
    factorTwoAffineCosDerivativeDerivInterval,
    factorTwoAffineCosDerivativeSecondInterval, P, E, F, A, U, U2, D, D2,
    S, u] using ⟨hTailValid, hTailAbs, hTailWidth⟩

private theorem affineCosTailInterval_metrics
    {n N : ℕ} (hn200 : n ≤ 200)
    (hden : (100000 : ℚ) ≤ (factorTwoAffineCosDenomInterval n N).lower) :
    (factorTwoAffineCosUnweightedTailInterval n N).Valid ∧
      (factorTwoAffineCosUnweightedTailInterval n N).AbsBound 3 ∧
      width (factorTwoAffineCosUnweightedTailInterval n N) ≤
        (51 / 100000000000 : ℚ) := by
  let d := (factorTwoAffineCosDenomInterval n N).lower
  let r := factorTwoAffineCosDerivativeTailRadiusQ n N
  let R : RatInterval := ⟨-r, r⟩
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hden
  have hr : r = 5 / (2 * d ^ 2) := by rfl
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hRvalid : R.Valid := by
    change -r ≤ r
    linarith
  have hRabs : R.AbsBound 1 := by
    unfold AbsBound
    change -(1 : ℚ) ≤ -r ∧ r ≤ 1
    constructor
    · have : r ≤ 1 := by
        rw [hr]
        have hdSq := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 100000)
          hden 2
        rw [div_le_iff₀ (by positivity : (0 : ℚ) < 2 * d ^ 2)]
        nlinarith
      linarith
    · rw [hr]
      have hdSq := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 100000)
        hden 2
      rw [div_le_iff₀ (by positivity : (0 : ℚ) < 2 * d ^ 2)]
      nlinarith
  have hRwidth : width R ≤ (1 / 2000000000 : ℚ) := by
    change r - -r ≤ (1 / 2000000000 : ℚ)
    have hdSq := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 100000)
      hden 2
    calc
      r - -r = 5 / d ^ 2 := by
        rw [hr]
        field_simp [hdpos.ne']
        ring
      _ ≤ (1 / 2000000000 : ℚ) := by
        rw [div_le_iff₀ (pow_pos hdpos 2)]
        nlinarith
  have hmain := affineCosTailMainInterval_metrics hn200 hden
  unfold factorTwoAffineCosUnweightedTailInterval
  dsimp only [r, R] at hRvalid hRabs hRwidth
  constructor
  · exact valid_add hmain.1 hRvalid
  constructor
  · exact affineCos_absBound_mono (absBound_add hmain.2.1 hRabs) (by norm_num)
  · rw [width_add]
    change width (factorTwoAffineCosUnweightedTailMainInterval n N) +
      width R ≤ (51 / 100000000000 : ℚ)
    calc
      width (factorTwoAffineCosUnweightedTailMainInterval n N) +
          width R ≤
        (2 / 1000000000000 : ℚ) + (1 / 2000000000 : ℚ) :=
          add_le_add hmain.2.2 hRwidth
      _ ≤ (51 / 100000000000 : ℚ) := by norm_num

private theorem affineCosZeroTailInterval_metrics :
    (factorTwoAffineCosZeroTailInterval 48).Valid ∧
      (factorTwoAffineCosZeroTailInterval 48).AbsBound 1 ∧
      width (factorTwoAffineCosZeroTailInterval 48) ≤
        (1 / 5000000000 : ℚ) := by
  norm_num [factorTwoAffineCosZeroTailInterval,
    factorTwoAffineCosInvSqTailLowerQ, factorTwoAffineCosInvSqTailUpperQ,
    factorTwoAffineCosXQ, Valid, AbsBound, width]

private theorem affineCosUnweightedHeadCount_le (n : ℕ) :
    factorTwoAffineCosUnweightedHeadCount n ≤ 384 := by
  by_cases hn : n = 0
  · simp [factorTwoAffineCosUnweightedHeadCount, hn]
  · by_cases hlow : n < 70
    · simp [factorTwoAffineCosUnweightedHeadCount, hn, hlow]
    · simp [factorTwoAffineCosUnweightedHeadCount, hn, hlow]

private theorem affineCosScheduledDenom_lower
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    (100000 : ℚ) ≤
      (factorTwoAffineCosDenomInterval n.1
        (factorTwoAffineCosUnweightedHeadCount n.1)).lower := by
  by_cases hlow : n.1 < 70
  · rw [factorTwoAffineCosUnweightedHeadCount, if_neg hn, if_pos hlow]
    change (100000 : ℚ) ≤ factorTwoAffineCosXQ 384 ^ 2 +
      (factorTwoAffineCosYInterval n.1).lower ^ 2
    have hsquare : 0 ≤ (factorTwoAffineCosYInterval n.1).lower ^ 2 :=
      sq_nonneg _
    norm_num [factorTwoAffineCosXQ]
    linarith
  · rw [factorTwoAffineCosUnweightedHeadCount, if_neg hn, if_neg hlow]
    have hn70 : 70 ≤ n.1 := Nat.le_of_not_gt hlow
    have hgrowth := affineCosYInterval_lower_growth n.1
    have hn70q : (70 : ℚ) ≤ n.1 := by exact_mod_cast hn70
    change (100000 : ℚ) ≤ factorTwoAffineCosXQ 0 ^ 2 +
      (factorTwoAffineCosYInterval n.1).lower ^ 2
    have hy : (3171 / 10 : ℚ) ≤
        (factorTwoAffineCosYInterval n.1).lower := by nlinarith
    have hsquare := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 3171 / 10)
      hy 2
    norm_num [factorTwoAffineCosXQ]
    nlinarith

private theorem affineCosUnweightedSeriesInterval_metrics
    (n : FactorTwoCanonicalEvenIndex) :
    (factorTwoAffineCosUnweightedSeriesInterval n.1).Valid ∧
      (factorTwoAffineCosUnweightedSeriesInterval n.1).AbsBound 9300 ∧
      width (factorTwoAffineCosUnweightedSeriesInterval n.1) ≤
        (11 / 20000000000 : ℚ) := by
  let K := factorTwoAffineCosUnweightedHeadCount n.1
  have hn200 : n.1 ≤ 200 := Nat.le_of_lt_succ n.isLt
  have hK384 : K ≤ 384 := affineCosUnweightedHeadCount_le n.1
  have hHeadValid := affineCosUnweightedHeadInterval_valid n.1 K
  have hHeadAbs := affineCosUnweightedHeadInterval_absBound n.1 K
  have hHeadWidth := affineCosUnweightedHeadInterval_width_le n.1 K
  have hHeadAbs9300 :
      (factorTwoAffineCosUnweightedHeadInterval n.1 K).AbsBound 9290 := by
    apply affineCos_absBound_mono hHeadAbs
    have hKq : (K : ℚ) ≤ 384 := by exact_mod_cast hK384
    nlinarith
  have hHeadWidth384 :
      width (factorTwoAffineCosUnweightedHeadInterval n.1 K) ≤
        (384 / 10000000000000 : ℚ) := by
    exact hHeadWidth.trans (by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hK384) (by norm_num))
  by_cases hn : n.1 = 0
  · have hK : K = 48 := by simp [K, factorTwoAffineCosUnweightedHeadCount, hn]
    have hzero := affineCosZeroTailInterval_metrics
    rw [factorTwoAffineCosUnweightedSeriesInterval]
    rw [if_pos hn]
    rw [hK] at hHeadValid hHeadAbs9300 hHeadWidth384
    rw [show factorTwoAffineCosUnweightedHeadCount n.1 = 48 by
      simp [factorTwoAffineCosUnweightedHeadCount, hn]]
    constructor
    · exact valid_add hHeadValid hzero.1
    constructor
    · exact affineCos_absBound_mono (absBound_add hHeadAbs9300 hzero.2.1)
        (by norm_num)
    · rw [width_add]
      calc
        width (factorTwoAffineCosUnweightedHeadInterval n.1 48) +
            width (factorTwoAffineCosZeroTailInterval 48) ≤
          (384 / 10000000000000 : ℚ) + (1 / 5000000000 : ℚ) :=
            add_le_add hHeadWidth384 hzero.2.2
        _ ≤ (11 / 20000000000 : ℚ) := by norm_num
  · have htail := affineCosTailInterval_metrics hn200
      (affineCosScheduledDenom_lower n hn)
    rw [factorTwoAffineCosUnweightedSeriesInterval]
    rw [if_neg hn]
    dsimp only [K] at hHeadValid hHeadAbs9300 hHeadWidth384 ⊢
    constructor
    · exact valid_add hHeadValid htail.1
    constructor
    · exact affineCos_absBound_mono (absBound_add hHeadAbs9300 htail.2.1)
        (by norm_num)
    · rw [width_add]
      calc
        width (factorTwoAffineCosUnweightedHeadInterval n.1
              (factorTwoAffineCosUnweightedHeadCount n.1)) +
            width (factorTwoAffineCosUnweightedTailInterval n.1
              (factorTwoAffineCosUnweightedHeadCount n.1)) ≤
          (384 / 10000000000000 : ℚ) + (51 / 100000000000 : ℚ) :=
            add_le_add hHeadWidth384 htail.2.2
        _ ≤ (11 / 20000000000 : ℚ) := by norm_num

private theorem affineCosDyadicQInterval_metrics (k : ℕ) :
    (factorTwoAffineCosDyadicQInterval k).Valid ∧
      (factorTwoAffineCosDyadicQInterval k).AbsBound 1 ∧
      0 ≤ (factorTwoAffineCosDyadicQInterval k).lower ∧
      width (factorTwoAffineCosDyadicQInterval k) ≤
        (1 / 1000000000000000 : ℚ) := by
  have hsValid : sqrtTwoInterval.Valid := valid_of_contains sqrtTwoInterval_contains
  have hsLower : (1 : ℚ) ≤ sqrtTwoInterval.lower := by
    norm_num [sqrtTwoInterval]
  have hsPos : 0 < sqrtTwoInterval.lower := lt_of_lt_of_le (by norm_num) hsLower
  have hsInvValid : sqrtTwoInterval⁻¹.Valid := valid_inv_of_pos hsValid hsPos
  have hsInvAbs : sqrtTwoInterval⁻¹.AbsBound 1 := by
    simpa only [inv_one] using
      absBound_inv_of_lower hsValid (by norm_num) hsLower
  have hsInvWidth : width sqrtTwoInterval⁻¹ ≤
      (1 / 1000000000000000 : ℚ) := by
    calc
      width sqrtTwoInterval⁻¹ ≤ width sqrtTwoInterval / ((1 : ℚ) * 1) :=
        width_inv_le_of_lower hsValid (by norm_num) hsLower
      _ = (1 / 1000000000000000 : ℚ) := by
        norm_num [width, sqrtTwoInterval]
  have hpowPos : (0 : ℚ) < (4 : ℚ) ^ k := by positivity
  have hpowOne : (1 : ℚ) ≤ (4 : ℚ) ^ k := one_le_pow₀ (by norm_num)
  have hPointValid : (RatInterval.pure ((4 : ℚ) ^ k)).Valid := valid_pure _
  have hQValid : (sqrtTwoInterval⁻¹ /
      RatInterval.pure ((4 : ℚ) ^ k)).Valid :=
    valid_div_of_pos hsInvValid hPointValid (by
      change 0 < (4 : ℚ) ^ k
      exact hpowPos)
  have hQAbs : (sqrtTwoInterval⁻¹ /
      RatInterval.pure ((4 : ℚ) ^ k)).AbsBound 1 := by
    simpa using absBound_div_of_lower hsInvValid hPointValid hsInvAbs
      (by norm_num) (by norm_num : (0 : ℚ) < 1) hpowOne
  have hQlower : 0 ≤ (sqrtTwoInterval⁻¹ /
      RatInterval.pure ((4 : ℚ) ^ k)).lower := by
    change 0 ≤ (sqrtTwoInterval⁻¹ *
      (RatInterval.pure ((4 : ℚ) ^ k))⁻¹).lower
    exact mul_lower_nonneg_of_nonneg (by
      change 0 ≤ sqrtTwoInterval.upper⁻¹
      norm_num [sqrtTwoInterval]) (by
        change 0 ≤ ((4 : ℚ) ^ k)⁻¹
        positivity) hsInvValid (valid_inv_of_pos hPointValid (by
          change 0 < (4 : ℚ) ^ k
          exact hpowPos))
  have hQWidth : width (sqrtTwoInterval⁻¹ /
      RatInterval.pure ((4 : ℚ) ^ k)) ≤
      (1 / 1000000000000000 : ℚ) := by
    change width (sqrtTwoInterval⁻¹ *
      (RatInterval.pure ((4 : ℚ) ^ k))⁻¹) ≤ _
    rw [show (RatInterval.pure ((4 : ℚ) ^ k))⁻¹ =
        RatInterval.pure (((4 : ℚ) ^ k)⁻¹) by rfl,
      width_mul_pure _ hsInvValid, abs_of_nonneg (by positivity)]
    calc
      ((4 : ℚ) ^ k)⁻¹ * width sqrtTwoInterval⁻¹ ≤
          1 * width sqrtTwoInterval⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          ((inv_le_one₀ hpowPos).2 hpowOne) (width_nonneg hsInvValid)
      _ ≤ (1 / 1000000000000000 : ℚ) := by simpa using hsInvWidth
  simpa only [factorTwoAffineCosDyadicQInterval] using
    ⟨hQValid, hQAbs, hQlower, hQWidth⟩

private theorem affineCosDyadicDInterval_metrics (k : ℕ) :
    (factorTwoAffineCosDyadicDInterval k).Valid ∧
      (factorTwoAffineCosDyadicDInterval k).AbsBound 1 ∧
      width (factorTwoAffineCosDyadicDInterval k) ≤
        (2 / 1000000000000000 : ℚ) := by
  let Q := factorTwoAffineCosDyadicQInterval k
  let F := RatInterval.pure 1 - Q
  have hQ := affineCosDyadicQInterval_metrics k
  have hFvalid : F.Valid := valid_sub (valid_pure 1) hQ.1
  have hFabs : F.AbsBound 1 := by
    unfold AbsBound
    change -(1 : ℚ) ≤ 1 - Q.upper ∧ 1 - Q.lower ≤ 1
    constructor
    · linarith [hQ.2.1.2]
    · linarith [hQ.2.2.1]
  have hFwidth : width F ≤ (1 / 1000000000000000 : ℚ) := by
    dsimp only [F]
    rw [width_sub, width_pure, zero_add]
    exact hQ.2.2.2
  have hDvalid : (F * F).Valid := valid_mul hFvalid hFvalid
  have hDabs : (F * F).AbsBound 1 := by
    simpa using absBound_mul hFvalid hFvalid hFabs hFabs
      (by norm_num) (by norm_num)
  have hDwidth : width (F * F) ≤
      (2 / 1000000000000000 : ℚ) := by
    calc
      width (F * F) ≤ 1 * width F + 1 * width F :=
        width_mul_le hFvalid hFvalid hFabs hFabs (by norm_num) (by norm_num)
      _ ≤ 1 * (1 / 1000000000000000 : ℚ) +
          1 * (1 / 1000000000000000 : ℚ) :=
        add_le_add (mul_le_mul_of_nonneg_left hFwidth (by norm_num))
          (mul_le_mul_of_nonneg_left hFwidth (by norm_num))
      _ = (2 / 1000000000000000 : ℚ) := by norm_num
  simpa only [factorTwoAffineCosDyadicDInterval, Q, F] using
    ⟨hDvalid, hDabs, hDwidth⟩

private theorem affineCosDyadicCorrectionInterval_metrics (n m : ℕ) :
    (factorTwoAffineCosDyadicCorrectionInterval n m).Valid ∧
      (factorTwoAffineCosDyadicCorrectionInterval n m).AbsBound 48 ∧
      width (factorTwoAffineCosDyadicCorrectionInterval n m) ≤
        (1 / 4000000000000 : ℚ) := by
  let A := factorTwoAffineCosDyadicDInterval (m + 1) - RatInterval.pure 1
  let T := factorTwoAffineCosUnweightedKernelInterval n m
  have hD := affineCosDyadicDInterval_metrics (m + 1)
  have hAvalid : A.Valid := valid_sub hD.1 (valid_pure 1)
  have hAabs : A.AbsBound 2 := by
    have h := absBound_sub hD.2.1
      (absBound_pure (q := (1 : ℚ)) (B := 1) (by norm_num))
    have heq : (1 : ℚ) + 1 = 2 := by norm_num
    rw [← heq]
    simpa only [A] using h
  have hAwidth : width A ≤ (2 / 1000000000000000 : ℚ) := by
    dsimp only [A]
    rw [width_sub, width_pure, add_zero]
    exact hD.2.2
  have hT := affineCosUnweightedKernelInterval_metrics n m
  have hvalid : (A * T).Valid := valid_mul hAvalid hT.1
  have habs : (A * T).AbsBound 48 := by
    have h := absBound_mul hAvalid hT.1 hAabs hT.2.1
      (by norm_num) (by norm_num)
    have heq : (2 : ℚ) * 24 = 48 := by norm_num
    rw [← heq]
    simpa only [T] using h
  have hwidth : width (A * T) ≤ (1 / 4000000000000 : ℚ) := by
    calc
      width (A * T) ≤ 24 * width A + 2 * width T :=
        width_mul_le hAvalid hT.1 hAabs hT.2.1 (by norm_num) (by norm_num)
      _ ≤ 24 * (2 / 1000000000000000 : ℚ) +
          2 * (1 / 10000000000000 : ℚ) :=
        add_le_add (mul_le_mul_of_nonneg_left hAwidth (by norm_num))
          (mul_le_mul_of_nonneg_left hT.2.2 (by norm_num))
      _ ≤ (1 / 4000000000000 : ℚ) := by norm_num
  simpa only [factorTwoAffineCosDyadicCorrectionInterval, A, T] using
    ⟨hvalid, habs, hwidth⟩

private theorem affineCosDyadicCorrectionHeadInterval_metrics (n K : ℕ) :
    (factorTwoAffineCosDyadicCorrectionHeadInterval n K).Valid ∧
      (factorTwoAffineCosDyadicCorrectionHeadInterval n K).AbsBound
        ((K : ℚ) * 48) ∧
      width (factorTwoAffineCosDyadicCorrectionHeadInterval n K) ≤
        (K : ℚ) / 4000000000000 := by
  have hvalid : (factorTwoAffineCosDyadicCorrectionHeadInterval n K).Valid := by
    induction K with
    | zero => exact valid_pure 0
    | succ K ih =>
        exact valid_add ih (affineCosDyadicCorrectionInterval_metrics n K).1
  have habs : (factorTwoAffineCosDyadicCorrectionHeadInterval n K).AbsBound
      ((K : ℚ) * 48) := by
    clear hvalid
    induction K with
    | zero =>
        simpa using absBound_pure (q := (0 : ℚ)) (B := 0) (by norm_num)
    | succ K ih =>
        have h := absBound_add ih
          (affineCosDyadicCorrectionInterval_metrics n K).2.1
        rw [factorTwoAffineCosDyadicCorrectionHeadInterval]
        rw [show (((K + 1 : ℕ) : ℚ) * 48) = (K : ℚ) * 48 + 48 by
          push_cast
          ring]
        exact h
  have hwidth := width_recursive_add_le_const_mul
    (factorTwoAffineCosDyadicCorrectionHeadInterval n)
    (factorTwoAffineCosDyadicCorrectionInterval n)
    (by rfl) (by intro k; rfl) K
    (fun k _hk ↦ (affineCosDyadicCorrectionInterval_metrics n k).2.2)
  refine ⟨hvalid, habs, ?_⟩
  simpa [div_eq_mul_inv] using hwidth

private theorem affineCosDyadicCorrectionSeriesInterval_metrics (n : ℕ) :
    (factorTwoAffineCosDyadicCorrectionSeriesInterval n).Valid ∧
      (factorTwoAffineCosDyadicCorrectionSeriesInterval n).AbsBound 961 ∧
      width (factorTwoAffineCosDyadicCorrectionSeriesInterval n) ≤
        (7 / 1000000000000 : ℚ) := by
  have hhead := affineCosDyadicCorrectionHeadInterval_metrics n 20
  have htailValid : (factorTwoAffineCosDyadicCorrectionTailInterval 20).Valid := by
    norm_num [factorTwoAffineCosDyadicCorrectionTailInterval,
      factorTwoAffineCosDyadicCorrectionTailRadiusQ, Valid]
  have htailAbs : (factorTwoAffineCosDyadicCorrectionTailInterval 20).AbsBound 1 := by
    norm_num [factorTwoAffineCosDyadicCorrectionTailInterval,
      factorTwoAffineCosDyadicCorrectionTailRadiusQ, AbsBound]
  have htailWidth : width (factorTwoAffineCosDyadicCorrectionTailInterval 20) ≤
      (2 / 1000000000000 : ℚ) := by
    norm_num [factorTwoAffineCosDyadicCorrectionTailInterval,
      factorTwoAffineCosDyadicCorrectionTailRadiusQ, width]
  unfold factorTwoAffineCosDyadicCorrectionSeriesInterval
  constructor
  · exact valid_add hhead.1 htailValid
  constructor
  · exact affineCos_absBound_mono (absBound_add hhead.2.1 htailAbs)
      (by norm_num)
  · rw [width_add]
    calc
      width (factorTwoAffineCosDyadicCorrectionHeadInterval n 20) +
          width (factorTwoAffineCosDyadicCorrectionTailInterval 20) ≤
        (20 / 4000000000000 : ℚ) + (2 / 1000000000000 : ℚ) :=
          add_le_add hhead.2.2 htailWidth
      _ = (7 / 1000000000000 : ℚ) := by norm_num

private theorem affineCosDyadicSeriesInterval_metrics
    (n : FactorTwoCanonicalEvenIndex) :
    (factorTwoAffineCosDyadicSeriesInterval n.1).Valid ∧
      (factorTwoAffineCosDyadicSeriesInterval n.1).AbsBound 11000 ∧
      width (factorTwoAffineCosDyadicSeriesInterval n.1) ≤
        (57 / 100000000000 : ℚ) := by
  have hmain := affineCosUnweightedSeriesInterval_metrics n
  have hcorr := affineCosDyadicCorrectionSeriesInterval_metrics n.1
  unfold factorTwoAffineCosDyadicSeriesInterval
  constructor
  · exact valid_add hmain.1 hcorr.1
  constructor
  · exact affineCos_absBound_mono (absBound_add hmain.2.1 hcorr.2.1)
      (by norm_num)
  · rw [width_add]
    calc
      width (factorTwoAffineCosUnweightedSeriesInterval n.1) +
          width (factorTwoAffineCosDyadicCorrectionSeriesInterval n.1) ≤
        (11 / 20000000000 : ℚ) + (7 / 1000000000000 : ℚ) :=
          add_le_add hmain.2.2 hcorr.2.2
      _ ≤ (57 / 100000000000 : ℚ) := by norm_num

private theorem affineCosTwoLengthInterval_metrics :
    factorTwoAffineCosTwoLengthInterval.Valid ∧
      factorTwoAffineCosTwoLengthInterval.AbsBound 2 ∧
      (1 : ℚ) ≤ factorTwoAffineCosTwoLengthInterval.lower ∧
      width factorTwoAffineCosTwoLengthInterval =
        (2 / 100000000000000 : ℚ) := by
  have hLogValid : factorTwoPrimeLogTwoInterval.Valid :=
    valid_of_contains factorTwoPrimeLogTwoInterval_contains
  have hLogAbs : factorTwoPrimeLogTwoInterval.AbsBound 1 := by
    norm_num [factorTwoPrimeLogTwoInterval, AbsBound]
  have hTwoAbs : (RatInterval.pure (2 : ℚ)).AbsBound 2 :=
    absBound_pure (by norm_num)
  have hvalid := valid_mul (valid_pure 2) hLogValid
  have habs := absBound_mul (valid_pure 2) hLogValid hTwoAbs hLogAbs
    (by norm_num) (by norm_num)
  have hlower : (RatInterval.pure 2 * factorTwoPrimeLogTwoInterval).lower =
      2 * factorTwoPrimeLogTwoInterval.lower :=
    affineCos_mul_lower_eq_of_nonneg (valid_pure 2) hLogValid
      (by norm_num [RatInterval.pure]) (by
        norm_num [factorTwoPrimeLogTwoInterval])
  have hwidth : width (RatInterval.pure 2 * factorTwoPrimeLogTwoInterval) =
      (2 / 100000000000000 : ℚ) := by
    rw [width_pure_mul 2 hLogValid, abs_of_nonneg (by norm_num)]
    norm_num [width, factorTwoPrimeLogTwoInterval]
  have habs' : (RatInterval.pure 2 * factorTwoPrimeLogTwoInterval).AbsBound 2 := by
    simpa only [mul_one] using habs
  simpa only [factorTwoAffineCosTwoLengthInterval] using
    ⟨hvalid, habs', (show (1 : ℚ) ≤
      (RatInterval.pure 2 * factorTwoPrimeLogTwoInterval).lower by
        rw [hlower]
        norm_num [factorTwoPrimeLogTwoInterval]), hwidth⟩

private theorem affineCosHeadCoefficient_metrics :
    (factorTwoHeadDefectInterval /
      factorTwoAffineCosTwoLengthInterval).Valid ∧
    (factorTwoHeadDefectInterval /
      factorTwoAffineCosTwoLengthInterval).AbsBound 1 ∧
    width (factorTwoHeadDefectInterval /
      factorTwoAffineCosTwoLengthInterval) ≤
      (4 / 100000000000000 : ℚ) := by
  have hD := affineCosTwoLengthInterval_metrics
  have hHvalid : factorTwoHeadDefectInterval.Valid :=
    valid_of_contains factorTwoHeadDefectInterval_contains
  have hHabs : factorTwoHeadDefectInterval.AbsBound 1 := by
    let F := sqrtTwoInterval - RatInterval.pure 1
    have hsValid : sqrtTwoInterval.Valid := valid_of_contains sqrtTwoInterval_contains
    have hFvalid : F.Valid := valid_sub hsValid (valid_pure 1)
    have hFabs : F.AbsBound 1 := by
      unfold AbsBound
      change -(1 : ℚ) ≤ sqrtTwoInterval.lower - 1 ∧
        sqrtTwoInterval.upper - 1 ≤ 1
      norm_num [sqrtTwoInterval]
    simpa only [factorTwoHeadDefectInterval, F, one_mul] using
      absBound_mul hFvalid hFvalid hFabs hFabs (by norm_num) (by norm_num)
  have hHwidth : width factorTwoHeadDefectInterval ≤
      (1 / 100000000000000 : ℚ) :=
    factorTwoPerturbationConstantIntervals_width_le.2.2
  have hvalid := valid_div_of_pos hHvalid hD.1
    (lt_of_lt_of_le (by norm_num) hD.2.2.1)
  have habs := absBound_div_of_lower hHvalid hD.1 hHabs (by norm_num)
    (by norm_num : (0 : ℚ) < 1) hD.2.2.1
  have hwidth := width_div_le_of_lower hHvalid hD.1 hHabs (by norm_num)
    (by norm_num : (0 : ℚ) < 1) hD.2.2.1
  refine ⟨hvalid, ?_, ?_⟩
  · simpa using habs
  · calc
      width (factorTwoHeadDefectInterval /
          factorTwoAffineCosTwoLengthInterval) ≤
        (1 : ℚ)⁻¹ * width factorTwoHeadDefectInterval +
          1 * (width factorTwoAffineCosTwoLengthInterval / (1 * 1)) := hwidth
      _ ≤ (1 : ℚ)⁻¹ * (1 / 100000000000000 : ℚ) +
          1 * ((2 / 100000000000000 : ℚ) / (1 * 1)) := by
        rw [hD.2.2.2]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hHwidth (by norm_num)) le_rfl
      _ ≤ (4 / 100000000000000 : ℚ) := by norm_num

private theorem affineCosSeriesCoefficient_metrics :
    (RatInterval.pure 1 / factorTwoAffineCosTwoLengthInterval).Valid ∧
      (RatInterval.pure 1 / factorTwoAffineCosTwoLengthInterval).AbsBound 1 ∧
      width (RatInterval.pure 1 / factorTwoAffineCosTwoLengthInterval) ≤
        (2 / 100000000000000 : ℚ) := by
  have hD := affineCosTwoLengthInterval_metrics
  have hvalid := valid_div_of_pos (valid_pure 1) hD.1
    (lt_of_lt_of_le (by norm_num) hD.2.2.1)
  have habs := absBound_div_of_lower (valid_pure 1) hD.1
    (absBound_pure (q := (1 : ℚ)) (B := 1) (by norm_num)) (by norm_num)
    (by norm_num : (0 : ℚ) < 1) hD.2.2.1
  have hwidth := width_div_le_of_lower (valid_pure 1) hD.1
    (absBound_pure (q := (1 : ℚ)) (B := 1) (by norm_num)) (by norm_num)
    (by norm_num : (0 : ℚ) < 1) hD.2.2.1
  refine ⟨hvalid, by simpa using habs, ?_⟩
  calc
    width (RatInterval.pure 1 / factorTwoAffineCosTwoLengthInterval) ≤
        (1 : ℚ)⁻¹ * width (RatInterval.pure 1) +
          1 * (width factorTwoAffineCosTwoLengthInterval / (1 * 1)) := hwidth
    _ = width factorTwoAffineCosTwoLengthInterval := by
      rw [width_pure]
      ring
    _ = (2 / 100000000000000 : ℚ) := hD.2.2.2

private theorem affineCosBaseInterval_metrics :
    ((RatInterval.pure 2 * factorTwoPrimeLogTwoInterval) /
      sqrtTwoInterval).Valid ∧
    ((RatInterval.pure 2 * factorTwoPrimeLogTwoInterval) /
      sqrtTwoInterval).AbsBound 2 ∧
    width ((RatInterval.pure 2 * factorTwoPrimeLogTwoInterval) /
      sqrtTwoInterval) ≤ (3 / 100000000000000 : ℚ) := by
  let L := RatInterval.pure 2 * factorTwoPrimeLogTwoInterval
  have hLmetrics := affineCosTwoLengthInterval_metrics
  have hLvalid : L.Valid := by
    simpa only [L, factorTwoAffineCosTwoLengthInterval] using hLmetrics.1
  have hLabs : L.AbsBound 2 := by
    simpa only [L, factorTwoAffineCosTwoLengthInterval] using hLmetrics.2.1
  have hLwidth : width L = (2 / 100000000000000 : ℚ) := by
    simpa only [L, factorTwoAffineCosTwoLengthInterval] using hLmetrics.2.2.2
  have hsValid : sqrtTwoInterval.Valid := valid_of_contains sqrtTwoInterval_contains
  have hsLower : (1 : ℚ) ≤ sqrtTwoInterval.lower := by
    norm_num [sqrtTwoInterval]
  have hsWidth : width sqrtTwoInterval =
      (1 / 1000000000000000 : ℚ) := by norm_num [width, sqrtTwoInterval]
  have hvalid := valid_div_of_pos hLvalid hsValid
    (lt_of_lt_of_le (by norm_num) hsLower)
  have habs := absBound_div_of_lower hLvalid hsValid hLabs (by norm_num)
    (by norm_num : (0 : ℚ) < 1) hsLower
  have hwidth := width_div_le_of_lower hLvalid hsValid hLabs (by norm_num)
    (by norm_num : (0 : ℚ) < 1) hsLower
  refine ⟨hvalid, ?_, ?_⟩
  · simpa using habs
  · calc
      width (L / sqrtTwoInterval) ≤
          (1 : ℚ)⁻¹ * width L +
            2 * (width sqrtTwoInterval / (1 * 1)) := hwidth
      _ = (2 / 100000000000000 : ℚ) +
          2 * (1 / 1000000000000000 : ℚ) := by rw [hLwidth, hsWidth]; norm_num
      _ ≤ (3 / 100000000000000 : ℚ) := by norm_num

private theorem affineCosPrimeCoefficient_metrics :
    (factorTwoPrimeBetaInterval * factorTwoPrimeAffineHeightInterval).Valid ∧
      (factorTwoPrimeBetaInterval *
        factorTwoPrimeAffineHeightInterval).AbsBound 1 ∧
      width (factorTwoPrimeBetaInterval *
        factorTwoPrimeAffineHeightInterval) ≤
        (2 / 1000000000000 : ℚ) := by
  have hBvalid : factorTwoPrimeBetaInterval.Valid :=
    valid_of_contains factorTwoPrimeBetaInterval_contains
  have hHvalid : factorTwoPrimeAffineHeightInterval.Valid :=
    valid_of_contains factorTwoPrimeAffineHeightInterval_contains
  have hBabs : factorTwoPrimeBetaInterval.AbsBound 1 := by
    have hLogValid : factorTwoPrimeLogThreeInterval.Valid :=
      valid_of_contains factorTwoPrimeLogThreeInterval_contains
    have hLogTwoAbs : factorTwoPrimeLogTwoInterval.AbsBound 1 := by
      norm_num [factorTwoPrimeLogTwoInterval, AbsBound]
    have hShiftAbs : factorTwoPrimeShiftInterval.AbsBound (1 / 2 : ℚ) := by
      norm_num [factorTwoPrimeShiftInterval, AbsBound]
    have hLogAbs : factorTwoPrimeLogThreeInterval.AbsBound (3 / 2 : ℚ) := by
      have h := absBound_add hLogTwoAbs hShiftAbs
      have heq : (1 : ℚ) + 1 / 2 = 3 / 2 := by norm_num
      rw [← heq]
      simpa only [factorTwoPrimeLogThreeInterval] using h
    have hSqrtValid : factorTwoPrimeSqrtThreeInterval.Valid :=
      valid_of_contains factorTwoPrimeSqrtThreeInterval_contains
    have hSqrtFloor : (3 / 2 : ℚ) ≤
        factorTwoPrimeSqrtThreeInterval.lower := by
      norm_num [factorTwoPrimeSqrtThreeInterval]
    have h := absBound_div_of_lower hLogValid hSqrtValid hLogAbs
      (by norm_num) (by norm_num : (0 : ℚ) < 3 / 2) hSqrtFloor
    have heq : (3 / 2 : ℚ) * (3 / 2 : ℚ)⁻¹ = 1 := by norm_num
    rw [← heq]
    simpa only [factorTwoPrimeBetaInterval] using h
  have hHabs : factorTwoPrimeAffineHeightInterval.AbsBound 1 := by
    let Num := RatInterval.pure 2 * factorTwoPrimeShiftInterval
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
    have hDenValid : Den.Valid := valid_of_contains factorTwoPrimeLogTwoInterval_contains
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
      exact affineCos_mul_lower_eq_of_nonneg hNumValid hInvValid
        hNumLower hInvLower
    have hRupperEq : R.upper = Num.upper * Den.lower⁻¹ := by
      change (Num * Den⁻¹).upper = Num.upper * Den⁻¹.upper
      exact affineCos_mul_upper_eq_of_nonneg hNumValid hInvValid
        hNumLower hInvLower
    have hNumLowerEq : Num.lower =
        2 * factorTwoPrimeShiftInterval.lower := by
      exact affineCos_mul_lower_eq_of_nonneg (valid_pure 2) hShiftValid
        hTwoLower hShiftLower
    have hNumUpperEq : Num.upper =
        2 * factorTwoPrimeShiftInterval.upper := by
      exact affineCos_mul_upper_eq_of_nonneg (valid_pure 2) hShiftValid
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
  have hwidth := width_mul_le hBvalid hHvalid hBabs hHabs
    (by norm_num) (by norm_num)
  refine ⟨valid_mul hBvalid hHvalid, ?_, ?_⟩
  · simpa using absBound_mul hBvalid hHvalid hBabs hHabs
      (by norm_num) (by norm_num)
  · calc
      width (factorTwoPrimeBetaInterval * factorTwoPrimeAffineHeightInterval) ≤
          width factorTwoPrimeBetaInterval +
            width factorTwoPrimeAffineHeightInterval := by simpa using hwidth
      _ ≤ (1 / 10000000000000 : ℚ) +
          (1 / 1000000000000 : ℚ) :=
        add_le_add factorTwoPerturbationConstantIntervals_width_le.1
          factorTwoPerturbationConstantIntervals_width_le.2.1
      _ ≤ (2 / 1000000000000 : ℚ) := by norm_num

private theorem affineCos_absBound_two_of_contains_unit
    {I : RatInterval} {x : ℝ} (hx : I.Contains x) (habs : |x| ≤ 1)
    (hw : width I ≤ (1 : ℚ)) : I.AbsBound 2 := by
  unfold Contains at hx
  rw [abs_le] at habs
  have hwReal : ((I.upper - I.lower : ℚ) : ℝ) ≤ 1 := by
    exact_mod_cast hw
  norm_num only [Rat.cast_sub, Rat.cast_one] at hwReal
  constructor
  · exact_mod_cast (show (-2 : ℝ) ≤ (I.lower : ℝ) by
      nlinarith [hx.1, hx.2, habs.1, habs.2, hwReal])
  · exact_mod_cast (show (I.upper : ℝ) ≤ 2 by
      nlinarith [hx.1, hx.2, habs.1, habs.2, hwReal])

private theorem affineCosPrimeCosInterval_metrics
    (n : FactorTwoCanonicalEvenIndex) :
    (factorTwoAffineCosPrimeCosInterval n).Valid ∧
      (factorTwoAffineCosPrimeCosInterval n).AbsBound 2 ∧
      width (factorTwoAffineCosPrimeCosInterval n) ≤
        (1 / 10000000000 : ℚ) := by
  have hcontains := factorTwoAffineCosPrimeCosInterval_contains n
  have hvalid := valid_of_contains hcontains
  have hwidth : width (factorTwoAffineCosPrimeCosInterval n) ≤
      (1 / 10000000000 : ℚ) := by
    by_cases hn : n.1 = 0
    · rw [factorTwoAffineCosPrimeCosInterval, if_pos hn, width_pure]
      norm_num
    · rw [factorTwoAffineCosPrimeCosInterval, if_neg hn]
      exact factorTwoPrimeCosInterval_width_le n
  have habs := affineCos_absBound_two_of_contains_unit hcontains
    (abs_cos_le_one _) (hwidth.trans (by norm_num))
  exact ⟨hvalid, habs, hwidth⟩
theorem factorTwoSymmetricAffineCosMomentIntervals_width_le :
    ∀ n : FactorTwoCanonicalEvenIndex,
      width (factorTwoSymmetricAffineCosMomentInterval n) ≤
        (1 / 1000000000 : ℚ) := by
  intro n
  let H := factorTwoHeadDefectInterval /
    factorTwoAffineCosTwoLengthInterval
  let J := factorTwoAffineCosInitialKernelInterval n.1
  let C := RatInterval.pure 1 / factorTwoAffineCosTwoLengthInterval
  let S := factorTwoAffineCosDyadicSeriesInterval n.1
  let B := (RatInterval.pure 2 * factorTwoPrimeLogTwoInterval) /
    sqrtTwoInterval
  let P := factorTwoPrimeBetaInterval * factorTwoPrimeAffineHeightInterval
  let Q := factorTwoAffineCosPrimeCosInterval n
  have hH : H.Valid ∧ H.AbsBound 1 ∧
      width H ≤ (4 / 100000000000000 : ℚ) := by
    simpa only [H] using affineCosHeadCoefficient_metrics
  have hJ : J.Valid ∧ J.AbsBound 24 ∧
      width J ≤ (1 / 10000000000000 : ℚ) := by
    simpa only [J] using affineCosInitialKernelInterval_metrics n.1
  have hC : C.Valid ∧ C.AbsBound 1 ∧
      width C ≤ (2 / 100000000000000 : ℚ) := by
    simpa only [C] using affineCosSeriesCoefficient_metrics
  have hS : S.Valid ∧ S.AbsBound 11000 ∧
      width S ≤ (57 / 100000000000 : ℚ) := by
    simpa only [S] using affineCosDyadicSeriesInterval_metrics n
  have hB : B.Valid ∧ B.AbsBound 2 ∧
      width B ≤ (3 / 100000000000000 : ℚ) := by
    simpa only [B] using affineCosBaseInterval_metrics
  have hP : P.Valid ∧ P.AbsBound 1 ∧
      width P ≤ (2 / 1000000000000 : ℚ) := by
    simpa only [P] using affineCosPrimeCoefficient_metrics
  have hQ : Q.Valid ∧ Q.AbsBound 2 ∧
      width Q ≤ (1 / 10000000000 : ℚ) := by
    simpa only [Q] using affineCosPrimeCosInterval_metrics n
  have hHJ : width (H * J) ≤ (11 / 10000000000000 : ℚ) := by
    calc
      width (H * J) ≤ 24 * width H + 1 * width J :=
        width_mul_le hH.1 hJ.1 hH.2.1 hJ.2.1 (by norm_num) (by norm_num)
      _ ≤ 24 * (4 / 100000000000000 : ℚ) +
          1 * (1 / 10000000000000 : ℚ) :=
        add_le_add (mul_le_mul_of_nonneg_left hH.2.2 (by norm_num))
          (mul_le_mul_of_nonneg_left hJ.2.2 (by norm_num))
      _ ≤ (11 / 10000000000000 : ℚ) := by norm_num
  have hCS : width (C * S) ≤ (79 / 100000000000 : ℚ) := by
    calc
      width (C * S) ≤ 11000 * width C + 1 * width S :=
        width_mul_le hC.1 hS.1 hC.2.1 hS.2.1 (by norm_num) (by norm_num)
      _ ≤ 11000 * (2 / 100000000000000 : ℚ) +
          1 * (57 / 100000000000 : ℚ) :=
        add_le_add (mul_le_mul_of_nonneg_left hC.2.2 (by norm_num))
          (mul_le_mul_of_nonneg_left hS.2.2 (by norm_num))
      _ = (79 / 100000000000 : ℚ) := by norm_num
  have hPQ : width (P * Q) ≤ (104 / 1000000000000 : ℚ) := by
    calc
      width (P * Q) ≤ 2 * width P + 1 * width Q :=
        width_mul_le hP.1 hQ.1 hP.2.1 hQ.2.1 (by norm_num) (by norm_num)
      _ ≤ 2 * (2 / 1000000000000 : ℚ) +
          1 * (1 / 10000000000 : ℚ) :=
        add_le_add (mul_le_mul_of_nonneg_left hP.2.2 (by norm_num))
          (mul_le_mul_of_nonneg_left hQ.2.2 (by norm_num))
      _ = (104 / 1000000000000 : ℚ) := by norm_num
  unfold factorTwoSymmetricAffineCosMomentInterval
  change width (H * J - C * S - B - P * Q) ≤ _
  rw [width_sub, width_sub, width_sub]
  calc
    width (H * J) + width (C * S) + width B + width (P * Q) ≤
        (11 / 10000000000000 : ℚ) +
          (79 / 100000000000 : ℚ) +
          (3 / 100000000000000 : ℚ) +
          (104 / 1000000000000 : ℚ) :=
      add_le_add (add_le_add (add_le_add hHJ hCS) hB.2.2) hPQ
    _ ≤ (1 / 1000000000 : ℚ) := by norm_num

theorem factorTwoSymmetricAffineCosMomentInterval_width_le
    (n : FactorTwoCanonicalEvenIndex) :
    width (factorTwoSymmetricAffineCosMomentInterval n) ≤
      (1 / 1000000000 : ℚ) :=
  factorTwoSymmetricAffineCosMomentIntervals_width_le n

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineCosEnclosures
