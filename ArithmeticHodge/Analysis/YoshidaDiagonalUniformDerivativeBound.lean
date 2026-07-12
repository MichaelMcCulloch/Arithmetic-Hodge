import ArithmeticHodge.Analysis.YoshidaDiagonalDigammaHighBound

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Set MeasureTheory intervalIntegral Filter

namespace ArithmeticHodge.Analysis.YoshidaDiagonalUniformDerivativeBound

open CorrectedTrapezoidRemainder
open DigammaTrapezoid
open YoshidaDiagonalDigammaHighBound
open YoshidaDiagonalUniformIdentity
open YoshidaOddGramPrefix

/-- The first-corrected Euler--Maclaurin main term for the derivative series. -/
def diagonalDerivativeTsumMain (y : ℝ) : ℝ :=
  -diagonalHighProfile y 1 +
    diagonalHighProfileDeriv y 1 / 2 -
    diagonalHighProfileSecondDeriv y 1 / 12

/-- The uniform analytic radius for the derivative series. -/
def diagonalDerivativeTsumRadius (y : ℝ) : ℝ :=
  5 / (2 * y ^ 4)

private def diagonalDerivativeCorrectedError (y : ℝ) (k : ℕ) : ℝ :=
  trapezoidal_error (diagonalHighProfileDeriv y) 1
      ((k : ℝ) + 1) ((k : ℝ) + 2) -
    (diagonalHighProfileSecondDeriv y ((k : ℝ) + 2) -
      diagonalHighProfileSecondDeriv y ((k : ℝ) + 1)) / 12

private def diagonalFourthMajorant (y t : ℝ) : ℝ :=
  10 * (t + 1 / 4) / (((t + 1 / 4) ^ 2 + y ^ 2) ^ 3)

private def diagonalFourthMajorantPrimitive (y t : ℝ) : ℝ :=
  (-5 : ℝ) / (2 * (((t + 1 / 4) ^ 2 + y ^ 2) ^ 2))

private theorem hasDerivAt_diagonalHighProfile
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

private theorem continuous_diagonalHighProfileFourthDeriv
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

private theorem one_div_twelve_mul_abs_fourth_le_majorant
    {y t : ℝ} (hy : 0 < y) (ht : 0 ≤ t) :
    (1 / 12 : ℝ) * |diagonalHighProfileFourthDeriv y t| ≤
      diagonalFourthMajorant y t := by
  let u : ℝ := t + 1 / 4
  let D : ℝ := u ^ 2 + y ^ 2
  let Q : ℝ := u ^ 4 - 10 * u ^ 2 * y ^ 2 + 5 * y ^ 4
  have hu : 0 < u := by
    dsimp [u]
    linarith
  have hD : 0 < D := by
    dsimp [D]
    positivity
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
  unfold diagonalHighProfileFourthDeriv diagonalFourthMajorant
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

private theorem hasDerivAt_diagonalFourthMajorantPrimitive
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (diagonalFourthMajorantPrimitive y)
      (diagonalFourthMajorant y t) t := by
  let u : ℝ → ℝ := fun s ↦ s + 1 / 4
  let D : ℝ → ℝ := fun s ↦ u s ^ 2 + y ^ 2
  have hu : HasDerivAt u 1 t := by
    simpa [u] using (hasDerivAt_id t).add_const (1 / 4)
  have hD : HasDerivAt D (2 * u t) t := by
    dsimp only [D]
    convert (hu.pow 2).add_const (y ^ 2) using 1
    all_goals ring_nf
  have hden : 2 * (D t) ^ 2 ≠ 0 := by
    have hDpos : 0 < D t := by
      dsimp [D, u]
      positivity
    positivity
  have hDne : (t + 1 / 4) ^ 2 + y ^ 2 ≠ 0 := by positivity
  have hdenDeriv : HasDerivAt (fun s ↦ 2 * (D s) ^ 2)
      (8 * u t * D t) t := by
    convert (hD.pow 2).const_mul 2 using 1
    all_goals ring_nf
  unfold diagonalFourthMajorantPrimitive diagonalFourthMajorant
  dsimp only [u, D] at hden hdenDeriv ⊢
  convert (hasDerivAt_const t (-5 : ℝ)).div hdenDeriv hden using 1
  field_simp [hDne]
  ring_nf

private theorem integral_diagonalFourthMajorant
    {y a b : ℝ} (hy : y ≠ 0) (hab : a ≤ b) :
    (∫ t in a..b, diagonalFourthMajorant y t) =
      diagonalFourthMajorantPrimitive y b -
        diagonalFourthMajorantPrimitive y a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _ht
    exact hasDerivAt_diagonalFourthMajorantPrimitive hy
  · have hcont : Continuous (diagonalFourthMajorant y) := by
      unfold diagonalFourthMajorant
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro t
        have hden : 0 < (t + 1 / 4) ^ 2 + y ^ 2 := by positivity
        exact (pow_pos hden 3).ne'
    exact hcont.continuousOn.intervalIntegrable_of_Icc hab

private theorem diagonalDerivativeCorrectedError_abs_le
    {y : ℝ} (hy : 0 < y) (k : ℕ) :
    |diagonalDerivativeCorrectedError y k| ≤
      ∫ t in ((k : ℝ) + 1)..((k : ℝ) + 2),
        diagonalFourthMajorant y t := by
  let a : ℝ := (k : ℝ) + 1
  have hfourInt : IntervalIntegrable (diagonalHighProfileFourthDeriv y)
      volume a (a + 1) :=
    (continuous_diagonalHighProfileFourthDeriv hy.ne').intervalIntegrable _ _
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
  have hid' : diagonalDerivativeCorrectedError y k =
      -(∫ t in a..a + 1,
        correctedTrapezoidThirdKernel a t *
          diagonalHighProfileFourthDeriv y t) := by
    have ha : (k : ℝ) + 2 = a + 1 := by
      dsimp [a]
      ring_nf
    unfold diagonalDerivativeCorrectedError
    rw [ha]
    exact hid
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
      (continuous_diagonalHighProfileFourthDeriv hy.ne')).abs.intervalIntegrable _ _
  have hmajorantInt : IntervalIntegrable (diagonalFourthMajorant y)
      volume a (a + 1) := by
    have hcont : Continuous (diagonalFourthMajorant y) := by
      unfold diagonalFourthMajorant
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
    _ ≤ ∫ t in a..a + 1, diagonalFourthMajorant y t := by
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
        _ ≤ diagonalFourthMajorant y t :=
          one_div_twelve_mul_abs_fourth_le_majorant hy (by
            dsimp only [a] at ht
            linarith [ht.1])
    _ = ∫ t in ((k : ℝ) + 1)..((k : ℝ) + 2),
        diagonalFourthMajorant y t := by
      dsimp only [a]
      congr 1
      all_goals ring_nf

private theorem diagonalDerivativeCorrectedError_sum_abs_le
    {y : ℝ} (hy : 0 < y) (N : ℕ) :
    |∑ k ∈ Finset.range N, diagonalDerivativeCorrectedError y k| ≤
      diagonalDerivativeTsumRadius y := by
  calc
    |∑ k ∈ Finset.range N, diagonalDerivativeCorrectedError y k| ≤
        ∑ k ∈ Finset.range N, |diagonalDerivativeCorrectedError y k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N,
        ∫ t in ((k : ℝ) + 1)..((k : ℝ) + 2),
          diagonalFourthMajorant y t := by
      exact Finset.sum_le_sum fun k _hk ↦
        diagonalDerivativeCorrectedError_abs_le hy k
    _ = ∑ k ∈ Finset.range N,
        (diagonalFourthMajorantPrimitive y ((k : ℝ) + 2) -
          diagonalFourthMajorantPrimitive y ((k : ℝ) + 1)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact integral_diagonalFourthMajorant hy.ne' (by norm_num)
    _ = diagonalFourthMajorantPrimitive y ((N : ℝ) + 1) -
        diagonalFourthMajorantPrimitive y 1 := by
      convert (Finset.sum_range_sub
        (fun k : ℕ ↦
          diagonalFourthMajorantPrimitive y ((k : ℝ) + 1)) N) using 1
      all_goals norm_num
      all_goals ring_nf
    _ ≤ diagonalDerivativeTsumRadius y := by
      have hnonpos : diagonalFourthMajorantPrimitive y ((N : ℝ) + 1) ≤ 0 := by
        unfold diagonalFourthMajorantPrimitive
        exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
      calc
        diagonalFourthMajorantPrimitive y ((N : ℝ) + 1) -
            diagonalFourthMajorantPrimitive y 1 ≤
            0 - diagonalFourthMajorantPrimitive y 1 :=
          sub_le_sub_right hnonpos _
        _ = 5 / (2 * ((((5 : ℝ) / 4) ^ 2 + y ^ 2) ^ 2)) := by
          unfold diagonalFourthMajorantPrimitive
          rw [show (1 : ℝ) + 1 / 4 = 5 / 4 by norm_num]
          ring_nf
        _ ≤ diagonalDerivativeTsumRadius y := by
          unfold diagonalDerivativeTsumRadius
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          have hbase : y ^ 2 ≤ ((5 : ℝ) / 4) ^ 2 + y ^ 2 := by
            nlinarith [sq_nonneg ((5 : ℝ) / 4)]
          have hsquare := pow_le_pow_left₀ (sq_nonneg y) hbase 2
          nlinarith [hsquare]

private theorem diagonalHighProfileSecondDeriv_abs_le_six_div_cube
    (y : ℝ) (j : ℕ) :
    |diagonalHighProfileSecondDeriv y (j + 1)| ≤
      6 / (((j : ℝ) + 1) ^ 3) := by
  let k : ℝ := (j : ℝ) + 1
  let u : ℝ := k + 1 / 4
  let D : ℝ := u ^ 2 + y ^ 2
  have hk : 0 < k := by
    dsimp [k]
    positivity
  have hu : 0 < u := by
    dsimp [u]
    linarith
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hpoly : |u ^ 2 - 3 * y ^ 2| ≤ 3 * D := by
    rw [abs_le]
    constructor <;> dsimp [D] <;> nlinarith [sq_nonneg u, sq_nonneg y]
  have huD : u ^ 2 ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg y]
  have hDsqRaw := pow_le_pow_left₀ (sq_nonneg u) huD 2
  have hDsq : u ^ 4 ≤ D ^ 2 := by
    nlinarith [hDsqRaw]
  have hku : k ≤ u := by
    dsimp [u]
    norm_num
  unfold diagonalHighProfileSecondDeriv
  dsimp only
  change |2 * u * (u ^ 2 - 3 * y ^ 2) / D ^ 3| ≤ 6 / k ^ 3
  rw [abs_div, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hu,
    abs_of_pos (pow_pos hD 3)]
  calc
    2 * u * |u ^ 2 - 3 * y ^ 2| / D ^ 3 ≤
        2 * u * (3 * D) / D ^ 3 := by
      gcongr
    _ = 6 * u / D ^ 2 := by
      field_simp [hD.ne']
      ring_nf
    _ ≤ 6 / u ^ 3 := by
      rw [div_le_div_iff₀ (pow_pos hD 2) (pow_pos hu 3)]
      nlinarith [hDsq]
    _ ≤ 6 / k ^ 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (pow_pos hk 3)
      exact pow_le_pow_left₀ hk.le hku 3

private theorem summable_diagonalHighProfileDeriv_nat_succ (y : ℝ) :
    Summable (fun j : ℕ ↦ diagonalHighProfileDeriv y (j + 1)) := by
  have hmajor : Summable (fun j : ℕ ↦
      1 / ((((j + 1 : ℕ) : ℝ) ^ 2))) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 h
  apply hmajor.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs]
  exact diagonalHighProfileDeriv_abs_le y j

private theorem summable_diagonalHighProfileSecondDeriv_nat_succ (y : ℝ) :
    Summable (fun j : ℕ ↦ diagonalHighProfileSecondDeriv y (j + 1)) := by
  have hbase : Summable (fun j : ℕ ↦
      1 / ((((j + 1 : ℕ) : ℝ) ^ 3))) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 h
  have hmajor : Summable (fun j : ℕ ↦
      6 / ((((j + 1 : ℕ) : ℝ) ^ 3))) := by
    simpa [div_eq_mul_inv] using hbase.mul_left (6 : ℝ)
  apply hmajor.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs]
  simpa only [Nat.cast_add, Nat.cast_one] using
    diagonalHighProfileSecondDeriv_abs_le_six_div_cube y j

private theorem tendsto_diagonalHighProfile_nat_succ (y : ℝ) :
    Tendsto (fun N : ℕ ↦ diagonalHighProfile y (N + 1))
      atTop (nhds 0) := by
  have hbase := tendsto_shiftedReciprocalRealPart_nat (1 / 4) y
  have hprofile : Tendsto (fun N : ℕ ↦ diagonalHighProfile y N)
      atTop (nhds 0) := by
    simpa [diagonalHighProfile, shiftedReciprocalRealPart, add_comm] using hbase
  convert hprofile.comp (tendsto_add_atTop_nat 1) using 1
  funext N
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]

private theorem sum_range_diagonalDerivativeCorrectedError_eq
    {y : ℝ} (hy : y ≠ 0) (N : ℕ) :
    (∑ k ∈ Finset.range N, diagonalDerivativeCorrectedError y k) =
      (∑ k ∈ Finset.range N, diagonalHighProfileDeriv y (k + 1)) -
        diagonalHighProfileDeriv y 1 / 2 +
        diagonalHighProfileDeriv y (N + 1) / 2 -
        (diagonalHighProfile y (N + 1) - diagonalHighProfile y 1) -
        (diagonalHighProfileSecondDeriv y (N + 1) -
          diagonalHighProfileSecondDeriv y 1) / 12 := by
  have hcont : Continuous (diagonalHighProfileDeriv y) :=
    continuous_iff_continuousAt.mpr fun t ↦
      (hasDerivAt_diagonalHighProfileDeriv (y := y) (t := t) hy).continuousAt
  have hcell (k : ℕ) :
      trapezoidal_error (diagonalHighProfileDeriv y) 1
          ((k : ℝ) + 1) ((k : ℝ) + 2) =
        (diagonalHighProfileDeriv y ((k : ℝ) + 1) +
            diagonalHighProfileDeriv y ((k : ℝ) + 2)) / 2 -
          (diagonalHighProfile y ((k : ℝ) + 2) -
            diagonalHighProfile y ((k : ℝ) + 1)) := by
    have hint :
        (∫ t in ((k : ℝ) + 1)..((k : ℝ) + 2),
          diagonalHighProfileDeriv y t) =
            diagonalHighProfile y ((k : ℝ) + 2) -
              diagonalHighProfile y ((k : ℝ) + 1) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t _ht
        exact hasDerivAt_diagonalHighProfile hy
      · exact hcont.intervalIntegrable _ _
    rw [trapezoidal_error, trapezoidal_integral_one, hint]
    ring_nf
  have hshift :
      (∑ k ∈ Finset.range N,
        diagonalHighProfileDeriv y ((k : ℝ) + 2)) =
        (∑ k ∈ Finset.range N,
          diagonalHighProfileDeriv y ((k : ℝ) + 1)) -
          diagonalHighProfileDeriv y 1 +
          diagonalHighProfileDeriv y ((N : ℝ) + 1) := by
    calc
      (∑ k ∈ Finset.range N,
          diagonalHighProfileDeriv y ((k : ℝ) + 2)) =
          (∑ k ∈ Finset.range (N + 1),
            diagonalHighProfileDeriv y ((k : ℝ) + 1)) -
            diagonalHighProfileDeriv y 1 := by
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_add, Nat.cast_one]
        ring_nf
      _ = (∑ k ∈ Finset.range N,
            diagonalHighProfileDeriv y ((k : ℝ) + 1)) -
            diagonalHighProfileDeriv y 1 +
            diagonalHighProfileDeriv y ((N : ℝ) + 1) := by
        rw [Finset.sum_range_succ]
        ring_nf
  have havg :
      (∑ k ∈ Finset.range N,
        (diagonalHighProfileDeriv y ((k : ℝ) + 1) +
          diagonalHighProfileDeriv y ((k : ℝ) + 2)) / 2) =
        (∑ k ∈ Finset.range N,
          diagonalHighProfileDeriv y ((k : ℝ) + 1)) -
          diagonalHighProfileDeriv y 1 / 2 +
          diagonalHighProfileDeriv y ((N : ℝ) + 1) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hshift]
    ring_nf
  have htelProfile :
      (∑ k ∈ Finset.range N,
        (diagonalHighProfile y ((k : ℝ) + 2) -
          diagonalHighProfile y ((k : ℝ) + 1))) =
        diagonalHighProfile y ((N : ℝ) + 1) -
          diagonalHighProfile y 1 := by
    convert (Finset.sum_range_sub
      (fun k : ℕ ↦ diagonalHighProfile y ((k : ℝ) + 1)) N) using 1
    all_goals norm_num
    all_goals ring_nf
  have htrap :
      (∑ k ∈ Finset.range N,
        trapezoidal_error (diagonalHighProfileDeriv y) 1
          ((k : ℝ) + 1) ((k : ℝ) + 2)) =
        (∑ k ∈ Finset.range N, diagonalHighProfileDeriv y (k + 1)) -
          diagonalHighProfileDeriv y 1 / 2 +
          diagonalHighProfileDeriv y (N + 1) / 2 -
          (diagonalHighProfile y (N + 1) - diagonalHighProfile y 1) := by
    calc
      (∑ k ∈ Finset.range N,
          trapezoidal_error (diagonalHighProfileDeriv y) 1
            ((k : ℝ) + 1) ((k : ℝ) + 2)) =
          ∑ k ∈ Finset.range N,
            ((diagonalHighProfileDeriv y ((k : ℝ) + 1) +
                diagonalHighProfileDeriv y ((k : ℝ) + 2)) / 2 -
              (diagonalHighProfile y ((k : ℝ) + 2) -
                diagonalHighProfile y ((k : ℝ) + 1))) := by
        apply Finset.sum_congr rfl
        intro k _hk
        exact hcell k
      _ = (∑ k ∈ Finset.range N,
            (diagonalHighProfileDeriv y ((k : ℝ) + 1) +
              diagonalHighProfileDeriv y ((k : ℝ) + 2)) / 2) -
            ∑ k ∈ Finset.range N,
              (diagonalHighProfile y ((k : ℝ) + 2) -
                diagonalHighProfile y ((k : ℝ) + 1)) :=
        by rw [Finset.sum_sub_distrib]
      _ = _ := by
        rw [havg, htelProfile]
  have htelSecond :
      (∑ k ∈ Finset.range N,
        (diagonalHighProfileSecondDeriv y ((k : ℝ) + 2) -
          diagonalHighProfileSecondDeriv y ((k : ℝ) + 1))) =
        diagonalHighProfileSecondDeriv y (N + 1) -
          diagonalHighProfileSecondDeriv y 1 := by
    convert (Finset.sum_range_sub
      (fun k : ℕ ↦ diagonalHighProfileSecondDeriv y ((k : ℝ) + 1)) N) using 1
    all_goals norm_num
    all_goals ring_nf
  unfold diagonalDerivativeCorrectedError
  rw [Finset.sum_sub_distrib, htrap, ← Finset.sum_div, htelSecond]

private theorem tendsto_sum_diagonalDerivativeCorrectedError
    {y : ℝ} (hy : 0 < y) :
    Tendsto
      (fun N : ℕ ↦
        ∑ k ∈ Finset.range N, diagonalDerivativeCorrectedError y k)
      atTop
      (nhds ((∑' j : ℕ, diagonalHighProfileDeriv y (j + 1)) -
        diagonalDerivativeTsumMain y)) := by
  have hsum := (summable_diagonalHighProfileDeriv_nat_succ y).hasSum.tendsto_sum_nat
  have hderiv := (summable_diagonalHighProfileDeriv_nat_succ y).tendsto_atTop_zero
  have hsecond :=
    (summable_diagonalHighProfileSecondDeriv_nat_succ y).tendsto_atTop_zero
  have hprofile := tendsto_diagonalHighProfile_nat_succ y
  have hderivOne : Tendsto
      (fun _ : ℕ ↦ diagonalHighProfileDeriv y 1) atTop
      (nhds (diagonalHighProfileDeriv y 1)) := tendsto_const_nhds
  have hprofileOne : Tendsto
      (fun _ : ℕ ↦ diagonalHighProfile y 1) atTop
      (nhds (diagonalHighProfile y 1)) := tendsto_const_nhds
  have hsecondOne : Tendsto
      (fun _ : ℕ ↦ diagonalHighProfileSecondDeriv y 1) atTop
      (nhds (diagonalHighProfileSecondDeriv y 1)) := tendsto_const_nhds
  have hlim := ((((hsum.sub (hderivOne.div_const 2)).add
      (hderiv.div_const 2)).sub (hprofile.sub hprofileOne)).sub
      ((hsecond.sub hsecondOne).div_const 12))
  convert hlim using 1
  · funext N
    rw [sum_range_diagonalDerivativeCorrectedError_eq hy.ne']
  · unfold diagonalDerivativeTsumMain
    ring_nf

/-- The derivative `tsum` is enclosed by the first-corrected
Euler--Maclaurin main term with a uniform `y⁻⁴` radius. -/
theorem diagonalHighProfileDeriv_tsum_sub_main_abs_le
    {y : ℝ} (hy : 0 < y) :
    |(∑' j : ℕ, diagonalHighProfileDeriv y (j + 1)) -
        diagonalDerivativeTsumMain y| ≤ diagonalDerivativeTsumRadius y := by
  have hlim := tendsto_sum_diagonalDerivativeCorrectedError hy
  exact le_of_tendsto' hlim.abs fun N ↦
    diagonalDerivativeCorrectedError_sum_abs_le hy N

/-- Direct normalization by the production factor `2 * yoshidaLength`. -/
theorem diagonalHighProfileDeriv_tsum_normalized_sub_main_abs_le
    {y : ℝ} (hy : 0 < y) :
    |(∑' j : ℕ, diagonalHighProfileDeriv y (j + 1)) /
          (2 * yoshidaLength) -
        diagonalDerivativeTsumMain y /
          (2 * yoshidaLength)| ≤
      5 / (4 * yoshidaLength * y ^ 4) := by
  have h := diagonalHighProfileDeriv_tsum_sub_main_abs_le hy
  unfold diagonalDerivativeTsumRadius at h
  rw [← sub_div, abs_div, abs_of_pos
    (mul_pos (by norm_num) yoshidaLength_pos)]
  calc
    |(∑' j : ℕ, diagonalHighProfileDeriv y (j + 1)) -
          diagonalDerivativeTsumMain y| /
          (2 * yoshidaLength) ≤
        (5 / (2 * y ^ 4)) / (2 * yoshidaLength) := by
      apply div_le_div_of_nonneg_right _
        (mul_nonneg (by norm_num) yoshidaLength_pos.le)
      exact h
    _ = 5 / (4 * yoshidaLength * y ^ 4) := by ring_nf

/-- Production specialization of the directly normalized enclosure. -/
theorem diagonalHighDerivativeTerm_normalized_sub_main_abs_le
    {n : ℕ} (hn : n ≠ 0) :
    |(∑' j : ℕ, diagonalHighDerivativeTerm n j) /
          (2 * yoshidaLength) -
        diagonalDerivativeTsumMain (yoshidaY n) /
          (2 * yoshidaLength)| ≤
      5 / (4 * yoshidaLength * yoshidaY n ^ 4) := by
  have hnOne : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hnOne
  have hy : 0 < yoshidaY n := by
    unfold yoshidaY yoshidaKappa
    exact div_pos
      (div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hnR)
        yoshidaLength_pos) (by norm_num)
  simpa only [diagonalHighDerivativeTerm] using
    diagonalHighProfileDeriv_tsum_normalized_sub_main_abs_le hy

/-- Exact production-frequency rewrite of the normalized radius. -/
theorem diagonalHighDerivativeTerm_normalized_sub_main_abs_le_pi
    {n : ℕ} (hn : n ≠ 0) :
    |(∑' j : ℕ, diagonalHighDerivativeTerm n j) /
          (2 * yoshidaLength) -
        diagonalDerivativeTsumMain (yoshidaY n) /
          (2 * yoshidaLength)| ≤
      5 * yoshidaLength ^ 3 /
        (4 * Real.pi ^ 4 * (n : ℝ) ^ 4) := by
  have h := diagonalHighDerivativeTerm_normalized_sub_main_abs_le hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  convert h using 1
  unfold yoshidaY yoshidaKappa
  field_simp [yoshidaLength_pos.ne', Real.pi_ne_zero, hnR]

end ArithmeticHodge.Analysis.YoshidaDiagonalUniformDerivativeBound
