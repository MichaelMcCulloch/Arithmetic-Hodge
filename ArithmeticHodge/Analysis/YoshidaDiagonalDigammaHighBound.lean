import ArithmeticHodge.Analysis.CorrectedTrapezoidRemainder
import ArithmeticHodge.Analysis.YoshidaDiagonalUniformIdentity

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Set MeasureTheory intervalIntegral Filter

namespace ArithmeticHodge.Analysis.YoshidaDiagonalDigammaHighBound

open CorrectedTrapezoidRemainder
open DigammaTrapezoid
open YoshidaDiagonalUniformIdentity

def diagonalHighProfileSecondDeriv (y t : ℝ) : ℝ :=
  let u := t + 1 / 4
  2 * u * (u ^ 2 - 3 * y ^ 2) / (u ^ 2 + y ^ 2) ^ 3

def diagonalHighProfileThirdDeriv (y t : ℝ) : ℝ :=
  let u := t + 1 / 4
  (-6 : ℝ) * (u ^ 4 - 6 * u ^ 2 * y ^ 2 + y ^ 4) /
    (u ^ 2 + y ^ 2) ^ 4

def diagonalHighProfileFourthDeriv (y t : ℝ) : ℝ :=
  let u := t + 1 / 4
  24 * u * (u ^ 4 - 10 * u ^ 2 * y ^ 2 + 5 * y ^ 4) /
    (u ^ 2 + y ^ 2) ^ 5

private def diagonalHighProfileFifthDeriv (y t : ℝ) : ℝ :=
  let u := t + 1 / 4
  120 * (-u ^ 6 + 15 * u ^ 4 * y ^ 2 -
      15 * u ^ 2 * y ^ 4 + y ^ 6) /
    (u ^ 2 + y ^ 2) ^ 6

def diagonalDigammaMain (y : ℝ) : ℝ :=
  Real.log ((1 / 16 : ℝ) + y ^ 2) / 2 -
    diagonalHighProfile y 0 / 2 +
    diagonalHighProfileDeriv y 0 / 12 -
    diagonalHighProfileThirdDeriv y 0 / 720

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

theorem hasDerivAt_diagonalHighProfileDeriv
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (diagonalHighProfileDeriv y)
      (diagonalHighProfileSecondDeriv y t) t := by
  have hu : HasDerivAt (fun s : ℝ ↦ s + 1 / 4) 1 t := by
    simpa using (hasDerivAt_id t).add_const (1 / 4)
  have h := (hasDerivAt_reciprocalRealPartDeriv
    (y := y) (u := t + 1 / 4) hy).comp t hu
  change HasDerivAt
    (reciprocalRealPartDeriv y ∘ fun s : ℝ ↦ s + 1 / 4)
    (reciprocalRealPartSecondDeriv y (t + 1 / 4)) t
  simpa only [mul_one] using h

theorem hasDerivAt_diagonalHighProfileSecondDeriv
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (diagonalHighProfileSecondDeriv y)
      (diagonalHighProfileThirdDeriv y t) t := by
  let u : ℝ → ℝ := fun s ↦ s + 1 / 4
  have hu : HasDerivAt u 1 t := by
    simpa [u] using (hasDerivAt_id t).add_const (1 / 4)
  have hD : HasDerivAt (fun s ↦ u s ^ 2 + y ^ 2) (2 * u t) t := by
    convert (hu.pow 2).add_const (y ^ 2) using 1
    all_goals ring
  have hnum : HasDerivAt
      (fun s ↦ 2 * u s * (u s ^ 2 - 3 * y ^ 2))
      (2 * (u t ^ 2 - 3 * y ^ 2) + 4 * u t ^ 2) t := by
    convert (hu.const_mul 2).mul ((hu.pow 2).sub_const (3 * y ^ 2)) using 1
    all_goals simp only [Pi.pow_apply]
    all_goals ring
  have hden : u t ^ 2 + y ^ 2 ≠ 0 := by
    dsimp [u]
    positivity
  unfold diagonalHighProfileSecondDeriv diagonalHighProfileThirdDeriv
  dsimp only
  convert hnum.div (hD.pow 3) (pow_ne_zero 3 hden) using 1
  simp only [Pi.pow_apply]
  field_simp [hden]
  ring

theorem hasDerivAt_diagonalHighProfileThirdDeriv
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (diagonalHighProfileThirdDeriv y)
      (diagonalHighProfileFourthDeriv y t) t := by
  let u : ℝ → ℝ := fun s ↦ s + 1 / 4
  have hu : HasDerivAt u 1 t := by
    simpa [u] using (hasDerivAt_id t).add_const (1 / 4)
  have hD : HasDerivAt (fun s ↦ u s ^ 2 + y ^ 2) (2 * u t) t := by
    convert (hu.pow 2).add_const (y ^ 2) using 1
    all_goals ring
  have hpoly : HasDerivAt
      (fun s ↦ u s ^ 4 - 6 * u s ^ 2 * y ^ 2 + y ^ 4)
      (4 * u t ^ 3 - 12 * u t * y ^ 2) t := by
    convert ((hu.pow 4).sub ((hu.pow 2).const_mul (6 * y ^ 2))).add_const
      (y ^ 4) using 1
    · funext s
      simp only [Pi.pow_apply, Pi.sub_apply]
      ring
    · ring
  have hden : u t ^ 2 + y ^ 2 ≠ 0 := by
    dsimp [u]
    positivity
  unfold diagonalHighProfileThirdDeriv diagonalHighProfileFourthDeriv
  dsimp only
  convert (hpoly.const_mul (-6)).div (hD.pow 4)
    (pow_ne_zero 4 hden) using 1
  simp only [Pi.pow_apply]
  field_simp [hden]
  ring

private theorem hasDerivAt_diagonalHighProfileFourthDeriv
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (diagonalHighProfileFourthDeriv y)
      (diagonalHighProfileFifthDeriv y t) t := by
  let u : ℝ → ℝ := fun s ↦ s + 1 / 4
  have hu : HasDerivAt u 1 t := by
    simpa [u] using (hasDerivAt_id t).add_const (1 / 4)
  have hD : HasDerivAt (fun s ↦ u s ^ 2 + y ^ 2) (2 * u t) t := by
    convert (hu.pow 2).add_const (y ^ 2) using 1
    all_goals ring
  have hpoly : HasDerivAt
      (fun s ↦ u s ^ 4 - 10 * u s ^ 2 * y ^ 2 + 5 * y ^ 4)
      (4 * u t ^ 3 - 20 * u t * y ^ 2) t := by
    convert ((hu.pow 4).sub ((hu.pow 2).const_mul (10 * y ^ 2))).add_const
      (5 * y ^ 4) using 1
    · funext s
      simp only [Pi.pow_apply, Pi.sub_apply]
      ring
    · ring
  have hnum : HasDerivAt
      (fun s ↦ 24 * u s *
        (u s ^ 4 - 10 * u s ^ 2 * y ^ 2 + 5 * y ^ 4))
      (24 * (u t ^ 4 - 10 * u t ^ 2 * y ^ 2 + 5 * y ^ 4) +
        24 * u t * (4 * u t ^ 3 - 20 * u t * y ^ 2)) t := by
    convert (hu.const_mul 24).mul hpoly using 1
    all_goals ring
  have hden : u t ^ 2 + y ^ 2 ≠ 0 := by
    dsimp [u]
    positivity
  unfold diagonalHighProfileFourthDeriv diagonalHighProfileFifthDeriv
  dsimp only
  convert hnum.div (hD.pow 5) (pow_ne_zero 5 hden) using 1
  simp only [Pi.pow_apply]
  field_simp [hden]
  ring

private theorem continuous_diagonalHighProfileFifthDeriv
    {y : ℝ} (hy : y ≠ 0) :
    Continuous (diagonalHighProfileFifthDeriv y) := by
  unfold diagonalHighProfileFifthDeriv
  dsimp only
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    have hden : 0 < (t + 1 / 4) ^ 2 + y ^ 2 := by positivity
    exact (pow_pos hden 6).ne'

private theorem abs_correctedTrapezoidFifthKernel_le
    {a t : ℝ} (ht : t ∈ Icc a (a + 1)) :
    |correctedTrapezoidFifthKernel a t| ≤ 1 / 720 := by
  let x : ℝ := t - a
  have hx0 : 0 ≤ x := by
    dsimp [x]
    linarith [ht.1]
  have hx1 : x ≤ 1 := by
    dsimp [x]
    linarith [ht.2]
  have honeSub : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hprod0 : 0 ≤ x * (1 - x) := mul_nonneg hx0 honeSub
  have hprod : x * (1 - x) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hmid : |x - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hlast : |x ^ 2 - x - 1 / 3| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hfactor : correctedTrapezoidFifthKernel a t =
      x * (1 - x) * (x - 1 / 2) * (x ^ 2 - x - 1 / 3) / 120 := by
    dsimp [correctedTrapezoidFifthKernel, x]
    ring
  rw [hfactor, abs_div, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg hx0, abs_of_nonneg honeSub,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 120)]
  calc
    x * (1 - x) * |x - 1 / 2| * |x ^ 2 - x - 1 / 3| / 120 ≤
        (1 / 4 : ℝ) * (1 / 2) * 1 / 120 := by gcongr
    _ ≤ 1 / 720 := by norm_num

private theorem abs_diagonalHighProfileFifthDeriv_le
    {y t : ℝ} (hy : 0 < y) (ht : 0 ≤ t) :
    |diagonalHighProfileFifthDeriv y t| ≤
      600 / (((t + 1 / 4) ^ 2 + y ^ 2) ^ 3) := by
  let u : ℝ := t + 1 / 4
  let D : ℝ := u ^ 2 + y ^ 2
  let P : ℝ := -u ^ 6 + 15 * u ^ 4 * y ^ 2 -
    15 * u ^ 2 * y ^ 4 + y ^ 6
  have hu : 0 < u := by
    dsimp [u]
    linarith
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hu6 : 0 ≤ u ^ 6 := pow_nonneg hu.le 6
  have hy6 : 0 ≤ y ^ 6 := pow_nonneg hy.le 6
  have hu4y2 : 0 ≤ u ^ 4 * y ^ 2 :=
    mul_nonneg (pow_nonneg hu.le 4) (sq_nonneg y)
  have hu2y4 : 0 ≤ u ^ 2 * y ^ 4 :=
    mul_nonneg (sq_nonneg u) (pow_nonneg hy.le 4)
  have hP : |P| ≤
      u ^ 6 + 15 * u ^ 4 * y ^ 2 + 15 * u ^ 2 * y ^ 4 + y ^ 6 := by
    rw [abs_le]
    constructor <;> dsimp [P] <;> nlinarith
  have hDexpand :
      5 * D ^ 3 =
        5 * u ^ 6 + 15 * u ^ 4 * y ^ 2 +
          15 * u ^ 2 * y ^ 4 + 5 * y ^ 6 := by
    dsimp [D]
    ring
  have hPfive : |P| ≤ 5 * D ^ 3 := by
    rw [hDexpand]
    nlinarith
  unfold diagonalHighProfileFifthDeriv
  dsimp only
  change |120 * P / D ^ 6| ≤ 600 / D ^ 3
  rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 120),
    abs_of_pos (pow_pos hD 6)]
  calc
    120 * |P| / D ^ 6 ≤ 120 * (5 * D ^ 3) / D ^ 6 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hPfive (by norm_num)) (pow_nonneg hD.le 6)
    _ = 600 / D ^ 3 := by
      field_simp [hD.ne']
      ring

private def diagonalFifthMajorant (y t : ℝ) : ℝ :=
  20 / (3 * (t + y) ^ 6)

private def diagonalFifthMajorantPrimitive (y t : ℝ) : ℝ :=
  (-4 : ℝ) / (3 * (t + y) ^ 5)

private theorem one_div_720_mul_abs_fifth_le_majorant
    {y t : ℝ} (hy : 0 < y) (ht : 0 ≤ t) :
    (1 / 720 : ℝ) * |diagonalHighProfileFifthDeriv y t| ≤
      diagonalFifthMajorant y t := by
  let u : ℝ := t + 1 / 4
  let D : ℝ := u ^ 2 + y ^ 2
  let s : ℝ := t + y
  have hs : 0 < s := by
    dsimp [s]
    linarith
  have hD : 0 < D := by
    dsimp [D, u]
    positivity
  have hfifth := abs_diagonalHighProfileFifthDeriv_le hy ht
  change |diagonalHighProfileFifthDeriv y t| ≤ 600 / D ^ 3 at hfifth
  have hDtwo : s ^ 2 ≤ 2 * D := by
    dsimp [s, D, u]
    nlinarith [sq_nonneg (t - y)]
  have hcube : s ^ 6 ≤ 8 * D ^ 3 := by
    calc
      s ^ 6 = (s ^ 2) ^ 3 := by ring
      _ ≤ (2 * D) ^ 3 := pow_le_pow_left₀ (sq_nonneg s) hDtwo 3
      _ = 8 * D ^ 3 := by ring
  have hdenOrder : s ^ 6 / 8 ≤ D ^ 3 := by linarith
  have hsmall : 0 < s ^ 6 / 8 := by positivity
  unfold diagonalFifthMajorant
  change (1 / 720 : ℝ) * |diagonalHighProfileFifthDeriv y t| ≤
    20 / (3 * s ^ 6)
  calc
    (1 / 720 : ℝ) * |diagonalHighProfileFifthDeriv y t| ≤
        (1 / 720 : ℝ) * (600 / D ^ 3) :=
      mul_le_mul_of_nonneg_left hfifth (by norm_num)
    _ = (5 / 6 : ℝ) / D ^ 3 := by ring
    _ ≤ (5 / 6 : ℝ) / (s ^ 6 / 8) :=
      div_le_div_of_nonneg_left (by norm_num) hsmall hdenOrder
    _ = 20 / (3 * s ^ 6) := by
      field_simp [hs.ne']
      ring

private theorem hasDerivAt_diagonalFifthMajorantPrimitive
    {y t : ℝ} (hyt : t + y ≠ 0) :
    HasDerivAt (diagonalFifthMajorantPrimitive y)
      (diagonalFifthMajorant y t) t := by
  have hu : HasDerivAt (fun s : ℝ ↦ s + y) 1 t := by
    simpa using (hasDerivAt_id t).add_const y
  have hden : HasDerivAt (fun s : ℝ ↦ 3 * (s + y) ^ 5)
      (15 * (t + y) ^ 4) t := by
    convert (hu.pow 5).const_mul 3 using 1
    all_goals ring
  have hden_ne : 3 * (t + y) ^ 5 ≠ 0 := by positivity
  unfold diagonalFifthMajorantPrimitive diagonalFifthMajorant
  convert (hasDerivAt_const t (-4 : ℝ)).div hden hden_ne using 1
  field_simp [hyt]
  ring

private theorem intervalIntegrable_diagonalFifthMajorant
    {y a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ t ∈ Icc a b, 0 < t + y) :
    IntervalIntegrable (diagonalFifthMajorant y) volume a b := by
  have hcont : ContinuousOn (diagonalFifthMajorant y) (Icc a b) := by
    unfold diagonalFifthMajorant
    exact continuousOn_const.div
      (continuousOn_const.mul ((continuousOn_id.add continuousOn_const).pow 6))
      (fun t ht ↦ by
        have := hpos t ht
        positivity)
  exact hcont.intervalIntegrable_of_Icc hab

private theorem integral_diagonalFifthMajorant
    {y a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ t ∈ Icc a b, 0 < t + y) :
    (∫ t in a..b, diagonalFifthMajorant y t) =
      diagonalFifthMajorantPrimitive y b -
        diagonalFifthMajorantPrimitive y a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    have ht' : t ∈ Icc a b := by
      rwa [uIcc_of_le hab] at ht
    exact hasDerivAt_diagonalFifthMajorantPrimitive (hpos t ht').ne'
  · exact intervalIntegrable_diagonalFifthMajorant hab hpos

private def diagonalHighCorrectedError (y : ℝ) (k : ℕ) : ℝ :=
  shiftedTrapezoidalError (1 / 4) y k -
      (diagonalHighProfileDeriv y (k + 1) -
        diagonalHighProfileDeriv y k) / 12 +
    (diagonalHighProfileThirdDeriv y (k + 1) -
      diagonalHighProfileThirdDeriv y k) / 720

private theorem diagonalHighCorrectedError_abs_le
    {y : ℝ} (hy : 0 < y) (k : ℕ) :
    |diagonalHighCorrectedError y k| ≤
      ∫ t in (k : ℝ)..k + 1, diagonalFifthMajorant y t := by
  have hfifth_int : IntervalIntegrable (diagonalHighProfileFifthDeriv y)
      volume (k : ℝ) (k + 1) :=
    (continuous_diagonalHighProfileFifthDeriv hy.ne').intervalIntegrable _ _
  have hid :=
    trapezoidal_error_one_sub_first_add_third_eq_integral_fifth
      (f := diagonalHighProfile y)
      (f1 := diagonalHighProfileDeriv y)
      (f2 := diagonalHighProfileSecondDeriv y)
      (f3 := diagonalHighProfileThirdDeriv y)
      (f4 := diagonalHighProfileFourthDeriv y)
      (f5 := diagonalHighProfileFifthDeriv y)
      (a := (k : ℝ))
      (fun t ↦ hasDerivAt_diagonalHighProfile hy.ne')
      (fun t ↦ hasDerivAt_diagonalHighProfileDeriv hy.ne')
      (fun t ↦ hasDerivAt_diagonalHighProfileSecondDeriv hy.ne')
      (fun t ↦ hasDerivAt_diagonalHighProfileThirdDeriv hy.ne')
      (fun t ↦ hasDerivAt_diagonalHighProfileFourthDeriv hy.ne')
      hfifth_int
  have hid' : diagonalHighCorrectedError y k =
      -(∫ t in (k : ℝ)..k + 1,
        correctedTrapezoidFifthKernel k t *
          diagonalHighProfileFifthDeriv y t) := by
    unfold diagonalHighCorrectedError shiftedTrapezoidalError
    rw [show shiftedReciprocalRealPart (1 / 4) y =
        diagonalHighProfile y by
      funext t
      simp [shiftedReciprocalRealPart, diagonalHighProfile, add_comm]]
    simpa [shiftedReciprocalRealPart, diagonalHighProfile, add_comm,
      Nat.cast_add, Nat.cast_one] using hid
  rw [hid', abs_neg]
  have hleft_int : IntervalIntegrable
      (fun t : ℝ ↦
        |correctedTrapezoidFifthKernel k t *
          diagonalHighProfileFifthDeriv y t|)
      volume (k : ℝ) (k + 1) := by
    have hkernel : Continuous (correctedTrapezoidFifthKernel (k : ℝ)) := by
      unfold correctedTrapezoidFifthKernel
      fun_prop
    exact (hkernel.mul
      (continuous_diagonalHighProfileFifthDeriv hy.ne')).abs.intervalIntegrable _ _
  have hpos : ∀ t ∈ Icc (k : ℝ) (k + 1), 0 < t + y := by
    intro t ht
    have htk : (0 : ℝ) ≤ t := (Nat.cast_nonneg k).trans ht.1
    linarith
  have hright_int : IntervalIntegrable (diagonalFifthMajorant y)
      volume (k : ℝ) (k + 1) :=
    intervalIntegrable_diagonalFifthMajorant (by norm_num) hpos
  calc
    |∫ t in (k : ℝ)..k + 1,
        correctedTrapezoidFifthKernel k t *
          diagonalHighProfileFifthDeriv y t| ≤
        ∫ t in (k : ℝ)..k + 1,
          |correctedTrapezoidFifthKernel k t *
            diagonalHighProfileFifthDeriv y t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in (k : ℝ)..k + 1, diagonalFifthMajorant y t := by
      apply intervalIntegral.integral_mono_on (by norm_num) hleft_int hright_int
      intro t ht
      rw [abs_mul]
      calc
        |correctedTrapezoidFifthKernel k t| *
            |diagonalHighProfileFifthDeriv y t| ≤
            (1 / 720 : ℝ) * |diagonalHighProfileFifthDeriv y t| :=
          mul_le_mul_of_nonneg_right
            (abs_correctedTrapezoidFifthKernel_le ht)
            (abs_nonneg _)
        _ ≤ diagonalFifthMajorant y t :=
          one_div_720_mul_abs_fifth_le_majorant hy
            ((Nat.cast_nonneg k).trans ht.1)

private theorem diagonalHighCorrectedError_sum_abs_le
    {y : ℝ} (hy : 0 < y) (N : ℕ) :
    |∑ k ∈ Finset.range N, diagonalHighCorrectedError y k| ≤
      4 / (3 * y ^ 5) := by
  calc
    |∑ k ∈ Finset.range N, diagonalHighCorrectedError y k| ≤
        ∑ k ∈ Finset.range N, |diagonalHighCorrectedError y k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N,
        ∫ t in (k : ℝ)..k + 1, diagonalFifthMajorant y t := by
      exact Finset.sum_le_sum fun k _hk ↦
        diagonalHighCorrectedError_abs_le hy k
    _ = ∑ k ∈ Finset.range N,
        (diagonalFifthMajorantPrimitive y (k + 1) -
          diagonalFifthMajorantPrimitive y k) := by
      apply Finset.sum_congr rfl
      intro k _hk
      apply integral_diagonalFifthMajorant (by norm_num)
      intro t ht
      have htk : (0 : ℝ) ≤ t := (Nat.cast_nonneg k).trans ht.1
      linarith
    _ = diagonalFifthMajorantPrimitive y N -
        diagonalFifthMajorantPrimitive y 0 := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
        (Finset.sum_range_sub
          (fun k : ℕ ↦ diagonalFifthMajorantPrimitive y (k : ℝ)) N)
    _ ≤ 4 / (3 * y ^ 5) := by
      have hNy : 0 < (N : ℝ) + y := by positivity
      have hnonpos :
          (-4 : ℝ) / (3 * ((N : ℝ) + y) ^ 5) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
      unfold diagonalFifthMajorantPrimitive
      norm_num only [Nat.cast_zero, zero_add]
      calc
        (-4 : ℝ) / (3 * ((N : ℝ) + y) ^ 5) -
            -4 / (3 * y ^ 5) =
            (-4 : ℝ) / (3 * ((N : ℝ) + y) ^ 5) +
              4 / (3 * y ^ 5) := by ring
        _ ≤ 0 + 4 / (3 * y ^ 5) :=
          add_le_add hnonpos (le_refl (4 / (3 * y ^ 5)))
        _ = 4 / (3 * y ^ 5) := by ring

private theorem abs_diagonalHighProfileDeriv_nat_le
    {y : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    |diagonalHighProfileDeriv y N| ≤ 1 / (N : ℝ) := by
  let n : ℝ := N
  let u : ℝ := n + 1 / 4
  let D : ℝ := u ^ 2 + y ^ 2
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast hN
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hu : 0 < u := by
    dsimp [u]
    linarith
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hnum : |y ^ 2 - u ^ 2| ≤ D := by
    rw [abs_le]
    dsimp [D]
    constructor <;> nlinarith [sq_nonneg y, sq_nonneg u]
  have hnu : n ≤ u := by
    dsimp [u]
    norm_num
  have hnSq : n ≤ n ^ 2 := by
    nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hn)]
  have hNuSq : n ≤ u ^ 2 :=
    hnSq.trans (pow_le_pow_left₀ hn0.le hnu 2)
  unfold diagonalHighProfileDeriv reciprocalRealPartDeriv
  change |(y ^ 2 - u ^ 2) / D ^ 2| ≤ 1 / n
  rw [abs_div, abs_of_pos (pow_pos hD 2)]
  calc
    |y ^ 2 - u ^ 2| / D ^ 2 ≤ D / D ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg D)
    _ = 1 / D := by
      field_simp [hD.ne']
    _ ≤ 1 / u ^ 2 := by
      apply one_div_le_one_div_of_le (sq_pos_of_pos hu)
      dsimp [D]
      nlinarith [sq_nonneg y]
    _ ≤ 1 / n := one_div_le_one_div_of_le hn0 hNuSq

private theorem tendsto_diagonalHighProfileDeriv_nat (y : ℝ) :
    Tendsto (fun N : ℕ ↦ diagonalHighProfileDeriv y N)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N ↦ abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact abs_diagonalHighProfileDeriv_nat_le hN
  · exact tendsto_const_div_atTop_nhds_zero_nat 1

private theorem abs_diagonalHighProfileThirdDeriv_nat_le
    {y : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    |diagonalHighProfileThirdDeriv y N| ≤ 18 / (N : ℝ) := by
  let n : ℝ := N
  let u : ℝ := n + 1 / 4
  let D : ℝ := u ^ 2 + y ^ 2
  let Q : ℝ := u ^ 4 - 6 * u ^ 2 * y ^ 2 + y ^ 4
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast hN
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hu : 0 < u := by
    dsimp [u]
    linarith
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hu4 : 0 ≤ u ^ 4 := pow_nonneg hu.le 4
  have hy4 : 0 ≤ y ^ 4 := by positivity
  have hu2y2 : 0 ≤ u ^ 2 * y ^ 2 :=
    mul_nonneg (sq_nonneg u) (sq_nonneg y)
  have hQ : |Q| ≤ u ^ 4 + 6 * u ^ 2 * y ^ 2 + y ^ 4 := by
    rw [abs_le]
    constructor <;> dsimp [Q] <;> nlinarith
  have hDexpand :
      3 * D ^ 2 = 3 * u ^ 4 + 6 * u ^ 2 * y ^ 2 + 3 * y ^ 4 := by
    dsimp [D]
    ring
  have hQthree : |Q| ≤ 3 * D ^ 2 := by
    rw [hDexpand]
    nlinarith
  have hnu : n ≤ u := by
    dsimp [u]
    norm_num
  have hNuSq : n ≤ u ^ 2 := by
    have hnSq : n ≤ n ^ 2 := by
      nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hn)]
    exact hnSq.trans (pow_le_pow_left₀ hn0.le hnu 2)
  have hND : n ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg y]
  have hDOne : 1 ≤ D := hn.trans hND
  have hDDsq : D ≤ D ^ 2 := by
    nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hDOne)]
  have hNDsq : n ≤ D ^ 2 := hND.trans hDDsq
  unfold diagonalHighProfileThirdDeriv
  dsimp only
  change |(-6 : ℝ) * Q / D ^ 4| ≤ 18 / n
  rw [abs_div, abs_mul, abs_of_nonpos (by norm_num : (-6 : ℝ) ≤ 0),
    abs_of_pos (pow_pos hD 4)]
  norm_num only [neg_neg]
  calc
    6 * |Q| / D ^ 4 ≤ 6 * (3 * D ^ 2) / D ^ 4 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQthree (by norm_num)) (pow_nonneg hD.le 4)
    _ = 18 / D ^ 2 := by
      field_simp [hD.ne']
      ring
    _ ≤ 18 / n :=
      div_le_div_of_nonneg_left (by norm_num) hn0 hNDsq

private theorem tendsto_diagonalHighProfileThirdDeriv_nat (y : ℝ) :
    Tendsto (fun N : ℕ ↦ diagonalHighProfileThirdDeriv y N)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N ↦ abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact abs_diagonalHighProfileThirdDeriv_nat_le hN
  · exact tendsto_const_div_atTop_nhds_zero_nat 18

private theorem sum_range_diagonalHighCorrectedError_eq
    (y : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, diagonalHighCorrectedError y k) =
      (∑ k ∈ Finset.range N,
        shiftedTrapezoidalError (1 / 4) y k) -
        (diagonalHighProfileDeriv y N -
          diagonalHighProfileDeriv y 0) / 12 +
        (diagonalHighProfileThirdDeriv y N -
          diagonalHighProfileThirdDeriv y 0) / 720 := by
  have htelOne :
      (∑ k ∈ Finset.range N,
        (diagonalHighProfileDeriv y (k + 1) -
          diagonalHighProfileDeriv y k)) =
        diagonalHighProfileDeriv y N - diagonalHighProfileDeriv y 0 := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
      (Finset.sum_range_sub
        (fun k : ℕ ↦ diagonalHighProfileDeriv y (k : ℝ)) N)
  have htelThree :
      (∑ k ∈ Finset.range N,
        (diagonalHighProfileThirdDeriv y (k + 1) -
          diagonalHighProfileThirdDeriv y k)) =
        diagonalHighProfileThirdDeriv y N -
          diagonalHighProfileThirdDeriv y 0 := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
      (Finset.sum_range_sub
        (fun k : ℕ ↦ diagonalHighProfileThirdDeriv y (k : ℝ)) N)
  simp only [diagonalHighCorrectedError, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [← Finset.sum_div, ← Finset.sum_div, htelOne, htelThree]

private theorem tendsto_neg_sum_diagonalHighCorrectedError
    {y : ℝ} (hy : 0 < y) :
    Tendsto
      (fun N : ℕ ↦
        -(∑ k ∈ Finset.range N, diagonalHighCorrectedError y k))
      atTop
      (nhds (-∑' k : ℕ, shiftedTrapezoidalError (1 / 4) y k -
        diagonalHighProfileDeriv y 0 / 12 +
        diagonalHighProfileThirdDeriv y 0 / 720)) := by
  have herr := (summable_shiftedTrapezoidalError
    (x := (1 / 4 : ℝ)) (y := y) (by norm_num) hy).hasSum.tendsto_sum_nat
  have hone := tendsto_diagonalHighProfileDeriv_nat y
  have hthree := tendsto_diagonalHighProfileThirdDeriv_nat y
  have honeZero : Tendsto
      (fun _ : ℕ ↦ diagonalHighProfileDeriv y 0) atTop
      (nhds (diagonalHighProfileDeriv y 0)) := tendsto_const_nhds
  have hthreeZero : Tendsto
      (fun _ : ℕ ↦ diagonalHighProfileThirdDeriv y 0) atTop
      (nhds (diagonalHighProfileThirdDeriv y 0)) := tendsto_const_nhds
  have hlim := ((herr.sub
      ((hone.sub honeZero).div_const 12)).add
      ((hthree.sub hthreeZero).div_const 720)).neg
  convert hlim using 1
  · funext N
    rw [sum_range_diagonalHighCorrectedError_eq]
  · ring_nf

theorem digamma_quarter_vertical_re_sub_highMain_abs_le
    {y : ℝ} (hy : 0 < y) :
    |(Complex.digamma ((1 / 4 : ℝ) + y * Complex.I)).re -
        diagonalDigammaMain y| ≤ 4 / (3 * y ^ 5) := by
  have hdigBase :=
    digamma_quarter_vertical_re_eq_primitive_sub_trapezoidalErrors
      (v := 2 * y) (by positivity)
  have hdig :
      (Complex.digamma ((1 / 4 : ℝ) + y * Complex.I)).re =
        shiftedReciprocalPrimitive (1 / 4) y 0 -
          shiftedReciprocalRealPart (1 / 4) y 0 / 2 -
          ∑' k : ℕ, shiftedTrapezoidalError (1 / 4) y k := by
    have htwo : 2 * y / 2 = y := by ring
    have htwoComplex : (((2 * y : ℝ) : ℂ) / 2) = (y : ℂ) := by
      push_cast
      ring
    rw [htwo] at hdigBase
    rw [htwoComplex] at hdigBase
    exact hdigBase
  have hprimitive :
      shiftedReciprocalPrimitive (1 / 4) y 0 =
        Real.log ((1 / 16 : ℝ) + y ^ 2) / 2 := by
    unfold shiftedReciprocalPrimitive
    norm_num
    ring
  have hprofile :
      shiftedReciprocalRealPart (1 / 4) y 0 =
        diagonalHighProfile y 0 := by
    simp [shiftedReciprocalRealPart, diagonalHighProfile, add_comm]
  have htarget :
      (Complex.digamma ((1 / 4 : ℝ) + y * Complex.I)).re -
          diagonalDigammaMain y =
        -∑' k : ℕ, shiftedTrapezoidalError (1 / 4) y k -
          diagonalHighProfileDeriv y 0 / 12 +
          diagonalHighProfileThirdDeriv y 0 / 720 := by
    rw [hdig, hprimitive, hprofile]
    unfold diagonalDigammaMain
    ring
  have hlim := tendsto_neg_sum_diagonalHighCorrectedError hy
  have hlim' : Tendsto
      (fun N : ℕ ↦
        -(∑ k ∈ Finset.range N, diagonalHighCorrectedError y k))
      atTop
      (nhds ((Complex.digamma
        ((1 / 4 : ℝ) + y * Complex.I)).re - diagonalDigammaMain y)) := by
    rw [htarget]
    exact hlim
  exact le_of_tendsto' hlim'.abs fun N ↦ by
    simpa only [abs_neg] using diagonalHighCorrectedError_sum_abs_le hy N

end ArithmeticHodge.Analysis.YoshidaDiagonalDigammaHighBound
