import ArithmeticHodge.Analysis.YoshidaConstantBounds
import ArithmeticHodge.Analysis.YoshidaRegularKernelBound

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelLowerStructural

noncomputable section

open YoshidaConstantBounds
open YoshidaRegularKernelBound

/-!
# A regular-kernel lower bound on the four-cell range

This module isolates the pointwise regular-kernel estimate used by both parity
closures.  It depends only on the common constant and regular-kernel modules,
so neither parity proof needs to import the other.
-/

private def fourCellRegularLowerPolynomial (r : ℝ) : ℝ :=
  31 * r ^ 7 - 49 * r ^ 6 + 27 * r ^ 5 - 53 * r ^ 4 +
    37 * r ^ 3 - 43 * r ^ 2 + r + 1

private theorem fourCellRegularLowerPolynomial_nonpos
    {r : ℝ} (hr1 : 1 ≤ r) (hr8 : r ≤ 8 / 5) :
    fourCellRegularLowerPolynomial r ≤ 0 := by
  let u : ℝ := (5 / 3 : ℝ) * (r - 1)
  have hu0 : 0 ≤ u := by
    have hr : 0 ≤ r - 1 := sub_nonneg.mpr hr1
    dsimp only [u]
    positivity
  have hu1 : u ≤ 1 := by
    dsimp only [u]
    linarith
  have hone : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  rw [show fourCellRegularLowerPolynomial r =
      -(48 * (1 - u) ^ 7 +
        (2064 / 5 : ℝ) * u * (1 - u) ^ 6 +
        (37296 / 25 : ℝ) * u ^ 2 * (1 - u) ^ 5 +
        2904 * u ^ 3 * (1 - u) ^ 4 +
        (2011008 / 625 : ℝ) * u ^ 4 * (1 - u) ^ 3 +
        (6041808 / 3125 : ℝ) * u ^ 5 * (1 - u) ^ 2 +
        (7870008 / 15625 : ℝ) * u ^ 6 * (1 - u) +
        (788043 / 78125 : ℝ) * u ^ 7) by
    dsimp only [u, fourCellRegularLowerPolynomial]
    ring]
  apply neg_nonpos.mpr
  positivity

/-- The Yoshida regular kernel remains at least `1 / 5` on every argument
produced by the four-cell positive-half fold.  The two-term logarithm lower
bound leaves a polynomial whose Bernstein coefficients on
`1 ≤ exp (t / 2) ≤ 8 / 5` are all negative. -/
theorem one_fifth_le_yoshidaRegularKernel_fourCellRange
    {t : ℝ} (ht0 : 0 ≤ t) (ht4 : t ≤ 5 * Real.log 2 / 4) :
    (1 / 5 : ℝ) ≤ yoshidaRegularKernel t := by
  by_cases ht : t = 0
  · norm_num [yoshidaRegularKernel, ht]
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    let u : ℝ := t / 2
    let r : ℝ := Real.exp u
    have hu0 : 0 ≤ u := by
      dsimp only [u]
      linarith
    have hu7 : u ≤ 7 / 16 := by
      dsimp only [u]
      have hlog := strict_log_two_bounds.2
      linarith
    have hu1 : u ≤ 1 := hu7.trans (by norm_num)
    have hexp := Real.exp_bound' hu0 hu1 (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ] at hexp
    have hexp8 : Real.exp u ≤ 8 / 5 := by
      calc
        Real.exp u ≤
            1 + u + u ^ 2 / 2 + u ^ 3 / 6 + 5 * u ^ 4 / 96 := by
          linarith
        _ ≤ 1 + (7 / 16 : ℝ) + (7 / 16 : ℝ) ^ 2 / 2 +
            (7 / 16 : ℝ) ^ 3 / 6 +
              5 * (7 / 16 : ℝ) ^ 4 / 96 := by
          gcongr
        _ ≤ 8 / 5 := by norm_num
    have hrpos : 0 < r := by
      dsimp only [r]
      positivity
    have hr1lt : 1 < r := by
      dsimp only [r, u]
      exact Real.one_lt_exp_iff.mpr (by linarith)
    have hr1 : 1 ≤ r := hr1lt.le
    have hr8 : r ≤ 8 / 5 := by
      simpa only [r] using hexp8
    have hrSq : r ^ 2 = Real.exp t := by
      dsimp only [r, u]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hrSqOne : 1 < r ^ 2 := by
      nlinarith [sq_nonneg (r - 1)]
    have hrFourthOne : 1 < r ^ 4 := by
      nlinarith [sq_nonneg (r ^ 2 - 1)]
    let z : ℝ := (r ^ 2 - 1) / (r ^ 2 + 1)
    have hzden : 0 < r ^ 2 + 1 := by positivity
    have hzpos : 0 < z := by
      dsimp only [z]
      exact div_pos (sub_pos.2 hrSqOne) hzden
    have hz0 : 0 ≤ z := hzpos.le
    have hz1 : z < 1 := by
      dsimp only [z]
      rw [div_lt_one hzden]
      linarith
    have hratio : (1 + z) / (1 - z) = r ^ 2 := by
      dsimp only [z]
      field_simp [ne_of_gt hzden]
      ring
    have hseries := Real.sum_range_le_log_div hz0 hz1 2
    norm_num [Finset.sum_range_succ] at hseries
    rw [hratio, hrSq, Real.log_exp] at hseries
    let A : ℝ := z + z ^ 3 / 3
    have hApos : 0 < A := by
      dsimp only [A]
      positivity
    have hAt : 2 * A ≤ t := by
      dsimp only [A]
      linarith
    have hrecip : 1 / (2 * t) ≤ 1 / (4 * A) := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * t)
        (by positivity : 0 < 4 * A)]
      nlinarith
    have hP := fourCellRegularLowerPolynomial_nonpos hr1 hr8
    let D : ℝ := 80 * (r + 1) * (r ^ 2 + 1) *
      (r ^ 2 - r + 1) * (r ^ 2 + r + 1)
    have hminus : 0 < r ^ 2 - r + 1 := by
      nlinarith [sq_nonneg (r - 1 / 2)]
    have hplus : 0 < r ^ 2 + r + 1 := by nlinarith
    have hmulMinus : r * (r - 1) + 1 ≠ 0 := by nlinarith
    have hmulPlus : r * (r + 1) + 1 ≠ 0 := by nlinarith
    have hDpos : 0 < D := by
      dsimp only [D]
      positivity
    have hAformula : A =
        4 * (r - 1) * (r + 1) * (r ^ 2 - r + 1) *
          (r ^ 2 + r + 1) / (3 * (r ^ 2 + 1) ^ 3) := by
      dsimp only [A, z]
      field_simp [ne_of_gt hzden]
      ring
    have hremainder :
        0 ≤ r ^ 3 / (r ^ 4 - 1) - 1 / (4 * A) - 1 / 5 := by
      rw [show r ^ 3 / (r ^ 4 - 1) - 1 / (4 * A) - 1 / 5 =
          -fourCellRegularLowerPolynomial r / D by
        rw [hAformula]
        dsimp only [D]
        unfold fourCellRegularLowerPolynomial
        field_simp [ne_of_gt hrpos, ne_of_gt hzden,
          ne_of_gt (sub_pos.2 hrFourthOne), ne_of_gt hApos,
          ne_of_gt (sub_pos.2 hr1lt)]
        field_simp [hmulMinus, hmulPlus]
        ring]
      exact div_nonneg (neg_nonneg.mpr hP) hDpos.le
    have hkernel : yoshidaRegularKernel t =
        r ^ 3 / (r ^ 4 - 1) - 1 / (2 * t) := by
      rw [yoshidaRegularKernel, if_neg ht, Real.sinh_eq, Real.exp_neg,
        ← hrSq]
      change r / (2 * ((r ^ 2 - (r ^ 2)⁻¹) / 2)) - 1 / (2 * t) =
        r ^ 3 / (r ^ 4 - 1) - 1 / (2 * t)
      field_simp [ne_of_gt hrpos, ne_of_gt (sub_pos.2 hrFourthOne)]
    rw [hkernel]
    calc
      (1 / 5 : ℝ) ≤ r ^ 3 / (r ^ 4 - 1) - 1 / (4 * A) := by
        linarith
      _ ≤ r ^ 3 / (r ^ 4 - 1) - 1 / (2 * t) :=
        sub_le_sub_left hrecip _

end

end ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelLowerStructural
