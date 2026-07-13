import ArithmeticHodge.Analysis.YoshidaRegularKernelBound
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaRegularKernelLowerBound

open YoshidaRegularKernelBound

noncomputable section

/-!
# Exact lower bound for Yoshida's regular kernel

The regular kernel stays within `1 / 32` of its removable value `1 / 4`
on the full endpoint interval.  The proof is structural: a two-term
logarithm estimate reduces the claim to convexity of an explicit polynomial.
-/

private def lowerPolynomial (r : ℝ) : ℝ :=
  13 * r ^ 7 - 19 * r ^ 6 + 12 * r ^ 5 - 20 * r ^ 4 +
    16 * r ^ 3 - 16 * r ^ 2 + r + 1

private def lowerPolynomialDeriv (r : ℝ) : ℝ :=
  91 * r ^ 6 - 114 * r ^ 5 + 60 * r ^ 4 - 80 * r ^ 3 +
    48 * r ^ 2 - 32 * r + 1

private def lowerPolynomialDeriv2 (r : ℝ) : ℝ :=
  546 * r ^ 5 - 570 * r ^ 4 + 240 * r ^ 3 - 240 * r ^ 2 +
    96 * r - 32

private theorem lowerPolynomial_hasDerivAt (r : ℝ) :
    HasDerivAt lowerPolynomial (lowerPolynomialDeriv r) r := by
  unfold lowerPolynomial lowerPolynomialDeriv
  have h7 := ((hasDerivAt_id r).pow 7).const_mul 13
  have h6 := ((hasDerivAt_id r).pow 6).const_mul 19
  have h5 := ((hasDerivAt_id r).pow 5).const_mul 12
  have h4 := ((hasDerivAt_id r).pow 4).const_mul 20
  have h3 := ((hasDerivAt_id r).pow 3).const_mul 16
  have h2 := ((hasDerivAt_id r).pow 2).const_mul 16
  convert ((((((h7.sub h6).add h5).sub h4).add h3).sub h2).add
    (hasDerivAt_id r)).add (hasDerivAt_const r 1) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem lowerPolynomialDeriv_hasDerivAt (r : ℝ) :
    HasDerivAt lowerPolynomialDeriv (lowerPolynomialDeriv2 r) r := by
  unfold lowerPolynomialDeriv lowerPolynomialDeriv2
  have h6 := ((hasDerivAt_id r).pow 6).const_mul 91
  have h5 := ((hasDerivAt_id r).pow 5).const_mul 114
  have h4 := ((hasDerivAt_id r).pow 4).const_mul 60
  have h3 := ((hasDerivAt_id r).pow 3).const_mul 80
  have h2 := ((hasDerivAt_id r).pow 2).const_mul 48
  have h1 := (hasDerivAt_id r).const_mul 32
  convert (((((h6.sub h5).add h4).sub h3).add h2).sub h1).add
    (hasDerivAt_const r 1) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem lowerPolynomial_convex :
    ConvexOn ℝ (Icc 1 (Real.sqrt 2)) lowerPolynomial := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (D := Icc (1 : ℝ) (Real.sqrt 2))
    (f' := lowerPolynomialDeriv) (f'' := lowerPolynomialDeriv2)
    (convex_Icc _ _) ?_ ?_ ?_ ?_
  · unfold lowerPolynomial
    fun_prop
  · intro r _hr
    exact (lowerPolynomial_hasDerivAt r).hasDerivWithinAt
  · intro r _hr
    exact (lowerPolynomialDeriv_hasDerivAt r).hasDerivWithinAt
  · intro r hr
    have hr1 : 1 ≤ r := (interior_subset hr).1
    have hu : 0 ≤ r - 1 := by linarith
    rw [show lowerPolynomialDeriv2 r =
        2 * (273 * (r - 1) ^ 5 + 1080 * (r - 1) ^ 4 +
          1710 * (r - 1) ^ 3 + 1260 * (r - 1) ^ 2 +
          393 * (r - 1) + 20) by
      unfold lowerPolynomialDeriv2
      ring]
    positivity

private theorem sqrt_two_lt_seventeen_div_twelve :
    Real.sqrt 2 < (17 / 12 : ℝ) := by
  rw [Real.sqrt_lt (by norm_num) (by norm_num)]
  norm_num

private theorem lowerPolynomial_sqrt_two :
    lowerPolynomial (Real.sqrt 2) = 185 * Real.sqrt 2 - 263 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold lowerPolynomial
  calc
    13 * Real.sqrt 2 ^ 7 - 19 * Real.sqrt 2 ^ 6 +
          12 * Real.sqrt 2 ^ 5 - 20 * Real.sqrt 2 ^ 4 +
          16 * Real.sqrt 2 ^ 3 - 16 * Real.sqrt 2 ^ 2 +
          Real.sqrt 2 + 1 =
        13 * (Real.sqrt 2 ^ 2) ^ 3 * Real.sqrt 2 -
          19 * (Real.sqrt 2 ^ 2) ^ 3 +
          12 * (Real.sqrt 2 ^ 2) ^ 2 * Real.sqrt 2 -
          20 * (Real.sqrt 2 ^ 2) ^ 2 +
          16 * (Real.sqrt 2 ^ 2) * Real.sqrt 2 -
          16 * (Real.sqrt 2 ^ 2) + Real.sqrt 2 + 1 := by ring
    _ = 185 * Real.sqrt 2 - 263 := by rw [hs]; ring

private theorem lowerPolynomial_nonpos
    {r : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ Real.sqrt 2) :
    lowerPolynomial r ≤ 0 := by
  have hmax := lowerPolynomial_convex.le_max_of_mem_Icc
    (⟨le_rfl, Real.one_lt_sqrt_two.le⟩ : (1 : ℝ) ∈ Icc 1 (Real.sqrt 2))
    (⟨Real.one_lt_sqrt_two.le, le_rfl⟩ : Real.sqrt 2 ∈ Icc 1 (Real.sqrt 2))
    (⟨hr1, hr2⟩ : r ∈ Icc 1 (Real.sqrt 2))
  have hleft : lowerPolynomial 1 ≤ 0 := by
    norm_num [lowerPolynomial]
  have hright : lowerPolynomial (Real.sqrt 2) ≤ 0 := by
    rw [lowerPolynomial_sqrt_two]
    linarith [sqrt_two_lt_seventeen_div_twelve]
  exact hmax.trans (max_le hleft hright)

/-- Yoshida's regular kernel is at least `7 / 32` throughout the endpoint
interval `[0, log 2]`. -/
theorem seven_div_thirty_two_le_yoshidaRegularKernel
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ Real.log 2) :
    (7 / 32 : ℝ) ≤ yoshidaRegularKernel t := by
  by_cases ht : t = 0
  · norm_num [yoshidaRegularKernel, ht]
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    let r : ℝ := Real.exp (t / 2)
    have hrpos : 0 < r := by
      dsimp only [r]
      positivity
    have hr1lt : 1 < r := by
      exact Real.one_lt_exp_iff.mpr (by linarith : 0 < t / 2)
    have hr1 : 1 ≤ r := hr1lt.le
    have hr2 : r ≤ Real.sqrt 2 := by
      dsimp only [r]
      calc
        Real.exp (t / 2) ≤ Real.exp (Real.log 2 / 2) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = Real.sqrt 2 := by
          rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          exact Real.exp_log (Real.sqrt_pos.2 (by norm_num))
    have hrSq : r ^ 2 = Real.exp t := by
      dsimp only [r]
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
    have hP := lowerPolynomial_nonpos hr1 hr2
    let D : ℝ := 32 * (r + 1) * (r ^ 2 + 1) *
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
        0 ≤ r ^ 3 / (r ^ 4 - 1) - 1 / (4 * A) - 7 / 32 := by
      rw [show r ^ 3 / (r ^ 4 - 1) - 1 / (4 * A) - 7 / 32 =
          -lowerPolynomial r / D by
        rw [hAformula]
        dsimp only [D]
        unfold lowerPolynomial
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
      (7 / 32 : ℝ) ≤ r ^ 3 / (r ^ 4 - 1) - 1 / (4 * A) := by
        linarith
      _ ≤ r ^ 3 / (r ^ 4 - 1) - 1 / (2 * t) :=
        sub_le_sub_left hrecip _

end

end ArithmeticHodge.Analysis.YoshidaRegularKernelLowerBound
