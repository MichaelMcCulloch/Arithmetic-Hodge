import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusStructural
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
open YoshidaFactorTwoPhaseLowSchur

/-!
# Rational Schur core for the intrinsic negative static split

The weak even direction is retained through the sum/difference coordinates
of the alternating block.  Once the four coupled correlations lie in the
displayed short intervals, a single exact `2 x 2` Schur complement is
positive.  There is no phase subdivision, sampled certificate, or mode
enumeration in this argument.
-/

def intrinsicStaticMinusEvenLower00 : ℝ := 11859 / 20000
def intrinsicStaticMinusEvenLower02 : ℝ := 27251 / 50000
def intrinsicStaticMinusEvenLower22 : ℝ := 10297 / 20000

def intrinsicStaticMinusOddLower11 : ℝ := 389 / 2000
def intrinsicStaticMinusOddLower13 : ℝ := 19 / 100
def intrinsicStaticMinusOddLower33 : ℝ := 1063 / 5000

def intrinsicStaticMinusEvenLower (c0 c2 : ℝ) : ℝ :=
  intrinsicStaticMinusEvenLower00 * c0 ^ 2 +
    2 * intrinsicStaticMinusEvenLower02 * c0 * c2 +
    intrinsicStaticMinusEvenLower22 * c2 ^ 2

def intrinsicStaticMinusOddLower (c1 c3 : ℝ) : ℝ :=
  intrinsicStaticMinusOddLower11 * c1 ^ 2 +
    2 * intrinsicStaticMinusOddLower13 * c1 * c3 +
    intrinsicStaticMinusOddLower33 * c3 ^ 2

theorem intrinsicStaticMinusEvenLower_principal_minors_pos :
    0 < intrinsicStaticMinusEvenLower00 ∧
      0 < intrinsicStaticMinusEvenLower00 *
          intrinsicStaticMinusEvenLower22 -
        intrinsicStaticMinusEvenLower02 ^ 2 := by
  norm_num [intrinsicStaticMinusEvenLower00,
    intrinsicStaticMinusEvenLower02, intrinsicStaticMinusEvenLower22]

theorem intrinsicStaticMinusOddLower_principal_minors_pos :
    0 < intrinsicStaticMinusOddLower11 ∧
      0 < intrinsicStaticMinusOddLower11 *
          intrinsicStaticMinusOddLower33 -
        intrinsicStaticMinusOddLower13 ^ 2 := by
  norm_num [intrinsicStaticMinusOddLower11,
    intrinsicStaticMinusOddLower13, intrinsicStaticMinusOddLower33]

/-- The rational even Gram lies below the complete even-minus endpoint.
The clean and negative-perturbation lower forms are added before any entry is
discarded. -/
theorem intrinsicStaticMinusEvenLower_le (c0 c2 : ℝ) :
    intrinsicStaticMinusEvenLower c0 c2 ≤
      factorTwoIntrinsicStaticEvenQuadratic (-1) c0 c2 := by
  have hclean := intrinsicEven_clean_rationalQuadratic_le c0 c2
  have hpert := evenNegativePerturbationSharp_quadratic_le c0 c2
  rw [factorTwoCenteredSymmetricPerturbation_structuralLow] at hpert
  unfold evenNegativePerturbationSharp00
    evenNegativePerturbationSharp02
    evenNegativePerturbationSharp22 at hpert
  unfold intrinsicStaticMinusEvenLower
    intrinsicStaticMinusEvenLower00 intrinsicStaticMinusEvenLower02
    intrinsicStaticMinusEvenLower22
    factorTwoIntrinsicStaticEvenQuadratic
    factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22 at ⊢
  norm_num at hclean hpert ⊢
  nlinarith

/-- The four short coupled intervals needed by the rational Schur core. -/
def FactorTwoIntrinsicAlternatingSharpBounds : Prop :=
  (56168 / 100000 : ℝ) <
      factorTwoIntrinsicAlternating01 + factorTwoIntrinsicAlternating21 ∧
    factorTwoIntrinsicAlternating01 + factorTwoIntrinsicAlternating21 <
      (56173 / 100000 : ℝ) ∧
  (1687 / 100000 : ℝ) <
      factorTwoIntrinsicAlternating01 - factorTwoIntrinsicAlternating21 ∧
    factorTwoIntrinsicAlternating01 - factorTwoIntrinsicAlternating21 <
      (1692 / 100000 : ℝ) ∧
  (53815 / 100000 : ℝ) <
      factorTwoIntrinsicAlternating03 + factorTwoIntrinsicAlternating23 ∧
    factorTwoIntrinsicAlternating03 + factorTwoIntrinsicAlternating23 <
      (53836 / 100000 : ℝ) ∧
  (2781 / 50000 : ℝ) <
      factorTwoIntrinsicAlternating03 - factorTwoIntrinsicAlternating23 ∧
    factorTwoIntrinsicAlternating03 - factorTwoIntrinsicAlternating23 <
      (348 / 6250 : ℝ)

private theorem rational_bilinear_cauchy_of_sum_difference_bounds
    (j01 j03 j21 j23 : ℝ)
    (hs1 : (56168 / 100000 : ℝ) < j01 + j21 ∧
      j01 + j21 < (56173 / 100000 : ℝ))
    (hd1 : (1687 / 100000 : ℝ) < j01 - j21 ∧
      j01 - j21 < (1692 / 100000 : ℝ))
    (hs3 : (53815 / 100000 : ℝ) < j03 + j23 ∧
      j03 + j23 < (53836 / 100000 : ℝ))
    (hd3 : (2781 / 50000 : ℝ) < j03 - j23 ∧
      j03 - j23 < (348 / 6250 : ℝ)) :
    ∀ c0 c2 c1 c3 : ℝ,
      (c0 * (j01 * c1 + j03 * c3) +
          c2 * (j21 * c1 + j23 * c3)) ^ 2 ≤
        4 * intrinsicStaticMinusEvenLower c0 c2 *
          intrinsicStaticMinusOddLower c1 c3 := by
  let q00 : ℝ := intrinsicStaticMinusEvenLower00
  let q02 : ℝ := intrinsicStaticMinusEvenLower02
  let q22 : ℝ := intrinsicStaticMinusEvenLower22
  let o11 : ℝ := intrinsicStaticMinusOddLower11
  let o13 : ℝ := intrinsicStaticMinusOddLower13
  let o33 : ℝ := intrinsicStaticMinusOddLower33
  let s1 : ℝ := j01 + j21
  let d1 : ℝ := j01 - j21
  let s3 : ℝ := j03 + j23
  let d3 : ℝ := j03 - j23
  have hs1L : (56168 / 100000 : ℝ) < s1 := by simpa only [s1] using hs1.1
  have hs1U : s1 < (56173 / 100000 : ℝ) := by simpa only [s1] using hs1.2
  have hd1L : (1687 / 100000 : ℝ) < d1 := by simpa only [d1] using hd1.1
  have hd1U : d1 < (1692 / 100000 : ℝ) := by simpa only [d1] using hd1.2
  have hs3L : (53815 / 100000 : ℝ) < s3 := by simpa only [s3] using hs3.1
  have hs3U : s3 < (53836 / 100000 : ℝ) := by simpa only [s3] using hs3.2
  have hd3L : (2781 / 50000 : ℝ) < d3 := by simpa only [d3] using hd3.1
  have hd3U : d3 < (348 / 6250 : ℝ) := by simpa only [d3] using hd3.2
  have hs1pos : 0 < s1 := (by norm_num : (0 : ℝ) < 56168 / 100000).trans hs1L
  have hd1pos : 0 < d1 := (by norm_num : (0 : ℝ) < 1687 / 100000).trans hd1L
  have hs3pos : 0 < s3 := (by norm_num : (0 : ℝ) < 53815 / 100000).trans hs3L
  have hd3pos : 0 < d3 := (by norm_num : (0 : ℝ) < 2781 / 50000).trans hd3L
  have hs1sqU : s1 ^ 2 < (56173 / 100000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hs1U hs1pos.le (by norm_num)
  have hd1sqU : d1 ^ 2 < (1692 / 100000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hd1U hd1pos.le (by norm_num)
  have hs3sqU : s3 ^ 2 < (53836 / 100000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hs3U hs3pos.le (by norm_num)
  have hd3sqU : d3 ^ 2 < (348 / 6250 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hd3U hd3pos.le (by norm_num)
  have hs1d1L :
      (56168 / 100000 : ℝ) * (1687 / 100000 : ℝ) < s1 * d1 := by
    calc
      (56168 / 100000 : ℝ) * (1687 / 100000 : ℝ) <
          s1 * (1687 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_right hs1L (by norm_num)
      _ < s1 * d1 := mul_lt_mul_of_pos_left hd1L hs1pos
  have hs3d3L :
      (53815 / 100000 : ℝ) * (2781 / 50000 : ℝ) < s3 * d3 := by
    calc
      (53815 / 100000 : ℝ) * (2781 / 50000 : ℝ) <
          s3 * (2781 / 50000 : ℝ) :=
        mul_lt_mul_of_pos_right hs3L (by norm_num)
      _ < s3 * d3 := mul_lt_mul_of_pos_left hd3L hs3pos
  have hs1s3L :
      (56168 / 100000 : ℝ) * (53815 / 100000 : ℝ) < s1 * s3 := by
    calc
      (56168 / 100000 : ℝ) * (53815 / 100000 : ℝ) <
          s1 * (53815 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_right hs1L (by norm_num)
      _ < s1 * s3 := mul_lt_mul_of_pos_left hs3L hs1pos
  have hs1s3U :
      s1 * s3 < (56173 / 100000 : ℝ) * (53836 / 100000 : ℝ) := by
    calc
      s1 * s3 < (56173 / 100000 : ℝ) * s3 :=
        mul_lt_mul_of_pos_right hs1U hs3pos
      _ < (56173 / 100000 : ℝ) * (53836 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_left hs3U (by norm_num)
  have hd1d3L :
      (1687 / 100000 : ℝ) * (2781 / 50000 : ℝ) < d1 * d3 := by
    calc
      (1687 / 100000 : ℝ) * (2781 / 50000 : ℝ) <
          d1 * (2781 / 50000 : ℝ) :=
        mul_lt_mul_of_pos_right hd1L (by norm_num)
      _ < d1 * d3 := mul_lt_mul_of_pos_left hd3L hd1pos
  have hd1d3U :
      d1 * d3 < (1692 / 100000 : ℝ) * (348 / 6250 : ℝ) := by
    calc
      d1 * d3 < (1692 / 100000 : ℝ) * d3 :=
        mul_lt_mul_of_pos_right hd1U hd3pos
      _ < (1692 / 100000 : ℝ) * (348 / 6250 : ℝ) :=
        mul_lt_mul_of_pos_left hd3U (by norm_num)
  have hs1d3L :
      (56168 / 100000 : ℝ) * (2781 / 50000 : ℝ) < s1 * d3 := by
    calc
      (56168 / 100000 : ℝ) * (2781 / 50000 : ℝ) <
          s1 * (2781 / 50000 : ℝ) :=
        mul_lt_mul_of_pos_right hs1L (by norm_num)
      _ < s1 * d3 := mul_lt_mul_of_pos_left hd3L hs1pos
  have hs1d3U :
      s1 * d3 < (56173 / 100000 : ℝ) * (348 / 6250 : ℝ) := by
    calc
      s1 * d3 < (56173 / 100000 : ℝ) * d3 :=
        mul_lt_mul_of_pos_right hs1U hd3pos
      _ < (56173 / 100000 : ℝ) * (348 / 6250 : ℝ) :=
        mul_lt_mul_of_pos_left hd3U (by norm_num)
  have hd1s3L :
      (1687 / 100000 : ℝ) * (53815 / 100000 : ℝ) < d1 * s3 := by
    calc
      (1687 / 100000 : ℝ) * (53815 / 100000 : ℝ) <
          d1 * (53815 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_right hd1L (by norm_num)
      _ < d1 * s3 := mul_lt_mul_of_pos_left hs3L hd1pos
  have hd1s3U :
      d1 * s3 < (1692 / 100000 : ℝ) * (53836 / 100000 : ℝ) := by
    calc
      d1 * s3 < (1692 / 100000 : ℝ) * s3 :=
        mul_lt_mul_of_pos_right hd1U hs3pos
      _ < (1692 / 100000 : ℝ) * (53836 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_left hs3U (by norm_num)
  let A11 : ℝ := q22 * j01 ^ 2 - 2 * q02 * j01 * j21 + q00 * j21 ^ 2
  let A13 : ℝ := q22 * j01 * j03 - q02 * (j01 * j23 + j21 * j03) +
    q00 * j21 * j23
  let A33 : ℝ := q22 * j03 ^ 2 - 2 * q02 * j03 * j23 + q00 * j23 ^ 2
  have hA11eq : A11 =
      ((q00 + q22 - 2 * q02) * s1 ^ 2 +
        (q00 + q22 + 2 * q02) * d1 ^ 2 +
        2 * (q22 - q00) * s1 * d1) / 4 := by
    dsimp only [A11, s1, d1]
    exact adjugateQuadratic_eq_sum_difference q00 q02 q22 j01 j21
  have hA13eq : A13 =
      ((q00 + q22 - 2 * q02) * s1 * s3 +
        (q00 + q22 + 2 * q02) * d1 * d3 +
        (q22 - q00) * (s1 * d3 + d1 * s3)) / 4 := by
    dsimp only [A13, s1, d1, s3, d3]
    exact adjugateBilinear_eq_sum_difference
      q00 q02 q22 j01 j21 j03 j23
  have hA33eq : A33 =
      ((q00 + q22 - 2 * q02) * s3 ^ 2 +
        (q00 + q22 + 2 * q02) * d3 ^ 2 +
        2 * (q22 - q00) * s3 * d3) / 4 := by
    dsimp only [A33, s3, d3]
    exact adjugateQuadratic_eq_sum_difference q00 q02 q22 j03 j23
  have hA11U : A11 < (59414162917 / 50000000000000 : ℝ) := by
    rw [hA11eq]
    norm_num [q00, q02, q22, intrinsicStaticMinusEvenLower00,
      intrinsicStaticMinusEvenLower02, intrinsicStaticMinusEvenLower22]
      at hs1sqU hd1sqU hs1d1L ⊢
    linarith only [hs1sqU, hd1sqU, hs1d1L]
  have hA13L : (1069 / 1000000 : ℝ) < A13 := by
    rw [hA13eq]
    norm_num [q00, q02, q22, intrinsicStaticMinusEvenLower00,
      intrinsicStaticMinusEvenLower02, intrinsicStaticMinusEvenLower22]
      at hs1s3L hd1d3L hs1d3U hd1s3U ⊢
    linarith only [hs1s3L, hd1d3L, hs1d3U, hd1s3U]
  have hA13U : A13 < (1074 / 1000000 : ℝ) := by
    rw [hA13eq]
    norm_num [q00, q02, q22, intrinsicStaticMinusEvenLower00,
      intrinsicStaticMinusEvenLower02, intrinsicStaticMinusEvenLower22]
      at hs1s3U hd1d3U hs1d3L hd1s3L ⊢
    linarith only [hs1s3U, hd1d3U, hs1d3L, hd1s3L]
  have hA33U : A33 < (18215 / 10000000 : ℝ) := by
    rw [hA33eq]
    norm_num [q00, q02, q22, intrinsicStaticMinusEvenLower00,
      intrinsicStaticMinusEvenLower02, intrinsicStaticMinusEvenLower22]
      at hs3sqU hd3sqU hs3d3L ⊢
    linarith only [hs3sqU, hd3sqU, hs3d3L]
  let D : ℝ := q00 * q22 - q02 ^ 2
  let r00 : ℝ := 4 * D * o11 - A11
  let r13 : ℝ := 4 * D * o13 - A13
  let r33 : ℝ := 4 * D * o33 - A33
  have hq00 : 0 < q00 := by
    norm_num [q00, intrinsicStaticMinusEvenLower00]
  have hD : 0 < D := by
    norm_num [D, q00, q02, q22, intrinsicStaticMinusEvenLower00,
      intrinsicStaticMinusEvenLower02, intrinsicStaticMinusEvenLower22]
  have hr00 : (5217 / 1000000 : ℝ) < r00 := by
    dsimp only [r00, D, q00, q02, q22, o11,
      intrinsicStaticMinusEvenLower00, intrinsicStaticMinusEvenLower02,
      intrinsicStaticMinusEvenLower22, intrinsicStaticMinusOddLower11]
    norm_num at hA11U ⊢
    linarith only [hA11U]
  have hr13pos : 0 < r13 := by
    dsimp only [r13, D, q00, q02, q22, o13,
      intrinsicStaticMinusEvenLower00, intrinsicStaticMinusEvenLower02,
      intrinsicStaticMinusEvenLower22, intrinsicStaticMinusOddLower13]
    norm_num at hA13U ⊢
    linarith only [hA13U]
  have hr13U : r13 < (5189 / 1000000 : ℝ) := by
    dsimp only [r13, D, q00, q02, q22, o13,
      intrinsicStaticMinusEvenLower00, intrinsicStaticMinusEvenLower02,
      intrinsicStaticMinusEvenLower22, intrinsicStaticMinusOddLower13]
    norm_num at hA13L ⊢
    linarith only [hA13L]
  have hr33 : (5180 / 1000000 : ℝ) < r33 := by
    dsimp only [r33, D, q00, q02, q22, o33,
      intrinsicStaticMinusEvenLower00, intrinsicStaticMinusEvenLower02,
      intrinsicStaticMinusEvenLower22, intrinsicStaticMinusOddLower33]
    norm_num at hA33U ⊢
    linarith only [hA33U]
  have hr00pos : 0 < r00 := (by norm_num : (0 : ℝ) < 5217 / 1000000).trans hr00
  have hr33pos : 0 < r33 := (by norm_num : (0 : ℝ) < 5180 / 1000000).trans hr33
  have hprod :
      (5217 / 1000000 : ℝ) * (5180 / 1000000 : ℝ) < r00 * r33 :=
    mul_lt_mul hr00 hr33.le (by norm_num) hr00pos.le
  have hrsq : r13 ^ 2 < (5189 / 1000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hr13U hr13pos.le (by norm_num)
  have hrdet : 0 < r00 * r33 - r13 ^ 2 := by
    have hrat : (5189 / 1000000 : ℝ) ^ 2 <
        (5217 / 1000000 : ℝ) * (5180 / 1000000 : ℝ) := by
      norm_num
    linarith only [hprod, hrsq, hrat]
  have hres : ∀ c1 c3 : ℝ,
      0 ≤ r00 * c1 ^ 2 + 2 * r13 * c1 * c3 + r33 * c3 ^ 2 := by
    intro c1 c3
    by_cases hne : c1 ≠ 0 ∨ c3 ≠ 0
    · exact (real_twoByTwo_quadratic_pos r00 r13 r33 c1 c3
        hr00pos hrdet hne).le
    · push_neg at hne
      rcases hne with ⟨rfl, rfl⟩
      norm_num
  have hschur : ∀ c1 c3 : ℝ,
      0 ≤
        4 * (q00 * q22 - q02 ^ 2) *
            (o11 * c1 ^ 2 + 2 * o13 * c1 * c3 + o33 * c3 ^ 2) -
          (q22 * (j01 * c1 + j03 * c3) ^ 2 -
            2 * q02 * (j01 * c1 + j03 * c3) *
              (j21 * c1 + j23 * c3) +
            q00 * (j21 * c1 + j23 * c3) ^ 2) := by
    intro c1 c3
    have h := hres c1 c3
    have heq :
        4 * (q00 * q22 - q02 ^ 2) *
              (o11 * c1 ^ 2 + 2 * o13 * c1 * c3 + o33 * c3 ^ 2) -
            (q22 * (j01 * c1 + j03 * c3) ^ 2 -
              2 * q02 * (j01 * c1 + j03 * c3) *
                (j21 * c1 + j23 * c3) +
              q00 * (j21 * c1 + j23 * c3) ^ 2) =
          r00 * c1 ^ 2 + 2 * r13 * c1 * c3 + r33 * c3 ^ 2 := by
      dsimp only [r00, r13, r33, D, A11, A13, A33]
      ring
    rw [heq]
    exact h
  have hcauchy := bilinear_sq_le_four_mul_of_schur
    q00 q02 q22 o11 o13 o33 j01 j03 j21 j23 hq00 hD hschur
  intro c0 c2 c1 c3
  have h := hcauchy c0 c2 c1 c3
  simpa only [intrinsicStaticMinusEvenLower,
    intrinsicStaticMinusOddLower, q00, q02, q22, o11, o13, o33] using h

/-- The sharp coupled alternating bounds imply the exact rational Cauchy
inequality between the two lower Grams. -/
theorem intrinsicStaticMinus_rationalCauchy_of_alternatingSharpBounds
    (hJ : FactorTwoIntrinsicAlternatingSharpBounds) :
    ∀ c0 c2 c1 c3 : ℝ,
      factorTwoIntrinsicStaticAlternating c0 c2 c1 c3 ^ 2 ≤
        4 * intrinsicStaticMinusEvenLower c0 c2 *
          intrinsicStaticMinusOddLower c1 c3 := by
  rcases hJ with ⟨hs1L, hs1U, hd1L, hd1U, hs3L, hs3U, hd3L, hd3U⟩
  have h := rational_bilinear_cauchy_of_sum_difference_bounds
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating03
    factorTwoIntrinsicAlternating21 factorTwoIntrinsicAlternating23
    ⟨hs1L, hs1U⟩ ⟨hd1L, hd1U⟩ ⟨hs3L, hs3U⟩ ⟨hd3L, hd3U⟩
  intro c0 c2 c1 c3
  have hc := h c0 c2 c1 c3
  simpa only [factorTwoIntrinsicStaticAlternating,
    factorTwoIntrinsicAlternatingRow0,
    factorTwoIntrinsicAlternatingRow2] using hc

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
