import ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhReciprocalMoments
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeCoefficients

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeGram

open YoshidaEndpointEvenAtanhReciprocalMajorant
open YoshidaEndpointEvenAtanhReciprocalMoments
open YoshidaEndpointEvenProjectedRemainderEnvelopeCoefficients
open YoshidaEndpointEvenProjectedRemainderEnvelopePolynomials

noncomputable section

/-- Closed form of the even moments of the reciprocal tail majorant. -/
def reciprocalMajorantEvenMoment (n : ℕ) : ℝ :=
  2 * ((60 / 41 : ℝ) / (2 * (n : ℝ) + 1) -
    (1800 / 1681 : ℝ) / (2 * (n : ℝ) + 3) +
    (17100 / 68921 : ℝ) / (2 * (n : ℝ) + 5) -
    (18 / 125 : ℝ) / (2 * (n : ℝ) + 7))

private theorem integral_evenPolynomial_mul_reciprocalMajorant
    (N : ℕ) (c : ℕ → ℝ) :
    (∫ x : ℝ in -1..1,
      (∑ n ∈ Finset.range N, c n * x ^ (2 * n)) *
        atanhTailWeightReciprocalMajorant x) =
      ∑ n ∈ Finset.range N, c n * reciprocalMajorantEvenMoment n := by
  rw [show (fun x : ℝ ↦
      (∑ n ∈ Finset.range N, c n * x ^ (2 * n)) *
        atanhTailWeightReciprocalMajorant x) =
      fun x ↦ ∑ n ∈ Finset.range N,
        c n * (x ^ (2 * n) * atanhTailWeightReciprocalMajorant x) by
    funext x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _hn
    ring]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n _hn
    rw [intervalIntegral.integral_const_mul,
      integral_pow_mul_atanhTailWeightReciprocalMajorant]
    rfl
  · intro n _hn
    apply Continuous.intervalIntegrable
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial
    fun_prop

private abbrev q00 : ℝ := -123253709 / 200000000
private abbrev q01 : ℝ := -213563519 / 200000000
private abbrev q02 : ℝ := 3507 / 200000000
private abbrev q03 : ℝ := 91 / 200000000

private abbrev q20 : ℝ := 89916223 / 200000000
private abbrev q21 : ℝ := -355248257 / 200000000
private abbrev q22 : ℝ := 125743 / 200000000
private abbrev q23 : ℝ := -89 / 200000000
private abbrev q24 : ℝ := 1 / 200000000

/-- Rational center of the constant polynomial envelope coefficient box. -/
def centeredEnvelopePolynomial0 (x : ℝ) : ℝ :=
  q00 + q01 * x ^ 2 + q02 * x ^ 4 + q03 * x ^ 6

/-- Rational center of the degree-two polynomial envelope coefficient box. -/
def centeredEnvelopePolynomial2 (x : ℝ) : ℝ :=
  q20 + q21 * x ^ 2 + q22 * x ^ 4 + q23 * x ^ 6 + q24 * x ^ 8

private def centeredEnvelopeGram00Coeff : ℕ → ℝ
  | 0 => q00 ^ 2
  | 1 => 2 * q00 * q01
  | 2 => q01 ^ 2 + 2 * q00 * q02
  | 3 => 2 * q00 * q03 + 2 * q01 * q02
  | 4 => q02 ^ 2 + 2 * q01 * q03
  | 5 => 2 * q02 * q03
  | 6 => q03 ^ 2
  | _ => 0

private def centeredEnvelopeGram02Coeff : ℕ → ℝ
  | 0 => q00 * q20
  | 1 => q00 * q21 + q01 * q20
  | 2 => q00 * q22 + q01 * q21 + q02 * q20
  | 3 => q00 * q23 + q01 * q22 + q02 * q21 + q03 * q20
  | 4 => q00 * q24 + q01 * q23 + q02 * q22 + q03 * q21
  | 5 => q01 * q24 + q02 * q23 + q03 * q22
  | 6 => q02 * q24 + q03 * q23
  | 7 => q03 * q24
  | _ => 0

private def centeredEnvelopeGram22Coeff : ℕ → ℝ
  | 0 => q20 ^ 2
  | 1 => 2 * q20 * q21
  | 2 => q21 ^ 2 + 2 * q20 * q22
  | 3 => 2 * q20 * q23 + 2 * q21 * q22
  | 4 => q22 ^ 2 + 2 * q20 * q24 + 2 * q21 * q23
  | 5 => 2 * q21 * q24 + 2 * q22 * q23
  | 6 => q23 ^ 2 + 2 * q22 * q24
  | 7 => 2 * q23 * q24
  | 8 => q24 ^ 2
  | _ => 0

private theorem centeredEnvelopePolynomial0_sq_eq (x : ℝ) :
    centeredEnvelopePolynomial0 x ^ 2 =
      ∑ n ∈ Finset.range 7, centeredEnvelopeGram00Coeff n * x ^ (2 * n) := by
  simp [centeredEnvelopePolynomial0, centeredEnvelopeGram00Coeff,
    Finset.sum_range_succ]
  ring

private theorem centeredEnvelopePolynomial0_mul_2_eq (x : ℝ) :
    centeredEnvelopePolynomial0 x * centeredEnvelopePolynomial2 x =
      ∑ n ∈ Finset.range 8, centeredEnvelopeGram02Coeff n * x ^ (2 * n) := by
  simp [centeredEnvelopePolynomial0, centeredEnvelopePolynomial2,
    centeredEnvelopeGram02Coeff, Finset.sum_range_succ]
  ring

private theorem centeredEnvelopePolynomial2_sq_eq (x : ℝ) :
    centeredEnvelopePolynomial2 x ^ 2 =
      ∑ n ∈ Finset.range 9, centeredEnvelopeGram22Coeff n * x ^ (2 * n) := by
  simp [centeredEnvelopePolynomial2, centeredEnvelopeGram22Coeff,
    Finset.sum_range_succ]
  ring

/-- Exact rational arithmetic encloses the Gram entry of the centered
constant envelope polynomial. -/
theorem centeredEnvelopeGram00_bounds :
    (19856211 / 10000000 : ℝ) <
        (∫ x : ℝ in -1..1, atanhTailWeightReciprocalMajorant x *
          centeredEnvelopePolynomial0 x ^ 2) ∧
      (∫ x : ℝ in -1..1, atanhTailWeightReciprocalMajorant x *
          centeredEnvelopePolynomial0 x ^ 2) <
        (19856214 / 10000000 : ℝ) := by
  rw [show (fun x : ℝ ↦ atanhTailWeightReciprocalMajorant x *
      centeredEnvelopePolynomial0 x ^ 2) =
      fun x ↦ (∑ n ∈ Finset.range 7,
        centeredEnvelopeGram00Coeff n * x ^ (2 * n)) *
          atanhTailWeightReciprocalMajorant x by
    funext x
    rw [← centeredEnvelopePolynomial0_sq_eq]
    ring,
    integral_evenPolynomial_mul_reciprocalMajorant]
  constructor <;>
    norm_num [centeredEnvelopeGram00Coeff, reciprocalMajorantEvenMoment,
      Finset.sum_range_succ]

/-- Exact rational arithmetic encloses the centered mixed Gram entry. -/
theorem centeredEnvelopeGram02_bounds :
    (3156654 / 10000000 : ℝ) <
        (∫ x : ℝ in -1..1, atanhTailWeightReciprocalMajorant x *
          centeredEnvelopePolynomial0 x * centeredEnvelopePolynomial2 x) ∧
      (∫ x : ℝ in -1..1, atanhTailWeightReciprocalMajorant x *
          centeredEnvelopePolynomial0 x * centeredEnvelopePolynomial2 x) <
        (3156657 / 10000000 : ℝ) := by
  rw [show (fun x : ℝ ↦ atanhTailWeightReciprocalMajorant x *
      centeredEnvelopePolynomial0 x * centeredEnvelopePolynomial2 x) =
      fun x ↦ (∑ n ∈ Finset.range 8,
        centeredEnvelopeGram02Coeff n * x ^ (2 * n)) *
          atanhTailWeightReciprocalMajorant x by
    funext x
    rw [← centeredEnvelopePolynomial0_mul_2_eq]
    ring,
    integral_evenPolynomial_mul_reciprocalMajorant]
  constructor <;>
    norm_num [centeredEnvelopeGram02Coeff, reciprocalMajorantEvenMoment,
      Finset.sum_range_succ]

/-- Exact rational arithmetic encloses the Gram entry of the centered
degree-two envelope polynomial. -/
theorem centeredEnvelopeGram22_bounds :
    (4954952 / 10000000 : ℝ) <
        (∫ x : ℝ in -1..1, atanhTailWeightReciprocalMajorant x *
          centeredEnvelopePolynomial2 x ^ 2) ∧
      (∫ x : ℝ in -1..1, atanhTailWeightReciprocalMajorant x *
          centeredEnvelopePolynomial2 x ^ 2) <
        (4954956 / 10000000 : ℝ) := by
  rw [show (fun x : ℝ ↦ atanhTailWeightReciprocalMajorant x *
      centeredEnvelopePolynomial2 x ^ 2) =
      fun x ↦ (∑ n ∈ Finset.range 9,
        centeredEnvelopeGram22Coeff n * x ^ (2 * n)) *
          atanhTailWeightReciprocalMajorant x by
    funext x
    rw [← centeredEnvelopePolynomial2_sq_eq]
    ring,
    integral_evenPolynomial_mul_reciprocalMajorant]
  constructor <;>
    norm_num [centeredEnvelopeGram22Coeff, reciprocalMajorantEvenMoment,
      Finset.sum_range_succ]

private theorem abs_add_four_le (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  calc
    |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
    _ ≤ (|a + b| + |c|) + |d| := by gcongr; exact abs_add_le _ _
    _ ≤ (|a| + |b| + |c|) + |d| := by gcongr; exact abs_add_le _ _
    _ = _ := by ring

private theorem abs_add_five_le (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  calc
    |a + b + c + d + e| ≤ |a + b + c + d| + |e| := abs_add_le _ _
    _ ≤ (|a| + |b| + |c| + |d|) + |e| := by
      gcongr
      exact abs_add_four_le _ _ _ _
    _ = _ := by ring

private theorem coefficient_center_errors :
    |projectedEnvelopeD00 - q00| < (1 / 200000000 : ℝ) ∧
    |projectedEnvelopeD01 - q01| < (1 / 200000000 : ℝ) ∧
    |projectedEnvelopeD02 - q02| < (1 / 200000000 : ℝ) ∧
    |projectedEnvelopeD03 - q03| < (1 / 200000000 : ℝ) ∧
    |projectedEnvelopeD20 - q20| < (1 / 200000000 : ℝ) ∧
    |projectedEnvelopeD21 - q21| < (1 / 200000000 : ℝ) ∧
    |projectedEnvelopeD22 - q22| < (1 / 200000000 : ℝ) ∧
    |projectedEnvelopeD23 - q23| < (1 / 200000000 : ℝ) ∧
    |projectedEnvelopeD24 - q24| < (1 / 200000000 : ℝ) := by
  have h00 := projectedEnvelopeD00_bounds
  have h01 := projectedEnvelopeD01_bounds
  have h02 := projectedEnvelopeD02_bounds
  have h03 := projectedEnvelopeD03_bounds
  have h20 := projectedEnvelopeD20_bounds
  have h21 := projectedEnvelopeD21_bounds
  have h22 := projectedEnvelopeD22_bounds
  have h23 := projectedEnvelopeD23_bounds
  have h24 := projectedEnvelopeD24_bounds
  rw [abs_lt, abs_lt, abs_lt, abs_lt, abs_lt, abs_lt, abs_lt, abs_lt,
    abs_lt]
  norm_num at h00 h01 h02 h03 h20 h21 h22 h23 h24 ⊢
  rcases h00 with ⟨h00l, h00u⟩
  rcases h01 with ⟨h01l, h01u⟩
  rcases h02 with ⟨h02l, h02u⟩
  rcases h03 with ⟨h03l, h03u⟩
  rcases h20 with ⟨h20l, h20u⟩
  rcases h21 with ⟨h21l, h21u⟩
  rcases h22 with ⟨h22l, h22u⟩
  rcases h23 with ⟨h23l, h23u⟩
  rcases h24 with ⟨h24l, h24u⟩
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

private theorem abs_pow_le_one_of_mem_Icc
    {x : ℝ} (hx : x ∈ Icc (-1) 1) (n : ℕ) :
    |x ^ n| ≤ 1 := by
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg x) (abs_le.mpr hx)

/-- The exact constant-envelope polynomial lies within the sum of its four
coefficient half-widths from the rational center. -/
theorem abs_shiftedPolynomial0_sub_center_lt
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |shiftedRemainderPolynomial6_0_explicit x - centeredEnvelopePolynomial0 x| <
      (1 / 50000000 : ℝ) := by
  rcases coefficient_center_errors with
    ⟨h00, h01, h02, h03, _h20, _h21, _h22, _h23, _h24⟩
  have hterm (d q : ℝ) (n : ℕ)
      (hd : |d - q| < (1 / 200000000 : ℝ)) :
      |(d - q) * x ^ n| < (1 / 200000000 : ℝ) := by
    rw [abs_mul]
    calc
      |d - q| * |x ^ n| ≤ |d - q| * 1 := by
        gcongr
        exact abs_pow_le_one_of_mem_Icc hx n
      _ < (1 / 200000000 : ℝ) := by simpa using hd
  rw [show shiftedRemainderPolynomial6_0_explicit x -
      centeredEnvelopePolynomial0 x =
      (projectedEnvelopeD00 - q00) +
        (projectedEnvelopeD01 - q01) * x ^ 2 +
        (projectedEnvelopeD02 - q02) * x ^ 4 +
        (projectedEnvelopeD03 - q03) * x ^ 6 by
    unfold shiftedRemainderPolynomial6_0_explicit centeredEnvelopePolynomial0
    ring]
  exact (abs_add_four_le _ _ _ _).trans_lt (by
    have ht00 := hterm projectedEnvelopeD00 q00 0 h00
    have ht01 := hterm projectedEnvelopeD01 q01 2 h01
    have ht02 := hterm projectedEnvelopeD02 q02 4 h02
    have ht03 := hterm projectedEnvelopeD03 q03 6 h03
    linarith [ht00, ht01, ht02, ht03])

/-- The degree-two envelope polynomial lies within the sum of its five
coefficient half-widths from the rational center. -/
theorem abs_shiftedPolynomial2_sub_center_lt
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |shiftedRemainderPolynomial6_2_explicit x - centeredEnvelopePolynomial2 x| <
      (1 / 40000000 : ℝ) := by
  rcases coefficient_center_errors with
    ⟨_h00, _h01, _h02, _h03, h20, h21, h22, h23, h24⟩
  have hterm (d q : ℝ) (n : ℕ)
      (hd : |d - q| < (1 / 200000000 : ℝ)) :
      |(d - q) * x ^ n| < (1 / 200000000 : ℝ) := by
    rw [abs_mul]
    calc
      |d - q| * |x ^ n| ≤ |d - q| * 1 := by
        gcongr
        exact abs_pow_le_one_of_mem_Icc hx n
      _ < (1 / 200000000 : ℝ) := by simpa using hd
  rw [show shiftedRemainderPolynomial6_2_explicit x -
      centeredEnvelopePolynomial2 x =
      (projectedEnvelopeD20 - q20) +
        (projectedEnvelopeD21 - q21) * x ^ 2 +
        (projectedEnvelopeD22 - q22) * x ^ 4 +
        (projectedEnvelopeD23 - q23) * x ^ 6 +
        (projectedEnvelopeD24 - q24) * x ^ 8 by
    unfold shiftedRemainderPolynomial6_2_explicit centeredEnvelopePolynomial2
    ring]
  exact (abs_add_five_le _ _ _ _ _).trans_lt (by
    have ht20 := hterm projectedEnvelopeD20 q20 0 h20
    have ht21 := hterm projectedEnvelopeD21 q21 2 h21
    have ht22 := hterm projectedEnvelopeD22 q22 4 h22
    have ht23 := hterm projectedEnvelopeD23 q23 6 h23
    have ht24 := hterm projectedEnvelopeD24 q24 8 h24
    linarith [ht20, ht21, ht22, ht23, ht24])

private theorem abs_centeredEnvelopePolynomial0_lt
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |centeredEnvelopePolynomial0 x| < (4211 / 2500 : ℝ) := by
  unfold centeredEnvelopePolynomial0
  have h2 := abs_pow_le_one_of_mem_Icc hx 2
  have h4 := abs_pow_le_one_of_mem_Icc hx 4
  have h6 := abs_pow_le_one_of_mem_Icc hx 6
  calc
    |q00 + q01 * x ^ 2 + q02 * x ^ 4 + q03 * x ^ 6| ≤
        |q00| + |q01 * x ^ 2| + |q02 * x ^ 4| + |q03 * x ^ 6| :=
      abs_add_four_le _ _ _ _
    _ ≤ |q00| + |q01| * 1 + |q02| * 1 + |q03| * 1 := by
      simp only [abs_mul]
      gcongr
    _ < (4211 / 2500 : ℝ) := by norm_num

private theorem abs_centeredEnvelopePolynomial2_lt
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |centeredEnvelopePolynomial2 x| < (2227 / 1000 : ℝ) := by
  unfold centeredEnvelopePolynomial2
  have h2 := abs_pow_le_one_of_mem_Icc hx 2
  have h4 := abs_pow_le_one_of_mem_Icc hx 4
  have h6 := abs_pow_le_one_of_mem_Icc hx 6
  have h8 := abs_pow_le_one_of_mem_Icc hx 8
  calc
    |q20 + q21 * x ^ 2 + q22 * x ^ 4 + q23 * x ^ 6 + q24 * x ^ 8| ≤
        |q20| + |q21 * x ^ 2| + |q22 * x ^ 4| + |q23 * x ^ 6| +
          |q24 * x ^ 8| := abs_add_five_le _ _ _ _ _
    _ ≤ |q20| + |q21| * 1 + |q22| * 1 + |q23| * 1 + |q24| * 1 := by
      simp only [abs_mul]
      gcongr
    _ < (2227 / 1000 : ℝ) := by norm_num

/-- Uniform bound for the exact constant-envelope polynomial. -/
theorem abs_shiftedRemainderPolynomial6_0_explicit_lt
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |shiftedRemainderPolynomial6_0_explicit x| < (337 / 200 : ℝ) := by
  have hdiff := abs_shiftedPolynomial0_sub_center_lt hx
  have hcenter := abs_centeredEnvelopePolynomial0_lt hx
  calc
    |shiftedRemainderPolynomial6_0_explicit x| =
        |(shiftedRemainderPolynomial6_0_explicit x -
            centeredEnvelopePolynomial0 x) + centeredEnvelopePolynomial0 x| := by
      congr 1
      ring
    _ ≤ |shiftedRemainderPolynomial6_0_explicit x -
          centeredEnvelopePolynomial0 x| + |centeredEnvelopePolynomial0 x| :=
      abs_add_le _ _
    _ < (337 / 200 : ℝ) := by
      norm_num at hdiff hcenter ⊢
      linarith

/-- Uniform bound for the exact degree-two envelope polynomial. -/
theorem abs_shiftedRemainderPolynomial6_2_explicit_lt
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |shiftedRemainderPolynomial6_2_explicit x| < (223 / 100 : ℝ) := by
  have hdiff := abs_shiftedPolynomial2_sub_center_lt hx
  have hcenter := abs_centeredEnvelopePolynomial2_lt hx
  calc
    |shiftedRemainderPolynomial6_2_explicit x| =
        |(shiftedRemainderPolynomial6_2_explicit x -
            centeredEnvelopePolynomial2 x) + centeredEnvelopePolynomial2 x| := by
      congr 1
      ring
    _ ≤ |shiftedRemainderPolynomial6_2_explicit x -
          centeredEnvelopePolynomial2 x| + |centeredEnvelopePolynomial2 x| :=
      abs_add_le _ _
    _ < (223 / 100 : ℝ) := by
      norm_num at hdiff hcenter ⊢
      linarith

/-- The cubic reciprocal majorant stays below `3/2` on the endpoint
interval. -/
theorem reciprocalMajorant_le_three_halves
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    atanhTailWeightReciprocalMajorant x ≤ (3 / 2 : ℝ) := by
  have hxSq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 (abs_le.mpr hx)
  have hxSq0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hone : 0 ≤ 1 - x ^ 2 := by linarith
  have h0term :
      (60 / 41 : ℝ) * (1 - x ^ 2) ^ 3 ≤
        (3 / 2 : ℝ) * (1 - x ^ 2) ^ 3 :=
    mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hone 3)
  have h1term :
      (5580 / 1681 : ℝ) * x ^ 2 * (1 - x ^ 2) ^ 2 ≤
        (9 / 2 : ℝ) * x ^ 2 * (1 - x ^ 2) ^ 2 := by
    have hbase : 0 ≤ x ^ 2 * (1 - x ^ 2) ^ 2 :=
      mul_nonneg hxSq0 (pow_nonneg hone 2)
    nlinarith [mul_le_mul_of_nonneg_right
      (show (5580 / 1681 : ℝ) ≤ 9 / 2 by norm_num) hbase]
  have h2term :
      (172080 / 68921 : ℝ) * (x ^ 2) ^ 2 * (1 - x ^ 2) ≤
        (9 / 2 : ℝ) * (x ^ 2) ^ 2 * (1 - x ^ 2) := by
    have hbase : 0 ≤ (x ^ 2) ^ 2 * (1 - x ^ 2) :=
      mul_nonneg (sq_nonneg _) hone
    nlinarith [mul_le_mul_of_nonneg_right
      (show (172080 / 68921 : ℝ) ≤ 9 / 2 by norm_num) hbase]
  have h3term :
      (4279422 / 8615125 : ℝ) * (x ^ 2) ^ 3 ≤
        (3 / 2 : ℝ) * (x ^ 2) ^ 3 :=
    mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hxSq0 3)
  unfold atanhTailWeightReciprocalMajorant
  rw [atanhTailWeightReciprocalMajorantPolynomial_eq_bernstein]
  calc
    (60 / 41 : ℝ) * (1 - x ^ 2) ^ 3 +
          (5580 / 1681 : ℝ) * x ^ 2 * (1 - x ^ 2) ^ 2 +
          (172080 / 68921 : ℝ) * (x ^ 2) ^ 2 * (1 - x ^ 2) +
          (4279422 / 8615125 : ℝ) * (x ^ 2) ^ 3 ≤
        (3 / 2 : ℝ) * (1 - x ^ 2) ^ 3 +
          (9 / 2 : ℝ) * x ^ 2 * (1 - x ^ 2) ^ 2 +
          (9 / 2 : ℝ) * (x ^ 2) ^ 2 * (1 - x ^ 2) +
          (3 / 2 : ℝ) * (x ^ 2) ^ 3 := by
      linarith
    _ = (3 / 2 : ℝ) := by ring

/-- Gram entry of the exact polynomial constant envelope. -/
def fixedProjectedEnvelopePolynomialGram00 : ℝ :=
  ∫ x : ℝ in -1..1, atanhTailWeightReciprocalMajorant x *
    shiftedRemainderPolynomial6_0_explicit x ^ 2

/-- Mixed Gram entry of the two exact polynomial envelopes. -/
def fixedProjectedEnvelopePolynomialGram02 : ℝ :=
  ∫ x : ℝ in -1..1, atanhTailWeightReciprocalMajorant x *
    shiftedRemainderPolynomial6_0_explicit x *
      shiftedRemainderPolynomial6_2_explicit x

/-- Gram entry of the exact polynomial degree-two envelope. -/
def fixedProjectedEnvelopePolynomialGram22 : ℝ :=
  ∫ x : ℝ in -1..1, atanhTailWeightReciprocalMajorant x *
    shiftedRemainderPolynomial6_2_explicit x ^ 2

private theorem abs_polynomialGram00_sub_center_lt :
    |fixedProjectedEnvelopePolynomialGram00 -
        (∫ x : ℝ in -1..1, atanhTailWeightReciprocalMajorant x *
          centeredEnvelopePolynomial0 x ^ 2)| <
      (21 / 100000000 : ℝ) := by
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦ atanhTailWeightReciprocalMajorant x *
        shiftedRemainderPolynomial6_0_explicit x ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial
      shiftedRemainderPolynomial6_0_explicit
    fun_prop
  have hcenter : IntervalIntegrable
      (fun x : ℝ ↦ atanhTailWeightReciprocalMajorant x *
        centeredEnvelopePolynomial0 x ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial centeredEnvelopePolynomial0
    fun_prop
  unfold fixedProjectedEnvelopePolynomialGram00
  rw [← intervalIntegral.integral_sub hpoly hcenter, ← Real.norm_eq_abs]
  calc
    ‖∫ x : ℝ in -1..1,
        atanhTailWeightReciprocalMajorant x *
            shiftedRemainderPolynomial6_0_explicit x ^ 2 -
          atanhTailWeightReciprocalMajorant x *
            centeredEnvelopePolynomial0 x ^ 2‖ ≤
        (102 / 1000000000 : ℝ) * |(1 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hU0 := atanhTailWeightReciprocalMajorant_nonneg_on_Icc hxIcc
      have hU := reciprocalMajorant_le_three_halves hxIcc
      have hd := abs_shiftedPolynomial0_sub_center_lt hxIcc
      have hD := abs_shiftedRemainderPolynomial6_0_explicit_lt hxIcc
      have hQ := abs_centeredEnvelopePolynomial0_lt hxIcc
      have hsum :
          |shiftedRemainderPolynomial6_0_explicit x +
              centeredEnvelopePolynomial0 x| <
            (337 / 200 : ℝ) + 4211 / 2500 :=
        (abs_add_le _ _).trans_lt (add_lt_add hD hQ)
      have hsq :
          |shiftedRemainderPolynomial6_0_explicit x ^ 2 -
              centeredEnvelopePolynomial0 x ^ 2| <
            (1 / 50000000 : ℝ) * ((337 / 200 : ℝ) + 4211 / 2500) := by
        rw [sq_sub_sq, abs_mul]
        calc
          |shiftedRemainderPolynomial6_0_explicit x +
                centeredEnvelopePolynomial0 x| *
              |shiftedRemainderPolynomial6_0_explicit x -
                centeredEnvelopePolynomial0 x| ≤
              ((337 / 200 : ℝ) + 4211 / 2500) *
                |shiftedRemainderPolynomial6_0_explicit x -
                  centeredEnvelopePolynomial0 x| :=
            mul_le_mul_of_nonneg_right hsum.le (abs_nonneg _)
          _ < ((337 / 200 : ℝ) + 4211 / 2500) *
              (1 / 50000000 : ℝ) :=
            mul_lt_mul_of_pos_left hd (by norm_num)
          _ = (1 / 50000000 : ℝ) *
              ((337 / 200 : ℝ) + 4211 / 2500) := by ring
      rw [show
          atanhTailWeightReciprocalMajorant x *
                shiftedRemainderPolynomial6_0_explicit x ^ 2 -
              atanhTailWeightReciprocalMajorant x *
                centeredEnvelopePolynomial0 x ^ 2 =
            atanhTailWeightReciprocalMajorant x *
              (shiftedRemainderPolynomial6_0_explicit x ^ 2 -
                centeredEnvelopePolynomial0 x ^ 2) by ring,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg hU0]
      calc
        atanhTailWeightReciprocalMajorant x *
            |shiftedRemainderPolynomial6_0_explicit x ^ 2 -
              centeredEnvelopePolynomial0 x ^ 2| ≤
            (3 / 2 : ℝ) *
              |shiftedRemainderPolynomial6_0_explicit x ^ 2 -
                centeredEnvelopePolynomial0 x ^ 2| := by gcongr
        _ ≤ (3 / 2 : ℝ) *
            ((1 / 50000000 : ℝ) * ((337 / 200 : ℝ) + 4211 / 2500)) := by
          gcongr
        _ ≤ (102 / 1000000000 : ℝ) := by norm_num
    _ < (21 / 100000000 : ℝ) := by norm_num

private theorem abs_polynomialGram02_sub_center_lt :
    |fixedProjectedEnvelopePolynomialGram02 -
        (∫ x : ℝ in -1..1, atanhTailWeightReciprocalMajorant x *
          centeredEnvelopePolynomial0 x * centeredEnvelopePolynomial2 x)| <
      (27 / 100000000 : ℝ) := by
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦ atanhTailWeightReciprocalMajorant x *
        shiftedRemainderPolynomial6_0_explicit x *
          shiftedRemainderPolynomial6_2_explicit x) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial
      shiftedRemainderPolynomial6_0_explicit
      shiftedRemainderPolynomial6_2_explicit
    fun_prop
  have hcenter : IntervalIntegrable
      (fun x : ℝ ↦ atanhTailWeightReciprocalMajorant x *
        centeredEnvelopePolynomial0 x * centeredEnvelopePolynomial2 x)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial centeredEnvelopePolynomial0
      centeredEnvelopePolynomial2
    fun_prop
  unfold fixedProjectedEnvelopePolynomialGram02
  rw [← intervalIntegral.integral_sub hpoly hcenter, ← Real.norm_eq_abs]
  calc
    ‖∫ x : ℝ in -1..1,
        atanhTailWeightReciprocalMajorant x *
              shiftedRemainderPolynomial6_0_explicit x *
            shiftedRemainderPolynomial6_2_explicit x -
          atanhTailWeightReciprocalMajorant x * centeredEnvelopePolynomial0 x *
            centeredEnvelopePolynomial2 x‖ ≤
        (131 / 1000000000 : ℝ) * |(1 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hU0 := atanhTailWeightReciprocalMajorant_nonneg_on_Icc hxIcc
      have hU := reciprocalMajorant_le_three_halves hxIcc
      have hd0 := abs_shiftedPolynomial0_sub_center_lt hxIcc
      have hd2 := abs_shiftedPolynomial2_sub_center_lt hxIcc
      have hD2 := abs_shiftedRemainderPolynomial6_2_explicit_lt hxIcc
      have hQ0 := abs_centeredEnvelopePolynomial0_lt hxIcc
      have hfirst :
          |(shiftedRemainderPolynomial6_0_explicit x -
              centeredEnvelopePolynomial0 x) *
              shiftedRemainderPolynomial6_2_explicit x| <
            (1 / 50000000 : ℝ) * (223 / 100) := by
        rw [abs_mul]
        calc
          |shiftedRemainderPolynomial6_0_explicit x -
                centeredEnvelopePolynomial0 x| *
              |shiftedRemainderPolynomial6_2_explicit x| ≤
              |shiftedRemainderPolynomial6_0_explicit x -
                centeredEnvelopePolynomial0 x| * (223 / 100 : ℝ) :=
            mul_le_mul_of_nonneg_left hD2.le (abs_nonneg _)
          _ < (1 / 50000000 : ℝ) * (223 / 100) :=
            mul_lt_mul_of_pos_right hd0 (by norm_num)
      have hsecond :
          |centeredEnvelopePolynomial0 x *
              (shiftedRemainderPolynomial6_2_explicit x -
                centeredEnvelopePolynomial2 x)| <
            (4211 / 2500 : ℝ) * (1 / 40000000) := by
        rw [abs_mul]
        calc
          |centeredEnvelopePolynomial0 x| *
              |shiftedRemainderPolynomial6_2_explicit x -
                centeredEnvelopePolynomial2 x| ≤
              (4211 / 2500 : ℝ) *
                |shiftedRemainderPolynomial6_2_explicit x -
                  centeredEnvelopePolynomial2 x| :=
            mul_le_mul_of_nonneg_right hQ0.le (abs_nonneg _)
          _ < (4211 / 2500 : ℝ) * (1 / 40000000) :=
            mul_lt_mul_of_pos_left hd2 (by norm_num)
      have hprod :
          |shiftedRemainderPolynomial6_0_explicit x *
                shiftedRemainderPolynomial6_2_explicit x -
              centeredEnvelopePolynomial0 x * centeredEnvelopePolynomial2 x| <
            (1 / 50000000 : ℝ) * (223 / 100) +
              (4211 / 2500 : ℝ) * (1 / 40000000) := by
        rw [show shiftedRemainderPolynomial6_0_explicit x *
                shiftedRemainderPolynomial6_2_explicit x -
              centeredEnvelopePolynomial0 x * centeredEnvelopePolynomial2 x =
            (shiftedRemainderPolynomial6_0_explicit x -
                centeredEnvelopePolynomial0 x) *
                shiftedRemainderPolynomial6_2_explicit x +
              centeredEnvelopePolynomial0 x *
                (shiftedRemainderPolynomial6_2_explicit x -
                  centeredEnvelopePolynomial2 x) by ring]
        exact (abs_add_le _ _).trans_lt (add_lt_add hfirst hsecond)
      rw [show
          atanhTailWeightReciprocalMajorant x *
                  shiftedRemainderPolynomial6_0_explicit x *
                shiftedRemainderPolynomial6_2_explicit x -
              atanhTailWeightReciprocalMajorant x * centeredEnvelopePolynomial0 x *
                centeredEnvelopePolynomial2 x =
            atanhTailWeightReciprocalMajorant x *
              (shiftedRemainderPolynomial6_0_explicit x *
                  shiftedRemainderPolynomial6_2_explicit x -
                centeredEnvelopePolynomial0 x * centeredEnvelopePolynomial2 x) by ring,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg hU0]
      calc
        atanhTailWeightReciprocalMajorant x *
            |shiftedRemainderPolynomial6_0_explicit x *
                  shiftedRemainderPolynomial6_2_explicit x -
                centeredEnvelopePolynomial0 x * centeredEnvelopePolynomial2 x| ≤
            (3 / 2 : ℝ) *
              |shiftedRemainderPolynomial6_0_explicit x *
                  shiftedRemainderPolynomial6_2_explicit x -
                centeredEnvelopePolynomial0 x * centeredEnvelopePolynomial2 x| := by
          gcongr
        _ ≤ (3 / 2 : ℝ) *
            ((1 / 50000000 : ℝ) * (223 / 100) +
              (4211 / 2500 : ℝ) * (1 / 40000000)) := by gcongr
        _ ≤ (131 / 1000000000 : ℝ) := by norm_num
    _ < (27 / 100000000 : ℝ) := by norm_num

private theorem abs_polynomialGram22_sub_center_lt :
    |fixedProjectedEnvelopePolynomialGram22 -
        (∫ x : ℝ in -1..1, atanhTailWeightReciprocalMajorant x *
          centeredEnvelopePolynomial2 x ^ 2)| <
      (34 / 100000000 : ℝ) := by
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦ atanhTailWeightReciprocalMajorant x *
        shiftedRemainderPolynomial6_2_explicit x ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial
      shiftedRemainderPolynomial6_2_explicit
    fun_prop
  have hcenter : IntervalIntegrable
      (fun x : ℝ ↦ atanhTailWeightReciprocalMajorant x *
        centeredEnvelopePolynomial2 x ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial centeredEnvelopePolynomial2
    fun_prop
  unfold fixedProjectedEnvelopePolynomialGram22
  rw [← intervalIntegral.integral_sub hpoly hcenter, ← Real.norm_eq_abs]
  calc
    ‖∫ x : ℝ in -1..1,
        atanhTailWeightReciprocalMajorant x *
            shiftedRemainderPolynomial6_2_explicit x ^ 2 -
          atanhTailWeightReciprocalMajorant x *
            centeredEnvelopePolynomial2 x ^ 2‖ ≤
        (168 / 1000000000 : ℝ) * |(1 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hU0 := atanhTailWeightReciprocalMajorant_nonneg_on_Icc hxIcc
      have hU := reciprocalMajorant_le_three_halves hxIcc
      have hd := abs_shiftedPolynomial2_sub_center_lt hxIcc
      have hD := abs_shiftedRemainderPolynomial6_2_explicit_lt hxIcc
      have hQ := abs_centeredEnvelopePolynomial2_lt hxIcc
      have hsum :
          |shiftedRemainderPolynomial6_2_explicit x +
              centeredEnvelopePolynomial2 x| <
            (223 / 100 : ℝ) + 2227 / 1000 :=
        (abs_add_le _ _).trans_lt (add_lt_add hD hQ)
      have hsq :
          |shiftedRemainderPolynomial6_2_explicit x ^ 2 -
              centeredEnvelopePolynomial2 x ^ 2| <
            (1 / 40000000 : ℝ) * ((223 / 100 : ℝ) + 2227 / 1000) := by
        rw [sq_sub_sq, abs_mul]
        calc
          |shiftedRemainderPolynomial6_2_explicit x +
                centeredEnvelopePolynomial2 x| *
              |shiftedRemainderPolynomial6_2_explicit x -
                centeredEnvelopePolynomial2 x| ≤
              ((223 / 100 : ℝ) + 2227 / 1000) *
                |shiftedRemainderPolynomial6_2_explicit x -
                  centeredEnvelopePolynomial2 x| :=
            mul_le_mul_of_nonneg_right hsum.le (abs_nonneg _)
          _ < ((223 / 100 : ℝ) + 2227 / 1000) *
              (1 / 40000000 : ℝ) :=
            mul_lt_mul_of_pos_left hd (by norm_num)
          _ = (1 / 40000000 : ℝ) *
              ((223 / 100 : ℝ) + 2227 / 1000) := by ring
      rw [show
          atanhTailWeightReciprocalMajorant x *
                shiftedRemainderPolynomial6_2_explicit x ^ 2 -
              atanhTailWeightReciprocalMajorant x *
                centeredEnvelopePolynomial2 x ^ 2 =
            atanhTailWeightReciprocalMajorant x *
              (shiftedRemainderPolynomial6_2_explicit x ^ 2 -
                centeredEnvelopePolynomial2 x ^ 2) by ring,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg hU0]
      calc
        atanhTailWeightReciprocalMajorant x *
            |shiftedRemainderPolynomial6_2_explicit x ^ 2 -
              centeredEnvelopePolynomial2 x ^ 2| ≤
            (3 / 2 : ℝ) *
              |shiftedRemainderPolynomial6_2_explicit x ^ 2 -
                centeredEnvelopePolynomial2 x ^ 2| := by gcongr
        _ ≤ (3 / 2 : ℝ) *
            ((1 / 40000000 : ℝ) * ((223 / 100 : ℝ) + 2227 / 1000)) := by
          gcongr
        _ ≤ (168 / 1000000000 : ℝ) := by norm_num
    _ < (34 / 100000000 : ℝ) := by norm_num

/-- Rational enclosure of the exact constant-envelope polynomial Gram. -/
theorem fixedProjectedEnvelopePolynomialGram00_bounds :
    (19856208 / 10000000 : ℝ) < fixedProjectedEnvelopePolynomialGram00 ∧
      fixedProjectedEnvelopePolynomialGram00 < (19856217 / 10000000 : ℝ) := by
  rcases centeredEnvelopeGram00_bounds with ⟨hlo, hup⟩
  rcases abs_lt.mp abs_polynomialGram00_sub_center_lt with ⟨herrl, herru⟩
  constructor <;> norm_num at hlo hup herrl herru ⊢ <;> linarith

/-- Rational enclosure of the exact mixed polynomial Gram. -/
theorem fixedProjectedEnvelopePolynomialGram02_bounds :
    (3156651 / 10000000 : ℝ) < fixedProjectedEnvelopePolynomialGram02 ∧
      fixedProjectedEnvelopePolynomialGram02 < (3156660 / 10000000 : ℝ) := by
  rcases centeredEnvelopeGram02_bounds with ⟨hlo, hup⟩
  rcases abs_lt.mp abs_polynomialGram02_sub_center_lt with ⟨herrl, herru⟩
  constructor <;> norm_num at hlo hup herrl herru ⊢ <;> linarith

/-- Rational enclosure of the exact degree-two polynomial Gram. -/
theorem fixedProjectedEnvelopePolynomialGram22_bounds :
    (4954948 / 10000000 : ℝ) < fixedProjectedEnvelopePolynomialGram22 ∧
      fixedProjectedEnvelopePolynomialGram22 < (4954960 / 10000000 : ℝ) := by
  rcases centeredEnvelopeGram22_bounds with ⟨hlo, hup⟩
  rcases abs_lt.mp abs_polynomialGram22_sub_center_lt with ⟨herrl, herru⟩
  constructor <;> norm_num at hlo hup herrl herru ⊢ <;> linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeGram
