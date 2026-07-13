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

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeGram
