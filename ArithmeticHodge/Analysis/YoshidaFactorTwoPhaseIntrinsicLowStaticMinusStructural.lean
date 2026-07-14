import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive

/-!
# Structural closure interface for the intrinsic negative static split

The alternating block is expressed in the sum/difference basis of the even
plane.  This is the basis in which the weak even direction and the small
cross-difference correlations remain visible.  All statements below are
exact finite-dimensional identities; there is no phase enumeration or
sampled certificate.
-/

/-- The adjugate quadratic in the even sum/difference basis. -/
theorem adjugateQuadratic_eq_sum_difference
    (q00 q02 q22 j0 j2 : ℝ) :
    q22 * j0 ^ 2 - 2 * q02 * j0 * j2 + q00 * j2 ^ 2 =
      ((q00 + q22 - 2 * q02) * (j0 + j2) ^ 2 +
        (q00 + q22 + 2 * q02) * (j0 - j2) ^ 2 +
        2 * (q22 - q00) * (j0 + j2) * (j0 - j2)) / 4 := by
  ring

/-- Polarized adjugate pairing in the same basis. -/
theorem adjugateBilinear_eq_sum_difference
    (q00 q02 q22 j0 j2 k0 k2 : ℝ) :
    q22 * j0 * k0 - q02 * (j0 * k2 + j2 * k0) + q00 * j2 * k2 =
      ((q00 + q22 - 2 * q02) * (j0 + j2) * (k0 + k2) +
        (q00 + q22 + 2 * q02) * (j0 - j2) * (k0 - k2) +
        (q22 - q00) *
          ((j0 + j2) * (k0 - k2) + (j0 - j2) * (k0 + k2))) / 4 := by
  ring

/-- A lower quadratic on each diagonal channel transports any structural
Cauchy inequality to the exact intrinsic static split. -/
theorem factorTwoIntrinsicStaticMinusCauchy_of_lower_quadratics
    (E O : ℝ → ℝ → ℝ)
    (hE : ∀ c0 c2 : ℝ,
      E c0 c2 ≤ factorTwoIntrinsicStaticEvenQuadratic (-1) c0 c2)
    (hO : ∀ c1 c3 : ℝ,
      O c1 c3 ≤ factorTwoIntrinsicStaticOddQuadratic (-1) c1 c3)
    (hE0 : ∀ c0 c2 : ℝ, 0 ≤ E c0 c2)
    (hO0 : ∀ c1 c3 : ℝ, 0 ≤ O c1 c3)
    (hCauchy : ∀ c0 c2 c1 c3 : ℝ,
      factorTwoIntrinsicStaticAlternating c0 c2 c1 c3 ^ 2 ≤
        4 * E c0 c2 * O c1 c3) :
    FactorTwoIntrinsicStaticCauchy (-1) := by
  intro c0 c2 c1 c3
  have hEmul :
      E c0 c2 * O c1 c3 ≤
        factorTwoIntrinsicStaticEvenQuadratic (-1) c0 c2 * O c1 c3 :=
    mul_le_mul_of_nonneg_right (hE c0 c2) (hO0 c1 c3)
  have hOmul :
      factorTwoIntrinsicStaticEvenQuadratic (-1) c0 c2 * O c1 c3 ≤
        factorTwoIntrinsicStaticEvenQuadratic (-1) c0 c2 *
          factorTwoIntrinsicStaticOddQuadratic (-1) c1 c3 := by
    exact mul_le_mul_of_nonneg_left (hO c1 c3)
      ((hE0 c0 c2).trans (hE c0 c2))
  calc
    factorTwoIntrinsicStaticAlternating c0 c2 c1 c3 ^ 2 ≤
        4 * E c0 c2 * O c1 c3 := hCauchy c0 c2 c1 c3
    _ ≤ 4 *
        factorTwoIntrinsicStaticEvenQuadratic (-1) c0 c2 *
          factorTwoIntrinsicStaticOddQuadratic (-1) c1 c3 := by
      nlinarith

/-- Exact Schur completion for an arbitrary positive definite even lower
form.  This is the algebraic bridge used after the analytic entry bounds are
inserted. -/
theorem bilinear_sq_le_four_mul_of_schur
    (q00 q02 q22 o11 o13 o33 j01 j03 j21 j23 : ℝ)
    (hq00 : 0 < q00)
    (hqdet : 0 < q00 * q22 - q02 ^ 2)
    (hres : ∀ c1 c3 : ℝ,
      0 ≤
        4 * (q00 * q22 - q02 ^ 2) *
            (o11 * c1 ^ 2 + 2 * o13 * c1 * c3 + o33 * c3 ^ 2) -
          (q22 * (j01 * c1 + j03 * c3) ^ 2 -
            2 * q02 * (j01 * c1 + j03 * c3) *
              (j21 * c1 + j23 * c3) +
            q00 * (j21 * c1 + j23 * c3) ^ 2)) :
    ∀ c0 c2 c1 c3 : ℝ,
      (c0 * (j01 * c1 + j03 * c3) +
          c2 * (j21 * c1 + j23 * c3)) ^ 2 ≤
        4 * (q00 * c0 ^ 2 + 2 * q02 * c0 * c2 + q22 * c2 ^ 2) *
          (o11 * c1 ^ 2 + 2 * o13 * c1 * c3 + o33 * c3 ^ 2) := by
  intro c0 c2 c1 c3
  let D : ℝ := q00 * q22 - q02 ^ 2
  let j0 : ℝ := j01 * c1 + j03 * c3
  let j2 : ℝ := j21 * c1 + j23 * c3
  let E : ℝ := q00 * c0 ^ 2 + 2 * q02 * c0 * c2 + q22 * c2 ^ 2
  let O : ℝ := o11 * c1 ^ 2 + 2 * o13 * c1 * c3 + o33 * c3 ^ 2
  let J : ℝ := c0 * j0 + c2 * j2
  let A : ℝ := q22 * j0 ^ 2 - 2 * q02 * j0 * j2 + q00 * j2 ^ 2
  have hD : 0 < D := by simpa only [D] using hqdet
  have hE : 0 ≤ E := by
    have hidentity :
        q00 * E = (q00 * c0 + q02 * c2) ^ 2 + D * c2 ^ 2 := by
      dsimp only [E, D]
      ring
    have hscaled : 0 ≤ q00 * E := by
      rw [hidentity]
      exact add_nonneg (sq_nonneg _) (mul_nonneg hD.le (sq_nonneg _))
    nlinarith
  have hA : 0 ≤ A := by
    dsimp only [A, j0, j2]
    exact twoByTwo_adjugateQuadratic_nonneg
      q00 q02 q22 _ _ hq00 hqdet
  have hAO : A ≤ 4 * D * O := by
    have h := hres c1 c3
    dsimp only [A, O, D, j0, j2] at h ⊢
    linarith
  have hLagrange :
      E * A - D * J ^ 2 =
        (c0 * (q00 * j2 - q02 * j0) +
          c2 * (q02 * j2 - q22 * j0)) ^ 2 := by
    dsimp only [E, A, D, J]
    ring
  have hDJ : D * J ^ 2 ≤ E * A := by
    nlinarith [sq_nonneg
      (c0 * (q00 * j2 - q02 * j0) +
        c2 * (q02 * j2 - q22 * j0))]
  have hEA : E * A ≤ E * (4 * D * O) :=
    mul_le_mul_of_nonneg_left hAO hE
  have hfinal : J ^ 2 ≤ 4 * E * O := by
    have : D * J ^ 2 ≤ D * (4 * E * O) := by
      calc
        D * J ^ 2 ≤ E * A := hDJ
        _ ≤ E * (4 * D * O) := hEA
        _ = D * (4 * E * O) := by ring
    nlinarith
  simpa only [E, O, J, j0, j2] using hfinal

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusStructural
