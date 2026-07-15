import Mathlib

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.ThreeByThreeFractionFreeGram

noncomputable section

open Polynomial

/-!
# Fraction-free three-by-three Gram algebra

These identities isolate the commutative-ring algebra behind a scalar Schur
elimination followed by a three-dimensional adjugate-Gram determinant.  They
are specialized to real polynomials because that is the production ring in
the projective factor-two argument.  No polynomial coefficients are
evaluated or enumerated.
-/

/-- Determinant of a symmetric `3 x 3` matrix in upper-triangular
coordinates. -/
def det3
    (a00 a01 a02 a11 a12 a22 : ℝ[X]) : ℝ[X] :=
  a00 * (a11 * a22 - a12 ^ 2) -
    a01 * (a01 * a22 - a02 * a12) +
    a02 * (a01 * a12 - a02 * a11)

/-- The explicit determinant of a scalar head `p`, three cross entries
`b`, and a symmetric `3 x 3` residual block `r`, with cross scale `x`. -/
def borderedGap
    (p x b0 b1 b2 r00 r01 r02 r11 r12 r22 : ℝ[X]) : ℝ[X] :=
  (p * (r00 * r11 - r01 ^ 2) -
      x * (r11 * b0 ^ 2 - 2 * r01 * b0 * b1 + r00 * b1 ^ 2)) * r22 -
    (x * (r00 * r11 - r01 ^ 2) * b2 ^ 2 +
      2 * x * (b1 * r01 - b0 * r11) * b2 * r02 +
      2 * x * (b0 * r01 - b1 * r00) * b2 * r12 +
      (p * r11 - x * b1 ^ 2) * r02 ^ 2 +
      2 * (x * b0 * b1 - p * r01) * r02 * r12 +
      (p * r00 - x * b0 ^ 2) * r12 ^ 2)

/-- Fraction-free elimination of the scalar head of a bordered symmetric
determinant. -/
theorem borderedGap_fractionFree
    (p x b0 b1 b2 r00 r01 r02 r11 r12 r22 : ℝ[X]) :
    p ^ 2 * borderedGap p x b0 b1 b2 r00 r01 r02 r11 r12 r22 =
      det3
        (p * r00 - x * b0 * b0)
        (p * r01 - x * b0 * b1)
        (p * r02 - x * b0 * b2)
        (p * r11 - x * b1 * b1)
        (p * r12 - x * b1 * b2)
        (p * r22 - x * b2 * b2) := by
  unfold borderedGap det3
  ring

/-- First mixed coefficient in `det (p O - x A)`. -/
def mixedOne
    (o00 o01 o02 o11 o12 o22 a00 a01 a02 a11 a12 a22 : ℝ[X]) : ℝ[X] :=
  (o11 * o22 - o12 ^ 2) * a00 +
    2 * (o02 * o12 - o01 * o22) * a01 +
    2 * (o01 * o12 - o02 * o11) * a02 +
    (o00 * o22 - o02 ^ 2) * a11 +
    2 * (o01 * o02 - o00 * o12) * a12 +
    (o00 * o11 - o01 ^ 2) * a22

/-- Second mixed coefficient after the `2 x 2` minors of `A` have been
factored as `p C`. -/
def mixedTwo
    (o00 o01 o02 o11 o12 o22 c00 c01 c02 c11 c12 c22 : ℝ[X]) : ℝ[X] :=
  o00 * c00 + 2 * o01 * c01 + 2 * o02 * c02 +
    o11 * c11 + 2 * o12 * c12 + o22 * c22

/-- Division-free cubic determinant polynomial after factoring the adjugate
Gram minors and determinant. -/
def rawDet
    (p x delta o00 o01 o02 o11 o12 o22
      a00 a01 a02 a11 a12 a22 c00 c01 c02 c11 c12 c22 : ℝ[X]) : ℝ[X] :=
  p * det3 o00 o01 o02 o11 o12 o22 -
    x * mixedOne o00 o01 o02 o11 o12 o22 a00 a01 a02 a11 a12 a22 +
    x ^ 2 * mixedTwo o00 o01 o02 o11 o12 o22 c00 c01 c02 c11 c12 c22 -
    x ^ 3 * delta ^ 2

/-- Expansion of `det (p O - x A)` after the six adjugate-Gram minor
identities and the Gram determinant identity are supplied. -/
theorem det3_affine_adjugateGram
    (p x delta o00 o01 o02 o11 o12 o22
      a00 a01 a02 a11 a12 a22 c00 c01 c02 c11 c12 c22 : ℝ[X])
    (hc00 : a11 * a22 - a12 ^ 2 = p * c00)
    (hc01 : a02 * a12 - a01 * a22 = p * c01)
    (hc02 : a01 * a12 - a02 * a11 = p * c02)
    (hc11 : a00 * a22 - a02 ^ 2 = p * c11)
    (hc12 : a01 * a02 - a00 * a12 = p * c12)
    (hc22 : a00 * a11 - a01 ^ 2 = p * c22)
    (hdet : det3 a00 a01 a02 a11 a12 a22 = p ^ 2 * delta ^ 2) :
    det3
        (p * o00 - x * a00)
        (p * o01 - x * a01)
        (p * o02 - x * a02)
        (p * o11 - x * a11)
        (p * o12 - x * a12)
        (p * o22 - x * a22) =
      p ^ 2 *
        rawDet p x delta o00 o01 o02 o11 o12 o22
          a00 a01 a02 a11 a12 a22 c00 c01 c02 c11 c12 c22 := by
  calc
    det3
        (p * o00 - x * a00)
        (p * o01 - x * a01)
        (p * o02 - x * a02)
        (p * o11 - x * a11)
        (p * o12 - x * a12)
        (p * o22 - x * a22) =
      p ^ 3 * det3 o00 o01 o02 o11 o12 o22 -
        x * p ^ 2 *
          mixedOne o00 o01 o02 o11 o12 o22 a00 a01 a02 a11 a12 a22 +
        x ^ 2 * p *
          (o00 * (a11 * a22 - a12 ^ 2) +
            2 * o01 * (a02 * a12 - a01 * a22) +
            2 * o02 * (a01 * a12 - a02 * a11) +
            o11 * (a00 * a22 - a02 ^ 2) +
            2 * o12 * (a01 * a02 - a00 * a12) +
            o22 * (a00 * a11 - a01 ^ 2)) -
        x ^ 3 * det3 a00 a01 a02 a11 a12 a22 := by
          unfold det3 mixedOne
          ring
    _ = p ^ 2 *
        rawDet p x delta o00 o01 o02 o11 o12 o22
          a00 a01 a02 a11 a12 a22 c00 c01 c02 c11 c12 c22 := by
      rw [hc00, hc01, hc02, hc11, hc12, hc22, hdet]
      unfold rawDet mixedTwo
      ring

private theorem det3_scale
    (d t00 t01 t02 t11 t12 t22 : ℝ[X]) :
    det3 (d * t00) (d * t01) (d * t02)
        (d * t11) (d * t12) (d * t22) =
      d ^ 3 * det3 t00 t01 t02 t11 t12 t22 := by
  unfold det3
  ring

/-- Complete fraction-free factorization.  The six `hs` hypotheses are the
polarized Schur updates; the six `hc` hypotheses and `hdet` are precisely the
three-dimensional adjugate-Gram identities. -/
theorem complete_fractionFree_factor
    (d p x delta b0 b1 b2
      o00 o01 o02 o11 o12 o22 h00 h01 h02 h11 h12 h22
      a00 a01 a02 a11 a12 a22 c00 c01 c02 c11 c12 c22 : ℝ[X])
    (hp : p ≠ 0)
    (hs00 : p * h00 + b0 * b0 = d * a00)
    (hs01 : p * h01 + b0 * b1 = d * a01)
    (hs02 : p * h02 + b0 * b2 = d * a02)
    (hs11 : p * h11 + b1 * b1 = d * a11)
    (hs12 : p * h12 + b1 * b2 = d * a12)
    (hs22 : p * h22 + b2 * b2 = d * a22)
    (hc00 : a11 * a22 - a12 ^ 2 = p * c00)
    (hc01 : a02 * a12 - a01 * a22 = p * c01)
    (hc02 : a01 * a12 - a02 * a11 = p * c02)
    (hc11 : a00 * a22 - a02 ^ 2 = p * c11)
    (hc12 : a01 * a02 - a00 * a12 = p * c12)
    (hc22 : a00 * a11 - a01 ^ 2 = p * c22)
    (hdet : det3 a00 a01 a02 a11 a12 a22 = p ^ 2 * delta ^ 2) :
    borderedGap p x b0 b1 b2
        (d * o00 - x * h00) (d * o01 - x * h01)
        (d * o02 - x * h02) (d * o11 - x * h11)
        (d * o12 - x * h12) (d * o22 - x * h22) =
      d ^ 3 *
        rawDet p x delta o00 o01 o02 o11 o12 o22
          a00 a01 a02 a11 a12 a22 c00 c01 c02 c11 c12 c22 := by
  apply (mul_left_cancel₀ (pow_ne_zero 2 hp))
  rw [borderedGap_fractionFree]
  have ht00 :
      p * (d * o00 - x * h00) - x * b0 * b0 =
        d * (p * o00 - x * a00) := by
    calc
      p * (d * o00 - x * h00) - x * b0 * b0 =
          d * p * o00 - x * (p * h00 + b0 * b0) := by ring
      _ = d * p * o00 - x * (d * a00) := by rw [hs00]
      _ = d * (p * o00 - x * a00) := by ring
  have ht01 :
      p * (d * o01 - x * h01) - x * b0 * b1 =
        d * (p * o01 - x * a01) := by
    calc
      p * (d * o01 - x * h01) - x * b0 * b1 =
          d * p * o01 - x * (p * h01 + b0 * b1) := by ring
      _ = d * p * o01 - x * (d * a01) := by rw [hs01]
      _ = d * (p * o01 - x * a01) := by ring
  have ht02 :
      p * (d * o02 - x * h02) - x * b0 * b2 =
        d * (p * o02 - x * a02) := by
    calc
      p * (d * o02 - x * h02) - x * b0 * b2 =
          d * p * o02 - x * (p * h02 + b0 * b2) := by ring
      _ = d * p * o02 - x * (d * a02) := by rw [hs02]
      _ = d * (p * o02 - x * a02) := by ring
  have ht11 :
      p * (d * o11 - x * h11) - x * b1 * b1 =
        d * (p * o11 - x * a11) := by
    calc
      p * (d * o11 - x * h11) - x * b1 * b1 =
          d * p * o11 - x * (p * h11 + b1 * b1) := by ring
      _ = d * p * o11 - x * (d * a11) := by rw [hs11]
      _ = d * (p * o11 - x * a11) := by ring
  have ht12 :
      p * (d * o12 - x * h12) - x * b1 * b2 =
        d * (p * o12 - x * a12) := by
    calc
      p * (d * o12 - x * h12) - x * b1 * b2 =
          d * p * o12 - x * (p * h12 + b1 * b2) := by ring
      _ = d * p * o12 - x * (d * a12) := by rw [hs12]
      _ = d * (p * o12 - x * a12) := by ring
  have ht22 :
      p * (d * o22 - x * h22) - x * b2 * b2 =
        d * (p * o22 - x * a22) := by
    calc
      p * (d * o22 - x * h22) - x * b2 * b2 =
          d * p * o22 - x * (p * h22 + b2 * b2) := by ring
      _ = d * p * o22 - x * (d * a22) := by rw [hs22]
      _ = d * (p * o22 - x * a22) := by ring
  rw [ht00, ht01, ht02, ht11, ht12, ht22, det3_scale,
    det3_affine_adjugateGram p x delta o00 o01 o02 o11 o12 o22
      a00 a01 a02 a11 a12 a22 c00 c01 c02 c11 c12 c22
      hc00 hc01 hc02 hc11 hc12 hc22 hdet]
  ring

end

end ArithmeticHodge.Analysis.ThreeByThreeFractionFreeGram
