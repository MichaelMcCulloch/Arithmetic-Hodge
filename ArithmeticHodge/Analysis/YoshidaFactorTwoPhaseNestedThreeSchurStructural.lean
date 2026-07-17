import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseNestedThreeSchurStructural

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

/-!
# A nested inverse-free `3 + 3 + 3` Schur completion

The first fraction-free Schur remainder is allowed to be supplied by an
exact algebraic identity.  Its resulting `3 + 3` form is then completed by
the existing inverse-free six-block theorem.  A second application of the
same theorem, with the lower six variables compressed into the first Schur
remainder, completes the original `3 + 3 + 3` form.

Thus the public theorem needs only strict Sylvester pivots for the first
block and its fraction-free middle Schur block, together with
nonnegativity of the final fraction-free `3 x 3` block.  There is no inverse,
division, or `9 x 9` determinant expansion.
-/

private theorem fractionFreeSchurQuadratic_eq
    (r00 r01 r02 r11 r12 r22
      u00 u01 u02 u10 u11 u12 u20 u21 u22
      v00 v01 v02 v11 v12 v22 z0 z1 z2 : ℝ) :
    symmetricQuadratic
        (symmetricDeterminant r00 r01 r02 r11 r12 r22 * v00 -
          unbalancedThreeAdjugatePair r00 r01 r02 r11 r12 r22
            u00 u10 u20 u00 u10 u20)
        (symmetricDeterminant r00 r01 r02 r11 r12 r22 * v01 -
          unbalancedThreeAdjugatePair r00 r01 r02 r11 r12 r22
            u00 u10 u20 u01 u11 u21)
        (symmetricDeterminant r00 r01 r02 r11 r12 r22 * v02 -
          unbalancedThreeAdjugatePair r00 r01 r02 r11 r12 r22
            u00 u10 u20 u02 u12 u22)
        (symmetricDeterminant r00 r01 r02 r11 r12 r22 * v11 -
          unbalancedThreeAdjugatePair r00 r01 r02 r11 r12 r22
            u01 u11 u21 u01 u11 u21)
        (symmetricDeterminant r00 r01 r02 r11 r12 r22 * v12 -
          unbalancedThreeAdjugatePair r00 r01 r02 r11 r12 r22
            u01 u11 u21 u02 u12 u22)
        (symmetricDeterminant r00 r01 r02 r11 r12 r22 * v22 -
          unbalancedThreeAdjugatePair r00 r01 r02 r11 r12 r22
            u02 u12 u22 u02 u12 u22)
        z0 z1 z2 =
      symmetricDeterminant r00 r01 r02 r11 r12 r22 *
          symmetricQuadratic v00 v01 v02 v11 v12 v22 z0 z1 z2 -
        adjugateQuadratic r00 r01 r02 r11 r12 r22
          (u00 * z0 + u01 * z1 + u02 * z2)
          (u10 * z0 + u11 * z1 + u12 * z2)
          (u20 * z0 + u21 * z1 + u22 * z2) := by
  unfold symmetricQuadratic unbalancedThreeAdjugatePair adjugateQuadratic
  ring

/-- Generic nested inverse-free Schur completion for a real symmetric
`3 + 3 + 3` block form.

`hFirstSchurEq` is the exact identification of the fraction-free Schur
remainder after eliminating the first block with the displayed lower
`3 + 3` form.  The `r` block is strictly positive by its three Sylvester
pivots.  `hW` is precisely positive semidefiniteness of the final
fraction-free `3 x 3` Schur block. -/
theorem nineBlock_nonneg_of_nested_fractionFreeSchur
    (a00 a01 a02 a11 a12 a22
      r00 r01 r02 r11 r12 r22
      u00 u01 u02 u10 u11 u12 u20 u21 u22
      v00 v01 v02 v11 v12 v22 : ℝ)
    (ha00 : 0 < a00)
    (haMinor : 0 < leadingMinorTwo a00 a01 a11)
    (haDet : 0 < symmetricDeterminant a00 a01 a02 a11 a12 a22)
    (hr00 : 0 < r00)
    (hrMinor : 0 < leadingMinorTwo r00 r01 r11)
    (hrDet : 0 < symmetricDeterminant r00 r01 r02 r11 r12 r22)
    (hW : ∀ z0 z1 z2 : ℝ,
      0 ≤ symmetricQuadratic
        (symmetricDeterminant r00 r01 r02 r11 r12 r22 * v00 -
          unbalancedThreeAdjugatePair r00 r01 r02 r11 r12 r22
            u00 u10 u20 u00 u10 u20)
        (symmetricDeterminant r00 r01 r02 r11 r12 r22 * v01 -
          unbalancedThreeAdjugatePair r00 r01 r02 r11 r12 r22
            u00 u10 u20 u01 u11 u21)
        (symmetricDeterminant r00 r01 r02 r11 r12 r22 * v02 -
          unbalancedThreeAdjugatePair r00 r01 r02 r11 r12 r22
            u00 u10 u20 u02 u12 u22)
        (symmetricDeterminant r00 r01 r02 r11 r12 r22 * v11 -
          unbalancedThreeAdjugatePair r00 r01 r02 r11 r12 r22
            u01 u11 u21 u01 u11 u21)
        (symmetricDeterminant r00 r01 r02 r11 r12 r22 * v12 -
          unbalancedThreeAdjugatePair r00 r01 r02 r11 r12 r22
            u01 u11 u21 u02 u12 u22)
        (symmetricDeterminant r00 r01 r02 r11 r12 r22 * v22 -
          unbalancedThreeAdjugatePair r00 r01 r02 r11 r12 r22
            u02 u12 u22 u02 u12 u22)
        z0 z1 z2)
    (ell0 ell1 ell2 remainder x0 x1 x2 y0 y1 y2 z0 z1 z2 : ℝ)
    (hFirstSchurEq :
      symmetricDeterminant a00 a01 a02 a11 a12 a22 * remainder -
          adjugateQuadratic a00 a01 a02 a11 a12 a22 ell0 ell1 ell2 =
        symmetricQuadratic r00 r01 r02 r11 r12 r22 y0 y1 y2 +
          2 * (y0 * (u00 * z0 + u01 * z1 + u02 * z2) +
            y1 * (u10 * z0 + u11 * z1 + u12 * z2) +
            y2 * (u20 * z0 + u21 * z1 + u22 * z2)) +
          symmetricQuadratic v00 v01 v02 v11 v12 v22 z0 z1 z2) :
    0 ≤ symmetricQuadratic a00 a01 a02 a11 a12 a22 x0 x1 x2 +
      2 * (x0 * ell0 + x1 * ell1 + x2 * ell2) + remainder := by
  have hLower :
      0 ≤ symmetricQuadratic r00 r01 r02 r11 r12 r22 y0 y1 y2 +
        2 * (y0 * (u00 * z0 + u01 * z1 + u02 * z2) +
          y1 * (u10 * z0 + u11 * z1 + u12 * z2) +
          y2 * (u20 * z0 + u21 * z1 + u22 * z2)) +
        symmetricQuadratic v00 v01 v02 v11 v12 v22 z0 z1 z2 := by
    apply sixBlock_nonneg_of_fractionFreeSchur
      r00 r01 r02 r11 r12 r22
      u00 u01 u02 u10 u11 u12 u20 u21 u22
      v00 v01 v02 v11 v12 v22
      hr00 hrMinor hrDet
    · intro w0 w1 w2
      rw [← fractionFreeSchurQuadratic_eq]
      exact hW w0 w1 w2
  have hFirstSchur :
      0 ≤ symmetricDeterminant a00 a01 a02 a11 a12 a22 * remainder -
        adjugateQuadratic a00 a01 a02 a11 a12 a22 ell0 ell1 ell2 := by
    rw [hFirstSchurEq]
    exact hLower
  have hOuterSchur : ∀ s0 s1 s2 : ℝ,
      0 ≤ symmetricDeterminant a00 a01 a02 a11 a12 a22 *
          symmetricQuadratic remainder 0 0 0 0 0 s0 s1 s2 -
        adjugateQuadratic a00 a01 a02 a11 a12 a22
          (ell0 * s0 + 0 * s1 + 0 * s2)
          (ell1 * s0 + 0 * s1 + 0 * s2)
          (ell2 * s0 + 0 * s1 + 0 * s2) := by
    intro s0 s1 s2
    have hIdentity :
        symmetricDeterminant a00 a01 a02 a11 a12 a22 *
            symmetricQuadratic remainder 0 0 0 0 0 s0 s1 s2 -
          adjugateQuadratic a00 a01 a02 a11 a12 a22
            (ell0 * s0 + 0 * s1 + 0 * s2)
            (ell1 * s0 + 0 * s1 + 0 * s2)
            (ell2 * s0 + 0 * s1 + 0 * s2) =
          s0 ^ 2 *
            (symmetricDeterminant a00 a01 a02 a11 a12 a22 * remainder -
              adjugateQuadratic a00 a01 a02 a11 a12 a22 ell0 ell1 ell2) := by
      unfold symmetricQuadratic adjugateQuadratic
      ring
    rw [hIdentity]
    exact mul_nonneg (sq_nonneg s0) hFirstSchur
  have hFull := sixBlock_nonneg_of_fractionFreeSchur
    a00 a01 a02 a11 a12 a22
    ell0 0 0 ell1 0 0 ell2 0 0
    remainder 0 0 0 0 0
    ha00 haMinor haDet hOuterSchur
    x0 x1 x2 1 0 0
  simpa [symmetricQuadratic] using hFull

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseNestedThreeSchurStructural
