import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSplitStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSplitStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Fraction-free Schur reduction of the corrected static blocks

Each corrected six-mode endpoint form is written as a symmetric `3 + 3`
block form.  The alternating coefficients are halved when they are placed in
the off-diagonal block: the quadratic cross term is `2 eᵀ K o`.  This is the
cross convention used throughout the file.

For a positive even block `E`, define the fraction-free odd Schur block

`T = det(E) O - Kᵀ adj(E) K`.

An exact adjugate completion proves that nonnegativity of the quadratic form
of `T` implies nonnegativity of the complete corrected endpoint form.  No
inverse, division, endpoint estimate, or coefficient enumeration is used.
-/

/-! ## Generic inverse-free `3 + 3` completion -/

/-- Polarized evaluation of the adjugate of a symmetric `3 x 3` matrix.
The matrix entries are ordered as `(00, 02, 04, 22, 24, 44)`. -/
def unbalancedThreeAdjugatePair
    (e00 e02 e04 e22 e24 e44
      u0 u2 u4 v0 v2 v4 : ℝ) : ℝ :=
  (e22 * e44 - e24 ^ 2) * u0 * v0 +
    (e04 * e24 - e02 * e44) * (u0 * v2 + u2 * v0) +
    (e02 * e24 - e04 * e22) * (u0 * v4 + u4 * v0) +
    (e00 * e44 - e04 ^ 2) * u2 * v2 +
    (e02 * e04 - e00 * e24) * (u2 * v4 + u4 * v2) +
    (e00 * e22 - e02 ^ 2) * u4 * v4

theorem unbalancedThreeAdjugatePair_self
    (e00 e02 e04 e22 e24 e44 u0 u2 u4 : ℝ) :
    unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
        u0 u2 u4 u0 u2 u4 =
      adjugateQuadratic e00 e02 e04 e22 e24 e44 u0 u2 u4 := by
  unfold unbalancedThreeAdjugatePair adjugateQuadratic
  ring

theorem unbalancedThreeAdjugatePair_linear_combination
    (e00 e02 e04 e22 e24 e44
      k01 k03 k05 k21 k23 k25 k41 k43 k45
      c1 c3 c5 : ℝ) :
    unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
        (k01 * c1 + k03 * c3 + k05 * c5)
        (k21 * c1 + k23 * c3 + k25 * c5)
        (k41 * c1 + k43 * c3 + k45 * c5)
        (k01 * c1 + k03 * c3 + k05 * c5)
        (k21 * c1 + k23 * c3 + k25 * c5)
        (k41 * c1 + k43 * c3 + k45 * c5) =
      symmetricQuadratic
        (unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
          k01 k21 k41 k01 k21 k41)
        (unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
          k01 k21 k41 k03 k23 k43)
        (unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
          k01 k21 k41 k05 k25 k45)
        (unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
          k03 k23 k43 k03 k23 k43)
        (unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
          k03 k23 k43 k05 k25 k45)
        (unbalancedThreeAdjugatePair e00 e02 e04 e22 e24 e44
          k05 k25 k45 k05 k25 k45)
        c1 c3 c5 := by
  unfold unbalancedThreeAdjugatePair symmetricQuadratic
  ring

private theorem symmetricQuadratic_fractionFree_sub
    (d o11 o13 o15 o33 o35 o55
      p11 p13 p15 p33 p35 p55 c1 c3 c5 : ℝ) :
    symmetricQuadratic
        (d * o11 - p11) (d * o13 - p13) (d * o15 - p15)
        (d * o33 - p33) (d * o35 - p35) (d * o55 - p55)
        c1 c3 c5 =
      d * symmetricQuadratic o11 o13 o15 o33 o35 o55 c1 c3 c5 -
        symmetricQuadratic p11 p13 p15 p33 p35 p55 c1 c3 c5 := by
  unfold symmetricQuadratic
  ring

private theorem fractionFreeSchurQuadratic_eq
    (e00 e02 e04 e22 e24 e44
      k01 k03 k05 k21 k23 k25 k41 k43 k45
      o11 o13 o15 o33 o35 o55 c1 c3 c5 : ℝ) :
    let d := symmetricDeterminant e00 e02 e04 e22 e24 e44
    symmetricQuadratic
        (d * o11 - unbalancedThreeAdjugatePair
          e00 e02 e04 e22 e24 e44 k01 k21 k41 k01 k21 k41)
        (d * o13 - unbalancedThreeAdjugatePair
          e00 e02 e04 e22 e24 e44 k01 k21 k41 k03 k23 k43)
        (d * o15 - unbalancedThreeAdjugatePair
          e00 e02 e04 e22 e24 e44 k01 k21 k41 k05 k25 k45)
        (d * o33 - unbalancedThreeAdjugatePair
          e00 e02 e04 e22 e24 e44 k03 k23 k43 k03 k23 k43)
        (d * o35 - unbalancedThreeAdjugatePair
          e00 e02 e04 e22 e24 e44 k03 k23 k43 k05 k25 k45)
        (d * o55 - unbalancedThreeAdjugatePair
          e00 e02 e04 e22 e24 e44 k05 k25 k45 k05 k25 k45)
        c1 c3 c5 =
      d * symmetricQuadratic o11 o13 o15 o33 o35 o55 c1 c3 c5 -
        adjugateQuadratic e00 e02 e04 e22 e24 e44
          (k01 * c1 + k03 * c3 + k05 * c5)
          (k21 * c1 + k23 * c3 + k25 * c5)
          (k41 * c1 + k43 * c3 + k45 * c5) := by
  dsimp only
  rw [symmetricQuadratic_fractionFree_sub]
  rw [← unbalancedThreeAdjugatePair_linear_combination]
  rw [unbalancedThreeAdjugatePair_self]

/-- The polarized form associated with `symmetricQuadratic`, grouped by its
left argument. -/
private def unbalancedThreeBilinear
    (e00 e02 e04 e22 e24 e44
      x0 x2 x4 y0 y2 y4 : ℝ) : ℝ :=
  x0 * (e00 * y0 + e02 * y2 + e04 * y4) +
    x2 * (e02 * y0 + e22 * y2 + e24 * y4) +
    x4 * (e04 * y0 + e24 * y2 + e44 * y4)

private theorem symmetricQuadratic_eq_bilinear_self
    (e00 e02 e04 e22 e24 e44 x0 x2 x4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44 x0 x2 x4 =
      unbalancedThreeBilinear e00 e02 e04 e22 e24 e44
        x0 x2 x4 x0 x2 x4 := by
  unfold symmetricQuadratic unbalancedThreeBilinear
  ring

private theorem symmetricQuadratic_add_vector
    (e00 e02 e04 e22 e24 e44
      x0 x2 x4 y0 y2 y4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44
        (x0 + y0) (x2 + y2) (x4 + y4) =
      symmetricQuadratic e00 e02 e04 e22 e24 e44 x0 x2 x4 +
        2 * unbalancedThreeBilinear e00 e02 e04 e22 e24 e44
          x0 x2 x4 y0 y2 y4 +
        symmetricQuadratic e00 e02 e04 e22 e24 e44 y0 y2 y4 := by
  unfold symmetricQuadratic unbalancedThreeBilinear
  ring

private theorem symmetricQuadratic_scale_vector
    (e00 e02 e04 e22 e24 e44 d x0 x2 x4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44
        (d * x0) (d * x2) (d * x4) =
      d ^ 2 * symmetricQuadratic e00 e02 e04 e22 e24 e44 x0 x2 x4 := by
  unfold symmetricQuadratic
  ring

private theorem unbalancedThreeBilinear_scale_left
    (e00 e02 e04 e22 e24 e44 d x0 x2 x4 y0 y2 y4 : ℝ) :
    unbalancedThreeBilinear e00 e02 e04 e22 e24 e44
        (d * x0) (d * x2) (d * x4) y0 y2 y4 =
      d * unbalancedThreeBilinear e00 e02 e04 e22 e24 e44
        x0 x2 x4 y0 y2 y4 := by
  unfold unbalancedThreeBilinear
  ring

private theorem adjugateVector_row0
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 : ℝ) :
    e00 * adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0 +
        e02 * adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1 +
        e04 * adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2 =
      symmetricDeterminant e00 e02 e04 e22 e24 e44 * ell0 := by
  simp only [adjugateVector]
  unfold symmetricDeterminant
  ring

private theorem adjugateVector_row2
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 : ℝ) :
    e02 * adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0 +
        e22 * adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1 +
        e24 * adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2 =
      symmetricDeterminant e00 e02 e04 e22 e24 e44 * ell2 := by
  simp only [adjugateVector]
  unfold symmetricDeterminant
  ring

private theorem adjugateVector_row4
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 : ℝ) :
    e04 * adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0 +
        e24 * adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1 +
        e44 * adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2 =
      symmetricDeterminant e00 e02 e04 e22 e24 e44 * ell4 := by
  simp only [adjugateVector]
  unfold symmetricDeterminant
  ring

private theorem unbalancedThreeBilinear_adjugateVector
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 x0 x2 x4 : ℝ) :
    unbalancedThreeBilinear e00 e02 e04 e22 e24 e44 x0 x2 x4
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2) =
      symmetricDeterminant e00 e02 e04 e22 e24 e44 *
        (x0 * ell0 + x2 * ell2 + x4 * ell4) := by
  unfold unbalancedThreeBilinear
  rw [adjugateVector_row0, adjugateVector_row2, adjugateVector_row4]
  ring

private theorem adjugateVector_dot
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 : ℝ) :
    adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0 * ell0 +
        adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1 * ell2 +
        adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2 * ell4 =
      adjugateQuadratic e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 := by
  simp only [adjugateVector]
  unfold adjugateQuadratic
  ring

private theorem symmetricQuadratic_adjugateVector
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2) =
      symmetricDeterminant e00 e02 e04 e22 e24 e44 *
        adjugateQuadratic e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 := by
  rw [symmetricQuadratic_eq_bilinear_self]
  rw [unbalancedThreeBilinear_adjugateVector]
  rw [adjugateVector_dot]

private theorem fractionFree_three_by_three_completion
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4
      c0 c2 c4 r : ℝ) :
    let d := symmetricDeterminant e00 e02 e04 e22 e24 e44
    let v := adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4
    d ^ 2 *
        (symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
          2 * (c0 * ell0 + c2 * ell2 + c4 * ell4) +
          r) =
      symmetricQuadratic e00 e02 e04 e22 e24 e44
          (d * c0 + v 0) (d * c2 + v 1) (d * c4 + v 2) +
        d * (d * r - adjugateQuadratic
          e00 e02 e04 e22 e24 e44 ell0 ell2 ell4) := by
  dsimp only
  rw [symmetricQuadratic_add_vector]
  rw [symmetricQuadratic_scale_vector]
  rw [unbalancedThreeBilinear_scale_left]
  rw [unbalancedThreeBilinear_adjugateVector]
  rw [symmetricQuadratic_adjugateVector]
  ring

/-- Reusable inverse-free block-Schur reduction.  Strict Sylvester pivots of
the even block and nonnegativity of the fraction-free `3 x 3` Schur block
imply nonnegativity of the full `3 + 3` quadratic. -/
theorem sixBlock_nonneg_of_fractionFreeSchur
    (e00 e02 e04 e22 e24 e44
      k01 k03 k05 k21 k23 k25 k41 k43 k45
      o11 o13 o15 o33 o35 o55 : ℝ)
    (he00 : 0 < e00)
    (heMinor : 0 < leadingMinorTwo e00 e02 e22)
    (heDet : 0 < symmetricDeterminant e00 e02 e04 e22 e24 e44)
    (hT : ∀ c1 c3 c5 : ℝ,
      0 ≤ symmetricDeterminant e00 e02 e04 e22 e24 e44 *
          symmetricQuadratic o11 o13 o15 o33 o35 o55 c1 c3 c5 -
        adjugateQuadratic e00 e02 e04 e22 e24 e44
          (k01 * c1 + k03 * c3 + k05 * c5)
          (k21 * c1 + k23 * c3 + k25 * c5)
          (k41 * c1 + k43 * c3 + k45 * c5))
    (c0 c2 c4 c1 c3 c5 : ℝ) :
    0 ≤ symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
      2 * (c0 * (k01 * c1 + k03 * c3 + k05 * c5) +
        c2 * (k21 * c1 + k23 * c3 + k25 * c5) +
        c4 * (k41 * c1 + k43 * c3 + k45 * c5)) +
      symmetricQuadratic o11 o13 o15 o33 o35 o55 c1 c3 c5 := by
  let d := symmetricDeterminant e00 e02 e04 e22 e24 e44
  let ell0 := k01 * c1 + k03 * c3 + k05 * c5
  let ell2 := k21 * c1 + k23 * c3 + k25 * c5
  let ell4 := k41 * c1 + k43 * c3 + k45 * c5
  let v := adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4
  have hEven : 0 ≤ symmetricQuadratic e00 e02 e04 e22 e24 e44
      (d * c0 + v 0) (d * c2 + v 1) (d * c4 + v 2) :=
    symmetricQuadratic_nonneg e00 e02 e04 e22 e24 e44
      he00 heMinor heDet _ _ _
  have hSchur := hT c1 c3 c5
  have hIdentity := fractionFree_three_by_three_completion
    e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 c0 c2 c4
      (symmetricQuadratic o11 o13 o15 o33 o35 o55 c1 c3 c5)
  dsimp only [d, ell0, ell2, ell4, v] at hEven hIdentity
  have hScaled : 0 ≤ symmetricDeterminant e00 e02 e04 e22 e24 e44 ^ 2 *
      (symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
        2 * (c0 * (k01 * c1 + k03 * c3 + k05 * c5) +
          c2 * (k21 * c1 + k23 * c3 + k25 * c5) +
          c4 * (k41 * c1 + k43 * c3 + k45 * c5)) +
        symmetricQuadratic o11 o13 o15 o33 o35 o55 c1 c3 c5) := by
    rw [hIdentity]
    exact add_nonneg hEven (mul_nonneg heDet.le hSchur)
  have hScaled' : 0 ≤
      (symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
        2 * (c0 * (k01 * c1 + k03 * c3 + k05 * c5) +
          c2 * (k21 * c1 + k23 * c3 + k25 * c5) +
          c4 * (k41 * c1 + k43 * c3 + k45 * c5)) +
        symmetricQuadratic o11 o13 o15 o33 o35 o55 c1 c3 c5) *
      symmetricDeterminant e00 e02 e04 e22 e24 e44 ^ 2 := by
    simpa only [mul_comm] using hScaled
  exact nonneg_of_mul_nonneg_left hScaled' (sq_pos_of_pos heDet)

/-! ## Endpoint block entries -/

def factorTwoIntrinsicSixUnbalancedEPlus00 : ℝ :=
  factorTwoStructuralPhaseLow00 1

def factorTwoIntrinsicSixUnbalancedEPlus02 : ℝ :=
  factorTwoStructuralPhaseLow02 1

def factorTwoIntrinsicSixUnbalancedEPlus04 : ℝ :=
  factorTwoIntrinsicFourP45Cross04 1

def factorTwoIntrinsicSixUnbalancedEPlus22 : ℝ :=
  factorTwoStructuralPhaseLow22 1

def factorTwoIntrinsicSixUnbalancedEPlus24 : ℝ :=
  factorTwoIntrinsicFourP45Cross24 1

def factorTwoIntrinsicSixUnbalancedEPlus44 : ℝ :=
  factorTwoIntrinsicP4PhaseDiagonal 1

def factorTwoIntrinsicSixUnbalancedEMinus00 : ℝ :=
  factorTwoStructuralPhaseLow00 (-1)

def factorTwoIntrinsicSixUnbalancedEMinus02 : ℝ :=
  factorTwoStructuralPhaseLow02 (-1)

def factorTwoIntrinsicSixUnbalancedEMinus04 : ℝ :=
  factorTwoIntrinsicFourP45Cross04 (-1)

def factorTwoIntrinsicSixUnbalancedEMinus22 : ℝ :=
  factorTwoStructuralPhaseLow22 (-1)

def factorTwoIntrinsicSixUnbalancedEMinus24 : ℝ :=
  factorTwoIntrinsicFourP45Cross24 (-1)

def factorTwoIntrinsicSixUnbalancedEMinus44 : ℝ :=
  factorTwoIntrinsicP4PhaseDiagonal (-1)

/-- The odd block paired with `E+` is the negative odd endpoint because
`factorTwoIntrinsicSixStaticOdd sigma` evaluates its entries at `-sigma`. -/
def factorTwoIntrinsicSixUnbalancedOMinus11 : ℝ :=
  factorTwoIntrinsicOddPhaseLow11 (-1)

def factorTwoIntrinsicSixUnbalancedOMinus13 : ℝ :=
  factorTwoIntrinsicOddPhaseLow13 (-1)

def factorTwoIntrinsicSixUnbalancedOMinus15 : ℝ :=
  factorTwoIntrinsicFourP45Cross15 (-1)

def factorTwoIntrinsicSixUnbalancedOMinus33 : ℝ :=
  factorTwoIntrinsicOddPhaseLow33 (-1)

def factorTwoIntrinsicSixUnbalancedOMinus35 : ℝ :=
  factorTwoIntrinsicFourP45Cross35 (-1)

def factorTwoIntrinsicSixUnbalancedOMinus55 : ℝ :=
  factorTwoIntrinsicP5PhaseDiagonal (-1)

/-- The odd block paired with `E-` is the positive odd endpoint. -/
def factorTwoIntrinsicSixUnbalancedOPlus11 : ℝ :=
  factorTwoIntrinsicOddPhaseLow11 1

def factorTwoIntrinsicSixUnbalancedOPlus13 : ℝ :=
  factorTwoIntrinsicOddPhaseLow13 1

def factorTwoIntrinsicSixUnbalancedOPlus15 : ℝ :=
  factorTwoIntrinsicFourP45Cross15 1

def factorTwoIntrinsicSixUnbalancedOPlus33 : ℝ :=
  factorTwoIntrinsicOddPhaseLow33 1

def factorTwoIntrinsicSixUnbalancedOPlus35 : ℝ :=
  factorTwoIntrinsicFourP45Cross35 1

def factorTwoIntrinsicSixUnbalancedOPlus55 : ℝ :=
  factorTwoIntrinsicP5PhaseDiagonal 1

/-! The factor `1/2` below is the off-diagonal block convention:
`factorTwoIntrinsicSixStaticAlternating = 2 eᵀ (A/2) o`. -/

def factorTwoIntrinsicSixUnbalancedKPlus01 : ℝ :=
  factorTwoIntrinsicAlternating01 / 2 - 63 / 1000

def factorTwoIntrinsicSixUnbalancedKPlus03 : ℝ :=
  factorTwoIntrinsicAlternating03 / 2 - 337 / 10000

def factorTwoIntrinsicSixUnbalancedKPlus05 : ℝ :=
  factorTwoIntrinsicFourP45Cross05 / 2 - 3 / 400

def factorTwoIntrinsicSixUnbalancedKPlus21 : ℝ :=
  factorTwoIntrinsicAlternating21 / 2 - 577 / 10000

def factorTwoIntrinsicSixUnbalancedKPlus23 : ℝ :=
  factorTwoIntrinsicAlternating23 / 2 - 7 / 200

def factorTwoIntrinsicSixUnbalancedKPlus25 : ℝ :=
  factorTwoIntrinsicFourP45Cross25 / 2 - 13 / 625

def factorTwoIntrinsicSixUnbalancedKPlus41 : ℝ :=
  factorTwoIntrinsicFourP45Cross41 / 2 - 169 / 5000

def factorTwoIntrinsicSixUnbalancedKPlus43 : ℝ :=
  factorTwoIntrinsicFourP45Cross43 / 2 - 253 / 5000

def factorTwoIntrinsicSixUnbalancedKPlus45 : ℝ :=
  factorTwoIntrinsicP45Alternating / 2 - 457 / 5000

def factorTwoIntrinsicSixUnbalancedKMinus01 : ℝ :=
  factorTwoIntrinsicAlternating01 / 2 + 63 / 1000

def factorTwoIntrinsicSixUnbalancedKMinus03 : ℝ :=
  factorTwoIntrinsicAlternating03 / 2 + 337 / 10000

def factorTwoIntrinsicSixUnbalancedKMinus05 : ℝ :=
  factorTwoIntrinsicFourP45Cross05 / 2 + 3 / 400

def factorTwoIntrinsicSixUnbalancedKMinus21 : ℝ :=
  factorTwoIntrinsicAlternating21 / 2 + 577 / 10000

def factorTwoIntrinsicSixUnbalancedKMinus23 : ℝ :=
  factorTwoIntrinsicAlternating23 / 2 + 7 / 200

def factorTwoIntrinsicSixUnbalancedKMinus25 : ℝ :=
  factorTwoIntrinsicFourP45Cross25 / 2 + 13 / 625

def factorTwoIntrinsicSixUnbalancedKMinus41 : ℝ :=
  factorTwoIntrinsicFourP45Cross41 / 2 + 169 / 5000

def factorTwoIntrinsicSixUnbalancedKMinus43 : ℝ :=
  factorTwoIntrinsicFourP45Cross43 / 2 + 253 / 5000

def factorTwoIntrinsicSixUnbalancedKMinus45 : ℝ :=
  factorTwoIntrinsicP45Alternating / 2 + 457 / 5000

/-! ## Fraction-free Schur blocks -/

def factorTwoIntrinsicSixUnbalancedEPlusDet : ℝ :=
  symmetricDeterminant
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44

def factorTwoIntrinsicSixUnbalancedEMinusDet : ℝ :=
  symmetricDeterminant
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44

private def factorTwoIntrinsicSixUnbalancedTPlusEntry
    (o u0 u2 u4 v0 v2 v4 : ℝ) : ℝ :=
  factorTwoIntrinsicSixUnbalancedEPlusDet * o -
    unbalancedThreeAdjugatePair
      factorTwoIntrinsicSixUnbalancedEPlus00
      factorTwoIntrinsicSixUnbalancedEPlus02
      factorTwoIntrinsicSixUnbalancedEPlus04
      factorTwoIntrinsicSixUnbalancedEPlus22
      factorTwoIntrinsicSixUnbalancedEPlus24
      factorTwoIntrinsicSixUnbalancedEPlus44
      u0 u2 u4 v0 v2 v4

private def factorTwoIntrinsicSixUnbalancedTMinusEntry
    (o u0 u2 u4 v0 v2 v4 : ℝ) : ℝ :=
  factorTwoIntrinsicSixUnbalancedEMinusDet * o -
    unbalancedThreeAdjugatePair
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus04
      factorTwoIntrinsicSixUnbalancedEMinus22
      factorTwoIntrinsicSixUnbalancedEMinus24
      factorTwoIntrinsicSixUnbalancedEMinus44
      u0 u2 u4 v0 v2 v4

def factorTwoIntrinsicSixUnbalancedTPlus11 : ℝ :=
  factorTwoIntrinsicSixUnbalancedTPlusEntry
    factorTwoIntrinsicSixUnbalancedOMinus11
    factorTwoIntrinsicSixUnbalancedKPlus01
    factorTwoIntrinsicSixUnbalancedKPlus21
    factorTwoIntrinsicSixUnbalancedKPlus41
    factorTwoIntrinsicSixUnbalancedKPlus01
    factorTwoIntrinsicSixUnbalancedKPlus21
    factorTwoIntrinsicSixUnbalancedKPlus41

def factorTwoIntrinsicSixUnbalancedTPlus13 : ℝ :=
  factorTwoIntrinsicSixUnbalancedTPlusEntry
    factorTwoIntrinsicSixUnbalancedOMinus13
    factorTwoIntrinsicSixUnbalancedKPlus01
    factorTwoIntrinsicSixUnbalancedKPlus21
    factorTwoIntrinsicSixUnbalancedKPlus41
    factorTwoIntrinsicSixUnbalancedKPlus03
    factorTwoIntrinsicSixUnbalancedKPlus23
    factorTwoIntrinsicSixUnbalancedKPlus43

def factorTwoIntrinsicSixUnbalancedTPlus15 : ℝ :=
  factorTwoIntrinsicSixUnbalancedTPlusEntry
    factorTwoIntrinsicSixUnbalancedOMinus15
    factorTwoIntrinsicSixUnbalancedKPlus01
    factorTwoIntrinsicSixUnbalancedKPlus21
    factorTwoIntrinsicSixUnbalancedKPlus41
    factorTwoIntrinsicSixUnbalancedKPlus05
    factorTwoIntrinsicSixUnbalancedKPlus25
    factorTwoIntrinsicSixUnbalancedKPlus45

def factorTwoIntrinsicSixUnbalancedTPlus33 : ℝ :=
  factorTwoIntrinsicSixUnbalancedTPlusEntry
    factorTwoIntrinsicSixUnbalancedOMinus33
    factorTwoIntrinsicSixUnbalancedKPlus03
    factorTwoIntrinsicSixUnbalancedKPlus23
    factorTwoIntrinsicSixUnbalancedKPlus43
    factorTwoIntrinsicSixUnbalancedKPlus03
    factorTwoIntrinsicSixUnbalancedKPlus23
    factorTwoIntrinsicSixUnbalancedKPlus43

def factorTwoIntrinsicSixUnbalancedTPlus35 : ℝ :=
  factorTwoIntrinsicSixUnbalancedTPlusEntry
    factorTwoIntrinsicSixUnbalancedOMinus35
    factorTwoIntrinsicSixUnbalancedKPlus03
    factorTwoIntrinsicSixUnbalancedKPlus23
    factorTwoIntrinsicSixUnbalancedKPlus43
    factorTwoIntrinsicSixUnbalancedKPlus05
    factorTwoIntrinsicSixUnbalancedKPlus25
    factorTwoIntrinsicSixUnbalancedKPlus45

def factorTwoIntrinsicSixUnbalancedTPlus55 : ℝ :=
  factorTwoIntrinsicSixUnbalancedTPlusEntry
    factorTwoIntrinsicSixUnbalancedOMinus55
    factorTwoIntrinsicSixUnbalancedKPlus05
    factorTwoIntrinsicSixUnbalancedKPlus25
    factorTwoIntrinsicSixUnbalancedKPlus45
    factorTwoIntrinsicSixUnbalancedKPlus05
    factorTwoIntrinsicSixUnbalancedKPlus25
    factorTwoIntrinsicSixUnbalancedKPlus45

def factorTwoIntrinsicSixUnbalancedTMinus11 : ℝ :=
  factorTwoIntrinsicSixUnbalancedTMinusEntry
    factorTwoIntrinsicSixUnbalancedOPlus11
    factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicSixUnbalancedKMinus41
    factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicSixUnbalancedKMinus41

def factorTwoIntrinsicSixUnbalancedTMinus13 : ℝ :=
  factorTwoIntrinsicSixUnbalancedTMinusEntry
    factorTwoIntrinsicSixUnbalancedOPlus13
    factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicSixUnbalancedKMinus41
    factorTwoIntrinsicSixUnbalancedKMinus03
    factorTwoIntrinsicSixUnbalancedKMinus23
    factorTwoIntrinsicSixUnbalancedKMinus43

def factorTwoIntrinsicSixUnbalancedTMinus15 : ℝ :=
  factorTwoIntrinsicSixUnbalancedTMinusEntry
    factorTwoIntrinsicSixUnbalancedOPlus15
    factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicSixUnbalancedKMinus41
    factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedKMinus45

def factorTwoIntrinsicSixUnbalancedTMinus33 : ℝ :=
  factorTwoIntrinsicSixUnbalancedTMinusEntry
    factorTwoIntrinsicSixUnbalancedOPlus33
    factorTwoIntrinsicSixUnbalancedKMinus03
    factorTwoIntrinsicSixUnbalancedKMinus23
    factorTwoIntrinsicSixUnbalancedKMinus43
    factorTwoIntrinsicSixUnbalancedKMinus03
    factorTwoIntrinsicSixUnbalancedKMinus23
    factorTwoIntrinsicSixUnbalancedKMinus43

def factorTwoIntrinsicSixUnbalancedTMinus35 : ℝ :=
  factorTwoIntrinsicSixUnbalancedTMinusEntry
    factorTwoIntrinsicSixUnbalancedOPlus35
    factorTwoIntrinsicSixUnbalancedKMinus03
    factorTwoIntrinsicSixUnbalancedKMinus23
    factorTwoIntrinsicSixUnbalancedKMinus43
    factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedKMinus45

def factorTwoIntrinsicSixUnbalancedTMinus55 : ℝ :=
  factorTwoIntrinsicSixUnbalancedTMinusEntry
    factorTwoIntrinsicSixUnbalancedOPlus55
    factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedKMinus45
    factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedKMinus45

def factorTwoIntrinsicSixUnbalancedTPlusQuadratic
    (c1 c3 c5 : ℝ) : ℝ :=
  symmetricQuadratic
    factorTwoIntrinsicSixUnbalancedTPlus11
    factorTwoIntrinsicSixUnbalancedTPlus13
    factorTwoIntrinsicSixUnbalancedTPlus15
    factorTwoIntrinsicSixUnbalancedTPlus33
    factorTwoIntrinsicSixUnbalancedTPlus35
    factorTwoIntrinsicSixUnbalancedTPlus55 c1 c3 c5

def factorTwoIntrinsicSixUnbalancedTMinusQuadratic
    (c1 c3 c5 : ℝ) : ℝ :=
  symmetricQuadratic
    factorTwoIntrinsicSixUnbalancedTMinus11
    factorTwoIntrinsicSixUnbalancedTMinus13
    factorTwoIntrinsicSixUnbalancedTMinus15
    factorTwoIntrinsicSixUnbalancedTMinus33
    factorTwoIntrinsicSixUnbalancedTMinus35
    factorTwoIntrinsicSixUnbalancedTMinus55 c1 c3 c5

theorem factorTwoIntrinsicSixUnbalancedTPlusQuadratic_eq_fractionFree
    (c1 c3 c5 : ℝ) :
    factorTwoIntrinsicSixUnbalancedTPlusQuadratic c1 c3 c5 =
      factorTwoIntrinsicSixUnbalancedEPlusDet *
          symmetricQuadratic
            factorTwoIntrinsicSixUnbalancedOMinus11
            factorTwoIntrinsicSixUnbalancedOMinus13
            factorTwoIntrinsicSixUnbalancedOMinus15
            factorTwoIntrinsicSixUnbalancedOMinus33
            factorTwoIntrinsicSixUnbalancedOMinus35
            factorTwoIntrinsicSixUnbalancedOMinus55 c1 c3 c5 -
        adjugateQuadratic
          factorTwoIntrinsicSixUnbalancedEPlus00
          factorTwoIntrinsicSixUnbalancedEPlus02
          factorTwoIntrinsicSixUnbalancedEPlus04
          factorTwoIntrinsicSixUnbalancedEPlus22
          factorTwoIntrinsicSixUnbalancedEPlus24
          factorTwoIntrinsicSixUnbalancedEPlus44
          (factorTwoIntrinsicSixUnbalancedKPlus01 * c1 +
            factorTwoIntrinsicSixUnbalancedKPlus03 * c3 +
            factorTwoIntrinsicSixUnbalancedKPlus05 * c5)
          (factorTwoIntrinsicSixUnbalancedKPlus21 * c1 +
            factorTwoIntrinsicSixUnbalancedKPlus23 * c3 +
            factorTwoIntrinsicSixUnbalancedKPlus25 * c5)
          (factorTwoIntrinsicSixUnbalancedKPlus41 * c1 +
            factorTwoIntrinsicSixUnbalancedKPlus43 * c3 +
            factorTwoIntrinsicSixUnbalancedKPlus45 * c5) := by
  unfold factorTwoIntrinsicSixUnbalancedTPlusQuadratic
    factorTwoIntrinsicSixUnbalancedTPlus11
    factorTwoIntrinsicSixUnbalancedTPlus13
    factorTwoIntrinsicSixUnbalancedTPlus15
    factorTwoIntrinsicSixUnbalancedTPlus33
    factorTwoIntrinsicSixUnbalancedTPlus35
    factorTwoIntrinsicSixUnbalancedTPlus55
    factorTwoIntrinsicSixUnbalancedTPlusEntry
  exact fractionFreeSchurQuadratic_eq
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    factorTwoIntrinsicSixUnbalancedKPlus01
    factorTwoIntrinsicSixUnbalancedKPlus03
    factorTwoIntrinsicSixUnbalancedKPlus05
    factorTwoIntrinsicSixUnbalancedKPlus21
    factorTwoIntrinsicSixUnbalancedKPlus23
    factorTwoIntrinsicSixUnbalancedKPlus25
    factorTwoIntrinsicSixUnbalancedKPlus41
    factorTwoIntrinsicSixUnbalancedKPlus43
    factorTwoIntrinsicSixUnbalancedKPlus45
    factorTwoIntrinsicSixUnbalancedOMinus11
    factorTwoIntrinsicSixUnbalancedOMinus13
    factorTwoIntrinsicSixUnbalancedOMinus15
    factorTwoIntrinsicSixUnbalancedOMinus33
    factorTwoIntrinsicSixUnbalancedOMinus35
    factorTwoIntrinsicSixUnbalancedOMinus55 c1 c3 c5

theorem factorTwoIntrinsicSixUnbalancedTMinusQuadratic_eq_fractionFree
    (c1 c3 c5 : ℝ) :
    factorTwoIntrinsicSixUnbalancedTMinusQuadratic c1 c3 c5 =
      factorTwoIntrinsicSixUnbalancedEMinusDet *
          symmetricQuadratic
            factorTwoIntrinsicSixUnbalancedOPlus11
            factorTwoIntrinsicSixUnbalancedOPlus13
            factorTwoIntrinsicSixUnbalancedOPlus15
            factorTwoIntrinsicSixUnbalancedOPlus33
            factorTwoIntrinsicSixUnbalancedOPlus35
            factorTwoIntrinsicSixUnbalancedOPlus55 c1 c3 c5 -
        adjugateQuadratic
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44
          (factorTwoIntrinsicSixUnbalancedKMinus01 * c1 +
            factorTwoIntrinsicSixUnbalancedKMinus03 * c3 +
            factorTwoIntrinsicSixUnbalancedKMinus05 * c5)
          (factorTwoIntrinsicSixUnbalancedKMinus21 * c1 +
            factorTwoIntrinsicSixUnbalancedKMinus23 * c3 +
            factorTwoIntrinsicSixUnbalancedKMinus25 * c5)
          (factorTwoIntrinsicSixUnbalancedKMinus41 * c1 +
            factorTwoIntrinsicSixUnbalancedKMinus43 * c3 +
            factorTwoIntrinsicSixUnbalancedKMinus45 * c5) := by
  unfold factorTwoIntrinsicSixUnbalancedTMinusQuadratic
    factorTwoIntrinsicSixUnbalancedTMinus11
    factorTwoIntrinsicSixUnbalancedTMinus13
    factorTwoIntrinsicSixUnbalancedTMinus15
    factorTwoIntrinsicSixUnbalancedTMinus33
    factorTwoIntrinsicSixUnbalancedTMinus35
    factorTwoIntrinsicSixUnbalancedTMinus55
    factorTwoIntrinsicSixUnbalancedTMinusEntry
  exact fractionFreeSchurQuadratic_eq
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicSixUnbalancedKMinus03
    factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicSixUnbalancedKMinus23
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedKMinus41
    factorTwoIntrinsicSixUnbalancedKMinus43
    factorTwoIntrinsicSixUnbalancedKMinus45
    factorTwoIntrinsicSixUnbalancedOPlus11
    factorTwoIntrinsicSixUnbalancedOPlus13
    factorTwoIntrinsicSixUnbalancedOPlus15
    factorTwoIntrinsicSixUnbalancedOPlus33
    factorTwoIntrinsicSixUnbalancedOPlus35
    factorTwoIntrinsicSixUnbalancedOPlus55 c1 c3 c5

def FactorTwoIntrinsicSixUnbalancedEPlusPositive : Prop :=
  0 < factorTwoIntrinsicSixUnbalancedEPlus00 ∧
    0 < leadingMinorTwo
      factorTwoIntrinsicSixUnbalancedEPlus00
      factorTwoIntrinsicSixUnbalancedEPlus02
      factorTwoIntrinsicSixUnbalancedEPlus22 ∧
    0 < factorTwoIntrinsicSixUnbalancedEPlusDet

def FactorTwoIntrinsicSixUnbalancedEMinusPositive : Prop :=
  0 < factorTwoIntrinsicSixUnbalancedEMinus00 ∧
    0 < leadingMinorTwo
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus22 ∧
    0 < factorTwoIntrinsicSixUnbalancedEMinusDet

def FactorTwoIntrinsicSixUnbalancedTPlusNonnegative : Prop :=
  ∀ c1 c3 c5 : ℝ,
    0 ≤ factorTwoIntrinsicSixUnbalancedTPlusQuadratic c1 c3 c5

def FactorTwoIntrinsicSixUnbalancedTMinusNonnegative : Prop :=
  ∀ c1 c3 c5 : ℝ,
    0 ≤ factorTwoIntrinsicSixUnbalancedTMinusQuadratic c1 c3 c5

def factorTwoIntrinsicSixUnbalancedTPlusMinor : ℝ :=
  leadingMinorTwo
    factorTwoIntrinsicSixUnbalancedTPlus11
    factorTwoIntrinsicSixUnbalancedTPlus13
    factorTwoIntrinsicSixUnbalancedTPlus33

def factorTwoIntrinsicSixUnbalancedTPlusDet : ℝ :=
  symmetricDeterminant
    factorTwoIntrinsicSixUnbalancedTPlus11
    factorTwoIntrinsicSixUnbalancedTPlus13
    factorTwoIntrinsicSixUnbalancedTPlus15
    factorTwoIntrinsicSixUnbalancedTPlus33
    factorTwoIntrinsicSixUnbalancedTPlus35
    factorTwoIntrinsicSixUnbalancedTPlus55

def factorTwoIntrinsicSixUnbalancedTMinusMinor : ℝ :=
  leadingMinorTwo
    factorTwoIntrinsicSixUnbalancedTMinus11
    factorTwoIntrinsicSixUnbalancedTMinus13
    factorTwoIntrinsicSixUnbalancedTMinus33

def factorTwoIntrinsicSixUnbalancedTMinusDet : ℝ :=
  symmetricDeterminant
    factorTwoIntrinsicSixUnbalancedTMinus11
    factorTwoIntrinsicSixUnbalancedTMinus13
    factorTwoIntrinsicSixUnbalancedTMinus15
    factorTwoIntrinsicSixUnbalancedTMinus33
    factorTwoIntrinsicSixUnbalancedTMinus35
    factorTwoIntrinsicSixUnbalancedTMinus55

/-- The three strict Sylvester gates are a scalar interface for positivity of
the positive corrected fraction-free Schur block. -/
theorem factorTwoIntrinsicSixUnbalancedTPlusNonnegative_of_sylvester
    (h11 : 0 < factorTwoIntrinsicSixUnbalancedTPlus11)
    (hMinor : 0 < factorTwoIntrinsicSixUnbalancedTPlusMinor)
    (hDet : 0 < factorTwoIntrinsicSixUnbalancedTPlusDet) :
    FactorTwoIntrinsicSixUnbalancedTPlusNonnegative := by
  intro c1 c3 c5
  unfold factorTwoIntrinsicSixUnbalancedTPlusQuadratic
  apply symmetricQuadratic_nonneg
  · exact h11
  · simpa only [factorTwoIntrinsicSixUnbalancedTPlusMinor] using hMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedTPlusDet] using hDet

/-- The three strict Sylvester gates are a scalar interface for positivity of
the negative corrected fraction-free Schur block. -/
theorem factorTwoIntrinsicSixUnbalancedTMinusNonnegative_of_sylvester
    (h11 : 0 < factorTwoIntrinsicSixUnbalancedTMinus11)
    (hMinor : 0 < factorTwoIntrinsicSixUnbalancedTMinusMinor)
    (hDet : 0 < factorTwoIntrinsicSixUnbalancedTMinusDet) :
    FactorTwoIntrinsicSixUnbalancedTMinusNonnegative := by
  intro c1 c3 c5
  unfold factorTwoIntrinsicSixUnbalancedTMinusQuadratic
  apply symmetricQuadratic_nonneg
  · exact h11
  · simpa only [factorTwoIntrinsicSixUnbalancedTMinusMinor] using hMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedTMinusDet] using hDet

/-! ## Identification with the corrected endpoint forms -/

theorem factorTwoIntrinsicSixUnbalancedStaticPlus_eq_block
    (c0 c2 c4 c1 c3 c5 : ℝ) :
    factorTwoIntrinsicSixUnbalancedStaticPlus c0 c2 c4 c1 c3 c5 =
      symmetricQuadratic
          factorTwoIntrinsicSixUnbalancedEPlus00
          factorTwoIntrinsicSixUnbalancedEPlus02
          factorTwoIntrinsicSixUnbalancedEPlus04
          factorTwoIntrinsicSixUnbalancedEPlus22
          factorTwoIntrinsicSixUnbalancedEPlus24
          factorTwoIntrinsicSixUnbalancedEPlus44 c0 c2 c4 +
        2 * (c0 *
            (factorTwoIntrinsicSixUnbalancedKPlus01 * c1 +
              factorTwoIntrinsicSixUnbalancedKPlus03 * c3 +
              factorTwoIntrinsicSixUnbalancedKPlus05 * c5) +
          c2 *
            (factorTwoIntrinsicSixUnbalancedKPlus21 * c1 +
              factorTwoIntrinsicSixUnbalancedKPlus23 * c3 +
              factorTwoIntrinsicSixUnbalancedKPlus25 * c5) +
          c4 *
            (factorTwoIntrinsicSixUnbalancedKPlus41 * c1 +
              factorTwoIntrinsicSixUnbalancedKPlus43 * c3 +
              factorTwoIntrinsicSixUnbalancedKPlus45 * c5)) +
        symmetricQuadratic
          factorTwoIntrinsicSixUnbalancedOMinus11
          factorTwoIntrinsicSixUnbalancedOMinus13
          factorTwoIntrinsicSixUnbalancedOMinus15
          factorTwoIntrinsicSixUnbalancedOMinus33
          factorTwoIntrinsicSixUnbalancedOMinus35
          factorTwoIntrinsicSixUnbalancedOMinus55 c1 c3 c5 := by
  unfold factorTwoIntrinsicSixUnbalancedStaticPlus
    factorTwoIntrinsicSixUnbalancedTransfer
    factorTwoIntrinsicSixStaticEven
    factorTwoIntrinsicSixStaticOdd
    factorTwoIntrinsicSixStaticAlternating
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    factorTwoIntrinsicSixUnbalancedOMinus11
    factorTwoIntrinsicSixUnbalancedOMinus13
    factorTwoIntrinsicSixUnbalancedOMinus15
    factorTwoIntrinsicSixUnbalancedOMinus33
    factorTwoIntrinsicSixUnbalancedOMinus35
    factorTwoIntrinsicSixUnbalancedOMinus55
    factorTwoIntrinsicSixUnbalancedKPlus01
    factorTwoIntrinsicSixUnbalancedKPlus03
    factorTwoIntrinsicSixUnbalancedKPlus05
    factorTwoIntrinsicSixUnbalancedKPlus21
    factorTwoIntrinsicSixUnbalancedKPlus23
    factorTwoIntrinsicSixUnbalancedKPlus25
    factorTwoIntrinsicSixUnbalancedKPlus41
    factorTwoIntrinsicSixUnbalancedKPlus43
    factorTwoIntrinsicSixUnbalancedKPlus45
    symmetricQuadratic
  ring

theorem factorTwoIntrinsicSixUnbalancedStaticMinus_eq_block
    (c0 c2 c4 c1 c3 c5 : ℝ) :
    factorTwoIntrinsicSixUnbalancedStaticMinus c0 c2 c4 c1 c3 c5 =
      symmetricQuadratic
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44 c0 c2 c4 +
        2 * (c0 *
            (factorTwoIntrinsicSixUnbalancedKMinus01 * c1 +
              factorTwoIntrinsicSixUnbalancedKMinus03 * c3 +
              factorTwoIntrinsicSixUnbalancedKMinus05 * c5) +
          c2 *
            (factorTwoIntrinsicSixUnbalancedKMinus21 * c1 +
              factorTwoIntrinsicSixUnbalancedKMinus23 * c3 +
              factorTwoIntrinsicSixUnbalancedKMinus25 * c5) +
          c4 *
            (factorTwoIntrinsicSixUnbalancedKMinus41 * c1 +
              factorTwoIntrinsicSixUnbalancedKMinus43 * c3 +
              factorTwoIntrinsicSixUnbalancedKMinus45 * c5)) +
        symmetricQuadratic
          factorTwoIntrinsicSixUnbalancedOPlus11
          factorTwoIntrinsicSixUnbalancedOPlus13
          factorTwoIntrinsicSixUnbalancedOPlus15
          factorTwoIntrinsicSixUnbalancedOPlus33
          factorTwoIntrinsicSixUnbalancedOPlus35
          factorTwoIntrinsicSixUnbalancedOPlus55 c1 c3 c5 := by
  unfold factorTwoIntrinsicSixUnbalancedStaticMinus
    factorTwoIntrinsicSixUnbalancedTransfer
    factorTwoIntrinsicSixStaticEven
    factorTwoIntrinsicSixStaticOdd
    factorTwoIntrinsicSixStaticAlternating
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    factorTwoIntrinsicSixUnbalancedOPlus11
    factorTwoIntrinsicSixUnbalancedOPlus13
    factorTwoIntrinsicSixUnbalancedOPlus15
    factorTwoIntrinsicSixUnbalancedOPlus33
    factorTwoIntrinsicSixUnbalancedOPlus35
    factorTwoIntrinsicSixUnbalancedOPlus55
    factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicSixUnbalancedKMinus03
    factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicSixUnbalancedKMinus23
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedKMinus41
    factorTwoIntrinsicSixUnbalancedKMinus43
    factorTwoIntrinsicSixUnbalancedKMinus45
    symmetricQuadratic
  ring

/-! ## Public endpoint reductions -/

/-- Positivity of `E+` and nonnegativity of
`det(E+) O- - K+ᵀ adj(E+) K+` close the corrected positive endpoint. -/
theorem factorTwoIntrinsicSixUnbalancedStaticPlusNonnegative_of_schur
    (hE : FactorTwoIntrinsicSixUnbalancedEPlusPositive)
    (hT : FactorTwoIntrinsicSixUnbalancedTPlusNonnegative) :
    FactorTwoIntrinsicSixUnbalancedStaticPlusNonnegative := by
  intro c0 c2 c4 c1 c3 c5
  rw [factorTwoIntrinsicSixUnbalancedStaticPlus_eq_block]
  rcases hE with ⟨he00, heMinor, heDet⟩
  apply sixBlock_nonneg_of_fractionFreeSchur
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    factorTwoIntrinsicSixUnbalancedKPlus01
    factorTwoIntrinsicSixUnbalancedKPlus03
    factorTwoIntrinsicSixUnbalancedKPlus05
    factorTwoIntrinsicSixUnbalancedKPlus21
    factorTwoIntrinsicSixUnbalancedKPlus23
    factorTwoIntrinsicSixUnbalancedKPlus25
    factorTwoIntrinsicSixUnbalancedKPlus41
    factorTwoIntrinsicSixUnbalancedKPlus43
    factorTwoIntrinsicSixUnbalancedKPlus45
    factorTwoIntrinsicSixUnbalancedOMinus11
    factorTwoIntrinsicSixUnbalancedOMinus13
    factorTwoIntrinsicSixUnbalancedOMinus15
    factorTwoIntrinsicSixUnbalancedOMinus33
    factorTwoIntrinsicSixUnbalancedOMinus35
    factorTwoIntrinsicSixUnbalancedOMinus55
    he00 heMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedEPlusDet] using heDet
  · intro d1 d3 d5
    have h := hT d1 d3 d5
    rw [factorTwoIntrinsicSixUnbalancedTPlusQuadratic_eq_fractionFree]
      at h
    simpa only [factorTwoIntrinsicSixUnbalancedEPlusDet] using h

/-- Positivity of `E-` and nonnegativity of
`det(E-) O+ - K-ᵀ adj(E-) K-` close the corrected negative endpoint. -/
theorem factorTwoIntrinsicSixUnbalancedStaticMinusNonnegative_of_schur
    (hE : FactorTwoIntrinsicSixUnbalancedEMinusPositive)
    (hT : FactorTwoIntrinsicSixUnbalancedTMinusNonnegative) :
    FactorTwoIntrinsicSixUnbalancedStaticMinusNonnegative := by
  intro c0 c2 c4 c1 c3 c5
  rw [factorTwoIntrinsicSixUnbalancedStaticMinus_eq_block]
  rcases hE with ⟨he00, heMinor, heDet⟩
  apply sixBlock_nonneg_of_fractionFreeSchur
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicSixUnbalancedKMinus03
    factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicSixUnbalancedKMinus23
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedKMinus41
    factorTwoIntrinsicSixUnbalancedKMinus43
    factorTwoIntrinsicSixUnbalancedKMinus45
    factorTwoIntrinsicSixUnbalancedOPlus11
    factorTwoIntrinsicSixUnbalancedOPlus13
    factorTwoIntrinsicSixUnbalancedOPlus15
    factorTwoIntrinsicSixUnbalancedOPlus33
    factorTwoIntrinsicSixUnbalancedOPlus35
    factorTwoIntrinsicSixUnbalancedOPlus55
    he00 heMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedEMinusDet] using heDet
  · intro d1 d3 d5
    have h := hT d1 d3 d5
    rw [factorTwoIntrinsicSixUnbalancedTMinusQuadratic_eq_fractionFree]
      at h
    simpa only [factorTwoIntrinsicSixUnbalancedEMinusDet] using h

end
