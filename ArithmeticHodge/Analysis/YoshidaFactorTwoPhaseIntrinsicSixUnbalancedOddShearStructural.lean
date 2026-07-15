import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedOddShearStructural

noncomputable section

open ThreeByThreeRankOneSchur

/-!
# Determinant-one shears for the odd Schur block

The corrected endpoint arguments use only unit upper-triangular changes of
the odd basis.  This file records the invariant identities once, separately
from all analytic estimates.  In particular, the final `3 x 3` determinant
is reduced to a `2 x 2` leading minor and one bordered square.
-/

/-- Subtracting `r` times the first basis vector from the second preserves
the leading `2 x 2` determinant. -/
theorem leadingMinorTwo_eq_shear
    (a b c r : ℝ) :
    leadingMinorTwo a b c =
      a * (c - 2 * r * b + r ^ 2 * a) - (b - r * a) ^ 2 := by
  unfold leadingMinorTwo
  ring

/-- A positive diagonal pair whose squared cross term is smaller than their
product has positive determinant. -/
theorem leadingMinorTwo_pos_of_shear
    (a p q : ℝ)
    (ha : 0 < a) (hq : 0 < q) (hp : p ^ 2 < a * q) :
    0 < a * q - p ^ 2 := by
  have hprod : 0 < a * q := mul_pos ha hq
  nlinarith

/-- The full symmetric determinant is invariant when the second basis
vector is replaced by `v₂ - r v₁`. -/
theorem symmetricDeterminant_eq_first_shear
    (a b u c v w r : ℝ) :
    symmetricDeterminant a b u c v w =
      symmetricDeterminant
        a (b - r * a) u
        (c - 2 * r * b + r ^ 2 * a) (v - r * u) w := by
  unfold symmetricDeterminant
  ring

/-- After the first shear, replacing the last basis vector by
`v₃ + alpha v₂ - beta v₁` preserves the determinant. -/
theorem symmetricDeterminant_eq_bordered_shear
    (a p u q v w alpha beta : ℝ) :
    symmetricDeterminant a p u q v w =
      symmetricDeterminant
        a p (u + alpha * p - beta * a) q
        (v + alpha * q - beta * p)
        (w + 2 * alpha * v - 2 * beta * u + alpha ^ 2 * q -
          2 * alpha * beta * p + beta ^ 2 * a) := by
  unfold symmetricDeterminant
  ring

/-- Fraction-free bordered completion of a symmetric `3 x 3` determinant.
It is the scalar Schur identity with no division by the first pivot. -/
theorem first_mul_symmetricDeterminant_eq_bordered
    (a p u q v w : ℝ) :
    a * symmetricDeterminant a p u q v w =
      (a * q - p ^ 2) * (a * w - u ^ 2) -
        (a * v - p * u) ^ 2 := by
  unfold symmetricDeterminant
  ring

/-- Positivity criterion supplied directly by the bordered identity. -/
theorem symmetricDeterminant_pos_of_bordered
    (a p u q v w : ℝ)
    (ha : 0 < a)
    (hgap :
      (a * v - p * u) ^ 2 <
        (a * q - p ^ 2) * (a * w - u ^ 2)) :
    0 < symmetricDeterminant a p u q v w := by
  have hscaled : 0 < a * symmetricDeterminant a p u q v w := by
    rw [first_mul_symmetricDeterminant_eq_bordered]
    linarith
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedOddShearStructural
