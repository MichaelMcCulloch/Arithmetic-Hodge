import ArithmeticHodge.Analysis.ThreeByThreeRankOneSchur

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.MultiplicativeWeilPairwiseCellAssemblyObstruction

open ThreeByThreeRankOneSchur

/-!
# Pairwise cell positivity does not assemble globally

An independent two-cell contraction certifies a `2 x 2` principal block.
Before using such estimates in a logarithmic-window argument one needs a
genuine compatibility theorem: positivity of every pair is not enough to
make the complete cell matrix positive semidefinite.

The exact three-cell path below is the minimal obstruction.  Every one of its
three two-cell restrictions is nonnegative, but the vector `(1,1,1)` has
negative global quadratic value.  Thus a sound Bombieri cell assembly must
retain a higher Schur condition, an operator contraction, or some additional
structure of the actual long-range kernel.
-/

/-- The real quadratic of a symmetric two-cell block. -/
def twoCellValue (q00 q01 q11 x0 x1 : ℝ) : ℝ :=
  q00 * x0 ^ 2 + 2 * q01 * x0 * x1 + q11 * x1 ^ 2

/-- The first adjacent block of the path kernel is a square. -/
theorem pathKernel_firstPair_nonnegative (x0 x1 : ℝ) :
    0 ≤ twoCellValue 1 (-1) 1 x0 x1 := by
  unfold twoCellValue
  nlinarith [sq_nonneg (x0 - x1)]

/-- The second adjacent block of the path kernel is a square. -/
theorem pathKernel_secondPair_nonnegative (x1 x2 : ℝ) :
    0 ≤ twoCellValue 1 (-1) 1 x1 x2 := by
  exact pathKernel_firstPair_nonnegative x1 x2

/-- The nonadjacent two-cell block is the identity. -/
theorem pathKernel_outerPair_nonnegative (x0 x2 : ℝ) :
    0 ≤ twoCellValue 1 0 1 x0 x2 := by
  unfold twoCellValue
  nlinarith [sq_nonneg x0, sq_nonneg x2]

/-- Nevertheless, the complete three-cell path is negative on `(1,1,1)`. -/
theorem pathKernel_threeCell_negative :
    symmetricQuadratic 1 (-1) 0 1 (-1) 1 1 1 1 < 0 := by
  norm_num [symmetricQuadratic]

/-- Exact obstruction to any local-to-global rule using only pairwise
two-cell nonnegativity. -/
theorem exists_pairwise_nonnegative_threeCell_negative :
    ∃ q00 q01 q02 q11 q12 q22 : ℝ,
      (∀ x0 x1, 0 ≤ twoCellValue q00 q01 q11 x0 x1) ∧
      (∀ x0 x2, 0 ≤ twoCellValue q00 q02 q22 x0 x2) ∧
      (∀ x1 x2, 0 ≤ twoCellValue q11 q12 q22 x1 x2) ∧
      ∃ x0 x1 x2,
        symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 < 0 := by
  refine ⟨1, -1, 0, 1, -1, 1, ?_, ?_, ?_, 1, 1, 1, ?_⟩
  · exact pathKernel_firstPair_nonnegative
  · exact pathKernel_outerPair_nonnegative
  · exact pathKernel_secondPair_nonnegative
  · exact pathKernel_threeCell_negative

end ArithmeticHodge.Analysis.MultiplicativeWeilPairwiseCellAssemblyObstruction
