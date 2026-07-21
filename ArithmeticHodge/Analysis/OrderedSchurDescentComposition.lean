import Mathlib
import ArithmeticHodge.Analysis.MultiplicativeWeilPairwiseCellAssemblyObstruction

set_option autoImplicit false

/-!
# Ordered Schur descent: one step, its cone invariance, its composition law

This file is a **skeleton girder**, not a bridge.  It formalises the purely
linear-algebraic content of "ordered Schur descent" for a real symmetric
`3 x 3` form, in the same division-free scalar idiom as
`ThreeByThreeRankOneSchur`.  Nothing here refers to `RiemannHypothesis`, the
Bombieri/Weil form, `ζ`, or any arithmetic positivity: it is a general fact
about eliminating one coordinate of a quadratic form, and it can not encode
or assume RH.

Its purpose is to connect two objects already in the repository:

* `ThreeByThreeRankOneSchur` — the ordered pivots (Sylvester) that *certify*
  positivity of a form (the "cone" is certified from the inside);
* `MultiplicativeWeilPairwiseCellAssemblyObstruction` — the compiled proof
  that positivity of every `2`-cell restriction does **not** assemble to
  global positivity (the path kernel `[[1,-1,0],[-1,1,-1],[0,-1,1]]`).

The link is the *ordered elimination step* itself.  Three facts:

1. **One-step descent identity** (`oneStep_descent_identity`).  Eliminating the
   first coordinate with pivot `q00` writes `q00 · Q` as a leading perfect
   square plus a residual two-variable *tail form* whose entries are the
   Schur complement of the pivot.  This is the finite scalar shadow of a
   canonical-system transfer step.

2. **Cone invariance** (`descent_preserves_cone`).  When the leading pivot is
   positive, the full form is nonnegative in every direction **iff** the
   residual tail form is.  Eliminating the pivot preserves the positivity
   question *exactly* — the finite shadow of Herglotz/`Im m ≥ 0` preservation
   under Schur descent.  This is the property that a genuine local-to-global
   assembly must respect and that raw pairwise data does not.

3. **Composition / cocycle law** (`schur_composition_identity`).  The Schur
   complement of the residual tail form equals the global determinant pivot:
   eliminating in two ordered steps yields the same final residual as a single
   block elimination.  This associativity is the discrete cocycle behind
   ordered composition (and is exactly what the `3`-cell path obstruction
   shows pairwise composition lacks).

Finally the **unit test** (`pathKernel_ordered_descent_unit_test`) runs the
descent on the compiled path kernel: a positive leading pivot, a *singular*
second pivot (an indivisible interval), and a strictly negative residual tail
correctly certify indefiniteness — precisely where all three `2`-cell blocks
are positive semidefinite.  Ordered composition sees what pairwise data can
not.
-/

namespace ArithmeticHodge.Analysis.OrderedSchurDescentComposition

open ArithmeticHodge.Analysis.ThreeByThreeRankOneSchur
open ArithmeticHodge.Analysis.MultiplicativeWeilPairwiseCellAssemblyObstruction

/-!
## One ordered elimination step
-/

/-- **One-step Schur descent.**  Multiplying the symmetric `3 x 3` form by its
leading pivot `q00` splits it exactly into a leading perfect square plus a
residual two-variable *tail form* `twoCellValue` in `x1, x2`.  The tail
entries `q00 q11 - q01²`, `q00 q12 - q01 q02`, `q00 q22 - q02²` are the
(division-free) Schur complement of the pivot.  Pure algebra; proved by
`ring`. -/
theorem oneStep_descent_identity
    (q00 q01 q02 q11 q12 q22 x0 x1 x2 : ℝ) :
    q00 * symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2
      = (q00 * x0 + q01 * x1 + q02 * x2) ^ 2
        + twoCellValue (leadingMinorTwo q00 q01 q11) (q00 * q12 - q01 * q02)
            (leadingMinorTwo q00 q02 q22) x1 x2 := by
  unfold symmetricQuadratic twoCellValue leadingMinorTwo
  ring

/-!
## Cone invariance of the descent step
-/

/-- **The descent step preserves the positivity cone exactly.**  With a strictly
positive leading pivot, the full `3 x 3` form is nonnegative in every direction
iff its residual tail form is.  This is the finite scalar shadow of Herglotz
(`Im m ≥ 0`) preservation under Schur elimination — the invariance a real
local-to-global assembly must have and that pairwise positivity lacks.  The
forward direction is division-free: it evaluates the hypothesis at the
rescaled point that annihilates the leading square. -/
theorem descent_preserves_cone
    (q00 q01 q02 q11 q12 q22 : ℝ) (h00 : 0 < q00) :
    (∀ x0 x1 x2 : ℝ, 0 ≤ symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2)
      ↔ (∀ x1 x2 : ℝ,
          0 ≤ twoCellValue (leadingMinorTwo q00 q01 q11) (q00 * q12 - q01 * q02)
            (leadingMinorTwo q00 q02 q22) x1 x2) := by
  constructor
  · intro h x1 x2
    have key := oneStep_descent_identity q00 q01 q02 q11 q12 q22
        (-(q01 * x1 + q02 * x2)) (q00 * x1) (q00 * x2)
    have hsq : q00 * (-(q01 * x1 + q02 * x2)) + q01 * (q00 * x1)
        + q02 * (q00 * x2) = 0 := by ring
    rw [hsq] at key
    have hhom : twoCellValue (leadingMinorTwo q00 q01 q11) (q00 * q12 - q01 * q02)
          (leadingMinorTwo q00 q02 q22) (q00 * x1) (q00 * x2)
        = q00 ^ 2 * twoCellValue (leadingMinorTwo q00 q01 q11)
            (q00 * q12 - q01 * q02) (leadingMinorTwo q00 q02 q22) x1 x2 := by
      unfold twoCellValue; ring
    rw [show ((0 : ℝ)) ^ 2 = 0 by norm_num, zero_add, hhom] at key
    have hQ := h (-(q01 * x1 + q02 * x2)) (q00 * x1) (q00 * x2)
    have hkey2 : 0 ≤ q00 ^ 2 * twoCellValue (leadingMinorTwo q00 q01 q11)
        (q00 * q12 - q01 * q02) (leadingMinorTwo q00 q02 q22) x1 x2 := by
      rw [← key]; exact mul_nonneg h00.le hQ
    have hq'' : 0 ≤ twoCellValue (leadingMinorTwo q00 q01 q11)
        (q00 * q12 - q01 * q02) (leadingMinorTwo q00 q02 q22) x1 x2 * q00 ^ 2 := by
      rwa [mul_comm] at hkey2
    exact nonneg_of_mul_nonneg_left hq'' (pow_pos h00 2)
  · intro h x0 x1 x2
    have key := oneStep_descent_identity q00 q01 q02 q11 q12 q22 x0 x1 x2
    have hT := h x1 x2
    have hq : 0 ≤ q00 * symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 := by
      rw [key]; exact add_nonneg (sq_nonneg _) hT
    have hq' : 0 ≤ symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 * q00 := by
      rwa [mul_comm] at hq
    exact nonneg_of_mul_nonneg_left hq' h00

/-!
## The composition (cocycle) law
-/

/-- **Ordered Schur descent composes.**  The `2 x 2` Schur complement
(`leadingMinorTwo`) of the residual tail form equals the leading pivot times
the full `3 x 3` determinant: the residual-of-the-residual is the global Schur
complement.  Equivalently, eliminating coordinate `0` then coordinate `1`
gives the same final pivot as one block elimination of `{0,1}`.  This
associativity is the discrete cocycle underlying ordered composition — the
structure the `3`-cell path obstruction proves pairwise gluing lacks.  Pure
algebra; proved by `ring`. -/
theorem schur_composition_identity
    (q00 q01 q02 q11 q12 q22 : ℝ) :
    leadingMinorTwo (leadingMinorTwo q00 q01 q11) (q00 * q12 - q01 * q02)
        (leadingMinorTwo q00 q02 q22)
      = q00 * symmetricDeterminant q00 q01 q02 q11 q12 q22 := by
  unfold leadingMinorTwo symmetricDeterminant
  ring

/-!
## Unit test on the compiled path kernel

The path kernel is `q00=1, q01=-1, q02=0, q11=1, q12=-1, q22=1`, i.e. the
matrix `[[1,-1,0],[-1,1,-1],[0,-1,1]]` from
`MultiplicativeWeilPairwiseCellAssemblyObstruction`, whose every `2`-cell
restriction is positive semidefinite.
-/

/-- The path kernel's **second pivot is singular**: after the first
elimination the leading Schur minor of the residual tail vanishes.  This is
the indivisible-interval case that ordinary (invertible) Schur elimination
can not step through. -/
theorem pathKernel_second_pivot_singular :
    leadingMinorTwo (1 : ℝ) (-1) 1 = 0 := by
  unfold leadingMinorTwo; norm_num

/-- The path kernel's **residual tail form is strictly negative** at `(1,1)`,
even though the leading pivot is positive. -/
theorem pathKernel_residual_negative :
    twoCellValue (leadingMinorTwo (1 : ℝ) (-1) 1) (1 * (-1) - (-1) * 0)
        (leadingMinorTwo (1 : ℝ) 0 1) 1 1 < 0 := by
  unfold twoCellValue leadingMinorTwo; norm_num

/-- **Ordered descent certifies the path kernel indefinite.**  Through cone
invariance, the strictly negative residual tail forces the full form to fail
nonnegativity — recovering the obstruction's `pathKernel_threeCell_negative`
from the descent side. -/
theorem pathKernel_descent_certifies_indefinite :
    ¬ (∀ x0 x1 x2 : ℝ, 0 ≤ symmetricQuadratic 1 (-1) 0 1 (-1) 1 x0 x1 x2) := by
  intro h
  have hres := (descent_preserves_cone 1 (-1) 0 1 (-1) 1 one_pos).1 h 1 1
  unfold twoCellValue leadingMinorTwo at hres
  norm_num at hres

/-- **Capstone unit test.**  On the path kernel — whose three `2`-cell
restrictions are all positive semidefinite
(`exists_pairwise_nonnegative_threeCell_negative`) — one ordered Schur descent
step exhibits a positive leading pivot, a singular second pivot, and a
strictly negative residual tail, and thereby certifies that the full form is
not positive semidefinite.  Ordered composition detects the indefiniteness
that pairwise data can not. -/
theorem pathKernel_ordered_descent_unit_test :
    (0 : ℝ) < 1
      ∧ leadingMinorTwo (1 : ℝ) (-1) 1 = 0
      ∧ (∃ x1 x2 : ℝ, twoCellValue (leadingMinorTwo (1 : ℝ) (-1) 1)
          (1 * (-1) - (-1) * 0) (leadingMinorTwo (1 : ℝ) 0 1) x1 x2 < 0)
      ∧ ¬ (∀ x0 x1 x2 : ℝ, 0 ≤ symmetricQuadratic 1 (-1) 0 1 (-1) 1 x0 x1 x2) := by
  refine ⟨one_pos, pathKernel_second_pivot_singular,
    ⟨1, 1, pathKernel_residual_negative⟩, pathKernel_descent_certifies_indefinite⟩

end ArithmeticHodge.Analysis.OrderedSchurDescentComposition
