import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.FiniteBilinearGramProjectionStructural

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Gram matrix of a finite vector family for a bilinear form. -/
def finiteBilinearGram
    {ι : Type*} (B : LinearMap.BilinForm ℝ V) (F : ι → V) :
    Matrix ι ι ℝ := fun i j ↦ B (F i) (F j)

/-- Cross Gram between two finite vector families. -/
def finiteBilinearCrossGram
    {ι κ : Type*} (B : LinearMap.BilinForm ℝ V)
    (F : ι → V) (G : κ → V) : Matrix ι κ ℝ :=
  fun i k ↦ B (F i) (G k)

/-- Residual row obtained by contracting the comparison family with a fixed
coefficient matrix before any Gram entries are evaluated. -/
def finiteProjectionResidualRow
    {ι κ : Type*} [Fintype κ]
    (F : ι → V) (G : κ → V) (C : Matrix ι κ ℝ) (i : ι) : V :=
  F i - ∑ k, C i k • G k

/-- Completion of squares at the level of finite vector families.  In
particular, the usual matrix projection defect is exactly the Gram of the
contracted residual rows, so its trace is a sum of residual energies rather
than a table of cross moments. -/
theorem finiteBilinearGram_projectionResidualRow_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (F : ι → V) (G : κ → V) (C : Matrix ι κ ℝ) :
    finiteBilinearGram B (finiteProjectionResidualRow F G C) =
      finiteBilinearGram B F -
        (finiteBilinearCrossGram B F G * Cᴴ +
          C * (finiteBilinearCrossGram B F G)ᴴ -
          C * finiteBilinearGram B G * Cᴴ) := by
  classical
  ext i j
  simp only [finiteBilinearGram, finiteProjectionResidualRow,
    LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    map_sum, LinearMap.sum_apply, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right, Matrix.sub_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    finiteBilinearCrossGram]
  simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
    hB.eq (G _) (F _)]
  simp_rw [Finset.sum_mul]
  simp only [mul_comm, mul_left_comm]
  ring_nf

/-- The trace of a finite bilinear Gram is the sum of its diagonal energies. -/
theorem finiteBilinearGram_trace
    {ι : Type*} [Fintype ι]
    (B : LinearMap.BilinForm ℝ V) (F : ι → V) :
    (finiteBilinearGram B F).trace = ∑ i, B (F i) (F i) := by
  rfl

/-- Trace form of the contracted projection identity. -/
theorem projectionDefect_trace_eq_sum_residual_energy
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (F : ι → V) (G : κ → V) (C : Matrix ι κ ℝ) :
    (finiteBilinearGram B F -
        (finiteBilinearCrossGram B F G * Cᴴ +
          C * (finiteBilinearCrossGram B F G)ᴴ -
          C * finiteBilinearGram B G * Cᴴ)).trace =
      ∑ i, B (finiteProjectionResidualRow F G C i)
        (finiteProjectionResidualRow F G C i) := by
  rw [← finiteBilinearGram_projectionResidualRow_eq B hB F G C]
  exact finiteBilinearGram_trace B _

end

end ArithmeticHodge.Analysis.FiniteBilinearGramProjectionStructural
