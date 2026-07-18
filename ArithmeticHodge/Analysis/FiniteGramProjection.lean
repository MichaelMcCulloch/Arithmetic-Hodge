import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.FiniteGramProjection

noncomputable section

/-- Coefficient embedding for subtracting a finite family of comparison
vectors from a finite family of target vectors. -/
def residualEmbedding
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (C : Matrix ι κ ℝ) : Matrix (ι ⊕ κ) ι ℝ :=
  Sum.elim (1 : Matrix ι ι ℝ) (-Cᴴ)

/-- Block multiplication identity behind the inverse-free finite Bessel
certificate. -/
theorem residualEmbedding_conjTranspose_mul_fromBlocks_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (B C : Matrix ι κ ℝ)
    (D : Matrix κ κ ℝ) :
    (residualEmbedding C)ᴴ * Matrix.fromBlocks R B Bᴴ D *
        residualEmbedding C =
      R - (B * Cᴴ + C * Bᴴ - C * D * Cᴴ) := by
  classical
  ext i j
  simp [residualEmbedding, Matrix.mul_apply, Matrix.one_apply,
    Finset.sum_mul]
  have hsum :
      (∑ x, (B i x + -∑ x_1, C i x_1 * D x_1 x) * C j x) =
        (∑ x, B i x * C j x) -
          ∑ x, (∑ x_1, C i x_1 * D x_1 x) * C j x := by
    calc
      _ = ∑ x, (B i x * C j x -
          (∑ x_1, C i x_1 * D x_1 x) * C j x) := by
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      _ = _ := by rw [Finset.sum_sub_distrib]
  rw [hsum]
  have hmul :
      (∑ x, (∑ x_1, C i x_1 * D x_1 x) * C j x) =
        ∑ x, ∑ x_1, C i x_1 * D x_1 x * C j x := by
    apply Finset.sum_congr rfl
    intro x _hx
    rw [Finset.sum_mul]
  rw [hmul]
  ring

/-- Inverse-free projection lower bound.  Any exact coefficient matrix `C`
produces a valid lower Gram; no inverse or orthonormalization of the comparison
family is required. -/
theorem residualGram_posSemidef
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (B C : Matrix ι κ ℝ)
    (D : Matrix κ κ ℝ)
    (hGram : (Matrix.fromBlocks R B Bᴴ D).PosSemidef) :
    (R - (B * Cᴴ + C * Bᴴ - C * D * Cᴴ)).PosSemidef := by
  have h := hGram.conjTranspose_mul_mul_same (residualEmbedding C)
  rwa [residualEmbedding_conjTranspose_mul_fromBlocks_mul] at h

end

end ArithmeticHodge.Analysis.FiniteGramProjection
