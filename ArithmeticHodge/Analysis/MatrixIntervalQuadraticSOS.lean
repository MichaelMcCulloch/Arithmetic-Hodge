import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.MatrixIntervalQuadraticSOS

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-!
# A matrix sum-of-squares certificate on `[-1,1]`

A symmetric matrix quadratic `H(a)` is positive definite on the closed
interval once it has an identity

`H(a) = P(a)ᴴ Q P(a) + (1 - a²) R`,

where `Q` is positive definite, `R` is positive semidefinite, and `P(a)` is
the full-column-rank affine lift `x ↦ (x, a x)`.  This is the matrix-valued
Markov--Lukacs certificate needed for a structural phase-disk proof; it uses
one fixed Gram and no subdivision of the phase interval.
-/

/-- Rectangular affine lift whose action on a vector is `(x, a x)`. -/
def affineLiftMatrix (a : ℝ) : Matrix (n ⊕ n) n ℝ
  | Sum.inl i, j => if i = j then 1 else 0
  | Sum.inr i, j => if i = j then a else 0

@[simp]
theorem affineLiftMatrix_mulVec_inl
    (a : ℝ) (x : n → ℝ) (i : n) :
    (affineLiftMatrix a *ᵥ x) (Sum.inl i) = x i := by
  simp [affineLiftMatrix, Matrix.mulVec, dotProduct]

@[simp]
theorem affineLiftMatrix_mulVec_inr
    (a : ℝ) (x : n → ℝ) (i : n) :
    (affineLiftMatrix a *ᵥ x) (Sum.inr i) = a * x i := by
  simp [affineLiftMatrix, Matrix.mulVec, dotProduct]

/-- The affine lift has full column rank because its first block is the
identity, independently of the phase parameter. -/
theorem affineLiftMatrix_mulVec_injective (a : ℝ) :
    Function.Injective (affineLiftMatrix (n := n) a).mulVec := by
  intro x y hxy
  funext i
  have hi := congrFun hxy (Sum.inl i)
  simpa using hi

/-- A fixed positive affine-lift Gram plus a positive interval reserve makes
the represented matrix positive definite at every `a` with `a² ≤ 1`. -/
theorem posDef_of_intervalQuadratic_sos
    (Q : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (R H : Matrix n n ℝ) (a : ℝ)
    (hQ : Q.PosDef) (hR : R.PosSemidef)
    (ha : a ^ 2 ≤ 1)
    (hH : H =
      (affineLiftMatrix (n := n) a)ᴴ * Q *
          affineLiftMatrix (n := n) a +
        (1 - a ^ 2) • R) :
    H.PosDef := by
  rw [hH]
  have hGram :
      ((affineLiftMatrix (n := n) a)ᴴ * Q *
        affineLiftMatrix (n := n) a).PosDef :=
    hQ.conjTranspose_mul_mul_same (affineLiftMatrix_mulVec_injective a)
  have hReserve : ((1 - a ^ 2) • R).PosSemidef :=
    hR.smul (sub_nonneg.mpr ha)
  exact hGram.add_posSemidef hReserve

end

end ArithmeticHodge.Analysis.MatrixIntervalQuadraticSOS
