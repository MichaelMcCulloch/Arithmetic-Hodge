import Mathlib.LinearAlgebra.Matrix.Polynomial
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural

noncomputable section

open Polynomial
open YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural

/-!
# Polynomial leading determinants for the direct cutoff-nine pencil

The four odd coordinates are reflected when the projective parameter changes
sign.  Scaling those coordinates by the parameter dephases every leading
principal block: the resulting matrix is affine in `x = t^2`.  Its determinant
is therefore an honest polynomial on the nonnegative half-line.
-/

/-- Even-coordinate predicate in the direct order
`(P0,P2,P4,P1,P3,P5,P6,P8,P7)`. -/
def factorTwoIntrinsicNineDirectEvenIndex (i : Fin 9) : Prop :=
  i.val < 3 ∨ i.val = 6 ∨ i.val = 7

private theorem factorTwoIntrinsicNineDirectEndpoint_crossParity_zero
    (a : ℝ) (i j : Fin 9)
    (hij : factorTwoIntrinsicNineDirectEvenIndex i ↔
      ¬ factorTwoIntrinsicNineDirectEvenIndex j) :
    factorTwoIntrinsicNineDirectLowMatrix a 0 i j = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [factorTwoIntrinsicNineDirectEvenIndex,
      factorTwoIntrinsicNineDirectLowMatrix,
      factorTwoIntrinsicNineDirectCoordinateBilinear,
      factorTwoIntrinsicNineDirectCoordinateQuadratic,
      factorTwoIntrinsicNineDirectLowQuadratic,
      factorTwoIntrinsicNineDirectEvenQuadratic,
      factorTwoIntrinsicNineDirectOddQuadratic,
      factorTwoIntrinsicNineDirectAlternating,
      factorTwoIntrinsicNineDirectUnit,
      YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction.factorTwoIntrinsicSixStaticEven,
      YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction.factorTwoIntrinsicSixStaticOdd,
      YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction.factorTwoIntrinsicSixStaticAlternating,
      YoshidaFactorTwoPhaseIntrinsicLow.factorTwoIntrinsicOddPhaseQuadratic,
      YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural.factorTwoIntrinsicNineP678LowReserve] <;>
    ring

private theorem factorTwoIntrinsicNineDirectAlternating_sameParity_zero
    (i j : Fin 9)
    (hij : factorTwoIntrinsicNineDirectEvenIndex i ↔
      factorTwoIntrinsicNineDirectEvenIndex j) :
    (2 • (factorTwoIntrinsicNineDirectLowMatrix 0 1 -
      factorTwoIntrinsicNineDirectLowMatrix 0 0)) i j = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [factorTwoIntrinsicNineDirectEvenIndex,
      factorTwoIntrinsicNineDirectLowMatrix,
      factorTwoIntrinsicNineDirectCoordinateBilinear,
      factorTwoIntrinsicNineDirectCoordinateQuadratic,
      factorTwoIntrinsicNineDirectLowQuadratic,
      factorTwoIntrinsicNineDirectEvenQuadratic,
      factorTwoIntrinsicNineDirectOddQuadratic,
      factorTwoIntrinsicNineDirectAlternating,
      factorTwoIntrinsicNineDirectUnit,
      YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction.factorTwoIntrinsicSixStaticEven,
      YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction.factorTwoIntrinsicSixStaticOdd,
      YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction.factorTwoIntrinsicSixStaticAlternating,
      YoshidaFactorTwoPhaseIntrinsicLow.factorTwoIntrinsicOddPhaseQuadratic,
      YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural.factorTwoIntrinsicNineP678LowReserve]

/-- Leading principal prefix of a direct `Fin 9` matrix. -/
def factorTwoIntrinsicNineDirectPrefix
    (k : ℕ) (hk : k ≤ 9) (A : Matrix (Fin 9) (Fin 9) ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  A.submatrix (Fin.castLE hk) (Fin.castLE hk)

/-- The endpoint-plus coefficient of a leading projective prefix. -/
def factorTwoIntrinsicNineDirectPrefixPlus (k : ℕ) (hk : k ≤ 9) :
    Matrix (Fin k) (Fin k) ℝ :=
  factorTwoIntrinsicNineDirectPrefix k hk
    (factorTwoIntrinsicNineDirectLowMatrix 1 0)

/-- The endpoint-minus coefficient of a leading projective prefix. -/
def factorTwoIntrinsicNineDirectPrefixMinus (k : ℕ) (hk : k ≤ 9) :
    Matrix (Fin k) (Fin k) ℝ :=
  factorTwoIntrinsicNineDirectPrefix k hk
    (factorTwoIntrinsicNineDirectLowMatrix (-1) 0)

/-- The coefficient linear in the projective tangent parameter. -/
def factorTwoIntrinsicNineDirectPrefixAlternating (k : ℕ) (hk : k ≤ 9) :
    Matrix (Fin k) (Fin k) ℝ :=
  factorTwoIntrinsicNineDirectPrefix k hk
    (2 • (factorTwoIntrinsicNineDirectLowMatrix 0 1 -
      factorTwoIntrinsicNineDirectLowMatrix 0 0))

/-- Even-coordinate predicate restricted to a leading prefix. -/
def factorTwoIntrinsicNineDirectPrefixEven
    {k : ℕ} (i : Fin k) : Prop :=
  i.val < 3 ∨ i.val = 6 ∨ i.val = 7

private theorem factorTwoIntrinsicNineDirectPrefixEndpoint_crossParity_zero
    (k : ℕ) (hk : k ≤ 9) (a : ℝ) (i j : Fin k)
    (hij : factorTwoIntrinsicNineDirectPrefixEven i ↔
      ¬ factorTwoIntrinsicNineDirectPrefixEven j) :
    factorTwoIntrinsicNineDirectPrefix k hk
        (factorTwoIntrinsicNineDirectLowMatrix a 0) i j = 0 := by
  apply factorTwoIntrinsicNineDirectEndpoint_crossParity_zero
  simpa [factorTwoIntrinsicNineDirectPrefixEven,
    factorTwoIntrinsicNineDirectEvenIndex] using hij

private theorem factorTwoIntrinsicNineDirectPrefixAlternating_sameParity_zero
    (k : ℕ) (hk : k ≤ 9) (i j : Fin k)
    (hij : factorTwoIntrinsicNineDirectPrefixEven i ↔
      factorTwoIntrinsicNineDirectPrefixEven j) :
    factorTwoIntrinsicNineDirectPrefixAlternating k hk i j = 0 := by
  apply factorTwoIntrinsicNineDirectAlternating_sameParity_zero
  simpa [factorTwoIntrinsicNineDirectPrefixEven,
    factorTwoIntrinsicNineDirectEvenIndex] using hij

/-- The constant coefficient of the dephased affine prefix.  Its lower-left
cross-parity block is the alternating coefficient; its upper-right block
vanishes. -/
def factorTwoIntrinsicNineDirectDephasedConstant
    (k : ℕ) (hk : k ≤ 9) : Matrix (Fin k) (Fin k) ℝ :=
  by
    classical
    exact fun i j ↦
      if factorTwoIntrinsicNineDirectPrefixEven i ↔
          factorTwoIntrinsicNineDirectPrefixEven j then
        factorTwoIntrinsicNineDirectPrefixPlus k hk i j
      else if ¬ factorTwoIntrinsicNineDirectPrefixEven i ∧
          factorTwoIntrinsicNineDirectPrefixEven j then
        factorTwoIntrinsicNineDirectPrefixAlternating k hk i j
      else 0

/-- The linear coefficient of the dephased affine prefix.  It contains the
endpoint-minus diagonal blocks and the alternating upper-right block. -/
def factorTwoIntrinsicNineDirectDephasedLinear
    (k : ℕ) (hk : k ≤ 9) : Matrix (Fin k) (Fin k) ℝ :=
  by
    classical
    exact fun i j ↦
      if factorTwoIntrinsicNineDirectPrefixEven i ↔
          factorTwoIntrinsicNineDirectPrefixEven j then
        factorTwoIntrinsicNineDirectPrefixMinus k hk i j
      else if factorTwoIntrinsicNineDirectPrefixEven i ∧
          ¬ factorTwoIntrinsicNineDirectPrefixEven j then
        factorTwoIntrinsicNineDirectPrefixAlternating k hk i j
      else 0

/-- The real dephased prefix, affine in `x`. -/
def factorTwoIntrinsicNineDirectDephasedMatrix
    (k : ℕ) (hk : k ≤ 9) (x : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  factorTwoIntrinsicNineDirectDephasedConstant k hk +
    x • factorTwoIntrinsicNineDirectDephasedLinear k hk

/-- Leading prefix of the original projective pencil. -/
def factorTwoIntrinsicNineDirectProjectivePrefix
    (k : ℕ) (hk : k ≤ 9) (t x : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  factorTwoIntrinsicNineDirectPrefix k hk
    (factorTwoIntrinsicNineDirectProjectiveMatrix t x)

/-- Diagonal odd-coordinate scaling used in the dephasing similarity. -/
def factorTwoIntrinsicNineDirectDephasingDiagonal
    (k : ℕ) (t : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  by
    classical
    exact Matrix.diagonal fun i ↦
      if factorTwoIntrinsicNineDirectPrefixEven i then 1 else t

theorem factorTwoIntrinsicNineDirectProjectivePrefix_eq
    (k : ℕ) (hk : k ≤ 9) (t x : ℝ) :
    factorTwoIntrinsicNineDirectProjectivePrefix k hk t x =
      factorTwoIntrinsicNineDirectPrefixPlus k hk +
        x • factorTwoIntrinsicNineDirectPrefixMinus k hk +
        t • factorTwoIntrinsicNineDirectPrefixAlternating k hk := by
  ext i j
  simp only [factorTwoIntrinsicNineDirectProjectivePrefix,
    factorTwoIntrinsicNineDirectPrefix,
    factorTwoIntrinsicNineDirectProjectiveMatrix,
    factorTwoIntrinsicNineDirectPrefixPlus,
    factorTwoIntrinsicNineDirectPrefixMinus,
    factorTwoIntrinsicNineDirectPrefixAlternating,
    Matrix.submatrix_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- Exact intertwining identity.  When `x=t²`, the original projective
prefix is similar to the affine dephased prefix away from `t=0`; the identity
itself remains valid at zero. -/
theorem factorTwoIntrinsicNineDirectDephasing_intertwine
    (k : ℕ) (hk : k ≤ 9) (t x : ℝ) (hx : x = t ^ 2) :
    factorTwoIntrinsicNineDirectDephasingDiagonal k t *
        factorTwoIntrinsicNineDirectDephasedMatrix k hk x =
      factorTwoIntrinsicNineDirectProjectivePrefix k hk t x *
        factorTwoIntrinsicNineDirectDephasingDiagonal k t := by
  classical
  subst x
  rw [factorTwoIntrinsicNineDirectProjectivePrefix_eq]
  ext i j
  rw [factorTwoIntrinsicNineDirectDephasingDiagonal,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : factorTwoIntrinsicNineDirectPrefixEven i <;>
    by_cases hj : factorTwoIntrinsicNineDirectPrefixEven j
  all_goals
    simp only [factorTwoIntrinsicNineDirectDephasedMatrix,
      factorTwoIntrinsicNineDirectDephasedConstant,
      factorTwoIntrinsicNineDirectDephasedLinear,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  · simp [hi, hj,
      factorTwoIntrinsicNineDirectPrefixAlternating_sameParity_zero]
  · have hplus : factorTwoIntrinsicNineDirectPrefixPlus k hk i j = 0 := by
      exact factorTwoIntrinsicNineDirectPrefixEndpoint_crossParity_zero
        k hk 1 i j (by simp [hi, hj])
    have hminus : factorTwoIntrinsicNineDirectPrefixMinus k hk i j = 0 := by
      exact factorTwoIntrinsicNineDirectPrefixEndpoint_crossParity_zero
        k hk (-1) i j (by simp [hi, hj])
    simp [hi, hj, hplus, hminus]
    ring
  · have hplus : factorTwoIntrinsicNineDirectPrefixPlus k hk i j = 0 := by
      exact factorTwoIntrinsicNineDirectPrefixEndpoint_crossParity_zero
        k hk 1 i j (by simp [hi, hj])
    have hminus : factorTwoIntrinsicNineDirectPrefixMinus k hk i j = 0 := by
      exact factorTwoIntrinsicNineDirectPrefixEndpoint_crossParity_zero
        k hk (-1) i j (by simp [hi, hj])
    simp [hi, hj, hplus, hminus]
  · simp [hi, hj,
      factorTwoIntrinsicNineDirectPrefixAlternating_sameParity_zero]
    ring

private theorem factorTwoIntrinsicNineDirectDephasingDiagonal_det_ne_zero
    (k : ℕ) (t : ℝ) (ht : t ≠ 0) :
    (factorTwoIntrinsicNineDirectDephasingDiagonal k t).det ≠ 0 := by
  classical
  rw [factorTwoIntrinsicNineDirectDephasingDiagonal, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  by_cases heven : factorTwoIntrinsicNineDirectPrefixEven i
  · simp [heven]
  · simp [heven, ht]

private theorem factorTwoIntrinsicNineDirectDephasedConstant_det_eq_plus
    (k : ℕ) (hk : k ≤ 9) :
    (factorTwoIntrinsicNineDirectDephasedConstant k hk).det =
      (factorTwoIntrinsicNineDirectPrefixPlus k hk).det := by
  classical
  have hdephased : ∀ i, factorTwoIntrinsicNineDirectPrefixEven i →
      ∀ j, ¬ factorTwoIntrinsicNineDirectPrefixEven j →
        factorTwoIntrinsicNineDirectDephasedConstant k hk i j = 0 := by
    intro i hi j hj
    simp [factorTwoIntrinsicNineDirectDephasedConstant, hi, hj]
  have hplus : ∀ i, factorTwoIntrinsicNineDirectPrefixEven i →
      ∀ j, ¬ factorTwoIntrinsicNineDirectPrefixEven j →
        factorTwoIntrinsicNineDirectPrefixPlus k hk i j = 0 := by
    intro i hi j hj
    exact factorTwoIntrinsicNineDirectPrefixEndpoint_crossParity_zero
      k hk 1 i j (by simp [hi, hj])
  have heven : Matrix.toSquareBlockProp
      (factorTwoIntrinsicNineDirectDephasedConstant k hk)
        factorTwoIntrinsicNineDirectPrefixEven =
      Matrix.toSquareBlockProp
        (factorTwoIntrinsicNineDirectPrefixPlus k hk)
          factorTwoIntrinsicNineDirectPrefixEven := by
    ext i j
    simp [Matrix.toSquareBlockProp, Matrix.toBlock,
      factorTwoIntrinsicNineDirectDephasedConstant, i.property, j.property]
  have hodd : Matrix.toSquareBlockProp
      (factorTwoIntrinsicNineDirectDephasedConstant k hk)
        (fun i ↦ ¬ factorTwoIntrinsicNineDirectPrefixEven i) =
      Matrix.toSquareBlockProp
        (factorTwoIntrinsicNineDirectPrefixPlus k hk)
          (fun i ↦ ¬ factorTwoIntrinsicNineDirectPrefixEven i) := by
    ext i j
    simp [Matrix.toSquareBlockProp, Matrix.toBlock,
      factorTwoIntrinsicNineDirectDephasedConstant, i.property, j.property]
  calc
    (factorTwoIntrinsicNineDirectDephasedConstant k hk).det =
        (Matrix.toSquareBlockProp
            (factorTwoIntrinsicNineDirectDephasedConstant k hk)
              factorTwoIntrinsicNineDirectPrefixEven).det *
          (Matrix.toSquareBlockProp
            (factorTwoIntrinsicNineDirectDephasedConstant k hk)
              (fun i ↦ ¬ factorTwoIntrinsicNineDirectPrefixEven i)).det :=
      Matrix.twoBlockTriangular_det' _ _ hdephased
    _ = (Matrix.toSquareBlockProp
            (factorTwoIntrinsicNineDirectPrefixPlus k hk)
              factorTwoIntrinsicNineDirectPrefixEven).det *
          (Matrix.toSquareBlockProp
            (factorTwoIntrinsicNineDirectPrefixPlus k hk)
              (fun i ↦ ¬ factorTwoIntrinsicNineDirectPrefixEven i)).det := by
      rw [heven, hodd]
    _ = (factorTwoIntrinsicNineDirectPrefixPlus k hk).det :=
      (Matrix.twoBlockTriangular_det' _ _ hplus).symm

private theorem factorTwoIntrinsicNineDirectDephasedLinear_det_eq_minus
    (k : ℕ) (hk : k ≤ 9) :
    (factorTwoIntrinsicNineDirectDephasedLinear k hk).det =
      (factorTwoIntrinsicNineDirectPrefixMinus k hk).det := by
  classical
  have hdephased : ∀ i, ¬ factorTwoIntrinsicNineDirectPrefixEven i →
      ∀ j, factorTwoIntrinsicNineDirectPrefixEven j →
        factorTwoIntrinsicNineDirectDephasedLinear k hk i j = 0 := by
    intro i hi j hj
    simp [factorTwoIntrinsicNineDirectDephasedLinear, hi, hj]
  have hminus : ∀ i, ¬ factorTwoIntrinsicNineDirectPrefixEven i →
      ∀ j, factorTwoIntrinsicNineDirectPrefixEven j →
        factorTwoIntrinsicNineDirectPrefixMinus k hk i j = 0 := by
    intro i hi j hj
    exact factorTwoIntrinsicNineDirectPrefixEndpoint_crossParity_zero
      k hk (-1) i j (by simp [hi, hj])
  have heven : Matrix.toSquareBlockProp
      (factorTwoIntrinsicNineDirectDephasedLinear k hk)
        factorTwoIntrinsicNineDirectPrefixEven =
      Matrix.toSquareBlockProp
        (factorTwoIntrinsicNineDirectPrefixMinus k hk)
          factorTwoIntrinsicNineDirectPrefixEven := by
    ext i j
    simp [Matrix.toSquareBlockProp, Matrix.toBlock,
      factorTwoIntrinsicNineDirectDephasedLinear, i.property, j.property]
  have hodd : Matrix.toSquareBlockProp
      (factorTwoIntrinsicNineDirectDephasedLinear k hk)
        (fun i ↦ ¬ factorTwoIntrinsicNineDirectPrefixEven i) =
      Matrix.toSquareBlockProp
        (factorTwoIntrinsicNineDirectPrefixMinus k hk)
          (fun i ↦ ¬ factorTwoIntrinsicNineDirectPrefixEven i) := by
    ext i j
    simp [Matrix.toSquareBlockProp, Matrix.toBlock,
      factorTwoIntrinsicNineDirectDephasedLinear, i.property, j.property]
  calc
    (factorTwoIntrinsicNineDirectDephasedLinear k hk).det =
        (Matrix.toSquareBlockProp
            (factorTwoIntrinsicNineDirectDephasedLinear k hk)
              factorTwoIntrinsicNineDirectPrefixEven).det *
          (Matrix.toSquareBlockProp
            (factorTwoIntrinsicNineDirectDephasedLinear k hk)
              (fun i ↦ ¬ factorTwoIntrinsicNineDirectPrefixEven i)).det :=
      Matrix.twoBlockTriangular_det _ _ hdephased
    _ = (Matrix.toSquareBlockProp
            (factorTwoIntrinsicNineDirectPrefixMinus k hk)
              factorTwoIntrinsicNineDirectPrefixEven).det *
          (Matrix.toSquareBlockProp
            (factorTwoIntrinsicNineDirectPrefixMinus k hk)
              (fun i ↦ ¬ factorTwoIntrinsicNineDirectPrefixEven i)).det := by
      rw [heven, hodd]
    _ = (factorTwoIntrinsicNineDirectPrefixMinus k hk).det :=
      (Matrix.twoBlockTriangular_det _ _ hminus).symm

/-- The dephased affine matrix has exactly the same determinant as the
original projective prefix on `x=t²`, including the singular chart point
`t=0`. -/
theorem factorTwoIntrinsicNineDirectDephasedMatrix_det_eq_projectivePrefix
    (k : ℕ) (hk : k ≤ 9) (t x : ℝ) (hx : x = t ^ 2) :
    (factorTwoIntrinsicNineDirectDephasedMatrix k hk x).det =
      (factorTwoIntrinsicNineDirectProjectivePrefix k hk t x).det := by
  by_cases ht : t = 0
  · subst t
    have hx0 : x = 0 := by simpa using hx
    subst x
    simpa [factorTwoIntrinsicNineDirectDephasedMatrix,
      factorTwoIntrinsicNineDirectProjectivePrefix_eq] using
      factorTwoIntrinsicNineDirectDephasedConstant_det_eq_plus k hk
  · have hintertwine := congrArg Matrix.det
        (factorTwoIntrinsicNineDirectDephasing_intertwine k hk t x hx)
    simp only [Matrix.det_mul] at hintertwine
    apply mul_left_cancel₀
      (factorTwoIntrinsicNineDirectDephasingDiagonal_det_ne_zero k t ht)
    simpa only [mul_comm] using hintertwine

/-- Polynomial determinant of the affine dephased prefix. -/
def factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial
    (k : ℕ) (hk : k ≤ 9) : ℝ[X] :=
  Matrix.det
    ((X : ℝ[X]) •
        (factorTwoIntrinsicNineDirectDephasedLinear k hk).map C +
      (factorTwoIntrinsicNineDirectDephasedConstant k hk).map C)

/-- Evaluation of the determinant polynomial recovers the real dephased
determinant exactly. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_eval
    (k : ℕ) (hk : k ≤ 9) (x : ℝ) :
    (factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial k hk).eval x =
      (factorTwoIntrinsicNineDirectDephasedMatrix k hk x).det := by
  unfold factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial
  rw [Polynomial.eval, ← coe_eval₂RingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [factorTwoIntrinsicNineDirectDephasedMatrix]
  ring

/-- The prefix determinant has degree at most the prefix size, without any
Leibniz expansion. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_natDegree_le
    (k : ℕ) (hk : k ≤ 9) :
    (factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial k hk).natDegree ≤ k := by
  simpa [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial] using
    (Polynomial.natDegree_det_X_add_C_le
      (factorTwoIntrinsicNineDirectDephasedLinear k hk)
      (factorTwoIntrinsicNineDirectDephasedConstant k hk))

/-- The constant determinant coefficient is the plus-endpoint prefix
determinant. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_coeff_zero
    (k : ℕ) (hk : k ≤ 9) :
    (factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial k hk).coeff 0 =
      (factorTwoIntrinsicNineDirectPrefixPlus k hk).det := by
  rw [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial,
    Polynomial.coeff_det_X_add_C_zero,
    factorTwoIntrinsicNineDirectDephasedConstant_det_eq_plus]

/-- The degree-`k` determinant coefficient is the minus-endpoint prefix
determinant. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_coeff_top
    (k : ℕ) (hk : k ≤ 9) :
    (factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial k hk).coeff k =
      (factorTwoIntrinsicNineDirectPrefixMinus k hk).det := by
  simpa [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial] using
    (Polynomial.coeff_det_X_add_C_card
      (factorTwoIntrinsicNineDirectDephasedLinear k hk)
      (factorTwoIntrinsicNineDirectDephasedConstant k hk)).trans
        (factorTwoIntrinsicNineDirectDephasedLinear_det_eq_minus k hk)

/-! ## The three remaining leading determinant polynomials -/

/-- The seventh leading determinant polynomial. -/
def factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven : ℝ[X] :=
  factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial 7 (by omega)

/-- The eighth leading determinant polynomial. -/
def factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight : ℝ[X] :=
  factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial 8 (by omega)

/-- The complete ninth determinant polynomial. -/
def factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine : ℝ[X] :=
  factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial 9 (by omega)

theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_eval
    (t x : ℝ) (hx : x = t ^ 2) :
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.eval x =
      (factorTwoIntrinsicNineDirectProjectivePrefix 7 (by omega) t x).det := by
  rw [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven,
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_eval]
  exact factorTwoIntrinsicNineDirectDephasedMatrix_det_eq_projectivePrefix
    7 (by omega) t x hx

theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight_eval
    (t x : ℝ) (hx : x = t ^ 2) :
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight.eval x =
      (factorTwoIntrinsicNineDirectProjectivePrefix 8 (by omega) t x).det := by
  rw [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight,
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_eval]
  exact factorTwoIntrinsicNineDirectDephasedMatrix_det_eq_projectivePrefix
    8 (by omega) t x hx

theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine_eval
    (t x : ℝ) (hx : x = t ^ 2) :
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine.eval x =
      (factorTwoIntrinsicNineDirectProjectivePrefix 9 (by omega) t x).det := by
  rw [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine,
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_eval]
  exact factorTwoIntrinsicNineDirectDephasedMatrix_det_eq_projectivePrefix
    9 (by omega) t x hx

theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_natDegree_le :
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.natDegree ≤ 7 := by
  exact factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_natDegree_le
    7 (by omega)

theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight_natDegree_le :
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight.natDegree ≤ 8 := by
  exact factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_natDegree_le
    8 (by omega)

theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine_natDegree_le :
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine.natDegree ≤ 9 := by
  exact factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_natDegree_le
    9 (by omega)

/-! ## A global two-quadratic half-line cone -/

/-- A polynomial is positive on the nonnegative half-line when it is the sum
of a positive quadratic head, a shifted positive quadratic head, and a
coefficientwise nonnegative shifted tail.  Each quadratic may use either a
nonnegative linear coefficient or a strict discriminant certificate. -/
def PositiveTwoQuadraticHeadsNonnegativeTailCone (p : ℝ[X]) : Prop :=
  ∃ c0 c1 c2 d0 d1 d2 : ℝ, ∃ m : ℕ, ∃ q : ℝ[X],
    p = (C c0 + C c1 * X + C c2 * X ^ 2) +
        X ^ m * (C d0 + C d1 * X + C d2 * X ^ 2) +
        X ^ (m + 3) * q ∧
      0 < c0 ∧ 0 < c2 ∧
      (0 ≤ c1 ∨ (c1 < 0 ∧ c1 ^ 2 < 4 * c0 * c2)) ∧
      0 < d0 ∧ 0 < d2 ∧
      (0 ≤ d1 ∨ (d1 < 0 ∧ d1 ^ 2 < 4 * d0 * d2)) ∧
      NonnegativeCoefficientCone q

/-- Two square completions and a coefficientwise tail prove positivity on
the entire half-line at once. -/
theorem eval_pos_of_mem_positiveTwoQuadraticHeadsNonnegativeTailCone
    (p : ℝ[X]) (hp : PositiveTwoQuadraticHeadsNonnegativeTailCone p)
    (x : ℝ) (hx : 0 ≤ x) :
    0 < p.eval x := by
  rcases hp with
    ⟨c0, c1, c2, d0, d1, d2, m, q, rfl,
      hc0, hc2, hc1, hd0, hd2, hd1, hq⟩
  have hcCone : PositiveQuadraticHeadNonnegativeTailCone
      (C c0 + C c1 * X + C c2 * X ^ 2) := by
    refine ⟨c0, c1, c2, 0, ?_, hc0, hc2, hc1, ?_⟩
    · simp
    · intro n
      simp
  have hdCone : PositiveQuadraticHeadNonnegativeTailCone
      (C d0 + C d1 * X + C d2 * X ^ 2) := by
    refine ⟨d0, d1, d2, 0, ?_, hd0, hd2, hd1, ?_⟩
    · simp
    · intro n
      simp
  have hcEval : 0 < c0 + c1 * x + c2 * x ^ 2 := by
    simpa only [eval_add, eval_mul, eval_pow, eval_C, eval_X] using
      eval_pos_of_mem_positiveQuadraticHeadNonnegativeTailCone
        _ hcCone x hx
  have hdEval : 0 < d0 + d1 * x + d2 * x ^ 2 := by
    simpa only [eval_add, eval_mul, eval_pow, eval_C, eval_X] using
      eval_pos_of_mem_positiveQuadraticHeadNonnegativeTailCone
        _ hdCone x hx
  have hqEval : 0 ≤ q.eval x :=
    eval_nonneg_of_mem_nonnegativeCoefficientCone q hq x hx
  have hsecond : 0 ≤ x ^ m * (d0 + d1 * x + d2 * x ^ 2) :=
    mul_nonneg (pow_nonneg hx m) hdEval.le
  have htail : 0 ≤ x ^ (m + 3) * q.eval x :=
    mul_nonneg (pow_nonneg hx (m + 3)) hqEval
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg hcEval hsecond) htail

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural
