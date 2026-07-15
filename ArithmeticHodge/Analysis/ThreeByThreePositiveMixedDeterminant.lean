import ArithmeticHodge.Analysis.PositiveDefiniteMixedDeterminant
import ArithmeticHodge.Analysis.ThreeByThreeConvexPencil

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.ThreeByThreePositiveMixedDeterminant

noncomputable section

open Matrix
open PositiveDefiniteMixedDeterminant
open ThreeByThreeConvexPencil
open ThreeByThreeRankOneSchur

/-- The concrete symmetric matrix represented by the six scalar coordinates
used throughout the three-dimensional Schur API. -/
def symmetricMatrix3
    (q00 q01 q02 q11 q12 q22 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q00, q01, q02; q01, q11, q12; q02, q12, q22]

/-- The coefficient linear in the second matrix in
`det (P + X M)`. -/
def mixedDeterminantOne
    (p00 p01 p02 p11 p12 p22
      m00 m01 m02 m11 m12 m22 : ℝ) : ℝ :=
  (p11 * p22 - p12 ^ 2) * m00 +
    2 * (p02 * p12 - p01 * p22) * m01 +
    2 * (p01 * p12 - p02 * p11) * m02 +
    (p00 * p22 - p02 ^ 2) * m11 +
    2 * (p01 * p02 - p00 * p12) * m12 +
    (p00 * p11 - p01 ^ 2) * m22

private theorem symmetricMatrix3_isHermitian
    (q00 q01 q02 q11 q12 q22 : ℝ) :
    (symmetricMatrix3 q00 q01 q02 q11 q12 q22).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricMatrix3, Matrix.conjTranspose_apply]

private theorem dotProduct_mulVec_symmetricMatrix3
    (q00 q01 q02 q11 q12 q22 : ℝ) (x : Fin 3 → ℝ) :
    star x ⬝ᵥ
        (symmetricMatrix3 q00 q01 q02 q11 q12 q22 *ᵥ x) =
      symmetricQuadratic q00 q01 q02 q11 q12 q22
        (x 0) (x 1) (x 2) := by
  simp [dotProduct, mulVec, symmetricMatrix3,
    Fin.sum_univ_succ, symmetricQuadratic]
  ring

/-- Scalar Sylvester gates give positive definiteness of the corresponding
concrete `Fin 3` matrix. -/
theorem symmetricMatrix3_posDef
    (q00 q01 q02 q11 q12 q22 : ℝ)
    (h00 : 0 < q00)
    (hminor : 0 < leadingMinorTwo q00 q01 q11)
    (hdet : 0 < symmetricDeterminant
      q00 q01 q02 q11 q12 q22) :
    (symmetricMatrix3 q00 q01 q02 q11 q12 q22).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (symmetricMatrix3_isHermitian q00 q01 q02 q11 q12 q22)
  intro x hx
  rw [dotProduct_mulVec_symmetricMatrix3]
  apply symmetricQuadratic_pos
    q00 q01 q02 q11 q12 q22 h00 hminor hdet
  by_contra h
  push_neg at h
  apply hx
  funext i
  fin_cases i <;> simp_all

private theorem trace_adjugate_mul_symmetricMatrix3
    (p00 p01 p02 p11 p12 p22
      m00 m01 m02 m11 m12 m22 : ℝ) :
    Matrix.trace
        ((symmetricMatrix3 p00 p01 p02 p11 p12 p22).adjugate *
          symmetricMatrix3 m00 m01 m02 m11 m12 m22) =
      mixedDeterminantOne
        p00 p01 p02 p11 p12 p22 m00 m01 m02 m11 m12 m22 := by
  rw [show
      (symmetricMatrix3 p00 p01 p02 p11 p12 p22).adjugate =
        !![p11 * p22 - p12 ^ 2, p02 * p12 - p01 * p22,
              p01 * p12 - p02 * p11;
            p02 * p12 - p01 * p22, p00 * p22 - p02 ^ 2,
              p01 * p02 - p00 * p12;
            p01 * p12 - p02 * p11, p01 * p02 - p00 * p12,
              p00 * p11 - p01 ^ 2] by
        unfold symmetricMatrix3
        rw [Matrix.adjugate_fin_three_of]
        ext i j
        fin_cases i <;> fin_cases j <;> simp <;> ring]
  simp [Matrix.trace, symmetricMatrix3,
    Fin.sum_univ_succ, mixedDeterminantOne]
  ring

/-- The first mixed determinant of two scalar positive-definite symmetric
forms is strictly positive. -/
theorem mixedDeterminantOne_pos
    (p00 p01 p02 p11 p12 p22
      m00 m01 m02 m11 m12 m22 : ℝ)
    (hp00 : 0 < p00)
    (hpminor : 0 < leadingMinorTwo p00 p01 p11)
    (hpdet : 0 < symmetricDeterminant
      p00 p01 p02 p11 p12 p22)
    (hm00 : 0 < m00)
    (hmminor : 0 < leadingMinorTwo m00 m01 m11)
    (hmdet : 0 < symmetricDeterminant
      m00 m01 m02 m11 m12 m22) :
    0 < mixedDeterminantOne
      p00 p01 p02 p11 p12 p22 m00 m01 m02 m11 m12 m22 := by
  rw [← trace_adjugate_mul_symmetricMatrix3]
  exact trace_adjugate_mul_pos_of_posDef
    (symmetricMatrix3_posDef
      p00 p01 p02 p11 p12 p22 hp00 hpminor hpdet)
    (symmetricMatrix3_posDef
      m00 m01 m02 m11 m12 m22 hm00 hmminor hmdet)

/-- The quadratic mixed coefficient is the first mixed coefficient with the
two endpoint forms exchanged. -/
theorem mixedDeterminantTwo_pos
    (p00 p01 p02 p11 p12 p22
      m00 m01 m02 m11 m12 m22 : ℝ)
    (hp00 : 0 < p00)
    (hpminor : 0 < leadingMinorTwo p00 p01 p11)
    (hpdet : 0 < symmetricDeterminant
      p00 p01 p02 p11 p12 p22)
    (hm00 : 0 < m00)
    (hmminor : 0 < leadingMinorTwo m00 m01 m11)
    (hmdet : 0 < symmetricDeterminant
      m00 m01 m02 m11 m12 m22) :
    0 < mixedDeterminantOne
      m00 m01 m02 m11 m12 m22 p00 p01 p02 p11 p12 p22 :=
  mixedDeterminantOne_pos
    m00 m01 m02 m11 m12 m22 p00 p01 p02 p11 p12 p22
    hm00 hmminor hmdet hp00 hpminor hpdet

end

end ArithmeticHodge.Analysis.ThreeByThreePositiveMixedDeterminant
