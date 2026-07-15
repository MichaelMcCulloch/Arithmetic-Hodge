import ArithmeticHodge.Analysis.ThreeByThreePositiveMixedDeterminant

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.ThreeByThreePositiveMixedDiscriminant

noncomputable section

open Matrix
open Polynomial
open ThreeByThreePositiveMixedDeterminant
open scoped ComplexOrder MatrixOrder

/-!
# Positivity of the fully mixed three-dimensional determinant

The first mixed determinant is quadratic in its first form.  Its cross term
is the fully polarized determinant of three forms.  This file proves that
cross term positive for three positive-definite real symmetric matrices.
The argument is invariant: congruence reduces one form to the identity, and
the identity case is the sum of the three positive two-coordinate pairings.
-/

/-- The determinant polynomial of the affine matrix pencil `A + X B`. -/
def determinantPencil
    (A B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ[X] :=
  (A.map (Polynomial.C : ℝ →+* ℝ[X]) +
    (X : ℝ[X]) • B.map (Polynomial.C : ℝ →+* ℝ[X])).det

/-- The coefficient linear in `B` in `det (A + X B)`. -/
def matrixMixedDeterminantOne
    (A B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  B 0 0 * A 1 1 * A 2 2 + A 0 0 * B 1 1 * A 2 2 +
    A 0 0 * A 1 1 * B 2 2 -
    (B 0 0 * A 1 2 * A 2 1 + A 0 0 * B 1 2 * A 2 1 +
      A 0 0 * A 1 2 * B 2 1) -
    (B 0 1 * A 1 0 * A 2 2 + A 0 1 * B 1 0 * A 2 2 +
      A 0 1 * A 1 0 * B 2 2) +
    (B 0 1 * A 1 2 * A 2 0 + A 0 1 * B 1 2 * A 2 0 +
      A 0 1 * A 1 2 * B 2 0) +
    (B 0 2 * A 1 0 * A 2 1 + A 0 2 * B 1 0 * A 2 1 +
      A 0 2 * A 1 0 * B 2 1) -
    (B 0 2 * A 1 1 * A 2 0 + A 0 2 * B 1 1 * A 2 0 +
      A 0 2 * A 1 1 * B 2 0)

private theorem determinantPencil_expansion
    (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    determinantPencil A B =
      C A.det + C (matrixMixedDeterminantOne A B) * X +
        C (matrixMixedDeterminantOne B A) * X ^ 2 + C B.det * X ^ 3 := by
  unfold determinantPencil matrixMixedDeterminantOne
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.map_apply,
    smul_apply, smul_eq_mul]
  simp only [map_add, map_sub, map_mul]
  ring

theorem matrixMixedDeterminantOne_eq_coefficient
    (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixMixedDeterminantOne A B = (determinantPencil A B).coeff 1 := by
  rw [determinantPencil_expansion]
  simp

theorem matrixMixedDeterminantOne_eq_trace_adjugate
    (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixMixedDeterminantOne A B = Matrix.trace (A.adjugate * B) := by
  unfold matrixMixedDeterminantOne
  have hadj : A.adjugate =
      !![A 1 1 * A 2 2 - A 1 2 * A 2 1,
          A 0 2 * A 2 1 - A 0 1 * A 2 2,
          A 0 1 * A 1 2 - A 0 2 * A 1 1;
        A 1 2 * A 2 0 - A 1 0 * A 2 2,
          A 0 0 * A 2 2 - A 0 2 * A 2 0,
          A 0 2 * A 1 0 - A 0 0 * A 1 2;
        A 1 0 * A 2 1 - A 1 1 * A 2 0,
          A 0 1 * A 2 0 - A 0 0 * A 2 1,
          A 0 0 * A 1 1 - A 0 1 * A 1 0] := by
    rw [show A =
        !![A 0 0, A 0 1, A 0 2;
          A 1 0, A 1 1, A 1 2;
          A 2 0, A 2 1, A 2 2] by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl]
    rw [Matrix.adjugate_fin_three_of]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [hadj]
  simp [Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  ring

theorem matrixMixedDeterminantOne_pos
    {A B : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    0 < matrixMixedDeterminantOne A B := by
  rw [matrixMixedDeterminantOne_eq_trace_adjugate]
  exact PositiveDefiniteMixedDeterminant.trace_adjugate_mul_pos_of_posDef
    hA hB

/-- The invariant matrix coefficient agrees with the scalar-coordinate
coefficient used by the three-dimensional Schur API. -/
theorem matrixMixedDeterminantOne_symmetricMatrix3
    (p00 p01 p02 p11 p12 p22
      m00 m01 m02 m11 m12 m22 : ℝ) :
    matrixMixedDeterminantOne
        (symmetricMatrix3 p00 p01 p02 p11 p12 p22)
        (symmetricMatrix3 m00 m01 m02 m11 m12 m22) =
      mixedDeterminantOne
        p00 p01 p02 p11 p12 p22 m00 m01 m02 m11 m12 m22 := by
  unfold matrixMixedDeterminantOne symmetricMatrix3 mixedDeterminantOne
  simp
  ring

/-- The cross term obtained by polarizing the first two slots. -/
def matrixMixedDiscriminant
    (A B D : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  matrixMixedDeterminantOne (A + B) D -
    matrixMixedDeterminantOne A D - matrixMixedDeterminantOne B D

/-- Simultaneous congruence of both entries of a pencil. -/
def matrixCongruence
    (T A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  T.transpose * A * T

private theorem determinantPencil_congruence
    (T A B : Matrix (Fin 3) (Fin 3) ℝ) :
    determinantPencil (matrixCongruence T A) (matrixCongruence T B) =
      C (T.det ^ 2) * determinantPencil A B := by
  have hmatrix :
      (matrixCongruence T A).map (Polynomial.C : ℝ →+* ℝ[X]) +
          (X : ℝ[X]) •
            (matrixCongruence T B).map (Polynomial.C : ℝ →+* ℝ[X]) =
        (T.map (Polynomial.C : ℝ →+* ℝ[X])).transpose *
          (A.map (Polynomial.C : ℝ →+* ℝ[X]) +
            (X : ℝ[X]) • B.map (Polynomial.C : ℝ →+* ℝ[X])) *
          T.map (Polynomial.C : ℝ →+* ℝ[X]) := by
    have htranspose :
        T.transpose.map (Polynomial.C : ℝ →+* ℝ[X]) =
          (T.map (Polynomial.C : ℝ →+* ℝ[X])).transpose := by
      ext i j
      simp
    simp only [matrixCongruence, Matrix.map_mul, htranspose]
    rw [Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  unfold determinantPencil
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hdet :
      (T.map (Polynomial.C : ℝ →+* ℝ[X])).det = C T.det := by
    symm
    exact (Polynomial.C : ℝ →+* ℝ[X]).map_det T
  rw [hdet]
  simp only [map_pow]
  ring

theorem matrixMixedDeterminantOne_congruence
    (T A B : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixMixedDeterminantOne (matrixCongruence T A)
        (matrixCongruence T B) =
      T.det ^ 2 * matrixMixedDeterminantOne A B := by
  rw [matrixMixedDeterminantOne_eq_coefficient,
    determinantPencil_congruence,
    Polynomial.coeff_C_mul]
  rw [← matrixMixedDeterminantOne_eq_coefficient]

theorem matrixMixedDiscriminant_congruence
    (T A B D : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixMixedDiscriminant (matrixCongruence T A)
        (matrixCongruence T B) (matrixCongruence T D) =
      T.det ^ 2 * matrixMixedDiscriminant A B D := by
  unfold matrixMixedDiscriminant
  rw [show matrixCongruence T A + matrixCongruence T B =
      matrixCongruence T (A + B) by
    unfold matrixCongruence
    simp only [Matrix.mul_add, Matrix.add_mul]]
  rw [matrixMixedDeterminantOne_congruence,
    matrixMixedDeterminantOne_congruence,
    matrixMixedDeterminantOne_congruence]
  ring

private theorem matrixMixedDeterminantOne_identity_formula
    (B : Matrix (Fin 3) (Fin 3) ℝ) :
    matrixMixedDeterminantOne 1 B =
      B 0 0 + B 1 1 + B 2 2 := by
  unfold matrixMixedDeterminantOne
  simp

private theorem matrixMixedDiscriminant_identity_formula
    (B D : Matrix (Fin 3) (Fin 3) ℝ)
    (hB : B.IsHermitian) (hD : D.IsHermitian) :
    matrixMixedDiscriminant 1 B D =
      (B 0 0 * D 1 1 + B 1 1 * D 0 0 -
          2 * B 0 1 * D 0 1) +
      (B 0 0 * D 2 2 + B 2 2 * D 0 0 -
          2 * B 0 2 * D 0 2) +
      (B 1 1 * D 2 2 + B 2 2 * D 1 1 -
          2 * B 1 2 * D 1 2) := by
  unfold matrixMixedDiscriminant matrixMixedDeterminantOne
  have hB10 : B 1 0 = B 0 1 := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hB 0) 1
  have hB20 : B 2 0 = B 0 2 := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hB 0) 2
  have hB21 : B 2 1 = B 1 2 := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hB 1) 2
  have hD10 : D 1 0 = D 0 1 := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hD 0) 1
  have hD20 : D 2 0 = D 0 2 := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hD 0) 2
  have hD21 : D 2 1 = D 1 2 := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hD 1) 2
  simp
  rw [hB10, hB20, hB21, hD10, hD20, hD21]
  ring

private theorem posDef_principalMinor_zero_one
    {B : Matrix (Fin 3) (Fin 3) ℝ} (hB : B.PosDef) :
    0 < B 0 0 * B 1 1 - B 0 1 ^ 2 := by
  let x : Fin 3 → ℝ := ![B 0 1, -B 0 0, 0]
  have h00 : 0 < B 0 0 := hB.diag_pos
  have hx : x ≠ 0 := by
    intro hx
    have hx1 := congrFun hx 1
    simp [x] at hx1
    linarith
  have hq := hB.dotProduct_mulVec_pos hx
  have hB10 : B 1 0 = B 0 1 := by
    simpa [Matrix.conjTranspose_apply] using
      congrFun (congrFun hB.isHermitian 0) 1
  simp [x, dotProduct, mulVec, Fin.sum_univ_succ] at hq
  rw [hB10] at hq
  nlinarith

private theorem posDef_principalMinor_zero_two
    {B : Matrix (Fin 3) (Fin 3) ℝ} (hB : B.PosDef) :
    0 < B 0 0 * B 2 2 - B 0 2 ^ 2 := by
  let x : Fin 3 → ℝ := ![B 0 2, 0, -B 0 0]
  have h00 : 0 < B 0 0 := hB.diag_pos
  have hx : x ≠ 0 := by
    intro hx
    have hx2 := congrFun hx 2
    simp [x] at hx2
    linarith
  have hq := hB.dotProduct_mulVec_pos hx
  have hB20 : B 2 0 = B 0 2 := by
    simpa [Matrix.conjTranspose_apply] using
      congrFun (congrFun hB.isHermitian 0) 2
  simp [x, dotProduct, mulVec, Fin.sum_univ_succ] at hq
  rw [hB20] at hq
  nlinarith

private theorem posDef_principalMinor_one_two
    {B : Matrix (Fin 3) (Fin 3) ℝ} (hB : B.PosDef) :
    0 < B 1 1 * B 2 2 - B 1 2 ^ 2 := by
  let x : Fin 3 → ℝ := ![0, B 1 2, -B 1 1]
  have h11 : 0 < B 1 1 := hB.diag_pos
  have hx : x ≠ 0 := by
    intro hx
    have hx2 := congrFun hx 2
    simp [x] at hx2
    linarith
  have hq := hB.dotProduct_mulVec_pos hx
  have hB21 : B 2 1 = B 1 2 := by
    simpa [Matrix.conjTranspose_apply] using
      congrFun (congrFun hB.isHermitian 1) 2
  simp [x, dotProduct, mulVec, Fin.sum_univ_succ] at hq
  rw [hB21] at hq
  nlinarith

private theorem positive_pairing_of_positive_principalMinors
    {a d b c f e : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hc : 0 < c) (hf : 0 < f)
    (hab : 0 < a * d - b ^ 2) (hce : 0 < c * f - e ^ 2) :
    0 < a * f + d * c - 2 * b * e := by
  have had : 0 < a * d := mul_pos ha hd
  have hcf : 0 < c * f := mul_pos hc hf
  have hab' : b ^ 2 < a * d := by linarith
  have hce' : e ^ 2 < c * f := by linarith
  have hprod : b ^ 2 * e ^ 2 < (a * d) * (c * f) := by
    calc
      b ^ 2 * e ^ 2 ≤ (a * d) * e ^ 2 :=
        mul_le_mul_of_nonneg_right hab'.le (sq_nonneg e)
      _ < (a * d) * (c * f) := mul_lt_mul_of_pos_left hce' had
  by_cases hbe : b * e ≤ 0
  · nlinarith [mul_pos (mul_pos ha hf) (mul_pos hd hc)]
  · have hbePos : 0 < b * e := lt_of_not_ge hbe
    have hfactor :
        0 < (a * f + d * c - 2 * (b * e)) *
          (a * f + d * c + 2 * (b * e)) := by
      nlinarith [sq_nonneg (a * f - d * c)]
    have hright : 0 < a * f + d * c + 2 * (b * e) := by
      positivity
    rcases (mul_pos_iff.mp hfactor) with h | h
    · nlinarith [h.1]
    · linarith [h.2, hright]

private theorem matrixMixedDiscriminant_identity_pos
    {B D : Matrix (Fin 3) (Fin 3) ℝ}
    (hB : B.PosDef) (hD : D.PosDef) :
    0 < matrixMixedDiscriminant 1 B D := by
  rw [matrixMixedDiscriminant_identity_formula B D
    hB.isHermitian hD.isHermitian]
  have h01 := positive_pairing_of_positive_principalMinors
    (hB.diag_pos (i := 0)) (hB.diag_pos (i := 1))
    (hD.diag_pos (i := 0)) (hD.diag_pos (i := 1))
    (posDef_principalMinor_zero_one hB)
    (posDef_principalMinor_zero_one hD)
  have h02 := positive_pairing_of_positive_principalMinors
    (hB.diag_pos (i := 0)) (hB.diag_pos (i := 2))
    (hD.diag_pos (i := 0)) (hD.diag_pos (i := 2))
    (posDef_principalMinor_zero_two hB)
    (posDef_principalMinor_zero_two hD)
  have h12 := positive_pairing_of_positive_principalMinors
    (hB.diag_pos (i := 1)) (hB.diag_pos (i := 2))
    (hD.diag_pos (i := 1)) (hD.diag_pos (i := 2))
    (posDef_principalMinor_one_two hB)
    (posDef_principalMinor_one_two hD)
  linarith

private theorem matrixCongruence_posDef
    {T A : Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IsUnit T) (hA : A.PosDef) :
    (matrixCongruence T A).PosDef := by
  have hInjective : Function.Injective T.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hT
  have h := hA.conjTranspose_mul_mul_same hInjective
  have htranspose : Tᴴ = T.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [htranspose] at h
  simpa only [matrixCongruence] using h

/-- The fully polarized determinant of three positive-definite real
three-dimensional forms is strictly positive. -/
theorem matrixMixedDiscriminant_pos
    {A B D : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hD : D.PosDef) :
    0 < matrixMixedDiscriminant A B D := by
  have hfac : ∃ K : Matrix (Fin 3) (Fin 3) ℝ,
      IsUnit K ∧ A = star K * K :=
    (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self (a := A)).mp
      hA.isStrictlyPositive
  obtain ⟨K, hKunit, hAK⟩ := hfac
  rw [Matrix.star_eq_conjTranspose] at hAK
  have hKstar : Kᴴ = K.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [hKstar] at hAK
  let T : Matrix (Fin 3) (Fin 3) ℝ := K⁻¹
  have hKdet : IsUnit K.det := K.isUnit_iff_isUnit_det.mp hKunit
  have hTunit : IsUnit T := by
    dsimp only [T]
    exact Matrix.isUnit_nonsing_inv_iff.mpr hKunit
  have hnormalize : matrixCongruence T A = 1 := by
    rw [hAK]
    unfold matrixCongruence
    have hleft : T.transpose * K.transpose = (K * T).transpose := by
      rw [Matrix.transpose_mul]
    calc
      T.transpose * (K.transpose * K) * T =
          (T.transpose * K.transpose) * (K * T) := by
        noncomm_ring
      _ = (K * T).transpose * (K * T) := by rw [hleft]
      _ = 1 := by
        dsimp only [T]
        rw [K.mul_nonsing_inv hKdet]
        simp
  have hB' : (matrixCongruence T B).PosDef :=
    matrixCongruence_posDef hTunit hB
  have hD' : (matrixCongruence T D).PosDef :=
    matrixCongruence_posDef hTunit hD
  have hnormalized :
      0 < matrixMixedDiscriminant (matrixCongruence T A)
        (matrixCongruence T B) (matrixCongruence T D) := by
    rw [hnormalize]
    exact matrixMixedDiscriminant_identity_pos hB' hD'
  rw [matrixMixedDiscriminant_congruence] at hnormalized
  have hTdet : IsUnit T.det := T.isUnit_iff_isUnit_det.mp hTunit
  have hTsq : 0 < T.det ^ 2 := sq_pos_of_ne_zero hTdet.ne_zero
  rcases (mul_pos_iff.mp hnormalized) with h | h
  · exact h.2
  · linarith [h.1, hTsq]

/-- Adding positive-definite forms in either slot strictly increases the
first mixed determinant.  This is the quantitative Loewner step used by the
endpoint pencil estimates. -/
theorem matrixMixedDeterminantOne_add_add_gt
    {A E B F : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A.PosDef) (hE : E.PosDef)
    (hB : B.PosDef) (hF : F.PosDef) :
    matrixMixedDeterminantOne A B <
      matrixMixedDeterminantOne (A + E) (B + F) := by
  have hlinear :
      matrixMixedDeterminantOne (A + E) (B + F) =
        matrixMixedDeterminantOne (A + E) B +
          matrixMixedDeterminantOne (A + E) F := by
    unfold matrixMixedDeterminantOne
    simp only [Matrix.add_apply]
    ring
  have hpolar :
      matrixMixedDeterminantOne (A + E) B =
        matrixMixedDeterminantOne A B +
          matrixMixedDeterminantOne E B +
          matrixMixedDiscriminant A E B := by
    unfold matrixMixedDiscriminant
    ring
  have hEB : 0 < matrixMixedDeterminantOne E B :=
    matrixMixedDeterminantOne_pos hE hB
  have hcross : 0 < matrixMixedDiscriminant A E B :=
    matrixMixedDiscriminant_pos hA hE hB
  have hsumF : 0 < matrixMixedDeterminantOne (A + E) F :=
    matrixMixedDeterminantOne_pos (hA.add hE) hF
  rw [hlinear, hpolar]
  linarith

end

end ArithmeticHodge.Analysis.ThreeByThreePositiveMixedDiscriminant
