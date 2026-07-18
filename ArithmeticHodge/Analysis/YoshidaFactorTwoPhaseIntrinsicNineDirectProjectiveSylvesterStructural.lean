import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveSylvesterStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectSixSchurStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural

/-!
# Three bordered Sylvester steps for the direct projective pencil

Mathlib does not expose a general leading-principal-minor criterion.  Only
three steps are needed here: the leading `Fin 6` block is already positive
definite, and positive determinants extend it successively to `Fin 7`,
`Fin 8`, and `Fin 9`.
-/

/-- A Hermitian real matrix with a positive-definite leading block and a
positive determinant is positive definite.  This is one scalar Schur step. -/
theorem posDef_fin_succ_of_leading_posDef_of_det_pos
    (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hM : M.IsHermitian)
    (hLeading :
      (M.submatrix Fin.castSucc Fin.castSucc).PosDef)
    (hdet : 0 < M.det) :
    M.PosDef := by
  let e : (Fin n ⊕ Fin 1) ≃ Fin (n + 1) := finSumFinEquiv
  let S : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
    M.submatrix e e
  let A : Matrix (Fin n) (Fin n) ℝ := S.toBlocks₁₁
  let B : Matrix (Fin n) (Fin 1) ℝ := S.toBlocks₁₂
  let D : Matrix (Fin 1) (Fin 1) ℝ := S.toBlocks₂₂
  have hS : S.IsHermitian := hM.submatrix e
  have hAeq : A = M.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    rfl
  have hA : A.PosDef := by
    rw [hAeq]
    exact hLeading
  have hBlocks : S = Matrix.fromBlocks A B Bᴴ D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · simpa only [A, B, D, Matrix.fromBlocks_apply₂₁,
        Matrix.conjTranspose_apply, star_trivial, Matrix.toBlocks₁₂,
        Matrix.of_apply] using (hS.apply (Sum.inr i) (Sum.inl j)).symm
    · rfl
  letI := hA.isUnit.invertible
  let K : Matrix (Fin 1) (Fin 1) ℝ := D - Bᴴ * A⁻¹ * B
  have hSdet : 0 < S.det := by
    simpa only [S, Matrix.det_submatrix_equiv_self] using hdet
  have hdetFactor : S.det = A.det * K.det := by
    rw [hBlocks, Matrix.det_fromBlocks₁₁]
    simp only [K, Matrix.invOf_eq_nonsing_inv]
  have hKdet : 0 < K.det := by
    nlinarith [hA.det_pos]
  have hKentry : 0 < K 0 0 := by
    rw [Matrix.det_fin_one] at hKdet
    exact hKdet
  have hK : K.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.conjTranspose_apply]
    · intro x hx
      have hx0 : x 0 ≠ 0 := by
        intro hzero
        apply hx
        funext i
        fin_cases i
        exact hzero
      simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_succ,
        Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      nlinarith [sq_pos_of_ne_zero hx0]
  have hSposSemidef : S.PosSemidef := by
    rw [hBlocks]
    exact (Matrix.PosDef.fromBlocks₁₁ B D hA).mpr hK.posSemidef
  have hMposSemidef : M.PosSemidef := by
    exact (Matrix.posSemidef_submatrix_equiv e).mp hSposSemidef
  apply (hMposSemidef.posDef_iff_isUnit).mpr
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr hdet.ne'

/-! ## Exact leading-block identifications -/

theorem factorTwoIntrinsicNineDirectProjectiveMatrix_isHermitian
    (t x : ℝ) :
    (factorTwoIntrinsicNineDirectProjectiveMatrix t x).IsHermitian := by
  have h10 : (factorTwoIntrinsicNineDirectLowMatrix 1 0).IsSymm :=
    factorTwoIntrinsicNineDirectLowMatrix_transpose 1 0
  have hm10 : (factorTwoIntrinsicNineDirectLowMatrix (-1) 0).IsSymm :=
    factorTwoIntrinsicNineDirectLowMatrix_transpose (-1) 0
  have h01 : (factorTwoIntrinsicNineDirectLowMatrix 0 1).IsSymm :=
    factorTwoIntrinsicNineDirectLowMatrix_transpose 0 1
  have h00 : (factorTwoIntrinsicNineDirectLowMatrix 0 0).IsSymm :=
    factorTwoIntrinsicNineDirectLowMatrix_transpose 0 0
  have hsymm : (factorTwoIntrinsicNineDirectProjectiveMatrix t x).IsSymm := by
    unfold factorTwoIntrinsicNineDirectProjectiveMatrix
    exact (h10.add (hm10.smul x)).add ((h01.sub h00).smul (2 * t))
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using hsymm

theorem factorTwoIntrinsicNineDirectProjectivePrefix_isHermitian
    (k : ℕ) (hk : k ≤ 9) (t x : ℝ) :
    (factorTwoIntrinsicNineDirectProjectivePrefix k hk t x).IsHermitian := by
  exact (factorTwoIntrinsicNineDirectProjectiveMatrix_isHermitian t x).submatrix _

theorem factorTwoIntrinsicNineDirectPrefix_succ_leading
    (k : ℕ) (hk : k + 1 ≤ 9) (A : Matrix (Fin 9) (Fin 9) ℝ) :
    (factorTwoIntrinsicNineDirectPrefix (k + 1) hk A).submatrix
        Fin.castSucc Fin.castSucc =
      factorTwoIntrinsicNineDirectPrefix k (by omega) A := by
  ext i j
  rfl

theorem factorTwoIntrinsicNineDirectProjectivePrefix_succ_leading
    (k : ℕ) (hk : k + 1 ≤ 9) (t x : ℝ) :
    (factorTwoIntrinsicNineDirectProjectivePrefix (k + 1) hk t x).submatrix
        Fin.castSucc Fin.castSucc =
      factorTwoIntrinsicNineDirectProjectivePrefix k (by omega) t x := by
  exact factorTwoIntrinsicNineDirectPrefix_succ_leading k hk _

theorem factorTwoIntrinsicNineDirectPrefix_six_eq_core
    (a b : ℝ) :
    factorTwoIntrinsicNineDirectPrefix 6 (by omega)
        (factorTwoIntrinsicNineDirectLowMatrix a b) =
      factorTwoIntrinsicNineDirectCoreMatrix a b := by
  ext i j
  rfl

theorem factorTwoIntrinsicNineDirectProjectivePrefix_six_eq_core
    (t x : ℝ) (hx : x = t ^ 2) :
    factorTwoIntrinsicNineDirectProjectivePrefix 6 (by omega) t x =
      (1 + x) • factorTwoIntrinsicNineDirectCoreMatrix
        ((1 - x) / (1 + x)) (2 * t / (1 + x)) := by
  unfold factorTwoIntrinsicNineDirectProjectivePrefix
  rw [factorTwoIntrinsicNineDirectProjectiveMatrix_eq_phase t x hx]
  change (1 + x) •
      factorTwoIntrinsicNineDirectPrefix 6 (by omega)
        (factorTwoIntrinsicNineDirectLowMatrix
          ((1 - x) / (1 + x)) (2 * t / (1 + x))) = _
  rw [factorTwoIntrinsicNineDirectPrefix_six_eq_core]

theorem factorTwoIntrinsicNineDirectProjectivePrefix_six_posDef
    (t : ℝ) :
    (factorTwoIntrinsicNineDirectProjectivePrefix 6 (by omega)
      t (t ^ 2)).PosDef := by
  have hden : 0 < 1 + t ^ 2 := by positivity
  have hcircle :
      ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 +
          (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
    field_simp [hden.ne']
    ring
  rw [factorTwoIntrinsicNineDirectProjectivePrefix_six_eq_core t (t ^ 2) rfl]
  exact (factorTwoIntrinsicNineDirectCoreMatrix_posDef
    ((1 - t ^ 2) / (1 + t ^ 2))
    (2 * t / (1 + t ^ 2)) hcircle.le).smul hden

/-! ## The three determinant gates -/

/-- Positivity of the three dephased determinant polynomials extends the
strict six-mode block to the complete projective `Fin 9` prefix. -/
theorem factorTwoIntrinsicNineDirectProjectivePrefix_nine_posDef_of_eval_pos
    (hSeven : ∀ x : ℝ, 0 ≤ x →
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.eval x)
    (hEight : ∀ x : ℝ, 0 ≤ x →
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight.eval x)
    (hNine : ∀ x : ℝ, 0 ≤ x →
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine.eval x)
    (t : ℝ) :
    (factorTwoIntrinsicNineDirectProjectivePrefix 9 (by omega)
      t (t ^ 2)).PosDef := by
  have hSix := factorTwoIntrinsicNineDirectProjectivePrefix_six_posDef t
  have hSevenDet : 0 <
      (factorTwoIntrinsicNineDirectProjectivePrefix 7 (by omega)
        t (t ^ 2)).det := by
    rw [← factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_eval
      t (t ^ 2) rfl]
    exact hSeven (t ^ 2) (sq_nonneg t)
  have hSevenPosDef :
      (factorTwoIntrinsicNineDirectProjectivePrefix 7 (by omega)
        t (t ^ 2)).PosDef := by
    apply posDef_fin_succ_of_leading_posDef_of_det_pos 6
    · exact factorTwoIntrinsicNineDirectProjectivePrefix_isHermitian
        7 (by omega) t (t ^ 2)
    · rw [factorTwoIntrinsicNineDirectProjectivePrefix_succ_leading]
      exact hSix
    · exact hSevenDet
  have hEightDet : 0 <
      (factorTwoIntrinsicNineDirectProjectivePrefix 8 (by omega)
        t (t ^ 2)).det := by
    rw [← factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight_eval
      t (t ^ 2) rfl]
    exact hEight (t ^ 2) (sq_nonneg t)
  have hEightPosDef :
      (factorTwoIntrinsicNineDirectProjectivePrefix 8 (by omega)
        t (t ^ 2)).PosDef := by
    apply posDef_fin_succ_of_leading_posDef_of_det_pos 7
    · exact factorTwoIntrinsicNineDirectProjectivePrefix_isHermitian
        8 (by omega) t (t ^ 2)
    · rw [factorTwoIntrinsicNineDirectProjectivePrefix_succ_leading]
      exact hSevenPosDef
    · exact hEightDet
  have hNineDet : 0 <
      (factorTwoIntrinsicNineDirectProjectivePrefix 9 (by omega)
        t (t ^ 2)).det := by
    rw [← factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine_eval
      t (t ^ 2) rfl]
    exact hNine (t ^ 2) (sq_nonneg t)
  apply posDef_fin_succ_of_leading_posDef_of_det_pos 8
  · exact factorTwoIntrinsicNineDirectProjectivePrefix_isHermitian
      9 (by omega) t (t ^ 2)
  · rw [factorTwoIntrinsicNineDirectProjectivePrefix_succ_leading]
    exact hEightPosDef
  · exact hNineDet

theorem factorTwoIntrinsicNineDirectProjectivePrefix_nine_eq_matrix
    (t x : ℝ) :
    factorTwoIntrinsicNineDirectProjectivePrefix 9 (by omega) t x =
      factorTwoIntrinsicNineDirectProjectiveMatrix t x := by
  ext i j
  rfl

theorem factorTwoIntrinsicNineDirectProjectiveMatrix_posDef_of_eval_pos
    (hSeven : ∀ x : ℝ, 0 ≤ x →
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.eval x)
    (hEight : ∀ x : ℝ, 0 ≤ x →
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight.eval x)
    (hNine : ∀ x : ℝ, 0 ≤ x →
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine.eval x)
    (t : ℝ) :
    (factorTwoIntrinsicNineDirectProjectiveMatrix t (t ^ 2)).PosDef := by
  rw [← factorTwoIntrinsicNineDirectProjectivePrefix_nine_eq_matrix]
  exact factorTwoIntrinsicNineDirectProjectivePrefix_nine_posDef_of_eval_pos
    hSeven hEight hNine t

theorem factorTwoIntrinsicNineDirectProjectiveMatrix_quadratic
    (t x : ℝ) (c : Fin 9 → ℝ) (hx : x = t ^ 2) :
    c ⬝ᵥ (factorTwoIntrinsicNineDirectProjectiveMatrix t x *ᵥ c) =
      factorTwoIntrinsicNineDirectProjectiveQuadratic t x c := by
  rw [factorTwoIntrinsicNineDirectProjectiveMatrix_eq_phase t x hx,
    factorTwoIntrinsicNineDirectProjectiveQuadratic_eq_phase t x c hx]
  simp only [smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [factorTwoIntrinsicNineDirectLowMatrix_quadratic]

theorem factorTwoIntrinsicNineDirectProjectiveQuadratic_nonneg_of_eval_pos
    (hSeven : ∀ x : ℝ, 0 ≤ x →
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.eval x)
    (hEight : ∀ x : ℝ, 0 ≤ x →
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight.eval x)
    (hNine : ∀ x : ℝ, 0 ≤ x →
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine.eval x)
    (t : ℝ) (c : Fin 9 → ℝ) :
    0 ≤ factorTwoIntrinsicNineDirectProjectiveQuadratic t (t ^ 2) c := by
  have hmatrix := factorTwoIntrinsicNineDirectProjectiveMatrix_posDef_of_eval_pos
    hSeven hEight hNine t
  have hnonneg := hmatrix.posSemidef.dotProduct_mulVec_nonneg c
  simp only [star_trivial] at hnonneg
  rw [factorTwoIntrinsicNineDirectProjectiveMatrix_quadratic
    t (t ^ 2) c rfl] at hnonneg
  exact hnonneg

/-! ## The omitted projective endpoint -/

theorem factorTwoIntrinsicNineDirectPrefixMinus_isHermitian
    (k : ℕ) (hk : k ≤ 9) :
    (factorTwoIntrinsicNineDirectPrefixMinus k hk).IsHermitian := by
  have hfull :
      (factorTwoIntrinsicNineDirectLowMatrix (-1) 0).IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using
      factorTwoIntrinsicNineDirectLowMatrix_transpose (-1) 0
  exact hfull.submatrix _

theorem factorTwoIntrinsicNineDirectPrefixMinus_succ_leading
    (k : ℕ) (hk : k + 1 ≤ 9) :
    (factorTwoIntrinsicNineDirectPrefixMinus (k + 1) hk).submatrix
        Fin.castSucc Fin.castSucc =
      factorTwoIntrinsicNineDirectPrefixMinus k (by omega) := by
  exact factorTwoIntrinsicNineDirectPrefix_succ_leading k hk _

theorem factorTwoIntrinsicNineDirectPrefixMinus_six_posDef :
    (factorTwoIntrinsicNineDirectPrefixMinus 6 (by omega)).PosDef := by
  rw [factorTwoIntrinsicNineDirectPrefixMinus,
    factorTwoIntrinsicNineDirectPrefix_six_eq_core]
  exact factorTwoIntrinsicNineDirectCoreMatrix_posDef (-1) 0 (by norm_num)

theorem factorTwoIntrinsicNineDirectPrefixMinus_nine_eq_matrix :
    factorTwoIntrinsicNineDirectPrefixMinus 9 (by omega) =
      factorTwoIntrinsicNineDirectLowMatrix (-1) 0 := by
  ext i j
  rfl

/-- Strict top coefficients of `p₇,p₈,p₉` are exactly the three
minus-endpoint leading determinants and hence close the omitted chart point. -/
theorem factorTwoIntrinsicNineDirectLowMatrix_minus_posDef_of_top_coeff_pos
    (hSevenTop : 0 <
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 7)
    (hEightTop : 0 <
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight.coeff 8)
    (hNineTop : 0 <
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine.coeff 9) :
    (factorTwoIntrinsicNineDirectLowMatrix (-1) 0).PosDef := by
  have hSix := factorTwoIntrinsicNineDirectPrefixMinus_six_posDef
  have hSevenDet :
      0 < (factorTwoIntrinsicNineDirectPrefixMinus 7 (by omega)).det := by
    rw [← factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_coeff_top]
    simpa [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven] using
      hSevenTop
  have hSevenPosDef :
      (factorTwoIntrinsicNineDirectPrefixMinus 7 (by omega)).PosDef := by
    apply posDef_fin_succ_of_leading_posDef_of_det_pos 6
    · exact factorTwoIntrinsicNineDirectPrefixMinus_isHermitian 7 (by omega)
    · rw [factorTwoIntrinsicNineDirectPrefixMinus_succ_leading]
      exact hSix
    · exact hSevenDet
  have hEightDet :
      0 < (factorTwoIntrinsicNineDirectPrefixMinus 8 (by omega)).det := by
    rw [← factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_coeff_top]
    simpa [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight] using
      hEightTop
  have hEightPosDef :
      (factorTwoIntrinsicNineDirectPrefixMinus 8 (by omega)).PosDef := by
    apply posDef_fin_succ_of_leading_posDef_of_det_pos 7
    · exact factorTwoIntrinsicNineDirectPrefixMinus_isHermitian 8 (by omega)
    · rw [factorTwoIntrinsicNineDirectPrefixMinus_succ_leading]
      exact hSevenPosDef
    · exact hEightDet
  have hNineDet :
      0 < (factorTwoIntrinsicNineDirectPrefixMinus 9 (by omega)).det := by
    rw [← factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_coeff_top]
    simpa [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine] using
      hNineTop
  rw [← factorTwoIntrinsicNineDirectPrefixMinus_nine_eq_matrix]
  apply posDef_fin_succ_of_leading_posDef_of_det_pos 8
  · exact factorTwoIntrinsicNineDirectPrefixMinus_isHermitian 9 (by omega)
  · rw [factorTwoIntrinsicNineDirectPrefixMinus_succ_leading]
    exact hEightPosDef
  · exact hNineDet

/-! ## Complete structural handoff -/

/-- The three global determinant gates and their three top coefficients imply
the direct cutoff-nine matrix on the whole phase circle. -/
theorem factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_determinant_gates
    (hSeven : ∀ x : ℝ, 0 ≤ x →
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.eval x)
    (hEight : ∀ x : ℝ, 0 ≤ x →
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight.eval x)
    (hNine : ∀ x : ℝ, 0 ≤ x →
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine.eval x)
    (hSevenTop : 0 <
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 7)
    (hEightTop : 0 <
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight.coeff 8)
    (hNineTop : 0 <
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine.coeff 9)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (factorTwoIntrinsicNineDirectLowMatrix a b).PosSemidef := by
  apply factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_projective
    (factorTwoIntrinsicNineDirectLowMatrix_minus_posDef_of_top_coeff_pos
      hSevenTop hEightTop hNineTop).posSemidef
  · intro t c
    exact factorTwoIntrinsicNineDirectProjectiveQuadratic_nonneg_of_eval_pos
      hSeven hEight hNine t c
  · exact hab

/-- Concrete cone interface for the remaining analytic work: two quadratic
heads for `p₇` and `p₉`, one quadratic head for `p₈`, coefficientwise
tails, and the three strict endpoint coefficients. -/
theorem factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_polynomial_cones
    (hSeven : PositiveTwoQuadraticHeadsNonnegativeTailCone
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven)
    (hEight : PositiveQuadraticHeadNonnegativeTailCone
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight)
    (hNine : PositiveTwoQuadraticHeadsNonnegativeTailCone
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine)
    (hSevenTop : 0 <
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 7)
    (hEightTop : 0 <
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight.coeff 8)
    (hNineTop : 0 <
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine.coeff 9)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (factorTwoIntrinsicNineDirectLowMatrix a b).PosSemidef := by
  apply factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_determinant_gates
  · intro x hx
    exact eval_pos_of_mem_positiveTwoQuadraticHeadsNonnegativeTailCone
      _ hSeven x hx
  · intro x hx
    exact eval_pos_of_mem_positiveQuadraticHeadNonnegativeTailCone
      _ hEight x hx
  · intro x hx
    exact eval_pos_of_mem_positiveTwoQuadraticHeadsNonnegativeTailCone
      _ hNine x hx
  · exact hSevenTop
  · exact hEightTop
  · exact hNineTop
  · exact hab

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveSylvesterStructural
