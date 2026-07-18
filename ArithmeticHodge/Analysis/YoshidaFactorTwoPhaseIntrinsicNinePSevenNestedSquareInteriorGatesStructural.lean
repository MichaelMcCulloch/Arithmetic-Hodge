import ArithmeticHodge.Analysis.ThreeByThreePositiveMixedDeterminant
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectPSevenNestedSquareStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveCoefficientGateStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveFractionFreeSchurStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveMixedRowCoefficientsStructural

set_option autoImplicit false

open Matrix Polynomial

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNinePSevenNestedSquareInteriorGatesStructural

noncomputable section

open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeConvexPencil
open ThreeByThreeRankOneSchur
open AffineDeterminantRowSubsetStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveFractionFreeSchurStructural

/-!
# The interior nested-square frontier for the seventh direct prefix

The endpoint determinants are deliberately not assumed here.  The first
reduction removes the opaque `Fin 7` determinant completely: its polynomial
is the single fraction-free Schur numerator obtained by bordering the strict
six-mode core with `P6`.
-/

private abbrev pSeven : ℝ[X] :=
  factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven

/-- The scalar fraction-free Schur numerator for the `P6` border. -/
def factorTwoIntrinsicNineDirectPSevenSchurNumerator : ℝ[X] :=
  factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrix
    1 (by omega) 0 0

/-- The seventh determinant polynomial is exactly one scalar bordered-Schur
numerator; no determinant expansion remains. -/
theorem factorTwoIntrinsicNineDirectPSeven_eq_schurNumerator :
    pSeven = factorTwoIntrinsicNineDirectPSevenSchurNumerator := by
  have h :=
    factorTwoIntrinsicNineDirectFractionFreeSchurPolynomialMatrixOne_det
  rw [Matrix.det_fin_one] at h
  exact h.symm

/-- Every coefficient of the seventh determinant is therefore a coefficient
of the scalar bordered-Schur numerator. -/
theorem factorTwoIntrinsicNineDirectPSeven_coeff_eq_schurNumerator_coeff
    (j : ℕ) :
    pSeven.coeff j = factorTwoIntrinsicNineDirectPSevenSchurNumerator.coeff j := by
  rw [factorTwoIntrinsicNineDirectPSeven_eq_schurNumerator]

/-! ## The two discriminants as one exact Loewner gate -/

/-- The tridiagonal coefficient form whose two nontrivial Sylvester pivots
are exactly the two nested-square discriminants (up to the harmless factor
`4`). -/
def factorTwoIntrinsicNineDirectPSevenHeadMatrix :
    Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (pSeven.coeff 0) (pSeven.coeff 1 / 2) 0
    (pSeven.coeff 2) (pSeven.coeff 3 / 2) (pSeven.coeff 4)

theorem factorTwoIntrinsicNineDirectPSevenHead_leadingMinorTwo :
    4 * leadingMinorTwo
        (pSeven.coeff 0) (pSeven.coeff 1 / 2) (pSeven.coeff 2) =
      4 * pSeven.coeff 0 * pSeven.coeff 2 - pSeven.coeff 1 ^ 2 := by
  unfold leadingMinorTwo
  ring

theorem factorTwoIntrinsicNineDirectPSevenHead_symmetricDeterminant :
    4 * symmetricDeterminant
        (pSeven.coeff 0) (pSeven.coeff 1 / 2) 0
        (pSeven.coeff 2) (pSeven.coeff 3 / 2) (pSeven.coeff 4) =
      (4 * pSeven.coeff 0 * pSeven.coeff 2 - pSeven.coeff 1 ^ 2) *
          pSeven.coeff 4 -
        pSeven.coeff 0 * pSeven.coeff 3 ^ 2 := by
  unfold symmetricDeterminant
  ring

/-- The endpoint pivot and the two interior discriminants imply positivity
of the single tridiagonal coefficient form. -/
theorem factorTwoIntrinsicNineDirectPSevenHeadMatrix_posDef
    (h0 : 0 < pSeven.coeff 0)
    (hΔ1 : 0 <
      4 * pSeven.coeff 0 * pSeven.coeff 2 - pSeven.coeff 1 ^ 2)
    (hΔ2 : 0 <
      (4 * pSeven.coeff 0 * pSeven.coeff 2 - pSeven.coeff 1 ^ 2) *
          pSeven.coeff 4 - pSeven.coeff 0 * pSeven.coeff 3 ^ 2) :
    factorTwoIntrinsicNineDirectPSevenHeadMatrix.PosDef := by
  apply symmetricMatrix3_posDef
  · exact h0
  · rw [← factorTwoIntrinsicNineDirectPSevenHead_leadingMinorTwo] at hΔ1
    nlinarith
  · rw [← factorTwoIntrinsicNineDirectPSevenHead_symmetricDeterminant] at hΔ2
    nlinarith

/-- Conversely, positivity of the coefficient form recovers the endpoint
pivot and both genuine interior discriminants. -/
theorem factorTwoIntrinsicNineDirectPSevenHeadMatrix_posDef_iff :
    factorTwoIntrinsicNineDirectPSevenHeadMatrix.PosDef ↔
      0 < pSeven.coeff 0 ∧
      0 < 4 * pSeven.coeff 0 * pSeven.coeff 2 - pSeven.coeff 1 ^ 2 ∧
      0 <
        (4 * pSeven.coeff 0 * pSeven.coeff 2 - pSeven.coeff 1 ^ 2) *
            pSeven.coeff 4 - pSeven.coeff 0 * pSeven.coeff 3 ^ 2 := by
  constructor
  · intro h
    have hq : ∀ x0 x1 x2 : ℝ,
        x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 →
          0 < symmetricQuadratic
            (pSeven.coeff 0) (pSeven.coeff 1 / 2) 0
            (pSeven.coeff 2) (pSeven.coeff 3 / 2) (pSeven.coeff 4)
            x0 x1 x2 := by
      intro x0 x1 x2 hx
      let x : Fin 3 → ℝ := ![x0, x1, x2]
      have hx' : x ≠ 0 := by
        intro hzero
        have h0 := congrFun hzero 0
        have h1 := congrFun hzero 1
        have h2 := congrFun hzero 2
        rcases hx with hx0 | hx1 | hx2
        · exact hx0 (by simpa [x] using h0)
        · exact hx1 (by simpa [x] using h1)
        · exact hx2 (by simpa [x] using h2)
      have hpos := h.dotProduct_mulVec_pos hx'
      have hid :
          star x ⬝ᵥ
              (factorTwoIntrinsicNineDirectPSevenHeadMatrix *ᵥ x) =
            symmetricQuadratic
              (pSeven.coeff 0) (pSeven.coeff 1 / 2) 0
              (pSeven.coeff 2) (pSeven.coeff 3 / 2) (pSeven.coeff 4)
              x0 x1 x2 := by
        simp [x, factorTwoIntrinsicNineDirectPSevenHeadMatrix,
          symmetricMatrix3, symmetricQuadratic, dotProduct, mulVec,
          Fin.sum_univ_succ]
        ring
      rw [hid] at hpos
      exact hpos
    obtain ⟨h0, hminor, hdet⟩ :=
      leadingMinors_pos_of_symmetricQuadratic_pos
        (pSeven.coeff 0) (pSeven.coeff 1 / 2) 0
        (pSeven.coeff 2) (pSeven.coeff 3 / 2) (pSeven.coeff 4) hq
    refine ⟨h0, ?_, ?_⟩
    · rw [← factorTwoIntrinsicNineDirectPSevenHead_leadingMinorTwo]
      exact mul_pos (by norm_num) hminor
    · rw [← factorTwoIntrinsicNineDirectPSevenHead_symmetricDeterminant]
      exact mul_pos (by norm_num) hdet
  · rintro ⟨h0, hΔ1, hΔ2⟩
    exact factorTwoIntrinsicNineDirectPSevenHeadMatrix_posDef h0 hΔ1 hΔ2

/-! ## A one-trace formula for the reversed tail coefficient -/

/-- The coefficient linear in `B` in an arbitrary affine determinant is the
adjugate trace.  This ring identity does not require either endpoint matrix
to be invertible or positive definite. -/
theorem coeff_one_det_X_smul_add_C_eq_trace_adjugate
    {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]
    (A B : Matrix n n R) :
    (Matrix.det
        ((X : R[X]) • B.map C + A.map C)).coeff 1 =
      Matrix.trace (A.adjugate * B) := by
  classical
  rw [coeff_det_X_smul_add_C_eq_sum_mixedRows_card,
    Finset.powersetCard_one, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Finset.piecewise_singleton]
  change (∑ j : n, (A.updateRow j (B j)).det) = _
  have hrow (j : n) :
      (A.updateRow j (B j)).det =
        ∑ i : n, A.adjugate i j * B j i := by
    rw [← Matrix.cramer_transpose_apply A (B j) j]
    have hb : B j = ∑ i : n,
        (B j i) • (Pi.single i (1 : R) : n → R) := by
      refine (pi_eq_sum_univ (B j)).trans ?_
      congr with i
      simp [Pi.single_apply, eq_comm]
    conv_lhs =>
      rw [hb, map_sum]
    simp_rw [map_smul]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    change B j i * A.adjugate i j = A.adjugate i j * B j i
    exact mul_comm _ _
  simp_rw [hrow]
  change (∑ j : n, ∑ i : n, A.adjugate i j * B j i) =
    ∑ i : n, ∑ j : n, A.adjugate i j * B j i
  exact Finset.sum_comm

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNinePSevenNestedSquareInteriorGatesStructural
