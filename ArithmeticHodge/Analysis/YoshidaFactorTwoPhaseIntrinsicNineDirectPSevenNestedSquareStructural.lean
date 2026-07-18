import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectPSevenNestedSquareStructural

noncomputable section

open Polynomial
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveSylvesterStructural

/-!
# Nested-square certificate for the seventh direct prefix

The first prefix beyond the proved six-mode core has degree seven.  Instead
of assigning its two negative-looking coefficients to arbitrarily chosen
quadratic heads, eliminate them successively by exact square completion.
The remaining obstruction is a cubic tail with manifestly nonnegative
coefficients on the projective half-line.
-/

/-- Exact denominator-free form of the two successive square completions.
This formulation avoids divisions and remains convenient for exact scalar
enclosures. -/
theorem degreeSeven_nestedSquareCompletion_pos
    (c0 c1 c2 c3 c4 c5 c6 c7 x : ℝ)
    (hx : 0 ≤ x)
    (h0 : 0 < c0)
    (hΔ1 : 0 < 4 * c0 * c2 - c1 ^ 2)
    (hΔ2 :
      0 < (4 * c0 * c2 - c1 ^ 2) * c4 - c0 * c3 ^ 2)
    (h5 : 0 ≤ c5) (h6 : 0 ≤ c6) (h7 : 0 ≤ c7) :
    0 < c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 +
      c4 * x ^ 4 + c5 * x ^ 5 + c6 * x ^ 6 + c7 * x ^ 7 := by
  let Δ1 := 4 * c0 * c2 - c1 ^ 2
  let Δ2 := Δ1 * c4 - c0 * c3 ^ 2
  let p := c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 +
    c4 * x ^ 4 + c5 * x ^ 5 + c6 * x ^ 6 + c7 * x ^ 7
  have hΔ1' : 0 < Δ1 := by simpa only [Δ1] using hΔ1
  have hΔ2' : 0 < Δ2 := by simpa only [Δ2, Δ1] using hΔ2
  have htail : 0 ≤ c5 * x + c6 * x ^ 2 + c7 * x ^ 3 := by
    positivity
  have hidentity :
      (4 * c0 * Δ1) * p =
        Δ1 * (2 * c0 + c1 * x) ^ 2 +
          x ^ 2 * (Δ1 + 2 * c0 * c3 * x) ^ 2 +
          4 * c0 * x ^ 4 * Δ2 +
          4 * c0 * Δ1 * x ^ 4 *
            (c5 * x + c6 * x ^ 2 + c7 * x ^ 3) := by
    dsimp only [p, Δ1, Δ2]
    ring
  have hrhs :
      0 < Δ1 * (2 * c0 + c1 * x) ^ 2 +
          x ^ 2 * (Δ1 + 2 * c0 * c3 * x) ^ 2 +
          4 * c0 * x ^ 4 * Δ2 +
          4 * c0 * Δ1 * x ^ 4 *
            (c5 * x + c6 * x ^ 2 + c7 * x ^ 3) := by
    by_cases hx0 : x = 0
    · subst x
      simp only [zero_pow (by omega : 2 ≠ 0), zero_mul, mul_zero,
        add_zero]
      positivity
    · have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hmain : 0 < 4 * c0 * x ^ 4 * Δ2 := by positivity
      positivity
  have hscale : 0 ≤ 4 * c0 * Δ1 := by positivity
  have hproduct : 0 < (4 * c0 * Δ1) * p := by
    rw [hidentity]
    exact hrhs
  have hp : 0 < p :=
    pos_of_mul_pos_left (by simpa only [mul_comm] using hproduct) hscale
  simpa only [p] using hp

private abbrev pSeven : ℝ[X] :=
  factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven

/-- Six scalar gates obtained from the nested-square certificate.  They are
strict only where square completion needs an invertible pivot; the cubic
tail is allowed to be merely coefficientwise nonnegative. -/
def FactorTwoIntrinsicNineDirectPSevenNestedSquareGates : Prop :=
  0 < pSeven.coeff 0 ∧
    0 < 4 * pSeven.coeff 0 * pSeven.coeff 2 - pSeven.coeff 1 ^ 2 ∧
    0 <
      (4 * pSeven.coeff 0 * pSeven.coeff 2 - pSeven.coeff 1 ^ 2) *
          pSeven.coeff 4 -
        pSeven.coeff 0 * pSeven.coeff 3 ^ 2 ∧
    0 ≤ pSeven.coeff 5 ∧
    0 ≤ pSeven.coeff 6 ∧
    0 < pSeven.coeff 7

/-- The six nested-square gates imply strict positivity of the seventh
prefix determinant on the complete projective half-line. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_eval_pos
    (h : FactorTwoIntrinsicNineDirectPSevenNestedSquareGates)
    (x : ℝ) (hx : 0 ≤ x) :
    0 < pSeven.eval x := by
  have heval :
      pSeven.eval x =
        pSeven.coeff 0 + pSeven.coeff 1 * x +
          pSeven.coeff 2 * x ^ 2 + pSeven.coeff 3 * x ^ 3 +
          pSeven.coeff 4 * x ^ 4 + pSeven.coeff 5 * x ^ 5 +
          pSeven.coeff 6 * x ^ 6 + pSeven.coeff 7 * x ^ 7 := by
    rw [pSeven.as_sum_range_C_mul_X_pow' (n := 8)
      (lt_of_le_of_lt
        factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_natDegree_le
        (by norm_num))]
    norm_num [Finset.sum_range_succ]
  rw [heval]
  apply degreeSeven_nestedSquareCompletion_pos
  · exact hx
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.le

/-! ## Closure of the actual `P6` prefix -/

/-- The nested-square gates extend the strict six-mode projective block by
the `P6` coordinate at every finite chart parameter. -/
theorem factorTwoIntrinsicNineDirectProjectivePrefix_seven_posDef
    (h : FactorTwoIntrinsicNineDirectPSevenNestedSquareGates)
    (t : ℝ) :
    (factorTwoIntrinsicNineDirectProjectivePrefix 7 (by omega)
      t (t ^ 2)).PosDef := by
  apply posDef_fin_succ_of_leading_posDef_of_det_pos 6
  · exact factorTwoIntrinsicNineDirectProjectivePrefix_isHermitian
      7 (by omega) t (t ^ 2)
  · rw [factorTwoIntrinsicNineDirectProjectivePrefix_succ_leading]
    exact factorTwoIntrinsicNineDirectProjectivePrefix_six_posDef t
  · rw [← factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_eval
      t (t ^ 2) rfl]
    exact factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_eval_pos
      h (t ^ 2) (sq_nonneg t)

/-- Strictness of the leading coefficient closes the one omitted projective
endpoint for the `P6` prefix. -/
theorem factorTwoIntrinsicNineDirectPrefixMinus_seven_posDef
    (hTop : 0 < pSeven.coeff 7) :
    (factorTwoIntrinsicNineDirectPrefixMinus 7 (by omega)).PosDef := by
  apply posDef_fin_succ_of_leading_posDef_of_det_pos 6
  · exact factorTwoIntrinsicNineDirectPrefixMinus_isHermitian 7 (by omega)
  · rw [factorTwoIntrinsicNineDirectPrefixMinus_succ_leading]
    exact factorTwoIntrinsicNineDirectPrefixMinus_six_posDef
  · rw [← factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_coeff_top]
    simpa only [pSeven,
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven] using hTop

/-- Consequently the six nested-square gates and the omitted-endpoint gate
close the actual direct `P6` prefix on the entire phase circle. -/
theorem factorTwoIntrinsicNineDirectP6PrefixMatrix_posDef_of_nestedSquareGates
    (h : FactorTwoIntrinsicNineDirectPSevenNestedSquareGates)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (factorTwoIntrinsicNineDirectP6PrefixMatrix a b).PosDef := by
  have hTop : 0 < pSeven.coeff 7 := h.2.2.2.2.2
  by_cases ha : a = -1
  · have hb : b = 0 := by
      rw [ha] at hab
      nlinarith [sq_nonneg b]
    simpa only [ha, hb, factorTwoIntrinsicNineDirectP6PrefixMatrix,
      factorTwoIntrinsicNineDirectPrefixMinus] using
      factorTwoIntrinsicNineDirectPrefixMinus_seven_posDef hTop
  · let t := b / (1 + a)
    obtain ⟨haChart, hbChart⟩ := unitCircle_eq_projectiveChart a b hab ha
    have hmatrix :
        factorTwoIntrinsicNineDirectProjectivePrefix 7 (by omega)
            t (t ^ 2) =
          (1 + t ^ 2) • factorTwoIntrinsicNineDirectP6PrefixMatrix a b := by
      unfold factorTwoIntrinsicNineDirectProjectivePrefix
        factorTwoIntrinsicNineDirectP6PrefixMatrix
      rw [factorTwoIntrinsicNineDirectProjectiveMatrix_eq_phase t (t ^ 2) rfl,
        ← haChart, ← hbChart]
      ext i j
      rfl
    have hProjective :=
      factorTwoIntrinsicNineDirectProjectivePrefix_seven_posDef h t
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · exact factorTwoIntrinsicNineDirectP6PrefixMatrix_isHermitian a b
    · intro x hx
      have hq := hProjective.dotProduct_mulVec_pos hx
      simp only [star_trivial] at hq ⊢
      rw [hmatrix] at hq
      simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hq
      exact pos_of_mul_pos_left (by simpa only [mul_comm] using hq)
        (by nlinarith [sq_nonneg t] : 0 ≤ 1 + t ^ 2)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectPSevenNestedSquareStructural
