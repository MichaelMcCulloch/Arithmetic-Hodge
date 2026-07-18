import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowUnbalancedStaticStructural

set_option autoImplicit false
set_option maxRecDepth 100000

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowUnbalancedStaticReserveStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
open YoshidaFactorTwoPhaseConcreteCleanOddMatrix
open YoshidaFactorTwoPhaseConcreteLowDiskSchur
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
open YoshidaFactorTwoPhaseConcreteLowUnbalancedStaticStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Quantitative reserves from an unbalanced static transfer

The arbitrary transfer does more than prove nonnegativity.  If both corrected
endpoint matrices dominate the same parity-block quadratic, that reserve
survives every phase in the closed disk without loss.  This is the form needed
to pay the low--tail Schur cross by one operator reserve rather than by
row-by-row estimates.
-/

/-- Subtracting fixed even and odd reserves from the two clean scalars reduces
the quantitative statement to the existing unbalanced interpolation. -/
theorem scalar_phase_ge_reserve_of_unbalanced_static_splits
    (QE PE QO PO J H RE RO a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hPlus : ∀ r s : ℝ,
      r ^ 2 * RE + s ^ 2 * RO ≤
        r ^ 2 * (QE + PE) + s ^ 2 * (QO - PO) +
          r * s * (J - 2 * H))
    (hMinus : ∀ r s : ℝ,
      r ^ 2 * RE + s ^ 2 * RO ≤
        r ^ 2 * (QE - PE) + s ^ 2 * (QO + PO) +
          r * s * (J + 2 * H)) :
    RE + RO ≤ QE + QO + a * (PE + PO) + b * J := by
  have h := scalar_phase_nonneg_of_unbalanced_static_splits
    (QE - RE) PE (QO - RO) PO J H a b hab
    (by
      intro r s
      have hrs := hPlus r s
      nlinarith)
    (by
      intro r s
      have hrs := hMinus r s
      nlinarith)
  nlinarith

/-- Scalar reserve handoff for the exact concrete low pencils. -/
theorem factorTwoConcreteLowPhase_ge_reserve_of_unbalanced_static
    (H RE RO : ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (hPlus : ∀ r s : ℝ,
      r ^ 2 * RE + s ^ 2 * RO ≤
        r ^ 2 * factorTwoConcreteEvenPencilValue 1 e +
          s ^ 2 * factorTwoConcreteOddPencilValue (-1) o +
          r * s * (factorTwoConcreteAlternatingValue e o - 2 * H))
    (hMinus : ∀ r s : ℝ,
      r ^ 2 * RE + s ^ 2 * RO ≤
        r ^ 2 * factorTwoConcreteEvenPencilValue (-1) e +
          s ^ 2 * factorTwoConcreteOddPencilValue 1 o +
          r * s * (factorTwoConcreteAlternatingValue e o + 2 * H))
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    RE + RO ≤ factorTwoEndpointChannelPhase
      (factorTwoAdaptedEvenLowSynthesis e)
      (factorTwoOddLowSynthesis o) a b := by
  let QE := e ⬝ᵥ (factorTwoConcreteAdaptedEvenCleanMatrix *ᵥ e)
  let PE := e ⬝ᵥ (factorTwoConcreteEvenPerturbationMatrix *ᵥ e)
  let QO := o ⬝ᵥ (factorTwoConcreteOddCleanMatrix *ᵥ o)
  let PO := o ⬝ᵥ (factorTwoConcreteOddPerturbationMatrix *ᵥ o)
  let J := factorTwoConcreteAlternatingValue e o
  have hpencilEven (t : ℝ) :
      factorTwoConcreteEvenPencilValue t e = QE + t * PE := by
    dsimp only [QE, PE]
    unfold factorTwoConcreteEvenPencilValue
    simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
  have hpencilOdd (t : ℝ) :
      factorTwoConcreteOddPencilValue t o = QO + t * PO := by
    dsimp only [QO, PO]
    unfold factorTwoConcreteOddPencilValue
    simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
  have hreserve := scalar_phase_ge_reserve_of_unbalanced_static_splits
    QE PE QO PO J H RE RO a b hab
    (by
      intro r s
      have hrs := hPlus r s
      rw [hpencilEven, hpencilOdd] at hrs
      dsimp only [J]
      nlinarith)
    (by
      intro r s
      have hrs := hMinus r s
      rw [hpencilEven, hpencilOdd] at hrs
      dsimp only [J]
      nlinarith)
  rw [factorTwoConcreteLowPhase_eq_pencils]
  rw [hpencilEven, hpencilOdd]
  dsimp only [J] at hreserve ⊢
  nlinarith

private theorem matrixQuadratic_smul
    {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (r : ℝ) (x : n → ℝ) :
    (r • x) ⬝ᵥ (M *ᵥ (r • x)) =
      r ^ 2 * (x ⬝ᵥ (M *ᵥ x)) := by
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

private theorem parityBlock_quadratic
    (E : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (O : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    let c := factorTwoPhaseLowCoefficients e o
    c ⬝ᵥ (factorTwoPhaseBlockMatrix E O 0 *ᵥ c) =
      e ⬝ᵥ (E *ᵥ e) + o ⬝ᵥ (O *ᵥ o) := by
  simpa only [zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero] using
    factorTwoPhaseBlockMatrix_quadratic E O 0 e o

/-- A common parity-block reserve dominated by the two corrected unbalanced
endpoints propagates to the exact concrete phase matrix on the whole disk. -/
theorem factorTwoConcreteLowPhaseMatrix_parityBlockReserve_of_unbalanced_static
    (H : Matrix YoshidaEvenIndex YoshidaOddIndex ℝ)
    (E : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (O : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (hPlus : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      c ⬝ᵥ (factorTwoPhaseBlockMatrix E O 0 *ᵥ c) ≤
        c ⬝ᵥ (factorTwoConcreteLowUnbalancedStaticPlusMatrix H *ᵥ c))
    (hMinus : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      c ⬝ᵥ (factorTwoPhaseBlockMatrix E O 0 *ᵥ c) ≤
        c ⬝ᵥ (factorTwoConcreteLowUnbalancedStaticMinusMatrix H *ᵥ c))
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (c : FactorTwoPhaseLowIndex → ℝ) :
    c ⬝ᵥ (factorTwoPhaseBlockMatrix E O 0 *ᵥ c) ≤
      c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c) := by
  let e : YoshidaEvenIndex → ℝ := fun i ↦ c (Sum.inl i)
  let o : YoshidaOddIndex → ℝ := fun i ↦ c (Sum.inr i)
  let RE := e ⬝ᵥ (E *ᵥ e)
  let RO := o ⬝ᵥ (O *ᵥ o)
  let HH := factorTwoConcreteLowTransferValue H e o
  have hc : factorTwoPhaseLowCoefficients e o = c := by
    funext i
    rcases i with i | i <;> rfl
  have hPlusScalar : ∀ r s : ℝ,
      r ^ 2 * RE + s ^ 2 * RO ≤
        r ^ 2 * factorTwoConcreteEvenPencilValue 1 e +
          s ^ 2 * factorTwoConcreteOddPencilValue (-1) o +
          r * s * (factorTwoConcreteAlternatingValue e o - 2 * HH) := by
    intro r s
    have h := hPlus (factorTwoPhaseLowCoefficients (r • e) (s • o))
    rw [parityBlock_quadratic,
      factorTwoConcreteLowUnbalancedStaticPlusMatrix_quadratic] at h
    rw [matrixQuadratic_smul, matrixQuadratic_smul,
      factorTwoConcreteEvenPencilValue_scale,
      factorTwoConcreteOddPencilValue_scale,
      factorTwoConcreteAlternatingValue_scale,
      factorTwoConcreteLowTransferValue_scale] at h
    dsimp only [RE, RO, HH]
    nlinarith
  have hMinusScalar : ∀ r s : ℝ,
      r ^ 2 * RE + s ^ 2 * RO ≤
        r ^ 2 * factorTwoConcreteEvenPencilValue (-1) e +
          s ^ 2 * factorTwoConcreteOddPencilValue 1 o +
          r * s * (factorTwoConcreteAlternatingValue e o + 2 * HH) := by
    intro r s
    have h := hMinus (factorTwoPhaseLowCoefficients (r • e) (s • o))
    rw [parityBlock_quadratic,
      factorTwoConcreteLowUnbalancedStaticMinusMatrix_quadratic] at h
    rw [matrixQuadratic_smul, matrixQuadratic_smul,
      factorTwoConcreteEvenPencilValue_scale,
      factorTwoConcreteOddPencilValue_scale,
      factorTwoConcreteAlternatingValue_scale,
      factorTwoConcreteLowTransferValue_scale] at h
    dsimp only [RE, RO, HH]
    nlinarith
  have hreserve := factorTwoConcreteLowPhase_ge_reserve_of_unbalanced_static
    HH RE RO e o hPlusScalar hMinusScalar a b hab
  rw [← hc, parityBlock_quadratic,
    ← factorTwoConcreteLowPhaseMatrix_represents]
  exact hreserve

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowUnbalancedStaticReserveStructural
