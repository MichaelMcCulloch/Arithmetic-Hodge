import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowSplitReserveStructural

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowSplitBlockReserveStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
open YoshidaFactorTwoPhaseConcreteLowSplitReserveStructural
open YoshidaFactorTwoPhaseConcreteLowSplitToeplitz
open YoshidaFactorTwoPhaseConcreteLowToeplitz
open YoshidaFactorTwoPhaseLowSchur

/-!
# Parity-block reserves survive the whole phase disk

The static-split transport is not intrinsically coordinatewise.  Every
quadratic reserve that is block diagonal for the even/odd parity splitting
obeys the same Hadamard and phase-lift identities.  Thus a common reserve by
two arbitrary parity-block quadratic forms propagates to the full phase disk
without loss.

This is the operator-level interface needed for the low-tail Schur step: the
reserve may now be chosen as a clean-energy form, avoiding a separate
Hilbert--Schmidt payment for every low Fourier row.
-/

private def parityBlockReserve
    (E : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (O : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (c : FactorTwoPhaseLowIndex → ℝ) : ℝ :=
  let e : YoshidaEvenIndex → ℝ := fun i ↦ c (Sum.inl i)
  let o : YoshidaOddIndex → ℝ := fun i ↦ c (Sum.inr i)
  e ⬝ᵥ (E *ᵥ e) + o ⬝ᵥ (O *ᵥ o)

private theorem parityBlockReserve_lowCoefficients
    (E : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (O : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    parityBlockReserve E O (factorTwoPhaseLowCoefficients e o) =
      e ⬝ᵥ (E *ᵥ e) + o ⬝ᵥ (O *ᵥ o) := by
  rfl

private theorem matrixQuadratic_zero
    {n : Type*} [Fintype n] (M : Matrix n n ℝ) :
    (0 : n → ℝ) ⬝ᵥ (M *ᵥ 0) = 0 := by
  simp

private theorem matrixQuadratic_neg
    {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x : n → ℝ) :
    (-x) ⬝ᵥ (M *ᵥ (-x)) = x ⬝ᵥ (M *ᵥ x) := by
  simp only [mulVec_neg, neg_dotProduct, dotProduct_neg]
  ring

private theorem matrixQuadratic_smul
    {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (r : ℝ) (x : n → ℝ) :
    (r • x) ⬝ᵥ (M *ᵥ (r • x)) =
      r ^ 2 * (x ⬝ᵥ (M *ᵥ x)) := by
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

private theorem matrixQuadratic_add_sub
    {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (x y : n → ℝ) :
    (x + y) ⬝ᵥ (M *ᵥ (x + y)) +
        (x - y) ⬝ᵥ (M *ᵥ (x - y)) =
      2 * (x ⬝ᵥ (M *ᵥ x) + y ⬝ᵥ (M *ᵥ y)) := by
  simp only [mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub]
  ring

private theorem matrixQuadratic_rev_sub_add
    {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (x y : n → ℝ) :
    (y - x) ⬝ᵥ (M *ᵥ (y - x)) +
        (x + y) ⬝ᵥ (M *ᵥ (x + y)) =
      2 * (x ⬝ᵥ (M *ᵥ x) + y ⬝ᵥ (M *ᵥ y)) := by
  simp only [mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub]
  ring

private theorem parityBlockReserve_eq_quadratic
    (E : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (O : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (c : FactorTwoPhaseLowIndex → ℝ) :
    parityBlockReserve E O c =
      c ⬝ᵥ (factorTwoPhaseBlockMatrix E O 0 *ᵥ c) := by
  let e : YoshidaEvenIndex → ℝ := fun i ↦ c (Sum.inl i)
  let o : YoshidaOddIndex → ℝ := fun i ↦ c (Sum.inr i)
  have hc : factorTwoPhaseLowCoefficients e o = c := by
    funext k
    rcases k with i | i <;> rfl
  have hq := factorTwoPhaseBlockMatrix_quadratic E O 0 e o
  dsimp only at hq
  rw [← hc]
  rw [hq]
  simp [parityBlockReserve_lowCoefficients]

private theorem factorTwoConcreteLowToeplitz_parityBlockReserve_of_split
    (E : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (O : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (hPlus : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      parityBlockReserve E O c ≤
        c ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix *ᵥ c))
    (hMinus : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      parityBlockReserve E O c ≤
        c ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix *ᵥ c))
    (x y : FactorTwoPhaseLowIndex → ℝ) :
    (parityBlockReserve E O x + parityBlockReserve E O y) / 2 ≤
      factorTwoPhaseToeplitzCoefficients x y ⬝ᵥ
        (factorTwoConcreteLowToeplitzMatrix *ᵥ
          factorTwoPhaseToeplitzCoefficients x y) := by
  let e₁ : YoshidaEvenIndex → ℝ := fun i ↦ x (Sum.inl i)
  let o₁ : YoshidaOddIndex → ℝ := fun i ↦ x (Sum.inr i)
  let e₂ : YoshidaEvenIndex → ℝ := fun i ↦ y (Sum.inl i)
  let o₂ : YoshidaOddIndex → ℝ := fun i ↦ y (Sum.inr i)
  have hx : factorTwoPhaseLowCoefficients e₁ o₁ = x := by
    funext k
    rcases k with i | i <;> rfl
  have hy : factorTwoPhaseLowCoefficients e₂ o₂ = y := by
    funext k
    rcases k with i | i <;> rfl
  let cPlus := factorTwoPhaseLowCoefficients (e₁ + e₂) (o₂ - o₁)
  let cMinus := factorTwoPhaseLowCoefficients (e₁ - e₂) (o₁ + o₂)
  have hsplit :
      factorTwoPhaseToeplitzCoefficients x y ⬝ᵥ
          (factorTwoConcreteLowToeplitzMatrix *ᵥ
            factorTwoPhaseToeplitzCoefficients x y) =
        (cPlus ⬝ᵥ
              (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix *ᵥ cPlus) +
          cMinus ⬝ᵥ
              (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix *ᵥ cMinus)) / 4 := by
    rw [← hx, ← hy]
    simpa only [cPlus, cMinus] using
      (factorTwoConcreteLowToeplitz_quadratic_eq_split e₁ e₂ o₁ o₂)
  have he := matrixQuadratic_add_sub E e₁ e₂
  have ho := matrixQuadratic_rev_sub_add O o₁ o₂
  have hxq : parityBlockReserve E O x =
      e₁ ⬝ᵥ (E *ᵥ e₁) + o₁ ⬝ᵥ (O *ᵥ o₁) := by
    rw [← hx]
    exact parityBlockReserve_lowCoefficients E O e₁ o₁
  have hyq : parityBlockReserve E O y =
      e₂ ⬝ᵥ (E *ᵥ e₂) + o₂ ⬝ᵥ (O *ᵥ o₂) := by
    rw [← hy]
    exact parityBlockReserve_lowCoefficients E O e₂ o₂
  have hreserve :
      parityBlockReserve E O cPlus +
          parityBlockReserve E O cMinus =
        2 * (parityBlockReserve E O x + parityBlockReserve E O y) := by
    simp only [cPlus, cMinus, parityBlockReserve_lowCoefficients]
    linarith
  have hsum := add_le_add (hPlus cPlus) (hMinus cMinus)
  rw [hsplit]
  nlinarith

private theorem factorTwoConcreteLowCleanBlock_parityBlockReserve_of_split
    (E : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (O : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (hPlus : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      parityBlockReserve E O c ≤
        c ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix *ᵥ c))
    (hMinus : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      parityBlockReserve E O c ≤
        c ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix *ᵥ c))
    (x : FactorTwoPhaseLowIndex → ℝ) :
    parityBlockReserve E O x ≤
      x ⬝ᵥ (factorTwoConcreteLowCleanBlockMatrix *ᵥ x) := by
  have hreserve :=
    factorTwoConcreteLowToeplitz_parityBlockReserve_of_split
      E O hPlus hMinus x 0
  have hzero : parityBlockReserve E O 0 = 0 := by
    simp [parityBlockReserve]
  have htoeplitz :
      factorTwoPhaseToeplitzCoefficients x 0 ⬝ᵥ
          (factorTwoConcreteLowToeplitzMatrix *ᵥ
            factorTwoPhaseToeplitzCoefficients x 0) =
        (x ⬝ᵥ (factorTwoConcreteLowCleanBlockMatrix *ᵥ x)) / 2 := by
    rw [factorTwoConcreteLowToeplitzMatrix,
      factorTwoPhaseToeplitzBlockMatrix_quadratic]
    simp only [mulVec_zero, dotProduct_zero, add_zero,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  rw [hzero, htoeplitz] at hreserve
  linarith

private theorem parityBlockReserve_phase_lifts
    (E : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (O : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) :
    parityBlockReserve E O (factorTwoPhaseLowCoefficients e 0) +
        parityBlockReserve E O
          (factorTwoPhaseLowCoefficients (a • e) (b • o)) +
        parityBlockReserve E O (factorTwoPhaseLowCoefficients 0 (-o)) +
        parityBlockReserve E O
          (factorTwoPhaseLowCoefficients (b • e) (-a • o)) =
      (1 + a ^ 2 + b ^ 2) *
        parityBlockReserve E O (factorTwoPhaseLowCoefficients e o) := by
  simp only [parityBlockReserve_lowCoefficients, matrixQuadratic_zero,
    zero_add, add_zero]
  rw [matrixQuadratic_neg, matrixQuadratic_smul, matrixQuadratic_smul,
    matrixQuadratic_smul, matrixQuadratic_smul]
  ring

/-- A common parity-block quadratic reserve for the two static splits
propagates, with no loss, to every concrete finite-low phase matrix on the
closed disk. -/
theorem factorTwoConcreteLowPhaseMatrix_parityBlockReserve_of_split
    (E : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (O : Matrix YoshidaOddIndex YoshidaOddIndex ℝ)
    (hPlus : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      c ⬝ᵥ (factorTwoPhaseBlockMatrix E O 0 *ᵥ c) ≤
        c ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix *ᵥ c))
    (hMinus : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      c ⬝ᵥ (factorTwoPhaseBlockMatrix E O 0 *ᵥ c) ≤
        c ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix *ᵥ c))
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (c : FactorTwoPhaseLowIndex → ℝ) :
    c ⬝ᵥ (factorTwoPhaseBlockMatrix E O 0 *ᵥ c) ≤
      c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c) := by
  let e : YoshidaEvenIndex → ℝ := fun i ↦ c (Sum.inl i)
  let o : YoshidaOddIndex → ℝ := fun i ↦ c (Sum.inr i)
  have hc : factorTwoPhaseLowCoefficients e o = c := by
    funext k
    rcases k with i | i <;> rfl
  have hPlus' : ∀ x : FactorTwoPhaseLowIndex → ℝ,
      parityBlockReserve E O x ≤
        x ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix *ᵥ x) := by
    intro x
    rw [parityBlockReserve_eq_quadratic]
    exact hPlus x
  have hMinus' : ∀ x : FactorTwoPhaseLowIndex → ℝ,
      parityBlockReserve E O x ≤
        x ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix *ᵥ x) := by
    intro x
    rw [parityBlockReserve_eq_quadratic]
    exact hMinus x
  have hcr := factorTwoConcreteLowToeplitz_parityBlockReserve_of_split
    E O hPlus' hMinus'
    (factorTwoPhaseLowCoefficients e 0)
    (factorTwoPhaseLowCoefficients (a • e) (b • o))
  have hcs := factorTwoConcreteLowToeplitz_parityBlockReserve_of_split
    E O hPlus' hMinus'
    (factorTwoPhaseLowCoefficients 0 (-o))
    (factorTwoPhaseLowCoefficients (b • e) (-a • o))
  have hweights := parityBlockReserve_phase_lifts E O e o a b
  have hlifts :
      ((1 + a ^ 2 + b ^ 2) / 2) * parityBlockReserve E O c ≤
        factorTwoPhaseToeplitzCoefficients
              (factorTwoPhaseLowCoefficients e 0)
              (factorTwoPhaseLowCoefficients (a • e) (b • o)) ⬝ᵥ
            (factorTwoConcreteLowToeplitzMatrix *ᵥ
              factorTwoPhaseToeplitzCoefficients
                (factorTwoPhaseLowCoefficients e 0)
                (factorTwoPhaseLowCoefficients (a • e) (b • o))) +
          factorTwoPhaseToeplitzCoefficients
              (factorTwoPhaseLowCoefficients 0 (-o))
              (factorTwoPhaseLowCoefficients (b • e) (-a • o)) ⬝ᵥ
            (factorTwoConcreteLowToeplitzMatrix *ᵥ
              factorTwoPhaseToeplitzCoefficients
                (factorTwoPhaseLowCoefficients 0 (-o))
                (factorTwoPhaseLowCoefficients (b • e) (-a • o))) := by
    rw [hc] at hweights
    nlinarith [add_le_add hcr hcs]
  have hclean :=
    factorTwoConcreteLowCleanBlock_parityBlockReserve_of_split
      E O hPlus' hMinus' c
  have hremainder : 0 ≤ (1 - (a ^ 2 + b ^ 2)) / 2 := by
    linarith
  have hcleanScaled := mul_le_mul_of_nonneg_left hclean hremainder
  have hdecomp :=
    factorTwoConcreteLowPhase_eq_toeplitz_lifts_add_clean_remainder e o a b
  dsimp only at hdecomp
  rw [hc] at hdecomp
  rw [← parityBlockReserve_eq_quadratic E O c]
  rw [hdecomp]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowSplitBlockReserveStructural
