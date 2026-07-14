import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowToeplitz

set_option autoImplicit false
set_option maxRecDepth 100000

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowSplitToeplitz

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
open YoshidaFactorTwoPhaseConcreteCleanOddMatrix
open YoshidaFactorTwoPhaseConcreteLowDiskSchur
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
open YoshidaFactorTwoPhaseConcreteLowToeplitz
open YoshidaFactorTwoPhaseLowSchur

/-!
# Real parity-split Toeplitz certificate

The oriented real Toeplitz matrix is orthogonally congruent to two real
`200 + 10` blocks.  An unnormalized Hadamard transform avoids square roots:
its quadratic is one quarter of the sum of the two split quadratics below.
The odd coordinate receives the parity sign in the first split.
-/

/-- The split with `Q_E + P_E` and `Q_O - P_O` on the diagonal. -/
def factorTwoConcreteLowSplitToeplitzEvenPlusMatrix :
    Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ :=
  factorTwoPhaseBlockMatrix
    (factorTwoConcreteAdaptedEvenCleanMatrix +
      factorTwoConcreteEvenPerturbationMatrix)
    (factorTwoConcreteOddCleanMatrix -
      factorTwoConcreteOddPerturbationMatrix)
    (fun i j ↦ factorTwoConcreteAlternatingMatrix i j / 2)

/-- The split with `Q_E - P_E` and `Q_O + P_O` on the diagonal. -/
def factorTwoConcreteLowSplitToeplitzEvenMinusMatrix :
    Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ :=
  factorTwoPhaseBlockMatrix
    (factorTwoConcreteAdaptedEvenCleanMatrix -
      factorTwoConcreteEvenPerturbationMatrix)
    (factorTwoConcreteOddCleanMatrix +
      factorTwoConcreteOddPerturbationMatrix)
    (fun i j ↦ factorTwoConcreteAlternatingMatrix i j / 2)

/-- Hermitian symmetry of the even-plus parity split. -/
theorem factorTwoConcreteLowSplitToeplitzEvenPlusMatrix_isHermitian :
    factorTwoConcreteLowSplitToeplitzEvenPlusMatrix.IsHermitian := by
  exact factorTwoPhaseBlockMatrix_isHermitian _
    (factorTwoConcreteAdaptedEvenCleanMatrix_isHermitian.add
      factorTwoConcreteEvenPerturbationMatrix_isHermitian)
    (factorTwoConcreteOddCleanMatrix_isHermitian.sub
      factorTwoConcreteOddPerturbationMatrix_isHermitian)

/-- Hermitian symmetry of the even-minus parity split. -/
theorem factorTwoConcreteLowSplitToeplitzEvenMinusMatrix_isHermitian :
    factorTwoConcreteLowSplitToeplitzEvenMinusMatrix.IsHermitian := by
  exact factorTwoPhaseBlockMatrix_isHermitian _
    (factorTwoConcreteAdaptedEvenCleanMatrix_isHermitian.sub
      factorTwoConcreteEvenPerturbationMatrix_isHermitian)
    (factorTwoConcreteOddCleanMatrix_isHermitian.add
      factorTwoConcreteOddPerturbationMatrix_isHermitian)

private theorem evenPerturbation_apply_comm
    (i j : YoshidaEvenIndex) :
    factorTwoConcreteEvenPerturbationMatrix i j =
      factorTwoConcreteEvenPerturbationMatrix j i := by
  simpa only [star_trivial] using
    (factorTwoConcreteEvenPerturbationMatrix_isHermitian.apply i j).symm

private theorem oddPerturbation_apply_comm
    (i j : YoshidaOddIndex) :
    factorTwoConcreteOddPerturbationMatrix i j =
      factorTwoConcreteOddPerturbationMatrix j i := by
  simpa only [star_trivial] using
    (factorTwoConcreteOddPerturbationMatrix_isHermitian.apply i j).symm

private theorem dotProduct_mulVec_comm_of_apply_comm
    {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (hM : ∀ i j, M i j = M j i)
    (x y : n → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  have hMT : Mᵀ = M := by
    ext i j
    exact hM j i
  calc
    x ⬝ᵥ (M *ᵥ y) = (x ᵥ* M) ⬝ᵥ y := dotProduct_mulVec x M y
    _ = (Mᵀ *ᵥ x) ⬝ᵥ y := by rw [mulVec_transpose]
    _ = (M *ᵥ x) ⬝ᵥ y := by rw [hMT]
    _ = y ⬝ᵥ (M *ᵥ x) := dotProduct_comm _ _

private theorem quadratic_add_sub_sum
    {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (x y : n → ℝ) :
    (x + y) ⬝ᵥ (M *ᵥ (x + y)) +
        (x - y) ⬝ᵥ (M *ᵥ (x - y)) =
      2 * (x ⬝ᵥ (M *ᵥ x) + y ⬝ᵥ (M *ᵥ y)) := by
  simp only [mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub]
  ring

private theorem quadratic_rev_sub_sum
    {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (x y : n → ℝ) :
    (y - x) ⬝ᵥ (M *ᵥ (y - x)) +
        (x + y) ⬝ᵥ (M *ᵥ (x + y)) =
      2 * (x ⬝ᵥ (M *ᵥ x) + y ⬝ᵥ (M *ᵥ y)) := by
  simp only [mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub]
  ring

private theorem quadratic_add_sub_difference
    {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (hM : ∀ i j, M i j = M j i)
    (x y : n → ℝ) :
    (x + y) ⬝ᵥ (M *ᵥ (x + y)) -
        (x - y) ⬝ᵥ (M *ᵥ (x - y)) =
      4 * (x ⬝ᵥ (M *ᵥ y)) := by
  have hxy := dotProduct_mulVec_comm_of_apply_comm M hM y x
  simp only [mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub]
  rw [hxy]
  ring

private theorem quadratic_rev_sub_difference
    {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (hM : ∀ i j, M i j = M j i)
    (x y : n → ℝ) :
    -((y - x) ⬝ᵥ (M *ᵥ (y - x))) +
        (x + y) ⬝ᵥ (M *ᵥ (x + y)) =
      4 * (x ⬝ᵥ (M *ᵥ y)) := by
  have hxy := dotProduct_mulVec_comm_of_apply_comm M hM y x
  simp only [mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub]
  rw [hxy]
  ring

private theorem alternatingValue_split
    (e₁ e₂ : YoshidaEvenIndex → ℝ)
    (o₁ o₂ : YoshidaOddIndex → ℝ) :
    factorTwoConcreteAlternatingValue (e₁ + e₂) (o₂ - o₁) +
        factorTwoConcreteAlternatingValue (e₁ - e₂) (o₁ + o₂) =
      2 * (factorTwoConcreteAlternatingValue e₁ o₂ -
        factorTwoConcreteAlternatingValue e₂ o₁) := by
  unfold factorTwoConcreteAlternatingValue
  simp only [Pi.add_apply, Pi.sub_apply]
  simp_rw [add_mul, sub_mul, mul_add, mul_sub]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [Finset.sum_add_distrib]
  ring

private theorem alternating_half_sum
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    (∑ i, ∑ j,
        e i * (factorTwoConcreteAlternatingMatrix i j / 2) * o j) =
      factorTwoConcreteAlternatingValue e o / 2 := by
  unfold factorTwoConcreteAlternatingValue
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

private theorem cleanBlock_quadratic
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    let x := factorTwoPhaseLowCoefficients e o
    x ⬝ᵥ (factorTwoConcreteLowCleanBlockMatrix *ᵥ x) =
      e ⬝ᵥ (factorTwoConcreteAdaptedEvenCleanMatrix *ᵥ e) +
        o ⬝ᵥ (factorTwoConcreteOddCleanMatrix *ᵥ o) := by
  simpa only [factorTwoConcreteLowCleanBlockMatrix, zero_apply, mul_zero,
    zero_mul, Finset.sum_const_zero, add_zero] using
    factorTwoPhaseBlockMatrix_quadratic
      factorTwoConcreteAdaptedEvenCleanMatrix
      factorTwoConcreteOddCleanMatrix 0 e o

private theorem orientedMatrix_cross
    (e₁ e₂ : YoshidaEvenIndex → ℝ)
    (o₁ o₂ : YoshidaOddIndex → ℝ) :
    let x := factorTwoPhaseLowCoefficients e₁ o₁
    let y := factorTwoPhaseLowCoefficients e₂ o₂
    ∑ i, ∑ j, x i * factorTwoConcreteLowOrientedMatrix i j * y j =
      e₁ ⬝ᵥ (factorTwoConcreteEvenPerturbationMatrix *ᵥ e₂) +
        o₁ ⬝ᵥ (factorTwoConcreteOddPerturbationMatrix *ᵥ o₂) +
        factorTwoConcreteAlternatingValue e₁ o₂ / 2 -
        factorTwoConcreteAlternatingValue e₂ o₁ / 2 := by
  have hupper := alternating_half_sum e₁ o₂
  have hreindex :
      (∑ j, ∑ i,
        o₁ j * factorTwoConcreteAlternatingMatrix i j * e₂ i) =
        factorTwoConcreteAlternatingValue e₂ o₁ := by
    unfold factorTwoConcreteAlternatingValue
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hlower :
      (∑ j, ∑ i,
        o₁ j * (-factorTwoConcreteAlternatingMatrix i j / 2) * e₂ i) =
        -factorTwoConcreteAlternatingValue e₂ o₁ / 2 := by
    calc
      (∑ j, ∑ i,
          o₁ j * (-factorTwoConcreteAlternatingMatrix i j / 2) * e₂ i) =
          (-1 / 2 : ℝ) *
            ∑ j, ∑ i,
              o₁ j * factorTwoConcreteAlternatingMatrix i j * e₂ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = _ := by rw [hreindex]; ring
  dsimp only
  simp only [dotProduct, mulVec, factorTwoPhaseLowCoefficients]
  simp_rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr,
    factorTwoConcreteLowOrientedMatrix, Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  rw [hupper, hlower]
  ring

private theorem splitEvenPlus_quadratic
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    let c := factorTwoPhaseLowCoefficients e o
    c ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix *ᵥ c) =
      e ⬝ᵥ (factorTwoConcreteAdaptedEvenCleanMatrix *ᵥ e) +
        e ⬝ᵥ (factorTwoConcreteEvenPerturbationMatrix *ᵥ e) +
        o ⬝ᵥ (factorTwoConcreteOddCleanMatrix *ᵥ o) -
        o ⬝ᵥ (factorTwoConcreteOddPerturbationMatrix *ᵥ o) +
        factorTwoConcreteAlternatingValue e o := by
  dsimp only
  rw [factorTwoConcreteLowSplitToeplitzEvenPlusMatrix,
    factorTwoPhaseBlockMatrix_quadratic]
  simp only [add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub]
  rw [alternating_half_sum]
  ring

private theorem splitEvenMinus_quadratic
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    let c := factorTwoPhaseLowCoefficients e o
    c ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix *ᵥ c) =
      e ⬝ᵥ (factorTwoConcreteAdaptedEvenCleanMatrix *ᵥ e) -
        e ⬝ᵥ (factorTwoConcreteEvenPerturbationMatrix *ᵥ e) +
        o ⬝ᵥ (factorTwoConcreteOddCleanMatrix *ᵥ o) +
        o ⬝ᵥ (factorTwoConcreteOddPerturbationMatrix *ᵥ o) +
        factorTwoConcreteAlternatingValue e o := by
  dsimp only
  rw [factorTwoConcreteLowSplitToeplitzEvenMinusMatrix,
    factorTwoPhaseBlockMatrix_quadratic]
  simp only [add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub]
  rw [alternating_half_sum]
  ring

/-- Exact unnormalized Hadamard/parity decomposition of the oriented
Toeplitz quadratic into the two real split quadratics. -/
theorem factorTwoConcreteLowToeplitz_quadratic_eq_split
    (e₁ e₂ : YoshidaEvenIndex → ℝ)
    (o₁ o₂ : YoshidaOddIndex → ℝ) :
    let x := factorTwoPhaseLowCoefficients e₁ o₁
    let y := factorTwoPhaseLowCoefficients e₂ o₂
    let c := factorTwoPhaseToeplitzCoefficients x y
    let cPlus := factorTwoPhaseLowCoefficients (e₁ + e₂) (o₂ - o₁)
    let cMinus := factorTwoPhaseLowCoefficients (e₁ - e₂) (o₁ + o₂)
    c ⬝ᵥ (factorTwoConcreteLowToeplitzMatrix *ᵥ c) =
      (cPlus ⬝ᵥ
          (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix *ᵥ cPlus) +
        cMinus ⬝ᵥ
          (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix *ᵥ cMinus)) / 4 := by
  have hQE := quadratic_add_sub_sum factorTwoConcreteAdaptedEvenCleanMatrix e₁ e₂
  have hQO := quadratic_rev_sub_sum factorTwoConcreteOddCleanMatrix o₁ o₂
  have hPE := quadratic_add_sub_difference
    factorTwoConcreteEvenPerturbationMatrix evenPerturbation_apply_comm e₁ e₂
  have hPO := quadratic_rev_sub_difference
    factorTwoConcreteOddPerturbationMatrix oddPerturbation_apply_comm o₁ o₂
  have hJ := alternatingValue_split e₁ e₂ o₁ o₂
  dsimp only
  rw [factorTwoConcreteLowToeplitzMatrix,
    factorTwoPhaseToeplitzBlockMatrix_quadratic,
    cleanBlock_quadratic, cleanBlock_quadratic,
    orientedMatrix_cross,
    splitEvenPlus_quadratic, splitEvenMinus_quadratic]
  linarith

private theorem toeplitzBlockMatrix_isHermitian
    {n : Type*} (Q B : Matrix n n ℝ) (hQ : Q.IsHermitian) :
    (factorTwoPhaseToeplitzBlockMatrix Q B).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  cases i with
  | inl i =>
      cases j with
      | inl j => simpa [factorTwoPhaseToeplitzBlockMatrix] using hQ.apply i j
      | inr j => simp [factorTwoPhaseToeplitzBlockMatrix]
  | inr i =>
      cases j with
      | inl j => simp [factorTwoPhaseToeplitzBlockMatrix]
      | inr j => simpa [factorTwoPhaseToeplitzBlockMatrix] using hQ.apply i j

private theorem cleanBlock_isHermitian :
    factorTwoConcreteLowCleanBlockMatrix.IsHermitian := by
  exact factorTwoPhaseBlockMatrix_isHermitian 0
    factorTwoConcreteAdaptedEvenCleanMatrix_isHermitian
    factorTwoConcreteOddCleanMatrix_isHermitian

private theorem toeplitzMatrix_isHermitian :
    factorTwoConcreteLowToeplitzMatrix.IsHermitian := by
  exact toeplitzBlockMatrix_isHermitian
    factorTwoConcreteLowCleanBlockMatrix
    factorTwoConcreteLowOrientedMatrix cleanBlock_isHermitian

/-- Positive semidefiniteness of both real parity splits implies
positive semidefiniteness of the oriented static Toeplitz matrix. -/
theorem factorTwoConcreteLowToeplitz_posSemidef_of_split
    (hPlus : factorTwoConcreteLowSplitToeplitzEvenPlusMatrix.PosSemidef)
    (hMinus : factorTwoConcreteLowSplitToeplitzEvenMinusMatrix.PosSemidef) :
    factorTwoConcreteLowToeplitzMatrix.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    toeplitzMatrix_isHermitian
  intro c
  let e₁ : YoshidaEvenIndex → ℝ := fun i ↦ c (Sum.inl (Sum.inl i))
  let o₁ : YoshidaOddIndex → ℝ := fun i ↦ c (Sum.inl (Sum.inr i))
  let e₂ : YoshidaEvenIndex → ℝ := fun i ↦ c (Sum.inr (Sum.inl i))
  let o₂ : YoshidaOddIndex → ℝ := fun i ↦ c (Sum.inr (Sum.inr i))
  let cPlus := factorTwoPhaseLowCoefficients (e₁ + e₂) (o₂ - o₁)
  let cMinus := factorTwoPhaseLowCoefficients (e₁ - e₂) (o₁ + o₂)
  have hc : c = factorTwoPhaseToeplitzCoefficients
      (factorTwoPhaseLowCoefficients e₁ o₁)
      (factorTwoPhaseLowCoefficients e₂ o₂) := by
    funext i
    rcases i with i | i <;> rcases i with i | i <;> rfl
  have hPlusNonneg :
      0 ≤ cPlus ⬝ᵥ
        (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix *ᵥ cPlus) :=
    hPlus.dotProduct_mulVec_nonneg cPlus
  have hMinusNonneg :
      0 ≤ cMinus ⬝ᵥ
        (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix *ᵥ cMinus) :=
    hMinus.dotProduct_mulVec_nonneg cMinus
  simp only [star_trivial]
  rw [hc, factorTwoConcreteLowToeplitz_quadratic_eq_split]
  exact div_nonneg (add_nonneg hPlusNonneg hMinusNonneg) (by norm_num)

/-- The two real split certificates imply positivity of every concrete
low-phase matrix throughout the closed phase disk. -/
theorem factorTwoConcreteLowPhaseMatrix_posSemidef_of_split
    (hPlus : factorTwoConcreteLowSplitToeplitzEvenPlusMatrix.PosSemidef)
    (hMinus : factorTwoConcreteLowSplitToeplitzEvenMinusMatrix.PosSemidef)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (factorTwoConcreteLowPhaseMatrix a b).PosSemidef := by
  exact factorTwoConcreteLowPhaseMatrix_posSemidef_of_toeplitz
    (factorTwoConcreteLowToeplitz_posSemidef_of_split hPlus hMinus)
    a b hab

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowSplitToeplitz
