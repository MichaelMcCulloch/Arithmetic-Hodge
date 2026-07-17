import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowSplitToeplitz

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowSplitReserveStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
open YoshidaFactorTwoPhaseConcreteCleanOddMatrix
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
open YoshidaFactorTwoPhaseConcreteLowSplitToeplitz
open YoshidaFactorTwoPhaseConcreteLowToeplitz
open YoshidaFactorTwoPhaseLowSchur

/-!
# A common static-split reserve controls the whole phase disk

The two fixed real parity splits retain quantitative information, not merely
positive semidefiniteness.  If both splits dominate the same diagonal
quadratic, the unnormalized Hadamard identity gives half that reserve on each
copy of the static Toeplitz space.  The two phase lifts spend the factor
`(1 + a^2 + b^2) / 2`; the clean remainder supplies the complementary factor
`(1 - a^2 - b^2) / 2`.  Consequently the original diagonal reserve survives
on every point of the closed phase disk with no loss.
-/

private def weightedCoordinateSquare
    {n : Type*} [Fintype n] (d x : n → ℝ) : ℝ :=
  ∑ i, d i * x i ^ 2

private theorem weightedCoordinateSquare_smul
    {n : Type*} [Fintype n]
    (d x : n → ℝ) (r : ℝ) :
    weightedCoordinateSquare d (r • x) =
      r ^ 2 * weightedCoordinateSquare d x := by
  unfold weightedCoordinateSquare
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem weightedCoordinateSquare_neg
    {n : Type*} [Fintype n]
    (d x : n → ℝ) :
    weightedCoordinateSquare d (-x) = weightedCoordinateSquare d x := by
  unfold weightedCoordinateSquare
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Pi.neg_apply]
  ring

private theorem weightedCoordinateSquare_zero
    {n : Type*} [Fintype n]
    (d : n → ℝ) :
    weightedCoordinateSquare d 0 = 0 := by
  simp [weightedCoordinateSquare]

private theorem weightedCoordinateSquare_lowCoefficients
    (d : FactorTwoPhaseLowIndex → ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    weightedCoordinateSquare d (factorTwoPhaseLowCoefficients e o) =
      weightedCoordinateSquare (fun i ↦ d (Sum.inl i)) e +
        weightedCoordinateSquare (fun j ↦ d (Sum.inr j)) o := by
  unfold weightedCoordinateSquare factorTwoPhaseLowCoefficients
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]

private theorem weightedCoordinateSquare_add_sub
    {n : Type*} [Fintype n]
    (d x y : n → ℝ) :
    weightedCoordinateSquare d (x + y) +
        weightedCoordinateSquare d (x - y) =
      2 * (weightedCoordinateSquare d x +
        weightedCoordinateSquare d y) := by
  calc
    weightedCoordinateSquare d (x + y) +
          weightedCoordinateSquare d (x - y) =
        ∑ i, (d i * (x i + y i) ^ 2 +
          d i * (x i - y i) ^ 2) := by
            unfold weightedCoordinateSquare
            rw [Finset.sum_add_distrib]
            simp only [Pi.add_apply, Pi.sub_apply]
    _ = ∑ i, 2 * (d i * x i ^ 2 + d i * y i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = 2 * (weightedCoordinateSquare d x +
        weightedCoordinateSquare d y) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      unfold weightedCoordinateSquare
      ring

private theorem weightedCoordinateSquare_rev_sub_add
    {n : Type*} [Fintype n]
    (d x y : n → ℝ) :
    weightedCoordinateSquare d (y - x) +
        weightedCoordinateSquare d (x + y) =
      2 * (weightedCoordinateSquare d x +
        weightedCoordinateSquare d y) := by
  calc
    weightedCoordinateSquare d (y - x) +
          weightedCoordinateSquare d (x + y) =
        ∑ i, (d i * (y i - x i) ^ 2 +
          d i * (x i + y i) ^ 2) := by
            unfold weightedCoordinateSquare
            rw [Finset.sum_add_distrib]
            simp only [Pi.add_apply, Pi.sub_apply]
    _ = ∑ i, 2 * (d i * x i ^ 2 + d i * y i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = 2 * (weightedCoordinateSquare d x +
        weightedCoordinateSquare d y) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      unfold weightedCoordinateSquare
      ring

private theorem factorTwoConcreteLowToeplitz_weightedReserve_of_split
    (d : FactorTwoPhaseLowIndex → ℝ)
    (hPlus : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      weightedCoordinateSquare d c ≤
        c ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix *ᵥ c))
    (hMinus : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      weightedCoordinateSquare d c ≤
        c ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix *ᵥ c))
    (x y : FactorTwoPhaseLowIndex → ℝ) :
    (weightedCoordinateSquare d x + weightedCoordinateSquare d y) / 2 ≤
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
  have he := weightedCoordinateSquare_add_sub
    (fun i ↦ d (Sum.inl i)) e₁ e₂
  have ho := weightedCoordinateSquare_rev_sub_add
    (fun i ↦ d (Sum.inr i)) o₁ o₂
  have hxw : weightedCoordinateSquare d x =
      weightedCoordinateSquare (fun i ↦ d (Sum.inl i)) e₁ +
        weightedCoordinateSquare (fun i ↦ d (Sum.inr i)) o₁ := by
    rw [← hx]
    exact weightedCoordinateSquare_lowCoefficients d e₁ o₁
  have hyw : weightedCoordinateSquare d y =
      weightedCoordinateSquare (fun i ↦ d (Sum.inl i)) e₂ +
        weightedCoordinateSquare (fun i ↦ d (Sum.inr i)) o₂ := by
    rw [← hy]
    exact weightedCoordinateSquare_lowCoefficients d e₂ o₂
  have hweights :
      weightedCoordinateSquare d cPlus +
          weightedCoordinateSquare d cMinus =
        2 * (weightedCoordinateSquare d x +
          weightedCoordinateSquare d y) := by
    simp only [cPlus, cMinus,
      weightedCoordinateSquare_lowCoefficients,
      hxw, hyw]
    linarith
  have hsum := add_le_add (hPlus cPlus) (hMinus cMinus)
  rw [hsplit]
  nlinarith

private theorem factorTwoConcreteLowCleanBlock_weightedReserve_of_split
    (d : FactorTwoPhaseLowIndex → ℝ)
    (hPlus : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      weightedCoordinateSquare d c ≤
        c ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix *ᵥ c))
    (hMinus : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      weightedCoordinateSquare d c ≤
        c ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix *ᵥ c))
    (x : FactorTwoPhaseLowIndex → ℝ) :
    weightedCoordinateSquare d x ≤
      x ⬝ᵥ (factorTwoConcreteLowCleanBlockMatrix *ᵥ x) := by
  have hreserve := factorTwoConcreteLowToeplitz_weightedReserve_of_split
    d hPlus hMinus x 0
  have hzero :
      factorTwoPhaseToeplitzCoefficients x 0 ⬝ᵥ
          (factorTwoConcreteLowToeplitzMatrix *ᵥ
            factorTwoPhaseToeplitzCoefficients x 0) =
        (x ⬝ᵥ (factorTwoConcreteLowCleanBlockMatrix *ᵥ x)) / 2 := by
    rw [factorTwoConcreteLowToeplitzMatrix,
      factorTwoPhaseToeplitzBlockMatrix_quadratic]
    simp only [mulVec_zero, dotProduct_zero, add_zero,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  rw [weightedCoordinateSquare_zero, hzero] at hreserve
  linarith

private theorem weightedCoordinateSquare_phase_lifts
    (d : FactorTwoPhaseLowIndex → ℝ)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) :
    weightedCoordinateSquare d (factorTwoPhaseLowCoefficients e 0) +
        weightedCoordinateSquare d
          (factorTwoPhaseLowCoefficients (a • e) (b • o)) +
        weightedCoordinateSquare d (factorTwoPhaseLowCoefficients 0 (-o)) +
        weightedCoordinateSquare d
          (factorTwoPhaseLowCoefficients (b • e) (-a • o)) =
      (1 + a ^ 2 + b ^ 2) *
        weightedCoordinateSquare d (factorTwoPhaseLowCoefficients e o) := by
  rw [weightedCoordinateSquare_lowCoefficients,
    weightedCoordinateSquare_lowCoefficients,
    weightedCoordinateSquare_lowCoefficients,
    weightedCoordinateSquare_lowCoefficients,
    weightedCoordinateSquare_lowCoefficients]
  simp only [weightedCoordinateSquare_zero, add_zero, zero_add]
  rw [weightedCoordinateSquare_smul, weightedCoordinateSquare_smul,
    weightedCoordinateSquare_neg, weightedCoordinateSquare_smul,
    weightedCoordinateSquare_smul]
  ring

private theorem factorTwoConcreteLowPhase_eq_toeplitz_lifts_add_clean_remainder
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) :
    let x := factorTwoPhaseLowCoefficients e o
    let er := factorTwoPhaseLowCoefficients e 0
    let es := factorTwoPhaseLowCoefficients 0 (-o)
    let yr := factorTwoPhaseLowCoefficients (a • e) (b • o)
    let ys := factorTwoPhaseLowCoefficients (b • e) (-a • o)
    let cr := factorTwoPhaseToeplitzCoefficients er yr
    let cs := factorTwoPhaseToeplitzCoefficients es ys
    x ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ x) =
      cr ⬝ᵥ (factorTwoConcreteLowToeplitzMatrix *ᵥ cr) +
        cs ⬝ᵥ (factorTwoConcreteLowToeplitzMatrix *ᵥ cs) +
        ((1 - (a ^ 2 + b ^ 2)) / 2) *
          (x ⬝ᵥ (factorTwoConcreteLowCleanBlockMatrix *ᵥ x)) := by
  dsimp only
  have hphase :
      factorTwoPhaseLowCoefficients e o ⬝ᵥ
          (factorTwoConcreteLowPhaseMatrix a b *ᵥ
            factorTwoPhaseLowCoefficients e o) =
        (e ⬝ᵥ (factorTwoConcreteAdaptedEvenCleanMatrix *ᵥ e) +
          o ⬝ᵥ (factorTwoConcreteOddCleanMatrix *ᵥ o)) +
        a * (e ⬝ᵥ (factorTwoConcreteEvenPerturbationMatrix *ᵥ e) +
          o ⬝ᵥ (factorTwoConcreteOddPerturbationMatrix *ᵥ o)) +
        b * ∑ i, ∑ j,
          e i * factorTwoConcreteAlternatingMatrix i j * o j := by
    simpa only [factorTwoConcreteLowPhaseMatrix] using
      (factorTwoFiniteLowPhaseMatrix_quadratic
        factorTwoConcreteAdaptedEvenCleanMatrix
        factorTwoConcreteEvenPerturbationMatrix
        factorTwoConcreteOddCleanMatrix
        factorTwoConcreteOddPerturbationMatrix
        factorTwoConcreteAlternatingMatrix e o a b)
  have hclean :
      factorTwoPhaseLowCoefficients e o ⬝ᵥ
          (factorTwoConcreteLowCleanBlockMatrix *ᵥ
            factorTwoPhaseLowCoefficients e o) =
        e ⬝ᵥ (factorTwoConcreteAdaptedEvenCleanMatrix *ᵥ e) +
          o ⬝ᵥ (factorTwoConcreteOddCleanMatrix *ᵥ o) := by
    simpa only [factorTwoConcreteLowCleanBlockMatrix, zero_apply, mul_zero,
      zero_mul, Finset.sum_const_zero, add_zero] using
      (factorTwoPhaseBlockMatrix_quadratic
        factorTwoConcreteAdaptedEvenCleanMatrix
        factorTwoConcreteOddCleanMatrix 0 e o)
  have hlift := factorTwoConcreteLowToeplitz_lift_sum e o a b
  dsimp only at hlift
  rw [hphase, hlift, hclean]
  ring

/-- If the two fixed static parity splits dominate the same diagonal
quadratic, then every concrete finite-low phase matrix on the closed disk
dominates that diagonal quadratic with exactly the same weights. -/
theorem factorTwoConcreteLowPhaseMatrix_weightedReserve_of_split
    (d : FactorTwoPhaseLowIndex → ℝ)
    (hPlus : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      ∑ k, d k * c k ^ 2 ≤
        c ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix *ᵥ c))
    (hMinus : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      ∑ k, d k * c k ^ 2 ≤
        c ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix *ᵥ c))
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (c : FactorTwoPhaseLowIndex → ℝ) :
    ∑ k, d k * c k ^ 2 ≤
      c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c) := by
  let e : YoshidaEvenIndex → ℝ := fun i ↦ c (Sum.inl i)
  let o : YoshidaOddIndex → ℝ := fun i ↦ c (Sum.inr i)
  have hc : factorTwoPhaseLowCoefficients e o = c := by
    funext k
    rcases k with i | i <;> rfl
  have hPlus' : ∀ x : FactorTwoPhaseLowIndex → ℝ,
      weightedCoordinateSquare d x ≤
        x ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix *ᵥ x) := by
    exact hPlus
  have hMinus' : ∀ x : FactorTwoPhaseLowIndex → ℝ,
      weightedCoordinateSquare d x ≤
        x ⬝ᵥ (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix *ᵥ x) := by
    exact hMinus
  have hcr := factorTwoConcreteLowToeplitz_weightedReserve_of_split
    d hPlus' hMinus'
    (factorTwoPhaseLowCoefficients e 0)
    (factorTwoPhaseLowCoefficients (a • e) (b • o))
  have hcs := factorTwoConcreteLowToeplitz_weightedReserve_of_split
    d hPlus' hMinus'
    (factorTwoPhaseLowCoefficients 0 (-o))
    (factorTwoPhaseLowCoefficients (b • e) (-a • o))
  have hweights := weightedCoordinateSquare_phase_lifts d e o a b
  have hlifts :
      ((1 + a ^ 2 + b ^ 2) / 2) * weightedCoordinateSquare d c ≤
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
  have hclean := factorTwoConcreteLowCleanBlock_weightedReserve_of_split
    d hPlus' hMinus' c
  have hremainder : 0 ≤ (1 - (a ^ 2 + b ^ 2)) / 2 := by
    linarith
  have hcleanScaled := mul_le_mul_of_nonneg_left hclean hremainder
  have hdecomp :=
    factorTwoConcreteLowPhase_eq_toeplitz_lifts_add_clean_remainder e o a b
  dsimp only at hdecomp
  rw [hc] at hdecomp
  change weightedCoordinateSquare d c ≤
    c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c)
  rw [hdecomp]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowSplitReserveStructural
