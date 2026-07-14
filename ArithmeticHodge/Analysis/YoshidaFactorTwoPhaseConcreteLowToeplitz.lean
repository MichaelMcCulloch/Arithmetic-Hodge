import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowDiskSchur

set_option autoImplicit false
set_option maxRecDepth 100000

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowToeplitz

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
open YoshidaFactorTwoPhaseConcreteCleanOddMatrix
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseConcreteLowDiskSchur
open YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur

/-!
# A static Toeplitz certificate for the concrete low phase disk

The disk family `Q + a P + b R` can be certified by one real symmetric
matrix, with no parameter subdivision.  The certificate is the real form of
the degree-one matrix Fejer--Riesz block

```text
  1/2 * [[Q, P - i R], [P + i R, Q]].
```

The even--odd bipartition turns this complex block into the real oriented
matrix below.  Positive semidefiniteness of the resulting `420 x 420` matrix
implies positive semidefiniteness of every concrete `210 x 210` phase matrix
on `a^2 + b^2 <= 1`.
-/

/-- Two copies of one finite coordinate space. -/
abbrev FactorTwoPhaseToeplitzIndex :=
  FactorTwoPhaseLowIndex ⊕ FactorTwoPhaseLowIndex

/-- Pack two vectors into the doubled coordinate space. -/
def factorTwoPhaseToeplitzCoefficients
    {n : Type*} (x y : n → ℝ) : n ⊕ n → ℝ :=
  Sum.elim x y

/-- The real two-copy Toeplitz block with diagonal `Q/2`, upper-right
`B/2`, and lower-left `Bᵀ/2`. -/
def factorTwoPhaseToeplitzBlockMatrix
    {n : Type*} (Q B : Matrix n n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ
  | Sum.inl i, Sum.inl j => Q i j / 2
  | Sum.inl i, Sum.inr j => B i j / 2
  | Sum.inr i, Sum.inl j => B j i / 2
  | Sum.inr i, Sum.inr j => Q i j / 2

/-- Exact quadratic expansion of the generic two-copy Toeplitz block. -/
theorem factorTwoPhaseToeplitzBlockMatrix_quadratic
    {n : Type*} [Fintype n]
    (Q B : Matrix n n ℝ) (x y : n → ℝ) :
    let c := factorTwoPhaseToeplitzCoefficients x y
    c ⬝ᵥ (factorTwoPhaseToeplitzBlockMatrix Q B *ᵥ c) =
      (x ⬝ᵥ (Q *ᵥ x) + y ⬝ᵥ (Q *ᵥ y)) / 2 +
        ∑ i, ∑ j, x i * B i j * y j := by
  classical
  have hcrossLeft :
      (∑ i, x i * ∑ j, (B i j / 2) * y j) =
        (∑ i, ∑ j, x i * B i j * y j) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hcrossRight :
      (∑ j, y j * ∑ i, (B i j / 2) * x i) =
        (∑ i, ∑ j, x i * B i j * y j) / 2 := by
    rw [Finset.sum_div]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hdiag (v : n → ℝ) :
      (∑ i, v i * ∑ j, (Q i j / 2) * v j) =
        (v ⬝ᵥ (Q *ᵥ v)) / 2 := by
    calc
      (∑ i, v i * ∑ j, (Q i j / 2) * v j) =
          ∑ i, ∑ j, (v i * Q i j * v j) / 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = ∑ i, (∑ j, v i * Q i j * v j) / 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (Finset.sum_div Finset.univ
          (fun j ↦ v i * Q i j * v j) 2).symm
      _ = (∑ i, ∑ j, v i * Q i j * v j) / 2 :=
        (Finset.sum_div Finset.univ
          (fun i ↦ ∑ j, v i * Q i j * v j) 2).symm
      _ = _ := by
        simp only [dotProduct, mulVec]
        congr 1
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
  simp only [dotProduct, mulVec, factorTwoPhaseToeplitzCoefficients]
  simp_rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr,
    factorTwoPhaseToeplitzBlockMatrix, mul_add,
    Finset.sum_add_distrib]
  rw [hdiag x, hcrossLeft, hcrossRight, hdiag y]
  simp only [dotProduct, mulVec]
  ring

/-- The clean block `Q` on the packed even--odd coordinate space. -/
def factorTwoConcreteLowCleanBlockMatrix :
    Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ :=
  factorTwoPhaseBlockMatrix
    factorTwoConcreteAdaptedEvenCleanMatrix
    factorTwoConcreteOddCleanMatrix 0

/-- The real form of `P - i R`.  Its lower-left alternating block has the
opposite sign from its upper-right block. -/
def factorTwoConcreteLowOrientedMatrix :
    Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ
  | Sum.inl i, Sum.inl j => factorTwoConcreteEvenPerturbationMatrix i j
  | Sum.inl i, Sum.inr j => factorTwoConcreteAlternatingMatrix i j / 2
  | Sum.inr i, Sum.inl j => -factorTwoConcreteAlternatingMatrix j i / 2
  | Sum.inr i, Sum.inr j => factorTwoConcreteOddPerturbationMatrix i j

/-- The one static `420 x 420` real Toeplitz matrix whose positivity
certifies the whole concrete low phase disk. -/
def factorTwoConcreteLowToeplitzMatrix :
    Matrix FactorTwoPhaseToeplitzIndex FactorTwoPhaseToeplitzIndex ℝ :=
  factorTwoPhaseToeplitzBlockMatrix
    factorTwoConcreteLowCleanBlockMatrix
    factorTwoConcreteLowOrientedMatrix

/-- Symmetry of the concrete even perturbation block. -/
theorem factorTwoConcreteEvenPerturbationMatrix_isHermitian :
    factorTwoConcreteEvenPerturbationMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [factorTwoConcreteEvenPerturbationMatrix, star_trivial]
  rw [factorTwoCenteredSymmetricPerturbationBilinear_eq_polarization
      _ _ (continuous_factorTwoCenteredAdaptedEvenLowProfile j)
        (continuous_factorTwoCenteredAdaptedEvenLowProfile i),
    factorTwoCenteredSymmetricPerturbationBilinear_eq_polarization
      _ _ (continuous_factorTwoCenteredAdaptedEvenLowProfile i)
        (continuous_factorTwoCenteredAdaptedEvenLowProfile j),
    factorTwoCenteredSymmetricPerturbationPolarization_comm]

/-- Symmetry of the concrete odd perturbation block. -/
theorem factorTwoConcreteOddPerturbationMatrix_isHermitian :
    factorTwoConcreteOddPerturbationMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [factorTwoConcreteOddPerturbationMatrix, star_trivial]
  rw [factorTwoCenteredSymmetricPerturbationBilinear_eq_polarization
      _ _ (continuous_factorTwoCenteredOddLowProfile j)
        (continuous_factorTwoCenteredOddLowProfile i),
    factorTwoCenteredSymmetricPerturbationBilinear_eq_polarization
      _ _ (continuous_factorTwoCenteredOddLowProfile i)
        (continuous_factorTwoCenteredOddLowProfile j),
    factorTwoCenteredSymmetricPerturbationPolarization_comm]

private theorem add_smul_isHermitian_real
    {n : Type*}
    {Q P : Matrix n n ℝ} (hQ : Q.IsHermitian) (hP : P.IsHermitian)
    (a : ℝ) : (Q + a • P).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hq := hQ.apply i j
  have hp := hP.apply i j
  simpa only [add_apply, smul_apply, smul_eq_mul, star_trivial] using
    congrArg₂ (fun x y : ℝ ↦ x + a * y) hq hp

/-- Every concrete low phase matrix is Hermitian. -/
theorem factorTwoConcreteLowPhaseMatrix_isHermitian (a b : ℝ) :
    (factorTwoConcreteLowPhaseMatrix a b).IsHermitian := by
  unfold factorTwoConcreteLowPhaseMatrix factorTwoFiniteLowPhaseMatrix
  apply factorTwoPhaseBlockMatrix_isHermitian
  · exact add_smul_isHermitian_real
      factorTwoConcreteAdaptedEvenCleanMatrix_isHermitian
      factorTwoConcreteEvenPerturbationMatrix_isHermitian a
  · exact add_smul_isHermitian_real
      factorTwoConcreteOddCleanMatrix_isHermitian
      factorTwoConcreteOddPerturbationMatrix_isHermitian a

private theorem factorTwoConcreteLowOrientedMatrix_cross
    (e₁ e₂ : YoshidaEvenIndex → ℝ)
    (o₁ o₂ : YoshidaOddIndex → ℝ) :
    let x := factorTwoPhaseLowCoefficients e₁ o₁
    let y := factorTwoPhaseLowCoefficients e₂ o₂
    ∑ i, ∑ j, x i * factorTwoConcreteLowOrientedMatrix i j * y j =
      e₁ ⬝ᵥ (factorTwoConcreteEvenPerturbationMatrix *ᵥ e₂) +
        o₁ ⬝ᵥ (factorTwoConcreteOddPerturbationMatrix *ᵥ o₂) +
        (∑ i, ∑ j,
          e₁ i * factorTwoConcreteAlternatingMatrix i j * o₂ j) / 2 -
        (∑ i, ∑ j,
          e₂ i * factorTwoConcreteAlternatingMatrix i j * o₁ j) / 2 := by
  classical
  have hupper :
      (∑ i, ∑ j,
        e₁ i * (factorTwoConcreteAlternatingMatrix i j / 2) * o₂ j) =
        (∑ i, ∑ j,
          e₁ i * factorTwoConcreteAlternatingMatrix i j * o₂ j) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hreindex :
      (∑ j, ∑ i,
        o₁ j * factorTwoConcreteAlternatingMatrix i j * e₂ i) =
        ∑ i, ∑ j,
          e₂ i * factorTwoConcreteAlternatingMatrix i j * o₁ j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hlower :
      (∑ j, ∑ i,
        o₁ j * (-factorTwoConcreteAlternatingMatrix i j / 2) * e₂ i) =
        -(∑ i, ∑ j,
          e₂ i * factorTwoConcreteAlternatingMatrix i j * o₁ j) / 2 := by
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
    factorTwoConcreteLowOrientedMatrix,
    Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  rw [hupper, hlower]
  ring

private theorem factorTwoConcreteLowCleanBlockMatrix_quadratic
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ) :
    let x := factorTwoPhaseLowCoefficients e o
    x ⬝ᵥ (factorTwoConcreteLowCleanBlockMatrix *ᵥ x) =
      e ⬝ᵥ (factorTwoConcreteAdaptedEvenCleanMatrix *ᵥ e) +
        o ⬝ᵥ (factorTwoConcreteOddCleanMatrix *ᵥ o) := by
  simpa only [factorTwoConcreteLowCleanBlockMatrix, zero_apply, mul_zero,
    zero_mul,
    Finset.sum_const_zero, add_zero] using
    factorTwoPhaseBlockMatrix_quadratic
      factorTwoConcreteAdaptedEvenCleanMatrix
      factorTwoConcreteOddCleanMatrix 0 e o

private theorem matrix_quadratic_smul
    {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (c : ℝ) (x : n → ℝ) :
    (c • x) ⬝ᵥ (M *ᵥ (c • x)) = c ^ 2 * (x ⬝ᵥ (M *ᵥ x)) := by
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

/-- The sum of the two real Toeplitz lifts equals the phase quadratic with
only `(1 + a^2 + b^2)/2` of the clean diagonal. -/
theorem factorTwoConcreteLowToeplitz_lift_sum
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) :
    let er : FactorTwoPhaseLowIndex → ℝ :=
      factorTwoPhaseLowCoefficients e 0
    let es : FactorTwoPhaseLowIndex → ℝ :=
      factorTwoPhaseLowCoefficients 0 (-o)
    let yr : FactorTwoPhaseLowIndex → ℝ :=
      factorTwoPhaseLowCoefficients (a • e) (b • o)
    let ys : FactorTwoPhaseLowIndex → ℝ :=
      factorTwoPhaseLowCoefficients (b • e) (-a • o)
    let cr := factorTwoPhaseToeplitzCoefficients er yr
    let cs := factorTwoPhaseToeplitzCoefficients es ys
    cr ⬝ᵥ (factorTwoConcreteLowToeplitzMatrix *ᵥ cr) +
        cs ⬝ᵥ (factorTwoConcreteLowToeplitzMatrix *ᵥ cs) =
      ((1 + a ^ 2 + b ^ 2) / 2) *
          (e ⬝ᵥ (factorTwoConcreteAdaptedEvenCleanMatrix *ᵥ e) +
            o ⬝ᵥ (factorTwoConcreteOddCleanMatrix *ᵥ o)) +
        a * (e ⬝ᵥ (factorTwoConcreteEvenPerturbationMatrix *ᵥ e) +
          o ⬝ᵥ (factorTwoConcreteOddPerturbationMatrix *ᵥ o)) +
        b * ∑ i, ∑ j,
          e i * factorTwoConcreteAlternatingMatrix i j * o j := by
  have hcross_smul :
      (∑ i, ∑ j,
        b * e i * factorTwoConcreteAlternatingMatrix i j * o j) =
        b * ∑ i, ∑ j,
          e i * factorTwoConcreteAlternatingMatrix i j * o j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hcross_right_smul :
      (∑ i, ∑ j,
        e i * factorTwoConcreteAlternatingMatrix i j * (b * o j)) =
        b * ∑ i, ∑ j,
          e i * factorTwoConcreteAlternatingMatrix i j * o j := by
    calc
      (∑ i, ∑ j,
          e i * factorTwoConcreteAlternatingMatrix i j * (b * o j)) =
          ∑ i, ∑ j,
            b * e i * factorTwoConcreteAlternatingMatrix i j * o j := by
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = _ := hcross_smul
  have hcross_left_smul_neg :
      (∑ i, ∑ j,
        b * e i * factorTwoConcreteAlternatingMatrix i j * (-o j)) =
        -(b * ∑ i, ∑ j,
          e i * factorTwoConcreteAlternatingMatrix i j * o j) := by
    calc
      (∑ i, ∑ j,
          b * e i * factorTwoConcreteAlternatingMatrix i j * (-o j)) =
          ∑ i, ∑ j,
            -(b * e i * factorTwoConcreteAlternatingMatrix i j * o j) := by
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = -(∑ i, ∑ j,
          b * e i * factorTwoConcreteAlternatingMatrix i j * o j) := by
        simp only [Finset.sum_neg_distrib]
      _ = _ := by rw [hcross_smul]
  dsimp only
  rw [factorTwoConcreteLowToeplitzMatrix,
    factorTwoPhaseToeplitzBlockMatrix_quadratic,
    factorTwoPhaseToeplitzBlockMatrix_quadratic]
  rw [factorTwoConcreteLowCleanBlockMatrix_quadratic,
    factorTwoConcreteLowCleanBlockMatrix_quadratic,
    factorTwoConcreteLowCleanBlockMatrix_quadratic,
    factorTwoConcreteLowCleanBlockMatrix_quadratic]
  rw [factorTwoConcreteLowOrientedMatrix_cross,
    factorTwoConcreteLowOrientedMatrix_cross]
  simp only [zero_dotProduct, mulVec_zero, dotProduct_zero,
    mulVec_smul, mulVec_neg,
    smul_dotProduct, dotProduct_smul, neg_dotProduct, dotProduct_neg,
    zero_add, add_zero, smul_eq_mul, Pi.smul_apply, Pi.neg_apply,
    Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]
  rw [hcross_right_smul, hcross_left_smul_neg]
  ring

/-- One static Toeplitz PSD certificate closes the concrete finite-low phase
for every point of the Euclidean disk. -/
theorem factorTwoConcreteLowPhase_nonneg_of_toeplitz_posSemidef
    (hToeplitz : factorTwoConcreteLowToeplitzMatrix.PosSemidef)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoAdaptedEvenLowSynthesis e)
      (factorTwoOddLowSynthesis o) a b := by
  let er : FactorTwoPhaseLowIndex → ℝ :=
    factorTwoPhaseLowCoefficients e 0
  let es : FactorTwoPhaseLowIndex → ℝ :=
    factorTwoPhaseLowCoefficients 0 (-o)
  let yr : FactorTwoPhaseLowIndex → ℝ :=
    factorTwoPhaseLowCoefficients (a • e) (b • o)
  let ys : FactorTwoPhaseLowIndex → ℝ :=
    factorTwoPhaseLowCoefficients (b • e) (-a • o)
  let cr := factorTwoPhaseToeplitzCoefficients er yr
  let cs := factorTwoPhaseToeplitzCoefficients es ys
  have hcr : 0 ≤ cr ⬝ᵥ (factorTwoConcreteLowToeplitzMatrix *ᵥ cr) :=
    hToeplitz.dotProduct_mulVec_nonneg cr
  have hcs : 0 ≤ cs ⬝ᵥ (factorTwoConcreteLowToeplitzMatrix *ᵥ cs) :=
    hToeplitz.dotProduct_mulVec_nonneg cs
  have hsum :
      0 ≤ ((1 + a ^ 2 + b ^ 2) / 2) *
          (e ⬝ᵥ (factorTwoConcreteAdaptedEvenCleanMatrix *ᵥ e) +
            o ⬝ᵥ (factorTwoConcreteOddCleanMatrix *ᵥ o)) +
        a * (e ⬝ᵥ (factorTwoConcreteEvenPerturbationMatrix *ᵥ e) +
          o ⬝ᵥ (factorTwoConcreteOddPerturbationMatrix *ᵥ o)) +
        b * ∑ i, ∑ j,
          e i * factorTwoConcreteAlternatingMatrix i j * o j := by
    rw [← factorTwoConcreteLowToeplitz_lift_sum e o a b]
    exact add_nonneg hcr hcs
  let x := factorTwoPhaseLowCoefficients e o
  let z := factorTwoPhaseToeplitzCoefficients x 0
  have hz : 0 ≤ z ⬝ᵥ (factorTwoConcreteLowToeplitzMatrix *ᵥ z) :=
    hToeplitz.dotProduct_mulVec_nonneg z
  have hclean :
      0 ≤ e ⬝ᵥ (factorTwoConcreteAdaptedEvenCleanMatrix *ᵥ e) +
        o ⬝ᵥ (factorTwoConcreteOddCleanMatrix *ᵥ o) := by
    have hz' : 0 ≤
        (e ⬝ᵥ (factorTwoConcreteAdaptedEvenCleanMatrix *ᵥ e) +
          o ⬝ᵥ (factorTwoConcreteOddCleanMatrix *ᵥ o)) / 2 := by
      simpa only [z, x, factorTwoConcreteLowToeplitzMatrix,
        factorTwoPhaseToeplitzBlockMatrix_quadratic,
        factorTwoConcreteLowCleanBlockMatrix_quadratic,
        zero_dotProduct, mulVec_zero, dotProduct_zero, add_zero,
        Pi.zero_apply, mul_zero, Finset.sum_const_zero]
        using hz
    linarith
  have hremainder :
      0 ≤ ((1 - (a ^ 2 + b ^ 2)) / 2) *
        (e ⬝ᵥ (factorTwoConcreteAdaptedEvenCleanMatrix *ᵥ e) +
          o ⬝ᵥ (factorTwoConcreteOddCleanMatrix *ᵥ o)) :=
    mul_nonneg (by linarith) hclean
  rw [factorTwoConcreteLowPhase_eq_pencils]
  unfold factorTwoConcreteEvenPencilValue
    factorTwoConcreteOddPencilValue factorTwoConcreteAlternatingValue
  simp only [add_mulVec, smul_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  nlinarith

/-- The static Toeplitz certificate implies positive semidefiniteness of
each concrete `210 x 210` matrix on the full phase disk. -/
theorem factorTwoConcreteLowPhaseMatrix_posSemidef_of_toeplitz
    (hToeplitz : factorTwoConcreteLowToeplitzMatrix.PosSemidef)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (factorTwoConcreteLowPhaseMatrix a b).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (factorTwoConcreteLowPhaseMatrix_isHermitian a b)
  intro x
  let e : YoshidaEvenIndex → ℝ := fun i ↦ x (Sum.inl i)
  let o : YoshidaOddIndex → ℝ := fun i ↦ x (Sum.inr i)
  have hx : factorTwoPhaseLowCoefficients e o = x := by
    funext i
    cases i <;> rfl
  have hnonneg :=
    factorTwoConcreteLowPhase_nonneg_of_toeplitz_posSemidef
      hToeplitz e o a b hab
  rw [factorTwoConcreteLowPhaseMatrix_represents] at hnonneg
  simpa only [hx] using hnonneg

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowToeplitz
