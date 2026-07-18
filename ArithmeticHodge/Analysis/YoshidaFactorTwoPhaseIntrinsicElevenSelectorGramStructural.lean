import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenSelectorGramStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural

noncomputable section

/-!
# Finite selector Gram synthesis

A finite linear combination of selector residuals has weighted dual cost
equal to the quadratic form of its full polarized Gram.  The statement is
dimension-independent; in particular it packages the retained three-row
whole square without committing the later cutoff-eleven argument to a
`3 x 3` expansion.
-/

/-- Full polarized weighted Gram of a finite selector family. -/
def factorTwoIntrinsicElevenSelectorGram
    {ι : Type*} [Fintype ι]
    (W : ℝ → ℝ) (F : ι → ℝ → ℝ) (q : ι → ℝ[X]) :
    Matrix ι ι ℝ := fun i j ↦
  factorTwoIntrinsicElevenSelectorCrossDual W (F i) (F j) (q i) (q j)

/-- Polarized selector pairings are symmetric over the real scalars. -/
theorem factorTwoIntrinsicElevenSelectorCrossDual_comm
    (W F G : ℝ → ℝ) (p q : ℝ[X]) :
    factorTwoIntrinsicElevenSelectorCrossDual W F G p q =
      factorTwoIntrinsicElevenSelectorCrossDual W G F q p := by
  unfold factorTwoIntrinsicElevenSelectorCrossDual
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

/-- Linear synthesis of a finite representer family. -/
def factorTwoIntrinsicElevenSelectorRepresenterSum
    {ι : Type*} [Fintype ι]
    (F : ι → ℝ → ℝ) (c : ι → ℝ) : ℝ → ℝ := fun x ↦
  ∑ i, c i * F i x

/-- Linear synthesis of the matching finite polynomial selectors. -/
def factorTwoIntrinsicElevenSelectorPolynomialSum
    {ι : Type*} [Fintype ι]
    (q : ι → ℝ[X]) (c : ι → ℝ) : ℝ[X] :=
  ∑ i, c i • q i

/-- Selector residual formation commutes exactly with finite linear
synthesis. -/
theorem factorTwoIntrinsicElevenSelectorResidual_sum
    {ι : Type*} [Fintype ι]
    (F : ι → ℝ → ℝ) (q : ι → ℝ[X]) (c : ι → ℝ) (x : ℝ) :
    factorTwoIntrinsicElevenSelectorResidual
        (factorTwoIntrinsicElevenSelectorRepresenterSum F c)
        (factorTwoIntrinsicElevenSelectorPolynomialSum q c) x =
      ∑ i, c i * factorTwoIntrinsicElevenSelectorResidual (F i) (q i) x := by
  classical
  unfold factorTwoIntrinsicElevenSelectorResidual
    factorTwoIntrinsicElevenSelectorRepresenterSum
    factorTwoIntrinsicElevenSelectorPolynomialSum centeredPolynomialLift
  rw [Polynomial.eval_finset_sum]
  simp_rw [Polynomial.eval_smul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [smul_eq_mul]
  ring

/-- The weighted square of a finite residual synthesis is the quadratic form
of its polarized Gram. -/
theorem factorTwoIntrinsicElevenSelectorDual_sum_eq_matrixQuadratic
    {ι : Type*} [Fintype ι]
    (W : ℝ → ℝ) (F : ι → ℝ → ℝ) (q : ι → ℝ[X])
    (hInt : ∀ i j, IntervalIntegrable
      (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual (F i) (q i) x *
          factorTwoIntrinsicElevenSelectorResidual (F j) (q j) x / W x)
      volume (-1) 1)
    (c : ι → ℝ) :
    factorTwoIntrinsicElevenSelectorDual W
        (factorTwoIntrinsicElevenSelectorRepresenterSum F c)
        (factorTwoIntrinsicElevenSelectorPolynomialSum q c) =
      star c ⬝ᵥ (factorTwoIntrinsicElevenSelectorGram W F q *ᵥ c) := by
  classical
  let R : ι → ℝ → ℝ := fun i ↦
    factorTwoIntrinsicElevenSelectorResidual (F i) (q i)
  unfold factorTwoIntrinsicElevenSelectorDual
  rw [show (fun x : ℝ ↦
      factorTwoIntrinsicElevenSelectorResidual
          (factorTwoIntrinsicElevenSelectorRepresenterSum F c)
          (factorTwoIntrinsicElevenSelectorPolynomialSum q c) x ^ 2 / W x) =
      fun x ↦ ∑ i, ∑ j, (c i * c j) * (R i x * R j x / W x) by
    funext x
    rw [factorTwoIntrinsicElevenSelectorResidual_sum]
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    dsimp only [R]
    ring]
  rw [intervalIntegral.integral_finset_sum]
  · simp only [dotProduct, mulVec,
      factorTwoIntrinsicElevenSelectorGram, star_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j _hj
      rw [intervalIntegral.integral_const_mul]
      unfold factorTwoIntrinsicElevenSelectorCrossDual
      dsimp only [R]
      ring
    · intro j _hj
      exact (hInt i j).const_mul (c i * c j)
  · intro i _hi
    have hsum := IntervalIntegrable.sum Finset.univ fun j _hj ↦
      (hInt i j).const_mul (c i * c j)
    convert hsum using 1
    funext x
    simp only [Finset.sum_apply, R]

/-- Every finite weighted selector Gram is positive semidefinite once its
polarized entries are integrable and the weight is positive on the endpoint
interval. -/
theorem factorTwoIntrinsicElevenSelectorGram_posSemidef
    {ι : Type*} [Fintype ι]
    (W : ℝ → ℝ) (F : ι → ℝ → ℝ) (q : ι → ℝ[X])
    (hW : ∀ x ∈ Icc (-1 : ℝ) 1, 0 < W x)
    (hInt : ∀ i j, IntervalIntegrable
      (fun x ↦
        factorTwoIntrinsicElevenSelectorResidual (F i) (q i) x *
          factorTwoIntrinsicElevenSelectorResidual (F j) (q j) x / W x)
      volume (-1) 1) :
    (factorTwoIntrinsicElevenSelectorGram W F q).PosSemidef := by
  have hHermitian :
      (factorTwoIntrinsicElevenSelectorGram W F q).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa [factorTwoIntrinsicElevenSelectorGram] using
      (factorTwoIntrinsicElevenSelectorCrossDual_comm
        W (F i) (F j) (q i) (q j)).symm
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHermitian
  intro c
  have hquad := factorTwoIntrinsicElevenSelectorDual_sum_eq_matrixQuadratic
    W F q hInt c
  rw [← hquad]
  exact factorTwoIntrinsicElevenSelectorDual_nonneg _ _ _ hW

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenSelectorGramStructural
