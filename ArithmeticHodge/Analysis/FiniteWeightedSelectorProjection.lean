import ArithmeticHodge.Analysis.FiniteGramProjection
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenSelectorGramStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.FiniteWeightedSelectorProjection

open FiniteGramProjection
open ShiftedLegendreLogEnergyOrthogonalProjection
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural
open YoshidaFactorTwoPhaseIntrinsicElevenSelectorGramStructural

noncomputable section

/-- Weighted Gram of a finite family of raw rows. -/
def finiteWeightedGram
    {ι : Type*} [Fintype ι]
    (W : ℝ → ℝ) (F : ι → ℝ → ℝ) : Matrix ι ι ℝ :=
  factorTwoIntrinsicElevenSelectorGram W F (fun _ ↦ (0 : ℝ[X]))

/-- Rectangular weighted cross Gram between two finite row families. -/
def finiteWeightedCrossGram
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : ℝ → ℝ) (F : ι → ℝ → ℝ) (G : κ → ℝ → ℝ) :
    Matrix ι κ ℝ := fun i k ↦
  factorTwoIntrinsicElevenSelectorCrossDual W (F i) (G k) 0 0

/-- The weighted Gram of a disjoint union is the corresponding block Gram. -/
theorem finiteWeightedGram_sum_eq_fromBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : ℝ → ℝ) (F : ι → ℝ → ℝ) (G : κ → ℝ → ℝ) :
    finiteWeightedGram W (Sum.elim F G) =
      Matrix.fromBlocks
        (finiteWeightedGram W F)
        (finiteWeightedCrossGram W F G)
        (finiteWeightedCrossGram W F G)ᴴ
        (finiteWeightedGram W G) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · simp only [finiteWeightedGram, finiteWeightedCrossGram,
      factorTwoIntrinsicElevenSelectorGram,
      Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, star_trivial]
    exact factorTwoIntrinsicElevenSelectorCrossDual_comm
      W (G i) (F j) 0 0
  · rfl

/-- A finite raw-row weighted Gram is positive semidefinite whenever every
normalized row belongs to the weighted `L²` space. -/
theorem finiteWeightedGram_posSemidef_of_memLp
    {ι : Type*} [Fintype ι]
    (W : ℝ → ℝ) (F : ι → ℝ → ℝ)
    (hW : ∀ x ∈ Icc (-1 : ℝ) 1, 0 < W x)
    (hF : ∀ i, MemLp (fun x ↦ F i x / Real.sqrt (W x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1))) :
    (finiteWeightedGram W F).PosSemidef := by
  unfold finiteWeightedGram
  apply factorTwoIntrinsicElevenSelectorGram_posSemidef W F
    (fun _ ↦ (0 : ℝ[X])) hW
  intro i j
  have hi : MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual (F i) 0 x /
        Real.sqrt (W x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa [factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift] using
      hF i
  have hj : MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual (F j) 0 x /
        Real.sqrt (W x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa [factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift] using
      hF j
  simpa [factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift] using
    intervalIntegrable_selectorCross_of_memLp
      W (F i) (F j) (0 : ℝ[X]) (0 : ℝ[X]) hW hi hj

/-- Inverse-free weighted Bessel certificate.  For any exact coefficient
matrix `C`, the displayed completion-of-squares Gram is a sound lower bound
for the target Gram. -/
theorem finiteWeightedProjectionResidual_posSemidef
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (W : ℝ → ℝ) (F : ι → ℝ → ℝ) (G : κ → ℝ → ℝ)
    (hW : ∀ x ∈ Icc (-1 : ℝ) 1, 0 < W x)
    (hF : ∀ i, MemLp (fun x ↦ F i x / Real.sqrt (W x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hG : ∀ k, MemLp (fun x ↦ G k x / Real.sqrt (W x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (C : Matrix ι κ ℝ) :
    (finiteWeightedGram W F -
      (finiteWeightedCrossGram W F G * Cᴴ +
        C * (finiteWeightedCrossGram W F G)ᴴ -
        C * finiteWeightedGram W G * Cᴴ)).PosSemidef := by
  apply residualGram_posSemidef
  rw [← finiteWeightedGram_sum_eq_fromBlocks]
  apply finiteWeightedGram_posSemidef_of_memLp W (Sum.elim F G) hW
  intro i
  rcases i with i | i
  · exact hF i
  · exact hG i

end

end ArithmeticHodge.Analysis.FiniteWeightedSelectorProjection
