import ArithmeticHodge.Analysis.FiniteBilinearGramProjectionStructural
import ArithmeticHodge.Analysis.FiniteIntervalWeightedGramTraceStructural
import ArithmeticHodge.Analysis.FiniteWeightedSelectorProjection

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.FiniteWeightedSelectorProjectionResidualStructural

open FiniteBilinearGramProjectionStructural
open FiniteGramProjection
open FiniteIntervalWeightedGramTraceStructural
open FiniteWeightedSelectorProjection
open ShiftedLegendreLogEnergyOrthogonalProjection
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural
open YoshidaFactorTwoPhaseIntrinsicElevenSelectorGramStructural

noncomputable section

/-!
# Residual rows for finite weighted selector projections

The completion-of-squares projection defect is itself the weighted Gram of
the coefficient-contracted residual rows.  This turns its trace into one
integral of a finite sum of squared residuals, rather than a table of cross
moments.
-/

/-- Synthesis of a finite row family by the columns of a coefficient
matrix. -/
def finiteWeightedSynthesis
    {sigma iota : Type*} [Fintype sigma]
    (H : sigma -> Real -> Real) (A : Matrix sigma iota Real) :
    iota -> Real -> Real := fun i x =>
  ∑ s, A s i * H s x

/-- A weighted Gram commutes with finite linear synthesis. -/
theorem finiteWeightedGram_synthesis
    {sigma iota : Type*} [Fintype sigma] [Fintype iota]
    (W : Real -> Real) (H : sigma -> Real -> Real)
    (A : Matrix sigma iota Real)
    (hInt : ∀ s t, IntervalIntegrable
      (fun x => H s x * H t x / W x) volume (-1) 1) :
    finiteWeightedGram W (finiteWeightedSynthesis H A) =
      A.conjTranspose * finiteWeightedGram W H * A := by
  classical
  ext i j
  simp only [finiteWeightedGram, factorTwoIntrinsicElevenSelectorGram,
    factorTwoIntrinsicElevenSelectorCrossDual,
    factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift,
    Polynomial.eval_zero, sub_zero, finiteWeightedSynthesis]
  rw [show (fun x : Real =>
      (∑ s, A s i * H s x) * (∑ t, A t j * H t x) / W x) =
      fun x => ∑ s, ∑ t,
        (A s i * A t j) * (H s x * H t x / W x) by
    funext x
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_div]
    simp_rw [Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _hs
    apply Finset.sum_congr rfl
    intro t _ht
    ring_nf]
  rw [intervalIntegral.integral_finset_sum]
  · have hInner (s : sigma) :
        (∫ x : Real in -1..1, ∑ t,
          (A s i * A t j) * (H s x * H t x / W x)) =
        ∑ t, ∫ x : Real in -1..1,
          (A s i * A t j) * (H s x * H t x / W x) := by
      apply intervalIntegral.integral_finset_sum
      intro t _ht
      exact (hInt s t).const_mul (A s i * A t j)
    simp_rw [hInner]
    simp_rw [intervalIntegral.integral_const_mul]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
      factorTwoIntrinsicElevenSelectorGram,
      factorTwoIntrinsicElevenSelectorCrossDual,
      factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift,
      Polynomial.eval_zero, sub_zero]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _ht
    apply Finset.sum_congr rfl
    intro s _hs
    ring
  · intro s _hs
    have hs := IntervalIntegrable.sum Finset.univ fun t _ht =>
      (hInt s t).const_mul (A s i * A t j)
    convert hs using 1
    funext x
    simp only [Finset.sum_apply]

/-- The weighted projection defect is exactly the weighted Gram of the
coefficient-contracted residual rows. -/
theorem finiteWeightedGram_projectionResidualRow_eq
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq iota]
    (W : Real -> Real) (F : iota -> Real -> Real)
    (G : kappa -> Real -> Real)
    (hW : ∀ x ∈ Icc (-1 : Real) 1, 0 < W x)
    (hF : ∀ i, MemLp (fun x => F i x / Real.sqrt (W x)) 2
      (volume.restrict (Ioc (-1 : Real) 1)))
    (hG : ∀ k, MemLp (fun x => G k x / Real.sqrt (W x)) 2
      (volume.restrict (Ioc (-1 : Real) 1)))
    (C : Matrix iota kappa Real) :
    finiteWeightedGram W (finiteProjectionResidualRow F G C) =
      finiteWeightedGram W F -
        (finiteWeightedCrossGram W F G * C.conjTranspose +
          C * (finiteWeightedCrossGram W F G).conjTranspose -
          C * finiteWeightedGram W G * C.conjTranspose) := by
  classical
  let H : (iota ⊕ kappa) -> Real -> Real := Sum.elim F G
  have hH : ∀ s t, IntervalIntegrable
      (fun x => H s x * H t x / W x) volume (-1) 1 := by
    intro s t
    rcases s with i | k <;> rcases t with j | l
    · simpa [H, factorTwoIntrinsicElevenSelectorResidual,
        centeredPolynomialLift] using intervalIntegrable_selectorCross_of_memLp
        W (F i) (F j) 0 0 hW (by
          simpa [factorTwoIntrinsicElevenSelectorResidual,
            centeredPolynomialLift] using hF i) (by
          simpa [factorTwoIntrinsicElevenSelectorResidual,
            centeredPolynomialLift] using hF j)
    · simpa [H, factorTwoIntrinsicElevenSelectorResidual,
        centeredPolynomialLift] using intervalIntegrable_selectorCross_of_memLp
        W (F i) (G l) 0 0 hW (by
          simpa [factorTwoIntrinsicElevenSelectorResidual,
            centeredPolynomialLift] using hF i) (by
          simpa [factorTwoIntrinsicElevenSelectorResidual,
            centeredPolynomialLift] using hG l)
    · simpa [H, factorTwoIntrinsicElevenSelectorResidual,
        centeredPolynomialLift] using intervalIntegrable_selectorCross_of_memLp
        W (G k) (F j) 0 0 hW (by
          simpa [factorTwoIntrinsicElevenSelectorResidual,
            centeredPolynomialLift] using hG k) (by
          simpa [factorTwoIntrinsicElevenSelectorResidual,
            centeredPolynomialLift] using hF j)
    · simpa [H, factorTwoIntrinsicElevenSelectorResidual,
        centeredPolynomialLift] using intervalIntegrable_selectorCross_of_memLp
        W (G k) (G l) 0 0 hW (by
          simpa [factorTwoIntrinsicElevenSelectorResidual,
            centeredPolynomialLift] using hG k) (by
          simpa [factorTwoIntrinsicElevenSelectorResidual,
            centeredPolynomialLift] using hG l)
  calc
    finiteWeightedGram W (finiteProjectionResidualRow F G C) =
        finiteWeightedGram W
          (finiteWeightedSynthesis H (residualEmbedding C)) := by
      congr 1
      funext i x
      simp [finiteProjectionResidualRow, finiteWeightedSynthesis, H,
        residualEmbedding, Matrix.one_apply, sub_eq_add_neg]
    _ = (residualEmbedding C).conjTranspose *
          finiteWeightedGram W H * residualEmbedding C :=
      finiteWeightedGram_synthesis W H (residualEmbedding C) hH
    _ = (residualEmbedding C).conjTranspose *
          Matrix.fromBlocks
            (finiteWeightedGram W F)
            (finiteWeightedCrossGram W F G)
            (finiteWeightedCrossGram W F G).conjTranspose
            (finiteWeightedGram W G) * residualEmbedding C := by
      rw [finiteWeightedGram_sum_eq_fromBlocks]
    _ = _ := residualEmbedding_conjTranspose_mul_fromBlocks_mul
      (finiteWeightedGram W F) (finiteWeightedCrossGram W F G) C
      (finiteWeightedGram W G)

/-- The selector-weighted Gram is the corresponding interval weighted Gram. -/
theorem finiteWeightedGram_eq_finiteIntervalWeightedGram
    {iota : Type*} [Fintype iota]
    (W : Real -> Real) (F : iota -> Real -> Real) :
    finiteWeightedGram W F = finiteIntervalWeightedGram (-1) 1 W F := by
  ext i j
  simp [finiteWeightedGram, finiteIntervalWeightedGram,
    factorTwoIntrinsicElevenSelectorGram,
    factorTwoIntrinsicElevenSelectorCrossDual,
    factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift]

end

end ArithmeticHodge.Analysis.FiniteWeightedSelectorProjectionResidualStructural
