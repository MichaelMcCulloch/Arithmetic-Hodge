import ArithmeticHodge.Analysis.RationalIntervalSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowSplitToeplitz

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowSplitCertificate

noncomputable section

open ArithmeticHodge.Analysis
open RatInterval
open RationalIntervalSchur
open YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
open YoshidaFactorTwoPhaseConcreteLowSplitToeplitz
open YoshidaFactorTwoPhaseLowSchur

/-!
# Interval-certificate boundary for the concrete low split

This module isolates the exact finite computation still needed by the
factor-two low-phase argument.  Any rational interval matrices containing the
two concrete parity splits, with kernel-checked positive Schur pivots in the
order below, certify every phase in the closed disk.
-/

/-- Natural even-then-odd elimination order for the concrete `200 + 10`
coordinate space. -/
def factorTwoConcreteLowSplitPivotOrder : List FactorTwoPhaseLowIndex :=
  (List.ofFn fun i : YoshidaEvenIndex ↦ (Sum.inl i : FactorTwoPhaseLowIndex)) ++
    List.ofFn fun j : YoshidaOddIndex ↦ (Sum.inr j : FactorTwoPhaseLowIndex)

theorem factorTwoConcreteLowSplitPivotOrder_nodup :
    factorTwoConcreteLowSplitPivotOrder.Nodup := by
  rw [factorTwoConcreteLowSplitPivotOrder, List.nodup_append]
  refine ⟨List.nodup_ofFn.mpr Sum.inl_injective,
    List.nodup_ofFn.mpr Sum.inr_injective, ?_⟩
  intro x hxLeft y hxRight
  rw [List.mem_ofFn] at hxLeft hxRight
  rcases hxLeft with ⟨i, rfl⟩
  rcases hxRight with ⟨j, rfl⟩
  exact Sum.inl_ne_inr

theorem factorTwoConcreteLowSplitPivotOrder_cover
    (i : FactorTwoPhaseLowIndex) :
    i ∈ factorTwoConcreteLowSplitPivotOrder := by
  rcases i with i | i
  · rw [factorTwoConcreteLowSplitPivotOrder, List.mem_append]
    exact Or.inl (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · rw [factorTwoConcreteLowSplitPivotOrder, List.mem_append]
    exact Or.inr (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- A containing rational interval matrix with positive exact Schur pivots
in any duplicate-free exhaustive order certifies the even-plus split. -/
theorem factorTwoConcreteLowSplitToeplitzEvenPlusMatrix_posDef_of_intervalOrder
    (ps : List FactorTwoPhaseLowIndex) (hNodup : ps.Nodup)
    (hCover : ∀ i, i ∈ ps)
    (M : Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex RatInterval)
    (hM : ∀ i j, (M i j).Contains
      (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix i j))
    (hPivots : PositivePivots ps M) :
    factorTwoConcreteLowSplitToeplitzEvenPlusMatrix.PosDef := by
  exact posDef_of_intervalPositivePivots M
    factorTwoConcreteLowSplitToeplitzEvenPlusMatrix
    factorTwoConcreteLowSplitToeplitzEvenPlusMatrix_isHermitian
    ps hPivots hNodup hCover hM

/-- A containing rational interval matrix with positive exact Schur pivots
in any duplicate-free exhaustive order certifies the even-minus split. -/
theorem factorTwoConcreteLowSplitToeplitzEvenMinusMatrix_posDef_of_intervalOrder
    (ps : List FactorTwoPhaseLowIndex) (hNodup : ps.Nodup)
    (hCover : ∀ i, i ∈ ps)
    (M : Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex RatInterval)
    (hM : ∀ i j, (M i j).Contains
      (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix i j))
    (hPivots : PositivePivots ps M) :
    factorTwoConcreteLowSplitToeplitzEvenMinusMatrix.PosDef := by
  exact posDef_of_intervalPositivePivots M
    factorTwoConcreteLowSplitToeplitzEvenMinusMatrix
    factorTwoConcreteLowSplitToeplitzEvenMinusMatrix_isHermitian
    ps hPivots hNodup hCover hM

/-- Natural-order specialization of the even-plus interval certificate. -/
theorem factorTwoConcreteLowSplitToeplitzEvenPlusMatrix_posDef_of_interval
    (M : Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex RatInterval)
    (hM : ∀ i j, (M i j).Contains
      (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix i j))
    (hPivots : PositivePivots factorTwoConcreteLowSplitPivotOrder M) :
    factorTwoConcreteLowSplitToeplitzEvenPlusMatrix.PosDef := by
  exact factorTwoConcreteLowSplitToeplitzEvenPlusMatrix_posDef_of_intervalOrder
    factorTwoConcreteLowSplitPivotOrder
    factorTwoConcreteLowSplitPivotOrder_nodup
    factorTwoConcreteLowSplitPivotOrder_cover M hM hPivots

/-- Natural-order specialization of the even-minus interval certificate. -/
theorem factorTwoConcreteLowSplitToeplitzEvenMinusMatrix_posDef_of_interval
    (M : Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex RatInterval)
    (hM : ∀ i j, (M i j).Contains
      (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix i j))
    (hPivots : PositivePivots factorTwoConcreteLowSplitPivotOrder M) :
    factorTwoConcreteLowSplitToeplitzEvenMinusMatrix.PosDef := by
  exact factorTwoConcreteLowSplitToeplitzEvenMinusMatrix_posDef_of_intervalOrder
    factorTwoConcreteLowSplitPivotOrder
    factorTwoConcreteLowSplitPivotOrder_nodup
    factorTwoConcreteLowSplitPivotOrder_cover M hM hPivots

/-- Two exact rational interval pivot certificates close the complete
concrete finite-low phase disk. -/
theorem factorTwoConcreteLowPhaseMatrix_posSemidef_of_splitIntervals
    (MPlus MMinus :
      Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex RatInterval)
    (hPlusContains : ∀ i j, (MPlus i j).Contains
      (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix i j))
    (hMinusContains : ∀ i j, (MMinus i j).Contains
      (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix i j))
    (hPlusPivots :
      PositivePivots factorTwoConcreteLowSplitPivotOrder MPlus)
    (hMinusPivots :
      PositivePivots factorTwoConcreteLowSplitPivotOrder MMinus)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (factorTwoConcreteLowPhaseMatrix a b).PosSemidef := by
  apply factorTwoConcreteLowPhaseMatrix_posSemidef_of_split
  · exact (factorTwoConcreteLowSplitToeplitzEvenPlusMatrix_posDef_of_interval
      MPlus hPlusContains hPlusPivots).posSemidef
  · exact (factorTwoConcreteLowSplitToeplitzEvenMinusMatrix_posDef_of_interval
      MMinus hMinusContains hMinusPivots).posSemidef
  · exact hab

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowSplitCertificate
