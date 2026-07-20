import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineStaticNestedSchurStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusNonnegativeStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusFinalDeterminantStructural

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineBalancedStaticNestedSchurStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicNineStaticNestedSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseNestedThreeSchurStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusNonnegativeStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusFinalDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

/-!
# Balanced fixed-core Schur reduction for the retained nine-mode endpoints

The existing nested endpoint reduction spends the entire structural
`P6/P8/P7` reserve.  The production low--tail allocation spends only
`15/16` of it.  This file keeps the already-proved intrinsic six-mode core
unchanged and records the exact positive diagonal correction left in the
terminal three-coordinate block.
-/

/-- The reserve actually spent by the balanced low--tail allocation. -/
def factorTwoIntrinsicNineBalancedReserveQuadratic
    (c6 c8 c7 : ℝ) : ℝ :=
  (15 / 16 : ℝ) * factorTwoIntrinsicNineReserveQuadratic c6 c8 c7

/-- The plus endpoint block after spending only `15/16` of the reserve. -/
def factorTwoIntrinsicNineBalancedPlusBlock
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) : ℝ :=
  factorTwoIntrinsicNinePlusBlock
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c0 c2 c4 c1 c3 c5 c6 c8 c7 +
    (1 / 16 : ℝ) * factorTwoIntrinsicNineReserveQuadratic c6 c8 c7

/-- The minus endpoint block after spending only `15/16` of the reserve. -/
def factorTwoIntrinsicNineBalancedMinusBlock
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) : ℝ :=
  factorTwoIntrinsicNineMinusBlock
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c0 c2 c4 c1 c3 c5 c6 c8 c7 +
    (1 / 16 : ℝ) * factorTwoIntrinsicNineReserveQuadratic c6 c8 c7

/-- Diagonal matrix entry of the retained `P6/P8/P7` reserve. -/
def factorTwoIntrinsicNineReserveEntry (n m : Fin 3) : ℝ :=
  match n.1, m.1 with
  | 0, 0 => factorTwoIntrinsicNineReserve6
  | 1, 1 => factorTwoIntrinsicNineReserve8
  | 2, 2 => factorTwoIntrinsicNineReserve7
  | _, _ => 0

/-- First fraction-free plus Schur block with the unused `1/16` reserve
restored.  The factor `det(E+)` is forced by the fraction-free completion. -/
def factorTwoIntrinsicNineBalancedUPlus
    (h07 h27 h47 h67 h87 : ℝ) (n m : Fin 3) : ℝ :=
  factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 n m +
    (1 / 16 : ℝ) * factorTwoIntrinsicSixUnbalancedEPlusDet *
      factorTwoIntrinsicNineReserveEntry n m

/-- First fraction-free minus Schur block with the unused `1/16` reserve
restored. -/
def factorTwoIntrinsicNineBalancedUMinus
    (h07 h27 h47 h67 h87 : ℝ) (n m : Fin 3) : ℝ :=
  factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 n m +
    (1 / 16 : ℝ) * factorTwoIntrinsicSixUnbalancedEMinusDet *
      factorTwoIntrinsicNineReserveEntry n m

/-- Terminal fraction-free plus Schur entry for the balanced reserve. -/
def factorTwoIntrinsicNineBalancedWPlus
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (n m : Fin 3) : ℝ :=
  factorTwoIntrinsicNineWentry
    (factorTwoIntrinsicNineTPlus 0 0)
    (factorTwoIntrinsicNineTPlus 0 1)
    (factorTwoIntrinsicNineTPlus 0 2)
    (factorTwoIntrinsicNineTPlus 1 1)
    (factorTwoIntrinsicNineTPlus 1 2)
    (factorTwoIntrinsicNineTPlus 2 2)
    (factorTwoIntrinsicNineBalancedUPlus h07 h27 h47 h67 h87 n m)
    (factorTwoIntrinsicNineRPlus h07 h27 h47 h61 h63 h65 h81 h83 h85 0 n)
    (factorTwoIntrinsicNineRPlus h07 h27 h47 h61 h63 h65 h81 h83 h85 1 n)
    (factorTwoIntrinsicNineRPlus h07 h27 h47 h61 h63 h65 h81 h83 h85 2 n)
    (factorTwoIntrinsicNineRPlus h07 h27 h47 h61 h63 h65 h81 h83 h85 0 m)
    (factorTwoIntrinsicNineRPlus h07 h27 h47 h61 h63 h65 h81 h83 h85 1 m)
    (factorTwoIntrinsicNineRPlus h07 h27 h47 h61 h63 h65 h81 h83 h85 2 m)

/-- Terminal fraction-free minus Schur entry for the balanced reserve. -/
def factorTwoIntrinsicNineBalancedWMinus
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (n m : Fin 3) : ℝ :=
  factorTwoIntrinsicNineWentry
    (factorTwoIntrinsicNineTMinus 0 0)
    (factorTwoIntrinsicNineTMinus 0 1)
    (factorTwoIntrinsicNineTMinus 0 2)
    (factorTwoIntrinsicNineTMinus 1 1)
    (factorTwoIntrinsicNineTMinus 1 2)
    (factorTwoIntrinsicNineTMinus 2 2)
    (factorTwoIntrinsicNineBalancedUMinus h07 h27 h47 h67 h87 n m)
    (factorTwoIntrinsicNineRMinus h07 h27 h47 h61 h63 h65 h81 h83 h85 0 n)
    (factorTwoIntrinsicNineRMinus h07 h27 h47 h61 h63 h65 h81 h83 h85 1 n)
    (factorTwoIntrinsicNineRMinus h07 h27 h47 h61 h63 h65 h81 h83 h85 2 n)
    (factorTwoIntrinsicNineRMinus h07 h27 h47 h61 h63 h65 h81 h83 h85 0 m)
    (factorTwoIntrinsicNineRMinus h07 h27 h47 h61 h63 h65 h81 h83 h85 1 m)
    (factorTwoIntrinsicNineRMinus h07 h27 h47 h61 h63 h65 h81 h83 h85 2 m)

/-- The coordinate reserve matrix represents the scalar reserve exactly. -/
theorem factorTwoIntrinsicNineReserveEntry_quadratic
    (c6 c8 c7 : ℝ) :
    symmetricQuadratic
        (factorTwoIntrinsicNineReserveEntry 0 0)
        (factorTwoIntrinsicNineReserveEntry 0 1)
        (factorTwoIntrinsicNineReserveEntry 0 2)
        (factorTwoIntrinsicNineReserveEntry 1 1)
        (factorTwoIntrinsicNineReserveEntry 1 2)
        (factorTwoIntrinsicNineReserveEntry 2 2) c6 c8 c7 =
      factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 := by
  simp [factorTwoIntrinsicNineReserveEntry,
    factorTwoIntrinsicNineReserveQuadratic, symmetricQuadratic]

/-- The balanced terminal plus block is the full-reserve block plus the
correct fraction-free diagonal correction. -/
theorem factorTwoIntrinsicNineBalancedWPlus_eq
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (n m : Fin 3) :
    factorTwoIntrinsicNineBalancedWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 n m =
      factorTwoIntrinsicNineWPlus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 n m +
        (1 / 16 : ℝ) * factorTwoIntrinsicSixUnbalancedEPlusDet *
          factorTwoIntrinsicSixUnbalancedTPlusDet *
          factorTwoIntrinsicNineReserveEntry n m := by
  unfold factorTwoIntrinsicNineBalancedWPlus
    factorTwoIntrinsicNineBalancedUPlus factorTwoIntrinsicNineWPlus
    factorTwoIntrinsicNineWentry factorTwoIntrinsicNineTPlus
    factorTwoIntrinsicSixUnbalancedTPlusDet
  ring

/-- Minus-endpoint counterpart of
`factorTwoIntrinsicNineBalancedWPlus_eq`. -/
theorem factorTwoIntrinsicNineBalancedWMinus_eq
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (n m : Fin 3) :
    factorTwoIntrinsicNineBalancedWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 n m =
      factorTwoIntrinsicNineWMinus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 n m +
        (1 / 16 : ℝ) * factorTwoIntrinsicSixUnbalancedEMinusDet *
          factorTwoIntrinsicSixUnbalancedTMinusDet *
          factorTwoIntrinsicNineReserveEntry n m := by
  unfold factorTwoIntrinsicNineBalancedWMinus
    factorTwoIntrinsicNineBalancedUMinus factorTwoIntrinsicNineWMinus
    factorTwoIntrinsicNineWentry factorTwoIntrinsicNineTMinus
    factorTwoIntrinsicSixUnbalancedTMinusDet
  ring

/-- Quadratic form of the first balanced plus Schur block. -/
theorem factorTwoIntrinsicNineBalancedUPlus_quadratic
    (h07 h27 h47 h67 h87 c6 c8 c7 : ℝ) :
    symmetricQuadratic
        (factorTwoIntrinsicNineBalancedUPlus h07 h27 h47 h67 h87 0 0)
        (factorTwoIntrinsicNineBalancedUPlus h07 h27 h47 h67 h87 0 1)
        (factorTwoIntrinsicNineBalancedUPlus h07 h27 h47 h67 h87 0 2)
        (factorTwoIntrinsicNineBalancedUPlus h07 h27 h47 h67 h87 1 1)
        (factorTwoIntrinsicNineBalancedUPlus h07 h27 h47 h67 h87 1 2)
        (factorTwoIntrinsicNineBalancedUPlus h07 h27 h47 h67 h87 2 2)
        c6 c8 c7 =
      symmetricQuadratic
          (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 0 0)
          (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 0 1)
          (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 0 2)
          (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 1 1)
          (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 1 2)
          (factorTwoIntrinsicNineUPlus h07 h27 h47 h67 h87 2 2)
          c6 c8 c7 +
        (1 / 16 : ℝ) * factorTwoIntrinsicSixUnbalancedEPlusDet *
          factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 := by
  rw [← factorTwoIntrinsicNineReserveEntry_quadratic c6 c8 c7]
  unfold factorTwoIntrinsicNineBalancedUPlus symmetricQuadratic
  ring

/-- Quadratic form of the first balanced minus Schur block. -/
theorem factorTwoIntrinsicNineBalancedUMinus_quadratic
    (h07 h27 h47 h67 h87 c6 c8 c7 : ℝ) :
    symmetricQuadratic
        (factorTwoIntrinsicNineBalancedUMinus h07 h27 h47 h67 h87 0 0)
        (factorTwoIntrinsicNineBalancedUMinus h07 h27 h47 h67 h87 0 1)
        (factorTwoIntrinsicNineBalancedUMinus h07 h27 h47 h67 h87 0 2)
        (factorTwoIntrinsicNineBalancedUMinus h07 h27 h47 h67 h87 1 1)
        (factorTwoIntrinsicNineBalancedUMinus h07 h27 h47 h67 h87 1 2)
        (factorTwoIntrinsicNineBalancedUMinus h07 h27 h47 h67 h87 2 2)
        c6 c8 c7 =
      symmetricQuadratic
          (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 0 0)
          (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 0 1)
          (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 0 2)
          (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 1 1)
          (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 1 2)
          (factorTwoIntrinsicNineUMinus h07 h27 h47 h67 h87 2 2)
          c6 c8 c7 +
        (1 / 16 : ℝ) * factorTwoIntrinsicSixUnbalancedEMinusDet *
          factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 := by
  rw [← factorTwoIntrinsicNineReserveEntry_quadratic c6 c8 c7]
  unfold factorTwoIntrinsicNineBalancedUMinus symmetricQuadratic
  ring

/-- Quadratic form of the terminal balanced plus Schur block. -/
theorem factorTwoIntrinsicNineBalancedWPlus_quadratic
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 c6 c8 c7 : ℝ) :
    symmetricQuadratic
        (factorTwoIntrinsicNineBalancedWPlus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 0)
        (factorTwoIntrinsicNineBalancedWPlus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 1)
        (factorTwoIntrinsicNineBalancedWPlus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 2)
        (factorTwoIntrinsicNineBalancedWPlus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 1)
        (factorTwoIntrinsicNineBalancedWPlus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 2)
        (factorTwoIntrinsicNineBalancedWPlus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 2 2)
        c6 c8 c7 =
      symmetricQuadratic
          (factorTwoIntrinsicNineWPlus
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 0)
          (factorTwoIntrinsicNineWPlus
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 1)
          (factorTwoIntrinsicNineWPlus
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 2)
          (factorTwoIntrinsicNineWPlus
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 1)
          (factorTwoIntrinsicNineWPlus
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 2)
          (factorTwoIntrinsicNineWPlus
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 2 2)
          c6 c8 c7 +
        (1 / 16 : ℝ) * factorTwoIntrinsicSixUnbalancedEPlusDet *
          factorTwoIntrinsicSixUnbalancedTPlusDet *
          factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 := by
  rw [← factorTwoIntrinsicNineReserveEntry_quadratic c6 c8 c7]
  simp only [factorTwoIntrinsicNineBalancedWPlus_eq]
  unfold symmetricQuadratic
  ring

/-- Quadratic form of the terminal balanced minus Schur block. -/
theorem factorTwoIntrinsicNineBalancedWMinus_quadratic
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 c6 c8 c7 : ℝ) :
    symmetricQuadratic
        (factorTwoIntrinsicNineBalancedWMinus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 0)
        (factorTwoIntrinsicNineBalancedWMinus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 1)
        (factorTwoIntrinsicNineBalancedWMinus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 2)
        (factorTwoIntrinsicNineBalancedWMinus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 1)
        (factorTwoIntrinsicNineBalancedWMinus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 2)
        (factorTwoIntrinsicNineBalancedWMinus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 2 2)
        c6 c8 c7 =
      symmetricQuadratic
          (factorTwoIntrinsicNineWMinus
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 0)
          (factorTwoIntrinsicNineWMinus
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 1)
          (factorTwoIntrinsicNineWMinus
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 2)
          (factorTwoIntrinsicNineWMinus
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 1)
          (factorTwoIntrinsicNineWMinus
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 2)
          (factorTwoIntrinsicNineWMinus
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 2 2)
          c6 c8 c7 +
        (1 / 16 : ℝ) * factorTwoIntrinsicSixUnbalancedEMinusDet *
          factorTwoIntrinsicSixUnbalancedTMinusDet *
          factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 := by
  rw [← factorTwoIntrinsicNineReserveEntry_quadratic c6 c8 c7]
  simp only [factorTwoIntrinsicNineBalancedWMinus_eq]
  unfold symmetricQuadratic
  ring

/-- The sole new plus-endpoint gate after reusing the unconditional
six-mode core. -/
def FactorTwoIntrinsicNineBalancedWPlusNonnegative
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ) : Prop :=
  ∀ z6 z8 z7 : ℝ, 0 ≤ symmetricQuadratic
    (factorTwoIntrinsicNineBalancedWPlus
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 0)
    (factorTwoIntrinsicNineBalancedWPlus
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 1)
    (factorTwoIntrinsicNineBalancedWPlus
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 2)
    (factorTwoIntrinsicNineBalancedWPlus
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 1)
    (factorTwoIntrinsicNineBalancedWPlus
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 2)
    (factorTwoIntrinsicNineBalancedWPlus
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 2 2)
    z6 z8 z7

/-- The sole new minus-endpoint gate after reusing the unconditional
six-mode core. -/
def FactorTwoIntrinsicNineBalancedWMinusNonnegative
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ) : Prop :=
  ∀ z6 z8 z7 : ℝ, 0 ≤ symmetricQuadratic
    (factorTwoIntrinsicNineBalancedWMinus
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 0)
    (factorTwoIntrinsicNineBalancedWMinus
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 1)
    (factorTwoIntrinsicNineBalancedWMinus
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 2)
    (factorTwoIntrinsicNineBalancedWMinus
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 1)
    (factorTwoIntrinsicNineBalancedWMinus
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 2)
    (factorTwoIntrinsicNineBalancedWMinus
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 2 2)
    z6 z8 z7

/-! ## Balanced nested Schur completion -/

/-- The unchanged six-mode Sylvester gates and positivity of the balanced
terminal `W+` block imply nonnegativity of the complete balanced plus
endpoint. -/
theorem factorTwoIntrinsicNineBalancedPlusBlock_nonnegative_of_nested_schur
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (hE00 : 0 < factorTwoIntrinsicSixUnbalancedEPlus00)
    (hEMinor : 0 < leadingMinorTwo
      factorTwoIntrinsicSixUnbalancedEPlus00
      factorTwoIntrinsicSixUnbalancedEPlus02
      factorTwoIntrinsicSixUnbalancedEPlus22)
    (hEDet : 0 < factorTwoIntrinsicSixUnbalancedEPlusDet)
    (hT11 : 0 < factorTwoIntrinsicSixUnbalancedTPlus11)
    (hTMinor : 0 < factorTwoIntrinsicSixUnbalancedTPlusMinor)
    (hTDet : 0 < factorTwoIntrinsicSixUnbalancedTPlusDet)
    (hW : ∀ z6 z8 z7 : ℝ, 0 ≤ symmetricQuadratic
      (factorTwoIntrinsicNineBalancedWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 0)
      (factorTwoIntrinsicNineBalancedWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 1)
      (factorTwoIntrinsicNineBalancedWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 2)
      (factorTwoIntrinsicNineBalancedWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 1)
      (factorTwoIntrinsicNineBalancedWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 2)
      (factorTwoIntrinsicNineBalancedWPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 2 2)
      z6 z8 z7)
    (c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) :
    0 ≤ factorTwoIntrinsicNineBalancedPlusBlock
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c0 c2 c4 c1 c3 c5 c6 c8 c7 := by
  unfold factorTwoIntrinsicNineBalancedPlusBlock
    factorTwoIntrinsicNinePlusBlock
  rw [add_assoc]
  apply nineBlock_nonneg_of_nested_fractionFreeSchur
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    (factorTwoIntrinsicNineTPlus 0 0)
    (factorTwoIntrinsicNineTPlus 0 1)
    (factorTwoIntrinsicNineTPlus 0 2)
    (factorTwoIntrinsicNineTPlus 1 1)
    (factorTwoIntrinsicNineTPlus 1 2)
    (factorTwoIntrinsicNineTPlus 2 2)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 0 0)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 0 1)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 0 2)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 1 0)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 1 1)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 1 2)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 2 0)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 2 1)
    (factorTwoIntrinsicNineRPlus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 2 2)
    (factorTwoIntrinsicNineBalancedUPlus h07 h27 h47 h67 h87 0 0)
    (factorTwoIntrinsicNineBalancedUPlus h07 h27 h47 h67 h87 0 1)
    (factorTwoIntrinsicNineBalancedUPlus h07 h27 h47 h67 h87 0 2)
    (factorTwoIntrinsicNineBalancedUPlus h07 h27 h47 h67 h87 1 1)
    (factorTwoIntrinsicNineBalancedUPlus h07 h27 h47 h67 h87 1 2)
    (factorTwoIntrinsicNineBalancedUPlus h07 h27 h47 h67 h87 2 2)
    (y0 := c1) (y1 := c3) (y2 := c5)
    (z0 := c6) (z1 := c8) (z2 := c7)
  · exact hE00
  · exact hEMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedEPlusDet] using hEDet
  · simpa only [factorTwoIntrinsicNineTPlus] using hT11
  · simpa only [factorTwoIntrinsicSixUnbalancedTPlusMinor,
      factorTwoIntrinsicNineTPlus] using hTMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedTPlusDet,
      factorTwoIntrinsicNineTPlus] using hTDet
  · intro z6 z8 z7
    simpa only [factorTwoIntrinsicNineBalancedWPlus,
      factorTwoIntrinsicNineWentry] using hW z6 z8 z7
  · rw [factorTwoIntrinsicNineBalancedUPlus_quadratic]
    have hFirst := factorTwoIntrinsicNinePlus_firstSchur_eq
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c1 c3 c5 c6 c8 c7
    unfold factorTwoIntrinsicSixUnbalancedEPlusDet at hFirst ⊢
    linear_combination hFirst

/-- Minus-endpoint counterpart of
`factorTwoIntrinsicNineBalancedPlusBlock_nonnegative_of_nested_schur`. -/
theorem factorTwoIntrinsicNineBalancedMinusBlock_nonnegative_of_nested_schur
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (hE00 : 0 < factorTwoIntrinsicSixUnbalancedEMinus00)
    (hEMinor : 0 < leadingMinorTwo
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus22)
    (hEDet : 0 < factorTwoIntrinsicSixUnbalancedEMinusDet)
    (hT11 : 0 < factorTwoIntrinsicSixUnbalancedTMinus11)
    (hTMinor : 0 < factorTwoIntrinsicSixUnbalancedTMinusMinor)
    (hTDet : 0 < factorTwoIntrinsicSixUnbalancedTMinusDet)
    (hW : ∀ z6 z8 z7 : ℝ, 0 ≤ symmetricQuadratic
      (factorTwoIntrinsicNineBalancedWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 0)
      (factorTwoIntrinsicNineBalancedWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 1)
      (factorTwoIntrinsicNineBalancedWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 0 2)
      (factorTwoIntrinsicNineBalancedWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 1)
      (factorTwoIntrinsicNineBalancedWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 1 2)
      (factorTwoIntrinsicNineBalancedWMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 2 2)
      z6 z8 z7)
    (c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) :
    0 ≤ factorTwoIntrinsicNineBalancedMinusBlock
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c0 c2 c4 c1 c3 c5 c6 c8 c7 := by
  unfold factorTwoIntrinsicNineBalancedMinusBlock
    factorTwoIntrinsicNineMinusBlock
  rw [add_assoc]
  apply nineBlock_nonneg_of_nested_fractionFreeSchur
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (factorTwoIntrinsicNineTMinus 0 0)
    (factorTwoIntrinsicNineTMinus 0 1)
    (factorTwoIntrinsicNineTMinus 0 2)
    (factorTwoIntrinsicNineTMinus 1 1)
    (factorTwoIntrinsicNineTMinus 1 2)
    (factorTwoIntrinsicNineTMinus 2 2)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 0 0)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 0 1)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 0 2)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 1 0)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 1 1)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 1 2)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 2 0)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 2 1)
    (factorTwoIntrinsicNineRMinus
      h07 h27 h47 h61 h63 h65 h81 h83 h85 2 2)
    (factorTwoIntrinsicNineBalancedUMinus h07 h27 h47 h67 h87 0 0)
    (factorTwoIntrinsicNineBalancedUMinus h07 h27 h47 h67 h87 0 1)
    (factorTwoIntrinsicNineBalancedUMinus h07 h27 h47 h67 h87 0 2)
    (factorTwoIntrinsicNineBalancedUMinus h07 h27 h47 h67 h87 1 1)
    (factorTwoIntrinsicNineBalancedUMinus h07 h27 h47 h67 h87 1 2)
    (factorTwoIntrinsicNineBalancedUMinus h07 h27 h47 h67 h87 2 2)
    (y0 := c1) (y1 := c3) (y2 := c5)
    (z0 := c6) (z1 := c8) (z2 := c7)
  · exact hE00
  · exact hEMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedEMinusDet] using hEDet
  · simpa only [factorTwoIntrinsicNineTMinus] using hT11
  · simpa only [factorTwoIntrinsicSixUnbalancedTMinusMinor,
      factorTwoIntrinsicNineTMinus] using hTMinor
  · simpa only [factorTwoIntrinsicSixUnbalancedTMinusDet,
      factorTwoIntrinsicNineTMinus] using hTDet
  · intro z6 z8 z7
    simpa only [factorTwoIntrinsicNineBalancedWMinus,
      factorTwoIntrinsicNineWentry] using hW z6 z8 z7
  · rw [factorTwoIntrinsicNineBalancedUMinus_quadratic]
    have hFirst := factorTwoIntrinsicNineMinus_firstSchur_eq
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c1 c3 c5 c6 c8 c7
    unfold factorTwoIntrinsicSixUnbalancedEMinusDet at hFirst ⊢
    linear_combination hFirst

/-- After inserting the existing structural six-mode gates, the balanced
plus endpoint depends only on its terminal `Fin 3` quadratic gate. -/
theorem factorTwoIntrinsicNineBalancedPlusBlock_nonnegative_of_W
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (hW : FactorTwoIntrinsicNineBalancedWPlusNonnegative
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87)
    (c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) :
    0 ≤ factorTwoIntrinsicNineBalancedPlusBlock
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c0 c2 c4 c1 c3 c5 c6 c8 c7 := by
  exact factorTwoIntrinsicNineBalancedPlusBlock_nonnegative_of_nested_schur
    h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
    factorTwoIntrinsicSixUnbalancedEPlus_positive.1
    factorTwoIntrinsicSixUnbalancedEPlus_positive.2.1
    factorTwoIntrinsicSixUnbalancedEPlus_positive.2.2
    factorTwoIntrinsicSixUnbalancedTPlus11_pos
    factorTwoIntrinsicSixUnbalancedTPlusMinor_pos
    factorTwoIntrinsicSixUnbalancedTPlusDet_pos hW
    c0 c2 c4 c1 c3 c5 c6 c8 c7

/-- After inserting the existing structural six-mode gates, the balanced
minus endpoint depends only on its terminal `Fin 3` quadratic gate. -/
theorem factorTwoIntrinsicNineBalancedMinusBlock_nonnegative_of_W
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (hW : FactorTwoIntrinsicNineBalancedWMinusNonnegative
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87)
    (c0 c2 c4 c1 c3 c5 c6 c8 c7 : ℝ) :
    0 ≤ factorTwoIntrinsicNineBalancedMinusBlock
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c0 c2 c4 c1 c3 c5 c6 c8 c7 := by
  exact factorTwoIntrinsicNineBalancedMinusBlock_nonnegative_of_nested_schur
    h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
    factorTwoIntrinsicSixUnbalancedEMinus_positive.1
    factorTwoIntrinsicSixUnbalancedEMinus_positive.2.1
    factorTwoIntrinsicSixUnbalancedEMinus_positive.2.2
    factorTwoIntrinsicSixUnbalancedTMinus11_pos
    factorTwoIntrinsicSixUnbalancedTMinusMinor_pos
    factorTwoIntrinsicSixUnbalancedTMinusDet_pos hW
    c0 c2 c4 c1 c3 c5 c6 c8 c7

/-- Exact identification of the balanced plus endpoint with the old
full-reserve block plus its unused positive diagonal reserve. -/
theorem factorTwoIntrinsicNineUnbalancedStaticPlus_sub_balancedReserve_eq_block
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineUnbalancedStaticPlus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
          c0 c2 c4 c6 c8 c1 c3 c5 c7 -
        factorTwoIntrinsicNineBalancedReserveQuadratic c6 c8 c7 =
      factorTwoIntrinsicNineBalancedPlusBlock
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
        c0 c2 c4 c1 c3 c5 c6 c8 c7 := by
  calc
    _ = (factorTwoIntrinsicNineUnbalancedStaticPlus
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
            c0 c2 c4 c6 c8 c1 c3 c5 c7 -
          factorTwoIntrinsicNineReserveQuadratic c6 c8 c7) +
        (1 / 16 : ℝ) * factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 := by
      unfold factorTwoIntrinsicNineBalancedReserveQuadratic
      ring
    _ = factorTwoIntrinsicNinePlusBlock
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
            c0 c2 c4 c1 c3 c5 c6 c8 c7 +
          (1 / 16 : ℝ) * factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 := by
      rw [factorTwoIntrinsicNineUnbalancedStaticPlus_sub_reserve_eq_block]
    _ = _ := rfl

/-- Exact identification of the balanced minus endpoint with the old
full-reserve block plus its unused positive diagonal reserve. -/
theorem factorTwoIntrinsicNineUnbalancedStaticMinus_sub_balancedReserve_eq_block
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineUnbalancedStaticMinus
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
          c0 c2 c4 c6 c8 c1 c3 c5 c7 -
        factorTwoIntrinsicNineBalancedReserveQuadratic c6 c8 c7 =
      factorTwoIntrinsicNineBalancedMinusBlock
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
        c0 c2 c4 c1 c3 c5 c6 c8 c7 := by
  calc
    _ = (factorTwoIntrinsicNineUnbalancedStaticMinus
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
            c0 c2 c4 c6 c8 c1 c3 c5 c7 -
          factorTwoIntrinsicNineReserveQuadratic c6 c8 c7) +
        (1 / 16 : ℝ) * factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 := by
      unfold factorTwoIntrinsicNineBalancedReserveQuadratic
      ring
    _ = factorTwoIntrinsicNineMinusBlock
            h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
            c0 c2 c4 c1 c3 c5 c6 c8 c7 +
          (1 / 16 : ℝ) * factorTwoIntrinsicNineReserveQuadratic c6 c8 c7 := by
      rw [factorTwoIntrinsicNineUnbalancedStaticMinus_sub_reserve_eq_block]
    _ = _ := rfl

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineBalancedStaticNestedSchurStructural
