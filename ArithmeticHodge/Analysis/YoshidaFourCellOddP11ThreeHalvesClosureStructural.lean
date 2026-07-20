import ArithmeticHodge.Analysis.YoshidaFourCellOddP11SelectorConstructionStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11ThreeHalvesClosureStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaFourCellOddP11ConcreteWeightedDualClosureStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddP11WeightedDualSelectorStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Three-halves closure of the odd `P₁₁+` corrected determinant

The scalar exact-tail weight is too small for the old selector certificate.
The corrected determinant only needs a matched enlargement: the core tail
reserve must dominate `3/2` times the weight, and the two selector rows may
spend that same enlarged reserve jointly.  This file proves that those two
structural estimates close the exact determinant, including the singular
finite-reserve fibers.
-/

/-- The genuine `P₁₁+` tail core dominates three halves of the exact scalar
weight. -/
def FourCellOddP11TailReserveThreeHalves : Prop :=
  ∀ (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    (3 / 2 : ℝ) * fourCellOddP1ExactTailWeight r ≤
      fourCellOddCoreLocalQuadratic r

/-- The two corrected selector rows spend at most the enlarged tail reserve.
Keeping the two rows together preserves their finite--tail correlation. -/
def FourCellOddP11JointSelectorThreeHalves : Prop :=
  ∀ (d e f g : ℝ) (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    fourCellOddP11FiniteCorrectedReserve d e f g *
          fourCellOddCoreLocalBilinear centeredP1 r ^ 2 +
        fourCellOddP11FiniteTailCorrectedCross d e f g r ^ 2 ≤
      fourCellOddP11FiniteCorrectedReserve d e f g *
        fourCellOddCoreLocalQuadratic centeredP1 *
          ((3 / 2 : ℝ) * fourCellOddP1ExactTailWeight r)

/-- The matched three-halves tail and joint-selector estimates imply the
actual universal corrected determinant.  The strict `P₃` finite reserve is
used only to recover the pure `P₁` tail row, so no division or positive
definiteness assumption is imposed on the arbitrary low profile. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_threeHalves
    (htail : FourCellOddP11TailReserveThreeHalves)
    (hjoint : FourCellOddP11JointSelectorThreeHalves) :
    FourCellOddP11CoupledRieszDefectNonnegative := by
  intro d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let b := fourCellOddCoreLocalBilinear centeredP1 p
  let C := fourCellOddCoreLocalQuadratic p
  let x := fourCellOddCoreLocalBilinear centeredP1 r
  let y := fourCellOddCoreLocalBilinear p r
  let z := fourCellOddCoreLocalQuadratic r
  let W := fourCellOddP1ExactTailWeight r
  let F := A * C - b ^ 2
  let X := A * y - b * x
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact fourCellOddCoreLocalQuadratic_centeredP1_nonneg
  have hF : 0 ≤ F := by
    dsimp only [F, A, b, C, p]
    simpa only [fourCellOddP11FiniteCorrectedReserve] using
      fourCellOddP11FiniteCorrectedReserve_nonnegative d e f g
  have hWz : (3 / 2 : ℝ) * W ≤ z := by
    dsimp only [W, z]
    exact htail r hr hrodd hr1 hr3 hr5 hr7 hr9
  have hcurrent := hjoint d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9
  have hprobe := hjoint 1 0 0 0 r hr hrodd hr1 hr3 hr5 hr7 hr9
  let F₃ := fourCellOddP11FiniteCorrectedReserve 1 0 0 0
  let X₃ := fourCellOddP11FiniteTailCorrectedCross 1 0 0 0 r
  have hF₃ : 0 < F₃ := by
    dsimp only [F₃]
    exact fourCellOddP11FiniteCorrectedReserve_P3_pos
  have hpure : x ^ 2 ≤ A * ((3 / 2 : ℝ) * W) := by
    dsimp only [F₃, X₃, x, A, W] at hprobe hF₃ ⊢
    by_contra hle
    have hgap : 0 <
        fourCellOddCoreLocalBilinear centeredP1 r ^ 2 -
          fourCellOddCoreLocalQuadratic centeredP1 *
            ((3 / 2 : ℝ) * fourCellOddP1ExactTailWeight r) :=
      sub_pos.mpr (lt_of_not_ge hle)
    have hprod := mul_pos hF₃ hgap
    nlinarith [sq_nonneg
      (fourCellOddP11FiniteTailCorrectedCross 1 0 0 0 r)]
  have hdet := coupledP1TailSchurDefect_nonneg_of_jointWeightedDual
    (A := A) (b := b) (C := C) (x := x) (y := y) (z := z)
    (W := (3 / 2 : ℝ) * W) hA hF hWz hpure
    (by
      dsimp only [F, X, A, b, C, x, y, W, p]
      simpa only [fourCellOddP11FiniteCorrectedReserve,
        fourCellOddP11FiniteTailCorrectedCross] using hcurrent)
  simpa only [fourCellOddP11CoupledRieszDefect, p, A, b, C, x, y, z]
    using hdet

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11ThreeHalvesClosureStructural
