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
# Matched-factor closure of the odd `P₁₁+` corrected determinant

The scalar exact-tail weight is too small for the old selector certificate.
The corrected determinant only needs a matched enlargement: for one common
factor `κ`, the core tail reserve must dominate `κ` times the weight, and the
two selector rows may spend that same enlarged reserve jointly.  This file
proves that any such matched factor closes the exact determinant, including
the singular finite-reserve fibers.  The named `3/2` interfaces are retained
as one concrete probe, not asserted to hold.
-/

/-- The genuine `P₁₁+` tail core dominates `κ` times the exact scalar
weight. -/
def FourCellOddP11TailReserveAtFactor (κ : ℝ) : Prop :=
  ∀ (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    κ * fourCellOddP1ExactTailWeight r ≤
      fourCellOddCoreLocalQuadratic r

/-- The two corrected selector rows spend at most the tail reserve enlarged
by `κ`.  Keeping the rows together preserves their finite--tail
correlation. -/
def FourCellOddP11JointSelectorAtFactor (κ : ℝ) : Prop :=
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
          (κ * fourCellOddP1ExactTailWeight r)

/-- A selector-free formulation of the same finite task: every retained
five-mode polynomial acts on the genuine tail with weighted norm at most `κ`
times its core norm. -/
def FourCellOddP11FiveModeCauchyAtFactor (κ : ℝ) : Prop :=
  ∀ (c d e f g : ℝ) (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    fourCellOddCoreLocalBilinear
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r ^ 2 ≤
      fourCellOddCoreLocalQuadratic
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) *
        (κ * fourCellOddP1ExactTailWeight r)

/-- The concrete three-halves tail probe. -/
def FourCellOddP11TailReserveThreeHalves : Prop :=
  FourCellOddP11TailReserveAtFactor (3 / 2 : ℝ)

/-- The concrete three-halves joint-selector probe. -/
def FourCellOddP11JointSelectorThreeHalves : Prop :=
  FourCellOddP11JointSelectorAtFactor (3 / 2 : ℝ)

/-- The concrete three-halves five-mode Cauchy probe. -/
def FourCellOddP11FiveModeCauchyThreeHalves : Prop :=
  FourCellOddP11FiveModeCauchyAtFactor (3 / 2 : ℝ)

/-- The universal five-mode weighted Cauchy bound at a nonnegative factor
supplies the joint two-selector estimate.  The exact Gram--Schmidt profile
identity preserves the full correlation, so there is no rowwise triangle
loss. -/
theorem fourCellOddP11JointSelectorAtFactor_of_fiveModeCauchy
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hcauchy : FourCellOddP11FiveModeCauchyAtFactor κ) :
    FourCellOddP11JointSelectorAtFactor κ := by
  intro d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let F := fourCellOddP11FiniteCorrectedReserve d e f g
  let x := fourCellOddCoreLocalBilinear centeredP1 r
  let X := fourCellOddP11FiniteTailCorrectedCross d e f g r
  let W := fourCellOddP1ExactTailWeight r
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact fourCellOddCoreLocalQuadratic_centeredP1_nonneg
  have hF : 0 ≤ F := by
    dsimp only [F]
    exact fourCellOddP11FiniteCorrectedReserve_nonnegative d e f g
  have hW : 0 ≤ κ * W := by
    exact mul_nonneg hκ
      (fourCellOddP1ExactTailWeight_nonneg r hr.continuous)
  apply (jointWeightedDual_iff_twoRowLoewner hA hF hW).2
  intro s t
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  let b := fourCellOddCoreLocalBilinear centeredP1 p
  have hrow := hcauchy
    (F * s - t * b) (t * A * d) (t * A * e) (t * A * f)
      (t * A * g) r hr hrodd hr1 hr3 hr5 hr7 hr9
  have hprofile :=
    fourCellOddP11CoupledLoewnerSelectorProfile_eq_lowProfile
      d e f g s t
  dsimp only [A, F, p, b] at hprofile
  rw [← hprofile] at hrow
  rw [fourCellOddCoreLocalBilinear_coupledLoewnerSelectorProfile
        d e f g s t r hr hrodd,
      fourCellOddCoreLocalQuadratic_coupledLoewnerSelectorProfile]
    at hrow
  dsimp only [A, F, x, X, W] at hrow ⊢
  simpa only [mul_assoc] using hrow

/-- Specialization of the matched-factor reduction at `κ = 3 / 2`. -/
theorem fourCellOddP11JointSelectorThreeHalves_of_fiveModeCauchy
    (hcauchy : FourCellOddP11FiveModeCauchyThreeHalves) :
    FourCellOddP11JointSelectorThreeHalves :=
  fourCellOddP11JointSelectorAtFactor_of_fiveModeCauchy
    (3 / 2 : ℝ) (by norm_num) hcauchy

/-- Tail domination and joint-selector control at one matched factor imply
the actual universal corrected determinant.  The strict `P₃` finite reserve
is used only to recover the pure `P₁` tail row, so no division or positive
definiteness assumption is imposed on the arbitrary low profile. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_matchedFactor
    (κ : ℝ)
    (htail : FourCellOddP11TailReserveAtFactor κ)
    (hjoint : FourCellOddP11JointSelectorAtFactor κ) :
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
  have hWz : κ * W ≤ z := by
    dsimp only [W, z]
    exact htail r hr hrodd hr1 hr3 hr5 hr7 hr9
  have hcurrent := hjoint d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9
  have hprobe := hjoint 1 0 0 0 r hr hrodd hr1 hr3 hr5 hr7 hr9
  let F₃ := fourCellOddP11FiniteCorrectedReserve 1 0 0 0
  let X₃ := fourCellOddP11FiniteTailCorrectedCross 1 0 0 0 r
  have hF₃ : 0 < F₃ := by
    dsimp only [F₃]
    exact fourCellOddP11FiniteCorrectedReserve_P3_pos
  have hpure : x ^ 2 ≤ A * (κ * W) := by
    dsimp only [F₃, X₃, x, A, W] at hprobe hF₃ ⊢
    by_contra hle
    have hgap : 0 <
        fourCellOddCoreLocalBilinear centeredP1 r ^ 2 -
          fourCellOddCoreLocalQuadratic centeredP1 *
            (κ * fourCellOddP1ExactTailWeight r) :=
      sub_pos.mpr (lt_of_not_ge hle)
    have hprod := mul_pos hF₃ hgap
    nlinarith [sq_nonneg
      (fourCellOddP11FiniteTailCorrectedCross 1 0 0 0 r)]
  have hdet := coupledP1TailSchurDefect_nonneg_of_jointWeightedDual
    (A := A) (b := b) (C := C) (x := x) (y := y) (z := z)
    (W := κ * W) hA hF hWz hpure
    (by
      dsimp only [F, X, A, b, C, x, y, W, p]
      simpa only [fourCellOddP11FiniteCorrectedReserve,
        fourCellOddP11FiniteTailCorrectedCross] using hcurrent)
  simpa only [fourCellOddP11CoupledRieszDefect, p, A, b, C, x, y, z]
    using hdet

/-- Selector-free matched-factor handoff: tail domination and the universal
five-mode weighted Cauchy inequality close the corrected determinant. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_matchedFactor_fiveModeCauchy
    (κ : ℝ) (hκ : 0 ≤ κ)
    (htail : FourCellOddP11TailReserveAtFactor κ)
    (hcauchy : FourCellOddP11FiveModeCauchyAtFactor κ) :
    FourCellOddP11CoupledRieszDefectNonnegative :=
  fourCellOddP11CoupledRieszDefectNonnegative_of_matchedFactor κ htail
    (fourCellOddP11JointSelectorAtFactor_of_fiveModeCauchy κ hκ hcauchy)

/-- Specialization of the matched-factor determinant closure at
`κ = 3 / 2`. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_threeHalves
    (htail : FourCellOddP11TailReserveThreeHalves)
    (hjoint : FourCellOddP11JointSelectorThreeHalves) :
    FourCellOddP11CoupledRieszDefectNonnegative :=
  fourCellOddP11CoupledRieszDefectNonnegative_of_matchedFactor
    (3 / 2 : ℝ) htail hjoint

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11ThreeHalvesClosureStructural
