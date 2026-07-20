import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoupledRieszClosureStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoupledRieszDefectClosureStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Coupled closure of the corrected odd `P₁`/`P₁₁+` determinant

The corrected determinant is a second Schur form.  Its finite reserve, tail
reserve, and corrected cross must be kept together; the cross is
`A*y - b*x`, not the uncorrected finite--tail row `y`.
-/

/-- Exact two-by-two completion for the corrected finite--tail determinant.
This is the correlation-sensitive replacement for three independent Cauchy
bounds. -/
theorem coupledP1TailSchurDefect_nonneg_of_correctedCross
    {A b C x y z : ℝ}
    (hfinite : 0 ≤ A * C - b ^ 2)
    (htail : 0 ≤ A * z - x ^ 2)
    (hcross : (A * y - b * x) ^ 2 ≤
      (A * C - b ^ 2) * (A * z - x ^ 2)) :
    0 ≤ coupledP1TailSchurDefect A b C x y z := by
  let F := A * C - b ^ 2
  let X := A * y - b * x
  let T := A * z - x ^ 2
  have hsum : 0 ≤ F + 2 * X + T := by
    by_cases hX : 0 ≤ X
    · positivity
    · have hneg : 0 ≤ -2 * X := by linarith
      have hFT : 0 ≤ F + T := add_nonneg hfinite htail
      have hsquares : (-2 * X) ^ 2 ≤ (F + T) ^ 2 := by
        dsimp only [F, X, T] at hfinite htail hcross ⊢
        nlinarith [sq_nonneg
          ((A * C - b ^ 2) - (A * z - x ^ 2))]
      have hlinear := (sq_le_sq₀ hneg hFT).mp hsquares
      linarith
  dsimp only [F, X, T] at hsum
  unfold coupledP1TailSchurDefect
  exact hsum

/-- Weighted-dual closure of the corrected determinant.  `D₀` is the dual
cost of the tail `P₁` row, while `D₁` is the dual cost of the corrected
finite--tail row.  The finite reserve pays `D₁`; the unused part `A-D₀` of
the tail pivot is retained, so no triangle inequality is used. -/
theorem coupledP1TailSchurDefect_nonneg_of_weightedDual
    {A b C x y z W D₀ D₁ : ℝ}
    (hA : 0 ≤ A)
    (hfinite : 0 ≤ A * C - b ^ 2)
    (hW : 0 ≤ W)
    (hWz : W ≤ z)
    (hD₀ : D₀ ≤ A)
    (hx : x ^ 2 ≤ D₀ * W)
    (hcorrected : (A * y - b * x) ^ 2 ≤ D₁ * W)
    (hdual : D₁ ≤ (A * C - b ^ 2) * (A - D₀)) :
    0 ≤ coupledP1TailSchurDefect A b C x y z := by
  let F := A * C - b ^ 2
  let X := A * y - b * x
  let T := A * z - x ^ 2
  have hgap : 0 ≤ A - D₀ := sub_nonneg.mpr hD₀
  have hAz : A * W ≤ A * z := mul_le_mul_of_nonneg_left hWz hA
  have htailLower : (A - D₀) * W ≤ T := by
    dsimp only [T]
    nlinarith
  have htail : 0 ≤ T :=
    (mul_nonneg hgap hW).trans htailLower
  have hdualW : D₁ * W ≤ F * (A - D₀) * W := by
    dsimp only [F] at hdual ⊢
    exact mul_le_mul_of_nonneg_right hdual hW
  have hreserveW : F * (A - D₀) * W ≤ F * T := by
    have := mul_le_mul_of_nonneg_left htailLower hfinite
    simpa only [F, mul_assoc] using this
  have hcross : X ^ 2 ≤ F * T := by
    dsimp only [X] at hcorrected ⊢
    exact hcorrected.trans (hdualW.trans hreserveW)
  exact coupledP1TailSchurDefect_nonneg_of_correctedCross
    hfinite htail hcross

/-- Finite corrected reserve of the retained `P₃/P₅/P₇/P₉` profile. -/
def fourCellOddP11FiniteCorrectedReserve
    (d e f g : ℝ) : ℝ :=
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  fourCellOddCoreLocalQuadratic centeredP1 *
      fourCellOddCoreLocalQuadratic p -
    fourCellOddCoreLocalBilinear centeredP1 p ^ 2

/-- Tail corrected reserve of one genuine `P₁₁+` residual. -/
def fourCellOddP11TailCorrectedReserve (r : ℝ → ℝ) : ℝ :=
  fourCellOddCoreLocalQuadratic centeredP1 *
      fourCellOddCoreLocalQuadratic r -
    fourCellOddCoreLocalBilinear centeredP1 r ^ 2

/-- The corrected finite--tail correlation.  This is the term whose sign is
lost by rowwise allocation. -/
def fourCellOddP11FiniteTailCorrectedCross
    (d e f g : ℝ) (r : ℝ → ℝ) : ℝ :=
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  fourCellOddCoreLocalQuadratic centeredP1 *
      fourCellOddCoreLocalBilinear p r -
    fourCellOddCoreLocalBilinear centeredP1 p *
      fourCellOddCoreLocalBilinear centeredP1 r

private theorem positiveHalfOcticEnergy_le_endpointPotentialEnergy_local
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ x : ℝ in 0..1, yoshidaEndpointOctic x * w x ^ 2) ≤
      ∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2 := by
  have hoctic : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointOctic x * w x ^ 2)
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold yoshidaEndpointOctic
    fun_prop
  have hpotential : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * w x ^ 2)
      volume 0 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq w hw).mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  apply intervalIntegral.integral_mono_on_of_le_Ioo
    (by norm_num : (0 : ℝ) ≤ 1) hoctic hpotential
  intro x hx
  exact mul_le_mul_of_nonneg_right
    (octic_le_endpointPotential (by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2]))
    (sq_nonneg (w x))

/-- The exact scalar weight used by the coupled dual is genuinely
nonnegative.  This uses the form-level octic density before replacing it by
the true endpoint potential. -/
theorem fourCellOddP1ExactTailWeight_nonneg
    (w : ℝ → ℝ) (hw : Continuous w) :
    0 ≤ fourCellOddP1ExactTailWeight w := by
  have hmass : 0 ≤ ∫ x : ℝ in 0..1, w x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  have hbase := one_fiftieth_positiveHalfMass_le_rawPrimePotentialTailWeight
    w hw
  have hpotential :=
    positiveHalfOcticEnergy_le_endpointPotentialEnergy_local w hw
  unfold fourCellOddP1ExactTailWeight at ⊢
  nlinarith

/-- Positivity of the already finite `P₃/P₅/P₇/P₉` corrected reserve. -/
def FourCellOddP11FiniteCorrectedReserveNonnegative : Prop :=
  ∀ d e f g : ℝ,
    0 ≤ fourCellOddP11FiniteCorrectedReserve d e f g

/-- Exact identification of the coefficient-level five-mode expression with
the function-level core quadratic.  This is an algebraic API bridge, not a
new positivity estimate. -/
def FourCellOddFiveModeCoreExpressionBridge : Prop :=
  ∀ c d e f g : ℝ,
    fourCellOddCoreLocalQuadratic
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) =
      fourCellOddFiveModeCoreExpression c d e f g

/-- The existing finite Schur theorem supplies the actual finite corrected
reserve as soon as the exact coefficient/function bridge is exposed. -/
theorem fourCellOddP11FiniteCorrectedReserve_nonnegative_of_bridge
    (hbridge : FourCellOddFiveModeCoreExpressionBridge) :
    FourCellOddP11FiniteCorrectedReserveNonnegative := by
  intro d e f g
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  have hp : Continuous p := by
    dsimp only [p]
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g).continuous
  have hp1 :
      fourCellOddOneThreeFiveSevenNineLowProfile 1 0 0 0 0 = centeredP1 := by
    funext t
    unfold fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  have hadd := fourCellOddCoreLocalQuadratic_add centeredP1 p
    (by unfold centeredP1; fun_prop) hp
  have hsum : centeredP1 + p =
      fourCellOddOneThreeFiveSevenNineLowProfile 1 d e f g := by
    funext t
    dsimp only [p]
    unfold fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
      centeredP1
    simp only [Pi.add_apply]
    ring
  rw [hsum, hbridge 1 d e f g] at hadd
  have hA : fourCellOddCoreLocalQuadratic centeredP1 =
      fourCellOddOneThreeFivePerturbed11 := by
    rw [← hp1, hbridge 1 0 0 0 0]
    unfold fourCellOddFiveModeCoreExpression
      fourCellOddOneThreeFivePerturbedQuadratic
    ring
  have hC : fourCellOddCoreLocalQuadratic p =
      fourCellOddFiveModeCoreExpression 0 d e f g := by
    dsimp only [p]
    exact hbridge 0 d e f g
  have hexpand : fourCellOddFiveModeCoreExpression 1 d e f g =
      fourCellOddOneThreeFivePerturbed11 +
        2 * fourCellOddP1FiveModeRow d e f g +
          fourCellOddFiveModeCoreExpression 0 d e f g := by
    unfold fourCellOddFiveModeCoreExpression fourCellOddP1FiveModeRow
      fourCellOddOneThreeFivePerturbedQuadratic
    ring
  have hB : fourCellOddCoreLocalBilinear centeredP1 p =
      fourCellOddP1FiveModeRow d e f g := by
    rw [hA, hC, hexpand] at hadd
    linarith
  have hrow := fourCellOddP1FiveModeRow_sq_le d e f g
  unfold fourCellOddP11FiniteCorrectedReserve
  dsimp only [p] at hA hB hC ⊢
  rw [hA, hB, hC]
  linarith

/-- A single weighted-dual certificate that retains the finite--tail cross.
`D₀` pays the pure `P₁` tail row.  The second inequality charges the corrected
cross to the finite reserve and precisely the unused pivot `A-D₀`. -/
def FourCellOddP11CoupledWeightedDualCertificate : Prop :=
  ∃ D₀ : ℝ,
    D₀ ≤ fourCellOddCoreLocalQuadratic centeredP1 ∧
    ∀ (d e f g : ℝ) (r : ℝ → ℝ),
      ContDiff ℝ 1 r → Function.Odd r →
      centeredOddP1Coefficient r = 0 →
      centeredOddP3Coefficient r = 0 →
      centeredOddP5Coefficient r = 0 →
      centeredOddP7Coefficient r = 0 →
      centeredOddP9Coefficient r = 0 →
      fourCellOddCoreLocalBilinear centeredP1 r ^ 2 ≤
          D₀ * fourCellOddP1ExactTailWeight r ∧
        fourCellOddP11FiniteTailCorrectedCross d e f g r ^ 2 ≤
          fourCellOddP11FiniteCorrectedReserve d e f g *
            (fourCellOddCoreLocalQuadratic centeredP1 - D₀) *
              fourCellOddP1ExactTailWeight r

/-- The coupled weighted-dual certificate proves the actual universal
corrected determinant sign. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_weightedDual
    (hfinite : FourCellOddP11FiniteCorrectedReserveNonnegative)
    (hdual : FourCellOddP11CoupledWeightedDualCertificate) :
    FourCellOddP11CoupledRieszDefectNonnegative := by
  rcases hdual with ⟨D₀, hD₀, hdual⟩
  intro d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let b := fourCellOddCoreLocalBilinear centeredP1 p
  let C := fourCellOddCoreLocalQuadratic p
  let x := fourCellOddCoreLocalBilinear centeredP1 r
  let y := fourCellOddCoreLocalBilinear p r
  let z := fourCellOddCoreLocalQuadratic r
  let W := fourCellOddP1ExactTailWeight r
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact fourCellOddCoreLocalQuadratic_centeredP1_nonneg
  have hF : 0 ≤ A * C - b ^ 2 := by
    simpa only [A, b, C, p, fourCellOddP11FiniteCorrectedReserve] using
      hfinite d e f g
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact fourCellOddP1ExactTailWeight_nonneg r hr.continuous
  have hWz : W ≤ z := by
    dsimp only [W, z]
    exact fourCellOddP1ExactTailWeight_le_core r hr hrodd hr1
  rcases hdual d e f g r hr hrodd hr1 hr3 hr5 hr7 hr9 with
    ⟨hx, hcross⟩
  have h := coupledP1TailSchurDefect_nonneg_of_weightedDual
    (A := A) (b := b) (C := C) (x := x) (y := y) (z := z)
    (W := W) (D₀ := D₀)
    (D₁ := (A * C - b ^ 2) * (A - D₀))
    hA hF hW hWz (by simpa only [A] using hD₀)
    (by simpa only [x, W] using hx)
    (by simpa only [A, b, x, y, W, p,
        fourCellOddP11FiniteTailCorrectedCross,
        fourCellOddP11FiniteCorrectedReserve] using hcross)
    (by rfl)
  simpa only [fourCellOddP11CoupledRieszDefect, p, A, b, C, x, y, z]
    using h

/-- Final structural handoff: the exact five-mode coefficient bridge and the
single coupled weighted-dual certificate close the actual `P₁₁+` defect. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_bridge_weightedDual
    (hbridge : FourCellOddFiveModeCoreExpressionBridge)
    (hdual : FourCellOddP11CoupledWeightedDualCertificate) :
    FourCellOddP11CoupledRieszDefectNonnegative :=
  fourCellOddP11CoupledRieszDefectNonnegative_of_weightedDual
    (fourCellOddP11FiniteCorrectedReserve_nonnegative_of_bridge hbridge) hdual

/-- Exact split of the actual corrected determinant into its finite reserve,
twice the corrected cross, and the tail reserve. -/
theorem fourCellOddP11CoupledRieszDefect_eq_reserves
    (d e f g : ℝ) (r : ℝ → ℝ) :
    fourCellOddP11CoupledRieszDefect d e f g r =
      fourCellOddP11FiniteCorrectedReserve d e f g +
        2 * fourCellOddP11FiniteTailCorrectedCross d e f g r +
          fourCellOddP11TailCorrectedReserve r := by
  unfold fourCellOddP11CoupledRieszDefect
    fourCellOddP11FiniteCorrectedReserve
    fourCellOddP11FiniteTailCorrectedCross
    fourCellOddP11TailCorrectedReserve
  unfold coupledP1TailSchurDefect
  rfl

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
