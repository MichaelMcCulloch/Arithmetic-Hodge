import ArithmeticHodge.Analysis.YoshidaFourCellOddFiveModeStrictCoercivityStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11DirectCorrectedCauchyStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddFiveModeStrictCoercivityStructural
open YoshidaFourCellOddP11ConcreteWeightedDualClosureStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# The direct corrected odd `P₁₁+` Cauchy frontier

A common scalar multiplication reserve loses the correlation between the
degree-one tail row and the other four retained rows.  The invariant norm is
instead obtained by taking the `P₁` Schur complement on both sides:

* `fourCellOddP11FiniteCorrectedReserve` is the corrected low quadratic;
* `fourCellOddP11TailCorrectedReserve` is the corrected tail quadratic;
* `fourCellOddP11FiniteTailCorrectedCross` is their corrected pairing.

This file proves that Cauchy--Schwarz for precisely these three objects is
equivalent to the actual universal corrected defect.  Thus the remaining
analytic problem is one direct four-row/tail contraction; no matched scalar
factor or independent row allocation occurs in the statement.
-/

/-- The exact correlation-preserving Cauchy statement after quotienting the
retained low block and the genuine tail by the common `P₁` row.  Tail
nonnegativity is included explicitly because it is one diagonal of the same
corrected form. -/
def FourCellOddP11DirectCorrectedCauchy : Prop :=
  ∀ (d e f g : ℝ) (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    0 ≤ fourCellOddP11TailCorrectedReserve r ∧
      fourCellOddP11FiniteTailCorrectedCross d e f g r ^ 2 ≤
        fourCellOddP11FiniteCorrectedReserve d e f g *
          fourCellOddP11TailCorrectedReserve r

private theorem centeredOddP1Coefficient_const_mul
    (r : ℝ → ℝ) (t : ℝ) :
    centeredOddP1Coefficient (fun x ↦ t * r x) =
      t * centeredOddP1Coefficient r := by
  unfold centeredOddP1Coefficient
  rw [show (fun x : ℝ ↦ t * r x * centeredP1 x) =
      fun x ↦ t * (r x * centeredP1 x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem centeredOddP3Coefficient_const_mul
    (r : ℝ → ℝ) (t : ℝ) :
    centeredOddP3Coefficient (fun x ↦ t * r x) =
      t * centeredOddP3Coefficient r := by
  unfold centeredOddP3Coefficient
  rw [show (fun x : ℝ ↦ t * r x * centeredP3 x) =
      fun x ↦ t * (r x * centeredP3 x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem centeredOddP5Coefficient_const_mul
    (r : ℝ → ℝ) (t : ℝ) :
    centeredOddP5Coefficient (fun x ↦ t * r x) =
      t * centeredOddP5Coefficient r := by
  unfold centeredOddP5Coefficient
  rw [show (fun x : ℝ ↦ t * r x * factorTwoCenteredP5 x) =
      fun x ↦ t * (r x * factorTwoCenteredP5 x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem centeredOddP7Coefficient_const_mul
    (r : ℝ → ℝ) (t : ℝ) :
    centeredOddP7Coefficient (fun x ↦ t * r x) =
      t * centeredOddP7Coefficient r := by
  unfold centeredOddP7Coefficient
  rw [show (fun x : ℝ ↦ t * r x * factorTwoCenteredP7 x) =
      fun x ↦ t * (r x * factorTwoCenteredP7 x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem centeredOddP9Coefficient_const_mul
    (r : ℝ → ℝ) (t : ℝ) :
    centeredOddP9Coefficient (fun x ↦ t * r x) =
      t * centeredOddP9Coefficient r := by
  unfold centeredOddP9Coefficient
  rw [show (fun x : ℝ ↦ t * r x * factorTwoCenteredP9 x) =
      fun x ↦ t * (r x * factorTwoCenteredP9 x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem odd_const_mul
    {r : ℝ → ℝ} (hodd : Function.Odd r) (t : ℝ) :
    Function.Odd (fun x ↦ t * r x) := by
  intro x
  change t * r (-x) = -(t * r x)
  rw [hodd]
  ring

/-- Exact binary-pencil identity for simultaneous scaling of the corrected
finite direction and tail direction.  It is the algebraic reason the
universal defect contains the full corrected Cauchy inequality, not merely
one sign test. -/
theorem fourCellOddP11CoupledRieszDefect_scale
    (d e f g s t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r) :
    fourCellOddP11CoupledRieszDefect
        (s * d) (s * e) (s * f) (s * g) (fun x ↦ t * r x) =
      fourCellOddP11FiniteCorrectedReserve d e f g * s ^ 2 +
        2 * fourCellOddP11FiniteTailCorrectedCross d e f g r * s * t +
          fourCellOddP11TailCorrectedReserve r * t ^ 2 := by
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  have hp : ContDiff ℝ 1 p := by
    dsimp only [p]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  have hpodd : Function.Odd p := by
    dsimp only [p]
    exact odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  have hP1 : ContDiff ℝ 1 centeredP1 := by
    unfold centeredP1
    fun_prop
  have hP1odd : Function.Odd centeredP1 := by
    intro x
    unfold centeredP1
    ring
  have hprofile :
      fourCellOddOneThreeFiveSevenNineLowProfile
          0 (s * d) (s * e) (s * f) (s * g) =
        fun x ↦ s * p x := by
    funext x
    dsimp only [p]
    unfold fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    ring
  have hsp : ContDiff ℝ 1 (fun x ↦ s * p x) := contDiff_const.mul hp
  have hspodd : Function.Odd (fun x ↦ s * p x) := odd_const_mul hpodd s
  have htr : ContDiff ℝ 1 (fun x ↦ t * r x) := contDiff_const.mul hr
  have htrodd : Function.Odd (fun x ↦ t * r x) := odd_const_mul hodd t
  have hQp := fourCellOddCoreLocalQuadratic_const_mul p hp hpodd s
  have hQr := fourCellOddCoreLocalQuadratic_const_mul r hr hodd t
  have hP1p := fourCellOddCoreLocalBilinear_const_mul_right
    centeredP1 p hP1 hp hP1odd hpodd s
  have hP1r := fourCellOddCoreLocalBilinear_const_mul_right
    centeredP1 r hP1 hr hP1odd hodd t
  have hprRight := fourCellOddCoreLocalBilinear_const_mul_right
    (fun x ↦ s * p x) r hsp hr hspodd hodd t
  have hprLeft := fourCellOddCoreLocalBilinear_const_mul_left
    p r hp hr hpodd hodd s
  rw [fourCellOddP11CoupledRieszDefect_eq_reserves]
  unfold fourCellOddP11FiniteCorrectedReserve
    fourCellOddP11FiniteTailCorrectedCross
    fourCellOddP11TailCorrectedReserve
  dsimp only
  rw [hprofile, hQp, hQr, hP1p, hP1r, hprRight, hprLeft]
  ring

/-- Direct corrected Cauchy implies the production corrected defect. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_directCorrectedCauchy
    (hcauchy : FourCellOddP11DirectCorrectedCauchy) :
    FourCellOddP11CoupledRieszDefectNonnegative := by
  intro d e f g r hr hodd hone hthree hfive hseven hnine
  rcases hcauchy d e f g r hr hodd hone hthree hfive hseven hnine with
    ⟨htail, hcross⟩
  have hfinite : 0 ≤ fourCellOddP11FiniteCorrectedReserve d e f g :=
    fourCellOddP11FiniteCorrectedReserve_nonnegative d e f g
  rw [fourCellOddP11CoupledRieszDefect_eq_reserves]
  let F := fourCellOddP11FiniteCorrectedReserve d e f g
  let X := fourCellOddP11FiniteTailCorrectedCross d e f g r
  let T := fourCellOddP11TailCorrectedReserve r
  have hsum : 0 ≤ F + 2 * X + T := by
    by_cases hX : 0 ≤ X
    · positivity
    · have hminus : 0 ≤ -2 * X := by linarith
      have hdiag : 0 ≤ F + T := add_nonneg hfinite htail
      have hsquares : (-2 * X) ^ 2 ≤ (F + T) ^ 2 := by
        dsimp only [F, X, T] at hcross ⊢
        nlinarith [sq_nonneg
          (fourCellOddP11FiniteCorrectedReserve d e f g -
            fourCellOddP11TailCorrectedReserve r)]
      have hlinear := (sq_le_sq₀ hminus hdiag).mp hsquares
      linarith
  simpa only [F, X, T] using hsum

/-- The universal corrected defect recovers both corrected diagonality and
the full mixed Cauchy inequality by testing every two-parameter scaled
pencil. -/
theorem fourCellOddP11DirectCorrectedCauchy_of_coupledRieszDefectNonnegative
    (hdefect : FourCellOddP11CoupledRieszDefectNonnegative) :
    FourCellOddP11DirectCorrectedCauchy := by
  intro d e f g r hr hodd hone hthree hfive hseven hnine
  let F := fourCellOddP11FiniteCorrectedReserve d e f g
  let X := fourCellOddP11FiniteTailCorrectedCross d e f g r
  let T := fourCellOddP11TailCorrectedReserve r
  have hpencil : ∀ s t : ℝ,
      0 ≤ F * s ^ 2 + 2 * X * s * t + T * t ^ 2 := by
    intro s t
    have hscaled := hdefect
      (s * d) (s * e) (s * f) (s * g) (fun x ↦ t * r x)
      (contDiff_const.mul hr) (odd_const_mul hodd t)
      (by rw [centeredOddP1Coefficient_const_mul, hone, mul_zero])
      (by rw [centeredOddP3Coefficient_const_mul, hthree, mul_zero])
      (by rw [centeredOddP5Coefficient_const_mul, hfive, mul_zero])
      (by rw [centeredOddP7Coefficient_const_mul, hseven, mul_zero])
      (by rw [centeredOddP9Coefficient_const_mul, hnine, mul_zero])
    rw [fourCellOddP11CoupledRieszDefect_scale
      d e f g s t r hr hodd] at hscaled
    simpa only [F, X, T] using hscaled
  rcases (real_quadratic_pencil_nonneg_iff F T X).mp hpencil with
    ⟨_hfinite, htail, hcross⟩
  exact ⟨htail, hcross⟩

/-- Exact characterization of the current odd `P₁₁+` frontier. -/
theorem fourCellOddP11DirectCorrectedCauchy_iff_coupledRieszDefectNonnegative :
    FourCellOddP11DirectCorrectedCauchy ↔
      FourCellOddP11CoupledRieszDefectNonnegative := by
  constructor
  · exact fourCellOddP11CoupledRieszDefectNonnegative_of_directCorrectedCauchy
  · exact fourCellOddP11DirectCorrectedCauchy_of_coupledRieszDefectNonnegative

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11DirectCorrectedCauchyStructural
