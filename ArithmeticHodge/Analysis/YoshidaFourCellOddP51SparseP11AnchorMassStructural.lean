import ArithmeticHodge.Analysis.YoshidaFourCellOddP51GalerkinPivotCoerciveReductionStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualEnergyStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualDualObstructionStructural

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP11AnchorMassStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreOrthogonality
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open ShiftedLegendreCenteredLowModeThreeL2
open ShiftedLegendreCenteredLowModes
open YoshidaEndpointOcticTwoModeSchurData
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddP11GalerkinFiniteSolveStructural
open YoshidaFourCellOddP11GalerkinRieszStructural
open YoshidaFourCellOddP11GalerkinResidualDualObstructionStructural
open YoshidaFourCellOddP11GalerkinResidualEnergyStructural
open YoshidaFourCellOddP11GalerkinSolutionBoxStructural
open YoshidaFourCellOddP11UniversalCoreCauchyStructural
open YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
open YoshidaFourCellOddP13AugmentedOptimalSelectorStructural
open YoshidaFourCellOddP51GalerkinPivotCoerciveReductionStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# The sparse `P11` anchor controls the `P51` mass

The four-coordinate `P3/P5/P7/P9` Galerkin solution is embedded in the
twenty-five-coordinate `P51` block by `Fin.addCases`; every remaining
coordinate is identically zero.  Core orthogonality gives an exact
Pythagorean split between `q51` and the retained correction.  Thus a
nonnegative `P51` pivot, the already certified small `P11` pivot, and the
uniform coercivity bound control the correction without expanding a single
`25 x 25` matrix entry.
-/

/-- Pad any old four-coordinate vector by a zero twenty-one-mode tail. -/
def fourCellOddP51PadP11Coefficients (b : Fin 4 → ℝ) :
    FourCellOddP51RetainedIndex → ℝ :=
  @Fin.addCases 4 21 (fun _ ↦ ℝ)
    b
    (fun _ ↦ 0)

/-- The exact old four-coordinate solve, padded by a zero twenty-one-mode
tail. -/
def fourCellOddP51SparseP11AnchorCoefficients :
    FourCellOddP51RetainedIndex → ℝ :=
  fourCellOddP51PadP11Coefficients
    fourCellOddP11GalerkinRetainedSolution

private theorem sparseP11Anchor_low_apply (i : Fin 4) :
    fourCellOddP51SparseP11AnchorCoefficients (Fin.castAdd 21 i) =
      fourCellOddP11GalerkinRetainedSolution i := by
  simp [fourCellOddP51SparseP11AnchorCoefficients,
    fourCellOddP51PadP11Coefficients]

private theorem sparseP11Anchor_high_apply (i : Fin 21) :
    fourCellOddP51SparseP11AnchorCoefficients (Fin.natAdd 4 i) = 0 := by
  simp [fourCellOddP51SparseP11AnchorCoefficients,
    fourCellOddP51PadP11Coefficients]

/-- The zero padding intertwines the generic and old retained-profile
interpretations. -/
theorem fourCellOddP51PadP11Coefficients_profile_eq (b : Fin 4 → ℝ) :
    fourCellOddP51RetainedProfile (fourCellOddP51PadP11Coefficients b) =
      fourCellOddP11GalerkinRetainedProfile b := by
  funext x
  unfold fourCellOddP51RetainedProfile fourCellOddFiniteRetainedProfile
  change (∑ i : Fin (4 + 21),
      fourCellOddP51PadP11Coefficients b i *
        fourCellOddFiniteRetainedBasis i x) = _
  rw [Fin.sum_univ_add]
  simp only [fourCellOddP51PadP11Coefficients, Fin.addCases_left,
    Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero]
  simp [Fin.sum_univ_succ, fourCellOddFiniteRetainedBasis,
    fourCellOddFiniteRetainedDegree, centeredShiftedLegendreReal,
    shiftedLegendreReal, Polynomial.shiftedLegendre,
    Finset.sum_range_succ, Polynomial.smul_eq_C_mul,
    fourCellOddP11GalerkinRetainedProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile, factorTwoOddStructuralLowProfile,
    centeredP1, centeredP3, factorTwoCenteredP5,
    factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  norm_num [Nat.choose]
  ring

/-- The sparse embedding reconstructs exactly the old retained profile. -/
theorem fourCellOddP51SparseP11Anchor_profile_eq :
    fourCellOddP51RetainedProfile
        fourCellOddP51SparseP11AnchorCoefficients =
      fourCellOddP11GalerkinRetainedProfile
        fourCellOddP11GalerkinRetainedSolution := by
  exact fourCellOddP51PadP11Coefficients_profile_eq _

/-- Retained coefficient correction from the sparse old solve to the exact
`P51` solve. -/
def fourCellOddP51SparseP11CorrectionCoefficients :
    FourCellOddP51RetainedIndex → ℝ :=
  fourCellOddP51RetainedSolution -
    fourCellOddP51SparseP11AnchorCoefficients

/-- The function represented by the retained coefficient correction. -/
def fourCellOddP51SparseP11Correction : ℝ → ℝ :=
  fourCellOddP51RetainedProfile
    fourCellOddP51SparseP11CorrectionCoefficients

theorem contDiff_fourCellOddP51SparseP11Correction :
    ContDiff ℝ 1 fourCellOddP51SparseP11Correction := by
  exact contDiff_fourCellOddFiniteRetainedProfile 24 _

theorem odd_fourCellOddP51SparseP11Correction :
    Function.Odd fourCellOddP51SparseP11Correction := by
  exact odd_fourCellOddFiniteRetainedProfile 24 _

private theorem p51Projection_eq_sparseAnchor_add_correction :
    fourCellOddP51RetainedProfile fourCellOddP51RetainedSolution =
      fourCellOddP51RetainedProfile
          fourCellOddP51SparseP11AnchorCoefficients +
        fourCellOddP51SparseP11Correction := by
  funext x
  unfold fourCellOddP51SparseP11Correction
    fourCellOddP51SparseP11CorrectionCoefficients
  change fourCellOddFiniteRetainedProfile 24
      fourCellOddP51RetainedSolution x =
    fourCellOddFiniteRetainedProfile 24
        fourCellOddP51SparseP11AnchorCoefficients x +
      fourCellOddFiniteRetainedProfile 24
        (fourCellOddP51RetainedSolution -
          fourCellOddP51SparseP11AnchorCoefficients) x
  unfold fourCellOddFiniteRetainedProfile
  simp only [Pi.sub_apply, Finset.sum_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The old four-mode residual is exactly `q51` plus one retained
correction. -/
theorem fourCellOddP11Residual_eq_q51_add_sparseCorrection :
    fourCellOddP11GalerkinRetainedResidualProfile =
      fourCellOddQ51 + fourCellOddP51SparseP11Correction := by
  funext x
  have hprojection := congrFun p51Projection_eq_sparseAnchor_add_correction x
  rw [fourCellOddP51SparseP11Anchor_profile_eq] at hprojection
  simp only [Pi.add_apply] at hprojection
  change fourCellOddFiniteRetainedProfile 24
      fourCellOddP51RetainedSolution x =
    fourCellOddP11GalerkinLowProfile
        (fourCellOddP11GalerkinRetainedSolution 0)
        (fourCellOddP11GalerkinRetainedSolution 1)
        (fourCellOddP11GalerkinRetainedSolution 2)
        (fourCellOddP11GalerkinRetainedSolution 3) x +
      fourCellOddP51SparseP11Correction x at hprojection
  unfold fourCellOddP11GalerkinRetainedResidualProfile
    fourCellOddP11GalerkinResidualProfile fourCellOddQ51
    fourCellOddP51GalerkinResidualProfile
    fourCellOddFiniteGalerkinResidualProfile
  simp only [Pi.add_apply]
  linarith

/-- The approximate residual attached to the padded coefficient vector is
literally the old four-mode Galerkin residual. -/
theorem fourCellOddP51SparseP11ApproximateResidual_eq :
    fourCellOddP51ApproximateResidual
        fourCellOddP51SparseP11AnchorCoefficients =
      fourCellOddP11GalerkinRetainedResidualProfile := by
  funext x
  unfold fourCellOddP51ApproximateResidual
    fourCellOddFiniteGalerkinResidualProfile
    fourCellOddP11GalerkinRetainedResidualProfile
    fourCellOddP11GalerkinResidualProfile
  have hprofile := congrFun fourCellOddP51SparseP11Anchor_profile_eq x
  change fourCellOddFiniteRetainedProfile 24
      fourCellOddP51SparseP11AnchorCoefficients x =
    fourCellOddP11GalerkinLowProfile
      (fourCellOddP11GalerkinRetainedSolution 0)
      (fourCellOddP11GalerkinRetainedSolution 1)
      (fourCellOddP11GalerkinRetainedSolution 2)
      (fourCellOddP11GalerkinRetainedSolution 3) x at hprofile
  rw [hprofile]

private def fourCellOddP11CoordinateUnit (i : Fin 4) : Fin 4 → ℝ :=
  fun j ↦ if j = i then 1 else 0

private theorem paddedP11CoordinateUnit_profile_eq_basis (i : Fin 4) :
    fourCellOddP51RetainedProfile
        (fourCellOddP51PadP11Coefficients
          (fourCellOddP11CoordinateUnit i)) =
      fourCellOddFiniteRetainedBasis (Fin.castAdd 21 i) := by
  funext x
  unfold fourCellOddP51RetainedProfile fourCellOddFiniteRetainedProfile
    fourCellOddP51PadP11Coefficients fourCellOddP11CoordinateUnit
  change (∑ j : Fin (4 + 21),
      Fin.addCases (fun k : Fin 4 ↦ if k = i then 1 else 0)
          (fun _ : Fin 21 ↦ 0) j *
        fourCellOddFiniteRetainedBasis j x) = _
  rw [Fin.sum_univ_add]
  simp

/-- All four old normal rows vanish exactly for the sparse anchor. -/
theorem fourCellOddP51SparseP11Anchor_low_normal_row_eq_zero (i : Fin 4) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP51ApproximateResidual
          fourCellOddP51SparseP11AnchorCoefficients)
        (fourCellOddFiniteRetainedBasis (Fin.castAdd 21 i)) = 0 := by
  rw [fourCellOddP51SparseP11ApproximateResidual_eq,
    ← paddedP11CoordinateUnit_profile_eq_basis,
    fourCellOddP51PadP11Coefficients_profile_eq]
  unfold fourCellOddP11GalerkinRetainedResidualProfile
  exact fourCellOddP11GalerkinRetainedSolution_orthogonal
    (fourCellOddP11CoordinateUnit i 0)
    (fourCellOddP11CoordinateUnit i 1)
    (fourCellOddP11CoordinateUnit i 2)
    (fourCellOddP11CoordinateUnit i 3)

/-- The sparse normal-residual energy is a single unenumerated high-mode
sum: the solved `P3/P5/P7/P9` block contributes identically zero. -/
def fourCellOddP51SparseP11HighNormalResidualEnergy : ℝ :=
  ∑ i : Fin 21,
    (2 * (@fourCellOddFiniteRetainedDegree 24
        (Fin.natAdd 4 i : Fin 25) : ℝ) + 1) *
      fourCellOddCoreLocalBilinear
        fourCellOddP11GalerkinRetainedResidualProfile
        (fourCellOddFiniteRetainedBasis
          (Fin.natAdd 4 i : Fin 25)) ^ 2

theorem fourCellOddP51SparseP11NormalResidualEnergy_eq_high :
    fourCellOddP51NormalResidualEnergy
        fourCellOddP51SparseP11AnchorCoefficients =
      fourCellOddP51SparseP11HighNormalResidualEnergy := by
  unfold fourCellOddP51SparseP11HighNormalResidualEnergy
  unfold fourCellOddP51NormalResidualEnergy
  rw [fourCellOddP51SparseP11ApproximateResidual_eq]
  change (∑ i : Fin (4 + 21),
      (2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1) *
        fourCellOddCoreLocalBilinear
          fourCellOddP11GalerkinRetainedResidualProfile
          (fourCellOddFiniteRetainedBasis i) ^ 2) = _
  rw [Fin.sum_univ_add]
  have hlow (i : Fin 4) :
      fourCellOddCoreLocalBilinear
          fourCellOddP11GalerkinRetainedResidualProfile
          (fourCellOddFiniteRetainedBasis (Fin.castAdd 21 i)) = 0 := by
    simpa only [fourCellOddP51SparseP11ApproximateResidual_eq] using
      fourCellOddP51SparseP11Anchor_low_normal_row_eq_zero i
  simp_rw [hlow]
  simp

private theorem q51_orthogonal_sparseCorrection :
    fourCellOddCoreLocalBilinear fourCellOddQ51
      fourCellOddP51SparseP11Correction = 0 := by
  exact fourCellOddQ51_finiteOrthogonal
    fourCellOddP51SparseP11CorrectionCoefficients

/-- Core Pythagoras for the sparse anchor; no finite matrix entry appears. -/
theorem fourCellOddP11Residual_quadratic_eq_q51_add_sparseCorrection :
    fourCellOddCoreLocalQuadratic
        fourCellOddP11GalerkinRetainedResidualProfile =
      fourCellOddP51GalerkinPivot +
        fourCellOddCoreLocalQuadratic
          fourCellOddP51SparseP11Correction := by
  rw [fourCellOddP11Residual_eq_q51_add_sparseCorrection,
    fourCellOddCoreLocalQuadratic_add fourCellOddQ51
      fourCellOddP51SparseP11Correction
      contDiff_fourCellOddQ51.continuous
      contDiff_fourCellOddP51SparseP11Correction.continuous,
    q51_orthogonal_sparseCorrection]
  unfold fourCellOddP51GalerkinPivot
  ring

/-- One scalar high-row budget for the sparse anchor implies the desired
`7/10000` floor.  This is the exact remaining analytic target for this
anchor: the first four coordinates have already been solved, while no
`25 x 25` determinant or inverse is expanded. -/
theorem seven_div_ten_thousand_le_fourCellOddP51GalerkinPivot_of_sparseP11
    (hcertificate :
      fourCellOddP51NormalResidualEnergy
          fourCellOddP51SparseP11AnchorCoefficients ≤
        fourCellOddNineteenTwentiethsCoercivityConstant *
          (fourCellOddCoreLocalQuadratic
              fourCellOddP11GalerkinRetainedResidualProfile -
            (7 / 10000 : ℝ))) :
    (7 / 10000 : ℝ) ≤ fourCellOddP51GalerkinPivot := by
  have hcorrection :=
    fourCellOddP51_correction_energy_le_normalResidualEnergy_div_exact
      fourCellOddP51SparseP11AnchorCoefficients
  change fourCellOddCoreLocalQuadratic
      fourCellOddP51SparseP11Correction ≤
    fourCellOddP51NormalResidualEnergy
        fourCellOddP51SparseP11AnchorCoefficients /
      fourCellOddNineteenTwentiethsCoercivityConstant at hcorrection
  have hkappa := fourCellOddNineteenTwentiethsCoercivityConstant_pos
  have hbudget :
      fourCellOddP51NormalResidualEnergy
          fourCellOddP51SparseP11AnchorCoefficients /
          fourCellOddNineteenTwentiethsCoercivityConstant ≤
        fourCellOddCoreLocalQuadratic
            fourCellOddP11GalerkinRetainedResidualProfile -
          (7 / 10000 : ℝ) := by
    apply (div_le_iff₀ hkappa).2
    simpa [mul_comm] using hcertificate
  have hsplit :=
    fourCellOddP11Residual_quadratic_eq_q51_add_sparseCorrection
  linarith

/-- High-mode-only form of the same floor certificate. -/
theorem seven_div_ten_thousand_le_fourCellOddP51GalerkinPivot_of_sparseP11High
    (hcertificate :
      fourCellOddP51SparseP11HighNormalResidualEnergy ≤
        fourCellOddNineteenTwentiethsCoercivityConstant *
          (fourCellOddCoreLocalQuadratic
              fourCellOddP11GalerkinRetainedResidualProfile -
            (7 / 10000 : ℝ))) :
    (7 / 10000 : ℝ) ≤ fourCellOddP51GalerkinPivot := by
  apply
    seven_div_ten_thousand_le_fourCellOddP51GalerkinPivot_of_sparseP11
  rwa [fourCellOddP51SparseP11NormalResidualEnergy_eq_high]

/-- The old retained projection has positive-half mass below `1/5`.
This is just the four diagonal Legendre weights and the public solution
box. -/
theorem integral_zero_one_sparseP11Anchor_sq_lt_one_fifth :
    (∫ x : ℝ in 0..1,
      fourCellOddP51RetainedProfile
        fourCellOddP51SparseP11AnchorCoefficients x ^ 2) <
      (1 / 5 : ℝ) := by
  rw [show fourCellOddP51RetainedProfile
        fourCellOddP51SparseP11AnchorCoefficients =
      fourCellOddFiniteRetainedProfile 24
        fourCellOddP51SparseP11AnchorCoefficients by rfl,
    integral_zero_one_fourCellOddFiniteRetainedProfile_sq]
  change (∑ i : Fin (4 + 21),
      fourCellOddP51SparseP11AnchorCoefficients i ^ 2 /
        (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1)) < _
  rw [Fin.sum_univ_add]
  simp only [sparseP11Anchor_low_apply, sparseP11Anchor_high_apply,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div,
    Finset.sum_const_zero, add_zero]
  simp [Fin.sum_univ_succ, fourCellOddFiniteRetainedDegree]
  rcases fourCellOddP11GalerkinRetainedSolution_coordinate_bounds with
    ⟨hs0lo, hs0hi, hs1lo, hs1hi, hs2lo, hs2hi, hs3lo, hs3hi⟩
  have hs0sq : fourCellOddP11GalerkinRetainedSolution 0 ^ 2 <
      (115 / 100 : ℝ) ^ 2 := by nlinarith
  have hs1sq : fourCellOddP11GalerkinRetainedSolution 1 ^ 2 <
      (23 / 100 : ℝ) ^ 2 := by nlinarith
  have hs2sq : fourCellOddP11GalerkinRetainedSolution 2 ^ 2 <
      (7 / 100 : ℝ) ^ 2 := by nlinarith
  have hs3sq : fourCellOddP11GalerkinRetainedSolution 3 ^ 2 <
      (3 / 100 : ℝ) ^ 2 := by nlinarith
  nlinarith

/-- A nonnegative exact `P51` pivot forces the sparse-anchor correction to
have mass below `45/343`. -/
theorem integral_zero_one_sparseP11Correction_sq_lt
    (hpivot : FourCellOddP51GalerkinPivotNonnegative) :
    (∫ x : ℝ in 0..1, fourCellOddP51SparseP11Correction x ^ 2) <
      (45 / 343 : ℝ) := by
  have hsplit :=
    fourCellOddP11Residual_quadratic_eq_q51_add_sparseCorrection
  have hanchor :=
    fourCellOddCoreLocalQuadratic_exactGalerkinResidual_lt_nine_div_2500
  have hcorrectionCore :
      fourCellOddCoreLocalQuadratic
          fourCellOddP51SparseP11Correction < (9 / 2500 : ℝ) := by
    change 0 ≤ fourCellOddP51GalerkinPivot at hpivot
    nlinarith
  have hcoercive := fourCellOddCorePositiveHalfCoerciveAt_rationalFloor
    fourCellOddP51SparseP11Correction
    contDiff_fourCellOddP51SparseP11Correction
    odd_fourCellOddP51SparseP11Correction
    (centeredOddP1Coefficient_fourCellOddFiniteRetainedProfile_eq_zero
      24 fourCellOddP51SparseP11CorrectionCoefficients)
  change (343 / 12500 : ℝ) *
      (∫ x : ℝ in 0..1, fourCellOddP51SparseP11Correction x ^ 2) ≤
        fourCellOddCoreLocalQuadratic
          fourCellOddP51SparseP11Correction at hcoercive
  nlinarith

private theorem continuous_centeredP1 : Continuous centeredP1 := by
  unfold centeredP1
  fun_prop

private theorem odd_centeredP1 : Function.Odd centeredP1 := by
  intro x
  unfold centeredP1
  ring

/-- Positive-half `P1` orthogonality of every generic finite retained
profile. -/
theorem integral_zero_one_centeredP1_mul_finiteRetained_eq_zero
    (N : ℕ) (a : Fin (N + 1) → ℝ) :
    (∫ x : ℝ in 0..1,
      centeredP1 x * fourCellOddFiniteRetainedProfile N a x) = 0 := by
  let p := fourCellOddFiniteRetainedProfile N a
  have hp : Continuous p :=
    (contDiff_fourCellOddFiniteRetainedProfile N a).continuous
  have hpodd : Function.Odd p :=
    odd_fourCellOddFiniteRetainedProfile N a
  have hcoefficient :=
    centeredOddP1Coefficient_fourCellOddFiniteRetainedProfile_eq_zero N a
  have hfull : (∫ x : ℝ in -1..1, centeredP1 x * p x) = 0 := by
    unfold centeredOddP1Coefficient at hcoefficient
    rw [show (fun x : ℝ ↦ centeredP1 x * p x) =
        fun x ↦ p x * centeredP1 x by
      funext x
      ring]
    nlinarith
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ centeredP1 x * p x)
    ((continuous_centeredP1.mul hp).intervalIntegrable _ _)
    (by
      intro x
      change centeredP1 (-x) * p (-x) = centeredP1 x * p x
      rw [odd_centeredP1, hpodd]
      ring)
  rw [hfull] at hfold
  dsimp only [p] at hfold ⊢
  linarith

/-- Exact Legendre Pythagoras for every finite Galerkin residual, before
using any normal equation. -/
theorem integral_zero_one_fourCellOddFiniteGalerkinResidualProfile_sq
    (N : ℕ) (a : Fin (N + 1) → ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddFiniteGalerkinResidualProfile N a x ^ 2) =
      (1 / 3 : ℝ) +
        ∫ x : ℝ in 0..1,
          fourCellOddFiniteRetainedProfile N a x ^ 2 := by
  let p := fourCellOddFiniteRetainedProfile N a
  have hp : Continuous p :=
    (contDiff_fourCellOddFiniteRetainedProfile N a).continuous
  have h11 : IntervalIntegrable (fun x : ℝ ↦ centeredP1 x ^ 2)
      volume 0 1 := (continuous_centeredP1.pow 2).intervalIntegrable _ _
  have h1p : IntervalIntegrable (fun x : ℝ ↦ centeredP1 x * p x)
      volume 0 1 := (continuous_centeredP1.mul hp).intervalIntegrable _ _
  have hpp : IntervalIntegrable (fun x : ℝ ↦ p x ^ 2)
      volume 0 1 := (hp.pow 2).intervalIntegrable _ _
  have hcross := integral_zero_one_centeredP1_mul_finiteRetained_eq_zero N a
  have hP1 : (∫ x : ℝ in 0..1, centeredP1 x ^ 2) = 1 / 3 := by
    have hfold := integral_sq_eq_two_mul_positiveHalf
      centeredP1 continuous_centeredP1 (Or.inr odd_centeredP1)
    rw [integral_centeredP1_sq] at hfold
    linarith
  unfold fourCellOddFiniteGalerkinResidualProfile
  rw [show (fun x : ℝ ↦
      (centeredP1 x - fourCellOddFiniteRetainedProfile N a x) ^ 2) =
      fun x ↦ centeredP1 x ^ 2 -
        2 * (centeredP1 x * p x) + p x ^ 2 by
    funext x
    dsimp only [p]
    ring,
    intervalIntegral.integral_add
      (h11.sub (h1p.const_mul _)) hpp,
    intervalIntegral.integral_sub h11 (h1p.const_mul _),
    intervalIntegral.integral_const_mul, hP1]
  dsimp only [p] at hcross ⊢
  rw [hcross]
  ring

/-- Structural mass bound for the exact `P51` residual.  The only premise
is the sign of its scalar Schur pivot; the proof uses four old coordinates,
not the twenty-five new ones. -/
theorem integral_zero_one_fourCellOddQ51_sq_lt_one
    (hpivot : FourCellOddP51GalerkinPivotNonnegative) :
    (∫ x : ℝ in 0..1, fourCellOddQ51 x ^ 2) < 1 := by
  let p := fourCellOddP51RetainedProfile fourCellOddP51RetainedSolution
  let a := fourCellOddP51RetainedProfile
    fourCellOddP51SparseP11AnchorCoefficients
  let d := fourCellOddP51SparseP11Correction
  have hp : Continuous p :=
    (contDiff_fourCellOddFiniteRetainedProfile 24 _).continuous
  have ha : Continuous a :=
    (contDiff_fourCellOddFiniteRetainedProfile 24 _).continuous
  have hd : Continuous d :=
    contDiff_fourCellOddP51SparseP11Correction.continuous
  have hreconstruct : p = a + d := by
    dsimp only [p, a, d]
    exact p51Projection_eq_sparseAnchor_add_correction
  have hpoint (x : ℝ) :
      p x ^ 2 ≤ (9 / 5 : ℝ) * a x ^ 2 + (9 / 4 : ℝ) * d x ^ 2 := by
    rw [hreconstruct]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (4 * a x - 5 * d x)]
  have hleft : IntervalIntegrable (fun x : ℝ ↦ p x ^ 2) volume 0 1 :=
    (hp.pow 2).intervalIntegrable _ _
  have haI : IntervalIntegrable (fun x : ℝ ↦ a x ^ 2) volume 0 1 :=
    (ha.pow 2).intervalIntegrable _ _
  have hdI : IntervalIntegrable (fun x : ℝ ↦ d x ^ 2) volume 0 1 :=
    (hd.pow 2).intervalIntegrable _ _
  have hright : IntervalIntegrable
      (fun x : ℝ ↦ (9 / 5 : ℝ) * a x ^ 2 +
        (9 / 4 : ℝ) * d x ^ 2) volume 0 1 :=
    (haI.const_mul _).add (hdI.const_mul _)
  have hmono := intervalIntegral.integral_mono
    (by norm_num : (0 : ℝ) ≤ 1)
    hleft hright
    hpoint
  rw [intervalIntegral.integral_add (haI.const_mul _) (hdI.const_mul _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hmono
  have hanchor := integral_zero_one_sparseP11Anchor_sq_lt_one_fifth
  have hcorrection := integral_zero_one_sparseP11Correction_sq_lt hpivot
  change (∫ x : ℝ in 0..1, a x ^ 2) < (1 / 5 : ℝ) at hanchor
  change (∫ x : ℝ in 0..1, d x ^ 2) < (45 / 343 : ℝ) at hcorrection
  have hprojection : (∫ x : ℝ in 0..1, p x ^ 2) < (2 / 3 : ℝ) := by
    nlinarith
  have hmass :=
    integral_zero_one_fourCellOddFiniteGalerkinResidualProfile_sq
      24 fourCellOddP51RetainedSolution
  change (∫ x : ℝ in 0..1, fourCellOddQ51 x ^ 2) =
    (1 / 3 : ℝ) + ∫ x : ℝ in 0..1, p x ^ 2 at hmass
  nlinarith

theorem integral_zero_one_fourCellOddQ51_sq_le_one
    (hpivot : FourCellOddP51GalerkinPivotNonnegative) :
    (∫ x : ℝ in 0..1, fourCellOddQ51 x ^ 2) ≤ 1 :=
  (integral_zero_one_fourCellOddQ51_sq_lt_one hpivot).le

/-- The single high-mode scalar certificate simultaneously supplies the
production pivot floor and the exact auxiliary mass bound. -/
theorem fourCellOddP51SparseP11HighCertificate_closes_floor_and_mass
    (hcertificate :
      fourCellOddP51SparseP11HighNormalResidualEnergy ≤
        fourCellOddNineteenTwentiethsCoercivityConstant *
          (fourCellOddCoreLocalQuadratic
              fourCellOddP11GalerkinRetainedResidualProfile -
            (7 / 10000 : ℝ))) :
    (7 / 10000 : ℝ) ≤ fourCellOddP51GalerkinPivot ∧
      (∫ x : ℝ in 0..1, fourCellOddQ51 x ^ 2) ≤ 1 := by
  have hpivot :=
    seven_div_ten_thousand_le_fourCellOddP51GalerkinPivot_of_sparseP11High
      hcertificate
  refine ⟨hpivot, integral_zero_one_fourCellOddQ51_sq_le_one ?_⟩
  change 0 ≤ fourCellOddP51GalerkinPivot
  exact (by norm_num : (0 : ℝ) ≤ 7 / 10000).trans hpivot

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP11AnchorMassStructural
