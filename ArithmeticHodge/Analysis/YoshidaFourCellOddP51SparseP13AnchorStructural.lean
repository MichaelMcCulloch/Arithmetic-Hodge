import ArithmeticHodge.Analysis.YoshidaFourCellOddP51GalerkinPivotCoerciveReductionStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP13RetainedFiniteSolveStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP11AnchorBesselStructural

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP13AnchorStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreOrthogonality
open ShiftedLegendreCenteredLowModeThreeL2
open ShiftedLegendreCenteredLowModes
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP13AugmentedDecompositionStructural
open YoshidaFourCellOddP13AugmentedResidualRepresenterStructural
open YoshidaFourCellOddP13RetentionStructural
open YoshidaFourCellOddP13RetainedFiniteSolveStructural
open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddP51GalerkinPivotCoerciveReductionStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51SparseP11AnchorBesselStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# The exact retained `P13` solve as a sparse `P51` anchor

The exact six-coordinate `P3/P5/P7/P9/P11/P13` Galerkin solution is
embedded in the twenty-five-coordinate `P51` block by one zero padding.
Its first six normal rows vanish by the universal finite-solve normality
theorem.  Hence the full defect is exactly one unenumerated nineteen-row
tail, and core orthogonality gives an exact Pythagorean pivot split.
-/

/-- Pad a six-coordinate vector by a zero nineteen-coordinate tail. -/
def fourCellOddP51PadP13Coefficients (b : Fin 6 → ℝ) :
    FourCellOddP51RetainedIndex → ℝ :=
  @Fin.addCases 6 19 (fun _ ↦ ℝ) b (fun _ ↦ 0)

/-- The exact retained `P13` solution, padded into the `P51` block. -/
def fourCellOddP51SparseP13AnchorCoefficients :
    FourCellOddP51RetainedIndex → ℝ :=
  fourCellOddP51PadP13Coefficients fourCellOddP13RetainedSolution

private theorem sparseP13Anchor_low_apply (i : Fin 6) :
    fourCellOddP51SparseP13AnchorCoefficients (Fin.castAdd 19 i) =
      fourCellOddP13RetainedSolution i := by
  simp [fourCellOddP51SparseP13AnchorCoefficients,
    fourCellOddP51PadP13Coefficients]

private theorem sparseP13Anchor_high_apply (i : Fin 19) :
    fourCellOddP51SparseP13AnchorCoefficients (Fin.natAdd 6 i) = 0 := by
  simp [fourCellOddP51SparseP13AnchorCoefficients,
    fourCellOddP51PadP13Coefficients]

/-- Zero padding intertwines the generic and exact retained-`P13`
profile interpretations. -/
theorem fourCellOddP51PadP13Coefficients_profile_eq (b : Fin 6 → ℝ) :
    fourCellOddP51RetainedProfile (fourCellOddP51PadP13Coefficients b) =
      fourCellOddP13RetainedProfile b := by
  funext x
  unfold fourCellOddP51RetainedProfile fourCellOddFiniteRetainedProfile
  change (∑ i : Fin (6 + 19),
      fourCellOddP51PadP13Coefficients b i *
        fourCellOddFiniteRetainedBasis i x) = _
  rw [Fin.sum_univ_add]
  simp only [fourCellOddP51PadP13Coefficients, Fin.addCases_left,
    Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero]
  simp [Fin.sum_univ_succ, fourCellOddFiniteRetainedBasis,
    fourCellOddFiniteRetainedDegree, centeredShiftedLegendreReal,
    shiftedLegendreReal, Polynomial.shiftedLegendre,
    Finset.sum_range_succ, Polynomial.smul_eq_C_mul,
    fourCellOddP13RetainedProfile, fourCellOddP13SevenModeProfile,
    fourCellOddP13SixModeProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile, factorTwoOddStructuralLowProfile,
    centeredP1, centeredP3, factorTwoCenteredP5,
    factorTwoCenteredP7_eq, factorTwoCenteredP9_eq,
    fourCellOddP11DirectTail, fourCellOddP13DirectTail]
  norm_num [Nat.choose]
  ring

/-- The sparse embedding reconstructs exactly the retained `P13` profile. -/
theorem fourCellOddP51SparseP13Anchor_profile_eq :
    fourCellOddP51RetainedProfile
        fourCellOddP51SparseP13AnchorCoefficients =
      fourCellOddP13RetainedProfile fourCellOddP13RetainedSolution := by
  exact fourCellOddP51PadP13Coefficients_profile_eq _

/-- The exact residual attached to the retained `P13` solve. -/
def fourCellOddP13RetainedSolvedResidual : ℝ → ℝ :=
  fourCellOddP13RetainedGalerkinResidualProfile
    (fourCellOddP13RetainedSolution 0)
    (fourCellOddP13RetainedSolution 1)
    (fourCellOddP13RetainedSolution 2)
    (fourCellOddP13RetainedSolution 3)
    (fourCellOddP13RetainedSolution 4)
    (fourCellOddP13RetainedSolution 5)

theorem contDiff_fourCellOddP13RetainedSolvedResidual :
    ContDiff ℝ 1 fourCellOddP13RetainedSolvedResidual := by
  exact contDiff_fourCellOddP13RetainedGalerkinResidualProfile _ _ _ _ _ _

theorem odd_fourCellOddP13RetainedSolvedResidual :
    Function.Odd fourCellOddP13RetainedSolvedResidual := by
  exact odd_fourCellOddP13RetainedGalerkinResidualProfile _ _ _ _ _ _

private theorem retainedSolution_vector_literal :
    (![fourCellOddP13RetainedSolution 0,
        fourCellOddP13RetainedSolution 1,
        fourCellOddP13RetainedSolution 2,
        fourCellOddP13RetainedSolution 3,
        fourCellOddP13RetainedSolution 4,
        fourCellOddP13RetainedSolution 5] : Fin 6 → ℝ) =
      fourCellOddP13RetainedSolution := by
  funext i
  fin_cases i <;> rfl

/-- The approximate residual of the padded vector is literally the exact
retained-`P13` residual. -/
theorem fourCellOddP51SparseP13ApproximateResidual_eq :
    fourCellOddP51ApproximateResidual
        fourCellOddP51SparseP13AnchorCoefficients =
      fourCellOddP13RetainedSolvedResidual := by
  funext x
  unfold fourCellOddP51ApproximateResidual
    fourCellOddFiniteGalerkinResidualProfile
    fourCellOddP13RetainedSolvedResidual
    fourCellOddP13RetainedGalerkinResidualProfile
  rw [retainedSolution_vector_literal]
  have hprofile := congrFun fourCellOddP51SparseP13Anchor_profile_eq x
  change fourCellOddFiniteRetainedProfile 24
      fourCellOddP51SparseP13AnchorCoefficients x =
    fourCellOddP13RetainedProfile fourCellOddP13RetainedSolution x at hprofile
  rw [hprofile]

/-- Retained coefficient correction from the sparse `P13` solve to the
exact `P51` solve. -/
def fourCellOddP51SparseP13CorrectionCoefficients :
    FourCellOddP51RetainedIndex → ℝ :=
  fourCellOddP51RetainedSolution -
    fourCellOddP51SparseP13AnchorCoefficients

/-- Function represented by the retained coefficient correction. -/
def fourCellOddP51SparseP13Correction : ℝ → ℝ :=
  fourCellOddP51RetainedProfile
    fourCellOddP51SparseP13CorrectionCoefficients

theorem contDiff_fourCellOddP51SparseP13Correction :
    ContDiff ℝ 1 fourCellOddP51SparseP13Correction := by
  exact contDiff_fourCellOddFiniteRetainedProfile 24 _

theorem odd_fourCellOddP51SparseP13Correction :
    Function.Odd fourCellOddP51SparseP13Correction := by
  exact odd_fourCellOddFiniteRetainedProfile 24 _

private theorem p51Projection_eq_sparseP13Anchor_add_correction :
    fourCellOddP51RetainedProfile fourCellOddP51RetainedSolution =
      fourCellOddP51RetainedProfile
          fourCellOddP51SparseP13AnchorCoefficients +
        fourCellOddP51SparseP13Correction := by
  funext x
  unfold fourCellOddP51SparseP13Correction
    fourCellOddP51SparseP13CorrectionCoefficients
  change fourCellOddFiniteRetainedProfile 24
      fourCellOddP51RetainedSolution x =
    fourCellOddFiniteRetainedProfile 24
        fourCellOddP51SparseP13AnchorCoefficients x +
      fourCellOddFiniteRetainedProfile 24
        (fourCellOddP51RetainedSolution -
          fourCellOddP51SparseP13AnchorCoefficients) x
  unfold fourCellOddFiniteRetainedProfile
  simp only [Pi.sub_apply, Finset.sum_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Exact pivot decomposition at the retained-`P13` anchor. -/
theorem fourCellOddP13RetainedSolvedResidual_eq_q51_add_sparseCorrection :
    fourCellOddP13RetainedSolvedResidual =
      fourCellOddQ51 + fourCellOddP51SparseP13Correction := by
  funext x
  have hprojection :=
    congrFun p51Projection_eq_sparseP13Anchor_add_correction x
  rw [fourCellOddP51SparseP13Anchor_profile_eq] at hprojection
  simp only [Pi.add_apply] at hprojection
  unfold fourCellOddP13RetainedSolvedResidual
    fourCellOddP13RetainedGalerkinResidualProfile fourCellOddQ51
    fourCellOddP51GalerkinResidualProfile
    fourCellOddFiniteGalerkinResidualProfile
  rw [retainedSolution_vector_literal]
  simp only [Pi.add_apply]
  change fourCellOddFiniteRetainedProfile 24
      fourCellOddP51RetainedSolution x =
    fourCellOddP13RetainedProfile fourCellOddP13RetainedSolution x +
      fourCellOddP51SparseP13Correction x at hprojection
  linarith

private def fourCellOddP13CoordinateUnit (i : Fin 6) : Fin 6 → ℝ :=
  fun j ↦ if j = i then 1 else 0

private theorem paddedP13CoordinateUnit_profile_eq_basis (i : Fin 6) :
    fourCellOddP51RetainedProfile
        (fourCellOddP51PadP13Coefficients
          (fourCellOddP13CoordinateUnit i)) =
      fourCellOddFiniteRetainedBasis (Fin.castAdd 19 i) := by
  funext x
  unfold fourCellOddP51RetainedProfile fourCellOddFiniteRetainedProfile
    fourCellOddP51PadP13Coefficients fourCellOddP13CoordinateUnit
  change (∑ j : Fin (6 + 19),
      Fin.addCases (fun k : Fin 6 ↦ if k = i then 1 else 0)
          (fun _ : Fin 19 ↦ 0) j *
        fourCellOddFiniteRetainedBasis j x) = _
  rw [Fin.sum_univ_add]
  simp

/-- The exact retained solve kills all first six `P51` normal rows at once. -/
theorem fourCellOddP51SparseP13Anchor_low_normal_row_eq_zero (i : Fin 6) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP51ApproximateResidual
          fourCellOddP51SparseP13AnchorCoefficients)
        (fourCellOddFiniteRetainedBasis (Fin.castAdd 19 i)) = 0 := by
  rw [fourCellOddP51SparseP13ApproximateResidual_eq,
    ← paddedP13CoordinateUnit_profile_eq_basis,
    fourCellOddP51PadP13Coefficients_profile_eq]
  unfold fourCellOddP13RetainedSolvedResidual
  exact fourCellOddP13RetainedSolution_orthogonal
    (fourCellOddP13CoordinateUnit i)

/-- The complete normal defect is the single unenumerated block
`P15/P17/.../P51`. -/
def fourCellOddP51SparseP13HighNormalResidualEnergy : ℝ :=
  ∑ i : Fin 19,
    (2 * (@fourCellOddFiniteRetainedDegree 24
        (Fin.natAdd 6 i : Fin 25) : ℝ) + 1) *
      fourCellOddCoreLocalBilinear
        fourCellOddP13RetainedSolvedResidual
        (fourCellOddFiniteRetainedBasis
          (Fin.natAdd 6 i : Fin 25)) ^ 2

theorem fourCellOddP51SparseP13NormalResidualEnergy_eq_high :
    fourCellOddP51NormalResidualEnergy
        fourCellOddP51SparseP13AnchorCoefficients =
      fourCellOddP51SparseP13HighNormalResidualEnergy := by
  unfold fourCellOddP51SparseP13HighNormalResidualEnergy
  unfold fourCellOddP51NormalResidualEnergy
  rw [fourCellOddP51SparseP13ApproximateResidual_eq]
  change (∑ i : Fin (6 + 19),
      (2 * (@fourCellOddFiniteRetainedDegree 24 i : ℝ) + 1) *
        fourCellOddCoreLocalBilinear
          fourCellOddP13RetainedSolvedResidual
          (fourCellOddFiniteRetainedBasis i) ^ 2) = _
  rw [Fin.sum_univ_add]
  have hlow (i : Fin 6) :
      fourCellOddCoreLocalBilinear
          fourCellOddP13RetainedSolvedResidual
          (fourCellOddFiniteRetainedBasis (Fin.castAdd 19 i)) = 0 := by
    simpa only [fourCellOddP51SparseP13ApproximateResidual_eq] using
      fourCellOddP51SparseP13Anchor_low_normal_row_eq_zero i
  simp_rw [hlow]
  simp

private theorem q51_orthogonal_sparseP13Correction :
    fourCellOddCoreLocalBilinear fourCellOddQ51
      fourCellOddP51SparseP13Correction = 0 := by
  exact fourCellOddQ51_finiteOrthogonal
    fourCellOddP51SparseP13CorrectionCoefficients

/-- Core Pythagoras for the exact retained-`P13` anchor. -/
theorem fourCellOddP13RetainedSolvedResidual_quadratic_eq_q51_add_correction :
    fourCellOddCoreLocalQuadratic fourCellOddP13RetainedSolvedResidual =
      fourCellOddP51GalerkinPivot +
        fourCellOddCoreLocalQuadratic
          fourCellOddP51SparseP13Correction := by
  rw [fourCellOddP13RetainedSolvedResidual_eq_q51_add_sparseCorrection,
    fourCellOddCoreLocalQuadratic_add fourCellOddQ51
      fourCellOddP51SparseP13Correction
      contDiff_fourCellOddQ51.continuous
      contDiff_fourCellOddP51SparseP13Correction.continuous,
    q51_orthogonal_sparseP13Correction]
  unfold fourCellOddP51GalerkinPivot
  ring

/-- A single nineteen-row scalar certificate implies the desired
`7/10000` `P51` pivot floor. -/
theorem seven_div_ten_thousand_le_fourCellOddP51GalerkinPivot_of_sparseP13
    (hcertificate :
      fourCellOddP51NormalResidualEnergy
          fourCellOddP51SparseP13AnchorCoefficients ≤
        fourCellOddNineteenTwentiethsCoercivityConstant *
          (fourCellOddCoreLocalQuadratic
              fourCellOddP13RetainedSolvedResidual -
            (7 / 10000 : ℝ))) :
    (7 / 10000 : ℝ) ≤ fourCellOddP51GalerkinPivot := by
  have hcorrection :=
    fourCellOddP51_correction_energy_le_normalResidualEnergy_div_exact
      fourCellOddP51SparseP13AnchorCoefficients
  change fourCellOddCoreLocalQuadratic
      fourCellOddP51SparseP13Correction ≤
    fourCellOddP51NormalResidualEnergy
        fourCellOddP51SparseP13AnchorCoefficients /
      fourCellOddNineteenTwentiethsCoercivityConstant at hcorrection
  have hkappa := fourCellOddNineteenTwentiethsCoercivityConstant_pos
  have hbudget :
      fourCellOddP51NormalResidualEnergy
          fourCellOddP51SparseP13AnchorCoefficients /
          fourCellOddNineteenTwentiethsCoercivityConstant ≤
        fourCellOddCoreLocalQuadratic
            fourCellOddP13RetainedSolvedResidual -
          (7 / 10000 : ℝ) := by
    apply (div_le_iff₀ hkappa).2
    simpa [mul_comm] using hcertificate
  have hsplit :=
    fourCellOddP13RetainedSolvedResidual_quadratic_eq_q51_add_correction
  linarith

/-- High-mode-only form of the retained-`P13` certificate. -/
theorem seven_div_ten_thousand_le_fourCellOddP51GalerkinPivot_of_sparseP13High
    (hcertificate :
      fourCellOddP51SparseP13HighNormalResidualEnergy ≤
        fourCellOddNineteenTwentiethsCoercivityConstant *
          (fourCellOddCoreLocalQuadratic
              fourCellOddP13RetainedSolvedResidual -
            (7 / 10000 : ℝ))) :
    (7 / 10000 : ℝ) ≤ fourCellOddP51GalerkinPivot := by
  apply
    seven_div_ten_thousand_le_fourCellOddP51GalerkinPivot_of_sparseP13
  rwa [fourCellOddP51SparseP13NormalResidualEnergy_eq_high]

/-- The same defect viewed on the pre-existing `P11+` Bessel block.  Its
first two rows (`P11,P13`) are zero; the other nineteen are precisely the
high energy above. -/
def fourCellOddP51SparseP13P11PlusNormalResidualEnergy : ℝ :=
  ∑ i : Fin 21,
    (2 * (@fourCellOddFiniteRetainedDegree 24
        (Fin.natAdd 4 i : Fin 25) : ℝ) + 1) *
      fourCellOddCoreLocalBilinear
        fourCellOddP13RetainedSolvedResidual
        (fourCellOddFiniteRetainedBasis
          (Fin.natAdd 4 i : Fin 25)) ^ 2

private theorem p11Plus_first_two_row_eq_zero (i : Fin 2) :
    fourCellOddCoreLocalBilinear
        fourCellOddP13RetainedSolvedResidual
        (fourCellOddFiniteRetainedBasis
          (Fin.natAdd 4 (Fin.castAdd 19 i) : Fin 25)) = 0 := by
  let j : Fin 6 := Fin.natAdd 4 i
  have hj :
      (Fin.natAdd 4 (Fin.castAdd 19 i) : Fin 25) =
        Fin.castAdd 19 j := by
    apply Fin.ext
    simp [j]
  rw [hj]
  simpa only [fourCellOddP51SparseP13ApproximateResidual_eq] using
    fourCellOddP51SparseP13Anchor_low_normal_row_eq_zero j

private theorem p11Plus_last_nineteen_index (i : Fin 19) :
    (Fin.natAdd 4 (Fin.natAdd 2 i) : Fin 25) =
      Fin.natAdd 6 i := by
  apply Fin.ext
  simp
  omega

/-- No row enumeration is hidden in the Bessel formulation: splitting the
`P11+` block once discards two exact zero rows and leaves `P15+`. -/
theorem fourCellOddP51SparseP13P11PlusNormalResidualEnergy_eq_high :
    fourCellOddP51SparseP13P11PlusNormalResidualEnergy =
      fourCellOddP51SparseP13HighNormalResidualEnergy := by
  unfold fourCellOddP51SparseP13P11PlusNormalResidualEnergy
    fourCellOddP51SparseP13HighNormalResidualEnergy
  change (∑ i : Fin (2 + 19),
      (2 * (@fourCellOddFiniteRetainedDegree 24
          (Fin.natAdd 4 i : Fin 25) : ℝ) + 1) *
        fourCellOddCoreLocalBilinear
          fourCellOddP13RetainedSolvedResidual
          (fourCellOddFiniteRetainedBasis
            (Fin.natAdd 4 i : Fin 25)) ^ 2) = _
  rw [Fin.sum_univ_add]
  simp_rw [p11Plus_first_two_row_eq_zero]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
    Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  rw [p11Plus_last_nineteen_index]

/-- One common `L²` representer controls all nineteen unsolved rows by a
single Bessel norm.  The two extra rows in the reusable `P11+` projection
are exact zeros, so there is no dimension loss. -/
theorem fourCellOddP51SparseP13HighNormalResidualEnergy_le_l2_of_representer
    (F : ℝ → ℝ)
    (hF : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hrow : ∀ i : Fin 21,
      fourCellOddCoreLocalBilinear
          fourCellOddP13RetainedSolvedResidual
          (fourCellOddFiniteRetainedBasis
            (Fin.natAdd 4 i : Fin 25)) =
        ∫ x : ℝ in 0..1,
          F x * fourCellOddFiniteRetainedBasis
            (Fin.natAdd 4 i : Fin 25) x) :
    fourCellOddP51SparseP13HighNormalResidualEnergy ≤
      ∫ x : ℝ in 0..1, F x ^ 2 := by
  rw [← fourCellOddP51SparseP13P11PlusNormalResidualEnergy_eq_high]
  unfold fourCellOddP51SparseP13P11PlusNormalResidualEnergy
  simp_rw [hrow]
  exact fourCellOddP51HighRowProjection_energy_le F hF

/-- The exact remaining analytic target can equivalently be discharged by
one common representer and one scalar norm bound. -/
theorem seven_div_ten_thousand_le_fourCellOddP51GalerkinPivot_of_sparseP13Representer
    (F : ℝ → ℝ)
    (hF : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hrow : ∀ i : Fin 21,
      fourCellOddCoreLocalBilinear
          fourCellOddP13RetainedSolvedResidual
          (fourCellOddFiniteRetainedBasis
            (Fin.natAdd 4 i : Fin 25)) =
        ∫ x : ℝ in 0..1,
          F x * fourCellOddFiniteRetainedBasis
            (Fin.natAdd 4 i : Fin 25) x)
    (hl2 : (∫ x : ℝ in 0..1, F x ^ 2) ≤
      fourCellOddNineteenTwentiethsCoercivityConstant *
        (fourCellOddCoreLocalQuadratic
            fourCellOddP13RetainedSolvedResidual -
          (7 / 10000 : ℝ))) :
    (7 / 10000 : ℝ) ≤ fourCellOddP51GalerkinPivot := by
  apply
    seven_div_ten_thousand_le_fourCellOddP51GalerkinPivot_of_sparseP13High
  exact (fourCellOddP51SparseP13HighNormalResidualEnergy_le_l2_of_representer
    F hF hrow).trans hl2

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP13AnchorStructural
