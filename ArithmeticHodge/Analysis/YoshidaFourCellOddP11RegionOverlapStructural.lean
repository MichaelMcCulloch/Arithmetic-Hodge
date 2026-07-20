import ArithmeticHodge.Analysis.YoshidaFourCellOddP11LowerMassRegionStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11RegionOverlapStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFourCellOddP11LowerMassRegionStructural
open YoshidaFourCellOddP11SchurResidualProfilesStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddP11UniversalCoreCauchyStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Exact gap between the two odd `P₁₁+` mass regions

The extension-row region and the Legendre-residual-mass region do not cover
the universal core pencil.  The pure finite `P₃` Schur residual lies strictly
outside both hypotheses.  This is a structural finite direction, not a
numerical tail search.
-/

private theorem fiveMode_P3_eq :
    fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0 = centeredP3 := by
  funext x
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp

private theorem finiteP3SchurResidual_apply (x : ℝ) :
    fourCellOddP11FiniteSchurResidualProfile 1 0 0 0 x =
      fourCellOddCoreLocalQuadratic centeredP1 * centeredP3 x -
        fourCellOddCoreLocalBilinear centeredP1 centeredP3 * centeredP1 x := by
  rw [fourCellOddP11FiniteSchurResidualProfile_apply, fiveMode_P3_eq]

/-- Exact lower-strip mass of the pure finite `P₃` Schur residual. -/
theorem integral_zero_three_fifths_finiteP3SchurResidual_sq :
    (∫ x : ℝ in 0..3 / 5,
        fourCellOddP11FiniteSchurResidualProfile 1 0 0 0 x ^ 2) =
      (1539 / 21875 : ℝ) *
          fourCellOddCoreLocalQuadratic centeredP1 ^ 2 +
        (432 / 3125 : ℝ) *
          fourCellOddCoreLocalQuadratic centeredP1 *
            fourCellOddCoreLocalBilinear centeredP1 centeredP3 +
        (9 / 125 : ℝ) *
          fourCellOddCoreLocalBilinear centeredP1 centeredP3 ^ 2 := by
  rw [show (fun x : ℝ ↦
      fourCellOddP11FiniteSchurResidualProfile 1 0 0 0 x ^ 2) =
      fun x ↦
        (fourCellOddCoreLocalQuadratic centeredP1 * centeredP3 x -
          fourCellOddCoreLocalBilinear centeredP1 centeredP3 *
            centeredP1 x) ^ 2 by
    funext x
    rw [finiteP3SchurResidual_apply]]
  unfold centeredP1 centeredP3
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 (3 / 5))
    (Continuous.intervalIntegrable (by fun_prop) 0 (3 / 5))]
  norm_num
  ring

/-- The pure finite `P₃` Schur residual strictly violates the sharp
extension-row lower-mass threshold.  The coefficient gap already visible in
the `P₁` square is
`9/125 - 12375/3288856 = 28052829/411107000`. -/
theorem finiteP3_extensionRowRegion_strictly_fails :
    (12375 / 3288856 : ℝ) *
        fourCellOddCoreLocalBilinear centeredP1 centeredP3 ^ 2 <
      ∫ x : ℝ in 0..3 / 5,
        fourCellOddP11FiniteSchurResidualProfile 1 0 0 0 x ^ 2 := by
  rw [integral_zero_three_fifths_finiteP3SchurResidual_sq,
    fourCellOddCoreLocalQuadratic_centeredP1_eq_perturbed11,
    fourCellOddCoreLocalBilinear_centeredP1_centeredP3_eq_perturbed13]
  rcases fourCellOddOneThreeFivePerturbed_entry_bounds with
    ⟨hAlo, _hAhi, hBlo, _hBhi, _hDlo, _hDhi,
      _hElo, _hEhi, _hFlo, _hFhi, _hGlo, _hGhi⟩
  have hA0 : 0 < fourCellOddOneThreeFivePerturbed11 := by linarith
  have hB0 : 0 < fourCellOddOneThreeFivePerturbed13 := by linarith
  have hAB : 0 < fourCellOddOneThreeFivePerturbed11 *
      fourCellOddOneThreeFivePerturbed13 := mul_pos hA0 hB0
  nlinarith [sq_nonneg fourCellOddOneThreeFivePerturbed11,
    sq_nonneg fourCellOddOneThreeFivePerturbed13]

/-- A genuine universal-pencil direction outside the union of the two
compiled sufficient regions.  The first strict inequality is the negation of
the extension-row hypothesis; the second is the strict reverse of the
Legendre-residual-mass hypothesis. -/
theorem pureP3_universalCorePencil_outside_both_mass_regions :
    let r : ℝ → ℝ := fun _ ↦ 0
    let row :=
      (1 : ℝ) * fourCellOddCoreLocalBilinear centeredP1
          (fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0) +
        (0 : ℝ) * fourCellOddCoreLocalBilinear centeredP1 r
    let w := fourCellOddP11UniversalCorePencilProfile 1 0 0 0 1 0 r
    let u := fourCellOddP11UniversalLegendreResidualBaseProfile
      1 0 0 0 1 0 r
    (12375 / 3288856 : ℝ) * row ^ 2 <
        (∫ x : ℝ in 0..3 / 5, w x ^ 2) ∧
      fourCellOddCoreLocalQuadratic centeredP1 ^ 2 *
          ((27 / 250 : ℝ) * (∫ x : ℝ in 0..3 / 5, u x ^ 2) +
            (13 / 20000 : ℝ) * (∫ x : ℝ in 0..1, u x ^ 2)) <
        fourCellOddCoreLocalQuadratic centeredP1 * row ^ 2 := by
  dsimp only
  rw [fiveMode_P3_eq]
  constructor
  · simpa [fourCellOddP11UniversalCorePencilProfile] using
      finiteP3_extensionRowRegion_strictly_fails
  · simpa [fourCellOddP11UniversalLegendreResidualBaseProfile,
      fiveMode_P3_eq] using
      centeredP3_residualMassRegion_strictly_fails

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11RegionOverlapStructural
