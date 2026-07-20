import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualLowerBoundStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedRankOneSchurStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedFiniteCertificateAssemblyStructural

noncomputable section

open YoshidaFourCellOddP11GalerkinResidualLowerBoundStructural
open YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
open YoshidaFourCellOddP13AugmentedRankOneSchurStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Assembly of the augmented finite Galerkin certificate

The old residual floor and the exact rank-one identity reduce positivity of
the augmented residual to three scalar inequalities.  This module keeps the
two new analytic estimates as hypotheses:

* `3 / 20 < D` for the orthogonalized `P₁₁` diagonal;
* `|b| < 1 / 250` for its row against the old residual.

The already certified structural floor `1 / 4000 < Q₀` then has more than
enough room for the rank-one Schur cost.  The same hypotheses make `D`
nonzero, so the exact reconstructed coefficients also satisfy all five
finite normal equations.
-/

/-- Transport the structural old-residual floor to the scalar name used by
the rank-one Schur module. -/
theorem one_div_four_thousand_lt_fourCellOddP11OldGalerkinResidualPivot :
    (1 / 4000 : ℝ) < fourCellOddP11OldGalerkinResidualPivot := by
  simpa only [fourCellOddP11OldGalerkinResidualPivot,
    fourCellOddP11OldGalerkinResidual] using
      one_div_four_thousand_lt_fourCellOddCoreLocalQuadratic_exactGalerkinResidual

/-- The requested rational rank-one assembly.  No estimate of `D` or `b` is
hidden here: they remain precisely the two displayed hypotheses. -/
theorem fourCellOddP13RankOneAugmentedResidual_core_pos_of_D_and_cross_bounds
    (hD : (3 / 20 : ℝ) < fourCellOddP11OldBlockSchurPivot)
    (hb : |fourCellOddP11ExactResidualTailCross| < (1 / 250 : ℝ)) :
    0 < fourCellOddCoreLocalQuadratic
      fourCellOddP13RankOneAugmentedResidual := by
  have hQ0 :=
    one_div_four_thousand_lt_fourCellOddP11OldGalerkinResidualPivot
  have hQ0pos : 0 < fourCellOddP11OldGalerkinResidualPivot := by
    linarith
  have hDpos : 0 < fourCellOddP11OldBlockSchurPivot := by
    linarith
  rcases abs_lt.mp hb with ⟨hbneg, hbpos⟩
  have hbsq : fourCellOddP11ExactResidualTailCross ^ 2 <
      (1 / 250 : ℝ) ^ 2 := by
    nlinarith
  have hrational : (1 / 250 : ℝ) ^ 2 <
      (1 / 4000 : ℝ) * (3 / 20 : ℝ) := by
    norm_num
  have hQ0floor :
      (1 / 4000 : ℝ) * (3 / 20 : ℝ) <
        fourCellOddP11OldGalerkinResidualPivot * (3 / 20 : ℝ) :=
    mul_lt_mul_of_pos_right hQ0 (by norm_num)
  have hDscale :
      fourCellOddP11OldGalerkinResidualPivot * (3 / 20 : ℝ) <
        fourCellOddP11OldGalerkinResidualPivot *
          fourCellOddP11OldBlockSchurPivot :=
    mul_lt_mul_of_pos_left hD hQ0pos
  apply fourCellOddP13RankOneAugmentedResidual_core_pos_of_schur hDpos
  exact hbsq.trans (hrational.trans (hQ0floor.trans hDscale))

/-- The lower bound on `D` also discharges the nonzero premise in the exact
finite-normal-equation theorem. -/
theorem fourCellOddP13RankOneAugmentedCoefficients_orthogonal_of_D_bound
    (hD : (3 / 20 : ℝ) < fourCellOddP11OldBlockSchurPivot) :
    FourCellOddP13AugmentedGalerkinFiniteOrthogonal
      (fourCellOddP13RankOneAugmentedCoefficients 0)
      (fourCellOddP13RankOneAugmentedCoefficients 1)
      (fourCellOddP13RankOneAugmentedCoefficients 2)
      (fourCellOddP13RankOneAugmentedCoefficients 3)
      (fourCellOddP13RankOneAugmentedCoefficients 4) := by
  apply fourCellOddP13RankOneAugmentedCoefficients_orthogonal
  exact ne_of_gt ((by norm_num : (0 : ℝ) < 3 / 20).trans hD)

/-- The exact reconstructed coefficients package finite orthogonality and
the nonnegative residual diagonal required by the augmented Riesz
certificate. -/
theorem fourCellOddP13RankOneAugmentedCoefficients_finite_certificate
    (hD : (3 / 20 : ℝ) < fourCellOddP11OldBlockSchurPivot)
    (hb : |fourCellOddP11ExactResidualTailCross| < (1 / 250 : ℝ)) :
    FourCellOddP13AugmentedGalerkinFiniteOrthogonal
        (fourCellOddP13RankOneAugmentedCoefficients 0)
        (fourCellOddP13RankOneAugmentedCoefficients 1)
        (fourCellOddP13RankOneAugmentedCoefficients 2)
        (fourCellOddP13RankOneAugmentedCoefficients 3)
        (fourCellOddP13RankOneAugmentedCoefficients 4) ∧
      0 ≤ fourCellOddCoreLocalQuadratic
        (fourCellOddP13AugmentedGalerkinResidualProfile
          (fourCellOddP13RankOneAugmentedCoefficients 0)
          (fourCellOddP13RankOneAugmentedCoefficients 1)
          (fourCellOddP13RankOneAugmentedCoefficients 2)
          (fourCellOddP13RankOneAugmentedCoefficients 3)
          (fourCellOddP13RankOneAugmentedCoefficients 4)) := by
  constructor
  · exact fourCellOddP13RankOneAugmentedCoefficients_orthogonal_of_D_bound hD
  · have hpos :=
      fourCellOddP13RankOneAugmentedResidual_core_pos_of_D_and_cross_bounds
        hD hb
    rw [fourCellOddP13RankOneAugmentedResidual_eq_GalerkinResidual] at hpos
    exact hpos.le

/-- Existential form of the completed finite half of the augmented
certificate. -/
theorem exists_fourCellOddP13AugmentedFiniteOrthogonal_and_core_nonneg
    (hD : (3 / 20 : ℝ) < fourCellOddP11OldBlockSchurPivot)
    (hb : |fourCellOddP11ExactResidualTailCross| < (1 / 250 : ℝ)) :
    ∃ a3 a5 a7 a9 a11 : ℝ,
      FourCellOddP13AugmentedGalerkinFiniteOrthogonal a3 a5 a7 a9 a11 ∧
        0 ≤ fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            a3 a5 a7 a9 a11) := by
  rcases fourCellOddP13RankOneAugmentedCoefficients_finite_certificate hD hb with
    ⟨horth, hnonneg⟩
  exact ⟨fourCellOddP13RankOneAugmentedCoefficients 0,
    fourCellOddP13RankOneAugmentedCoefficients 1,
    fourCellOddP13RankOneAugmentedCoefficients 2,
    fourCellOddP13RankOneAugmentedCoefficients 3,
    fourCellOddP13RankOneAugmentedCoefficients 4, horth, hnonneg⟩

/-- Once the remaining `P₁₃+` residual dual is supplied for the same
exact coefficients, the preceding finite assembly closes the full augmented
Galerkin/Riesz certificate proposition. -/
theorem fourCellOddP13AugmentedGalerkinRieszCertificate_of_rankOne_bounds
    (kappa : ℝ)
    (hD : (3 / 20 : ℝ) < fourCellOddP11OldBlockSchurPivot)
    (hb : |fourCellOddP11ExactResidualTailCross| < (1 / 250 : ℝ))
    (hdual : FourCellOddP13AugmentedGalerkinResidualL2Dual kappa
      (fourCellOddP13RankOneAugmentedCoefficients 0)
      (fourCellOddP13RankOneAugmentedCoefficients 1)
      (fourCellOddP13RankOneAugmentedCoefficients 2)
      (fourCellOddP13RankOneAugmentedCoefficients 3)
      (fourCellOddP13RankOneAugmentedCoefficients 4)) :
    FourCellOddP13AugmentedGalerkinRieszCertificate kappa := by
  rcases fourCellOddP13RankOneAugmentedCoefficients_finite_certificate hD hb with
    ⟨horth, hnonneg⟩
  exact ⟨fourCellOddP13RankOneAugmentedCoefficients 0,
    fourCellOddP13RankOneAugmentedCoefficients 1,
    fourCellOddP13RankOneAugmentedCoefficients 2,
    fourCellOddP13RankOneAugmentedCoefficients 3,
    fourCellOddP13RankOneAugmentedCoefficients 4,
    horth, hnonneg, hdual⟩

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedFiniteCertificateAssemblyStructural
