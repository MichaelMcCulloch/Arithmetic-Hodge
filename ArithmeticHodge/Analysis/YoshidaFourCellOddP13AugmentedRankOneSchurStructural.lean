import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinSolutionBoxStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

open MeasureTheory Real Set Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedRankOneSchurStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11GalerkinFiniteSolveStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP11GalerkinRieszStructural
open YoshidaFourCellOddP11GalerkinSolutionBoxStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddP13AugmentedDecompositionStructural
open YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Rank-one Schur update after retaining `P11`

This module expresses the enlarged `P3/P5/P7/P9/P11` Galerkin residual as
one exact rank-one update of the old `P3/P5/P7/P9` residual.  All analytic
estimates are left as scalar hypotheses.  The conclusion is the exact Schur
identity

`D * Q(qAug) = Q(q0) * D - b^2`.
-/

private def oldBasisThree : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0

private def oldBasisFive : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0

private def oldBasisSeven : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0

private def oldBasisNine : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1

private theorem contDiff_oldBasisThree : ContDiff ℝ 1 oldBasisThree :=
  contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0

private theorem contDiff_oldBasisFive : ContDiff ℝ 1 oldBasisFive :=
  contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0

private theorem contDiff_oldBasisSeven : ContDiff ℝ 1 oldBasisSeven :=
  contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0

private theorem contDiff_oldBasisNine : ContDiff ℝ 1 oldBasisNine :=
  contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1

private theorem odd_oldBasisThree : Function.Odd oldBasisThree :=
  odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0

private theorem odd_oldBasisFive : Function.Odd oldBasisFive :=
  odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0

private theorem odd_oldBasisSeven : Function.Odd oldBasisSeven :=
  odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0

private theorem odd_oldBasisNine : Function.Odd oldBasisNine :=
  odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1

private theorem contDiff_retainedProfile (x : Fin 4 → ℝ) :
    ContDiff ℝ 1 (fourCellOddP11GalerkinRetainedProfile x) :=
  contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
    0 (x 0) (x 1) (x 2) (x 3)

private theorem odd_retainedProfile (x : Fin 4 → ℝ) :
    Function.Odd (fourCellOddP11GalerkinRetainedProfile x) :=
  odd_fourCellOddOneThreeFiveSevenNineLowProfile
    0 (x 0) (x 1) (x 2) (x 3)

private theorem odd_const_mul
    {v : ℝ → ℝ} (hv : Function.Odd v) (a : ℝ) :
    Function.Odd (fun x ↦ a * v x) := by
  intro x
  change a * v (-x) = -(a * v x)
  rw [hv]
  ring

private theorem bilinear_add_right
    (u v w : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w)
    (huodd : Function.Odd u) (hvodd : Function.Odd v)
    (hwodd : Function.Odd w) :
    fourCellOddCoreLocalBilinear u (v + w) =
      fourCellOddCoreLocalBilinear u v +
        fourCellOddCoreLocalBilinear u w := by
  calc
    fourCellOddCoreLocalBilinear u (v + w) =
        fourCellOddCoreLocalBilinear (v + w) u :=
      fourCellOddCoreLocalBilinear_comm u (v + w)
        hu.continuous (hv.add hw).continuous
    _ = fourCellOddCoreLocalBilinear v u +
          fourCellOddCoreLocalBilinear w u :=
      fourCellOddCoreLocalBilinear_add_left
        v w u hv hw hu hvodd hwodd huodd
    _ = fourCellOddCoreLocalBilinear u v +
          fourCellOddCoreLocalBilinear u w := by
      rw [fourCellOddCoreLocalBilinear_comm v u
          hv.continuous hu.continuous,
        fourCellOddCoreLocalBilinear_comm w u
          hw.continuous hu.continuous]

private theorem retainedProfile_decompose (x : Fin 4 → ℝ) :
    fourCellOddP11GalerkinRetainedProfile x =
      ((fun z ↦ x 0 * oldBasisThree z) +
        (fun z ↦ x 1 * oldBasisFive z)) +
      (fun z ↦ x 2 * oldBasisSeven z) +
      (fun z ↦ x 3 * oldBasisNine z) := by
  funext z
  unfold fourCellOddP11GalerkinRetainedProfile
    oldBasisThree oldBasisFive oldBasisSeven oldBasisNine
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp only [Pi.add_apply]
  ring

private theorem bilinear_retainedProfile_right
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (huodd : Function.Odd u)
    (x : Fin 4 → ℝ) :
    fourCellOddCoreLocalBilinear u
        (fourCellOddP11GalerkinRetainedProfile x) =
      x 0 * fourCellOddCoreLocalBilinear u oldBasisThree +
      x 1 * fourCellOddCoreLocalBilinear u oldBasisFive +
      x 2 * fourCellOddCoreLocalBilinear u oldBasisSeven +
      x 3 * fourCellOddCoreLocalBilinear u oldBasisNine := by
  let v3 : ℝ → ℝ := fun z ↦ x 0 * oldBasisThree z
  let v5 : ℝ → ℝ := fun z ↦ x 1 * oldBasisFive z
  let v7 : ℝ → ℝ := fun z ↦ x 2 * oldBasisSeven z
  let v9 : ℝ → ℝ := fun z ↦ x 3 * oldBasisNine z
  have hv3 : ContDiff ℝ 1 v3 := contDiff_const.mul contDiff_oldBasisThree
  have hv5 : ContDiff ℝ 1 v5 := contDiff_const.mul contDiff_oldBasisFive
  have hv7 : ContDiff ℝ 1 v7 := contDiff_const.mul contDiff_oldBasisSeven
  have hv9 : ContDiff ℝ 1 v9 := contDiff_const.mul contDiff_oldBasisNine
  have hv3odd : Function.Odd v3 := odd_const_mul odd_oldBasisThree (x 0)
  have hv5odd : Function.Odd v5 := odd_const_mul odd_oldBasisFive (x 1)
  have hv7odd : Function.Odd v7 := odd_const_mul odd_oldBasisSeven (x 2)
  have hv9odd : Function.Odd v9 := odd_const_mul odd_oldBasisNine (x 3)
  rw [retainedProfile_decompose]
  change fourCellOddCoreLocalBilinear u (((v3 + v5) + v7) + v9) = _
  rw [bilinear_add_right u ((v3 + v5) + v7) v9
      hu ((hv3.add hv5).add hv7) hv9 huodd
      ((hv3odd.add hv5odd).add hv7odd) hv9odd,
    bilinear_add_right u (v3 + v5) v7 hu (hv3.add hv5) hv7 huodd
      (hv3odd.add hv5odd) hv7odd,
    bilinear_add_right u v3 v5 hu hv3 hv5 huodd hv3odd hv5odd]
  dsimp only [v3, v5, v7, v9]
  rw [fourCellOddCoreLocalBilinear_const_mul_right
      u oldBasisThree hu contDiff_oldBasisThree huodd odd_oldBasisThree (x 0),
    fourCellOddCoreLocalBilinear_const_mul_right
      u oldBasisFive hu contDiff_oldBasisFive huodd odd_oldBasisFive (x 1),
    fourCellOddCoreLocalBilinear_const_mul_right
      u oldBasisSeven hu contDiff_oldBasisSeven huodd odd_oldBasisSeven (x 2),
    fourCellOddCoreLocalBilinear_const_mul_right
      u oldBasisNine hu contDiff_oldBasisNine huodd odd_oldBasisNine (x 3)]

private theorem retainedGram_eq_localBasis :
    fourCellOddP11GalerkinRetainedGram =
      !![fourCellOddCoreLocalBilinear oldBasisThree oldBasisThree,
          fourCellOddCoreLocalBilinear oldBasisThree oldBasisFive,
          fourCellOddCoreLocalBilinear oldBasisThree oldBasisSeven,
          fourCellOddCoreLocalBilinear oldBasisThree oldBasisNine;
        fourCellOddCoreLocalBilinear oldBasisFive oldBasisThree,
          fourCellOddCoreLocalBilinear oldBasisFive oldBasisFive,
          fourCellOddCoreLocalBilinear oldBasisFive oldBasisSeven,
          fourCellOddCoreLocalBilinear oldBasisFive oldBasisNine;
        fourCellOddCoreLocalBilinear oldBasisSeven oldBasisThree,
          fourCellOddCoreLocalBilinear oldBasisSeven oldBasisFive,
          fourCellOddCoreLocalBilinear oldBasisSeven oldBasisSeven,
          fourCellOddCoreLocalBilinear oldBasisSeven oldBasisNine;
        fourCellOddCoreLocalBilinear oldBasisNine oldBasisThree,
          fourCellOddCoreLocalBilinear oldBasisNine oldBasisFive,
          fourCellOddCoreLocalBilinear oldBasisNine oldBasisSeven,
          fourCellOddCoreLocalBilinear oldBasisNine oldBasisNine] := by
  rfl

private theorem retainedGram_mulVec (x : Fin 4 → ℝ) :
    fourCellOddP11GalerkinRetainedGram *ᵥ x =
      ![fourCellOddCoreLocalBilinear oldBasisThree
          (fourCellOddP11GalerkinRetainedProfile x),
        fourCellOddCoreLocalBilinear oldBasisFive
          (fourCellOddP11GalerkinRetainedProfile x),
        fourCellOddCoreLocalBilinear oldBasisSeven
          (fourCellOddP11GalerkinRetainedProfile x),
        fourCellOddCoreLocalBilinear oldBasisNine
          (fourCellOddP11GalerkinRetainedProfile x)] := by
  funext i
  fin_cases i
  · rw [bilinear_retainedProfile_right oldBasisThree contDiff_oldBasisThree
      odd_oldBasisThree x]
    rw [retainedGram_eq_localBasis]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · rw [bilinear_retainedProfile_right oldBasisFive contDiff_oldBasisFive
      odd_oldBasisFive x]
    rw [retainedGram_eq_localBasis]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · rw [bilinear_retainedProfile_right oldBasisSeven contDiff_oldBasisSeven
      odd_oldBasisSeven x]
    rw [retainedGram_eq_localBasis]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · rw [bilinear_retainedProfile_right oldBasisNine contDiff_oldBasisNine
      odd_oldBasisNine x]
    rw [retainedGram_eq_localBasis]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

/-- The exact mixed row between the old retained block and `P11`. -/
def fourCellOddP11OldBlockTailRow : Fin 4 → ℝ :=
  ![fourCellOddCoreLocalBilinear oldBasisThree fourCellOddP11DirectTail,
    fourCellOddCoreLocalBilinear oldBasisFive fourCellOddP11DirectTail,
    fourCellOddCoreLocalBilinear oldBasisSeven fourCellOddP11DirectTail,
    fourCellOddCoreLocalBilinear oldBasisNine fourCellOddP11DirectTail]

/-- Coefficients of the exact old-block projection of `P11`. -/
def fourCellOddP11OldBlockProjectionCoefficients : Fin 4 → ℝ :=
  fourCellOddP11GalerkinRetainedGram⁻¹ *ᵥ fourCellOddP11OldBlockTailRow

/-- The exact projection of `P11` into `span(P3,P5,P7,P9)`. -/
def fourCellOddP11OldBlockProjection : ℝ → ℝ :=
  fourCellOddP11GalerkinRetainedProfile
    fourCellOddP11OldBlockProjectionCoefficients

theorem fourCellOddP11OldBlockProjectionCoefficients_normalEquation :
    fourCellOddP11GalerkinRetainedGram *ᵥ
        fourCellOddP11OldBlockProjectionCoefficients =
      fourCellOddP11OldBlockTailRow := by
  have hdet : IsUnit fourCellOddP11GalerkinRetainedGram.det :=
    fourCellOddP11GalerkinRetainedGram.isUnit_iff_isUnit_det.mp
      fourCellOddP11GalerkinRetainedGram_isUnit
  unfold fourCellOddP11OldBlockProjectionCoefficients
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv fourCellOddP11GalerkinRetainedGram hdet,
    Matrix.one_mulVec]

theorem contDiff_fourCellOddP11OldBlockProjection :
    ContDiff ℝ 1 fourCellOddP11OldBlockProjection :=
  contDiff_retainedProfile _

theorem odd_fourCellOddP11OldBlockProjection :
    Function.Odd fourCellOddP11OldBlockProjection :=
  odd_retainedProfile _

/-- The old-block projection has the same core row as `P11` against every
old retained vector. -/
theorem fourCellOddP11OldBlockProjection_normal (y : Fin 4 → ℝ) :
    fourCellOddCoreLocalBilinear fourCellOddP11OldBlockProjection
        (fourCellOddP11GalerkinRetainedProfile y) =
      fourCellOddCoreLocalBilinear fourCellOddP11DirectTail
        (fourCellOddP11GalerkinRetainedProfile y) := by
  have hrows :=
    (retainedGram_mulVec fourCellOddP11OldBlockProjectionCoefficients).symm.trans
      fourCellOddP11OldBlockProjectionCoefficients_normalEquation
  have h3 : fourCellOddCoreLocalBilinear oldBasisThree
      fourCellOddP11OldBlockProjection =
        fourCellOddCoreLocalBilinear oldBasisThree fourCellOddP11DirectTail := by
    have hi := congrFun hrows 0
    simpa only [fourCellOddP11OldBlockProjection,
      fourCellOddP11OldBlockTailRow] using hi
  have h5 : fourCellOddCoreLocalBilinear oldBasisFive
      fourCellOddP11OldBlockProjection =
        fourCellOddCoreLocalBilinear oldBasisFive fourCellOddP11DirectTail := by
    have hi := congrFun hrows 1
    simpa only [fourCellOddP11OldBlockProjection,
      fourCellOddP11OldBlockTailRow] using hi
  have h7 : fourCellOddCoreLocalBilinear oldBasisSeven
      fourCellOddP11OldBlockProjection =
        fourCellOddCoreLocalBilinear oldBasisSeven fourCellOddP11DirectTail := by
    have hi := congrFun hrows 2
    simpa only [fourCellOddP11OldBlockProjection,
      fourCellOddP11OldBlockTailRow] using hi
  have h9 : fourCellOddCoreLocalBilinear oldBasisNine
      fourCellOddP11OldBlockProjection =
        fourCellOddCoreLocalBilinear oldBasisNine fourCellOddP11DirectTail := by
    have hi := congrFun hrows 3
    simpa only [fourCellOddP11OldBlockProjection,
      fourCellOddP11OldBlockTailRow] using hi
  rw [bilinear_retainedProfile_right fourCellOddP11OldBlockProjection
      contDiff_fourCellOddP11OldBlockProjection
      odd_fourCellOddP11OldBlockProjection y,
    bilinear_retainedProfile_right fourCellOddP11DirectTail
      contDiff_fourCellOddP11DirectTail odd_fourCellOddP11DirectTail y]
  rw [fourCellOddCoreLocalBilinear_comm fourCellOddP11OldBlockProjection
      oldBasisThree contDiff_fourCellOddP11OldBlockProjection.continuous
      contDiff_oldBasisThree.continuous,
    fourCellOddCoreLocalBilinear_comm fourCellOddP11OldBlockProjection
      oldBasisFive contDiff_fourCellOddP11OldBlockProjection.continuous
      contDiff_oldBasisFive.continuous,
    fourCellOddCoreLocalBilinear_comm fourCellOddP11OldBlockProjection
      oldBasisSeven contDiff_fourCellOddP11OldBlockProjection.continuous
      contDiff_oldBasisSeven.continuous,
    fourCellOddCoreLocalBilinear_comm fourCellOddP11OldBlockProjection
      oldBasisNine contDiff_fourCellOddP11OldBlockProjection.continuous
      contDiff_oldBasisNine.continuous,
    fourCellOddCoreLocalBilinear_comm fourCellOddP11DirectTail
      oldBasisThree contDiff_fourCellOddP11DirectTail.continuous
      contDiff_oldBasisThree.continuous,
    fourCellOddCoreLocalBilinear_comm fourCellOddP11DirectTail
      oldBasisFive contDiff_fourCellOddP11DirectTail.continuous
      contDiff_oldBasisFive.continuous,
    fourCellOddCoreLocalBilinear_comm fourCellOddP11DirectTail
      oldBasisSeven contDiff_fourCellOddP11DirectTail.continuous
      contDiff_oldBasisSeven.continuous,
    fourCellOddCoreLocalBilinear_comm fourCellOddP11DirectTail
      oldBasisNine contDiff_fourCellOddP11DirectTail.continuous
      contDiff_oldBasisNine.continuous,
    h3, h5, h7, h9]

/-- The component of `P11` core-orthogonal to the old retained block. -/
def fourCellOddP11OldBlockResidual : ℝ → ℝ := fun x ↦
  fourCellOddP11DirectTail x - fourCellOddP11OldBlockProjection x

theorem contDiff_fourCellOddP11OldBlockResidual :
    ContDiff ℝ 1 fourCellOddP11OldBlockResidual := by
  unfold fourCellOddP11OldBlockResidual
  exact contDiff_fourCellOddP11DirectTail.sub
    contDiff_fourCellOddP11OldBlockProjection

theorem odd_fourCellOddP11OldBlockResidual :
    Function.Odd fourCellOddP11OldBlockResidual := by
  intro x
  unfold fourCellOddP11OldBlockResidual
  rw [odd_fourCellOddP11DirectTail, odd_fourCellOddP11OldBlockProjection]
  ring

theorem fourCellOddP11DirectTail_eq_oldBlockResidual_add_projection :
    fourCellOddP11DirectTail =
      fourCellOddP11OldBlockResidual + fourCellOddP11OldBlockProjection := by
  funext x
  unfold fourCellOddP11OldBlockResidual
  simp only [Pi.add_apply]
  ring

/-- Exact core orthogonality of the Schur direction to the old block. -/
theorem fourCellOddP11OldBlockResidual_orthogonal (y : Fin 4 → ℝ) :
    fourCellOddCoreLocalBilinear fourCellOddP11OldBlockResidual
        (fourCellOddP11GalerkinRetainedProfile y) = 0 := by
  have hnormal := fourCellOddP11OldBlockProjection_normal y
  let negProj : ℝ → ℝ := fun x ↦ (-1 : ℝ) *
    fourCellOddP11OldBlockProjection x
  have hneg : ContDiff ℝ 1 negProj :=
    contDiff_const.mul contDiff_fourCellOddP11OldBlockProjection
  have hnegodd : Function.Odd negProj :=
    odd_const_mul odd_fourCellOddP11OldBlockProjection (-1)
  have hresidual : fourCellOddP11OldBlockResidual =
      fourCellOddP11DirectTail + negProj := by
    funext x
    unfold fourCellOddP11OldBlockResidual
    dsimp only [negProj]
    simp only [Pi.add_apply]
    ring
  rw [hresidual,
    fourCellOddCoreLocalBilinear_add_left
      fourCellOddP11DirectTail negProj
      (fourCellOddP11GalerkinRetainedProfile y)
      contDiff_fourCellOddP11DirectTail hneg (contDiff_retainedProfile y)
      odd_fourCellOddP11DirectTail hnegodd (odd_retainedProfile y)]
  dsimp only [negProj]
  rw [fourCellOddCoreLocalBilinear_const_mul_left
    fourCellOddP11OldBlockProjection
    (fourCellOddP11GalerkinRetainedProfile y)
    contDiff_fourCellOddP11OldBlockProjection (contDiff_retainedProfile y)
    odd_fourCellOddP11OldBlockProjection (odd_retainedProfile y) (-1),
    hnormal]
  ring

/-- The old exact Galerkin residual, named as the first Schur pivot vector. -/
def fourCellOddP11OldGalerkinResidual : ℝ → ℝ :=
  fourCellOddP11GalerkinRetainedResidualProfile

theorem contDiff_fourCellOddP11OldGalerkinResidual :
    ContDiff ℝ 1 fourCellOddP11OldGalerkinResidual := by
  unfold fourCellOddP11OldGalerkinResidual
    fourCellOddP11GalerkinRetainedResidualProfile
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
  exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _

theorem odd_fourCellOddP11OldGalerkinResidual :
    Function.Odd fourCellOddP11OldGalerkinResidual := by
  unfold fourCellOddP11OldGalerkinResidual
    fourCellOddP11GalerkinRetainedResidualProfile
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
  exact odd_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _

theorem fourCellOddP11OldGalerkinResidual_orthogonal (y : Fin 4 → ℝ) :
    fourCellOddCoreLocalBilinear fourCellOddP11OldGalerkinResidual
        (fourCellOddP11GalerkinRetainedProfile y) = 0 := by
  exact fourCellOddP11GalerkinRetainedSolution_orthogonal
    (y 0) (y 1) (y 2) (y 3)

/-- The old residual quadratic `Q0`. -/
def fourCellOddP11OldGalerkinResidualPivot : ℝ :=
  fourCellOddCoreLocalQuadratic fourCellOddP11OldGalerkinResidual

/-- The new diagonal Schur pivot `D = Q(u)`. -/
def fourCellOddP11OldBlockSchurPivot : ℝ :=
  fourCellOddCoreLocalQuadratic fourCellOddP11OldBlockResidual

/-- The mixed Schur scalar `b = B(q0,P11)`. -/
def fourCellOddP11ExactResidualTailCross : ℝ :=
  fourCellOddCoreLocalBilinear
    fourCellOddP11OldGalerkinResidual fourCellOddP11DirectTail

/-- The Schur pivot is also the remaining `P11` row of its orthogonalized
direction. -/
theorem fourCellOddP11OldBlockSchurPivot_eq_residual_tail_row :
    fourCellOddP11OldBlockSchurPivot =
      fourCellOddCoreLocalBilinear
        fourCellOddP11OldBlockResidual fourCellOddP11DirectTail := by
  rw [fourCellOddP11DirectTail_eq_oldBlockResidual_add_projection,
    bilinear_add_right fourCellOddP11OldBlockResidual
      fourCellOddP11OldBlockResidual fourCellOddP11OldBlockProjection
      contDiff_fourCellOddP11OldBlockResidual
      contDiff_fourCellOddP11OldBlockResidual
      contDiff_fourCellOddP11OldBlockProjection
      odd_fourCellOddP11OldBlockResidual
      odd_fourCellOddP11OldBlockResidual
      odd_fourCellOddP11OldBlockProjection,
    fourCellOddCoreLocalBilinear_self_eq_quadratic
      fourCellOddP11OldBlockResidual
      contDiff_fourCellOddP11OldBlockResidual
      odd_fourCellOddP11OldBlockResidual]
  have horth := fourCellOddP11OldBlockResidual_orthogonal
    fourCellOddP11OldBlockProjectionCoefficients
  change fourCellOddCoreLocalBilinear fourCellOddP11OldBlockResidual
      fourCellOddP11OldBlockProjection = 0 at horth
  rw [horth]
  unfold fourCellOddP11OldBlockSchurPivot
  ring

/-- Coordinate-free Schur formula
`D = Q(P11) - B(projOld(P11),P11)`. -/
theorem fourCellOddP11OldBlockSchurPivot_eq_tail_diagonal_sub_projection_row :
    fourCellOddP11OldBlockSchurPivot =
      fourCellOddCoreLocalQuadratic fourCellOddP11DirectTail -
        fourCellOddCoreLocalBilinear
          fourCellOddP11OldBlockProjection fourCellOddP11DirectTail := by
  have horth := fourCellOddP11OldBlockResidual_orthogonal
    fourCellOddP11OldBlockProjectionCoefficients
  change fourCellOddCoreLocalBilinear fourCellOddP11OldBlockResidual
      fourCellOddP11OldBlockProjection = 0 at horth
  have hadd := fourCellOddCoreLocalQuadratic_add
    fourCellOddP11OldBlockResidual fourCellOddP11OldBlockProjection
    contDiff_fourCellOddP11OldBlockResidual.continuous
    contDiff_fourCellOddP11OldBlockProjection.continuous
  rw [← fourCellOddP11DirectTail_eq_oldBlockResidual_add_projection,
    horth] at hadd
  have hprojSelf := fourCellOddCoreLocalBilinear_self_eq_quadratic
    fourCellOddP11OldBlockProjection
    contDiff_fourCellOddP11OldBlockProjection
    odd_fourCellOddP11OldBlockProjection
  have hnormal := fourCellOddP11OldBlockProjection_normal
    fourCellOddP11OldBlockProjectionCoefficients
  change fourCellOddCoreLocalBilinear fourCellOddP11OldBlockProjection
      fourCellOddP11OldBlockProjection =
        fourCellOddCoreLocalBilinear fourCellOddP11DirectTail
          fourCellOddP11OldBlockProjection at hnormal
  rw [hprojSelf] at hnormal
  have hprojTail :
      fourCellOddCoreLocalBilinear
          fourCellOddP11OldBlockProjection fourCellOddP11DirectTail =
        fourCellOddCoreLocalQuadratic fourCellOddP11OldBlockProjection := by
    calc
      fourCellOddCoreLocalBilinear
          fourCellOddP11OldBlockProjection fourCellOddP11DirectTail =
          fourCellOddCoreLocalBilinear
            fourCellOddP11DirectTail fourCellOddP11OldBlockProjection :=
        fourCellOddCoreLocalBilinear_comm
          fourCellOddP11OldBlockProjection fourCellOddP11DirectTail
          contDiff_fourCellOddP11OldBlockProjection.continuous
          contDiff_fourCellOddP11DirectTail.continuous
      _ = fourCellOddCoreLocalQuadratic fourCellOddP11OldBlockProjection :=
        hnormal.symm
  unfold fourCellOddP11OldBlockSchurPivot
  linarith

/-- Since `q0` is old-block orthogonal, its row against the orthogonalized
`P11` direction is exactly `b`. -/
theorem fourCellOddP11OldGalerkinResidual_oldBlockResidual_cross :
    fourCellOddCoreLocalBilinear
        fourCellOddP11OldGalerkinResidual fourCellOddP11OldBlockResidual =
      fourCellOddP11ExactResidualTailCross := by
  let negProj : ℝ → ℝ := fun x ↦ (-1 : ℝ) *
    fourCellOddP11OldBlockProjection x
  have hneg : ContDiff ℝ 1 negProj :=
    contDiff_const.mul contDiff_fourCellOddP11OldBlockProjection
  have hnegodd : Function.Odd negProj :=
    odd_const_mul odd_fourCellOddP11OldBlockProjection (-1)
  have hresidual : fourCellOddP11OldBlockResidual =
      fourCellOddP11DirectTail + negProj := by
    funext x
    unfold fourCellOddP11OldBlockResidual
    dsimp only [negProj]
    simp only [Pi.add_apply]
    ring
  rw [hresidual,
    bilinear_add_right fourCellOddP11OldGalerkinResidual
      fourCellOddP11DirectTail negProj
      contDiff_fourCellOddP11OldGalerkinResidual
      contDiff_fourCellOddP11DirectTail hneg
      odd_fourCellOddP11OldGalerkinResidual
      odd_fourCellOddP11DirectTail hnegodd]
  dsimp only [negProj]
  rw [fourCellOddCoreLocalBilinear_const_mul_right
    fourCellOddP11OldGalerkinResidual fourCellOddP11OldBlockProjection
    contDiff_fourCellOddP11OldGalerkinResidual
    contDiff_fourCellOddP11OldBlockProjection
    odd_fourCellOddP11OldGalerkinResidual
    odd_fourCellOddP11OldBlockProjection (-1)]
  have horth := fourCellOddP11OldGalerkinResidual_orthogonal
    fourCellOddP11OldBlockProjectionCoefficients
  change fourCellOddCoreLocalBilinear fourCellOddP11OldGalerkinResidual
      fourCellOddP11OldBlockProjection = 0 at horth
  rw [horth]
  unfold fourCellOddP11ExactResidualTailCross
  ring

/-- The single coefficient of the rank-one update. -/
def fourCellOddP11AugmentedSchurLambda : ℝ :=
  fourCellOddP11ExactResidualTailCross / fourCellOddP11OldBlockSchurPivot

/-- Updated coefficients in the old four-dimensional block. -/
def fourCellOddP13RankOneUpdatedOldCoefficients : Fin 4 → ℝ := fun i ↦
  fourCellOddP11GalerkinRetainedSolution i -
    fourCellOddP11AugmentedSchurLambda *
      fourCellOddP11OldBlockProjectionCoefficients i

/-- The five reconstructed augmented coefficients
`(a - lambda z, lambda)`. -/
def fourCellOddP13RankOneAugmentedCoefficients : Fin 5 → ℝ :=
  ![fourCellOddP13RankOneUpdatedOldCoefficients 0,
    fourCellOddP13RankOneUpdatedOldCoefficients 1,
    fourCellOddP13RankOneUpdatedOldCoefficients 2,
    fourCellOddP13RankOneUpdatedOldCoefficients 3,
    fourCellOddP11AugmentedSchurLambda]

/-- The rank-one update `qAug = q0 - lambda*u`. -/
def fourCellOddP13RankOneAugmentedResidual : ℝ → ℝ := fun x ↦
  fourCellOddP11OldGalerkinResidual x -
    fourCellOddP11AugmentedSchurLambda * fourCellOddP11OldBlockResidual x

theorem contDiff_fourCellOddP13RankOneAugmentedResidual :
    ContDiff ℝ 1 fourCellOddP13RankOneAugmentedResidual := by
  unfold fourCellOddP13RankOneAugmentedResidual
  exact contDiff_fourCellOddP11OldGalerkinResidual.sub
    (contDiff_const.mul contDiff_fourCellOddP11OldBlockResidual)

theorem odd_fourCellOddP13RankOneAugmentedResidual :
    Function.Odd fourCellOddP13RankOneAugmentedResidual := by
  intro x
  unfold fourCellOddP13RankOneAugmentedResidual
  rw [odd_fourCellOddP11OldGalerkinResidual,
    odd_fourCellOddP11OldBlockResidual]
  ring

/-- Exact reconstruction of the rank-one update as an augmented Galerkin
residual with coefficients `(a - lambda z, lambda)`. -/
theorem fourCellOddP13RankOneAugmentedResidual_eq_GalerkinResidual :
    fourCellOddP13RankOneAugmentedResidual =
      fourCellOddP13AugmentedGalerkinResidualProfile
        (fourCellOddP13RankOneAugmentedCoefficients 0)
        (fourCellOddP13RankOneAugmentedCoefficients 1)
        (fourCellOddP13RankOneAugmentedCoefficients 2)
        (fourCellOddP13RankOneAugmentedCoefficients 3)
        (fourCellOddP13RankOneAugmentedCoefficients 4) := by
  funext x
  unfold fourCellOddP13RankOneAugmentedResidual
    fourCellOddP11OldGalerkinResidual
    fourCellOddP11GalerkinRetainedResidualProfile
    fourCellOddP11GalerkinResidualProfile
    fourCellOddP11GalerkinLowProfile
    fourCellOddP11OldBlockResidual
    fourCellOddP11OldBlockProjection
    fourCellOddP11GalerkinRetainedProfile
    fourCellOddP13AugmentedGalerkinResidualProfile
    fourCellOddP11AugmentedLowProfile
    fourCellOddP13RankOneAugmentedCoefficients
    fourCellOddP13RankOneUpdatedOldCoefficients
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp
  ring

/-- The rank-one residual remains orthogonal to every old retained vector. -/
theorem fourCellOddP13RankOneAugmentedResidual_oldBlock_orthogonal
    (y : Fin 4 → ℝ) :
    fourCellOddCoreLocalBilinear fourCellOddP13RankOneAugmentedResidual
        (fourCellOddP11GalerkinRetainedProfile y) = 0 := by
  let negU : ℝ → ℝ := fun x ↦
    (-fourCellOddP11AugmentedSchurLambda) *
      fourCellOddP11OldBlockResidual x
  have hneg : ContDiff ℝ 1 negU :=
    contDiff_const.mul contDiff_fourCellOddP11OldBlockResidual
  have hnegodd : Function.Odd negU :=
    odd_const_mul odd_fourCellOddP11OldBlockResidual
      (-fourCellOddP11AugmentedSchurLambda)
  have hupdate : fourCellOddP13RankOneAugmentedResidual =
      fourCellOddP11OldGalerkinResidual + negU := by
    funext x
    unfold fourCellOddP13RankOneAugmentedResidual
    dsimp only [negU]
    simp only [Pi.add_apply]
    ring
  rw [hupdate,
    fourCellOddCoreLocalBilinear_add_left
      fourCellOddP11OldGalerkinResidual negU
      (fourCellOddP11GalerkinRetainedProfile y)
      contDiff_fourCellOddP11OldGalerkinResidual hneg (contDiff_retainedProfile y)
      odd_fourCellOddP11OldGalerkinResidual hnegodd (odd_retainedProfile y)]
  dsimp only [negU]
  rw [fourCellOddCoreLocalBilinear_const_mul_left
    fourCellOddP11OldBlockResidual
    (fourCellOddP11GalerkinRetainedProfile y)
    contDiff_fourCellOddP11OldBlockResidual (contDiff_retainedProfile y)
    odd_fourCellOddP11OldBlockResidual (odd_retainedProfile y)
    (-fourCellOddP11AugmentedSchurLambda),
    fourCellOddP11OldGalerkinResidual_orthogonal y,
    fourCellOddP11OldBlockResidual_orthogonal y]
  ring

/-- If the new Schur pivot is nonzero, the updated residual is orthogonal to
the newly retained `P11` direction. -/
theorem fourCellOddP13RankOneAugmentedResidual_tail_orthogonal
    (hD : fourCellOddP11OldBlockSchurPivot ≠ 0) :
    fourCellOddCoreLocalBilinear fourCellOddP13RankOneAugmentedResidual
      fourCellOddP11DirectTail = 0 := by
  let negU : ℝ → ℝ := fun x ↦
    (-fourCellOddP11AugmentedSchurLambda) *
      fourCellOddP11OldBlockResidual x
  have hneg : ContDiff ℝ 1 negU :=
    contDiff_const.mul contDiff_fourCellOddP11OldBlockResidual
  have hnegodd : Function.Odd negU :=
    odd_const_mul odd_fourCellOddP11OldBlockResidual
      (-fourCellOddP11AugmentedSchurLambda)
  have hupdate : fourCellOddP13RankOneAugmentedResidual =
      fourCellOddP11OldGalerkinResidual + negU := by
    funext x
    unfold fourCellOddP13RankOneAugmentedResidual
    dsimp only [negU]
    simp only [Pi.add_apply]
    ring
  rw [hupdate,
    fourCellOddCoreLocalBilinear_add_left
      fourCellOddP11OldGalerkinResidual negU fourCellOddP11DirectTail
      contDiff_fourCellOddP11OldGalerkinResidual hneg
      contDiff_fourCellOddP11DirectTail
      odd_fourCellOddP11OldGalerkinResidual hnegodd
      odd_fourCellOddP11DirectTail]
  dsimp only [negU]
  rw [fourCellOddCoreLocalBilinear_const_mul_left
    fourCellOddP11OldBlockResidual fourCellOddP11DirectTail
    contDiff_fourCellOddP11OldBlockResidual contDiff_fourCellOddP11DirectTail
    odd_fourCellOddP11OldBlockResidual odd_fourCellOddP11DirectTail
    (-fourCellOddP11AugmentedSchurLambda),
    ← fourCellOddP11OldBlockSchurPivot_eq_residual_tail_row]
  change fourCellOddP11ExactResidualTailCross +
      (-fourCellOddP11AugmentedSchurLambda) *
        fourCellOddP11OldBlockSchurPivot = 0
  unfold fourCellOddP11AugmentedSchurLambda
  field_simp
  ring

/-- The reconstructed five coefficients satisfy all enlarged finite normal
equations whenever the Schur pivot is nonzero. -/
theorem fourCellOddP13RankOneAugmentedCoefficients_orthogonal
    (hD : fourCellOddP11OldBlockSchurPivot ≠ 0) :
    FourCellOddP13AugmentedGalerkinFiniteOrthogonal
      (fourCellOddP13RankOneAugmentedCoefficients 0)
      (fourCellOddP13RankOneAugmentedCoefficients 1)
      (fourCellOddP13RankOneAugmentedCoefficients 2)
      (fourCellOddP13RankOneAugmentedCoefficients 3)
      (fourCellOddP13RankOneAugmentedCoefficients 4) := by
  intro d e f g h
  let y : Fin 4 → ℝ := ![d, e, f, g]
  let ht : ℝ → ℝ := fun x ↦ h * fourCellOddP11DirectTail x
  have hyt :
      fourCellOddP11AugmentedLowProfile d e f g h =
        fourCellOddP11GalerkinRetainedProfile y + ht := by
    funext x
    unfold fourCellOddP11AugmentedLowProfile
      fourCellOddP11GalerkinRetainedProfile
    dsimp only [y, ht]
    simp only [Pi.add_apply]
    simp
  have hht : ContDiff ℝ 1 ht :=
    contDiff_const.mul contDiff_fourCellOddP11DirectTail
  have hhtodd : Function.Odd ht :=
    odd_const_mul odd_fourCellOddP11DirectTail h
  rw [← fourCellOddP13RankOneAugmentedResidual_eq_GalerkinResidual, hyt,
    bilinear_add_right fourCellOddP13RankOneAugmentedResidual
      (fourCellOddP11GalerkinRetainedProfile y) ht
      contDiff_fourCellOddP13RankOneAugmentedResidual (contDiff_retainedProfile y)
      hht odd_fourCellOddP13RankOneAugmentedResidual (odd_retainedProfile y)
      hhtodd]
  dsimp only [ht]
  rw [fourCellOddCoreLocalBilinear_const_mul_right
      fourCellOddP13RankOneAugmentedResidual fourCellOddP11DirectTail
      contDiff_fourCellOddP13RankOneAugmentedResidual
      contDiff_fourCellOddP11DirectTail
      odd_fourCellOddP13RankOneAugmentedResidual
      odd_fourCellOddP11DirectTail h,
    fourCellOddP13RankOneAugmentedResidual_oldBlock_orthogonal y,
    fourCellOddP13RankOneAugmentedResidual_tail_orthogonal hD]
  ring

/-- Polarized quadratic expansion of the rank-one update, before dividing by
the Schur pivot. -/
theorem fourCellOddP13RankOneAugmentedResidual_quadratic_expansion :
    fourCellOddCoreLocalQuadratic fourCellOddP13RankOneAugmentedResidual =
      fourCellOddP11OldGalerkinResidualPivot -
        2 * fourCellOddP11AugmentedSchurLambda *
          fourCellOddP11ExactResidualTailCross +
        fourCellOddP11AugmentedSchurLambda ^ 2 *
          fourCellOddP11OldBlockSchurPivot := by
  let negU : ℝ → ℝ := fun x ↦
    (-fourCellOddP11AugmentedSchurLambda) *
      fourCellOddP11OldBlockResidual x
  have hneg : ContDiff ℝ 1 negU :=
    contDiff_const.mul contDiff_fourCellOddP11OldBlockResidual
  have hupdate : fourCellOddP13RankOneAugmentedResidual =
      fourCellOddP11OldGalerkinResidual + negU := by
    funext x
    unfold fourCellOddP13RankOneAugmentedResidual
    dsimp only [negU]
    simp only [Pi.add_apply]
    ring
  rw [hupdate,
    fourCellOddCoreLocalQuadratic_add
      fourCellOddP11OldGalerkinResidual negU
      contDiff_fourCellOddP11OldGalerkinResidual.continuous hneg.continuous]
  dsimp only [negU]
  rw [fourCellOddCoreLocalBilinear_const_mul_right
      fourCellOddP11OldGalerkinResidual fourCellOddP11OldBlockResidual
      contDiff_fourCellOddP11OldGalerkinResidual
      contDiff_fourCellOddP11OldBlockResidual
      odd_fourCellOddP11OldGalerkinResidual
      odd_fourCellOddP11OldBlockResidual
      (-fourCellOddP11AugmentedSchurLambda),
    fourCellOddCoreLocalQuadratic_const_mul
      fourCellOddP11OldBlockResidual
      contDiff_fourCellOddP11OldBlockResidual
      odd_fourCellOddP11OldBlockResidual
      (-fourCellOddP11AugmentedSchurLambda),
    fourCellOddP11OldGalerkinResidual_oldBlockResidual_cross]
  unfold fourCellOddP11OldGalerkinResidualPivot
    fourCellOddP11OldBlockSchurPivot
  ring

/-- Exact division-free rank-one Schur identity. -/
theorem fourCellOddP13RankOneAugmentedResidual_schur_identity
    (hD : fourCellOddP11OldBlockSchurPivot ≠ 0) :
    fourCellOddP11OldBlockSchurPivot *
        fourCellOddCoreLocalQuadratic fourCellOddP13RankOneAugmentedResidual =
      fourCellOddP11OldGalerkinResidualPivot *
          fourCellOddP11OldBlockSchurPivot -
        fourCellOddP11ExactResidualTailCross ^ 2 := by
  rw [fourCellOddP13RankOneAugmentedResidual_quadratic_expansion]
  unfold fourCellOddP11AugmentedSchurLambda
  field_simp
  ring

/-- Quotient form of the same Schur identity. -/
theorem fourCellOddP13RankOneAugmentedResidual_quadratic_eq_schur :
    fourCellOddP11OldBlockSchurPivot ≠ 0 →
    fourCellOddCoreLocalQuadratic fourCellOddP13RankOneAugmentedResidual =
      fourCellOddP11OldGalerkinResidualPivot -
        fourCellOddP11ExactResidualTailCross ^ 2 /
          fourCellOddP11OldBlockSchurPivot := by
  intro hD
  have hid := fourCellOddP13RankOneAugmentedResidual_schur_identity hD
  field_simp
  nlinarith

/-- Nonnegative scalar Schur data imply nonnegativity of the reconstructed
augmented residual. -/
theorem fourCellOddP13RankOneAugmentedResidual_core_nonneg_of_schur
    (hD : 0 < fourCellOddP11OldBlockSchurPivot)
    (hcost : fourCellOddP11ExactResidualTailCross ^ 2 ≤
      fourCellOddP11OldGalerkinResidualPivot *
        fourCellOddP11OldBlockSchurPivot) :
    0 ≤ fourCellOddCoreLocalQuadratic
      fourCellOddP13RankOneAugmentedResidual := by
  have hid := fourCellOddP13RankOneAugmentedResidual_schur_identity
    (ne_of_gt hD)
  nlinarith

/-- Strict scalar Schur data imply positivity of the reconstructed augmented
residual. -/
theorem fourCellOddP13RankOneAugmentedResidual_core_pos_of_schur
    (hD : 0 < fourCellOddP11OldBlockSchurPivot)
    (hcost : fourCellOddP11ExactResidualTailCross ^ 2 <
      fourCellOddP11OldGalerkinResidualPivot *
        fourCellOddP11OldBlockSchurPivot) :
    0 < fourCellOddCoreLocalQuadratic
      fourCellOddP13RankOneAugmentedResidual := by
  have hid := fourCellOddP13RankOneAugmentedResidual_schur_identity
    (ne_of_gt hD)
  nlinarith

/-- Clean rational interface for the analytic estimates: the floors
`Q0 >= 1/5000`, `D > 3/20`, and `|b| < 3/1000` force strict positivity. -/
theorem fourCellOddP13RankOneAugmentedResidual_core_pos_of_rational_bounds
    (hQ0 : (1 / 5000 : ℝ) ≤ fourCellOddP11OldGalerkinResidualPivot)
    (hD : (3 / 20 : ℝ) < fourCellOddP11OldBlockSchurPivot)
    (hb : |fourCellOddP11ExactResidualTailCross| < (3 / 1000 : ℝ)) :
    0 < fourCellOddCoreLocalQuadratic
      fourCellOddP13RankOneAugmentedResidual := by
  have hQ0pos : 0 < fourCellOddP11OldGalerkinResidualPivot := by
    linarith
  have hDpos : 0 < fourCellOddP11OldBlockSchurPivot := by
    linarith
  have hbounds := abs_lt.mp hb
  have hbsq : fourCellOddP11ExactResidualTailCross ^ 2 <
      (3 / 1000 : ℝ) ^ 2 := by
    nlinarith
  have hscale :
      fourCellOddP11OldGalerkinResidualPivot * (3 / 20 : ℝ) <
        fourCellOddP11OldGalerkinResidualPivot *
          fourCellOddP11OldBlockSchurPivot :=
    mul_lt_mul_of_pos_left hD hQ0pos
  have hfloor :
      (1 / 5000 : ℝ) * (3 / 20 : ℝ) ≤
        fourCellOddP11OldGalerkinResidualPivot * (3 / 20 : ℝ) :=
    mul_le_mul_of_nonneg_right hQ0 (by norm_num)
  apply fourCellOddP13RankOneAugmentedResidual_core_pos_of_schur hDpos
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedRankOneSchurStructural
