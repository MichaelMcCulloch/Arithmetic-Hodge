import ArithmeticHodge.Analysis.YoshidaFourCellOddP13RetentionStructural
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

open MeasureTheory Real Set Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP13RetainedFiniteSolveStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddP13AugmentedDecompositionStructural
open YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
open YoshidaFourCellOddP13AugmentedResidualRepresenterStructural
open YoshidaFourCellOddP13RetentionStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# Exact finite solve after genuinely retaining `P13`

The retained block is now `P3/P5/P7/P9/P11/P13`.  Its core Gram is
nonsingular for a structural reason: a kernel vector has zero core
quadratic, while actual-core coercivity on the `P1`-orthogonal odd space
controls its exact diagonal seven-mode mass.  Positivity of the six
Legendre masses then kills every coordinate.  No determinant expansion is
used.
-/

/-- A coefficient vector interpreted in the six-dimensional retained block. -/
def fourCellOddP13RetainedProfile (x : Fin 6 → ℝ) : ℝ → ℝ :=
  fourCellOddP13SevenModeProfile
    0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

private def retainedBasis : Fin 6 → (ℝ → ℝ) :=
  ![centeredP3, factorTwoCenteredP5, factorTwoCenteredP7,
    factorTwoCenteredP9, fourCellOddP11DirectTail,
    fourCellOddP13DirectTail]

private theorem contDiff_centeredP1_local : ContDiff ℝ 1 centeredP1 := by
  unfold centeredP1
  fun_prop

private theorem odd_centeredP1_local : Function.Odd centeredP1 := by
  intro t
  unfold centeredP1
  ring

private theorem contDiff_centeredP3_local : ContDiff ℝ 1 centeredP3 := by
  unfold centeredP3
  fun_prop

private theorem odd_centeredP3_local : Function.Odd centeredP3 := by
  intro t
  unfold centeredP3
  ring

private theorem contDiff_factorTwoCenteredP5_local :
    ContDiff ℝ 1 factorTwoCenteredP5 := by
  unfold factorTwoCenteredP5
  fun_prop

private theorem contDiff_factorTwoCenteredP7_local :
    ContDiff ℝ 1 factorTwoCenteredP7 := by
  rw [show factorTwoCenteredP7 = fun t ↦
      (429 * t ^ 7 - 693 * t ^ 5 + 315 * t ^ 3 - 35 * t) / 16 by
    funext t
    exact factorTwoCenteredP7_eq t]
  fun_prop

private theorem contDiff_factorTwoCenteredP9_local :
    ContDiff ℝ 1 factorTwoCenteredP9 := by
  rw [show factorTwoCenteredP9 = fun t ↦
      (12155 * t ^ 9 - 25740 * t ^ 7 + 18018 * t ^ 5 -
        4620 * t ^ 3 + 315 * t) / 128 by
    funext t
    exact factorTwoCenteredP9_eq t]
  fun_prop

private theorem contDiff_retainedBasis (i : Fin 6) :
    ContDiff ℝ 1 (retainedBasis i) := by
  fin_cases i
  · exact contDiff_centeredP3_local
  · exact contDiff_factorTwoCenteredP5_local
  · exact contDiff_factorTwoCenteredP7_local
  · exact contDiff_factorTwoCenteredP9_local
  · exact contDiff_fourCellOddP11DirectTail
  · exact contDiff_fourCellOddP13DirectTail

private theorem odd_retainedBasis (i : Fin 6) :
    Function.Odd (retainedBasis i) := by
  fin_cases i
  · exact odd_centeredP3_local
  · exact odd_factorTwoCenteredP5
  · exact odd_factorTwoCenteredP7
  · exact odd_factorTwoCenteredP9
  · exact odd_fourCellOddP11DirectTail
  · exact odd_fourCellOddP13DirectTail

theorem contDiff_fourCellOddP13RetainedProfile (x : Fin 6 → ℝ) :
    ContDiff ℝ 1 (fourCellOddP13RetainedProfile x) :=
  contDiff_fourCellOddP13SevenModeProfile
    0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

theorem odd_fourCellOddP13RetainedProfile (x : Fin 6 → ℝ) :
    Function.Odd (fourCellOddP13RetainedProfile x) :=
  odd_fourCellOddP13SevenModeProfile
    0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

/-- Exact diagonal positive-half mass of the six retained coordinates. -/
theorem integral_zero_one_fourCellOddP13RetainedProfile_sq
    (x : Fin 6 → ℝ) :
    (∫ t : ℝ in 0..1, fourCellOddP13RetainedProfile x t ^ 2) =
      (x 0) ^ 2 / 7 + (x 1) ^ 2 / 11 + (x 2) ^ 2 / 15 +
        (x 3) ^ 2 / 19 + (x 4) ^ 2 / 23 + (x 5) ^ 2 / 27 := by
  change (∫ t : ℝ in 0..1,
      fourCellOddP13SevenModeSelector
        0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) t ^ 2) = _
  rw [integral_zero_one_fourCellOddP13SevenModeSelector_sq]
  ring

/-- Algebraic independence of the retained coordinates, extracted from the
positive diagonal mass rather than from monomial coefficients. -/
theorem fourCellOddP13RetainedProfile_coefficients_eq_zero_of_mass_nonpos
    (x : Fin 6 → ℝ)
    (hmass : (∫ t : ℝ in 0..1,
      fourCellOddP13RetainedProfile x t ^ 2) ≤ 0) :
    x = 0 := by
  rw [integral_zero_one_fourCellOddP13RetainedProfile_sq] at hmass
  have hx0 : x 0 = 0 := by
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 3), sq_nonneg (x 4), sq_nonneg (x 5)]
  have hx1 : x 1 = 0 := by
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 3), sq_nonneg (x 4), sq_nonneg (x 5)]
  have hx2 : x 2 = 0 := by
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 3), sq_nonneg (x 4), sq_nonneg (x 5)]
  have hx3 : x 3 = 0 := by
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 3), sq_nonneg (x 4), sq_nonneg (x 5)]
  have hx4 : x 4 = 0 := by
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 3), sq_nonneg (x 4), sq_nonneg (x 5)]
  have hx5 : x 5 = 0 := by
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 3), sq_nonneg (x 4), sq_nonneg (x 5)]
  funext i
  fin_cases i <;> simp [hx0, hx1, hx2, hx3, hx4, hx5]

private theorem centeredOddP1Coefficient_add_const_mul_local
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) (a : ℝ) :
    centeredOddP1Coefficient (u + fun t ↦ a * v t) =
      centeredOddP1Coefficient u + a * centeredOddP1Coefficient v := by
  unfold centeredOddP1Coefficient
  have huI : IntervalIntegrable (fun t : ℝ ↦ u t * centeredP1 t)
      volume (-1) 1 :=
    (hu.mul contDiff_centeredP1_local.continuous).intervalIntegrable _ _
  have hvI : IntervalIntegrable (fun t : ℝ ↦
      a * (v t * centeredP1 t)) volume (-1) 1 :=
    (continuous_const.mul
      (hv.mul contDiff_centeredP1_local.continuous)).intervalIntegrable _ _
  rw [show (fun t : ℝ ↦
      (u + fun z ↦ a * v z) t * centeredP1 t) =
      fun t ↦ u t * centeredP1 t + a * (v t * centeredP1 t) by
    funext t
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add huI hvI,
    intervalIntegral.integral_const_mul]
  ring

private theorem centeredOddP1Coefficient_fourCellOddP13DirectTail_eq_zero :
    centeredOddP1Coefficient fourCellOddP13DirectTail = 0 := by
  have hhalf : (∫ t : ℝ in 0..1,
      fourCellOddP13DirectTail t * centeredP1 t) = 0 := by
    rw [show (fun t : ℝ ↦
        fourCellOddP13DirectTail t * centeredP1 t) =
      fun t ↦ centeredP1 t * fourCellOddP13DirectTail t by
        funext t
        ring]
    exact integral_zero_one_centeredP1_mul_fourCellOddP13DirectTail_eq_zero
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun t : ℝ ↦ fourCellOddP13DirectTail t * centeredP1 t)
    ((contDiff_fourCellOddP13DirectTail.continuous.mul
      contDiff_centeredP1_local.continuous).intervalIntegrable _ _)
    (by
      intro t
      change fourCellOddP13DirectTail (-t) * centeredP1 (-t) =
        fourCellOddP13DirectTail t * centeredP1 t
      rw [odd_fourCellOddP13DirectTail, odd_centeredP1_local]
      ring)
  rw [hhalf] at hfold
  unfold centeredOddP1Coefficient
  rw [hfold]
  ring

private theorem centeredOddP1Coefficient_fourCellOddP13RetainedProfile_eq_zero
    (x : Fin 6 → ℝ) :
    centeredOddP1Coefficient (fourCellOddP13RetainedProfile x) = 0 := by
  let u := fourCellOddP11AugmentedLowProfile
    (x 0) (x 1) (x 2) (x 3) (x 4)
  have hu : Continuous u := by
    dsimp only [u]
    exact (contDiff_fourCellOddP11AugmentedLowProfile _ _ _ _ _).continuous
  have hprofile : fourCellOddP13RetainedProfile x =
      u + fun t ↦ x 5 * fourCellOddP13DirectTail t := by
    funext t
    dsimp only [u]
    unfold fourCellOddP13RetainedProfile fourCellOddP13SevenModeProfile
      fourCellOddP13SixModeProfile fourCellOddP11AugmentedLowProfile
    simp only [Pi.add_apply]
  rw [hprofile,
    centeredOddP1Coefficient_add_const_mul_local u
      fourCellOddP13DirectTail hu
      contDiff_fourCellOddP13DirectTail.continuous (x 5),
    centeredOddP1Coefficient_augmentedLowProfile_eq_zero,
    centeredOddP1Coefficient_fourCellOddP13DirectTail_eq_zero]
  ring

/-- Exact core Gram of the retained `P3/P5/P7/P9/P11/P13` block. -/
def fourCellOddP13RetainedGram : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j ↦ fourCellOddCoreLocalBilinear (retainedBasis i) (retainedBasis j)

/-- Exact `P1` mixed row in retained coordinates. -/
def fourCellOddP13RetainedRhs : Fin 6 → ℝ :=
  fun i ↦ fourCellOddCoreLocalBilinear (retainedBasis i) centeredP1

private theorem odd_const_mul
    {v : ℝ → ℝ} (hv : Function.Odd v) (a : ℝ) :
    Function.Odd (fun t ↦ a * v t) := by
  intro t
  change a * v (-t) = -(a * v t)
  rw [hv]
  ring

private theorem fourCellOddCoreLocalBilinear_add_right
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

private theorem fourCellOddP13RetainedProfile_decompose
    (x : Fin 6 → ℝ) :
    fourCellOddP13RetainedProfile x =
      (((((fun t ↦ x 0 * centeredP3 t) +
        (fun t ↦ x 1 * factorTwoCenteredP5 t)) +
        (fun t ↦ x 2 * factorTwoCenteredP7 t)) +
        (fun t ↦ x 3 * factorTwoCenteredP9 t)) +
        (fun t ↦ x 4 * fourCellOddP11DirectTail t)) +
        (fun t ↦ x 5 * fourCellOddP13DirectTail t) := by
  funext t
  unfold fourCellOddP13RetainedProfile fourCellOddP13SevenModeProfile
    fourCellOddP13SixModeProfile
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp only [Pi.add_apply]
  ring

private theorem fourCellOddCoreLocalBilinear_retainedProfile_right
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (huodd : Function.Odd u)
    (x : Fin 6 → ℝ) :
    fourCellOddCoreLocalBilinear u (fourCellOddP13RetainedProfile x) =
      x 0 * fourCellOddCoreLocalBilinear u centeredP3 +
      x 1 * fourCellOddCoreLocalBilinear u factorTwoCenteredP5 +
      x 2 * fourCellOddCoreLocalBilinear u factorTwoCenteredP7 +
      x 3 * fourCellOddCoreLocalBilinear u factorTwoCenteredP9 +
      x 4 * fourCellOddCoreLocalBilinear u fourCellOddP11DirectTail +
      x 5 * fourCellOddCoreLocalBilinear u fourCellOddP13DirectTail := by
  let v3 : ℝ → ℝ := fun t ↦ x 0 * centeredP3 t
  let v5 : ℝ → ℝ := fun t ↦ x 1 * factorTwoCenteredP5 t
  let v7 : ℝ → ℝ := fun t ↦ x 2 * factorTwoCenteredP7 t
  let v9 : ℝ → ℝ := fun t ↦ x 3 * factorTwoCenteredP9 t
  let v11 : ℝ → ℝ := fun t ↦ x 4 * fourCellOddP11DirectTail t
  let v13 : ℝ → ℝ := fun t ↦ x 5 * fourCellOddP13DirectTail t
  have hv3 : ContDiff ℝ 1 v3 := contDiff_const.mul contDiff_centeredP3_local
  have hv5 : ContDiff ℝ 1 v5 := contDiff_const.mul contDiff_factorTwoCenteredP5_local
  have hv7 : ContDiff ℝ 1 v7 := contDiff_const.mul contDiff_factorTwoCenteredP7_local
  have hv9 : ContDiff ℝ 1 v9 := contDiff_const.mul contDiff_factorTwoCenteredP9_local
  have hv11 : ContDiff ℝ 1 v11 :=
    contDiff_const.mul contDiff_fourCellOddP11DirectTail
  have hv13 : ContDiff ℝ 1 v13 :=
    contDiff_const.mul contDiff_fourCellOddP13DirectTail
  have hv3odd : Function.Odd v3 := odd_const_mul odd_centeredP3_local (x 0)
  have hv5odd : Function.Odd v5 := odd_const_mul odd_factorTwoCenteredP5 (x 1)
  have hv7odd : Function.Odd v7 := odd_const_mul odd_factorTwoCenteredP7 (x 2)
  have hv9odd : Function.Odd v9 := odd_const_mul odd_factorTwoCenteredP9 (x 3)
  have hv11odd : Function.Odd v11 := odd_const_mul odd_fourCellOddP11DirectTail (x 4)
  have hv13odd : Function.Odd v13 := odd_const_mul odd_fourCellOddP13DirectTail (x 5)
  rw [fourCellOddP13RetainedProfile_decompose]
  change fourCellOddCoreLocalBilinear u
      (((((v3 + v5) + v7) + v9) + v11) + v13) = _
  rw [fourCellOddCoreLocalBilinear_add_right u ((((v3 + v5) + v7) + v9) + v11)
      v13 hu ((((hv3.add hv5).add hv7).add hv9).add hv11) hv13 huodd
      ((((hv3odd.add hv5odd).add hv7odd).add hv9odd).add hv11odd) hv13odd,
    fourCellOddCoreLocalBilinear_add_right u (((v3 + v5) + v7) + v9)
      v11 hu (((hv3.add hv5).add hv7).add hv9) hv11 huodd
      (((hv3odd.add hv5odd).add hv7odd).add hv9odd) hv11odd,
    fourCellOddCoreLocalBilinear_add_right u ((v3 + v5) + v7)
      v9 hu ((hv3.add hv5).add hv7) hv9 huodd
      ((hv3odd.add hv5odd).add hv7odd) hv9odd,
    fourCellOddCoreLocalBilinear_add_right u (v3 + v5)
      v7 hu (hv3.add hv5) hv7 huodd (hv3odd.add hv5odd) hv7odd,
    fourCellOddCoreLocalBilinear_add_right u v3 v5
      hu hv3 hv5 huodd hv3odd hv5odd]
  dsimp only [v3, v5, v7, v9, v11, v13]
  rw [fourCellOddCoreLocalBilinear_const_mul_right
      u centeredP3 hu contDiff_centeredP3_local huodd odd_centeredP3_local (x 0),
    fourCellOddCoreLocalBilinear_const_mul_right
      u factorTwoCenteredP5 hu contDiff_factorTwoCenteredP5_local
        huodd odd_factorTwoCenteredP5 (x 1),
    fourCellOddCoreLocalBilinear_const_mul_right
      u factorTwoCenteredP7 hu contDiff_factorTwoCenteredP7_local
        huodd odd_factorTwoCenteredP7 (x 2),
    fourCellOddCoreLocalBilinear_const_mul_right
      u factorTwoCenteredP9 hu contDiff_factorTwoCenteredP9_local
        huodd odd_factorTwoCenteredP9 (x 3),
    fourCellOddCoreLocalBilinear_const_mul_right
      u fourCellOddP11DirectTail hu contDiff_fourCellOddP11DirectTail
        huodd odd_fourCellOddP11DirectTail (x 4),
    fourCellOddCoreLocalBilinear_const_mul_right
      u fourCellOddP13DirectTail hu contDiff_fourCellOddP13DirectTail
        huodd odd_fourCellOddP13DirectTail (x 5)]

private theorem fourCellOddCoreLocalBilinear_retainedProfile_left
    (x : Fin 6 → ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 1 v) (hvodd : Function.Odd v) :
    fourCellOddCoreLocalBilinear (fourCellOddP13RetainedProfile x) v =
      x 0 * fourCellOddCoreLocalBilinear centeredP3 v +
      x 1 * fourCellOddCoreLocalBilinear factorTwoCenteredP5 v +
      x 2 * fourCellOddCoreLocalBilinear factorTwoCenteredP7 v +
      x 3 * fourCellOddCoreLocalBilinear factorTwoCenteredP9 v +
      x 4 * fourCellOddCoreLocalBilinear fourCellOddP11DirectTail v +
      x 5 * fourCellOddCoreLocalBilinear fourCellOddP13DirectTail v := by
  rw [fourCellOddCoreLocalBilinear_comm
      (fourCellOddP13RetainedProfile x) v
      (contDiff_fourCellOddP13RetainedProfile x).continuous hv.continuous,
    fourCellOddCoreLocalBilinear_retainedProfile_right v hv hvodd x,
    fourCellOddCoreLocalBilinear_comm v centeredP3
      hv.continuous contDiff_centeredP3_local.continuous,
    fourCellOddCoreLocalBilinear_comm v factorTwoCenteredP5
      hv.continuous contDiff_factorTwoCenteredP5_local.continuous,
    fourCellOddCoreLocalBilinear_comm v factorTwoCenteredP7
      hv.continuous contDiff_factorTwoCenteredP7_local.continuous,
    fourCellOddCoreLocalBilinear_comm v factorTwoCenteredP9
      hv.continuous contDiff_factorTwoCenteredP9_local.continuous,
    fourCellOddCoreLocalBilinear_comm v fourCellOddP11DirectTail
      hv.continuous contDiff_fourCellOddP11DirectTail.continuous,
    fourCellOddCoreLocalBilinear_comm v fourCellOddP13DirectTail
      hv.continuous contDiff_fourCellOddP13DirectTail.continuous]

private theorem fourCellOddP13RetainedGram_mulVec (x : Fin 6 → ℝ) :
    fourCellOddP13RetainedGram *ᵥ x =
      fun i ↦ fourCellOddCoreLocalBilinear
        (retainedBasis i) (fourCellOddP13RetainedProfile x) := by
  funext i
  rw [fourCellOddCoreLocalBilinear_retainedProfile_right
    (retainedBasis i) (contDiff_retainedBasis i) (odd_retainedBasis i) x]
  simp [fourCellOddP13RetainedGram, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, retainedBasis]
  ring

/-- The retained Gram has trivial kernel by actual-core coercivity and the
positive diagonal seven-mode mass. -/
theorem fourCellOddP13RetainedGram_kernel
    (x : Fin 6 → ℝ) (hx : fourCellOddP13RetainedGram *ᵥ x = 0) :
    x = 0 := by
  have hrows := fourCellOddP13RetainedGram_mulVec x
  rw [hx] at hrows
  have hrow (i : Fin 6) :
      fourCellOddCoreLocalBilinear (retainedBasis i)
        (fourCellOddP13RetainedProfile x) = 0 := by
    have hi := congrFun hrows i
    simpa using hi.symm
  have h3 : fourCellOddCoreLocalBilinear centeredP3
      (fourCellOddP13RetainedProfile x) = 0 := by
    simpa [retainedBasis] using hrow 0
  have h5 : fourCellOddCoreLocalBilinear factorTwoCenteredP5
      (fourCellOddP13RetainedProfile x) = 0 := by
    simpa [retainedBasis] using hrow 1
  have h7 : fourCellOddCoreLocalBilinear factorTwoCenteredP7
      (fourCellOddP13RetainedProfile x) = 0 := by
    simpa [retainedBasis] using hrow 2
  have h9 : fourCellOddCoreLocalBilinear factorTwoCenteredP9
      (fourCellOddP13RetainedProfile x) = 0 := by
    simpa [retainedBasis] using hrow 3
  have h11 : fourCellOddCoreLocalBilinear fourCellOddP11DirectTail
      (fourCellOddP13RetainedProfile x) = 0 := by
    simpa [retainedBasis] using hrow 4
  have h13 : fourCellOddCoreLocalBilinear fourCellOddP13DirectTail
      (fourCellOddP13RetainedProfile x) = 0 := by
    simpa [retainedBasis] using hrow 5
  have hself : fourCellOddCoreLocalBilinear
      (fourCellOddP13RetainedProfile x)
      (fourCellOddP13RetainedProfile x) = 0 := by
    rw [fourCellOddCoreLocalBilinear_retainedProfile_left x
      (fourCellOddP13RetainedProfile x)
      (contDiff_fourCellOddP13RetainedProfile x)
      (odd_fourCellOddP13RetainedProfile x), h3, h5, h7, h9, h11, h13]
    ring
  have hdiag := fourCellOddCoreLocalBilinear_self_eq_quadratic
    (fourCellOddP13RetainedProfile x)
    (contDiff_fourCellOddP13RetainedProfile x)
    (odd_fourCellOddP13RetainedProfile x)
  have hqzero : fourCellOddCoreLocalQuadratic
      (fourCellOddP13RetainedProfile x) = 0 := by
    linarith
  have hcoercive := fourCellOddCorePositiveHalfCoerciveAt_rationalFloor
    (fourCellOddP13RetainedProfile x)
    (contDiff_fourCellOddP13RetainedProfile x)
    (odd_fourCellOddP13RetainedProfile x)
    (centeredOddP1Coefficient_fourCellOddP13RetainedProfile_eq_zero x)
  rw [hqzero] at hcoercive
  have hmass : (∫ t : ℝ in 0..1,
      fourCellOddP13RetainedProfile x t ^ 2) ≤ 0 := by
    nlinarith
  exact fourCellOddP13RetainedProfile_coefficients_eq_zero_of_mass_nonpos
    x hmass

/-- The exact retained core Gram matrix is nonsingular. -/
theorem fourCellOddP13RetainedGram_isUnit :
    IsUnit fourCellOddP13RetainedGram := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hsub : fourCellOddP13RetainedGram *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp
    (fourCellOddP13RetainedGram_kernel (x - y) hsub)

private theorem fourCellOddP13RetainedGram_det_isUnit :
    IsUnit fourCellOddP13RetainedGram.det :=
  fourCellOddP13RetainedGram.isUnit_iff_isUnit_det.mp
    fourCellOddP13RetainedGram_isUnit

/-- Exact inverse-defined solution of the six retained normal equations. -/
def fourCellOddP13RetainedSolution : Fin 6 → ℝ :=
  fourCellOddP13RetainedGram⁻¹ *ᵥ fourCellOddP13RetainedRhs

theorem fourCellOddP13RetainedSolution_normalEquation :
    fourCellOddP13RetainedGram *ᵥ fourCellOddP13RetainedSolution =
      fourCellOddP13RetainedRhs := by
  unfold fourCellOddP13RetainedSolution
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv fourCellOddP13RetainedGram
      fourCellOddP13RetainedGram_det_isUnit,
    Matrix.one_mulVec]

/-- The inverse-defined normal equations hold against every retained
`P3/P5/P7/P9/P11/P13` profile. -/
theorem fourCellOddP13RetainedSolution_normal (y : Fin 6 → ℝ) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP13RetainedProfile fourCellOddP13RetainedSolution)
        (fourCellOddP13RetainedProfile y) =
      fourCellOddCoreLocalBilinear centeredP1
        (fourCellOddP13RetainedProfile y) := by
  let proj := fourCellOddP13RetainedProfile fourCellOddP13RetainedSolution
  have hproj : ContDiff ℝ 1 proj :=
    contDiff_fourCellOddP13RetainedProfile _
  have hprojodd : Function.Odd proj :=
    odd_fourCellOddP13RetainedProfile _
  have hrows : (fun i ↦ fourCellOddCoreLocalBilinear
      (retainedBasis i) proj) = fourCellOddP13RetainedRhs :=
    (fourCellOddP13RetainedGram_mulVec
      fourCellOddP13RetainedSolution).symm.trans
      fourCellOddP13RetainedSolution_normalEquation
  have hrow (i : Fin 6) :
      fourCellOddCoreLocalBilinear proj (retainedBasis i) =
        fourCellOddCoreLocalBilinear centeredP1 (retainedBasis i) := by
    have hi := congrFun hrows i
    change fourCellOddCoreLocalBilinear (retainedBasis i) proj =
      fourCellOddCoreLocalBilinear (retainedBasis i) centeredP1 at hi
    rw [fourCellOddCoreLocalBilinear_comm proj (retainedBasis i)
        hproj.continuous (contDiff_retainedBasis i).continuous,
      fourCellOddCoreLocalBilinear_comm centeredP1 (retainedBasis i)
        contDiff_centeredP1_local.continuous
          (contDiff_retainedBasis i).continuous]
    exact hi
  have h3 : fourCellOddCoreLocalBilinear proj centeredP3 =
      fourCellOddCoreLocalBilinear centeredP1 centeredP3 := by
    simpa [retainedBasis] using hrow 0
  have h5 : fourCellOddCoreLocalBilinear proj factorTwoCenteredP5 =
      fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP5 := by
    simpa [retainedBasis] using hrow 1
  have h7 : fourCellOddCoreLocalBilinear proj factorTwoCenteredP7 =
      fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP7 := by
    simpa [retainedBasis] using hrow 2
  have h9 : fourCellOddCoreLocalBilinear proj factorTwoCenteredP9 =
      fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP9 := by
    simpa [retainedBasis] using hrow 3
  have h11 : fourCellOddCoreLocalBilinear proj fourCellOddP11DirectTail =
      fourCellOddCoreLocalBilinear centeredP1 fourCellOddP11DirectTail := by
    simpa [retainedBasis] using hrow 4
  have h13 : fourCellOddCoreLocalBilinear proj fourCellOddP13DirectTail =
      fourCellOddCoreLocalBilinear centeredP1 fourCellOddP13DirectTail := by
    simpa [retainedBasis] using hrow 5
  change fourCellOddCoreLocalBilinear proj
      (fourCellOddP13RetainedProfile y) = _
  rw [fourCellOddCoreLocalBilinear_retainedProfile_right
      proj hproj hprojodd y,
    fourCellOddCoreLocalBilinear_retainedProfile_right centeredP1
      contDiff_centeredP1_local odd_centeredP1_local y,
    h3, h5, h7, h9, h11, h13]

/-- The exact `P1` residual after projection to all six retained modes. -/
def fourCellOddP13RetainedGalerkinResidualProfile
    (a3 a5 a7 a9 a11 a13 : ℝ) : ℝ → ℝ := fun t ↦
  centeredP1 t - fourCellOddP13RetainedProfile ![a3, a5, a7, a9, a11, a13] t

theorem contDiff_fourCellOddP13RetainedGalerkinResidualProfile
    (a3 a5 a7 a9 a11 a13 : ℝ) :
    ContDiff ℝ 1
      (fourCellOddP13RetainedGalerkinResidualProfile
        a3 a5 a7 a9 a11 a13) :=
  contDiff_centeredP1_local.sub
    (contDiff_fourCellOddP13RetainedProfile ![a3, a5, a7, a9, a11, a13])

theorem odd_fourCellOddP13RetainedGalerkinResidualProfile
    (a3 a5 a7 a9 a11 a13 : ℝ) :
    Function.Odd
      (fourCellOddP13RetainedGalerkinResidualProfile
        a3 a5 a7 a9 a11 a13) := by
  intro t
  unfold fourCellOddP13RetainedGalerkinResidualProfile
  rw [odd_centeredP1_local,
    odd_fourCellOddP13RetainedProfile ![a3, a5, a7, a9, a11, a13]]
  ring

/-- Exact core orthogonality of a residual to the complete retained block. -/
def FourCellOddP13RetainedGalerkinFiniteOrthogonal
    (a3 a5 a7 a9 a11 a13 : ℝ) : Prop :=
  ∀ y : Fin 6 → ℝ,
    fourCellOddCoreLocalBilinear
      (fourCellOddP13RetainedGalerkinResidualProfile
        a3 a5 a7 a9 a11 a13)
      (fourCellOddP13RetainedProfile y) = 0

/-- The inverse solution makes the `P1` residual core-orthogonal to all six
retained modes. -/
theorem fourCellOddP13RetainedSolution_orthogonal :
    FourCellOddP13RetainedGalerkinFiniteOrthogonal
      (fourCellOddP13RetainedSolution 0)
      (fourCellOddP13RetainedSolution 1)
      (fourCellOddP13RetainedSolution 2)
      (fourCellOddP13RetainedSolution 3)
      (fourCellOddP13RetainedSolution 4)
      (fourCellOddP13RetainedSolution 5) := by
  intro y
  let proj := fourCellOddP13RetainedProfile fourCellOddP13RetainedSolution
  let p := fourCellOddP13RetainedProfile y
  have hproj : ContDiff ℝ 1 proj :=
    contDiff_fourCellOddP13RetainedProfile _
  have hprojodd : Function.Odd proj :=
    odd_fourCellOddP13RetainedProfile _
  have hp : ContDiff ℝ 1 p := contDiff_fourCellOddP13RetainedProfile _
  have hpodd : Function.Odd p := odd_fourCellOddP13RetainedProfile _
  have hnormal := fourCellOddP13RetainedSolution_normal y
  have hcoordinates :
      (![fourCellOddP13RetainedSolution 0,
          fourCellOddP13RetainedSolution 1,
          fourCellOddP13RetainedSolution 2,
          fourCellOddP13RetainedSolution 3,
          fourCellOddP13RetainedSolution 4,
          fourCellOddP13RetainedSolution 5] : Fin 6 → ℝ) =
        fourCellOddP13RetainedSolution := by
    funext i
    fin_cases i <;> rfl
  have hresidual :
      fourCellOddP13RetainedGalerkinResidualProfile
          (fourCellOddP13RetainedSolution 0)
          (fourCellOddP13RetainedSolution 1)
          (fourCellOddP13RetainedSolution 2)
          (fourCellOddP13RetainedSolution 3)
          (fourCellOddP13RetainedSolution 4)
          (fourCellOddP13RetainedSolution 5) =
        centeredP1 + fun t ↦ (-1 : ℝ) * proj t := by
    funext t
    unfold fourCellOddP13RetainedGalerkinResidualProfile
    rw [hcoordinates]
    dsimp only [proj]
    simp only [Pi.add_apply]
    ring
  change fourCellOddCoreLocalBilinear
    (fourCellOddP13RetainedGalerkinResidualProfile
      (fourCellOddP13RetainedSolution 0)
      (fourCellOddP13RetainedSolution 1)
      (fourCellOddP13RetainedSolution 2)
      (fourCellOddP13RetainedSolution 3)
      (fourCellOddP13RetainedSolution 4)
      (fourCellOddP13RetainedSolution 5)) p = 0
  rw [hresidual,
    fourCellOddCoreLocalBilinear_add_left centeredP1
      (fun t ↦ (-1 : ℝ) * proj t) p
      contDiff_centeredP1_local (contDiff_const.mul hproj) hp
      odd_centeredP1_local (odd_const_mul hprojodd (-1)) hpodd,
    fourCellOddCoreLocalBilinear_const_mul_left proj p
      hproj hp hprojodd hpodd (-1)]
  change fourCellOddCoreLocalBilinear proj p =
    fourCellOddCoreLocalBilinear centeredP1 p at hnormal
  rw [hnormal]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP13RetainedFiniteSolveStructural
