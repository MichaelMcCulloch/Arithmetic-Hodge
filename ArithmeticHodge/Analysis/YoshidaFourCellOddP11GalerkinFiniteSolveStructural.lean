import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinRieszStructural
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

open MeasureTheory Real Set Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinFiniteSolveStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddFiveModeStrictCoercivityStructural
open YoshidaFourCellOddP11GalerkinRieszStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Exact finite Galerkin solve for the odd corrected cross

The retained `P₃/P₅/P₇/P₉` core Gram matrix has trivial kernel:
otherwise its kernel vector would give a nonzero retained five-mode profile
with zero core quadratic, contradicting strict five-mode coercivity.  Its
nonsingular inverse therefore solves the four Galerkin normal equations.
No entry of the Gram matrix is numerically evaluated.
-/

/-- A coefficient vector interpreted as a retained `P₃/P₅/P₇/P₉`
profile. -/
def fourCellOddP11GalerkinRetainedProfile
    (x : Fin 4 → ℝ) : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile
    0 (x 0) (x 1) (x 2) (x 3)

private def retainedBasisThree : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0

private def retainedBasisFive : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0

private def retainedBasisSeven : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0

private def retainedBasisNine : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1

/-- The exact core Gram matrix of the retained four-dimensional block. -/
def fourCellOddP11GalerkinRetainedGram : Matrix (Fin 4) (Fin 4) ℝ :=
  !![fourCellOddCoreLocalBilinear retainedBasisThree retainedBasisThree,
      fourCellOddCoreLocalBilinear retainedBasisThree retainedBasisFive,
      fourCellOddCoreLocalBilinear retainedBasisThree retainedBasisSeven,
      fourCellOddCoreLocalBilinear retainedBasisThree retainedBasisNine;
    fourCellOddCoreLocalBilinear retainedBasisFive retainedBasisThree,
      fourCellOddCoreLocalBilinear retainedBasisFive retainedBasisFive,
      fourCellOddCoreLocalBilinear retainedBasisFive retainedBasisSeven,
      fourCellOddCoreLocalBilinear retainedBasisFive retainedBasisNine;
    fourCellOddCoreLocalBilinear retainedBasisSeven retainedBasisThree,
      fourCellOddCoreLocalBilinear retainedBasisSeven retainedBasisFive,
      fourCellOddCoreLocalBilinear retainedBasisSeven retainedBasisSeven,
      fourCellOddCoreLocalBilinear retainedBasisSeven retainedBasisNine;
    fourCellOddCoreLocalBilinear retainedBasisNine retainedBasisThree,
      fourCellOddCoreLocalBilinear retainedBasisNine retainedBasisFive,
      fourCellOddCoreLocalBilinear retainedBasisNine retainedBasisSeven,
      fourCellOddCoreLocalBilinear retainedBasisNine retainedBasisNine]

/-- The exact `P₁` mixed row in retained coordinates. -/
def fourCellOddP11GalerkinRetainedRhs : Fin 4 → ℝ :=
  ![fourCellOddCoreLocalBilinear retainedBasisThree centeredP1,
    fourCellOddCoreLocalBilinear retainedBasisFive centeredP1,
    fourCellOddCoreLocalBilinear retainedBasisSeven centeredP1,
    fourCellOddCoreLocalBilinear retainedBasisNine centeredP1]

private theorem odd_const_mul
    {v : ℝ → ℝ} (hv : Function.Odd v) (a : ℝ) :
    Function.Odd (fun x ↦ a * v x) := by
  intro x
  change a * v (-x) = -(a * v x)
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

private theorem contDiff_retainedBasisThree :
    ContDiff ℝ 1 retainedBasisThree :=
  contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0

private theorem contDiff_retainedBasisFive :
    ContDiff ℝ 1 retainedBasisFive :=
  contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0

private theorem contDiff_retainedBasisSeven :
    ContDiff ℝ 1 retainedBasisSeven :=
  contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0

private theorem contDiff_retainedBasisNine :
    ContDiff ℝ 1 retainedBasisNine :=
  contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1

private theorem odd_retainedBasisThree : Function.Odd retainedBasisThree :=
  odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0

private theorem odd_retainedBasisFive : Function.Odd retainedBasisFive :=
  odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0

private theorem odd_retainedBasisSeven : Function.Odd retainedBasisSeven :=
  odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0

private theorem odd_retainedBasisNine : Function.Odd retainedBasisNine :=
  odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1

private theorem contDiff_fourCellOddP11GalerkinRetainedProfile
    (x : Fin 4 → ℝ) :
    ContDiff ℝ 1 (fourCellOddP11GalerkinRetainedProfile x) :=
  contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
    0 (x 0) (x 1) (x 2) (x 3)

private theorem odd_fourCellOddP11GalerkinRetainedProfile
    (x : Fin 4 → ℝ) :
    Function.Odd (fourCellOddP11GalerkinRetainedProfile x) :=
  odd_fourCellOddOneThreeFiveSevenNineLowProfile
    0 (x 0) (x 1) (x 2) (x 3)

private theorem fourCellOddP11GalerkinRetainedProfile_decompose
    (x : Fin 4 → ℝ) :
    fourCellOddP11GalerkinRetainedProfile x =
      ((fun z ↦ x 0 * retainedBasisThree z) +
        (fun z ↦ x 1 * retainedBasisFive z)) +
      (fun z ↦ x 2 * retainedBasisSeven z) +
      (fun z ↦ x 3 * retainedBasisNine z) := by
  funext z
  unfold fourCellOddP11GalerkinRetainedProfile
    retainedBasisThree retainedBasisFive retainedBasisSeven retainedBasisNine
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp only [Pi.add_apply]
  ring

private theorem fourCellOddCoreLocalBilinear_retainedProfile_right
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (huodd : Function.Odd u)
    (x : Fin 4 → ℝ) :
    fourCellOddCoreLocalBilinear u
        (fourCellOddP11GalerkinRetainedProfile x) =
      x 0 * fourCellOddCoreLocalBilinear u retainedBasisThree +
      x 1 * fourCellOddCoreLocalBilinear u retainedBasisFive +
      x 2 * fourCellOddCoreLocalBilinear u retainedBasisSeven +
      x 3 * fourCellOddCoreLocalBilinear u retainedBasisNine := by
  let v₃ : ℝ → ℝ := fun z ↦ x 0 * retainedBasisThree z
  let v₅ : ℝ → ℝ := fun z ↦ x 1 * retainedBasisFive z
  let v₇ : ℝ → ℝ := fun z ↦ x 2 * retainedBasisSeven z
  let v₉ : ℝ → ℝ := fun z ↦ x 3 * retainedBasisNine z
  have hv₃ : ContDiff ℝ 1 v₃ := contDiff_const.mul contDiff_retainedBasisThree
  have hv₅ : ContDiff ℝ 1 v₅ := contDiff_const.mul contDiff_retainedBasisFive
  have hv₇ : ContDiff ℝ 1 v₇ := contDiff_const.mul contDiff_retainedBasisSeven
  have hv₉ : ContDiff ℝ 1 v₉ := contDiff_const.mul contDiff_retainedBasisNine
  have hv₃odd : Function.Odd v₃ := odd_const_mul odd_retainedBasisThree (x 0)
  have hv₅odd : Function.Odd v₅ := odd_const_mul odd_retainedBasisFive (x 1)
  have hv₇odd : Function.Odd v₇ := odd_const_mul odd_retainedBasisSeven (x 2)
  have hv₉odd : Function.Odd v₉ := odd_const_mul odd_retainedBasisNine (x 3)
  rw [fourCellOddP11GalerkinRetainedProfile_decompose]
  change fourCellOddCoreLocalBilinear u (((v₃ + v₅) + v₇) + v₉) = _
  rw [fourCellOddCoreLocalBilinear_add_right u ((v₃ + v₅) + v₇) v₉
      hu ((hv₃.add hv₅).add hv₇) hv₉ huodd
      ((hv₃odd.add hv₅odd).add hv₇odd) hv₉odd,
    fourCellOddCoreLocalBilinear_add_right u (v₃ + v₅) v₇
      hu (hv₃.add hv₅) hv₇ huodd
      (hv₃odd.add hv₅odd) hv₇odd,
    fourCellOddCoreLocalBilinear_add_right u v₃ v₅
      hu hv₃ hv₅ huodd hv₃odd hv₅odd]
  dsimp only [v₃, v₅, v₇, v₉]
  rw [fourCellOddCoreLocalBilinear_const_mul_right
      u retainedBasisThree hu contDiff_retainedBasisThree
        huodd odd_retainedBasisThree (x 0),
    fourCellOddCoreLocalBilinear_const_mul_right
      u retainedBasisFive hu contDiff_retainedBasisFive
        huodd odd_retainedBasisFive (x 1),
    fourCellOddCoreLocalBilinear_const_mul_right
      u retainedBasisSeven hu contDiff_retainedBasisSeven
        huodd odd_retainedBasisSeven (x 2),
    fourCellOddCoreLocalBilinear_const_mul_right
      u retainedBasisNine hu contDiff_retainedBasisNine
        huodd odd_retainedBasisNine (x 3)]

private theorem fourCellOddCoreLocalBilinear_retainedProfile_left
    (x : Fin 4 → ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 1 v) (hvodd : Function.Odd v) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP11GalerkinRetainedProfile x) v =
      x 0 * fourCellOddCoreLocalBilinear retainedBasisThree v +
      x 1 * fourCellOddCoreLocalBilinear retainedBasisFive v +
      x 2 * fourCellOddCoreLocalBilinear retainedBasisSeven v +
      x 3 * fourCellOddCoreLocalBilinear retainedBasisNine v := by
  rw [fourCellOddCoreLocalBilinear_comm
      (fourCellOddP11GalerkinRetainedProfile x) v
      (contDiff_fourCellOddP11GalerkinRetainedProfile x).continuous hv.continuous,
    fourCellOddCoreLocalBilinear_retainedProfile_right v hv hvodd x,
    fourCellOddCoreLocalBilinear_comm v retainedBasisThree
      hv.continuous contDiff_retainedBasisThree.continuous,
    fourCellOddCoreLocalBilinear_comm v retainedBasisFive
      hv.continuous contDiff_retainedBasisFive.continuous,
    fourCellOddCoreLocalBilinear_comm v retainedBasisSeven
      hv.continuous contDiff_retainedBasisSeven.continuous,
    fourCellOddCoreLocalBilinear_comm v retainedBasisNine
      hv.continuous contDiff_retainedBasisNine.continuous]

private theorem fourCellOddP11GalerkinRetainedGram_mulVec
    (x : Fin 4 → ℝ) :
    fourCellOddP11GalerkinRetainedGram *ᵥ x =
      ![fourCellOddCoreLocalBilinear retainedBasisThree
          (fourCellOddP11GalerkinRetainedProfile x),
        fourCellOddCoreLocalBilinear retainedBasisFive
          (fourCellOddP11GalerkinRetainedProfile x),
        fourCellOddCoreLocalBilinear retainedBasisSeven
          (fourCellOddP11GalerkinRetainedProfile x),
        fourCellOddCoreLocalBilinear retainedBasisNine
          (fourCellOddP11GalerkinRetainedProfile x)] := by
  funext i
  fin_cases i
  · rw [fourCellOddCoreLocalBilinear_retainedProfile_right
      retainedBasisThree contDiff_retainedBasisThree
        odd_retainedBasisThree x]
    simp [fourCellOddP11GalerkinRetainedGram, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring
  · rw [fourCellOddCoreLocalBilinear_retainedProfile_right
      retainedBasisFive contDiff_retainedBasisFive odd_retainedBasisFive x]
    simp [fourCellOddP11GalerkinRetainedGram, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring
  · rw [fourCellOddCoreLocalBilinear_retainedProfile_right
      retainedBasisSeven contDiff_retainedBasisSeven
        odd_retainedBasisSeven x]
    simp [fourCellOddP11GalerkinRetainedGram, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring
  · rw [fourCellOddCoreLocalBilinear_retainedProfile_right
      retainedBasisNine contDiff_retainedBasisNine odd_retainedBasisNine x]
    simp [fourCellOddP11GalerkinRetainedGram, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring

/-- The retained Gram operator has trivial kernel, by strict positivity of
the actual core form on the retained subspace. -/
theorem fourCellOddP11GalerkinRetainedGram_kernel
    (x : Fin 4 → ℝ)
    (hx : fourCellOddP11GalerkinRetainedGram *ᵥ x = 0) :
    x = 0 := by
  have hrows := fourCellOddP11GalerkinRetainedGram_mulVec x
  rw [hx] at hrows
  have h₃ : fourCellOddCoreLocalBilinear retainedBasisThree
      (fourCellOddP11GalerkinRetainedProfile x) = 0 := by
    have := congrFun hrows 0
    simpa using this.symm
  have h₅ : fourCellOddCoreLocalBilinear retainedBasisFive
      (fourCellOddP11GalerkinRetainedProfile x) = 0 := by
    have := congrFun hrows 1
    simpa using this.symm
  have h₇ : fourCellOddCoreLocalBilinear retainedBasisSeven
      (fourCellOddP11GalerkinRetainedProfile x) = 0 := by
    have := congrFun hrows 2
    simpa using this.symm
  have h₉ : fourCellOddCoreLocalBilinear retainedBasisNine
      (fourCellOddP11GalerkinRetainedProfile x) = 0 := by
    have := congrFun hrows 3
    simpa using this.symm
  have hself : fourCellOddCoreLocalBilinear
      (fourCellOddP11GalerkinRetainedProfile x)
      (fourCellOddP11GalerkinRetainedProfile x) = 0 := by
    rw [fourCellOddCoreLocalBilinear_retainedProfile_left x
      (fourCellOddP11GalerkinRetainedProfile x)
      (contDiff_fourCellOddP11GalerkinRetainedProfile x)
      (odd_fourCellOddP11GalerkinRetainedProfile x), h₃, h₅, h₇, h₉]
    ring
  by_contra hxzero
  have hcoeff :
      (![0, x 0, x 1, x 2, x 3] : Fin 5 → ℝ) ≠ 0 := by
    intro hzero
    apply hxzero
    funext i
    fin_cases i
    · have hi := congrFun hzero 1
      simpa using hi
    · have hi := congrFun hzero 2
      simpa using hi
    · have hi := congrFun hzero 3
      simpa using hi
    · have hi := congrFun hzero 4
      simpa using hi
  have hpos := fourCellOddCoreLocalQuadratic_fiveMode_pos
    0 (x 0) (x 1) (x 2) (x 3) hcoeff
  have hdiag := fourCellOddCoreLocalBilinear_self_eq_quadratic
    (fourCellOddP11GalerkinRetainedProfile x)
    (contDiff_fourCellOddP11GalerkinRetainedProfile x)
    (odd_fourCellOddP11GalerkinRetainedProfile x)
  change 0 < fourCellOddCoreLocalQuadratic
    (fourCellOddP11GalerkinRetainedProfile x) at hpos
  rw [hself] at hdiag
  linarith

/-- The exact retained core Gram matrix is nonsingular. -/
theorem fourCellOddP11GalerkinRetainedGram_isUnit :
    IsUnit fourCellOddP11GalerkinRetainedGram := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hsub : fourCellOddP11GalerkinRetainedGram *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp
    (fourCellOddP11GalerkinRetainedGram_kernel (x - y) hsub)

private theorem fourCellOddP11GalerkinRetainedGram_det_isUnit :
    IsUnit fourCellOddP11GalerkinRetainedGram.det :=
  fourCellOddP11GalerkinRetainedGram.isUnit_iff_isUnit_det.mp
    fourCellOddP11GalerkinRetainedGram_isUnit

/-- The exact inverse-defined coefficient vector solving the finite normal
equations. -/
def fourCellOddP11GalerkinRetainedSolution : Fin 4 → ℝ :=
  fourCellOddP11GalerkinRetainedGram⁻¹ *ᵥ
    fourCellOddP11GalerkinRetainedRhs

theorem fourCellOddP11GalerkinRetainedSolution_normalEquation :
    fourCellOddP11GalerkinRetainedGram *ᵥ
        fourCellOddP11GalerkinRetainedSolution =
      fourCellOddP11GalerkinRetainedRhs := by
  unfold fourCellOddP11GalerkinRetainedSolution
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv fourCellOddP11GalerkinRetainedGram
      fourCellOddP11GalerkinRetainedGram_det_isUnit,
    Matrix.one_mulVec]

private theorem contDiff_centeredP1_local : ContDiff ℝ 1 centeredP1 := by
  unfold centeredP1
  fun_prop

private theorem odd_centeredP1_local : Function.Odd centeredP1 := by
  intro x
  unfold centeredP1
  ring

/-- The four inverse-defined normal equations imply the normal equation
against every retained profile. -/
theorem fourCellOddP11GalerkinRetainedSolution_normal
    (y : Fin 4 → ℝ) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP11GalerkinRetainedProfile
          fourCellOddP11GalerkinRetainedSolution)
        (fourCellOddP11GalerkinRetainedProfile y) =
      fourCellOddCoreLocalBilinear centeredP1
        (fourCellOddP11GalerkinRetainedProfile y) := by
  let h := fourCellOddP11GalerkinRetainedProfile
    fourCellOddP11GalerkinRetainedSolution
  have hh : ContDiff ℝ 1 h :=
    contDiff_fourCellOddP11GalerkinRetainedProfile _
  have hhodd : Function.Odd h :=
    odd_fourCellOddP11GalerkinRetainedProfile _
  have hrows :=
    (fourCellOddP11GalerkinRetainedGram_mulVec
      fourCellOddP11GalerkinRetainedSolution).symm.trans
      fourCellOddP11GalerkinRetainedSolution_normalEquation
  have h₃ : fourCellOddCoreLocalBilinear retainedBasisThree h =
      fourCellOddCoreLocalBilinear retainedBasisThree centeredP1 := by
    have hi := congrFun hrows 0
    simpa only [h, fourCellOddP11GalerkinRetainedRhs] using hi
  have h₅ : fourCellOddCoreLocalBilinear retainedBasisFive h =
      fourCellOddCoreLocalBilinear retainedBasisFive centeredP1 := by
    have hi := congrFun hrows 1
    simpa only [h, fourCellOddP11GalerkinRetainedRhs] using hi
  have h₇ : fourCellOddCoreLocalBilinear retainedBasisSeven h =
      fourCellOddCoreLocalBilinear retainedBasisSeven centeredP1 := by
    have hi := congrFun hrows 2
    simpa only [h, fourCellOddP11GalerkinRetainedRhs] using hi
  have h₉ : fourCellOddCoreLocalBilinear retainedBasisNine h =
      fourCellOddCoreLocalBilinear retainedBasisNine centeredP1 := by
    have hi := congrFun hrows 3
    simpa only [h, fourCellOddP11GalerkinRetainedRhs] using hi
  have h₃' : fourCellOddCoreLocalBilinear h retainedBasisThree =
      fourCellOddCoreLocalBilinear centeredP1 retainedBasisThree := by
    rw [fourCellOddCoreLocalBilinear_comm h retainedBasisThree
        hh.continuous contDiff_retainedBasisThree.continuous,
      fourCellOddCoreLocalBilinear_comm centeredP1 retainedBasisThree
        contDiff_centeredP1_local.continuous
          contDiff_retainedBasisThree.continuous]
    exact h₃
  have h₅' : fourCellOddCoreLocalBilinear h retainedBasisFive =
      fourCellOddCoreLocalBilinear centeredP1 retainedBasisFive := by
    rw [fourCellOddCoreLocalBilinear_comm h retainedBasisFive
        hh.continuous contDiff_retainedBasisFive.continuous,
      fourCellOddCoreLocalBilinear_comm centeredP1 retainedBasisFive
        contDiff_centeredP1_local.continuous
          contDiff_retainedBasisFive.continuous]
    exact h₅
  have h₇' : fourCellOddCoreLocalBilinear h retainedBasisSeven =
      fourCellOddCoreLocalBilinear centeredP1 retainedBasisSeven := by
    rw [fourCellOddCoreLocalBilinear_comm h retainedBasisSeven
        hh.continuous contDiff_retainedBasisSeven.continuous,
      fourCellOddCoreLocalBilinear_comm centeredP1 retainedBasisSeven
        contDiff_centeredP1_local.continuous
          contDiff_retainedBasisSeven.continuous]
    exact h₇
  have h₉' : fourCellOddCoreLocalBilinear h retainedBasisNine =
      fourCellOddCoreLocalBilinear centeredP1 retainedBasisNine := by
    rw [fourCellOddCoreLocalBilinear_comm h retainedBasisNine
        hh.continuous contDiff_retainedBasisNine.continuous,
      fourCellOddCoreLocalBilinear_comm centeredP1 retainedBasisNine
        contDiff_centeredP1_local.continuous
          contDiff_retainedBasisNine.continuous]
    exact h₉
  change fourCellOddCoreLocalBilinear h
      (fourCellOddP11GalerkinRetainedProfile y) = _
  rw [fourCellOddCoreLocalBilinear_retainedProfile_right h hh hhodd y,
    fourCellOddCoreLocalBilinear_retainedProfile_right centeredP1
      contDiff_centeredP1_local odd_centeredP1_local y,
    h₃', h₅', h₇', h₉']

/-- The inverse-defined finite projection makes `P₁ - h` exactly
core-orthogonal to the complete retained `P₃/P₅/P₇/P₉` space. -/
theorem fourCellOddP11GalerkinRetainedSolution_orthogonal :
    FourCellOddP11GalerkinFiniteOrthogonal
      (fourCellOddP11GalerkinRetainedSolution 0)
      (fourCellOddP11GalerkinRetainedSolution 1)
      (fourCellOddP11GalerkinRetainedSolution 2)
      (fourCellOddP11GalerkinRetainedSolution 3) := by
  intro d e f g
  let y : Fin 4 → ℝ := ![d, e, f, g]
  let h := fourCellOddP11GalerkinRetainedProfile
    fourCellOddP11GalerkinRetainedSolution
  let p := fourCellOddP11GalerkinRetainedProfile y
  have hh : ContDiff ℝ 1 h :=
    contDiff_fourCellOddP11GalerkinRetainedProfile _
  have hhodd : Function.Odd h :=
    odd_fourCellOddP11GalerkinRetainedProfile _
  have hp : ContDiff ℝ 1 p :=
    contDiff_fourCellOddP11GalerkinRetainedProfile _
  have hpodd : Function.Odd p :=
    odd_fourCellOddP11GalerkinRetainedProfile _
  have hnormal := fourCellOddP11GalerkinRetainedSolution_normal y
  have hresidual :
      fourCellOddP11GalerkinResidualProfile
          (fourCellOddP11GalerkinRetainedSolution 0)
          (fourCellOddP11GalerkinRetainedSolution 1)
          (fourCellOddP11GalerkinRetainedSolution 2)
          (fourCellOddP11GalerkinRetainedSolution 3) =
        centeredP1 + fun x ↦ (-1 : ℝ) * h x := by
    funext x
    dsimp only [h, fourCellOddP11GalerkinRetainedProfile]
    unfold fourCellOddP11GalerkinResidualProfile
      fourCellOddP11GalerkinLowProfile
    simp only [Pi.add_apply]
    ring
  change fourCellOddCoreLocalBilinear
    (fourCellOddP11GalerkinResidualProfile
      (fourCellOddP11GalerkinRetainedSolution 0)
      (fourCellOddP11GalerkinRetainedSolution 1)
      (fourCellOddP11GalerkinRetainedSolution 2)
      (fourCellOddP11GalerkinRetainedSolution 3)) p = 0
  rw [hresidual,
    fourCellOddCoreLocalBilinear_add_left centeredP1
      (fun x ↦ (-1 : ℝ) * h x) p
      contDiff_centeredP1_local (contDiff_const.mul hh) hp
      odd_centeredP1_local (odd_const_mul hhodd (-1)) hpodd,
    fourCellOddCoreLocalBilinear_const_mul_left h p hh hp hhodd hpodd (-1)]
  change fourCellOddCoreLocalBilinear h p =
    fourCellOddCoreLocalBilinear centeredP1 p at hnormal
  rw [hnormal]
  ring

/-- Existence of an exact finite Galerkin projection. -/
theorem exists_fourCellOddP11GalerkinFiniteOrthogonal :
    ∃ a₃ a₅ a₇ a₉ : ℝ,
      FourCellOddP11GalerkinFiniteOrthogonal a₃ a₅ a₇ a₉ := by
  exact ⟨fourCellOddP11GalerkinRetainedSolution 0,
    fourCellOddP11GalerkinRetainedSolution 1,
    fourCellOddP11GalerkinRetainedSolution 2,
    fourCellOddP11GalerkinRetainedSolution 3,
    fourCellOddP11GalerkinRetainedSolution_orthogonal⟩

/-- Every Galerkin residual has strictly positive core quadratic.  This is
stronger than needed for the finite solve and follows because its `P₁`
coefficient is exactly one. -/
theorem fourCellOddP11GalerkinResidualProfile_core_pos
    (a₃ a₅ a₇ a₉ : ℝ) :
    0 < fourCellOddCoreLocalQuadratic
      (fourCellOddP11GalerkinResidualProfile a₃ a₅ a₇ a₉) := by
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
  apply fourCellOddCoreLocalQuadratic_fiveMode_pos
  intro hzero
  have hfirst := congrFun hzero 0
  norm_num at hfirst

/-- The exact finite solution has a strictly positive residual pivot. -/
theorem fourCellOddP11GalerkinRetainedSolution_residual_core_pos :
    0 < fourCellOddCoreLocalQuadratic
      (fourCellOddP11GalerkinResidualProfile
        (fourCellOddP11GalerkinRetainedSolution 0)
        (fourCellOddP11GalerkinRetainedSolution 1)
        (fourCellOddP11GalerkinRetainedSolution 2)
        (fourCellOddP11GalerkinRetainedSolution 3)) :=
  fourCellOddP11GalerkinResidualProfile_core_pos _ _ _ _

/-- Combined finite certificate: exact Galerkin orthogonality and a strictly
positive residual quadratic. -/
theorem exists_fourCellOddP11GalerkinFiniteOrthogonal_and_core_pos :
    ∃ a₃ a₅ a₇ a₉ : ℝ,
      FourCellOddP11GalerkinFiniteOrthogonal a₃ a₅ a₇ a₉ ∧
        0 < fourCellOddCoreLocalQuadratic
          (fourCellOddP11GalerkinResidualProfile a₃ a₅ a₇ a₉) := by
  exact ⟨fourCellOddP11GalerkinRetainedSolution 0,
    fourCellOddP11GalerkinRetainedSolution 1,
    fourCellOddP11GalerkinRetainedSolution 2,
    fourCellOddP11GalerkinRetainedSolution 3,
    fourCellOddP11GalerkinRetainedSolution_orthogonal,
    fourCellOddP11GalerkinRetainedSolution_residual_core_pos⟩

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinFiniteSolveStructural
