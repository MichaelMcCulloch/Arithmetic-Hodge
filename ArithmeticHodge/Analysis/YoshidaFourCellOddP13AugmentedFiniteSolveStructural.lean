import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

open MeasureTheory Polynomial Real Set Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedFiniteSolveStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddFiveModeStrictCoercivityStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddP13AugmentedDecompositionStructural
open YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Exact finite solve after retaining `P11`

The augmented `P3/P5/P7/P9/P11` Gram is nonsingular for structural reasons:
every vector in this block is `P1`-orthogonal, and the actual odd core is
coercive there.  Its inverse therefore gives the exact five-coordinate
Galerkin projection.  No determinant expansion or entry enumeration is
needed.
-/

/-- A coefficient vector interpreted in the enlarged retained block. -/
def fourCellOddP13AugmentedRetainedProfile
    (x : Fin 5 → ℝ) : ℝ → ℝ :=
  fourCellOddP11AugmentedLowProfile (x 0) (x 1) (x 2) (x 3) (x 4)

private def augmentedRetainedPolynomial (x : Fin 5 → ℝ) : ℝ[X] :=
  x 0 • ((1 / 2 : ℝ) • ((5 : ℝ) • Polynomial.X ^ 3 - (3 : ℝ) • Polynomial.X)) +
    x 1 • ((1 / 8 : ℝ) •
      ((63 : ℝ) • Polynomial.X ^ 5 - (70 : ℝ) • Polynomial.X ^ 3 +
        (15 : ℝ) • Polynomial.X)) +
    x 2 • ((1 / 16 : ℝ) •
      ((429 : ℝ) • Polynomial.X ^ 7 - (693 : ℝ) • Polynomial.X ^ 5 +
        (315 : ℝ) • Polynomial.X ^ 3 - (35 : ℝ) • Polynomial.X)) +
    x 3 • ((1 / 128 : ℝ) •
      ((12155 : ℝ) • Polynomial.X ^ 9 - (25740 : ℝ) • Polynomial.X ^ 7 +
        (18018 : ℝ) • Polynomial.X ^ 5 - (4620 : ℝ) • Polynomial.X ^ 3 +
          (315 : ℝ) • Polynomial.X)) +
    x 4 • ((1 / 256 : ℝ) •
      ((88179 : ℝ) • Polynomial.X ^ 11 - (230945 : ℝ) • Polynomial.X ^ 9 +
        (218790 : ℝ) • Polynomial.X ^ 7 - (90090 : ℝ) • Polynomial.X ^ 5 +
          (15015 : ℝ) • Polynomial.X ^ 3 - (693 : ℝ) • Polynomial.X))

private theorem fourCellOddP11DirectTail_eq_monomials (t : ℝ) :
    fourCellOddP11DirectTail t =
      (88179 * t ^ 11 - 230945 * t ^ 9 + 218790 * t ^ 7 -
        90090 * t ^ 5 + 15015 * t ^ 3 - 693 * t) / 256 := by
  unfold fourCellOddP11DirectTail
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, Polynomial.smul_eq_C_mul]
  ring

private theorem augmentedRetainedPolynomial_eval
    (x : Fin 5 → ℝ) (t : ℝ) :
    (augmentedRetainedPolynomial x).eval t =
      fourCellOddP13AugmentedRetainedProfile x t := by
  unfold augmentedRetainedPolynomial fourCellOddP13AugmentedRetainedProfile
    fourCellOddP11AugmentedLowProfile
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP3 factorTwoCenteredP5
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    Polynomial.eval_pow, Polynomial.eval_X, smul_eq_mul]
  rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq,
    fourCellOddP11DirectTail_eq_monomials]
  ring

private theorem augmentedRetainedProfile_eq_zero_coefficients
    (x : Fin 5 → ℝ)
    (hx : fourCellOddP13AugmentedRetainedProfile x = 0) :
    x = 0 := by
  have hp : augmentedRetainedPolynomial x = 0 := by
    apply Polynomial.funext
    intro t
    rw [augmentedRetainedPolynomial_eval]
    rw [hx]
    simp
  have h11 := congrArg (fun p : ℝ[X] ↦ p.coeff 11) hp
  have h9 := congrArg (fun p : ℝ[X] ↦ p.coeff 9) hp
  have h7 := congrArg (fun p : ℝ[X] ↦ p.coeff 7) hp
  have h5 := congrArg (fun p : ℝ[X] ↦ p.coeff 5) hp
  have h3 := congrArg (fun p : ℝ[X] ↦ p.coeff 3) hp
  norm_num [augmentedRetainedPolynomial, Polynomial.coeff_X] at h11 h9 h7 h5 h3
  have hx4 : x 4 = 0 := by linarith
  have hx3 : x 3 = 0 := by linarith
  have hx2 : x 2 = 0 := by linarith
  have hx1 : x 1 = 0 := by linarith
  have hx0 : x 0 = 0 := by linarith
  funext i
  fin_cases i <;> simp [hx0, hx1, hx2, hx3, hx4]

/-- Exact Pythagorean split between the old retained block and `P11`. -/
theorem integral_zero_one_fourCellOddP13AugmentedRetainedProfile_sq
    (x : Fin 5 → ℝ) :
    (∫ t : ℝ in 0..1, fourCellOddP13AugmentedRetainedProfile x t ^ 2) =
      (∫ t : ℝ in 0..1,
        fourCellOddOneThreeFiveSevenNineLowProfile
          0 (x 0) (x 1) (x 2) (x 3) t ^ 2) + (x 4) ^ 2 / 23 := by
  let u := fourCellOddOneThreeFiveSevenNineLowProfile
    0 (x 0) (x 1) (x 2) (x 3)
  let p := fourCellOddP11DirectTail
  have hu : Continuous u :=
    (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
      0 (x 0) (x 1) (x 2) (x 3)).continuous
  have hp : Continuous p := contDiff_fourCellOddP11DirectTail.continuous
  rcases fourCellOddP11DirectTail_moments with ⟨h1, h3, h5, h7, h9⟩
  have hcross : (∫ t : ℝ in 0..1, u t * p t) = 0 := by
    dsimp only [u, p]
    exact integral_zero_one_fiveMode_mul_P11Plus_eq_zero
      fourCellOddP11DirectTail hp odd_fourCellOddP11DirectTail
      h1 h3 h5 h7 h9 0 (x 0) (x 1) (x 2) (x 3)
  have huuI : IntervalIntegrable (fun t : ℝ ↦ u t ^ 2) volume 0 1 :=
    (hu.pow 2).intervalIntegrable _ _
  have hupI : IntervalIntegrable (fun t : ℝ ↦ u t * p t) volume 0 1 :=
    (hu.mul hp).intervalIntegrable _ _
  have hppI : IntervalIntegrable (fun t : ℝ ↦ p t ^ 2) volume 0 1 :=
    (hp.pow 2).intervalIntegrable _ _
  change (∫ t : ℝ in 0..1, (u t + x 4 * p t) ^ 2) = _
  rw [show (fun t : ℝ ↦ (u t + x 4 * p t) ^ 2) =
      fun t ↦ u t ^ 2 + 2 * x 4 * (u t * p t) + (x 4) ^ 2 * p t ^ 2 by
    funext t
    ring,
    intervalIntegral.integral_add
      (huuI.add (hupI.const_mul _)) (hppI.const_mul _),
    intervalIntegral.integral_add huuI (hupI.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    hcross, integral_zero_one_fourCellOddP11DirectTail_sq]
  dsimp only [u]
  ring

private def retainedBasisThree : ℝ → ℝ :=
  fourCellOddP11AugmentedLowProfile 1 0 0 0 0

private def retainedBasisFive : ℝ → ℝ :=
  fourCellOddP11AugmentedLowProfile 0 1 0 0 0

private def retainedBasisSeven : ℝ → ℝ :=
  fourCellOddP11AugmentedLowProfile 0 0 1 0 0

private def retainedBasisNine : ℝ → ℝ :=
  fourCellOddP11AugmentedLowProfile 0 0 0 1 0

private def retainedBasisEleven : ℝ → ℝ :=
  fourCellOddP11AugmentedLowProfile 0 0 0 0 1

/-- Exact core Gram of the enlarged retained block. -/
def fourCellOddP13AugmentedRetainedGram : Matrix (Fin 5) (Fin 5) ℝ :=
  !![fourCellOddCoreLocalBilinear retainedBasisThree retainedBasisThree,
      fourCellOddCoreLocalBilinear retainedBasisThree retainedBasisFive,
      fourCellOddCoreLocalBilinear retainedBasisThree retainedBasisSeven,
      fourCellOddCoreLocalBilinear retainedBasisThree retainedBasisNine,
      fourCellOddCoreLocalBilinear retainedBasisThree retainedBasisEleven;
    fourCellOddCoreLocalBilinear retainedBasisFive retainedBasisThree,
      fourCellOddCoreLocalBilinear retainedBasisFive retainedBasisFive,
      fourCellOddCoreLocalBilinear retainedBasisFive retainedBasisSeven,
      fourCellOddCoreLocalBilinear retainedBasisFive retainedBasisNine,
      fourCellOddCoreLocalBilinear retainedBasisFive retainedBasisEleven;
    fourCellOddCoreLocalBilinear retainedBasisSeven retainedBasisThree,
      fourCellOddCoreLocalBilinear retainedBasisSeven retainedBasisFive,
      fourCellOddCoreLocalBilinear retainedBasisSeven retainedBasisSeven,
      fourCellOddCoreLocalBilinear retainedBasisSeven retainedBasisNine,
      fourCellOddCoreLocalBilinear retainedBasisSeven retainedBasisEleven;
    fourCellOddCoreLocalBilinear retainedBasisNine retainedBasisThree,
      fourCellOddCoreLocalBilinear retainedBasisNine retainedBasisFive,
      fourCellOddCoreLocalBilinear retainedBasisNine retainedBasisSeven,
      fourCellOddCoreLocalBilinear retainedBasisNine retainedBasisNine,
      fourCellOddCoreLocalBilinear retainedBasisNine retainedBasisEleven;
    fourCellOddCoreLocalBilinear retainedBasisEleven retainedBasisThree,
      fourCellOddCoreLocalBilinear retainedBasisEleven retainedBasisFive,
      fourCellOddCoreLocalBilinear retainedBasisEleven retainedBasisSeven,
      fourCellOddCoreLocalBilinear retainedBasisEleven retainedBasisNine,
      fourCellOddCoreLocalBilinear retainedBasisEleven retainedBasisEleven]

/-- Exact `P1` mixed row in enlarged retained coordinates. -/
def fourCellOddP13AugmentedRetainedRhs : Fin 5 → ℝ :=
  ![fourCellOddCoreLocalBilinear retainedBasisThree centeredP1,
    fourCellOddCoreLocalBilinear retainedBasisFive centeredP1,
    fourCellOddCoreLocalBilinear retainedBasisSeven centeredP1,
    fourCellOddCoreLocalBilinear retainedBasisNine centeredP1,
    fourCellOddCoreLocalBilinear retainedBasisEleven centeredP1]

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

private theorem contDiff_retainedBasisThree :
    ContDiff ℝ 1 retainedBasisThree :=
  contDiff_fourCellOddP11AugmentedLowProfile 1 0 0 0 0

private theorem contDiff_retainedBasisFive :
    ContDiff ℝ 1 retainedBasisFive :=
  contDiff_fourCellOddP11AugmentedLowProfile 0 1 0 0 0

private theorem contDiff_retainedBasisSeven :
    ContDiff ℝ 1 retainedBasisSeven :=
  contDiff_fourCellOddP11AugmentedLowProfile 0 0 1 0 0

private theorem contDiff_retainedBasisNine :
    ContDiff ℝ 1 retainedBasisNine :=
  contDiff_fourCellOddP11AugmentedLowProfile 0 0 0 1 0

private theorem contDiff_retainedBasisEleven :
    ContDiff ℝ 1 retainedBasisEleven :=
  contDiff_fourCellOddP11AugmentedLowProfile 0 0 0 0 1

private theorem odd_retainedBasisThree : Function.Odd retainedBasisThree :=
  odd_fourCellOddP11AugmentedLowProfile 1 0 0 0 0

private theorem odd_retainedBasisFive : Function.Odd retainedBasisFive :=
  odd_fourCellOddP11AugmentedLowProfile 0 1 0 0 0

private theorem odd_retainedBasisSeven : Function.Odd retainedBasisSeven :=
  odd_fourCellOddP11AugmentedLowProfile 0 0 1 0 0

private theorem odd_retainedBasisNine : Function.Odd retainedBasisNine :=
  odd_fourCellOddP11AugmentedLowProfile 0 0 0 1 0

private theorem odd_retainedBasisEleven : Function.Odd retainedBasisEleven :=
  odd_fourCellOddP11AugmentedLowProfile 0 0 0 0 1

private theorem contDiff_fourCellOddP13AugmentedRetainedProfile
    (x : Fin 5 → ℝ) :
    ContDiff ℝ 1 (fourCellOddP13AugmentedRetainedProfile x) :=
  contDiff_fourCellOddP11AugmentedLowProfile
    (x 0) (x 1) (x 2) (x 3) (x 4)

private theorem odd_fourCellOddP13AugmentedRetainedProfile
    (x : Fin 5 → ℝ) :
    Function.Odd (fourCellOddP13AugmentedRetainedProfile x) :=
  odd_fourCellOddP11AugmentedLowProfile
    (x 0) (x 1) (x 2) (x 3) (x 4)

private theorem fourCellOddP13AugmentedRetainedProfile_decompose
    (x : Fin 5 → ℝ) :
    fourCellOddP13AugmentedRetainedProfile x =
      (((fun t ↦ x 0 * retainedBasisThree t) +
        (fun t ↦ x 1 * retainedBasisFive t)) +
        (fun t ↦ x 2 * retainedBasisSeven t) +
        (fun t ↦ x 3 * retainedBasisNine t)) +
        (fun t ↦ x 4 * retainedBasisEleven t) := by
  funext t
  unfold fourCellOddP13AugmentedRetainedProfile
    retainedBasisThree retainedBasisFive retainedBasisSeven retainedBasisNine
    retainedBasisEleven fourCellOddP11AugmentedLowProfile
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp only [Pi.add_apply]
  ring

private theorem fourCellOddCoreLocalBilinear_retainedProfile_right
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (huodd : Function.Odd u)
    (x : Fin 5 → ℝ) :
    fourCellOddCoreLocalBilinear u
        (fourCellOddP13AugmentedRetainedProfile x) =
      x 0 * fourCellOddCoreLocalBilinear u retainedBasisThree +
      x 1 * fourCellOddCoreLocalBilinear u retainedBasisFive +
      x 2 * fourCellOddCoreLocalBilinear u retainedBasisSeven +
      x 3 * fourCellOddCoreLocalBilinear u retainedBasisNine +
      x 4 * fourCellOddCoreLocalBilinear u retainedBasisEleven := by
  let v3 : ℝ → ℝ := fun t ↦ x 0 * retainedBasisThree t
  let v5 : ℝ → ℝ := fun t ↦ x 1 * retainedBasisFive t
  let v7 : ℝ → ℝ := fun t ↦ x 2 * retainedBasisSeven t
  let v9 : ℝ → ℝ := fun t ↦ x 3 * retainedBasisNine t
  let v11 : ℝ → ℝ := fun t ↦ x 4 * retainedBasisEleven t
  have hv3 : ContDiff ℝ 1 v3 := contDiff_const.mul contDiff_retainedBasisThree
  have hv5 : ContDiff ℝ 1 v5 := contDiff_const.mul contDiff_retainedBasisFive
  have hv7 : ContDiff ℝ 1 v7 := contDiff_const.mul contDiff_retainedBasisSeven
  have hv9 : ContDiff ℝ 1 v9 := contDiff_const.mul contDiff_retainedBasisNine
  have hv11 : ContDiff ℝ 1 v11 := contDiff_const.mul contDiff_retainedBasisEleven
  have hv3odd : Function.Odd v3 := odd_const_mul odd_retainedBasisThree (x 0)
  have hv5odd : Function.Odd v5 := odd_const_mul odd_retainedBasisFive (x 1)
  have hv7odd : Function.Odd v7 := odd_const_mul odd_retainedBasisSeven (x 2)
  have hv9odd : Function.Odd v9 := odd_const_mul odd_retainedBasisNine (x 3)
  have hv11odd : Function.Odd v11 := odd_const_mul odd_retainedBasisEleven (x 4)
  rw [fourCellOddP13AugmentedRetainedProfile_decompose]
  change fourCellOddCoreLocalBilinear u ((((v3 + v5) + v7) + v9) + v11) = _
  rw [fourCellOddCoreLocalBilinear_add_right u (((v3 + v5) + v7) + v9) v11
      hu (((hv3.add hv5).add hv7).add hv9) hv11 huodd
      (((hv3odd.add hv5odd).add hv7odd).add hv9odd) hv11odd,
    fourCellOddCoreLocalBilinear_add_right u ((v3 + v5) + v7) v9
      hu ((hv3.add hv5).add hv7) hv9 huodd
      ((hv3odd.add hv5odd).add hv7odd) hv9odd,
    fourCellOddCoreLocalBilinear_add_right u (v3 + v5) v7
      hu (hv3.add hv5) hv7 huodd (hv3odd.add hv5odd) hv7odd,
    fourCellOddCoreLocalBilinear_add_right u v3 v5
      hu hv3 hv5 huodd hv3odd hv5odd]
  dsimp only [v3, v5, v7, v9, v11]
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
        huodd odd_retainedBasisNine (x 3),
    fourCellOddCoreLocalBilinear_const_mul_right
      u retainedBasisEleven hu contDiff_retainedBasisEleven
        huodd odd_retainedBasisEleven (x 4)]

private theorem fourCellOddCoreLocalBilinear_retainedProfile_left
    (x : Fin 5 → ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 1 v) (hvodd : Function.Odd v) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP13AugmentedRetainedProfile x) v =
      x 0 * fourCellOddCoreLocalBilinear retainedBasisThree v +
      x 1 * fourCellOddCoreLocalBilinear retainedBasisFive v +
      x 2 * fourCellOddCoreLocalBilinear retainedBasisSeven v +
      x 3 * fourCellOddCoreLocalBilinear retainedBasisNine v +
      x 4 * fourCellOddCoreLocalBilinear retainedBasisEleven v := by
  rw [fourCellOddCoreLocalBilinear_comm
      (fourCellOddP13AugmentedRetainedProfile x) v
      (contDiff_fourCellOddP13AugmentedRetainedProfile x).continuous hv.continuous,
    fourCellOddCoreLocalBilinear_retainedProfile_right v hv hvodd x,
    fourCellOddCoreLocalBilinear_comm v retainedBasisThree
      hv.continuous contDiff_retainedBasisThree.continuous,
    fourCellOddCoreLocalBilinear_comm v retainedBasisFive
      hv.continuous contDiff_retainedBasisFive.continuous,
    fourCellOddCoreLocalBilinear_comm v retainedBasisSeven
      hv.continuous contDiff_retainedBasisSeven.continuous,
    fourCellOddCoreLocalBilinear_comm v retainedBasisNine
      hv.continuous contDiff_retainedBasisNine.continuous,
    fourCellOddCoreLocalBilinear_comm v retainedBasisEleven
      hv.continuous contDiff_retainedBasisEleven.continuous]

private theorem fourCellOddP13AugmentedRetainedGram_mulVec
    (x : Fin 5 → ℝ) :
    fourCellOddP13AugmentedRetainedGram *ᵥ x =
      ![fourCellOddCoreLocalBilinear retainedBasisThree
          (fourCellOddP13AugmentedRetainedProfile x),
        fourCellOddCoreLocalBilinear retainedBasisFive
          (fourCellOddP13AugmentedRetainedProfile x),
        fourCellOddCoreLocalBilinear retainedBasisSeven
          (fourCellOddP13AugmentedRetainedProfile x),
        fourCellOddCoreLocalBilinear retainedBasisNine
          (fourCellOddP13AugmentedRetainedProfile x),
        fourCellOddCoreLocalBilinear retainedBasisEleven
          (fourCellOddP13AugmentedRetainedProfile x)] := by
  funext i
  fin_cases i
  · rw [fourCellOddCoreLocalBilinear_retainedProfile_right
      retainedBasisThree contDiff_retainedBasisThree odd_retainedBasisThree x]
    simp [fourCellOddP13AugmentedRetainedGram, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring
  · rw [fourCellOddCoreLocalBilinear_retainedProfile_right
      retainedBasisFive contDiff_retainedBasisFive odd_retainedBasisFive x]
    simp [fourCellOddP13AugmentedRetainedGram, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring
  · rw [fourCellOddCoreLocalBilinear_retainedProfile_right
      retainedBasisSeven contDiff_retainedBasisSeven odd_retainedBasisSeven x]
    simp [fourCellOddP13AugmentedRetainedGram, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring
  · rw [fourCellOddCoreLocalBilinear_retainedProfile_right
      retainedBasisNine contDiff_retainedBasisNine odd_retainedBasisNine x]
    simp [fourCellOddP13AugmentedRetainedGram, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring
  · rw [fourCellOddCoreLocalBilinear_retainedProfile_right
      retainedBasisEleven contDiff_retainedBasisEleven
        odd_retainedBasisEleven x]
    simp [fourCellOddP13AugmentedRetainedGram, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring

/-- The enlarged retained Gram has trivial kernel by actual-core coercivity. -/
theorem fourCellOddP13AugmentedRetainedGram_kernel
    (x : Fin 5 → ℝ)
    (hx : fourCellOddP13AugmentedRetainedGram *ᵥ x = 0) :
    x = 0 := by
  have hrows := fourCellOddP13AugmentedRetainedGram_mulVec x
  rw [hx] at hrows
  have h3 : fourCellOddCoreLocalBilinear retainedBasisThree
      (fourCellOddP13AugmentedRetainedProfile x) = 0 := by
    have h := congrFun hrows 0
    simpa using h.symm
  have h5 : fourCellOddCoreLocalBilinear retainedBasisFive
      (fourCellOddP13AugmentedRetainedProfile x) = 0 := by
    have h := congrFun hrows 1
    simpa using h.symm
  have h7 : fourCellOddCoreLocalBilinear retainedBasisSeven
      (fourCellOddP13AugmentedRetainedProfile x) = 0 := by
    have h := congrFun hrows 2
    simpa using h.symm
  have h9 : fourCellOddCoreLocalBilinear retainedBasisNine
      (fourCellOddP13AugmentedRetainedProfile x) = 0 := by
    have h := congrFun hrows 3
    simpa using h.symm
  have h11 : fourCellOddCoreLocalBilinear retainedBasisEleven
      (fourCellOddP13AugmentedRetainedProfile x) = 0 := by
    have h := congrFun hrows 4
    simpa using h.symm
  have hself : fourCellOddCoreLocalBilinear
      (fourCellOddP13AugmentedRetainedProfile x)
      (fourCellOddP13AugmentedRetainedProfile x) = 0 := by
    rw [fourCellOddCoreLocalBilinear_retainedProfile_left x
      (fourCellOddP13AugmentedRetainedProfile x)
      (contDiff_fourCellOddP13AugmentedRetainedProfile x)
      (odd_fourCellOddP13AugmentedRetainedProfile x), h3, h5, h7, h9, h11]
    ring
  have hdiag := fourCellOddCoreLocalBilinear_self_eq_quadratic
    (fourCellOddP13AugmentedRetainedProfile x)
    (contDiff_fourCellOddP13AugmentedRetainedProfile x)
    (odd_fourCellOddP13AugmentedRetainedProfile x)
  have hqzero : fourCellOddCoreLocalQuadratic
      (fourCellOddP13AugmentedRetainedProfile x) = 0 := by
    linarith
  have hp1 : centeredOddP1Coefficient
      (fourCellOddP13AugmentedRetainedProfile x) = 0 := by
    exact centeredOddP1Coefficient_augmentedLowProfile_eq_zero
      (x 0) (x 1) (x 2) (x 3) (x 4)
  have hcoercive := fourCellOddCorePositiveHalfCoerciveAt_rationalFloor
    (fourCellOddP13AugmentedRetainedProfile x)
    (contDiff_fourCellOddP13AugmentedRetainedProfile x)
    (odd_fourCellOddP13AugmentedRetainedProfile x) hp1
  rw [hqzero,
    integral_zero_one_fourCellOddP13AugmentedRetainedProfile_sq] at hcoercive
  have hold : 0 ≤ ∫ t : ℝ in 0..1,
      fourCellOddOneThreeFiveSevenNineLowProfile
        0 (x 0) (x 1) (x 2) (x 3) t ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hx4 : x 4 = 0 := by
    nlinarith [sq_nonneg (x 4)]
  by_contra hxzero
  have hcoeff : (![0, x 0, x 1, x 2, x 3] : Fin 5 → ℝ) ≠ 0 := by
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
    · simpa using hx4
  have hpos := fourCellOddCoreLocalQuadratic_fiveMode_pos
    0 (x 0) (x 1) (x 2) (x 3) hcoeff
  have hprofile : fourCellOddP13AugmentedRetainedProfile x =
      fourCellOddOneThreeFiveSevenNineLowProfile
        0 (x 0) (x 1) (x 2) (x 3) := by
    funext t
    unfold fourCellOddP13AugmentedRetainedProfile
      fourCellOddP11AugmentedLowProfile
    rw [hx4]
    ring
  rw [hprofile] at hqzero
  linarith

/-- The exact enlarged core Gram matrix is nonsingular. -/
theorem fourCellOddP13AugmentedRetainedGram_isUnit :
    IsUnit fourCellOddP13AugmentedRetainedGram := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hsub : fourCellOddP13AugmentedRetainedGram *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp
    (fourCellOddP13AugmentedRetainedGram_kernel (x - y) hsub)

private theorem fourCellOddP13AugmentedRetainedGram_det_isUnit :
    IsUnit fourCellOddP13AugmentedRetainedGram.det :=
  fourCellOddP13AugmentedRetainedGram.isUnit_iff_isUnit_det.mp
    fourCellOddP13AugmentedRetainedGram_isUnit

/-- Exact inverse-defined solution of the five augmented normal equations. -/
def fourCellOddP13AugmentedRetainedSolution : Fin 5 → ℝ :=
  fourCellOddP13AugmentedRetainedGram⁻¹ *ᵥ
    fourCellOddP13AugmentedRetainedRhs

theorem fourCellOddP13AugmentedRetainedSolution_normalEquation :
    fourCellOddP13AugmentedRetainedGram *ᵥ
        fourCellOddP13AugmentedRetainedSolution =
      fourCellOddP13AugmentedRetainedRhs := by
  unfold fourCellOddP13AugmentedRetainedSolution
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv fourCellOddP13AugmentedRetainedGram
      fourCellOddP13AugmentedRetainedGram_det_isUnit,
    Matrix.one_mulVec]

private theorem contDiff_centeredP1_local : ContDiff ℝ 1 centeredP1 := by
  unfold centeredP1
  fun_prop

private theorem odd_centeredP1_local : Function.Odd centeredP1 := by
  intro t
  unfold centeredP1
  ring

/-- The inverse-defined normal equations hold against every enlarged
retained profile. -/
theorem fourCellOddP13AugmentedRetainedSolution_normal
    (y : Fin 5 → ℝ) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP13AugmentedRetainedProfile
          fourCellOddP13AugmentedRetainedSolution)
        (fourCellOddP13AugmentedRetainedProfile y) =
      fourCellOddCoreLocalBilinear centeredP1
        (fourCellOddP13AugmentedRetainedProfile y) := by
  let h := fourCellOddP13AugmentedRetainedProfile
    fourCellOddP13AugmentedRetainedSolution
  have hh : ContDiff ℝ 1 h :=
    contDiff_fourCellOddP13AugmentedRetainedProfile _
  have hhodd : Function.Odd h :=
    odd_fourCellOddP13AugmentedRetainedProfile _
  have hrows :=
    (fourCellOddP13AugmentedRetainedGram_mulVec
      fourCellOddP13AugmentedRetainedSolution).symm.trans
      fourCellOddP13AugmentedRetainedSolution_normalEquation
  have h3 : fourCellOddCoreLocalBilinear retainedBasisThree h =
      fourCellOddCoreLocalBilinear retainedBasisThree centeredP1 := by
    have hi := congrFun hrows 0
    simpa only [h, fourCellOddP13AugmentedRetainedRhs] using hi
  have h5 : fourCellOddCoreLocalBilinear retainedBasisFive h =
      fourCellOddCoreLocalBilinear retainedBasisFive centeredP1 := by
    have hi := congrFun hrows 1
    simpa only [h, fourCellOddP13AugmentedRetainedRhs] using hi
  have h7 : fourCellOddCoreLocalBilinear retainedBasisSeven h =
      fourCellOddCoreLocalBilinear retainedBasisSeven centeredP1 := by
    have hi := congrFun hrows 2
    simpa only [h, fourCellOddP13AugmentedRetainedRhs] using hi
  have h9 : fourCellOddCoreLocalBilinear retainedBasisNine h =
      fourCellOddCoreLocalBilinear retainedBasisNine centeredP1 := by
    have hi := congrFun hrows 3
    simpa only [h, fourCellOddP13AugmentedRetainedRhs] using hi
  have h11 : fourCellOddCoreLocalBilinear retainedBasisEleven h =
      fourCellOddCoreLocalBilinear retainedBasisEleven centeredP1 := by
    have hi := congrFun hrows 4
    simpa only [h, fourCellOddP13AugmentedRetainedRhs] using hi
  have h3' : fourCellOddCoreLocalBilinear h retainedBasisThree =
      fourCellOddCoreLocalBilinear centeredP1 retainedBasisThree := by
    rw [fourCellOddCoreLocalBilinear_comm h retainedBasisThree
        hh.continuous contDiff_retainedBasisThree.continuous,
      fourCellOddCoreLocalBilinear_comm centeredP1 retainedBasisThree
        contDiff_centeredP1_local.continuous
          contDiff_retainedBasisThree.continuous]
    exact h3
  have h5' : fourCellOddCoreLocalBilinear h retainedBasisFive =
      fourCellOddCoreLocalBilinear centeredP1 retainedBasisFive := by
    rw [fourCellOddCoreLocalBilinear_comm h retainedBasisFive
        hh.continuous contDiff_retainedBasisFive.continuous,
      fourCellOddCoreLocalBilinear_comm centeredP1 retainedBasisFive
        contDiff_centeredP1_local.continuous
          contDiff_retainedBasisFive.continuous]
    exact h5
  have h7' : fourCellOddCoreLocalBilinear h retainedBasisSeven =
      fourCellOddCoreLocalBilinear centeredP1 retainedBasisSeven := by
    rw [fourCellOddCoreLocalBilinear_comm h retainedBasisSeven
        hh.continuous contDiff_retainedBasisSeven.continuous,
      fourCellOddCoreLocalBilinear_comm centeredP1 retainedBasisSeven
        contDiff_centeredP1_local.continuous
          contDiff_retainedBasisSeven.continuous]
    exact h7
  have h9' : fourCellOddCoreLocalBilinear h retainedBasisNine =
      fourCellOddCoreLocalBilinear centeredP1 retainedBasisNine := by
    rw [fourCellOddCoreLocalBilinear_comm h retainedBasisNine
        hh.continuous contDiff_retainedBasisNine.continuous,
      fourCellOddCoreLocalBilinear_comm centeredP1 retainedBasisNine
        contDiff_centeredP1_local.continuous
          contDiff_retainedBasisNine.continuous]
    exact h9
  have h11' : fourCellOddCoreLocalBilinear h retainedBasisEleven =
      fourCellOddCoreLocalBilinear centeredP1 retainedBasisEleven := by
    rw [fourCellOddCoreLocalBilinear_comm h retainedBasisEleven
        hh.continuous contDiff_retainedBasisEleven.continuous,
      fourCellOddCoreLocalBilinear_comm centeredP1 retainedBasisEleven
        contDiff_centeredP1_local.continuous
          contDiff_retainedBasisEleven.continuous]
    exact h11
  change fourCellOddCoreLocalBilinear h
      (fourCellOddP13AugmentedRetainedProfile y) = _
  rw [fourCellOddCoreLocalBilinear_retainedProfile_right h hh hhodd y,
    fourCellOddCoreLocalBilinear_retainedProfile_right centeredP1
      contDiff_centeredP1_local odd_centeredP1_local y,
    h3', h5', h7', h9', h11']

/-- The exact inverse solution makes the `P1` residual core-orthogonal to
the complete `P3/P5/P7/P9/P11` block. -/
theorem fourCellOddP13AugmentedRetainedSolution_orthogonal :
    FourCellOddP13AugmentedGalerkinFiniteOrthogonal
      (fourCellOddP13AugmentedRetainedSolution 0)
      (fourCellOddP13AugmentedRetainedSolution 1)
      (fourCellOddP13AugmentedRetainedSolution 2)
      (fourCellOddP13AugmentedRetainedSolution 3)
      (fourCellOddP13AugmentedRetainedSolution 4) := by
  intro d e f g h
  let y : Fin 5 → ℝ := ![d, e, f, g, h]
  let proj := fourCellOddP13AugmentedRetainedProfile
    fourCellOddP13AugmentedRetainedSolution
  let p := fourCellOddP13AugmentedRetainedProfile y
  have hproj : ContDiff ℝ 1 proj :=
    contDiff_fourCellOddP13AugmentedRetainedProfile _
  have hprojodd : Function.Odd proj :=
    odd_fourCellOddP13AugmentedRetainedProfile _
  have hp : ContDiff ℝ 1 p :=
    contDiff_fourCellOddP13AugmentedRetainedProfile _
  have hpodd : Function.Odd p :=
    odd_fourCellOddP13AugmentedRetainedProfile _
  have hnormal := fourCellOddP13AugmentedRetainedSolution_normal y
  have hresidual :
      fourCellOddP13AugmentedGalerkinResidualProfile
          (fourCellOddP13AugmentedRetainedSolution 0)
          (fourCellOddP13AugmentedRetainedSolution 1)
          (fourCellOddP13AugmentedRetainedSolution 2)
          (fourCellOddP13AugmentedRetainedSolution 3)
          (fourCellOddP13AugmentedRetainedSolution 4) =
        centeredP1 + fun t ↦ (-1 : ℝ) * proj t := by
    funext t
    dsimp only [proj, fourCellOddP13AugmentedRetainedProfile]
    unfold fourCellOddP13AugmentedGalerkinResidualProfile
    simp only [Pi.add_apply]
    ring
  change fourCellOddCoreLocalBilinear
    (fourCellOddP13AugmentedGalerkinResidualProfile
      (fourCellOddP13AugmentedRetainedSolution 0)
      (fourCellOddP13AugmentedRetainedSolution 1)
      (fourCellOddP13AugmentedRetainedSolution 2)
      (fourCellOddP13AugmentedRetainedSolution 3)
      (fourCellOddP13AugmentedRetainedSolution 4)) p = 0
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

/-- The augmented finite orthogonality component of the production
certificate is unconditional. -/
theorem exists_fourCellOddP13AugmentedGalerkinFiniteOrthogonal :
    ∃ a3 a5 a7 a9 a11 : ℝ,
      FourCellOddP13AugmentedGalerkinFiniteOrthogonal a3 a5 a7 a9 a11 := by
  exact ⟨fourCellOddP13AugmentedRetainedSolution 0,
    fourCellOddP13AugmentedRetainedSolution 1,
    fourCellOddP13AugmentedRetainedSolution 2,
    fourCellOddP13AugmentedRetainedSolution 3,
    fourCellOddP13AugmentedRetainedSolution 4,
    fourCellOddP13AugmentedRetainedSolution_orthogonal⟩

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedFiniteSolveStructural
