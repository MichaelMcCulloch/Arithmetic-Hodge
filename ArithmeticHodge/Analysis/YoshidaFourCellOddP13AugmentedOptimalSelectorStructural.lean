import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedResidualRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedFiniteSolveStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedOptimalSelectorStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP13AugmentedDecompositionStructural
open YoshidaFourCellOddP13AugmentedFiniteSolveStructural
open YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
open YoshidaFourCellOddP13AugmentedResidualRepresenterStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaRegularKernelBound

/-!
# Optimal shared six-mode selector for the augmented odd residual

The lower and upper endpoint strips carry two different exact row densities,
but the quotient uses one selector on their union.  This file constructs the
orthogonal projection of that piecewise density onto
`P1/P3/P5/P7/P9/P11`.  Its coefficients are the six exact split moments,
and the residual norm satisfies an exact Pythagorean identity.
-/

/-- Lower-strip row density for fixed augmented Galerkin coefficients. -/
def fourCellOddP13AugmentedLowerRow
    (a3 a5 a7 a9 a11 : ℝ) : ℝ → ℝ :=
  fourCellOddP13SixModeLowerRepresenter
    1 (-a3) (-a5) (-a7) (-a9) (-a11)

/-- Upper-strip row density for fixed augmented Galerkin coefficients. -/
def fourCellOddP13AugmentedUpperRow
    (a3 a5 a7 a9 a11 : ℝ) : ℝ → ℝ :=
  fourCellOddP13SixModeUpperRepresenter
    1 (-a3) (-a5) (-a7) (-a9) (-a11)

/-- Piecewise two-strip pairing with a test function. -/
def fourCellOddP13AugmentedTwoStripPair
    (a3 a5 a7 a9 a11 : ℝ) (q : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ in 0..3 / 5,
      fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11 x * q x) +
    ∫ x : ℝ in 3 / 5..1,
      fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11 x * q x

/-- Squared two-strip norm of a lower/upper pair. -/
def fourCellOddP13TwoStripNormSq (L U : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ in 0..3 / 5, L x ^ 2) +
    ∫ x : ℝ in 3 / 5..1, U x ^ 2

private theorem continuous_centeredP1_local : Continuous centeredP1 := by
  unfold centeredP1
  fun_prop

private theorem odd_centeredP1_local : Function.Odd centeredP1 := by
  intro x
  unfold centeredP1
  ring

private theorem integral_zero_one_centeredP1_mul_augmentedLow_eq_zero
    (d e f g h : ℝ) :
    (∫ x : ℝ in 0..1,
      centeredP1 x * fourCellOddP11AugmentedLowProfile d e f g h x) = 0 := by
  let u := fourCellOddP11AugmentedLowProfile d e f g h
  have hu : Continuous u :=
    (contDiff_fourCellOddP11AugmentedLowProfile d e f g h).continuous
  have huodd : Function.Odd u :=
    odd_fourCellOddP11AugmentedLowProfile d e f g h
  have hcoefficient :=
    centeredOddP1Coefficient_augmentedLowProfile_eq_zero d e f g h
  have hfull : (∫ x : ℝ in -1..1, centeredP1 x * u x) = 0 := by
    unfold centeredOddP1Coefficient at hcoefficient
    rw [show (fun x : ℝ ↦ centeredP1 x * u x) =
        fun x ↦ u x * centeredP1 x by
      funext x
      ring]
    nlinarith
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ centeredP1 x * u x)
    ((continuous_centeredP1_local.mul hu).intervalIntegrable _ _)
    (by
      intro x
      change centeredP1 (-x) * u (-x) = centeredP1 x * u x
      rw [odd_centeredP1_local, huodd]
      ring)
  rw [hfull] at hfold
  dsimp only [u] at hfold ⊢
  linarith

private theorem integral_zero_one_centeredP1_sq_local :
    (∫ x : ℝ in 0..1, centeredP1 x ^ 2) = 1 / 3 := by
  have hfold := integral_sq_eq_two_mul_positiveHalf
    centeredP1 continuous_centeredP1_local (Or.inr odd_centeredP1_local)
  rw [YoshidaEndpointOcticTwoModeSchurData.integral_centeredP1_sq] at hfold
  linarith

/-- Exact positive-half mass of an arbitrary retained six-mode selector. -/
theorem integral_zero_one_fourCellOddP13SixModeSelector_sq
    (b1 b3 b5 b7 b9 b11 : ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x ^ 2) =
      b1 ^ 2 / 3 + b3 ^ 2 / 7 + b5 ^ 2 / 11 +
        b7 ^ 2 / 15 + b9 ^ 2 / 19 + b11 ^ 2 / 23 := by
  let u := fourCellOddP11AugmentedLowProfile b3 b5 b7 b9 b11
  have hu : Continuous u :=
    (contDiff_fourCellOddP11AugmentedLowProfile b3 b5 b7 b9 b11).continuous
  have h1u := integral_zero_one_centeredP1_mul_augmentedLow_eq_zero
    b3 b5 b7 b9 b11
  have h11 : IntervalIntegrable (fun x : ℝ ↦ centeredP1 x ^ 2)
      volume 0 1 := (continuous_centeredP1_local.pow 2).intervalIntegrable _ _
  have h1uI : IntervalIntegrable (fun x : ℝ ↦ centeredP1 x * u x)
      volume 0 1 := (continuous_centeredP1_local.mul hu).intervalIntegrable _ _
  have huuI : IntervalIntegrable (fun x : ℝ ↦ u x ^ 2)
      volume 0 1 := (hu.pow 2).intervalIntegrable _ _
  rw [show fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 =
      fun x ↦ b1 * centeredP1 x + u x by
    funext x
    dsimp only [u]
    unfold fourCellOddP13SixModeSelector fourCellOddP13SixModeProfile
      fourCellOddP11AugmentedLowProfile
      fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    ring]
  rw [show (fun x : ℝ ↦ (b1 * centeredP1 x + u x) ^ 2) =
      fun x ↦ b1 ^ 2 * centeredP1 x ^ 2 +
        2 * b1 * (centeredP1 x * u x) + u x ^ 2 by
    funext x
    ring,
    intervalIntegral.integral_add
      ((h11.const_mul _).add (h1uI.const_mul _)) huuI,
    intervalIntegral.integral_add (h11.const_mul _) (h1uI.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_zero_one_centeredP1_sq_local, h1u,
    integral_zero_one_fourCellOddP11AugmentedLowProfile_sq]
  ring

/-- Exact positive-half Gram pairing of two retained six-mode selectors. -/
theorem integral_zero_one_fourCellOddP13SixModeSelector_mul
    (b1 b3 b5 b7 b9 b11 c1 c3 c5 c7 c9 c11 : ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x *
        fourCellOddP13SixModeSelector c1 c3 c5 c7 c9 c11 x) =
      b1 * c1 / 3 + b3 * c3 / 7 + b5 * c5 / 11 +
        b7 * c7 / 15 + b9 * c9 / 19 + b11 * c11 / 23 := by
  let p := fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11
  let q := fourCellOddP13SixModeSelector c1 c3 c5 c7 c9 c11
  have hp : Continuous p := by
    dsimp only [p, fourCellOddP13SixModeSelector]
    exact (contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous
  have hq : Continuous q := by
    dsimp only [q, fourCellOddP13SixModeSelector]
    exact (contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous
  rw [show (fun x : ℝ ↦ p x * q x) = fun x ↦
      (1 / 2 : ℝ) * ((p x + q x) ^ 2 - p x ^ 2 - q x ^ 2) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  rw [show (fun x : ℝ ↦ (p x + q x) ^ 2 - p x ^ 2 - q x ^ 2) =
      fun x ↦ (p + q) x ^ 2 - p x ^ 2 - q x ^ 2 by
    funext x
    simp only [Pi.add_apply],
    intervalIntegral.integral_sub
      (((hp.add hq).pow 2 |>.intervalIntegrable _ _).sub
        (hp.pow 2 |>.intervalIntegrable _ _))
      (hq.pow 2 |>.intervalIntegrable _ _),
    intervalIntegral.integral_sub
      ((hp.add hq).pow 2 |>.intervalIntegrable _ _)
      (hp.pow 2 |>.intervalIntegrable _ _)]
  have hpq : p + q = fourCellOddP13SixModeSelector
      (b1 + c1) (b3 + c3) (b5 + c5) (b7 + c7) (b9 + c9) (b11 + c11) := by
    funext x
    dsimp only [p, q]
    unfold fourCellOddP13SixModeSelector fourCellOddP13SixModeProfile
      fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp only [Pi.add_apply]
    ring
  rw [hpq,
    integral_zero_one_fourCellOddP13SixModeSelector_sq,
    show (∫ x : ℝ in 0..1, p x ^ 2) =
        b1 ^ 2 / 3 + b3 ^ 2 / 7 + b5 ^ 2 / 11 +
          b7 ^ 2 / 15 + b9 ^ 2 / 19 + b11 ^ 2 / 23 by
      dsimp only [p]
      exact integral_zero_one_fourCellOddP13SixModeSelector_sq _ _ _ _ _ _,
    show (∫ x : ℝ in 0..1, q x ^ 2) =
        c1 ^ 2 / 3 + c3 ^ 2 / 7 + c5 ^ 2 / 11 +
          c7 ^ 2 / 15 + c9 ^ 2 / 19 + c11 ^ 2 / 23 by
      dsimp only [q]
      exact integral_zero_one_fourCellOddP13SixModeSelector_sq _ _ _ _ _ _]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedOptimalSelectorStructural
