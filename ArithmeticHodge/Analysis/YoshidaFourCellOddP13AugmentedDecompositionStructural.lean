import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualDualDirectStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedDecompositionStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Exact `P11`/`P13+` decomposition for the odd four-cell residual

The first tail mode reverses the old five-mode `1 / 50` dual allocation.
The structural repair is to retain that mode.  This file splits every
`P11+` residual into its normalized classical `P11` coordinate and a
residual orthogonal to `P1,P3,P5,P7,P9,P11`.  The normalization and the
positive-half Pythagorean identity are exact.
-/

/-- The normalized positive-half `P11` coordinate.  The factor `23` is the
inverse of the exact positive-half mass of the classical centered `P11`.
-/
def fourCellOddP11PositiveCoefficient (r : ℝ → ℝ) : ℝ :=
  23 * (∫ x : ℝ in 0..1, r x * fourCellOddP11DirectTail x)

/-- The residual after retaining the exact `P11` coordinate. -/
def fourCellOddP13Residual (r : ℝ → ℝ) : ℝ → ℝ := fun x ↦
  r x - fourCellOddP11PositiveCoefficient r * fourCellOddP11DirectTail x

theorem contDiff_fourCellOddP13Residual
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) :
    ContDiff ℝ 1 (fourCellOddP13Residual r) := by
  unfold fourCellOddP13Residual
  exact hr.sub (contDiff_const.mul contDiff_fourCellOddP11DirectTail)

theorem odd_fourCellOddP13Residual
    (r : ℝ → ℝ) (hodd : Function.Odd r) :
    Function.Odd (fourCellOddP13Residual r) := by
  intro x
  unfold fourCellOddP13Residual
  rw [hodd, odd_fourCellOddP11DirectTail]
  ring

/-- Exact reconstruction after the first tail coordinate is retained. -/
theorem p11Projection_add_fourCellOddP13Residual
    (r : ℝ → ℝ) :
    (fun x ↦ fourCellOddP11PositiveCoefficient r *
        fourCellOddP11DirectTail x) + fourCellOddP13Residual r = r := by
  funext x
  unfold fourCellOddP13Residual
  simp only [Pi.add_apply]
  ring

private theorem lowerMoment_fourCellOddP13Residual_eq_zero
    (r phi : ℝ → ℝ) (hr : Continuous r) (hphi : Continuous phi)
    (hrMoment : (∫ x : ℝ in -1..1, r x * phi x) = 0)
    (hP11Moment :
      (∫ x : ℝ in -1..1, fourCellOddP11DirectTail x * phi x) = 0) :
    (∫ x : ℝ in -1..1, fourCellOddP13Residual r x * phi x) = 0 := by
  have hrI : IntervalIntegrable (fun x : ℝ ↦ r x * phi x) volume (-1) 1 :=
    (hr.mul hphi).intervalIntegrable _ _
  have hpI : IntervalIntegrable (fun x : ℝ ↦
      fourCellOddP11PositiveCoefficient r *
        (fourCellOddP11DirectTail x * phi x)) volume (-1) 1 :=
    (continuous_const.mul
      (contDiff_fourCellOddP11DirectTail.continuous.mul hphi)).intervalIntegrable _ _
  rw [show (fun x : ℝ ↦ fourCellOddP13Residual r x * phi x) =
      fun x ↦ r x * phi x - fourCellOddP11PositiveCoefficient r *
        (fourCellOddP11DirectTail x * phi x) by
    funext x
    unfold fourCellOddP13Residual
    ring,
    intervalIntegral.integral_sub hrI hpI,
    intervalIntegral.integral_const_mul,
    hrMoment, hP11Moment]
  ring

/-- Removing `P11` preserves all five lower odd Legendre equations. -/
theorem fourCellOddP13Residual_lowerMoments
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    centeredOddP1Coefficient (fourCellOddP13Residual r) = 0 ∧
      centeredOddP3Coefficient (fourCellOddP13Residual r) = 0 ∧
      centeredOddP5Coefficient (fourCellOddP13Residual r) = 0 ∧
      centeredOddP7Coefficient (fourCellOddP13Residual r) = 0 ∧
      centeredOddP9Coefficient (fourCellOddP13Residual r) = 0 := by
  rcases fourCellOddP11DirectTail_moments with
    ⟨hp1, hp3, hp5, hp7, hp9⟩
  have hr1 : (∫ x : ℝ in -1..1, r x * centeredP1 x) = 0 := by
    unfold centeredOddP1Coefficient at h1
    nlinarith
  have hr3 : (∫ x : ℝ in -1..1, r x * centeredP3 x) = 0 := by
    unfold centeredOddP3Coefficient at h3
    nlinarith
  have hr5 : (∫ x : ℝ in -1..1, r x * factorTwoCenteredP5 x) = 0 := by
    unfold centeredOddP5Coefficient at h5
    nlinarith
  have hr7 : (∫ x : ℝ in -1..1, r x * factorTwoCenteredP7 x) = 0 := by
    unfold centeredOddP7Coefficient at h7
    nlinarith
  have hr9 : (∫ x : ℝ in -1..1, r x * factorTwoCenteredP9 x) = 0 := by
    unfold centeredOddP9Coefficient at h9
    nlinarith
  have hp1' : (∫ x : ℝ in -1..1,
      fourCellOddP11DirectTail x * centeredP1 x) = 0 := by
    unfold centeredOddP1Coefficient at hp1
    nlinarith
  have hp3' : (∫ x : ℝ in -1..1,
      fourCellOddP11DirectTail x * centeredP3 x) = 0 := by
    unfold centeredOddP3Coefficient at hp3
    nlinarith
  have hp5' : (∫ x : ℝ in -1..1,
      fourCellOddP11DirectTail x * factorTwoCenteredP5 x) = 0 := by
    unfold centeredOddP5Coefficient at hp5
    nlinarith
  have hp7' : (∫ x : ℝ in -1..1,
      fourCellOddP11DirectTail x * factorTwoCenteredP7 x) = 0 := by
    unfold centeredOddP7Coefficient at hp7
    nlinarith
  have hp9' : (∫ x : ℝ in -1..1,
      fourCellOddP11DirectTail x * factorTwoCenteredP9 x) = 0 := by
    unfold centeredOddP9Coefficient at hp9
    nlinarith
  constructor
  · unfold centeredOddP1Coefficient
    rw [lowerMoment_fourCellOddP13Residual_eq_zero r centeredP1
      hr.continuous (by unfold centeredP1; fun_prop) hr1 hp1']
    ring
  constructor
  · unfold centeredOddP3Coefficient
    rw [lowerMoment_fourCellOddP13Residual_eq_zero r centeredP3
      hr.continuous (by unfold centeredP3; fun_prop) hr3 hp3']
    ring
  constructor
  · unfold centeredOddP5Coefficient
    rw [lowerMoment_fourCellOddP13Residual_eq_zero r factorTwoCenteredP5
      hr.continuous continuous_factorTwoCenteredP5 hr5 hp5']
    ring
  constructor
  · unfold centeredOddP7Coefficient
    rw [lowerMoment_fourCellOddP13Residual_eq_zero r factorTwoCenteredP7
      hr.continuous continuous_factorTwoCenteredP7 hr7 hp7']
    ring
  · unfold centeredOddP9Coefficient
    rw [lowerMoment_fourCellOddP13Residual_eq_zero r factorTwoCenteredP9
      hr.continuous continuous_factorTwoCenteredP9 hr9 hp9']
    ring

/-- The new residual is exactly orthogonal to `P11` on the positive half. -/
theorem integral_zero_one_fourCellOddP13Residual_mul_P11_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r) :
    (∫ x : ℝ in 0..1,
      fourCellOddP13Residual r x * fourCellOddP11DirectTail x) = 0 := by
  have hrpI : IntervalIntegrable (fun x : ℝ ↦
      r x * fourCellOddP11DirectTail x) volume 0 1 :=
    (hr.mul contDiff_fourCellOddP11DirectTail.continuous).intervalIntegrable _ _
  have hppI : IntervalIntegrable (fun x : ℝ ↦
      fourCellOddP11DirectTail x ^ 2) volume 0 1 :=
    (contDiff_fourCellOddP11DirectTail.continuous.pow 2).intervalIntegrable _ _
  rw [show (fun x : ℝ ↦
      fourCellOddP13Residual r x * fourCellOddP11DirectTail x) =
      fun x ↦ r x * fourCellOddP11DirectTail x -
        fourCellOddP11PositiveCoefficient r *
          fourCellOddP11DirectTail x ^ 2 by
    funext x
    unfold fourCellOddP13Residual
    ring,
    intervalIntegral.integral_sub hrpI (hppI.const_mul _),
    intervalIntegral.integral_const_mul,
    integral_zero_one_fourCellOddP11DirectTail_sq]
  unfold fourCellOddP11PositiveCoefficient
  ring

/-- Exact positive-half Pythagoras for the retained `P11` coordinate and the
genuine `P13+` residual. -/
theorem integral_zero_one_r_sq_eq_P11_add_P13
    (r : ℝ → ℝ) (hr : Continuous r) :
    (∫ x : ℝ in 0..1, r x ^ 2) =
      fourCellOddP11PositiveCoefficient r ^ 2 / 23 +
        (∫ x : ℝ in 0..1, fourCellOddP13Residual r x ^ 2) := by
  let c := fourCellOddP11PositiveCoefficient r
  let p := fourCellOddP11DirectTail
  let v := fourCellOddP13Residual r
  have hp : Continuous p := contDiff_fourCellOddP11DirectTail.continuous
  have hv : Continuous v := by
    dsimp only [v]
    unfold fourCellOddP13Residual
    exact hr.sub
      (continuous_const.mul contDiff_fourCellOddP11DirectTail.continuous)
  have hppI : IntervalIntegrable (fun x : ℝ ↦ p x ^ 2) volume 0 1 :=
    (hp.pow 2).intervalIntegrable _ _
  have hpvI : IntervalIntegrable (fun x : ℝ ↦ p x * v x) volume 0 1 :=
    (hp.mul hv).intervalIntegrable _ _
  have hvvI : IntervalIntegrable (fun x : ℝ ↦ v x ^ 2) volume 0 1 :=
    (hv.pow 2).intervalIntegrable _ _
  have hcross : (∫ x : ℝ in 0..1, p x * v x) = 0 := by
    have h := integral_zero_one_fourCellOddP13Residual_mul_P11_eq_zero r hr
    dsimp only [p, v]
    rw [show (fun x : ℝ ↦
        fourCellOddP11DirectTail x * fourCellOddP13Residual r x) =
      fun x ↦ fourCellOddP13Residual r x * fourCellOddP11DirectTail x by
        funext x
        ring]
    exact h
  have hreconstruct : r = fun x ↦ c * p x + v x := by
    funext x
    have h := congrFun (p11Projection_add_fourCellOddP13Residual r) x
    dsimp only [c, p, v] at h ⊢
    simpa only [Pi.add_apply] using h.symm
  calc
    (∫ x : ℝ in 0..1, r x ^ 2) =
        ∫ x : ℝ in 0..1, (c * p x + v x) ^ 2 := by rw [hreconstruct]
    _ = ∫ x : ℝ in 0..1,
          c ^ 2 * p x ^ 2 + 2 * c * (p x * v x) + v x ^ 2 := by
      congr 1
      funext x
      ring
    _ = c ^ 2 * (∫ x : ℝ in 0..1, p x ^ 2) +
          2 * c * (∫ x : ℝ in 0..1, p x * v x) +
            (∫ x : ℝ in 0..1, v x ^ 2) := by
      rw [intervalIntegral.integral_add
          ((hppI.const_mul _).add (hpvI.const_mul _)) hvvI,
        intervalIntegral.integral_add (hppI.const_mul _) (hpvI.const_mul _),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ = c ^ 2 / 23 + (∫ x : ℝ in 0..1, v x ^ 2) := by
      rw [hcross]
      dsimp only [p]
      rw [integral_zero_one_fourCellOddP11DirectTail_sq]
      ring
    _ = fourCellOddP11PositiveCoefficient r ^ 2 / 23 +
          (∫ x : ℝ in 0..1, fourCellOddP13Residual r x ^ 2) := by
      rfl

/-- The `P13+` residual mass is bounded by the original `P11+` mass, with
the exact discarded square visible in the proof. -/
theorem integral_zero_one_fourCellOddP13Residual_sq_le
    (r : ℝ → ℝ) (hr : Continuous r) :
    (∫ x : ℝ in 0..1, fourCellOddP13Residual r x ^ 2) ≤
      ∫ x : ℝ in 0..1, r x ^ 2 := by
  have hsplit := integral_zero_one_r_sq_eq_P11_add_P13 r hr
  have hsq : 0 ≤ fourCellOddP11PositiveCoefficient r ^ 2 / 23 := by positivity
  linarith

/-! ## The enlarged finite low block -/

/-- The old `P3/P5/P7/P9` block enlarged by the first genuine tail mode. -/
def fourCellOddP11AugmentedLowProfile
    (d e f g h : ℝ) : ℝ → ℝ := fun x ↦
  fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g x +
    h * fourCellOddP11DirectTail x

theorem contDiff_fourCellOddP11AugmentedLowProfile
    (d e f g h : ℝ) :
    ContDiff ℝ 1 (fourCellOddP11AugmentedLowProfile d e f g h) := by
  unfold fourCellOddP11AugmentedLowProfile
  exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g).add
    (contDiff_const.mul contDiff_fourCellOddP11DirectTail)

theorem odd_fourCellOddP11AugmentedLowProfile
    (d e f g h : ℝ) :
    Function.Odd (fourCellOddP11AugmentedLowProfile d e f g h) := by
  intro x
  unfold fourCellOddP11AugmentedLowProfile
  rw [odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g,
    odd_fourCellOddP11DirectTail]
  ring

/-- Exact reconstruction of an old five-mode-plus-`P11+` profile as the
enlarged finite block plus a genuine `P13+` residual. -/
theorem fiveMode_add_tail_eq_augmentedLow_add_P13Residual
    (d e f g : ℝ) (r : ℝ → ℝ) :
    fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g + r =
      fourCellOddP11AugmentedLowProfile d e f g
          (fourCellOddP11PositiveCoefficient r) +
        fourCellOddP13Residual r := by
  funext x
  unfold fourCellOddP11AugmentedLowProfile fourCellOddP13Residual
  simp only [Pi.add_apply]
  ring

/-- The enlarged finite block is exactly mass-orthogonal to the `P13+`
residual obtained from any genuine `P11+` profile. -/
theorem integral_zero_one_augmentedLow_mul_P13Residual_eq_zero
    (d e f g h : ℝ) (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    (∫ x : ℝ in 0..1,
      fourCellOddP11AugmentedLowProfile d e f g h x *
        fourCellOddP13Residual r x) = 0 := by
  let v := fourCellOddP13Residual r
  have hv : ContDiff ℝ 1 v := by
    dsimp only [v]
    exact contDiff_fourCellOddP13Residual r hr
  have hvodd : Function.Odd v := by
    dsimp only [v]
    exact odd_fourCellOddP13Residual r hodd
  rcases fourCellOddP13Residual_lowerMoments r hr h1 h3 h5 h7 h9 with
    ⟨hv1, hv3, hv5, hv7, hv9⟩
  have hlow : (∫ x : ℝ in 0..1,
      fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g x * v x) = 0 :=
    integral_zero_one_fiveMode_mul_P11Plus_eq_zero
      v hv.continuous hvodd hv1 hv3 hv5 hv7 hv9 0 d e f g
  have hP11 : (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * v x) = 0 := by
    have h := integral_zero_one_fourCellOddP13Residual_mul_P11_eq_zero
      r hr.continuous
    dsimp only [v]
    rw [show (fun x : ℝ ↦
        fourCellOddP11DirectTail x * fourCellOddP13Residual r x) =
      fun x ↦ fourCellOddP13Residual r x * fourCellOddP11DirectTail x by
        funext x
        ring]
    exact h
  have hlowI : IntervalIntegrable (fun x : ℝ ↦
      fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g x * v x)
      volume 0 1 :=
    ((contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g).continuous.mul
      hv.continuous).intervalIntegrable _ _
  have hpI : IntervalIntegrable (fun x : ℝ ↦
      h * (fourCellOddP11DirectTail x * v x)) volume 0 1 :=
    (continuous_const.mul
      (contDiff_fourCellOddP11DirectTail.continuous.mul hv.continuous))
      |>.intervalIntegrable _ _
  unfold fourCellOddP11AugmentedLowProfile
  rw [show (fun x : ℝ ↦
      (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g x +
        h * fourCellOddP11DirectTail x) * v x) =
      fun x ↦
        fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g x * v x +
          h * (fourCellOddP11DirectTail x * v x) by
    funext x
    ring,
    intervalIntegral.integral_add hlowI hpI,
    intervalIntegral.integral_const_mul,
    hlow, hP11]
  ring

/-- Generic version of the enlarged-block orthogonality: the tail may be any
smooth odd profile satisfying the five old moment equations and the new
positive-half `P11` equation. -/
theorem integral_zero_one_augmentedLow_mul_P13Plus_eq_zero
    (d e f g h : ℝ) (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0)
    (h11 : (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * r x) = 0) :
    (∫ x : ℝ in 0..1,
      fourCellOddP11AugmentedLowProfile d e f g h x * r x) = 0 := by
  have hlow := integral_zero_one_fiveMode_mul_P11Plus_eq_zero
    r hr.continuous hodd h1 h3 h5 h7 h9 0 d e f g
  have hlowI : IntervalIntegrable (fun x : ℝ ↦
      fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g x * r x)
      volume 0 1 :=
    ((contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g).continuous.mul
      hr.continuous).intervalIntegrable _ _
  have hpI : IntervalIntegrable (fun x : ℝ ↦
      h * (fourCellOddP11DirectTail x * r x)) volume 0 1 :=
    (continuous_const.mul
      (contDiff_fourCellOddP11DirectTail.continuous.mul hr.continuous))
      |>.intervalIntegrable _ _
  unfold fourCellOddP11AugmentedLowProfile
  rw [show (fun x : ℝ ↦
      (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g x +
        h * fourCellOddP11DirectTail x) * r x) =
      fun x ↦
        fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g x * r x +
          h * (fourCellOddP11DirectTail x * r x) by
    funext x
    ring,
    intervalIntegral.integral_add hlowI hpI,
    intervalIntegral.integral_const_mul,
    hlow, h11]
  ring

/-- Generic positive-half mass Pythagoras at the enlarged cutoff. -/
theorem integral_zero_one_scaled_augmentedLow_add_P13Plus_sq
    (d e f g h s t : ℝ) (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0)
    (h11 : (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * r x) = 0) :
    (∫ x : ℝ in 0..1,
      (s * fourCellOddP11AugmentedLowProfile d e f g h x + t * r x) ^ 2) =
      s ^ 2 * (∫ x : ℝ in 0..1,
        fourCellOddP11AugmentedLowProfile d e f g h x ^ 2) +
      t ^ 2 * (∫ x : ℝ in 0..1, r x ^ 2) := by
  let u := fourCellOddP11AugmentedLowProfile d e f g h
  have hu : Continuous u :=
    (contDiff_fourCellOddP11AugmentedLowProfile d e f g h).continuous
  have huuI : IntervalIntegrable (fun x : ℝ ↦ u x ^ 2) volume 0 1 :=
    (hu.pow 2).intervalIntegrable _ _
  have hurI : IntervalIntegrable (fun x : ℝ ↦ u x * r x) volume 0 1 :=
    (hu.mul hr.continuous).intervalIntegrable _ _
  have hrrI : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2) volume 0 1 :=
    (hr.continuous.pow 2).intervalIntegrable _ _
  have hcross : (∫ x : ℝ in 0..1, u x * r x) = 0 := by
    dsimp only [u]
    exact integral_zero_one_augmentedLow_mul_P13Plus_eq_zero
      d e f g h r hr hodd h1 h3 h5 h7 h9 h11
  change (∫ x : ℝ in 0..1, (s * u x + t * r x) ^ 2) = _
  rw [show (fun x : ℝ ↦ (s * u x + t * r x) ^ 2) =
      fun x ↦ s ^ 2 * u x ^ 2 + 2 * s * t * (u x * r x) +
        t ^ 2 * r x ^ 2 by
    funext x
    ring,
    intervalIntegral.integral_add
      ((huuI.const_mul _).add (hurI.const_mul _)) (hrrI.const_mul _),
    intervalIntegral.integral_add (huuI.const_mul _) (hurI.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    hcross]
  dsimp only [u]
  ring

/-- Exact positive-half mass Pythagoras for an arbitrary enlarged low vector
and a scaled `P13+` residual. -/
theorem integral_zero_one_scaled_augmentedLow_add_P13Residual_sq
    (d e f g h s t : ℝ) (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    (∫ x : ℝ in 0..1,
      (s * fourCellOddP11AugmentedLowProfile d e f g h x +
        t * fourCellOddP13Residual r x) ^ 2) =
      s ^ 2 * (∫ x : ℝ in 0..1,
        fourCellOddP11AugmentedLowProfile d e f g h x ^ 2) +
      t ^ 2 * (∫ x : ℝ in 0..1, fourCellOddP13Residual r x ^ 2) := by
  let u := fourCellOddP11AugmentedLowProfile d e f g h
  let v := fourCellOddP13Residual r
  have hu : Continuous u :=
    (contDiff_fourCellOddP11AugmentedLowProfile d e f g h).continuous
  have hv : Continuous v :=
    (contDiff_fourCellOddP13Residual r hr).continuous
  have huuI : IntervalIntegrable (fun x : ℝ ↦ u x ^ 2) volume 0 1 :=
    (hu.pow 2).intervalIntegrable _ _
  have huvI : IntervalIntegrable (fun x : ℝ ↦ u x * v x) volume 0 1 :=
    (hu.mul hv).intervalIntegrable _ _
  have hvvI : IntervalIntegrable (fun x : ℝ ↦ v x ^ 2) volume 0 1 :=
    (hv.pow 2).intervalIntegrable _ _
  have hcross : (∫ x : ℝ in 0..1, u x * v x) = 0 := by
    dsimp only [u, v]
    exact integral_zero_one_augmentedLow_mul_P13Residual_eq_zero
      d e f g h r hr hodd h1 h3 h5 h7 h9
  change (∫ x : ℝ in 0..1, (s * u x + t * v x) ^ 2) = _
  rw [show (fun x : ℝ ↦ (s * u x + t * v x) ^ 2) =
      fun x ↦ s ^ 2 * u x ^ 2 + 2 * s * t * (u x * v x) +
        t ^ 2 * v x ^ 2 by
    funext x
    ring,
    intervalIntegral.integral_add
      ((huuI.const_mul _).add (huvI.const_mul _)) (hvvI.const_mul _),
    intervalIntegral.integral_add (huuI.const_mul _) (huvI.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    hcross]
  dsimp only [u, v]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedDecompositionStructural
