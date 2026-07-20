import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CrossSquareExtensionStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11LowerMassRegionStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOcticPotential
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11CrossSquareExtensionStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP11SchurResidualProfilesStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddP11UniversalCoreCauchyStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# The lower-mass region of the odd P11+ Schur pencil

Every direction of the universal Schur pencil is orthogonal to `P₁` for
the complete core form, but generally not for the Legendre coefficient.
Subtracting that Legendre component therefore diagonalizes the core with a
*negative* rank-one correction.  The already proved quantitative coercivity
on `P₁⊥` absorbs that correction whenever its lower-strip reserve is
large enough.

For the actual pencil the Legendre residual has an especially simple form:
it is the positive `P₁` pivot times the original finite `P₃/P₅/P₇/P₉`
profile plus the genuine `P₁₁+` tail.  Thus the region below retains the
real moment structure instead of treating the Schur residuals as arbitrary
functions.
-/

private theorem contDiff_centeredP1 : ContDiff ℝ 1 centeredP1 := by
  unfold centeredP1
  fun_prop

private theorem odd_centeredP1 : Function.Odd centeredP1 := by
  intro x
  unfold centeredP1
  ring

/-- Exact rank-one diagonalization on the core-orthogonal hyperplane. -/
theorem fourCellOddCoreLocalQuadratic_eq_p1Residual_sub
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hcore : fourCellOddCoreLocalBilinear centeredP1 w = 0) :
    fourCellOddCoreLocalQuadratic w =
      fourCellOddCoreLocalQuadratic (fourCellOddP1Residual w) -
        fourCellOddCoreLocalQuadratic centeredP1 *
          centeredOddP1Coefficient w ^ 2 := by
  let c := centeredOddP1Coefficient w
  let v := fourCellOddP1Residual w
  let p : ℝ → ℝ := fun x ↦ c * centeredP1 x
  have hv : ContDiff ℝ 1 v := by
    dsimp only [v]
    exact contDiff_fourCellOddP1Residual w hw
  have hvodd : Function.Odd v := by
    dsimp only [v]
    exact odd_fourCellOddP1Residual w hodd
  have hp : ContDiff ℝ 1 p := by
    dsimp only [p]
    exact contDiff_const.mul contDiff_centeredP1
  have hpodd : Function.Odd p := by
    intro x
    dsimp only [p]
    rw [odd_centeredP1]
    ring
  have hreconstruct : v + p = w := by
    dsimp only [v, p, c]
    exact fourCellOddP1Residual_add_projection w
  have hpcore :
      fourCellOddCoreLocalBilinear p centeredP1 =
        c * fourCellOddCoreLocalQuadratic centeredP1 := by
    dsimp only [p]
    rw [fourCellOddCoreLocalBilinear_const_mul_left
      centeredP1 centeredP1 contDiff_centeredP1 contDiff_centeredP1
      odd_centeredP1 odd_centeredP1 c,
      fourCellOddCoreLocalBilinear_self_eq_quadratic
        centeredP1 contDiff_centeredP1 odd_centeredP1]
  have hvcore :
      fourCellOddCoreLocalBilinear v centeredP1 =
        -c * fourCellOddCoreLocalQuadratic centeredP1 := by
    have hsum : fourCellOddCoreLocalBilinear (v + p) centeredP1 = 0 := by
      rw [hreconstruct,
        fourCellOddCoreLocalBilinear_comm w centeredP1
          hw.continuous contDiff_centeredP1.continuous]
      exact hcore
    rw [fourCellOddCoreLocalBilinear_add_left
      v p centeredP1 hv hp contDiff_centeredP1 hvodd hpodd odd_centeredP1,
      hpcore] at hsum
    linarith
  have hvp : fourCellOddCoreLocalBilinear v p =
      -c ^ 2 * fourCellOddCoreLocalQuadratic centeredP1 := by
    dsimp only [p]
    rw [fourCellOddCoreLocalBilinear_const_mul_right
      v centeredP1 hv contDiff_centeredP1 hvodd odd_centeredP1 c,
      hvcore]
    ring
  have hqp : fourCellOddCoreLocalQuadratic p =
      c ^ 2 * fourCellOddCoreLocalQuadratic centeredP1 := by
    dsimp only [p]
    exact fourCellOddCoreLocalQuadratic_const_mul
      centeredP1 contDiff_centeredP1 odd_centeredP1 c
  have hsum := fourCellOddCoreLocalQuadratic_add
    v p hv.continuous hp.continuous
  rw [hreconstruct, hvp, hqp] at hsum
  dsimp only [v, c] at hsum ⊢
  linarith

/-- The quantitative `P₁⊥` reserve closes the region in which the
Legendre residual mass dominates the rank-one extension row. -/
theorem fourCellOddCoreLocalQuadratic_nonneg_of_p1ResidualMassRegion
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hcore : fourCellOddCoreLocalBilinear centeredP1 w = 0)
    (hregion :
      fourCellOddCoreLocalQuadratic centeredP1 *
          centeredOddP1Coefficient w ^ 2 ≤
        (27 / 250 : ℝ) *
            (∫ x : ℝ in 0..3 / 5, fourCellOddP1Residual w x ^ 2) +
          (13 / 20000 : ℝ) *
            (∫ x : ℝ in 0..1, fourCellOddP1Residual w x ^ 2)) :
    0 ≤ fourCellOddCoreLocalQuadratic w := by
  let v := fourCellOddP1Residual w
  have hv : ContDiff ℝ 1 v := by
    dsimp only [v]
    exact contDiff_fourCellOddP1Residual w hw
  have hvodd : Function.Odd v := by
    dsimp only [v]
    exact odd_fourCellOddP1Residual w hodd
  have hvone : centeredOddP1Coefficient v = 0 := by
    dsimp only [v]
    exact centeredOddP1Coefficient_fourCellOddP1Residual_eq_zero
      w hw.continuous
  have hreserve := lowerTailMargin_add_globalMass_le_core_add_localWidthDefect_of_P1
    v hv hvodd hvone
  change
    (27 / 250 : ℝ) * (∫ x : ℝ in 0..3 / 5, v x ^ 2) +
        (13 / 20000 : ℝ) * (∫ x : ℝ in 0..1, v x ^ 2) ≤
      fourCellOddCoreLocalQuadratic v at hreserve
  have hdiag := fourCellOddCoreLocalQuadratic_eq_p1Residual_sub
    w hw hodd hcore
  dsimp only [v] at hreserve
  linarith

/-- The unresidualized `P₁⊥` direction underlying the universal Schur
pencil. -/
def fourCellOddP11UniversalLegendreResidualBaseProfile
    (d e f g s t : ℝ) (r : ℝ → ℝ) : ℝ → ℝ := fun x ↦
  s * fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g x + t * r x

/-- On the genuine Schur plane the Legendre residual is just the positive
core pivot times the unresidualized finite-plus-tail direction. -/
theorem fourCellOddP1Residual_universalCorePencilProfile
    (d e f g s t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (h1 : centeredOddP1Coefficient r = 0) :
    fourCellOddP1Residual
        (fourCellOddP11UniversalCorePencilProfile d e f g s t r) =
      fun x ↦ fourCellOddCoreLocalQuadratic centeredP1 *
        fourCellOddP11UniversalLegendreResidualBaseProfile
          d e f g s t r x := by
  have hcoeff := centeredOddP1Coefficient_universalCorePencilProfile
    d e f g s t r hr h1
  funext x
  unfold fourCellOddP1Residual
  rw [hcoeff]
  unfold fourCellOddP11UniversalCorePencilProfile
    fourCellOddP11TailSchurResidualProfile
  rw [fourCellOddP11FiniteSchurResidualProfile_apply]
  unfold fourCellOddP11UniversalLegendreResidualBaseProfile centeredP1
  ring

/-- The five `P₁₁+` moment equations make the positive-half mass of the
underlying finite-plus-tail direction exactly diagonal. -/
theorem integral_zero_one_universalLegendreResidualBase_sq
    (d e f g s t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    (∫ x : ℝ in 0..1,
        fourCellOddP11UniversalLegendreResidualBaseProfile
          d e f g s t r x ^ 2) =
      s ^ 2 * (∫ x : ℝ in 0..1,
        fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g x ^ 2) +
      t ^ 2 * (∫ x : ℝ in 0..1, r x ^ 2) := by
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  have hp : Continuous p := by
    dsimp only [p]
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
      0 d e f g).continuous
  have hpsq : IntervalIntegrable (fun x : ℝ ↦ p x ^ 2) volume 0 1 :=
    (hp.pow 2).intervalIntegrable _ _
  have hrsq : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2) volume 0 1 :=
    (hr.continuous.pow 2).intervalIntegrable _ _
  have hcrossInt : IntervalIntegrable (fun x : ℝ ↦ p x * r x)
      volume 0 1 := (hp.mul hr.continuous).intervalIntegrable _ _
  have hcross : (∫ x : ℝ in 0..1, p x * r x) = 0 := by
    dsimp only [p]
    exact integral_zero_one_fiveMode_mul_P11Plus_eq_zero
      r hr.continuous hodd h1 h3 h5 h7 h9 0 d e f g
  unfold fourCellOddP11UniversalLegendreResidualBaseProfile
  change (∫ x : ℝ in 0..1, (s * p x + t * r x) ^ 2) = _
  rw [show (fun x : ℝ ↦ (s * p x + t * r x) ^ 2) =
      fun x ↦ s ^ 2 * p x ^ 2 + 2 * s * t * (p x * r x) +
        t ^ 2 * r x ^ 2 by
      funext x
      ring,
    intervalIntegral.integral_add
      ((hpsq.const_mul _).add (hcrossInt.const_mul _))
      (hrsq.const_mul _),
    intervalIntegral.integral_add (hpsq.const_mul _)
      (hcrossInt.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    hcross]
  dsimp only [p]
  ring

/-- Concrete complementary region on the universal Schur pencil.  It is
the exact weighted lower/global mass reserve of the Legendre residual,
expressed before multiplication by the positive `P₁` pivot. -/
theorem universalCorePencil_nonnegative_of_residualMassRegion
    (d e f g s t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (hregion :
      fourCellOddCoreLocalQuadratic centeredP1 *
          (s * fourCellOddCoreLocalBilinear centeredP1
              (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g) +
            t * fourCellOddCoreLocalBilinear centeredP1 r) ^ 2 ≤
        fourCellOddCoreLocalQuadratic centeredP1 ^ 2 *
          ((27 / 250 : ℝ) *
              (∫ x : ℝ in 0..3 / 5,
                fourCellOddP11UniversalLegendreResidualBaseProfile
                  d e f g s t r x ^ 2) +
            (13 / 20000 : ℝ) *
              (∫ x : ℝ in 0..1,
                fourCellOddP11UniversalLegendreResidualBaseProfile
                  d e f g s t r x ^ 2))) :
    0 ≤ fourCellOddCoreLocalQuadratic
      (fourCellOddP11UniversalCorePencilProfile d e f g s t r) := by
  let w := fourCellOddP11UniversalCorePencilProfile d e f g s t r
  let u := fourCellOddP11UniversalLegendreResidualBaseProfile
    d e f g s t r
  have hw : ContDiff ℝ 1 w := by
    dsimp only [w]
    exact contDiff_fourCellOddP11UniversalCorePencilProfile
      d e f g s t r hr
  have hwodd : Function.Odd w := by
    dsimp only [w]
    exact odd_fourCellOddP11UniversalCorePencilProfile
      d e f g s t r hodd
  have hcore : fourCellOddCoreLocalBilinear centeredP1 w = 0 := by
    dsimp only [w]
    exact
      fourCellOddCoreLocalBilinear_centeredP1_universalCorePencilProfile_eq_zero
        d e f g s t r hr hodd
  apply fourCellOddCoreLocalQuadratic_nonneg_of_p1ResidualMassRegion
    w hw hwodd hcore
  have hcoeff := centeredOddP1Coefficient_universalCorePencilProfile
    d e f g s t r hr h1
  have hresidual := fourCellOddP1Residual_universalCorePencilProfile
    d e f g s t r hr h1
  dsimp only [w] at hcoeff hresidual ⊢
  rw [hcoeff, hresidual]
  change
    fourCellOddCoreLocalQuadratic centeredP1 *
        (-(s * fourCellOddCoreLocalBilinear centeredP1
              (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g) +
            t * fourCellOddCoreLocalBilinear centeredP1 r)) ^ 2 ≤ _
  rw [show (fun x : ℝ ↦
      (fourCellOddCoreLocalQuadratic centeredP1 * u x) ^ 2) =
      fun x ↦ fourCellOddCoreLocalQuadratic centeredP1 ^ 2 * u x ^ 2 by
    funext x
    ring]
  repeat rw [intervalIntegral.integral_const_mul]
  dsimp only [u]
  nlinarith

private theorem integral_zero_three_fifths_centeredP3_sq :
    (∫ x : ℝ in 0..3 / 5, centeredP3 x ^ 2) =
      (1539 / 21875 : ℝ) := by
  unfold centeredP3
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 (3 / 5))
    (Continuous.intervalIntegrable (by fun_prop) 0 (3 / 5))]
  norm_num

private theorem integral_zero_one_centeredP3_sq :
    (∫ x : ℝ in 0..1, centeredP3 x ^ 2) = (1 / 7 : ℝ) := by
  unfold centeredP3
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 1)
    (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  norm_num

theorem fourCellOddCoreLocalQuadratic_centeredP1_eq_perturbed11 :
    fourCellOddCoreLocalQuadratic centeredP1 =
      fourCellOddOneThreeFivePerturbed11 := by
  have h :=
    fourCellOddCoreLocalQuadratic_oneThreeFiveLowProfile_eq_perturbed 1 0 0
  have hp : fourCellOddOneThreeFiveLowProfile 1 0 0 = centeredP1 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  rw [hp] at h
  simpa [fourCellOddOneThreeFivePerturbedQuadratic] using h

theorem fourCellOddCoreLocalBilinear_centeredP1_centeredP3_eq_perturbed13 :
    fourCellOddCoreLocalBilinear centeredP1 centeredP3 =
      fourCellOddOneThreeFivePerturbed13 := by
  have hsum :=
    fourCellOddCoreLocalQuadratic_oneThreeFiveLowProfile_eq_perturbed 1 1 0
  have hP1 :=
    fourCellOddCoreLocalQuadratic_oneThreeFiveLowProfile_eq_perturbed 1 0 0
  have hP3 :=
    fourCellOddCoreLocalQuadratic_oneThreeFiveLowProfile_eq_perturbed 0 1 0
  have hpSum : fourCellOddOneThreeFiveLowProfile 1 1 0 =
      centeredP1 + centeredP3 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp only [Pi.add_apply]
    ring
  have hp1 : fourCellOddOneThreeFiveLowProfile 1 0 0 = centeredP1 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  have hp3 : fourCellOddOneThreeFiveLowProfile 0 1 0 = centeredP3 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  rw [hpSum] at hsum
  rw [hp1] at hP1
  rw [hp3] at hP3
  have hadd := fourCellOddCoreLocalQuadratic_add centeredP1 centeredP3
    (by unfold centeredP1; fun_prop) (by unfold centeredP3; fun_prop)
  rw [hsum, hP1, hP3] at hadd
  unfold fourCellOddOneThreeFivePerturbedQuadratic at hadd
  norm_num at hadd
  linarith

/-- The residual-mass region is genuinely complementary, not automatic.
Already the pure finite `P₃` Schur direction strictly reverses its defining
mass inequality.  This does not threaten finite positivity; it proves that
the remaining middle region must retain the finite Schur reserve rather than
trying to close from the generic `P₁⊥` mass margin alone. -/
theorem centeredP3_residualMassRegion_strictly_fails :
    fourCellOddCoreLocalQuadratic centeredP1 ^ 2 *
        ((27 / 250 : ℝ) *
            (∫ x : ℝ in 0..3 / 5, centeredP3 x ^ 2) +
          (13 / 20000 : ℝ) *
            (∫ x : ℝ in 0..1, centeredP3 x ^ 2)) <
      fourCellOddCoreLocalQuadratic centeredP1 *
        fourCellOddCoreLocalBilinear centeredP1 centeredP3 ^ 2 := by
  rw [fourCellOddCoreLocalQuadratic_centeredP1_eq_perturbed11,
    fourCellOddCoreLocalBilinear_centeredP1_centeredP3_eq_perturbed13,
    integral_zero_three_fifths_centeredP3_sq,
    integral_zero_one_centeredP3_sq]
  rcases fourCellOddOneThreeFivePerturbed_entry_bounds with
    ⟨hAlo, hAhi, hBlo, _hBhi, _hDlo, _hDhi,
      _hElo, _hEhi, _hFlo, _hFhi, _hGlo, _hGhi⟩
  let A := fourCellOddOneThreeFivePerturbed11
  let B := fourCellOddOneThreeFivePerturbed13
  let R : ℝ :=
    (27 / 250 : ℝ) * (1539 / 21875) +
      (13 / 20000 : ℝ) * (1 / 7)
  have hA0 : 0 < A := by dsimp only [A]; linarith
  have hB0 : 0 < B := by dsimp only [B]; linarith
  have hR0 : 0 < R := by norm_num [R]
  have hAR : A * R < (248102 / 1000000 : ℝ) * R := by
    exact mul_lt_mul_of_pos_right (by simpa only [A] using hAhi) hR0
  have hBR : (248102 / 1000000 : ℝ) * R <
      (218706 / 1000000 : ℝ) ^ 2 := by
    norm_num [R]
  have hBsq : (218706 / 1000000 : ℝ) ^ 2 < B ^ 2 := by
    dsimp only [B] at hB0 ⊢
    nlinarith
  have hrow : A * R < B ^ 2 := hAR.trans (hBR.trans hBsq)
  have hscaled := mul_lt_mul_of_pos_left hrow hA0
  dsimp only [A, B, R] at hscaled ⊢
  nlinarith

/-- Exact localization of every hypothetical negative direction.  The first
inequality is the extension-row obstruction from the cross-square estimate;
the second says that even the diagonal `P₁⊥` lower/global reserve must be
too small.  Its global term is diagonalized by all five `P₁₁+` moments.
Consequently the unresolved directions occupy a genuine middle region, not
either of the two coercive extremes. -/
theorem universalCorePencil_middleRegion_of_negative
    (d e f g s t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0)
    (hneg : fourCellOddCoreLocalQuadratic
      (fourCellOddP11UniversalCorePencilProfile d e f g s t r) < 0) :
    (12375 / 3288856 : ℝ) *
          (s * fourCellOddCoreLocalBilinear centeredP1
              (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g) +
            t * fourCellOddCoreLocalBilinear centeredP1 r) ^ 2 <
        (∫ x : ℝ in 0..3 / 5,
          fourCellOddP11UniversalCorePencilProfile d e f g s t r x ^ 2) ∧
      fourCellOddCoreLocalQuadratic centeredP1 ^ 2 *
          ((27 / 250 : ℝ) *
              (∫ x : ℝ in 0..3 / 5,
                fourCellOddP11UniversalLegendreResidualBaseProfile
                  d e f g s t r x ^ 2) +
            (13 / 20000 : ℝ) *
              (s ^ 2 * (∫ x : ℝ in 0..1,
                  fourCellOddOneThreeFiveSevenNineLowProfile
                    0 d e f g x ^ 2) +
                t ^ 2 * (∫ x : ℝ in 0..1, r x ^ 2))) <
        fourCellOddCoreLocalQuadratic centeredP1 *
          (s * fourCellOddCoreLocalBilinear centeredP1
              (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g) +
            t * fourCellOddCoreLocalBilinear centeredP1 r) ^ 2 := by
  constructor
  · exact universalCorePencil_lowerMass_gt_extensionRow_of_negative
      d e f g s t r hr hodd h1 hneg
  · have hfail : ¬(
        fourCellOddCoreLocalQuadratic centeredP1 *
            (s * fourCellOddCoreLocalBilinear centeredP1
                (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g) +
              t * fourCellOddCoreLocalBilinear centeredP1 r) ^ 2 ≤
          fourCellOddCoreLocalQuadratic centeredP1 ^ 2 *
            ((27 / 250 : ℝ) *
                (∫ x : ℝ in 0..3 / 5,
                  fourCellOddP11UniversalLegendreResidualBaseProfile
                    d e f g s t r x ^ 2) +
              (13 / 20000 : ℝ) *
                (∫ x : ℝ in 0..1,
                  fourCellOddP11UniversalLegendreResidualBaseProfile
                    d e f g s t r x ^ 2))) := by
      intro hregion
      have hnonneg := universalCorePencil_nonnegative_of_residualMassRegion
        d e f g s t r hr hodd h1 hregion
      linarith
    have hstrict :
        fourCellOddCoreLocalQuadratic centeredP1 ^ 2 *
            ((27 / 250 : ℝ) *
                (∫ x : ℝ in 0..3 / 5,
                  fourCellOddP11UniversalLegendreResidualBaseProfile
                    d e f g s t r x ^ 2) +
              (13 / 20000 : ℝ) *
                (∫ x : ℝ in 0..1,
                  fourCellOddP11UniversalLegendreResidualBaseProfile
                    d e f g s t r x ^ 2)) <
          fourCellOddCoreLocalQuadratic centeredP1 *
            (s * fourCellOddCoreLocalBilinear centeredP1
                (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g) +
              t * fourCellOddCoreLocalBilinear centeredP1 r) ^ 2 :=
      lt_of_not_ge hfail
    rw [integral_zero_one_universalLegendreResidualBase_sq
      d e f g s t r hr hodd h1 h3 h5 h7 h9] at hstrict
    exact hstrict

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11LowerMassRegionStructural
