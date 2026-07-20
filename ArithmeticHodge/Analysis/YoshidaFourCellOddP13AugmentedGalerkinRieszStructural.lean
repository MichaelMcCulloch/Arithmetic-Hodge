import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedDecompositionStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreIntegratedRegularAbsorptionStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedGalerkinRieszStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11CorrectedDeterminantAuditStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP11GalerkinRieszStructural
open YoshidaFourCellOddP11UniversalCoreCauchyStructural
open YoshidaFourCellOddP13AugmentedDecompositionStructural
open YoshidaFourCellOddCoreIntegratedRegularAbsorptionStructural
open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Galerkin--Riesz reduction after retaining `P11`

The five-mode Galerkin residual fails its proposed unweighted tail test in
the first omitted direction.  Here that direction is moved into the finite
space.  The only analytic dual left by this reduction is therefore on the
genuine `P13+` residual.
-/

/-- Residual of `P1` after projection into the enlarged
`P3/P5/P7/P9/P11` block. -/
def fourCellOddP13AugmentedGalerkinResidualProfile
    (a3 a5 a7 a9 a11 : ℝ) : ℝ → ℝ := fun x ↦
  centeredP1 x -
    fourCellOddP11AugmentedLowProfile a3 a5 a7 a9 a11 x

theorem contDiff_fourCellOddP13AugmentedGalerkinResidualProfile
    (a3 a5 a7 a9 a11 : ℝ) :
    ContDiff ℝ 1
      (fourCellOddP13AugmentedGalerkinResidualProfile a3 a5 a7 a9 a11) := by
  have hp1 : ContDiff ℝ 1 centeredP1 := by
    unfold centeredP1
    fun_prop
  unfold fourCellOddP13AugmentedGalerkinResidualProfile
  exact hp1.sub
    (contDiff_fourCellOddP11AugmentedLowProfile a3 a5 a7 a9 a11)

theorem odd_fourCellOddP13AugmentedGalerkinResidualProfile
    (a3 a5 a7 a9 a11 : ℝ) :
    Function.Odd
      (fourCellOddP13AugmentedGalerkinResidualProfile a3 a5 a7 a9 a11) := by
  intro x
  unfold fourCellOddP13AugmentedGalerkinResidualProfile centeredP1
  rw [odd_fourCellOddP11AugmentedLowProfile]
  ring

/-- Exact core orthogonality of the new residual to all five retained
directions. -/
def FourCellOddP13AugmentedGalerkinFiniteOrthogonal
    (a3 a5 a7 a9 a11 : ℝ) : Prop :=
  ∀ d e f g h : ℝ,
    fourCellOddCoreLocalBilinear
      (fourCellOddP13AugmentedGalerkinResidualProfile a3 a5 a7 a9 a11)
      (fourCellOddP11AugmentedLowProfile d e f g h) = 0

/-- Positive-half coercivity of the actual core on the `P1`-orthogonal odd
space.  The integrated nineteen-twentieths theorem is intended to discharge
this interface at its exact constant. -/
def FourCellOddCorePositiveHalfCoerciveAt (kappa : ℝ) : Prop :=
  ∀ (w : ℝ → ℝ), ContDiff ℝ 1 w → Function.Odd w →
    centeredOddP1Coefficient w = 0 →
      kappa * (∫ x : ℝ in 0..1, w x ^ 2) ≤
        fourCellOddCoreLocalQuadratic w

/-- The integrated absorption theorem discharges the coercivity interface at
the exact nineteen-twentieths constant. -/
theorem fourCellOddCorePositiveHalfCoerciveAt_nineteenTwentieths :
    FourCellOddCorePositiveHalfCoerciveAt
      fourCellOddNineteenTwentiethsCoercivityConstant := by
  intro w hw hodd h1
  exact coercivityConstant_mul_positiveHalfMass_le_coreLocalQuadratic_of_P1
    w hw hodd h1

/-- A rational specialization useful for an entirely rational augmented
Galerkin certificate. -/
theorem fourCellOddCorePositiveHalfCoerciveAt_rationalFloor :
    FourCellOddCorePositiveHalfCoerciveAt (343 / 12500 : ℝ) := by
  intro w hw hodd h1
  exact
    threeHundredFortyThree_div_twelveThousandFiveHundred_mul_mass_le_coreLocalQuadratic_of_P1
      w hw hodd h1

/-- The sole infinite-dimensional estimate after the augmented finite solve:
the residual row is tested only on the genuine `P13+` subspace. -/
def FourCellOddP13AugmentedGalerkinResidualL2Dual
    (kappa a3 a5 a7 a9 a11 : ℝ) : Prop :=
  ∀ (r : ℝ → ℝ), ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    (∫ x : ℝ in 0..1, fourCellOddP11DirectTail x * r x) = 0 →
      fourCellOddCoreLocalBilinear
          (fourCellOddP13AugmentedGalerkinResidualProfile
            a3 a5 a7 a9 a11) r ^ 2 ≤
        fourCellOddCoreLocalQuadratic
            (fourCellOddP13AugmentedGalerkinResidualProfile
              a3 a5 a7 a9 a11) *
          (kappa * (∫ x : ℝ in 0..1, r x ^ 2))

private theorem odd_const_mul
    {v : ℝ → ℝ} (hv : Function.Odd v) (t : ℝ) :
    Function.Odd (fun x ↦ t * v x) := by
  intro x
  change t * v (-x) = -(t * v x)
  rw [hv]
  ring

private theorem centeredOddP1Coefficient_add_const_mul
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) (t : ℝ) :
    centeredOddP1Coefficient (u + fun x ↦ t * v x) =
      centeredOddP1Coefficient u + t * centeredOddP1Coefficient v := by
  unfold centeredOddP1Coefficient
  have huI : IntervalIntegrable (fun x : ℝ ↦ u x * centeredP1 x)
      volume (-1) 1 :=
    (hu.mul (by unfold centeredP1; fun_prop)).intervalIntegrable _ _
  have hvI : IntervalIntegrable (fun x : ℝ ↦
      t * (v x * centeredP1 x)) volume (-1) 1 :=
    (continuous_const.mul
      (hv.mul (by unfold centeredP1; fun_prop))).intervalIntegrable _ _
  rw [show (fun x : ℝ ↦
      (u + fun y ↦ t * v y) x * centeredP1 x) =
      fun x ↦ u x * centeredP1 x + t * (v x * centeredP1 x) by
    funext x
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add huI hvI,
    intervalIntegral.integral_const_mul]
  ring

theorem centeredOddP1Coefficient_augmentedLowProfile_eq_zero
    (d e f g h : ℝ) :
    centeredOddP1Coefficient
      (fourCellOddP11AugmentedLowProfile d e f g h) = 0 := by
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  have hp : Continuous p :=
    (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g).continuous
  have hp1 : centeredOddP1Coefficient p = 0 := by
    dsimp only [p]
    simpa using centeredOddP1Coefficient_fiveModeLowProfile 0 d e f g
  have h11 : centeredOddP1Coefficient fourCellOddP11DirectTail = 0 :=
    fourCellOddP11DirectTail_moments.1
  change centeredOddP1Coefficient
    (p + fun x ↦ h * fourCellOddP11DirectTail x) = 0
  rw [centeredOddP1Coefficient_add_const_mul p fourCellOddP11DirectTail
      hp contDiff_fourCellOddP11DirectTail.continuous h,
    hp1, h11]
  ring

/-- Coercivity of the actual core retains the full scaled `P13+` mass after
an arbitrary enlarged low vector is added. -/
theorem kappa_mul_scaled_P13Mass_le_augmentedMiddleQuadratic
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hcoercive : FourCellOddCorePositiveHalfCoerciveAt kappa)
    (d e f g h t : ℝ) (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0)
    (h11 : (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * r x) = 0) :
    t ^ 2 * (kappa * (∫ x : ℝ in 0..1, r x ^ 2)) ≤
      fourCellOddCoreLocalQuadratic
        (fourCellOddP11AugmentedLowProfile d e f g h +
          fun x ↦ t * r x) := by
  let u := fourCellOddP11AugmentedLowProfile d e f g h
  let tr : ℝ → ℝ := fun x ↦ t * r x
  have hu : ContDiff ℝ 1 u :=
    contDiff_fourCellOddP11AugmentedLowProfile d e f g h
  have huodd : Function.Odd u :=
    odd_fourCellOddP11AugmentedLowProfile d e f g h
  have htr : ContDiff ℝ 1 tr := contDiff_const.mul hr
  have htrodd : Function.Odd tr := odd_const_mul hodd t
  have hu1 : centeredOddP1Coefficient u = 0 := by
    dsimp only [u]
    exact centeredOddP1Coefficient_augmentedLowProfile_eq_zero d e f g h
  have hsum1 : centeredOddP1Coefficient (u + tr) = 0 := by
    dsimp only [tr]
    rw [centeredOddP1Coefficient_add_const_mul u r
      hu.continuous hr.continuous t, hu1, h1]
    ring
  have hcore := hcoercive (u + tr) (hu.add htr)
    (huodd.add htrodd) hsum1
  have hmass := integral_zero_one_scaled_augmentedLow_add_P13Plus_sq
    d e f g h 1 t r hr hodd h1 h3 h5 h7 h9 h11
  have huMass : 0 ≤ ∫ x : ℝ in 0..1, u x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (u x))
  have hkLow : 0 ≤ kappa * (∫ x : ℝ in 0..1, u x ^ 2) :=
    mul_nonneg hkappa huMass
  dsimp only [tr] at hcore
  change kappa * (∫ x : ℝ in 0..1,
    (u + fun x ↦ t * r x) x ^ 2) ≤ _ at hcore
  simp only [one_mul, one_pow] at hmass
  change (∫ x : ℝ in 0..1, (u x + t * r x) ^ 2) =
    (∫ x : ℝ in 0..1, u x ^ 2) +
      t ^ 2 * (∫ x : ℝ in 0..1, r x ^ 2) at hmass
  have hlower :
      kappa * (t ^ 2 * (∫ x : ℝ in 0..1, r x ^ 2)) ≤
        kappa * (∫ x : ℝ in 0..1, (u x + t * r x) ^ 2) := by
    rw [hmass]
    nlinarith
  have hresult :
      t ^ 2 * (kappa * (∫ x : ℝ in 0..1, r x ^ 2)) ≤
        fourCellOddCoreLocalQuadratic (u + fun x ↦ t * r x) := by
    calc
      t ^ 2 * (kappa * (∫ x : ℝ in 0..1, r x ^ 2)) =
          kappa * (t ^ 2 * (∫ x : ℝ in 0..1, r x ^ 2)) := by ring
      _ ≤ kappa * (∫ x : ℝ in 0..1, (u x + t * r x) ^ 2) := hlower
      _ = kappa * (∫ x : ℝ in 0..1,
          (u + fun x ↦ t * r x) x ^ 2) := by rfl
      _ ≤ fourCellOddCoreLocalQuadratic (u + fun x ↦ t * r x) := hcore
  simpa only [u] using hresult

/-- Exact quadratic split for the enlarged Galerkin block.  Orthogonality
kills the finite mixed row, leaving only the one `P13+` residual row. -/
theorem fourCellOddCoreLocalQuadratic_augmentedGalerkin_split
    (a3 a5 a7 a9 a11 d e f g h s t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (horth : FourCellOddP13AugmentedGalerkinFiniteOrthogonal
      a3 a5 a7 a9 a11) :
    let p := fourCellOddP11AugmentedLowProfile d e f g h
    let q := fourCellOddP13AugmentedGalerkinResidualProfile
      a3 a5 a7 a9 a11
    let u := fourCellOddP11AugmentedLowProfile
      (s * a3 + t * d) (s * a5 + t * e) (s * a7 + t * f)
        (s * a9 + t * g) (s * a11 + t * h)
    fourCellOddCoreLocalQuadratic
        (fun x ↦ s * centeredP1 x + t * (p x + r x)) =
      fourCellOddCoreLocalQuadratic (u + fun x ↦ t * r x) +
        2 * s * t * fourCellOddCoreLocalBilinear q r +
          s ^ 2 * fourCellOddCoreLocalQuadratic q := by
  dsimp only
  let p := fourCellOddP11AugmentedLowProfile d e f g h
  let q := fourCellOddP13AugmentedGalerkinResidualProfile
    a3 a5 a7 a9 a11
  let u := fourCellOddP11AugmentedLowProfile
    (s * a3 + t * d) (s * a5 + t * e) (s * a7 + t * f)
      (s * a9 + t * g) (s * a11 + t * h)
  let sq : ℝ → ℝ := fun x ↦ s * q x
  let tr : ℝ → ℝ := fun x ↦ t * r x
  have hq : ContDiff ℝ 1 q := by
    dsimp only [q]
    exact contDiff_fourCellOddP13AugmentedGalerkinResidualProfile
      a3 a5 a7 a9 a11
  have hqodd : Function.Odd q := by
    dsimp only [q]
    exact odd_fourCellOddP13AugmentedGalerkinResidualProfile
      a3 a5 a7 a9 a11
  have hu : ContDiff ℝ 1 u := by
    dsimp only [u]
    exact contDiff_fourCellOddP11AugmentedLowProfile _ _ _ _ _
  have huodd : Function.Odd u := by
    dsimp only [u]
    exact odd_fourCellOddP11AugmentedLowProfile _ _ _ _ _
  have hsq : ContDiff ℝ 1 sq := contDiff_const.mul hq
  have hsqodd : Function.Odd sq := odd_const_mul hqodd s
  have htr : ContDiff ℝ 1 tr := contDiff_const.mul hr
  have htrodd : Function.Odd tr := odd_const_mul hodd t
  have hqu : fourCellOddCoreLocalBilinear q u = 0 := by
    dsimp only [q, u]
    exact horth _ _ _ _ _
  have hqtr : fourCellOddCoreLocalBilinear q tr =
      t * fourCellOddCoreLocalBilinear q r := by
    dsimp only [tr]
    exact fourCellOddCoreLocalBilinear_const_mul_right
      q r hq hr hqodd hodd t
  have hqadd : fourCellOddCoreLocalBilinear q (u + tr) =
      fourCellOddCoreLocalBilinear q u +
        fourCellOddCoreLocalBilinear q tr := by
    calc
      fourCellOddCoreLocalBilinear q (u + tr) =
          fourCellOddCoreLocalBilinear (u + tr) q :=
        fourCellOddCoreLocalBilinear_comm q (u + tr)
          hq.continuous (hu.add htr).continuous
      _ = fourCellOddCoreLocalBilinear u q +
            fourCellOddCoreLocalBilinear tr q :=
        fourCellOddCoreLocalBilinear_add_left
          u tr q hu htr hq huodd htrodd hqodd
      _ = fourCellOddCoreLocalBilinear q u +
            fourCellOddCoreLocalBilinear q tr := by
        rw [fourCellOddCoreLocalBilinear_comm u q hu.continuous hq.continuous,
          fourCellOddCoreLocalBilinear_comm tr q htr.continuous hq.continuous]
  have hcross : fourCellOddCoreLocalBilinear sq (u + tr) =
      s * t * fourCellOddCoreLocalBilinear q r := by
    dsimp only [sq]
    rw [fourCellOddCoreLocalBilinear_const_mul_left
      q (u + tr) hq (hu.add htr) hqodd (huodd.add htrodd) s,
      hqadd, hqu, hqtr]
    ring
  have hsqQ : fourCellOddCoreLocalQuadratic sq =
      s ^ 2 * fourCellOddCoreLocalQuadratic q := by
    dsimp only [sq]
    exact fourCellOddCoreLocalQuadratic_const_mul q hq hqodd s
  have hreconstruct :
      (fun x ↦ s * centeredP1 x + t * (p x + r x)) =
        sq + (u + tr) := by
    funext x
    dsimp only [p, q, u, sq, tr]
    unfold fourCellOddP13AugmentedGalerkinResidualProfile
      fourCellOddP11AugmentedLowProfile
      fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp only [Pi.add_apply]
    ring
  rw [hreconstruct,
    fourCellOddCoreLocalQuadratic_add sq (u + tr)
      hsq.continuous (hu.add htr).continuous,
    hcross, hsqQ]
  dsimp only [p, q, u]
  ring

/-- A finite augmented Galerkin solution, its nonnegative residual diagonal,
and the single genuine `P13+` residual dual. -/
def FourCellOddP13AugmentedGalerkinRieszCertificate (kappa : ℝ) : Prop :=
  ∃ a3 a5 a7 a9 a11 : ℝ,
    FourCellOddP13AugmentedGalerkinFiniteOrthogonal a3 a5 a7 a9 a11 ∧
      0 ≤ fourCellOddCoreLocalQuadratic
        (fourCellOddP13AugmentedGalerkinResidualProfile
          a3 a5 a7 a9 a11) ∧
      FourCellOddP13AugmentedGalerkinResidualL2Dual
        kappa a3 a5 a7 a9 a11

/-- Fixed-coefficient augmented Galerkin/Riesz reduction.  This theorem is
the exact replacement for the false five-mode `1 / 50` route: the first
omitted direction is finite, and only `P13+` remains analytic. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_augmentedGalerkinRiesz
    (kappa a3 a5 a7 a9 a11 : ℝ) (hkappa : 0 ≤ kappa)
    (hcoercive : FourCellOddCorePositiveHalfCoerciveAt kappa)
    (horth : FourCellOddP13AugmentedGalerkinFiniteOrthogonal
      a3 a5 a7 a9 a11)
    (hqnonneg : 0 ≤ fourCellOddCoreLocalQuadratic
      (fourCellOddP13AugmentedGalerkinResidualProfile a3 a5 a7 a9 a11))
    (hdual : FourCellOddP13AugmentedGalerkinResidualL2Dual
      kappa a3 a5 a7 a9 a11) :
    FourCellOddP11CoupledRieszDefectNonnegative := by
  intro d e f g r hr hodd h1 h3 h5 h7 h9
  let c := fourCellOddP11PositiveCoefficient r
  let v := fourCellOddP13Residual r
  let p0 := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  let p := fourCellOddP11AugmentedLowProfile d e f g c
  let q := fourCellOddP13AugmentedGalerkinResidualProfile
    a3 a5 a7 a9 a11
  have hv : ContDiff ℝ 1 v := by
    dsimp only [v]
    exact contDiff_fourCellOddP13Residual r hr
  have hvodd : Function.Odd v := by
    dsimp only [v]
    exact odd_fourCellOddP13Residual r hodd
  rcases fourCellOddP13Residual_lowerMoments r hr h1 h3 h5 h7 h9 with
    ⟨hv1, hv3, hv5, hv7, hv9⟩
  have hv11 : (∫ x : ℝ in 0..1,
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
  have hmass0 : 0 ≤ kappa * (∫ x : ℝ in 0..1, v x ^ 2) := by
    exact mul_nonneg hkappa
      (intervalIntegral.integral_nonneg (by norm_num)
        (fun x _hx ↦ sq_nonneg (v x)))
  have hresidualDual := hdual v hv hvodd hv1 hv3 hv5 hv7 hv9 hv11
  have hq : ContDiff ℝ 1 q := by
    dsimp only [q]
    exact contDiff_fourCellOddP13AugmentedGalerkinResidualProfile
      a3 a5 a7 a9 a11
  have hqodd : Function.Odd q := by
    dsimp only [q]
    exact odd_fourCellOddP13AugmentedGalerkinResidualProfile
      a3 a5 a7 a9 a11
  have hpencil : ∀ s t : ℝ,
      0 ≤ fourCellOddCoreLocalQuadratic
        (fun x ↦ s * centeredP1 x + t * (p0 x + r x)) := by
    intro s t
    let u := fourCellOddP11AugmentedLowProfile
      (s * a3 + t * d) (s * a5 + t * e) (s * a7 + t * f)
        (s * a9 + t * g) (s * a11 + t * c)
    have hmiddle := kappa_mul_scaled_P13Mass_le_augmentedMiddleQuadratic
      kappa hkappa hcoercive
      (s * a3 + t * d) (s * a5 + t * e) (s * a7 + t * f)
        (s * a9 + t * g) (s * a11 + t * c) t
      v hv hvodd hv1 hv3 hv5 hv7 hv9 hv11
    have hbinary :=
      (real_quadratic_pencil_nonneg_iff
        (fourCellOddCoreLocalQuadratic q)
        (kappa * (∫ x : ℝ in 0..1, v x ^ 2))
        (fourCellOddCoreLocalBilinear q v)).2
          ⟨by simpa only [q] using hqnonneg, hmass0,
            by simpa only [q] using hresidualDual⟩ s t
    have hsplit := fourCellOddCoreLocalQuadratic_augmentedGalerkin_split
      a3 a5 a7 a9 a11 d e f g c s t v hv hvodd horth
    have hreconstruct : p0 + r = p + v := by
      dsimp only [p0, p, v, c]
      exact fiveMode_add_tail_eq_augmentedLow_add_P13Residual d e f g r
    have hprofile :
        (fun x ↦ s * centeredP1 x + t * (p0 x + r x)) =
          (fun x ↦ s * centeredP1 x + t * (p x + v x)) := by
      funext x
      have hx := congrFun hreconstruct x
      simp only [Pi.add_apply] at hx
      rw [hx]
    rw [hprofile]
    dsimp only [p, q, u] at hsplit hmiddle hbinary ⊢
    rw [hsplit]
    linarith
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let B := fourCellOddCoreLocalQuadratic (p0 + r)
  let C := fourCellOddCoreLocalBilinear centeredP1 (p0 + r)
  have hp0 : ContDiff ℝ 1 p0 := by
    dsimp only [p0]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  have hp0odd : Function.Odd p0 := by
    dsimp only [p0]
    exact odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  have hP1 : ContDiff ℝ 1 centeredP1 := by
    unfold centeredP1
    fun_prop
  have hP1odd : Function.Odd centeredP1 := by
    intro x
    unfold centeredP1
    ring
  have hvfull : ContDiff ℝ 1 (p0 + r) := hp0.add hr
  have hvfullodd : Function.Odd (p0 + r) := hp0odd.add hodd
  have hquad : ∀ s t : ℝ,
      0 ≤ A * s ^ 2 + 2 * C * s * t + B * t ^ 2 := by
    intro s t
    have hnonneg := hpencil s t
    let sp : ℝ → ℝ := fun x ↦ s * centeredP1 x
    let tv : ℝ → ℝ := fun x ↦ t * (p0 + r) x
    have hsp : ContDiff ℝ 1 sp := contDiff_const.mul hP1
    have hspodd : Function.Odd sp := odd_const_mul hP1odd s
    have htv : ContDiff ℝ 1 tv := contDiff_const.mul hvfull
    have htvodd : Function.Odd tv := odd_const_mul hvfullodd t
    have hsum :
        (fun x ↦ s * centeredP1 x + t * (p0 x + r x)) = sp + tv := by
      funext x
      rfl
    rw [hsum,
      fourCellOddCoreLocalQuadratic_add sp tv
        hsp.continuous htv.continuous] at hnonneg
    have hspQ := fourCellOddCoreLocalQuadratic_const_mul
      centeredP1 hP1 hP1odd s
    have htvQ := fourCellOddCoreLocalQuadratic_const_mul
      (p0 + r) hvfull hvfullodd t
    have hcross : fourCellOddCoreLocalBilinear sp tv =
        s * t * fourCellOddCoreLocalBilinear centeredP1 (p0 + r) := by
      dsimp only [sp, tv]
      rw [fourCellOddCoreLocalBilinear_const_mul_left
          centeredP1 (fun x ↦ t * (p0 + r) x)
            hP1 (contDiff_const.mul hvfull) hP1odd
              (odd_const_mul hvfullodd t) s,
        fourCellOddCoreLocalBilinear_const_mul_right
          centeredP1 (p0 + r) hP1 hvfull hP1odd hvfullodd t]
      ring
    rw [hspQ, htvQ, hcross] at hnonneg
    dsimp only [A, B, C]
    convert hnonneg using 1
    ring
  rcases (real_quadratic_pencil_nonneg_iff A B C).1 hquad with
    ⟨_hA, _hB, hschur⟩
  apply (fourCellOddP11CoupledRieszDefect_nonneg_iff_aggregate
    d e f g r hr hodd).2
  simpa only [p0, A, B, C] using hschur

/-- Certificate-level handoff at any nonnegative coercivity constant. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_augmentedCertificate
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hcoercive : FourCellOddCorePositiveHalfCoerciveAt kappa)
    (hcert : FourCellOddP13AugmentedGalerkinRieszCertificate kappa) :
    FourCellOddP11CoupledRieszDefectNonnegative := by
  rcases hcert with ⟨a3, a5, a7, a9, a11, horth, hq, hdual⟩
  exact fourCellOddP11CoupledRieszDefectNonnegative_of_augmentedGalerkinRiesz
    kappa a3 a5 a7 a9 a11 hkappa hcoercive horth hq hdual

/-- Production specialization: after integrated regular absorption, the odd
four-cell frontier is reduced to one exact augmented finite solve and its
`P13+` residual dual. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_nineteenTwentieths_augmentedCertificate
    (hcert : FourCellOddP13AugmentedGalerkinRieszCertificate
      fourCellOddNineteenTwentiethsCoercivityConstant) :
    FourCellOddP11CoupledRieszDefectNonnegative :=
  fourCellOddP11CoupledRieszDefectNonnegative_of_augmentedCertificate
    fourCellOddNineteenTwentiethsCoercivityConstant
    fourCellOddNineteenTwentiethsCoercivityConstant_pos.le
    fourCellOddCorePositiveHalfCoerciveAt_nineteenTwentieths hcert

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
