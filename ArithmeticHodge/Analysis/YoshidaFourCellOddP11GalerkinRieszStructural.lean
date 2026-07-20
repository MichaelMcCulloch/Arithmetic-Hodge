import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CorrectedCrossOnlyStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11LowerMassRegionStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinRieszStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddFiveModeStrictCoercivityStructural
open YoshidaFourCellOddP11CorrectedCrossOnlyStructural
open YoshidaFourCellOddP11CorrectedDeterminantAuditStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP11LowerMassRegionStructural
open YoshidaFourCellOddP11UniversalCoreCauchyStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Galerkin--Riesz reduction of the corrected odd cross

The retained space is `L = span(P₃,P₅,P₇,P₉)`.  Given `h ∈ L`, set
`q = P₁ - h`.  If `q` is core-orthogonal to `L`, then in the full pencil

`s P₁ + t (p + r) = s q + ((s h + t p) + t r)`

the first mixed row sees only the genuine `P₁₁+` residual `r`.  The
unconditional `P₁`-zero coercivity theorem reserves `1/50` of the positive
half `L²` mass of `r`, uniformly in the retained vector `s h + t p`.  Thus one
single `L²` dual bound for the residual row of `q` proves the complete
correlation-preserving target.  No scalar lower bound is substituted for the
actual tail Schur reserve.
-/

/-- A candidate Galerkin projection of `P₁` into the retained
`P₃/P₅/P₇/P₉` space. -/
def fourCellOddP11GalerkinLowProfile
    (a₃ a₅ a₇ a₉ : ℝ) : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile 0 a₃ a₅ a₇ a₉

/-- The residual `q = P₁ - h` of a candidate retained Galerkin projection.
-/
def fourCellOddP11GalerkinResidualProfile
    (a₃ a₅ a₇ a₉ : ℝ) : ℝ → ℝ := fun x ↦
  centeredP1 x - fourCellOddP11GalerkinLowProfile a₃ a₅ a₇ a₉ x

/-- The Galerkin residual is itself a retained five-mode profile. -/
theorem fourCellOddP11GalerkinResidualProfile_eq_fiveMode
    (a₃ a₅ a₇ a₉ : ℝ) :
    fourCellOddP11GalerkinResidualProfile a₃ a₅ a₇ a₉ =
      fourCellOddOneThreeFiveSevenNineLowProfile
        1 (-a₃) (-a₅) (-a₇) (-a₉) := by
  funext x
  unfold fourCellOddP11GalerkinResidualProfile
    fourCellOddP11GalerkinLowProfile
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  ring

/-- Exact core orthogonality of the candidate residual to the whole retained
four-dimensional space. -/
def FourCellOddP11GalerkinFiniteOrthogonal
    (a₃ a₅ a₇ a₉ : ℝ) : Prop :=
  ∀ d e f g : ℝ,
    fourCellOddCoreLocalBilinear
        (fourCellOddP11GalerkinResidualProfile a₃ a₅ a₇ a₉)
        (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g) = 0

/-- The sole infinite-dimensional premise of the Galerkin route.  Its right
side is exactly the `1/50` positive-half mass that remains uniformly after an
arbitrary retained vector is added to a `P₁₁+` residual. -/
def FourCellOddP11GalerkinResidualL2Dual
    (a₃ a₅ a₇ a₉ : ℝ) : Prop :=
  ∀ (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    fourCellOddCoreLocalBilinear
        (fourCellOddP11GalerkinResidualProfile a₃ a₅ a₇ a₉) r ^ 2 ≤
      fourCellOddCoreLocalQuadratic
          (fourCellOddP11GalerkinResidualProfile a₃ a₅ a₇ a₉) *
        ((1 / 50 : ℝ) * (∫ x : ℝ in 0..1, r x ^ 2))

/-- A finite Galerkin choice together with its one residual `L²` dual bound.
-/
def FourCellOddP11GalerkinRieszCertificate : Prop :=
  ∃ a₃ a₅ a₇ a₉ : ℝ,
    FourCellOddP11GalerkinFiniteOrthogonal a₃ a₅ a₇ a₉ ∧
      FourCellOddP11GalerkinResidualL2Dual a₃ a₅ a₇ a₉

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

private theorem odd_const_mul
    {v : ℝ → ℝ} (hv : Function.Odd v) (t : ℝ) :
    Function.Odd (fun x ↦ t * v x) := by
  intro x
  change t * v (-x) = -(t * v x)
  rw [hv]
  ring

/-- Exact quadratic split behind the Galerkin reduction.  The finite mixed
row vanishes by the Galerkin equation, leaving only `B(q,r)`. -/
theorem fourCellOddCoreLocalQuadratic_galerkinRiesz_split
    (a₃ a₅ a₇ a₉ d e f g s t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (horth : FourCellOddP11GalerkinFiniteOrthogonal a₃ a₅ a₇ a₉) :
    let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
    let q := fourCellOddP11GalerkinResidualProfile a₃ a₅ a₇ a₉
    let u := fourCellOddOneThreeFiveSevenNineLowProfile 0
      (s * a₃ + t * d) (s * a₅ + t * e)
        (s * a₇ + t * f) (s * a₉ + t * g)
    fourCellOddCoreLocalQuadratic
        (fun x ↦ s * centeredP1 x + t * (p x + r x)) =
      fourCellOddCoreLocalQuadratic (u + fun x ↦ t * r x) +
        2 * s * t * fourCellOddCoreLocalBilinear q r +
          s ^ 2 * fourCellOddCoreLocalQuadratic q := by
  dsimp only
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  let q := fourCellOddP11GalerkinResidualProfile a₃ a₅ a₇ a₉
  let u := fourCellOddOneThreeFiveSevenNineLowProfile 0
    (s * a₃ + t * d) (s * a₅ + t * e)
      (s * a₇ + t * f) (s * a₉ + t * g)
  let sq : ℝ → ℝ := fun x ↦ s * q x
  let tr : ℝ → ℝ := fun x ↦ t * r x
  have hq : ContDiff ℝ 1 q := by
    dsimp only [q]
    rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hqodd : Function.Odd q := by
    dsimp only [q]
    rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
    exact odd_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hu : ContDiff ℝ 1 u := by
    dsimp only [u]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have huodd : Function.Odd u := by
    dsimp only [u]
    exact odd_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hsq : ContDiff ℝ 1 sq := contDiff_const.mul hq
  have hsqodd : Function.Odd sq := odd_const_mul hqodd s
  have htr : ContDiff ℝ 1 tr := contDiff_const.mul hr
  have htrodd : Function.Odd tr := odd_const_mul hodd t
  have hqu : fourCellOddCoreLocalBilinear q u = 0 := by
    dsimp only [q, u]
    exact horth _ _ _ _
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
    unfold fourCellOddP11GalerkinResidualProfile
      fourCellOddP11GalerkinLowProfile
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

/-- The retained/P₁₁+ block keeps the full `1/50` mass of the tail after
an arbitrary retained vector is added. -/
theorem one_fiftieth_tailMass_le_galerkinMiddleQuadratic
    (d e f g t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    t ^ 2 * ((1 / 50 : ℝ) * (∫ x : ℝ in 0..1, r x ^ 2)) ≤
      fourCellOddCoreLocalQuadratic
        (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g +
          fun x ↦ t * r x) := by
  let u := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  let tr : ℝ → ℝ := fun x ↦ t * r x
  have hu : ContDiff ℝ 1 u := by
    dsimp only [u]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have huodd : Function.Odd u := by
    dsimp only [u]
    exact odd_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have htr : ContDiff ℝ 1 tr := contDiff_const.mul hr
  have htrodd : Function.Odd tr := odd_const_mul hodd t
  have hu1 : centeredOddP1Coefficient u = 0 := by
    dsimp only [u]
    exact centeredOddP1Coefficient_fiveModeLowProfile 0 d e f g
  have hsum1 : centeredOddP1Coefficient (u + tr) = 0 := by
    dsimp only [tr]
    rw [centeredOddP1Coefficient_add_const_mul u r hu.continuous hr.continuous,
      hu1, h1]
    ring
  have hcoercive :=
    one_fiftieth_positiveHalfMass_le_core_add_localWidthDefect_of_P1
      (u + tr) (hu.add htr) (huodd.add htrodd) hsum1
  change (1 / 50 : ℝ) * (∫ x : ℝ in 0..1, (u + tr) x ^ 2) ≤
    fourCellOddCoreLocalQuadratic (u + tr) at hcoercive
  have hmass := integral_zero_one_universalLegendreResidualBase_sq
    d e f g 1 t r hr hodd h1 h3 h5 h7 h9
  have hprofile :
      fourCellOddP11UniversalLegendreResidualBaseProfile
          d e f g 1 t r = u + tr := by
    funext x
    unfold fourCellOddP11UniversalLegendreResidualBaseProfile
    dsimp only [u, tr]
    simp only [Pi.add_apply, one_mul]
  rw [hprofile] at hmass
  have huMass : 0 ≤ ∫ x : ℝ in 0..1, u x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (u x))
  dsimp only [tr] at hmass hcoercive ⊢
  simp only [Pi.add_apply] at hmass hcoercive
  nlinarith

/-- Fixed-coefficient Galerkin/Riesz reduction.  Once the finite Galerkin
equations hold, the one residual `L²` dual estimate proves the exact complete
`P₁`-orthogonal form-dual target. -/
theorem fourCellOddP1OrthogonalFormDualBound_of_galerkinRiesz
    (a₃ a₅ a₇ a₉ : ℝ)
    (horth : FourCellOddP11GalerkinFiniteOrthogonal a₃ a₅ a₇ a₉)
    (hdual : FourCellOddP11GalerkinResidualL2Dual a₃ a₅ a₇ a₉) :
    FourCellOddP1OrthogonalFormDualBound := by
  apply
    (fourCellOddP11CoupledRieszDefectNonnegative_iff_P1OrthogonalFormDual).1
  intro d e f g r hr hodd h1 h3 h5 h7 h9
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  let q := fourCellOddP11GalerkinResidualProfile a₃ a₅ a₇ a₉
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let B := fourCellOddCoreLocalQuadratic (p + r)
  let C := fourCellOddCoreLocalBilinear centeredP1 (p + r)
  have hq : ContDiff ℝ 1 q := by
    dsimp only [q]
    rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hqodd : Function.Odd q := by
    dsimp only [q]
    rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
    exact odd_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hqpos : 0 < fourCellOddCoreLocalQuadratic q := by
    dsimp only [q]
    rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
    apply fourCellOddCoreLocalQuadratic_fiveMode_pos
    intro hzero
    have hfirst := congrFun hzero 0
    norm_num at hfirst
  have hmass0 : 0 ≤ (1 / 50 : ℝ) * (∫ x : ℝ in 0..1, r x ^ 2) := by
    exact mul_nonneg (by norm_num)
      (intervalIntegral.integral_nonneg (by norm_num)
        (fun x _hx ↦ sq_nonneg (r x)))
  have hresidualDual := hdual r hr hodd h1 h3 h5 h7 h9
  have hpencil : ∀ s t : ℝ,
      0 ≤ fourCellOddCoreLocalQuadratic
        (fun x ↦ s * centeredP1 x + t * (p x + r x)) := by
    intro s t
    let u := fourCellOddOneThreeFiveSevenNineLowProfile 0
      (s * a₃ + t * d) (s * a₅ + t * e)
        (s * a₇ + t * f) (s * a₉ + t * g)
    have hmiddle := one_fiftieth_tailMass_le_galerkinMiddleQuadratic
      (s * a₃ + t * d) (s * a₅ + t * e)
        (s * a₇ + t * f) (s * a₉ + t * g) t
          r hr hodd h1 h3 h5 h7 h9
    have hbinary :=
      (real_quadratic_pencil_nonneg_iff
        (fourCellOddCoreLocalQuadratic q)
        ((1 / 50 : ℝ) * (∫ x : ℝ in 0..1, r x ^ 2))
        (fourCellOddCoreLocalBilinear q r)).2
          ⟨hqpos.le, hmass0, by simpa only [q] using hresidualDual⟩ s t
    have hsplit := fourCellOddCoreLocalQuadratic_galerkinRiesz_split
      a₃ a₅ a₇ a₉ d e f g s t r hr hodd horth
    dsimp only [p, q, u] at hsplit hmiddle hbinary ⊢
    rw [hsplit]
    linarith
  have hp : ContDiff ℝ 1 p := by
    dsimp only [p]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hpodd : Function.Odd p := by
    dsimp only [p]
    exact odd_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hP1 : ContDiff ℝ 1 centeredP1 := by
    unfold centeredP1
    fun_prop
  have hP1odd : Function.Odd centeredP1 := by
    intro x
    unfold centeredP1
    ring
  have hv : ContDiff ℝ 1 (p + r) := hp.add hr
  have hvodd : Function.Odd (p + r) := hpodd.add hodd
  have hquad : ∀ s t : ℝ,
      0 ≤ A * s ^ 2 + 2 * C * s * t + B * t ^ 2 := by
    intro s t
    have h := hpencil s t
    let sp : ℝ → ℝ := fun x ↦ s * centeredP1 x
    let tv : ℝ → ℝ := fun x ↦ t * (p + r) x
    have hsp : ContDiff ℝ 1 sp := contDiff_const.mul hP1
    have hspodd : Function.Odd sp := odd_const_mul hP1odd s
    have htv : ContDiff ℝ 1 tv := contDiff_const.mul hv
    have htvodd : Function.Odd tv := odd_const_mul hvodd t
    have hsum :
        (fun x ↦ s * centeredP1 x + t * (p x + r x)) = sp + tv := by
      funext x
      rfl
    rw [hsum,
      fourCellOddCoreLocalQuadratic_add sp tv
        hsp.continuous htv.continuous] at h
    have hspQ := fourCellOddCoreLocalQuadratic_const_mul
      centeredP1 hP1 hP1odd s
    have htvQ := fourCellOddCoreLocalQuadratic_const_mul
      (p + r) hv hvodd t
    have hcross : fourCellOddCoreLocalBilinear sp tv =
        s * t * fourCellOddCoreLocalBilinear centeredP1 (p + r) := by
      dsimp only [sp, tv]
      rw [fourCellOddCoreLocalBilinear_const_mul_left
          centeredP1 (fun x ↦ t * (p + r) x)
            hP1 (contDiff_const.mul hv) hP1odd (odd_const_mul hvodd t) s,
        fourCellOddCoreLocalBilinear_const_mul_right
          centeredP1 (p + r) hP1 hv hP1odd hvodd t]
      ring
    rw [hspQ, htvQ, hcross] at h
    dsimp only [A, B, C]
    convert h using 1
    ring
  rcases (real_quadratic_pencil_nonneg_iff A B C).1 hquad with
    ⟨_A0, _B0, hschur⟩
  apply (fourCellOddP11CoupledRieszDefect_nonneg_iff_aggregate
    d e f g r hr hodd).2
  simpa only [p, A, B, C] using hschur

/-- Certificate-level handoff to the exact odd frontier. -/
theorem fourCellOddP1OrthogonalFormDualBound_of_galerkinRieszCertificate
    (hcert : FourCellOddP11GalerkinRieszCertificate) :
    FourCellOddP1OrthogonalFormDualBound := by
  rcases hcert with ⟨a₃, a₅, a₇, a₉, horth, hdual⟩
  exact fourCellOddP1OrthogonalFormDualBound_of_galerkinRiesz
    a₃ a₅ a₇ a₉ horth hdual

/-- The same certificate closes the sole remaining corrected cross, by the
already proved exact equivalence. -/
theorem fourCellOddP11CorrectedCrossCauchyOnly_of_galerkinRieszCertificate
    (hcert : FourCellOddP11GalerkinRieszCertificate) :
    FourCellOddP11CorrectedCrossCauchyOnly :=
  (fourCellOddP11CorrectedCrossCauchyOnly_iff_P1OrthogonalFormDual).2
    (fourCellOddP1OrthogonalFormDualBound_of_galerkinRieszCertificate hcert)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinRieszStructural
