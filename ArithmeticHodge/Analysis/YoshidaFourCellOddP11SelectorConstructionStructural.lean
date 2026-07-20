import ArithmeticHodge.Analysis.YoshidaFourCellOddP11WeightedDualSelectorStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11SelectorConstructionStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
open YoshidaFourCellOddP11WeightedDualSelectorStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Structural construction of the odd `P₁₁+` coupled selector

The corrected finite--tail row is represented by an explicit retained
degree-`< 11` profile.  This is the inverse-free Gram--Schmidt residual of
the finite `P₃/P₅/P₇/P₉` profile against `P₁`.  The two-row Loewner
expression then becomes one ordinary form pairing with an explicit retained
profile, and its metric is exactly diagonal.
-/

/-- The inverse-free Schur residual of the finite `P₃/P₅/P₇/P₉` profile
against `P₁`.  Its definition displays it as an explicit degree-`< 11`
odd polynomial, with no division by the `P₁` pivot. -/
def fourCellOddP11FiniteSchurResidualProfile
    (d e f g : ℝ) : ℝ → ℝ :=
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let b := fourCellOddCoreLocalBilinear centeredP1 p
  fourCellOddOneThreeFiveSevenNineLowProfile
    (-b) (A * d) (A * e) (A * f) (A * g)

/-- Pointwise Gram--Schmidt identity for the explicit retained selector. -/
theorem fourCellOddP11FiniteSchurResidualProfile_apply
    (d e f g x : ℝ) :
    fourCellOddP11FiniteSchurResidualProfile d e f g x =
      fourCellOddCoreLocalQuadratic centeredP1 *
          fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g x -
        fourCellOddCoreLocalBilinear centeredP1
            (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g) *
          centeredP1 x := by
  unfold fourCellOddP11FiniteSchurResidualProfile
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  ring

theorem contDiff_fourCellOddP11FiniteSchurResidualProfile
    (d e f g : ℝ) :
    ContDiff ℝ 1 (fourCellOddP11FiniteSchurResidualProfile d e f g) := by
  unfold fourCellOddP11FiniteSchurResidualProfile
  exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _

theorem odd_fourCellOddP11FiniteSchurResidualProfile
    (d e f g : ℝ) :
    Function.Odd (fourCellOddP11FiniteSchurResidualProfile d e f g) := by
  unfold fourCellOddP11FiniteSchurResidualProfile
  exact odd_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _

/-- The exact polarization agrees with the core quadratic on the diagonal. -/
theorem fourCellOddCoreLocalBilinear_self_eq_quadratic
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (hvodd : Function.Odd v) :
    fourCellOddCoreLocalBilinear v v =
      fourCellOddCoreLocalQuadratic v := by
  have hadd := fourCellOddCoreLocalQuadratic_add
    v v hv.continuous hv.continuous
  have hscale := fourCellOddCoreLocalQuadratic_const_mul v hv hvodd (2 : ℝ)
  have hfun : v + v = fun x ↦ (2 : ℝ) * v x := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [hfun, hscale] at hadd
  linarith

private theorem fourCellOddCoreLocalQuadratic_centeredP1_eq_perturbed11 :
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

private theorem fourCellOddCoreLocalQuadratic_centeredP3_eq_perturbed33 :
    fourCellOddCoreLocalQuadratic centeredP3 =
      fourCellOddOneThreeFivePerturbed33 := by
  have h :=
    fourCellOddCoreLocalQuadratic_oneThreeFiveLowProfile_eq_perturbed 0 1 0
  have hp : fourCellOddOneThreeFiveLowProfile 0 1 0 = centeredP3 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  rw [hp] at h
  simpa [fourCellOddOneThreeFivePerturbedQuadratic] using h

private theorem fourCellOddCoreLocalBilinear_centeredP1_centeredP3_eq_perturbed13 :
    fourCellOddCoreLocalBilinear centeredP1 centeredP3 =
      fourCellOddOneThreeFivePerturbed13 := by
  have hsum :=
    fourCellOddCoreLocalQuadratic_oneThreeFiveLowProfile_eq_perturbed 1 1 0
  have hp : fourCellOddOneThreeFiveLowProfile 1 1 0 =
      centeredP1 + centeredP3 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp only [Pi.add_apply]
    ring
  rw [hp] at hsum
  have hP1 : Continuous centeredP1 := by
    unfold centeredP1
    fun_prop
  have hP3 : Continuous centeredP3 := by
    unfold centeredP3
    fun_prop
  have hadd := fourCellOddCoreLocalQuadratic_add
    centeredP1 centeredP3 hP1 hP3
  rw [hsum, fourCellOddCoreLocalQuadratic_centeredP1_eq_perturbed11,
    fourCellOddCoreLocalQuadratic_centeredP3_eq_perturbed33] at hadd
  unfold fourCellOddOneThreeFivePerturbedQuadratic at hadd
  norm_num at hadd
  linarith

/-- A single explicit finite direction has strictly positive corrected
reserve.  Consequently the pure `P₁` row is already contained in the
two-row family; it need not be imposed separately. -/
theorem fourCellOddP11FiniteCorrectedReserve_P3_pos :
    0 < fourCellOddP11FiniteCorrectedReserve 1 0 0 0 := by
  have hp : fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0 =
      centeredP3 := by
    funext x
    unfold fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  unfold fourCellOddP11FiniteCorrectedReserve
  rw [hp]
  dsimp only
  rw [fourCellOddCoreLocalQuadratic_centeredP1_eq_perturbed11,
    fourCellOddCoreLocalQuadratic_centeredP3_eq_perturbed33,
    fourCellOddCoreLocalBilinear_centeredP1_centeredP3_eq_perturbed13]
  exact fourCellOddOneThreeFivePerturbed_principal_data.2.1

/-- Testing the coupled row at the strict `P₃` reserve and `(s,t)=(1,0)`
recovers the nominally separate pure `P₁` estimate. -/
theorem fourCellOddP11PureP1Row_of_P3CoupledLoewner
    (r : ℝ → ℝ)
    (hloewner : ∀ s t : ℝ,
      (fourCellOddP11FiniteCorrectedReserve 1 0 0 0 * s *
            fourCellOddCoreLocalBilinear centeredP1 r +
          t * fourCellOddP11FiniteTailCorrectedCross 1 0 0 0 r) ^ 2 ≤
        fourCellOddP11FiniteCorrectedReserve 1 0 0 0 *
          fourCellOddCoreLocalQuadratic centeredP1 *
            (fourCellOddP11FiniteCorrectedReserve 1 0 0 0 * s ^ 2 + t ^ 2) *
              fourCellOddP1ExactTailWeight r) :
    fourCellOddCoreLocalBilinear centeredP1 r ^ 2 ≤
      fourCellOddCoreLocalQuadratic centeredP1 *
        fourCellOddP1ExactTailWeight r := by
  let F := fourCellOddP11FiniteCorrectedReserve 1 0 0 0
  have hF : 0 < F := by
    dsimp only [F]
    exact fourCellOddP11FiniteCorrectedReserve_P3_pos
  have htest := hloewner 1 0
  have hscaled :
      F ^ 2 * fourCellOddCoreLocalBilinear centeredP1 r ^ 2 ≤
        F ^ 2 * (fourCellOddCoreLocalQuadratic centeredP1 *
          fourCellOddP1ExactTailWeight r) := by
    dsimp only [F] at htest ⊢
    convert htest using 1 <;> ring
  nlinarith [sq_pos_of_pos hF]

/-- The corrected finite--tail cross is exactly pairing against the explicit
Schur residual profile. -/
theorem fourCellOddCoreLocalBilinear_finiteSchurResidualProfile
    (d e f g : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hrodd : Function.Odd r) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP11FiniteSchurResidualProfile d e f g) r =
      fourCellOddP11FiniteTailCorrectedCross d e f g r := by
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let b := fourCellOddCoreLocalBilinear centeredP1 p
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
  have hAp : ContDiff ℝ 1 (fun x ↦ A * p x) := contDiff_const.mul hp
  have hmbP1 : ContDiff ℝ 1 (fun x ↦ (-b) * centeredP1 x) :=
    contDiff_const.mul hP1
  have hApodd : Function.Odd (fun x ↦ A * p x) := by
    intro x
    change A * p (-x) = -(A * p x)
    rw [hpodd]
    ring
  have hmbP1odd : Function.Odd (fun x ↦ (-b) * centeredP1 x) := by
    intro x
    change (-b) * centeredP1 (-x) = -((-b) * centeredP1 x)
    rw [hP1odd]
    ring
  have hprofile :
      fourCellOddP11FiniteSchurResidualProfile d e f g =
        (fun x ↦ A * p x) + (fun x ↦ (-b) * centeredP1 x) := by
    funext x
    rw [fourCellOddP11FiniteSchurResidualProfile_apply]
    dsimp only [A, b, p]
    simp only [Pi.add_apply]
    ring
  rw [hprofile,
    fourCellOddCoreLocalBilinear_add_left
      (fun x ↦ A * p x) (fun x ↦ (-b) * centeredP1 x) r
      hAp hmbP1 hr hApodd hmbP1odd hrodd,
    fourCellOddCoreLocalBilinear_const_mul_left p r hp hr hpodd hrodd A,
    fourCellOddCoreLocalBilinear_const_mul_left
      centeredP1 r hP1 hr hP1odd hrodd (-b)]
  unfold fourCellOddP11FiniteTailCorrectedCross
  dsimp only [A, b, p]
  ring

/-- The constructed finite selector is exactly core-orthogonal to `P₁`. -/
theorem fourCellOddCoreLocalBilinear_centeredP1_finiteSchurResidualProfile_eq_zero
    (d e f g : ℝ) :
    fourCellOddCoreLocalBilinear centeredP1
      (fourCellOddP11FiniteSchurResidualProfile d e f g) = 0 := by
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  have hp : ContDiff ℝ 1 p := by
    dsimp only [p]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hP1 : ContDiff ℝ 1 centeredP1 := by
    unfold centeredP1
    fun_prop
  have hP1odd : Function.Odd centeredP1 := by
    intro x
    unfold centeredP1
    ring
  rw [fourCellOddCoreLocalBilinear_comm centeredP1
      (fourCellOddP11FiniteSchurResidualProfile d e f g)
      hP1.continuous
      (contDiff_fourCellOddP11FiniteSchurResidualProfile d e f g).continuous,
    fourCellOddCoreLocalBilinear_finiteSchurResidualProfile
      d e f g centeredP1 hP1 hP1odd]
  unfold fourCellOddP11FiniteTailCorrectedCross
  dsimp only [p]
  rw [fourCellOddCoreLocalBilinear_comm p centeredP1
      hp.continuous hP1.continuous,
    fourCellOddCoreLocalBilinear_self_eq_quadratic centeredP1 hP1 hP1odd]
  ring

/-- Exact norm of the inverse-free Schur residual.  Thus the finite corrected
reserve is not merely a determinant: after multiplication by the `P₁` pivot,
it is the core norm of an explicit degree-`< 11` selector. -/
theorem fourCellOddCoreLocalQuadratic_finiteSchurResidualProfile
    (d e f g : ℝ) :
    fourCellOddCoreLocalQuadratic
        (fourCellOddP11FiniteSchurResidualProfile d e f g) =
      fourCellOddCoreLocalQuadratic centeredP1 *
        fourCellOddP11FiniteCorrectedReserve d e f g := by
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  let h := fourCellOddP11FiniteSchurResidualProfile d e f g
  have hp : ContDiff ℝ 1 p := by
    dsimp only [p]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hpodd : Function.Odd p := by
    dsimp only [p]
    exact odd_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hh : ContDiff ℝ 1 h := by
    dsimp only [h]
    exact contDiff_fourCellOddP11FiniteSchurResidualProfile d e f g
  have hhodd : Function.Odd h := by
    dsimp only [h]
    exact odd_fourCellOddP11FiniteSchurResidualProfile d e f g
  have hP1 : ContDiff ℝ 1 centeredP1 := by
    unfold centeredP1
    fun_prop
  have hP1odd : Function.Odd centeredP1 := by
    intro x
    unfold centeredP1
    ring
  calc
    fourCellOddCoreLocalQuadratic h =
        fourCellOddCoreLocalBilinear h h :=
      (fourCellOddCoreLocalBilinear_self_eq_quadratic h hh hhodd).symm
    _ = fourCellOddP11FiniteTailCorrectedCross d e f g h :=
      fourCellOddCoreLocalBilinear_finiteSchurResidualProfile
        d e f g h hh hhodd
    _ = fourCellOddCoreLocalQuadratic centeredP1 *
        fourCellOddP11FiniteCorrectedReserve d e f g := by
      unfold fourCellOddP11FiniteTailCorrectedCross
        fourCellOddP11FiniteCorrectedReserve
      dsimp only [p, h]
      rw [fourCellOddCoreLocalBilinear_comm
          (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g)
          (fourCellOddP11FiniteSchurResidualProfile d e f g)
          hp.continuous hh.continuous,
        fourCellOddCoreLocalBilinear_finiteSchurResidualProfile
          d e f g (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g)
          hp hpodd,
        fourCellOddCoreLocalBilinear_centeredP1_finiteSchurResidualProfile_eq_zero]
      unfold fourCellOddP11FiniteTailCorrectedCross
      dsimp only [p]
      rw [fourCellOddCoreLocalBilinear_self_eq_quadratic
        (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g) hp hpodd]
      ring

/-! ## The coupled two-row selector -/

/-- The single retained profile representing an arbitrary linear combination
of the two Loewner output rows. -/
def fourCellOddP11CoupledLoewnerSelectorProfile
    (d e f g s t : ℝ) : ℝ → ℝ := fun x ↦
  (fourCellOddP11FiniteCorrectedReserve d e f g * s) * centeredP1 x +
    t * fourCellOddP11FiniteSchurResidualProfile d e f g x

/-- Explicit five retained coordinates of the coupled selector.  In
particular, every two-row Loewner test is represented by one degree-`< 11`
odd polynomial. -/
theorem fourCellOddP11CoupledLoewnerSelectorProfile_eq_lowProfile
    (d e f g s t : ℝ) :
    fourCellOddP11CoupledLoewnerSelectorProfile d e f g s t =
      let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
      let A := fourCellOddCoreLocalQuadratic centeredP1
      let b := fourCellOddCoreLocalBilinear centeredP1 p
      let F := fourCellOddP11FiniteCorrectedReserve d e f g
      fourCellOddOneThreeFiveSevenNineLowProfile
        (F * s - t * b) (t * A * d) (t * A * e) (t * A * f) (t * A * g) := by
  funext x
  unfold fourCellOddP11CoupledLoewnerSelectorProfile
    fourCellOddP11FiniteSchurResidualProfile
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  ring

theorem contDiff_fourCellOddP11CoupledLoewnerSelectorProfile
    (d e f g s t : ℝ) :
    ContDiff ℝ 1
      (fourCellOddP11CoupledLoewnerSelectorProfile d e f g s t) := by
  rw [fourCellOddP11CoupledLoewnerSelectorProfile_eq_lowProfile]
  exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _

theorem odd_fourCellOddP11CoupledLoewnerSelectorProfile
    (d e f g s t : ℝ) :
    Function.Odd
      (fourCellOddP11CoupledLoewnerSelectorProfile d e f g s t) := by
  rw [fourCellOddP11CoupledLoewnerSelectorProfile_eq_lowProfile]
  exact odd_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _

/-- The Loewner numerator is exactly the core pairing of the explicit coupled
selector with the `P₁₁+` tail. -/
theorem fourCellOddCoreLocalBilinear_coupledLoewnerSelectorProfile
    (d e f g s t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hrodd : Function.Odd r) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP11CoupledLoewnerSelectorProfile d e f g s t) r =
      fourCellOddP11FiniteCorrectedReserve d e f g * s *
          fourCellOddCoreLocalBilinear centeredP1 r +
        t * fourCellOddP11FiniteTailCorrectedCross d e f g r := by
  let F := fourCellOddP11FiniteCorrectedReserve d e f g
  let h := fourCellOddP11FiniteSchurResidualProfile d e f g
  have hP1 : ContDiff ℝ 1 centeredP1 := by
    unfold centeredP1
    fun_prop
  have hP1odd : Function.Odd centeredP1 := by
    intro x
    unfold centeredP1
    ring
  have hh : ContDiff ℝ 1 h := by
    dsimp only [h]
    exact contDiff_fourCellOddP11FiniteSchurResidualProfile d e f g
  have hhodd : Function.Odd h := by
    dsimp only [h]
    exact odd_fourCellOddP11FiniteSchurResidualProfile d e f g
  have hFsP1 : ContDiff ℝ 1 (fun x ↦ (F * s) * centeredP1 x) :=
    contDiff_const.mul hP1
  have hth : ContDiff ℝ 1 (fun x ↦ t * h x) := contDiff_const.mul hh
  have hFsP1odd : Function.Odd (fun x ↦ (F * s) * centeredP1 x) := by
    intro x
    change (F * s) * centeredP1 (-x) = -((F * s) * centeredP1 x)
    rw [hP1odd]
    ring
  have hthodd : Function.Odd (fun x ↦ t * h x) := by
    intro x
    change t * h (-x) = -(t * h x)
    rw [hhodd]
    ring
  have hprofile :
      fourCellOddP11CoupledLoewnerSelectorProfile d e f g s t =
        (fun x ↦ (F * s) * centeredP1 x) + (fun x ↦ t * h x) := by
    funext x
    unfold fourCellOddP11CoupledLoewnerSelectorProfile
    dsimp only [F, h]
    simp only [Pi.add_apply]
  rw [hprofile,
    fourCellOddCoreLocalBilinear_add_left
      (fun x ↦ (F * s) * centeredP1 x) (fun x ↦ t * h x) r
      hFsP1 hth hr hFsP1odd hthodd hrodd,
    fourCellOddCoreLocalBilinear_const_mul_left
      centeredP1 r hP1 hr hP1odd hrodd (F * s),
    fourCellOddCoreLocalBilinear_const_mul_left h r hh hr hhodd hrodd t,
    fourCellOddCoreLocalBilinear_finiteSchurResidualProfile d e f g r hr hrodd]

/-- Exact diagonal metric of the coupled selector.  The algebraic
Gram--Schmidt construction removes the mixed term without any estimate. -/
theorem fourCellOddCoreLocalQuadratic_coupledLoewnerSelectorProfile
    (d e f g s t : ℝ) :
    fourCellOddCoreLocalQuadratic
        (fourCellOddP11CoupledLoewnerSelectorProfile d e f g s t) =
      fourCellOddP11FiniteCorrectedReserve d e f g *
        fourCellOddCoreLocalQuadratic centeredP1 *
          (fourCellOddP11FiniteCorrectedReserve d e f g * s ^ 2 + t ^ 2) := by
  let F := fourCellOddP11FiniteCorrectedReserve d e f g
  let h := fourCellOddP11FiniteSchurResidualProfile d e f g
  let u : ℝ → ℝ := fun x ↦ (F * s) * centeredP1 x
  let v : ℝ → ℝ := fun x ↦ t * h x
  have hP1 : ContDiff ℝ 1 centeredP1 := by
    unfold centeredP1
    fun_prop
  have hP1odd : Function.Odd centeredP1 := by
    intro x
    unfold centeredP1
    ring
  have hh : ContDiff ℝ 1 h := by
    dsimp only [h]
    exact contDiff_fourCellOddP11FiniteSchurResidualProfile d e f g
  have hhodd : Function.Odd h := by
    dsimp only [h]
    exact odd_fourCellOddP11FiniteSchurResidualProfile d e f g
  have hu : ContDiff ℝ 1 u := by
    dsimp only [u]
    exact contDiff_const.mul hP1
  have hv : ContDiff ℝ 1 v := by
    dsimp only [v]
    exact contDiff_const.mul hh
  have huodd : Function.Odd u := by
    intro x
    change (F * s) * centeredP1 (-x) = -((F * s) * centeredP1 x)
    rw [hP1odd]
    ring
  have hvodd : Function.Odd v := by
    intro x
    change t * h (-x) = -(t * h x)
    rw [hhodd]
    ring
  have hprofile :
      fourCellOddP11CoupledLoewnerSelectorProfile d e f g s t = u + v := by
    funext x
    unfold fourCellOddP11CoupledLoewnerSelectorProfile
    dsimp only [F, h, u, v]
    simp only [Pi.add_apply]
  have hcross : fourCellOddCoreLocalBilinear u v = 0 := by
    dsimp only [u, v]
    rw [fourCellOddCoreLocalBilinear_const_mul_left
        centeredP1 (fun x ↦ t * h x) hP1 hv hP1odd hvodd (F * s),
      fourCellOddCoreLocalBilinear_const_mul_right
        centeredP1 h hP1 hh hP1odd hhodd t,
      fourCellOddCoreLocalBilinear_centeredP1_finiteSchurResidualProfile_eq_zero]
    ring
  rw [hprofile, fourCellOddCoreLocalQuadratic_add u v hu.continuous hv.continuous,
    hcross]
  dsimp only [u, v]
  rw [fourCellOddCoreLocalQuadratic_const_mul centeredP1 hP1 hP1odd (F * s),
    fourCellOddCoreLocalQuadratic_const_mul h hh hhodd t,
    fourCellOddCoreLocalQuadratic_finiteSchurResidualProfile]
  dsimp only [F, h]
  ring

/-- Every coupled selector is annihilated by a genuine `P₁₁+` tail in
the positive-half mass pairing.  This is the exact selector-subtraction
identity used by a weighted Riesz proof. -/
theorem integral_zero_one_coupledLoewnerSelectorProfile_mul_P11Plus_eq_zero
    (d e f g s t : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (hfive : centeredOddP5Coefficient r = 0)
    (hseven : centeredOddP7Coefficient r = 0)
    (hnine : centeredOddP9Coefficient r = 0) :
    (∫ x : ℝ in 0..1,
      fourCellOddP11CoupledLoewnerSelectorProfile d e f g s t x * r x) = 0 := by
  rw [fourCellOddP11CoupledLoewnerSelectorProfile_eq_lowProfile]
  exact integral_zero_one_fiveMode_mul_P11Plus_eq_zero
    r hr hodd hone hthree hfive hseven hnine _ _ _ _ _

/-- Pointwise structural normal form of the second Loewner inequality: it is
precisely the weighted Cauchy inequality for one explicit degree-`< 11`
selector profile. -/
theorem fourCellOddP11CoupledLoewner_iff_explicitSelectorCauchy
    (d e f g s t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r) :
    (fourCellOddP11FiniteCorrectedReserve d e f g * s *
            fourCellOddCoreLocalBilinear centeredP1 r +
          t * fourCellOddP11FiniteTailCorrectedCross d e f g r) ^ 2 ≤
        fourCellOddP11FiniteCorrectedReserve d e f g *
          fourCellOddCoreLocalQuadratic centeredP1 *
            (fourCellOddP11FiniteCorrectedReserve d e f g * s ^ 2 + t ^ 2) *
              fourCellOddP1ExactTailWeight r ↔
      fourCellOddCoreLocalBilinear
          (fourCellOddP11CoupledLoewnerSelectorProfile d e f g s t) r ^ 2 ≤
        fourCellOddCoreLocalQuadratic
            (fourCellOddP11CoupledLoewnerSelectorProfile d e f g s t) *
          fourCellOddP1ExactTailWeight r := by
  rw [fourCellOddCoreLocalBilinear_coupledLoewnerSelectorProfile
      d e f g s t r hr hodd,
    fourCellOddCoreLocalQuadratic_coupledLoewnerSelectorProfile]

/-- Exact structural reduction of the actual production certificate.  The
separate pure row is redundant by the strict `P₃` test above, and every
remaining test is one weighted Cauchy inequality for the displayed retained
selector. -/
theorem fourCellOddP11CoupledSelectorLoewnerCertificate_iff_explicitSelectorCauchy :
    FourCellOddP11CoupledSelectorLoewnerCertificate ↔
      ∀ (d e f g : ℝ) (r : ℝ → ℝ),
        ContDiff ℝ 1 r → Function.Odd r →
        centeredOddP1Coefficient r = 0 →
        centeredOddP3Coefficient r = 0 →
        centeredOddP5Coefficient r = 0 →
        centeredOddP7Coefficient r = 0 →
        centeredOddP9Coefficient r = 0 →
        ∀ s t : ℝ,
          fourCellOddCoreLocalBilinear
              (fourCellOddP11CoupledLoewnerSelectorProfile d e f g s t) r ^ 2 ≤
            fourCellOddCoreLocalQuadratic
                (fourCellOddP11CoupledLoewnerSelectorProfile d e f g s t) *
              fourCellOddP1ExactTailWeight r := by
  constructor
  · intro hcertificate d e f g r hr hodd hone hthree hfive hseven hnine s t
    rcases hcertificate d e f g r hr hodd hone hthree hfive hseven hnine with
      ⟨_pure, hloewner⟩
    exact (fourCellOddP11CoupledLoewner_iff_explicitSelectorCauchy
      d e f g s t r hr hodd).mp (hloewner s t)
  · intro hselector d e f g r hr hodd hone hthree hfive hseven hnine
    constructor
    · apply fourCellOddP11PureP1Row_of_P3CoupledLoewner r
      intro s t
      apply (fourCellOddP11CoupledLoewner_iff_explicitSelectorCauchy
        1 0 0 0 s t r hr hodd).mpr
      exact hselector 1 0 0 0 r hr hodd hone hthree hfive hseven hnine s t
    · intro s t
      apply (fourCellOddP11CoupledLoewner_iff_explicitSelectorCauchy
        d e f g s t r hr hodd).mpr
      exact hselector d e f g r hr hodd hone hthree hfive hseven hnine s t

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11SelectorConstructionStructural
