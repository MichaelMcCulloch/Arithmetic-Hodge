import ArithmeticHodge.Analysis.YoshidaFourCellOddP51GalerkinRieszStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51RawMassCancellationStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreLogKernel
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoEndpointBilinear
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# Exact raw-log and scalar-mass cancellation at the P51 cutoff

The inverse-solved profile `q51` belongs to the complete odd Legendre block
through degree 51.  A genuine `P53+` residual is orthogonal to every one of
those modes.  The raw-log eigenidentity therefore kills the complete global
singular row at once, and the same moment equations kill the scalar mass
row.  No mode value or matrix entry is expanded here.
-/

theorem centeredPullback_fourCellOddFiniteRetainedBasis
    {N : ℕ} (i : Fin (N + 1)) (t : ℝ) :
    centeredPullback (fourCellOddFiniteRetainedBasis i) t =
      -(shiftedLegendreReal
        (fourCellOddFiniteRetainedDegree i)).eval t := by
  unfold centeredPullback fourCellOddFiniteRetainedBasis
  rw [eval_centeredShiftedLegendreReal]
  congr 2
  ring

private theorem contDiff_fourCellOddFiniteRetainedPartialProfile
    {N : ℕ} (a : Fin (N + 1) → ℝ)
    (s : Finset (Fin (N + 1))) :
    ContDiff ℝ 1 (s.sum fun i ↦
      fun x ↦ a i * fourCellOddFiniteRetainedBasis i x) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (contDiff_const.mul
        (contDiff_fourCellOddFiniteRetainedBasis i)).add ih

private theorem integral_neg_one_one_basis_mul_tail_eq_zero
    {N : ℕ} (i : Fin (N + 1)) (r : ℝ → ℝ)
    (hr : Continuous r) (hodd : Function.Odd r)
    (hmoment : (∫ x : ℝ in 0..1,
      fourCellOddFiniteRetainedBasis i x * r x) = 0) :
    (∫ x : ℝ in -1..1,
      r x * fourCellOddFiniteRetainedBasis i x) = 0 := by
  let f : ℝ → ℝ := fun x ↦
    fourCellOddFiniteRetainedBasis i x * r x
  have hf : Continuous f :=
    (contDiff_fourCellOddFiniteRetainedBasis i).continuous.mul hr
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    rw [odd_fourCellOddFiniteRetainedBasis i, hodd]
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    f (hf.intervalIntegrable _ _) hfeven
  have hfull : (∫ x : ℝ in -1..1, f x) = 0 := by
    dsimp only [f] at hfold
    rw [hmoment] at hfold
    linarith
  calc
    (∫ x : ℝ in -1..1,
        r x * fourCellOddFiniteRetainedBasis i x) =
      ∫ x : ℝ in -1..1, f x := by
        apply intervalIntegral.integral_congr
        intro x _hx
        dsimp only [f]
        ring
    _ = 0 := hfull

theorem centeredRawLogBilinear_finiteRetainedBasis_tail_eq_zero
    {N : ℕ} (i : Fin (N + 1)) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (hmoment : (∫ x : ℝ in 0..1,
      fourCellOddFiniteRetainedBasis i x * r x) = 0) :
    centeredRawLogBilinear (fourCellOddFiniteRetainedBasis i) r = 0 := by
  have hraw := centeredRawLogBilinear_neg_shiftedLegendre_eq_moment_local
    (fourCellOddFiniteRetainedDegree i)
      (fourCellOddFiniteRetainedBasis i) r hr.continuous
        (centeredPullback_fourCellOddFiniteRetainedBasis i)
  have hfull := integral_neg_one_one_basis_mul_tail_eq_zero
    i r hr.continuous hodd hmoment
  rw [hfull] at hraw
  simpa using hraw

private theorem centeredRawLogBilinear_partialProfile_tail_eq_zero
    {N : ℕ} (a : Fin (N + 1) → ℝ)
    (s : Finset (Fin (N + 1))) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (hmoment : ∀ i : Fin (N + 1),
      (∫ x : ℝ in 0..1,
        fourCellOddFiniteRetainedBasis i x * r x) = 0) :
    centeredRawLogBilinear
      (s.sum fun i ↦ fun x ↦
        a i * fourCellOddFiniteRetainedBasis i x) r = 0 := by
  induction s using Finset.induction_on with
  | empty =>
      simp [centeredRawLogBilinear]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hu : ContDiff ℝ 1
          (fun x ↦ a i * fourCellOddFiniteRetainedBasis i x) :=
        contDiff_const.mul (contDiff_fourCellOddFiniteRetainedBasis i)
      have hv := contDiff_fourCellOddFiniteRetainedPartialProfile a s
      rw [centeredRawLogBilinear_add_left_local _ _ r
        (hu.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1))
        (hv.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1))
        (hr.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)),
        centeredRawLogBilinear_const_mul_left_local]
      rw [centeredRawLogBilinear_finiteRetainedBasis_tail_eq_zero
        i r hr hodd (hmoment i), ih]
      ring

theorem centeredRawLogBilinear_finiteRetainedProfile_tail_eq_zero
    (N : ℕ) (a : Fin (N + 1) → ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (hmoment : ∀ i : Fin (N + 1),
      (∫ x : ℝ in 0..1,
        fourCellOddFiniteRetainedBasis i x * r x) = 0) :
    centeredRawLogBilinear
      (fourCellOddFiniteRetainedProfile N a) r = 0 := by
  classical
  unfold fourCellOddFiniteRetainedProfile
  exact centeredRawLogBilinear_partialProfile_tail_eq_zero
    a Finset.univ r hr hodd hmoment

private theorem centeredPullback_centeredP1
    (t : ℝ) :
    centeredPullback centeredP1 t =
      -(shiftedLegendreReal 1).eval t := by
  unfold centeredPullback centeredP1
  calc
    2 * t - 1 =
        -(centeredShiftedLegendreReal 1).eval (2 * t - 1) := by
      rw [eval_centeredShiftedLegendreReal_one]
      ring
    _ = -(shiftedLegendreReal 1).eval (((2 * t - 1) + 1) / 2) := by
      rw [eval_centeredShiftedLegendreReal]
    _ = -(shiftedLegendreReal 1).eval t := by
      congr 2
      ring

theorem centeredRawLogBilinear_centeredP1_tail_eq_zero
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (h1 : centeredOddP1Coefficient r = 0) :
    centeredRawLogBilinear centeredP1 r = 0 := by
  have hraw := centeredRawLogBilinear_neg_shiftedLegendre_eq_moment_local
    1 centeredP1 r hr.continuous centeredPullback_centeredP1
  have hmoment : (∫ x : ℝ in -1..1, r x * centeredP1 x) = 0 := by
    unfold centeredOddP1Coefficient at h1
    nlinarith
  rw [hmoment] at hraw
  simpa using hraw

/-- The complete global singular row vanishes between `q51` and a genuine
`P53+` residual. -/
theorem centeredRawLogBilinear_fourCellOddQ51_P53Plus_eq_zero
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    centeredRawLogBilinear fourCellOddQ51 r = 0 := by
  have hP1 := centeredRawLogBilinear_centeredP1_tail_eq_zero
    r hr htail.1
  have hretained :=
    centeredRawLogBilinear_finiteRetainedProfile_tail_eq_zero
      24 fourCellOddP51RetainedSolution r hr hodd htail.2
  have hretained' : centeredRawLogBilinear
      (fourCellOddP51RetainedProfile fourCellOddP51RetainedSolution) r = 0 := by
    simpa only [fourCellOddP51RetainedProfile] using hretained
  rw [fourCellOddQ51_eq]
  rw [show (fun x ↦ centeredP1 x -
      fourCellOddP51RetainedProfile fourCellOddP51RetainedSolution x) =
      centeredP1 + fun x ↦ (-1 : ℝ) *
        fourCellOddP51RetainedProfile fourCellOddP51RetainedSolution x by
    funext x
    simp only [Pi.add_apply]
    ring]
  have hP1smooth : ContDiff ℝ 1 centeredP1 := by
    unfold centeredP1
    fun_prop
  have hprojsmooth : ContDiff ℝ 1
      (fourCellOddP51RetainedProfile fourCellOddP51RetainedSolution) := by
    simpa only [fourCellOddP51RetainedProfile] using
      contDiff_fourCellOddFiniteRetainedProfile
        24 fourCellOddP51RetainedSolution
  rw [centeredRawLogBilinear_add_left_local _ _ r
      (hP1smooth.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1))
      ((contDiff_const.mul hprojsmooth).contDiffOn.locallyLipschitzOn
        (convex_Icc (-1) 1))
      (hr.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)),
    centeredRawLogBilinear_const_mul_left_local, hP1, hretained']
  ring

theorem integral_zero_one_centeredP1_mul_P53Plus_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0) :
    (∫ x : ℝ in 0..1, centeredP1 x * r x) = 0 := by
  let f : ℝ → ℝ := fun x ↦ centeredP1 x * r x
  have hf : Continuous f := (by unfold f centeredP1; fun_prop)
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    rw [hodd]
    unfold centeredP1
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    f (hf.intervalIntegrable _ _) hfeven
  have hfull : (∫ x : ℝ in -1..1, f x) = 0 := by
    dsimp only [f]
    unfold centeredOddP1Coefficient at h1
    have horient : (∫ x : ℝ in -1..1,
        centeredP1 x * r x) =
        ∫ x : ℝ in -1..1, r x * centeredP1 x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      ring
    rw [horient]
    nlinarith
  rw [hfull] at hfold
  linarith

/-- The scalar mass row of `q51` also vanishes on the genuine tail. -/
theorem integral_zero_one_fourCellOddQ51_mul_P53Plus_eq_zero
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    (∫ x : ℝ in 0..1, fourCellOddQ51 x * r x) = 0 := by
  have hP1 := integral_zero_one_centeredP1_mul_P53Plus_eq_zero
    r hr.continuous hodd htail.1
  have hproj :=
    integral_zero_one_fourCellOddFiniteRetainedProfile_mul_tail_eq_zero
      24 fourCellOddP51RetainedSolution r hr.continuous htail.2
  have hproj' : (∫ x : ℝ in 0..1,
      fourCellOddP51RetainedProfile fourCellOddP51RetainedSolution x * r x) =
      0 := by
    simpa only [fourCellOddP51RetainedProfile] using hproj
  rw [fourCellOddQ51_eq]
  have hP1I : IntervalIntegrable
      (fun x : ℝ ↦ centeredP1 x * r x) volume 0 1 :=
    ((by unfold centeredP1; fun_prop : Continuous centeredP1).mul
      hr.continuous).intervalIntegrable _ _
  have hprojI : IntervalIntegrable
      (fun x : ℝ ↦
        fourCellOddP51RetainedProfile fourCellOddP51RetainedSolution x * r x)
      volume 0 1 :=
    ((contDiff_fourCellOddFiniteRetainedProfile
      24 fourCellOddP51RetainedSolution).continuous.mul hr.continuous)
        |>.intervalIntegrable _ _
  rw [show (fun x : ℝ ↦
      (centeredP1 x -
        fourCellOddP51RetainedProfile fourCellOddP51RetainedSolution x) *
          r x) = fun x ↦ centeredP1 x * r x -
            fourCellOddP51RetainedProfile
              fourCellOddP51RetainedSolution x * r x by
      funext x
      ring,
    intervalIntegral.integral_sub hP1I hprojI, hP1, hproj']
  ring

/-- On the P53+ space the raw-strip polarization is exactly the adverse
endpoint-strip polarization. -/
theorem fourCellOddRawStripCancellationPolarization_Q51_P53Plus_eq
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    fourCellOddRawStripCancellationPolarization fourCellOddQ51 r =
      -(1 / 2 : ℝ) *
        fourCellOddEndpointStripOddRawPolarization fourCellOddQ51 r := by
  rw [fourCellOddRawStripCancellationPolarization_eq_centered_sub_strip
      fourCellOddQ51 r contDiff_fourCellOddQ51 hr
        odd_fourCellOddQ51 hodd,
    centeredRawLogBilinear_fourCellOddQ51_P53Plus_eq_zero r hr hodd htail]
  ring

/-- Exact form-level row after both global singular and scalar mass
cancellations.  The remaining terms are precisely the upper-strip endpoint
row, endpoint potential, and the single smooth regular correlation. -/
theorem fourCellOddCoreLocalBilinear_Q51_P53Plus_eq_retained_regular
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    fourCellOddCoreLocalBilinear fourCellOddQ51 r =
      -(1 / 2 : ℝ) *
          fourCellOddEndpointStripOddRawPolarization fourCellOddQ51 r +
        fourCellOddRetainedPrimePotentialBilinear fourCellOddQ51 r -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              factorTwoCenteredCorrelationBilinear fourCellOddQ51 r t) := by
  rw [fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  unfold fourCellOddRetainedEndpointBilinear
    fourCellOddSignedMassRegularBilinear
  rw [fourCellOddRawStripCancellationPolarization_Q51_P53Plus_eq
      r hr hodd htail,
    integral_zero_one_fourCellOddQ51_mul_P53Plus_eq_zero r hr hodd htail]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51RawMassCancellationStructural
