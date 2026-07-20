import ArithmeticHodge.Analysis.YoshidaFourCellOddP51EndpointStripRepresenterStructural
import ArithmeticHodge.Analysis.ShiftedLegendreL2SpectralGap
import ArithmeticHodge.Analysis.ShiftedLegendreCenteredParity

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators InnerProductSpace unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51UpperStripTailStructural

noncomputable section

open ShiftedLegendreBasis
open ShiftedLegendreOrthogonality
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreL2Basis
open ShiftedLegendreL2SpectralGap
open ShiftedLegendreCenteredParity
open UnitIntervalLogEnergyAffine
open UnitIntervalIntegralBridge
open YoshidaFourCellOddP51EndpointStripRepresenterStructural

/-!
# The honest upper-strip tail at the P51 cutoff

The endpoint correction is polynomial on its physical strip, but extending it
by zero to the positive half introduces a genuine jump at `3/5`.  Consequently
it is not a finite Legendre packet.  This file realizes that discontinuous
density directly in `L²(0,1)`, removes every degree below `53` by the Hilbert
projection, and exposes the exact remaining norm and pairing.  No Legendre
coefficient is enumerated.
-/

/-- The physical upper strip inside the unit interval. -/
def fourCellOddP51UpperStrip : Set unitInterval :=
  {t | (3 / 5 : ℝ) < (t : ℝ)}

theorem measurableSet_fourCellOddP51UpperStrip :
    MeasurableSet fourCellOddP51UpperStrip := by
  exact measurableSet_lt measurable_const measurable_subtype_coe

/-- Continuous polynomial density before imposing its physical support. -/
def fourCellOddP51UpperCorrectionContinuous : C(unitInterval, ℝ) where
  toFun t := fourCellOddQ51UpperEndpointCorrection (t : ℝ)
  continuous_toFun :=
    continuous_fourCellOddQ51UpperEndpointCorrection.comp continuous_subtype_val

/-- The correction extended by zero below the physical cutoff.  The strict
inequality records the cutoff jump honestly; changing the single boundary
value would produce the same `L²` class. -/
def fourCellOddP51UpperStripDensityReal (x : ℝ) : ℝ :=
  (Ioi (3 / 5 : ℝ)).indicator fourCellOddQ51UpperEndpointCorrection x

def fourCellOddP51UpperStripDensity (t : unitInterval) : ℝ :=
  fourCellOddP51UpperStripDensityReal (t : ℝ)

theorem fourCellOddP51UpperStripDensity_apply (t : unitInterval) :
    fourCellOddP51UpperStripDensity t =
      fourCellOddP51UpperStrip.indicator
        fourCellOddP51UpperCorrectionContinuous t := by
  rfl

theorem memLp_fourCellOddP51UpperCorrectionContinuous :
    MemLp (⇑fourCellOddP51UpperCorrectionContinuous) 2
      (volume : Measure unitInterval) := by
  have hcompact : HasCompactSupport
      (⇑fourCellOddP51UpperCorrectionContinuous) :=
    isClosed_closure.isCompact
  exact fourCellOddP51UpperCorrectionContinuous.continuous.memLp_of_hasCompactSupport
    hcompact

theorem memLp_fourCellOddP51UpperStripDensity :
    MemLp fourCellOddP51UpperStripDensity 2
      (volume : Measure unitInterval) := by
  rw [show fourCellOddP51UpperStripDensity =
      fourCellOddP51UpperStrip.indicator
        fourCellOddP51UpperCorrectionContinuous by
    funext t
    exact fourCellOddP51UpperStripDensity_apply t]
  exact memLp_fourCellOddP51UpperCorrectionContinuous.indicator
    measurableSet_fourCellOddP51UpperStrip

/-- Canonical `L²(0,1)` realization of the supported correction. -/
def fourCellOddP51UpperStripL2 : UnitIntervalL2 :=
  memLp_fourCellOddP51UpperStripDensity.toLp
    fourCellOddP51UpperStripDensity

/-- Exact coefficient formula in the native shifted basis on the physical
positive half.  The actual centered `P53+` coordinates are constructed from
the odd extension below; this preliminary formula records the strip cutoff
without conflating the two coordinate systems. -/
theorem repr_fourCellOddP51UpperStripL2 (n : ℕ) :
    shiftedLegendreHilbertBasis.repr
        fourCellOddP51UpperStripL2 n =
      ‖shiftedLegendreL2 n‖⁻¹ *
        ∫ x : ℝ in 3 / 5..1,
          fourCellOddQ51UpperEndpointCorrection x *
            (shiftedLegendreReal n).eval x := by
  rw [fourCellOddP51UpperStripL2,
    shiftedLegendreHilbertBasis_repr_eq]
  apply congrArg (fun z : ℝ ↦ ‖shiftedLegendreL2 n‖⁻¹ * z)
  change (∫ t : unitInterval,
      (fun x : ℝ ↦ fourCellOddP51UpperStripDensityReal x *
        (shiftedLegendreReal n).eval x) (t : ℝ)) = _
  rw [integral_unitInterval_eq_intervalIntegral
    (fun x : ℝ ↦ fourCellOddP51UpperStripDensityReal x *
      (shiftedLegendreReal n).eval x)]
  let g : ℝ → ℝ := fun x ↦
    fourCellOddP51UpperStripDensityReal x *
      (shiftedLegendreReal n).eval x
  let q : ℝ → ℝ := fun x ↦
    fourCellOddQ51UpperEndpointCorrection x *
      (shiftedLegendreReal n).eval x
  have hq : IntervalIntegrable q volume 0 1 := by
    exact (continuous_fourCellOddQ51UpperEndpointCorrection.mul
      (shiftedLegendreReal n).continuous).intervalIntegrable _ _
  have hg : IntervalIntegrable g volume 0 1 := by
    have hgEq : g = (Ioi (3 / 5 : ℝ)).indicator q := by
      funext x
      by_cases hx : (3 / 5 : ℝ) < x <;>
        simp [g, q, fourCellOddP51UpperStripDensityReal, hx]
    rw [hgEq]
    apply hq.mono_fun
    · exact hq.def'.aestronglyMeasurable.indicator measurableSet_Ioi
    · exact Filter.Eventually.of_forall fun x ↦
        norm_indicator_le_norm_self _ _
  have hgLower : IntervalIntegrable g volume 0 (3 / 5) := by
    exact hg.mono_set (by
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
      exact ⟨hx.1, hx.2.trans (by norm_num)⟩)
  have hgUpper : IntervalIntegrable g volume (3 / 5) 1 := by
    exact hg.mono_set (by
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
      exact ⟨(by linarith [hx.1]), hx.2⟩)
  have hLower : (∫ x : ℝ in 0..3 / 5, g x) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ : ℝ ↦ 0)]
    · simp
    · intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
      simp [g, fourCellOddP51UpperStripDensityReal,
        not_lt.mpr hx.2]
  have hUpper : (∫ x : ℝ in 3 / 5..1, g x) =
      ∫ x : ℝ in 3 / 5..1, q x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with x
    intro hx
    rw [uIoc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    simp [g, q, fourCellOddP51UpperStripDensityReal, hx.1]
  change (∫ x : ℝ in 0..1, g x) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hgLower hgUpper,
    hLower, zero_add, hUpper]

/-! ## Centered odd realization used by the P53+ tail -/

/-- Odd extension of the physical positive-half correction.  On the
centered interval it is supported on `[-1,-3/5) ∪ (3/5,1]`. -/
def fourCellOddP51UpperStripOddExtension (x : ℝ) : ℝ :=
  if 0 ≤ x then fourCellOddP51UpperStripDensityReal x
  else -fourCellOddP51UpperStripDensityReal (-x)

theorem odd_fourCellOddP51UpperStripOddExtension :
    Function.Odd fourCellOddP51UpperStripOddExtension := by
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hnx : 0 ≤ -x := by linarith
    have hx0 : ¬0 ≤ x := not_le.mpr hx
    simp [fourCellOddP51UpperStripOddExtension, hnx, hx0]
  · have hcut : ¬ (3 / 5 : ℝ) < 0 := by norm_num
    simp [fourCellOddP51UpperStripOddExtension,
      fourCellOddP51UpperStripDensityReal, hcut]
  · have hx0 : 0 ≤ x := hx.le
    have hnx : ¬0 ≤ -x := by linarith
    simp [fourCellOddP51UpperStripOddExtension, hx0, hnx]

/-- Canonical centered pullback of the odd extension. -/
def fourCellOddP51UpperStripOddPullback (t : unitInterval) : ℝ :=
  centeredPullback fourCellOddP51UpperStripOddExtension (t : ℝ)

theorem fourCellOddP51UpperStripOddPullback_symm (t : unitInterval) :
    fourCellOddP51UpperStripOddPullback (unitInterval.symm t) =
      -fourCellOddP51UpperStripOddPullback t := by
  exact centeredPullback_symm_of_odd
    fourCellOddP51UpperStripOddExtension
    odd_fourCellOddP51UpperStripOddExtension t

/-- Positive and negative pullback support pieces. -/
def fourCellOddP51UpperPullbackSet : Set unitInterval :=
  {t | (4 / 5 : ℝ) < (t : ℝ)}

def fourCellOddP51LowerPullbackSet : Set unitInterval :=
  {t | (t : ℝ) < (1 / 5 : ℝ)}

theorem measurableSet_fourCellOddP51UpperPullbackSet :
    MeasurableSet fourCellOddP51UpperPullbackSet := by
  exact measurableSet_lt measurable_const measurable_subtype_coe

theorem measurableSet_fourCellOddP51LowerPullbackSet :
    MeasurableSet fourCellOddP51LowerPullbackSet := by
  exact measurableSet_lt measurable_subtype_coe measurable_const

def fourCellOddP51UpperPullbackContinuous : C(unitInterval, ℝ) where
  toFun t := fourCellOddQ51UpperEndpointCorrection (2 * (t : ℝ) - 1)
  continuous_toFun :=
    continuous_fourCellOddQ51UpperEndpointCorrection.comp (by fun_prop)

def fourCellOddP51LowerPullbackContinuous : C(unitInterval, ℝ) where
  toFun t := -fourCellOddQ51UpperEndpointCorrection (1 - 2 * (t : ℝ))
  continuous_toFun :=
    (continuous_fourCellOddQ51UpperEndpointCorrection.comp (by fun_prop)).neg

theorem fourCellOddP51UpperStripOddPullback_eq_indicators :
    fourCellOddP51UpperStripOddPullback =
      fourCellOddP51UpperPullbackSet.indicator
          fourCellOddP51UpperPullbackContinuous +
        fourCellOddP51LowerPullbackSet.indicator
          fourCellOddP51LowerPullbackContinuous := by
  funext t
  unfold fourCellOddP51UpperStripOddPullback centeredPullback
    fourCellOddP51UpperStripOddExtension
    fourCellOddP51UpperStripDensityReal
    fourCellOddP51UpperPullbackSet fourCellOddP51LowerPullbackSet
    fourCellOddP51UpperPullbackContinuous
    fourCellOddP51LowerPullbackContinuous
  rw [Pi.add_apply]
  by_cases hcenter : 0 ≤ 2 * (t : ℝ) - 1
  · have hnotLower : ¬ (t : ℝ) < 1 / 5 := by linarith
    by_cases hupper : (4 / 5 : ℝ) < (t : ℝ)
    · have hsupport : (3 / 5 : ℝ) < 2 * (t : ℝ) - 1 := by
        linarith
      have hsupportMem : 2 * (t : ℝ) - 1 ∈ Ioi (3 / 5 : ℝ) :=
        hsupport
      have hupperMem : t ∈ {s : unitInterval | (4 / 5 : ℝ) < (s : ℝ)} :=
        hupper
      have hnotLowerMem : t ∉ {s : unitInterval | (s : ℝ) < (1 / 5 : ℝ)} :=
        hnotLower
      rw [if_pos hcenter]
      rw [Set.indicator_of_mem hsupportMem]
      rw [Set.indicator_of_mem hupperMem,
        Set.indicator_of_notMem hnotLowerMem]
      simp
    · have hnotSupport : ¬ (3 / 5 : ℝ) < 2 * (t : ℝ) - 1 := by
        linarith
      have hnotSupportMem : 2 * (t : ℝ) - 1 ∉ Ioi (3 / 5 : ℝ) :=
        hnotSupport
      have hnotUpperMem : t ∉ {s : unitInterval | (4 / 5 : ℝ) < (s : ℝ)} :=
        hupper
      have hnotLowerMem : t ∉ {s : unitInterval | (s : ℝ) < (1 / 5 : ℝ)} :=
        hnotLower
      rw [if_pos hcenter]
      rw [Set.indicator_of_notMem hnotSupportMem]
      rw [Set.indicator_of_notMem hnotUpperMem,
        Set.indicator_of_notMem hnotLowerMem]
      simp
  · have hnotUpper : ¬ (4 / 5 : ℝ) < (t : ℝ) := by linarith
    by_cases hlower : (t : ℝ) < (1 / 5 : ℝ)
    · have hsupport : (3 / 5 : ℝ) < -(2 * (t : ℝ) - 1) := by
        linarith
      have hsupportMem : -(2 * (t : ℝ) - 1) ∈ Ioi (3 / 5 : ℝ) :=
        hsupport
      have hnotUpperMem : t ∉ {s : unitInterval | (4 / 5 : ℝ) < (s : ℝ)} :=
        hnotUpper
      have hlowerMem : t ∈ {s : unitInterval | (s : ℝ) < (1 / 5 : ℝ)} :=
        hlower
      rw [if_neg hcenter]
      rw [Set.indicator_of_mem hsupportMem]
      rw [Set.indicator_of_notMem hnotUpperMem,
        Set.indicator_of_mem hlowerMem]
      simp only [ContinuousMap.coe_mk, zero_add]
      congr 2
      ring
    · have hnotSupport : ¬ (3 / 5 : ℝ) < -(2 * (t : ℝ) - 1) := by
        linarith
      have hnotSupportMem : -(2 * (t : ℝ) - 1) ∉ Ioi (3 / 5 : ℝ) :=
        hnotSupport
      have hnotUpperMem : t ∉ {s : unitInterval | (4 / 5 : ℝ) < (s : ℝ)} :=
        hnotUpper
      have hnotLowerMem : t ∉ {s : unitInterval | (s : ℝ) < (1 / 5 : ℝ)} :=
        hlower
      rw [if_neg hcenter]
      rw [Set.indicator_of_notMem hnotSupportMem]
      rw [Set.indicator_of_notMem hnotUpperMem,
        Set.indicator_of_notMem hnotLowerMem]
      simp

private theorem memLp_continuousMap_two (f : C(unitInterval, ℝ)) :
    MemLp (⇑f) 2 (volume : Measure unitInterval) := by
  have hcompact : HasCompactSupport (⇑f) := isClosed_closure.isCompact
  exact f.continuous.memLp_of_hasCompactSupport hcompact

theorem memLp_fourCellOddP51UpperStripOddPullback :
    MemLp fourCellOddP51UpperStripOddPullback 2
      (volume : Measure unitInterval) := by
  rw [fourCellOddP51UpperStripOddPullback_eq_indicators]
  exact ((memLp_continuousMap_two
      fourCellOddP51UpperPullbackContinuous).indicator
        measurableSet_fourCellOddP51UpperPullbackSet).add
    ((memLp_continuousMap_two
      fourCellOddP51LowerPullbackContinuous).indicator
        measurableSet_fourCellOddP51LowerPullbackSet)

/-- The actual centered odd `L²` source generated by the upper strip. -/
def fourCellOddP51UpperStripOddL2 : UnitIntervalL2 :=
  memLp_fourCellOddP51UpperStripOddPullback.toLp
    fourCellOddP51UpperStripOddPullback

/-- Every coefficient of the centered source is the exact centered Legendre
pairing with the odd extension, including the affine Jacobian `1/2`. -/
theorem repr_fourCellOddP51UpperStripOddL2 (n : ℕ) :
    shiftedLegendreHilbertBasis.repr
        fourCellOddP51UpperStripOddL2 n =
      ‖shiftedLegendreL2 n‖⁻¹ * (1 / 2 : ℝ) *
        (∫ x : ℝ in -1..1,
          fourCellOddP51UpperStripOddExtension x *
            (centeredShiftedLegendreReal n).eval x) := by
  rw [fourCellOddP51UpperStripOddL2,
    shiftedLegendreHilbertBasis_repr_eq]
  rw [mul_assoc]
  apply congrArg (fun z : ℝ ↦ ‖shiftedLegendreL2 n‖⁻¹ * z)
  calc
    (∫ t : unitInterval,
        fourCellOddP51UpperStripOddPullback t *
          (shiftedLegendreReal n).eval (t : ℝ)) =
      ∫ t : unitInterval,
        (fun x : ℝ ↦ fourCellOddP51UpperStripOddExtension x *
          (centeredShiftedLegendreReal n).eval x)
            (2 * (t : ℝ) - 1) := by
      apply integral_congr_ae
      filter_upwards [] with t
      unfold fourCellOddP51UpperStripOddPullback centeredPullback
      rw [eval_centeredShiftedLegendreReal]
      congr 2
      ring
    _ = ∫ t : ℝ in 0..1,
        (fun x : ℝ ↦ fourCellOddP51UpperStripOddExtension x *
          (centeredShiftedLegendreReal n).eval x) (2 * t - 1) := by
      exact integral_unitInterval_eq_intervalIntegral
        (fun t : ℝ ↦
          (fun x : ℝ ↦ fourCellOddP51UpperStripOddExtension x *
            (centeredShiftedLegendreReal n).eval x) (2 * t - 1))
    _ = (1 / 2 : ℝ) *
        (∫ x : ℝ in -1..1,
          fourCellOddP51UpperStripOddExtension x *
            (centeredShiftedLegendreReal n).eval x) := by
      exact integral_comp_two_mul_sub_one
        (fun x : ℝ ↦ fourCellOddP51UpperStripOddExtension x *
          (centeredShiftedLegendreReal n).eval x)

/-- The supported source has no even centered Legendre coordinates. -/
theorem repr_fourCellOddP51UpperStripOddL2_eq_zero_of_even
    (n : ℕ) (hn : Even n) :
    shiftedLegendreHilbertBasis.repr
        fourCellOddP51UpperStripOddL2 n = 0 := by
  exact shiftedLegendreHilbertBasis_repr_eq_zero_of_symm_neg_of_even
    fourCellOddP51UpperStripOddPullback
    memLp_fourCellOddP51UpperStripOddPullback
    fourCellOddP51UpperStripOddPullback_symm n hn

private theorem repr_shiftedLegendrePartialProjection
    (F : UnitIntervalL2) (N n : ℕ) :
    shiftedLegendreHilbertBasis.repr
        (shiftedLegendrePartialProjection F N) n =
      if n < N then shiftedLegendreHilbertBasis.repr F n else 0 := by
  rw [shiftedLegendreHilbertBasis.repr_apply_apply]
  unfold shiftedLegendrePartialProjection
  rw [inner_sum]
  by_cases hn : n < N
  · rw [if_pos hn]
    have hnmem : n ∈ Finset.range N := Finset.mem_range.mpr hn
    rw [Finset.sum_eq_single n]
    · rw [inner_smul_right,
        (orthonormal_iff_ite.mp
          shiftedLegendreHilbertBasis.orthonormal n n)]
      simp
    · intro b hb hbn
      rw [inner_smul_right,
        (orthonormal_iff_ite.mp
          shiftedLegendreHilbertBasis.orthonormal n b),
        if_neg (Ne.symm hbn)]
      simp
    · exact fun hnnot ↦ (hnnot hnmem).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    rw [inner_smul_right,
      (orthonormal_iff_ite.mp
        shiftedLegendreHilbertBasis.orthonormal n b)]
    rw [if_neg]
    · simp
    · intro hnb
      subst b
      exact hn (Finset.mem_range.mp hb)

/-- The first P53+ centered degree is `53`; all degrees `<53` are removed
at once by the exact Hilbert projection. -/
def fourCellOddP51UpperStripP53PlusL2 : UnitIntervalL2 :=
  fourCellOddP51UpperStripOddL2 -
    shiftedLegendrePartialProjection
      fourCellOddP51UpperStripOddL2 53

theorem repr_fourCellOddP51UpperStripP53PlusL2 (n : ℕ) :
    shiftedLegendreHilbertBasis.repr
        fourCellOddP51UpperStripP53PlusL2 n =
      if n < 53 then 0
      else shiftedLegendreHilbertBasis.repr
        fourCellOddP51UpperStripOddL2 n := by
  unfold fourCellOddP51UpperStripP53PlusL2
  rw [shiftedLegendreHilbertBasis.repr_apply_apply, inner_sub_right,
    ← shiftedLegendreHilbertBasis.repr_apply_apply,
    ← shiftedLegendreHilbertBasis.repr_apply_apply,
    repr_shiftedLegendrePartialProjection]
  by_cases hn : n < 53 <;> simp [hn]

theorem repr_fourCellOddP51UpperStripP53PlusL2_eq_zero_of_lt
    (n : ℕ) (hn : n < 53) :
    shiftedLegendreHilbertBasis.repr
        fourCellOddP51UpperStripP53PlusL2 n = 0 := by
  rw [repr_fourCellOddP51UpperStripP53PlusL2, if_pos hn]

theorem repr_fourCellOddP51UpperStripP53PlusL2_eq_zero_of_even
    (n : ℕ) (hn : Even n) :
    shiftedLegendreHilbertBasis.repr
        fourCellOddP51UpperStripP53PlusL2 n = 0 := by
  rw [repr_fourCellOddP51UpperStripP53PlusL2]
  split_ifs
  · rfl
  · exact repr_fourCellOddP51UpperStripOddL2_eq_zero_of_even n hn

/-- The finite projection captures exactly the partial Parseval mass. -/
private theorem inner_shiftedLegendrePartialProjection_eq_partialNormSq
    (F : UnitIntervalL2) (N : ℕ) :
    inner ℝ F (shiftedLegendrePartialProjection F N) =
      shiftedLegendrePartialNormSq F N := by
  rw [shiftedLegendrePartialProjection, inner_sum,
    shiftedLegendrePartialNormSq]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [real_inner_smul_right]
  have hrepr : inner ℝ F (shiftedLegendreHilbertBasis n) =
      shiftedLegendreHilbertBasis.repr F n := by
    rw [real_inner_comm]
    exact (shiftedLegendreHilbertBasis.repr_apply_apply F n).symm
  rw [hrepr]
  ring

/-- Exact Pythagorean norm of the supported `P53+` tail.  Thus the whole
upper-strip problem is reduced to one scalar: the full supported mass minus
the first fifty-three Parseval coordinates. -/
theorem norm_sq_fourCellOddP51UpperStripP53PlusL2 :
    ‖fourCellOddP51UpperStripP53PlusL2‖ ^ 2 =
      ‖fourCellOddP51UpperStripOddL2‖ ^ 2 -
        shiftedLegendrePartialNormSq
          fourCellOddP51UpperStripOddL2 53 := by
  unfold fourCellOddP51UpperStripP53PlusL2
  rw [norm_sub_sq_real,
    inner_shiftedLegendrePartialProjection_eq_partialNormSq,
    norm_sq_shiftedLegendrePartialProjection]
  ring

/-- Removing the complete low projection does not change pairing against a
genuine degree-`53+` Hilbert tail. -/
theorem inner_fourCellOddP51UpperStripOddL2_eq_P53PlusL2
    (R : UnitIntervalL2)
    (hR : ∀ n : ℕ, n < 53 →
      shiftedLegendreHilbertBasis.repr R n = 0) :
    inner ℝ fourCellOddP51UpperStripOddL2 R =
      inner ℝ fourCellOddP51UpperStripP53PlusL2 R := by
  have hproj : inner ℝ
      (shiftedLegendrePartialProjection
        fourCellOddP51UpperStripOddL2 53) R = 0 := by
    rw [shiftedLegendrePartialProjection, sum_inner]
    apply Finset.sum_eq_zero
    intro n hn
    rw [real_inner_smul_left]
    have hrepr : inner ℝ (shiftedLegendreHilbertBasis n) R =
        shiftedLegendreHilbertBasis.repr R n :=
      (shiftedLegendreHilbertBasis.repr_apply_apply R n).symm
    rw [hrepr, hR n (Finset.mem_range.mp hn), mul_zero]
  unfold fourCellOddP51UpperStripP53PlusL2
  rw [inner_sub_left, hproj, sub_zero]

/-- Non-enumerative Cauchy contraction for the honest upper-strip tail. -/
theorem sq_inner_fourCellOddP51UpperStripOddL2_le_P53Plus_norm
    (R : UnitIntervalL2)
    (hR : ∀ n : ℕ, n < 53 →
      shiftedLegendreHilbertBasis.repr R n = 0) :
    inner ℝ fourCellOddP51UpperStripOddL2 R ^ 2 ≤
      ‖fourCellOddP51UpperStripP53PlusL2‖ ^ 2 * ‖R‖ ^ 2 := by
  rw [inner_fourCellOddP51UpperStripOddL2_eq_P53PlusL2 R hR]
  have h := abs_real_inner_le_norm
    fourCellOddP51UpperStripP53PlusL2 R
  calc
    inner ℝ fourCellOddP51UpperStripP53PlusL2 R ^ 2 =
        |inner ℝ fourCellOddP51UpperStripP53PlusL2 R| ^ 2 := by
      rw [sq_abs]
    _ ≤ (‖fourCellOddP51UpperStripP53PlusL2‖ * ‖R‖) ^ 2 := by
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = ‖fourCellOddP51UpperStripP53PlusL2‖ ^ 2 * ‖R‖ ^ 2 := by
      ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51UpperStripTailStructural
