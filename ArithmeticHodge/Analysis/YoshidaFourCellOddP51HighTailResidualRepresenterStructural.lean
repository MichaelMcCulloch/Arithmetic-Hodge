import ArithmeticHodge.Analysis.YoshidaFourCellOddP51Polynomial18TailStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP51UpperStripTailStructural

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators InnerProductSpace unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailResidualRepresenterStructural

noncomputable section

open ShiftedLegendreL2Basis
open ShiftedLegendreL2SpectralGap
open ShiftedLegendreCenteredLowModes
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaEndpointOcticPotential
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialOddTailParsevalStructural
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFourCellEvenZeroCoshCoupledCoreStructural
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP51EndpointStripRepresenterStructural
open YoshidaFourCellOddP51EndpointPotentialTailConcreteStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51Kernel18RowDecompositionStructural
open YoshidaFourCellOddP51Kernel18ErrorBudgetStructural
open YoshidaFourCellOddP51Polynomial18TailStructural
open YoshidaFourCellOddP51TailBudgetAssemblyStructural
open YoshidaFourCellOddP51UpperStripTailStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural

/-!
# One honest Hilbert representer for the complete P51 high-tail row

The endpoint potential, the polynomial regular row, and the discontinuous
upper-strip correction already have separate `L²(0,1)` realizations.  This
file assembles their genuine `P53+` projections before taking a norm.  Thus
all cancellation between the three analytic channels is retained, and the
universal tail estimate reduces to one scalar norm inequality.
-/

private theorem inner_toLp_eq_integral_mul
    (f g : unitInterval → ℝ) (hf : MemLp f 2) (hg : MemLp g 2) :
    inner ℝ (hf.toLp f) (hg.toLp g) =
      ∫ t : unitInterval, f t * g t := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with t hft hgt
  rw [hft, hgt]
  change g t * f t = f t * g t
  ring

private theorem coe_cutoffEightPotentialLegendreSourceL2_ae
    (m : ℕ) :
    ((cutoffEightPotentialLegendreSourceL2 m : UnitIntervalL2) :
        unitInterval → ℝ) =ᵐ[volume]
      fun t : unitInterval ↦
        centeredPullback (cutoffEightPotentialLegendreSource m) (t : ℝ) := by
  unfold cutoffEightPotentialLegendreSourceL2
  exact MemLp.coeFn_toLp _

private theorem inner_oddEndpointPotentialLegendreSourceL2_centeredPullbackL2
    (i : ℕ) (r : ℝ → ℝ) (hr : Continuous r)
    (hodd : Function.Odd r) :
    inner ℝ (oddEndpointPotentialLegendreSourceL2 i)
        (centeredPullbackL2 r hr) =
      ∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x *
          (centeredShiftedLegendreReal (oddLegendreIndex i)).eval x * r x := by
  let S : ℝ → ℝ := cutoffEightPotentialLegendreSource
    (oddLegendreIndex i)
  have hsourceAe := coe_cutoffEightPotentialLegendreSourceL2_ae
    (oddLegendreIndex i)
  have hrAe := (centeredPullback_memLp_two r hr).coeFn_toLp
  have hinner :
      inner ℝ (oddEndpointPotentialLegendreSourceL2 i)
          (centeredPullbackL2 r hr) =
        ∫ t : unitInterval,
          centeredPullback S (t : ℝ) * centeredPullback r (t : ℝ) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hsourceAe, hrAe] with t hsource hrval
    have hrval' : ((centeredPullbackL2 r hr : unitInterval → ℝ) t) =
        centeredPullback r (t : ℝ) := by
      simpa only [centeredPullbackL2] using hrval
    have hsource' :
        ((oddEndpointPotentialLegendreSourceL2 i : unitInterval → ℝ) t) =
          centeredPullback S (t : ℝ) := by
      simpa only [oddEndpointPotentialLegendreSourceL2, S] using hsource
    rw [hrval', hsource']
    change centeredPullback r (t : ℝ) * centeredPullback S (t : ℝ) = _
    ring
  have hfull :
      (∫ t : unitInterval,
        centeredPullback S (t : ℝ) * centeredPullback r (t : ℝ)) =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, S x * r x := by
    calc
      _ = ∫ t : ℝ in 0..1, S (2 * t - 1) * r (2 * t - 1) := by
        change (∫ t : unitInterval,
            (fun s : ℝ ↦ S (2 * s - 1) * r (2 * s - 1)) (t : ℝ)) = _
        exact integral_unitInterval_eq_intervalIntegral
          (fun s : ℝ ↦ S (2 * s - 1) * r (2 * s - 1))
      _ = (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, S x * r x := by
        exact integral_comp_two_mul_sub_one (fun x : ℝ ↦ S x * r x)
  have hSodd : Function.Odd S := by
    intro x
    dsimp only [S]
    unfold cutoffEightPotentialLegendreSource yoshidaEndpointPotential
    rw [eval_centeredShiftedLegendreReal_neg]
    have hpow : (-1 : ℝ) ^ oddLegendreIndex i = -1 := by
      unfold oddLegendreIndex
      rw [pow_add, pow_mul]
      norm_num
    rw [hpow]
    ring
  have hSI : IntervalIntegrable (fun x : ℝ ↦ S x * r x)
      volume (-1) 1 := by
    dsimp only [S]
    unfold cutoffEightPotentialLegendreSource
    exact
      YoshidaEndpointEvenTailRepresenter.intervalIntegrable_endpointPotential_mul
        (fun x : ℝ ↦
          (centeredShiftedLegendreReal (oddLegendreIndex i)).eval x)
        r (centeredShiftedLegendreReal (oddLegendreIndex i)).continuous hr
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ S x * r x) hSI
    (by
      intro x
      change S (-x) * r (-x) = S x * r x
      rw [hSodd x, hodd x]
      ring)
  calc
    inner ℝ (oddEndpointPotentialLegendreSourceL2 i)
        (centeredPullbackL2 r hr) =
        (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, S x * r x :=
      hinner.trans hfull
    _ = ∫ x : ℝ in 0..1, S x * r x := by rw [hfold]; ring
    _ = _ := by rfl

/-- The concrete endpoint-potential Hilbert source has exactly the
production sign and positive-half normalization. -/
theorem inner_fourCellOddQ51ScaledEndpointPotentialSourceL2_centeredPullbackL2
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r) :
    inner ℝ fourCellOddQ51ScaledEndpointPotentialSourceL2
        (centeredPullbackL2 r hr) =
      (93 / 50 : ℝ) * ∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x * fourCellOddQ51 x * r x := by
  classical
  have htermI (i : Fin 26) : IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddQ51OddLegendreCoefficients i *
        (yoshidaEndpointPotential x *
          (centeredShiftedLegendreReal (oddLegendreIndex i)).eval x * r x))
      volume 0 1 := by
    have hfull :=
      YoshidaEndpointEvenTailRepresenter.intervalIntegrable_endpointPotential_mul
        (fun x : ℝ ↦
          (centeredShiftedLegendreReal (oddLegendreIndex i)).eval x)
        r (centeredShiftedLegendreReal (oddLegendreIndex i)).continuous hr
    exact (hfull.mono_set (by
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact ⟨by linarith [hx.1], hx.2⟩)).const_mul _
  rw [fourCellOddQ51ScaledEndpointPotentialSourceL2,
    oddEndpointPotentialFiniteProfileSourceL2,
    real_inner_smul_left, sum_inner]
  simp_rw [real_inner_smul_left,
    inner_oddEndpointPotentialLegendreSourceL2_centeredPullbackL2 _ r hr hodd]
  have hprofile := fourCellOddP51CanonicalOddLegendreProfile_q51Coefficients
  have hsum :
      (∑ i : Fin 26, fourCellOddQ51OddLegendreCoefficients i *
        ∫ x : ℝ in 0..1,
          yoshidaEndpointPotential x *
            (centeredShiftedLegendreReal (oddLegendreIndex i)).eval x * r x) =
      ∫ x : ℝ in 0..1,
        -(yoshidaEndpointPotential x * fourCellOddQ51 x * r x) := by
    rw [show (∑ i : Fin 26, fourCellOddQ51OddLegendreCoefficients i *
        ∫ x : ℝ in 0..1,
          yoshidaEndpointPotential x *
            (centeredShiftedLegendreReal (oddLegendreIndex i)).eval x * r x) =
        ∑ i : Fin 26, ∫ x : ℝ in 0..1,
          fourCellOddQ51OddLegendreCoefficients i *
            (yoshidaEndpointPotential x *
              (centeredShiftedLegendreReal (oddLegendreIndex i)).eval x *
                r x) by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [intervalIntegral.integral_const_mul]]
    rw [← intervalIntegral.integral_finset_sum (fun i _hi ↦ htermI i)]
    apply intervalIntegral.integral_congr
    intro x _hx
    calc
      (∑ i : Fin 26, fourCellOddQ51OddLegendreCoefficients i *
          (yoshidaEndpointPotential x *
            (centeredShiftedLegendreReal (oddLegendreIndex i)).eval x * r x)) =
          yoshidaEndpointPotential x * r x *
            (∑ i : Fin 26, fourCellOddQ51OddLegendreCoefficients i *
              (centeredShiftedLegendreReal (oddLegendreIndex i)).eval x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = -(yoshidaEndpointPotential x * fourCellOddQ51 x * r x) := by
        have hx := congrFun hprofile x
        unfold fourCellOddP51CanonicalOddLegendreProfile at hx
        rw [hx]
        ring
  rw [hsum, intervalIntegral.integral_neg]
  ring

/-! ## Pairing of the supported upper-strip source -/

private theorem intervalIntegrable_upperStripOddExtension_mul
    (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddP51UpperStripOddExtension x * r x)
      volume (-1) 1 := by
  let U : ℝ → ℝ := fourCellOddQ51UpperEndpointCorrection
  let qplus : ℝ → ℝ := fun x ↦ U x * r x
  let qminus : ℝ → ℝ := fun x ↦ (-U (-x)) * r x
  let g : ℝ → ℝ :=
    (Ioi (3 / 5 : ℝ)).indicator qplus +
      (Iio (-(3 / 5 : ℝ))).indicator qminus
  have hqplus : IntervalIntegrable qplus volume (-1) 1 := by
    exact (continuous_fourCellOddQ51UpperEndpointCorrection.mul hr)
      |>.intervalIntegrable _ _
  have hqminus : IntervalIntegrable qminus volume (-1) 1 := by
    exact (((continuous_fourCellOddQ51UpperEndpointCorrection.comp
      continuous_neg).neg).mul hr).intervalIntegrable _ _
  have hg : IntervalIntegrable g volume (-1) 1 := by
    have hplus : IntervalIntegrable
        ((Ioi (3 / 5 : ℝ)).indicator qplus) volume (-1) 1 := by
      apply hqplus.mono_fun
      · exact hqplus.def'.aestronglyMeasurable.indicator measurableSet_Ioi
      · exact Filter.Eventually.of_forall fun x ↦
          norm_indicator_le_norm_self _ _
    have hminus : IntervalIntegrable
        ((Iio (-(3 / 5 : ℝ))).indicator qminus) volume (-1) 1 := by
      apply hqminus.mono_fun
      · exact hqminus.def'.aestronglyMeasurable.indicator measurableSet_Iio
      · exact Filter.Eventually.of_forall fun x ↦
          norm_indicator_le_norm_self _ _
    exact hplus.add hminus
  apply hg.congr
  intro x hx
  dsimp only [g, qplus, qminus, U]
  unfold fourCellOddP51UpperStripOddExtension
    fourCellOddP51UpperStripDensityReal
  by_cases hx0 : 0 ≤ x
  · have hnotneg : ¬ x < -(3 / 5 : ℝ) := by linarith
    by_cases hcut : (3 / 5 : ℝ) < x <;>
      simp [hx0, hnotneg, hcut]
  · have hxneg : x < 0 := lt_of_not_ge hx0
    have hnotpos : ¬ (3 / 5 : ℝ) < x := by linarith
    by_cases hcut : x < -(3 / 5 : ℝ)
    · have hsupport : (3 / 5 : ℝ) < -x := by linarith
      simp [hx0, hnotpos, hcut, hsupport]
    · have hnSupport : ¬ (3 / 5 : ℝ) < -x := by linarith
      simp [hx0, hnotpos, hcut, hnSupport]

/-- The centered odd upper-strip source pairs exactly as the physical
positive-half upper-strip correction. -/
theorem inner_fourCellOddP51UpperStripOddL2_centeredPullbackL2
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r) :
    inner ℝ fourCellOddP51UpperStripOddL2 (centeredPullbackL2 r hr) =
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddQ51UpperEndpointCorrection x * r x := by
  have hinner := inner_toLp_eq_integral_mul
    fourCellOddP51UpperStripOddPullback
    (fun t : unitInterval ↦ centeredPullback r (t : ℝ))
    memLp_fourCellOddP51UpperStripOddPullback
    (centeredPullback_memLp_two r hr)
  have hfull :
      (∫ t : unitInterval,
        fourCellOddP51UpperStripOddPullback t *
          centeredPullback r (t : ℝ)) =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        fourCellOddP51UpperStripOddExtension x * r x := by
    calc
      _ = ∫ t : ℝ in 0..1,
          fourCellOddP51UpperStripOddExtension (2 * t - 1) *
            r (2 * t - 1) := by
        change (∫ t : unitInterval,
            (fun s : ℝ ↦
              fourCellOddP51UpperStripOddExtension (2 * s - 1) *
                r (2 * s - 1)) (t : ℝ)) = _
        exact integral_unitInterval_eq_intervalIntegral
          (fun s : ℝ ↦
            fourCellOddP51UpperStripOddExtension (2 * s - 1) *
              r (2 * s - 1))
      _ = (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
          fourCellOddP51UpperStripOddExtension x * r x := by
        exact integral_comp_two_mul_sub_one
          (fun x : ℝ ↦ fourCellOddP51UpperStripOddExtension x * r x)
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ fourCellOddP51UpperStripOddExtension x * r x)
    (intervalIntegrable_upperStripOddExtension_mul r hr)
    (by
      intro x
      change fourCellOddP51UpperStripOddExtension (-x) * r (-x) =
        fourCellOddP51UpperStripOddExtension x * r x
      rw [odd_fourCellOddP51UpperStripOddExtension x, hodd x]
      ring)
  have hpositive :
      (∫ x : ℝ in 0..1,
        fourCellOddP51UpperStripOddExtension x * r x) =
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddQ51UpperEndpointCorrection x * r x := by
    let g : ℝ → ℝ := fun x ↦
      fourCellOddP51UpperStripOddExtension x * r x
    have hg : IntervalIntegrable g volume 0 1 :=
      (intervalIntegrable_upperStripOddExtension_mul r hr).mono_set (by
        intro x hx
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        exact ⟨by linarith [hx.1], hx.2⟩)
    have hgLower : IntervalIntegrable g volume 0 (3 / 5) :=
      hg.mono_set (by
        intro x hx
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact ⟨hx.1, hx.2.trans (by norm_num)⟩)
    have hgUpper : IntervalIntegrable g volume (3 / 5) 1 :=
      hg.mono_set (by
        intro x hx
        rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact ⟨by linarith [hx.1], hx.2⟩)
    rw [← intervalIntegral.integral_add_adjacent_intervals hgLower hgUpper]
    have hlower : (∫ x : ℝ in 0..3 / 5, g x) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ : ℝ ↦ 0)]
      · simp
      · intro x hx
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
        simp [g, fourCellOddP51UpperStripOddExtension,
          fourCellOddP51UpperStripDensityReal, hx.1,
          not_lt.mpr hx.2]
    rw [hlower, zero_add]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (3 / 5 : ℝ)] with x hxne
    intro hx
    rw [uIoc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    simp [g, fourCellOddP51UpperStripOddExtension,
      fourCellOddP51UpperStripDensityReal, hx0, hx.1]
  simpa only [fourCellOddP51UpperStripOddL2, centeredPullbackL2]
    using (hinner.trans (hfull.trans (by rw [hfold, hpositive]; ring)))

/-! ## Complete projected main row -/

/-- The complete `P53+` Hilbert representer of the degree-eighteen main
row.  Forming the sum before taking the norm retains every cross-channel
cancellation. -/
def fourCellOddP51Kernel18MainP53PlusL2 : UnitIntervalL2 :=
  fourCellOddQ51ScaledEndpointPotentialP53PlusL2 +
    fourCellOddP51Polynomial18RegularP53PlusL2 +
      fourCellOddP51UpperStripP53PlusL2

theorem oddP53PlusHilbertTail_fourCellOddP51Kernel18MainP53PlusL2 :
    OddP53PlusHilbertTail fourCellOddP51Kernel18MainP53PlusL2 := by
  intro n hn
  unfold fourCellOddP51Kernel18MainP53PlusL2
  rw [shiftedLegendreHilbertBasis.repr_apply_apply, inner_add_right,
    inner_add_right,
    ← shiftedLegendreHilbertBasis.repr_apply_apply,
    ← shiftedLegendreHilbertBasis.repr_apply_apply,
    ← shiftedLegendreHilbertBasis.repr_apply_apply]
  have hpotential : shiftedLegendreHilbertBasis.repr
      fourCellOddQ51ScaledEndpointPotentialP53PlusL2 n = 0 := by
    unfold fourCellOddQ51ScaledEndpointPotentialP53PlusL2
      oddEndpointPotentialP53PlusL2
      oddEndpointPotentialFiniteProfileTailL2
    rw [shiftedLegendreHilbertBasis.repr_apply_apply,
      real_inner_smul_right, inner_sum]
    rw [show (∑ i : Fin 26,
        inner ℝ (shiftedLegendreHilbertBasis n)
          (fourCellOddQ51OddLegendreCoefficients i •
            oddEndpointPotentialLegendreTailL2 26 i)) = 0 by
      apply Finset.sum_eq_zero
      intro i _hi
      rw [real_inner_smul_right,
        ← shiftedLegendreHilbertBasis.repr_apply_apply,
        repr_oddEndpointPotentialLegendreTailL2, if_pos (by
          simpa only [oddLegendreIndex] using hn)]
      ring]
    ring
  have hregular : shiftedLegendreHilbertBasis.repr
      fourCellOddP51Polynomial18RegularP53PlusL2 n = 0 := by
    rw [repr_fourCellOddP51Polynomial18RegularP53PlusL2, if_pos hn]
  have hupper : shiftedLegendreHilbertBasis.repr
      fourCellOddP51UpperStripP53PlusL2 n = 0 :=
    repr_fourCellOddP51UpperStripP53PlusL2_eq_zero_of_lt n hn
  rw [hpotential, hregular, hupper, add_zero, zero_add]

/-- Exact pairing identity for the complete projected main row against a
smooth odd `P53+` test. -/
theorem inner_fourCellOddP51Kernel18MainP53PlusL2_centeredPullbackL2
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    inner ℝ fourCellOddP51Kernel18MainP53PlusL2
        (centeredPullbackL2 r hr.continuous) =
      ∫ x : ℝ in 0..1,
        fourCellOddP51Kernel18MainRepresenter x * r x := by
  let R : UnitIntervalL2 := centeredPullbackL2 r hr.continuous
  have hR : OddP53PlusHilbertTail R :=
    oddP53PlusHilbertTail_centeredPullbackL2 r hr hodd htail
  have hpotential : inner ℝ
      fourCellOddQ51ScaledEndpointPotentialP53PlusL2 R =
      (93 / 50 : ℝ) * ∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x * fourCellOddQ51 x * r x := by
    calc
      inner ℝ fourCellOddQ51ScaledEndpointPotentialP53PlusL2 R =
          inner ℝ fourCellOddQ51ScaledEndpointPotentialSourceL2 R :=
        inner_fourCellOddQ51ScaledEndpointPotentialP53PlusL2_eq_source R hR
      _ = _ := by
        dsimp only [R]
        exact
          inner_fourCellOddQ51ScaledEndpointPotentialSourceL2_centeredPullbackL2
            r hr.continuous hodd
  have hregular : inner ℝ
      fourCellOddP51Polynomial18RegularP53PlusL2 R =
      ∫ x : ℝ in 0..1,
        ((-2 * fourCellOperatorHalfWidth) *
          factorTwoContinuousLagK
            fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x) *
          r x := by
    calc
      inner ℝ fourCellOddP51Polynomial18RegularP53PlusL2 R =
          inner ℝ fourCellOddP51Polynomial18RegularSourceL2 R :=
        (inner_fourCellOddP51Polynomial18RegularSourceL2_eq_P53PlusL2
          R hR).symm
      _ = _ := by
        dsimp only [R]
        exact
          inner_fourCellOddP51Polynomial18RegularSourceL2_centeredPullbackL2
            r hr.continuous hodd
  have hupper : inner ℝ fourCellOddP51UpperStripP53PlusL2 R =
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddQ51UpperEndpointCorrection x * r x := by
    calc
      inner ℝ fourCellOddP51UpperStripP53PlusL2 R =
          inner ℝ fourCellOddP51UpperStripOddL2 R :=
        (inner_fourCellOddP51UpperStripOddL2_eq_P53PlusL2 R hR).symm
      _ = _ := by
        dsimp only [R]
        exact inner_fourCellOddP51UpperStripOddL2_centeredPullbackL2
          r hr.continuous hodd
  have hmain := integral_zero_one_fourCellOddP51Kernel18MainRepresenter_mul
    r hr.continuous
  have hregularScale :
      (∫ x : ℝ in 0..1,
        ((-2 * fourCellOperatorHalfWidth) *
          factorTwoContinuousLagK
            fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x) *
          r x) =
      -2 * fourCellOperatorHalfWidth *
        ∫ x : ℝ in 0..1,
          factorTwoContinuousLagK
            fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x *
              r x := by
    rw [show (fun x : ℝ ↦
        ((-2 * fourCellOperatorHalfWidth) *
          factorTwoContinuousLagK
            fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x) *
          r x) = fun x ↦
        (-2 * fourCellOperatorHalfWidth) *
          (factorTwoContinuousLagK
            fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51 x *
              r x) by
      funext x
      ring,
      intervalIntegral.integral_const_mul]
  change inner ℝ
      (fourCellOddQ51ScaledEndpointPotentialP53PlusL2 +
        fourCellOddP51Polynomial18RegularP53PlusL2 +
          fourCellOddP51UpperStripP53PlusL2) R = _
  rw [inner_add_left, inner_add_left, hpotential, hregular, hupper,
    hregularScale]
  linarith

/-- Exact one-scalar norm certificate for the complete main row. -/
def FourCellOddP51Kernel18MainP53PlusNormCertificate
    (rho kappa : ℝ) : Prop :=
  ‖fourCellOddP51Kernel18MainP53PlusL2‖ ^ 2 ≤
    rho * (fourCellOddP51GalerkinPivot * kappa)

/-- The exact combined norm certificate supplies a universal main-row tail
budget without discarding cross-channel cancellation. -/
theorem fourCellOddP51Kernel18MainTailPairBudget_of_P53PlusNormCertificate
    (rho kappa : ℝ)
    (hcertificate :
      FourCellOddP51Kernel18MainP53PlusNormCertificate rho kappa) :
    FourCellOddP51TailPairBudget rho kappa
      fourCellOddP51Kernel18MainRepresenter := by
  intro r hr hodd htail
  let R : UnitIntervalL2 := centeredPullbackL2 r hr.continuous
  have hinner := abs_real_inner_le_norm
    fourCellOddP51Kernel18MainP53PlusL2 R
  have hsquare := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
  have hmass : 0 ≤ ‖R‖ ^ 2 := sq_nonneg _
  rw [sq_abs, mul_pow] at hsquare
  rw [← inner_fourCellOddP51Kernel18MainP53PlusL2_centeredPullbackL2
    r hr hodd htail]
  calc
    inner ℝ fourCellOddP51Kernel18MainP53PlusL2 R ^ 2 ≤
        ‖fourCellOddP51Kernel18MainP53PlusL2‖ ^ 2 * ‖R‖ ^ 2 := hsquare
    _ ≤ (rho * (fourCellOddP51GalerkinPivot * kappa)) * ‖R‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcertificate hmass
    _ = rho * (fourCellOddP51GalerkinPivot *
        (kappa * (∫ x : ℝ in 0..1, r x ^ 2))) := by
      rw [show ‖R‖ ^ 2 = ∫ x : ℝ in 0..1, r x ^ 2 by
        dsimp only [R]
        exact norm_sq_centeredPullbackL2_eq_zero_one_of_odd
          r hr.continuous hodd]
      ring

/-- The only scalar data needed on the residual side at the `1/8` high-tail
constant: pivot sign, the exact combined main norm, and the tiny kernel-error
norm. -/
def FourCellOddP51OneEighthHighTailResidualCertificate : Prop :=
  FourCellOddP51GalerkinPivotNonnegative ∧
    FourCellOddP51Kernel18MainP53PlusNormCertificate (9 / 10) (1 / 8) ∧
    (∫ x : ℝ in 0..1,
      fourCellOddP51Kernel18ErrorRepresenter x ^ 2) ≤
        (1 / 1000 : ℝ) *
          (fourCellOddP51GalerkinPivot * (1 / 8 : ℝ))

/-- The three scalar facts above prove the exact universal residual dual at
the `1/8` constant used by the high-tail middle reduction. -/
theorem fourCellOddP51GalerkinP53PlusResidualDual_oneEighth_of_certificate
    (hcertificate : FourCellOddP51OneEighthHighTailResidualCertificate) :
    FourCellOddP51GalerkinP53PlusResidualDual (1 / 8) := by
  rcases hcertificate with ⟨hpivot, hmainNorm, herrorNorm⟩
  have hmain : FourCellOddP51TailPairBudget (9 / 10) (1 / 8)
      fourCellOddP51Kernel18MainRepresenter :=
    fourCellOddP51Kernel18MainTailPairBudget_of_P53PlusNormCertificate
      (9 / 10) (1 / 8) hmainNorm
  have herror : FourCellOddP51TailPairBudget (1 / 1000) (1 / 8)
      fourCellOddP51Kernel18ErrorRepresenter :=
    fourCellOddP51TailPairBudget_one_thousandth_of_memLp_l2
      (1 / 8) fourCellOddP51Kernel18ErrorRepresenter
      memLp_fourCellOddP51Kernel18ErrorRepresenter_two_restrict herrorNorm
  exact fourCellOddP51GalerkinP53PlusResidualDual_of_tailBudgets
    (1 / 8) (by norm_num) hpivot
    fourCellOddP51Kernel18MainRepresenter
    fourCellOddP51Kernel18ErrorRepresenter
    fourCellOddP51Kernel18TailRowDecomposition hmain herror

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailResidualRepresenterStructural
