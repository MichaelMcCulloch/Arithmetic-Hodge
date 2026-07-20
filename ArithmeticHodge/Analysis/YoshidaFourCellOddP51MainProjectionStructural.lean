import ArithmeticHodge.Analysis.YoshidaFourCellOddP51Kernel18MainSelectorStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP11AnchorMassStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51MainProjectionStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointPotentialBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointOcticTwoModeSchurData
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP51EndpointStripRepresenterStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51Kernel18ErrorBudgetStructural
open YoshidaFourCellOddP51Kernel18MainSelectorStructural
open YoshidaFourCellOddP51Kernel18RowDecompositionStructural
open YoshidaFourCellOddP51SparseP11AnchorMassStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural

/-!
# Orthogonal projection of the complete P51 main row

The endpoint-potential, polynomial-lag, and supported upper-strip terms must
be kept together: their cross terms are part of the available margin.  This
file records the coordinate-free projection step for the complete piecewise
main row.  Once its residual is normal to `P1,P3,...,P51`, its squared norm is
the exact Pythagorean deficit, with no triangle inequality.
-/

/-- Normal equations for a complete low selector.  These are exactly the
twenty-six odd coordinates removed before the `P53+` tail estimate. -/
def FourCellOddP51MainSelectorNormalEquations
    (c : ℝ) (a : FourCellOddP51RetainedIndex → ℝ) : Prop :=
  (∫ x : ℝ in 0..1,
      fourCellOddP51Kernel18MainSelectorResidual c a x * centeredP1 x) = 0 ∧
    ∀ i : FourCellOddP51RetainedIndex,
      (∫ x : ℝ in 0..1,
        fourCellOddP51Kernel18MainSelectorResidual c a x *
          fourCellOddFiniteRetainedBasis i x) = 0

/-- Canonical `P1` coefficient of the complete main row on the positive
half.  The factor three is the reciprocal squared norm of `P1`. -/
def fourCellOddP51Kernel18MainCanonicalP1Coefficient : ℝ :=
  3 * ∫ x : ℝ in 0..1,
    fourCellOddP51Kernel18MainRepresenter x * centeredP1 x

/-- Canonical retained coefficient of the complete main row.  Orthogonality
of the centered odd Legendre family makes the reciprocal diagonal weight
`2 * degree + 1`. -/
def fourCellOddP51Kernel18MainCanonicalRetainedCoefficients
    (i : FourCellOddP51RetainedIndex) : ℝ :=
  (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1) *
    ∫ x : ℝ in 0..1,
      fourCellOddP51Kernel18MainRepresenter x *
        fourCellOddFiniteRetainedBasis i x

private theorem memLp_two_restrict_zero_one_of_continuous
    (f : ℝ → ℝ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hfMeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hf.aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hfMeas]
  have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
      (Icc (0 : ℝ) 1) :=
    (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hcompact.mono_set Ioc_subset_Icc_self

private theorem intervalIntegrable_zero_one_mul_of_memLp_two
    (f g : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    IntervalIntegrable (fun x : ℝ ↦ f x * g x) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  exact hf.integrable_mul hg

private theorem integral_zero_one_centeredP1_sq :
    (∫ x : ℝ in 0..1, centeredP1 x ^ 2) = 1 / 3 := by
  have hfold := integral_sq_eq_two_mul_positiveHalf
    centeredP1 (by unfold centeredP1; fun_prop)
    (Or.inr (by intro x; unfold centeredP1; ring))
  rw [integral_centeredP1_sq] at hfold
  linarith

private theorem intervalIntegrable_log_sq_zero_one :
    IntervalIntegrable (fun x : ℝ ↦ Real.log x ^ 2) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  have hr : IntegrableOn
      (fun x : ℝ ↦ 16 * x ^ (-(1 / 2 : ℝ))) (Ioc 0 1) volume := by
    have h := intervalIntegral.intervalIntegrable_rpow'
      (a := (0 : ℝ)) (b := 1) (r := -(1 / 2 : ℝ)) (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
    exact h.const_mul 16
  apply Integrable.mono' hr
  · exact (Real.measurable_log.pow_const 2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    let y : ℝ := x ^ (1 / 4 : ℝ)
    have hy : 0 < y := Real.rpow_pos_of_pos hx0 _
    have hlog := Real.abs_log_mul_self_rpow_lt x (1 / 4 : ℝ)
      hx0 hx1 (by norm_num)
    norm_num at hlog
    have hprod : |Real.log x| * y < 4 := by
      dsimp only [y]
      simpa only [abs_mul,
        abs_of_pos (Real.rpow_pos_of_pos hx0 _)] using hlog
    have hp0 : 0 ≤ |Real.log x| * y :=
      mul_nonneg (abs_nonneg _) hy.le
    have hmul :
        0 ≤ (4 - |Real.log x| * y) * (4 + |Real.log x| * y) :=
      mul_nonneg (sub_nonneg.mpr hprod.le) (add_nonneg (by norm_num) hp0)
    have hsq : |Real.log x| ^ 2 * y ^ 2 ≤ 16 := by
      nlinarith only [hmul]
    have hySq : y ^ 2 = x ^ (1 / 2 : ℝ) := by
      dsimp only [y]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have hneg : x ^ (-(1 / 2 : ℝ)) = (y ^ 2)⁻¹ := by
      rw [Real.rpow_neg hx0.le, hySq]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs, hneg,
      ← div_eq_mul_inv]
    exact (le_div_iff₀ (sq_pos_of_pos hy)).2 hsq

private theorem intervalIntegrable_log_sq_zero_two :
    IntervalIntegrable (fun x : ℝ ↦ Real.log x ^ 2) volume 0 2 := by
  apply intervalIntegrable_log_sq_zero_one.trans
  apply ContinuousOn.intervalIntegrable
  exact (Real.continuousOn_log.mono (by
    intro x hx
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith [hx.1])).pow 2

private theorem intervalIntegrable_endpointPotential_sq :
    IntervalIntegrable (fun x : ℝ ↦ yoshidaEndpointPotential x ^ 2)
      volume (-1) 1 := by
  have hlog := intervalIntegrable_log_sq_zero_two
  have hminus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 - x) ^ 2) volume (-1) 1 := by
    convert (hlog.comp_sub_left 1).symm using 1 <;> norm_num
  have hplus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 + x) ^ 2) volume (-1) 1 := by
    convert hlog.comp_add_left 1 using 1 <;> norm_num
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    at hminus hplus ⊢
  have hdom : IntegrableOn
      (fun x : ℝ ↦ (1 / 2 : ℝ) *
        (Real.log (1 - x) ^ 2 + Real.log (1 + x) ^ 2))
      (Ioc (-1) 1) volume := (hminus.add hplus).const_mul (1 / 2)
  apply Integrable.mono' hdom
  · unfold yoshidaEndpointPotential
    exact (((Real.measurable_log.comp
      (measurable_const.sub (measurable_id.pow_const 2))).neg.div_const 2)
        |>.pow_const 2).aestronglyMeasurable
  · have hne1 : ∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-1 : ℝ) 1)), x ≠ 1 :=
      (MeasureTheory.Measure.ae_ne volume (1 : ℝ)).filter_mono
        (ae_mono Measure.restrict_le_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne1] with x hx hx1
    have hxneg1 : x ≠ -1 := ne_of_gt hx.1
    have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    have hadd : 1 + x ≠ 0 := by
      intro hzero
      apply hxneg1
      linarith
    unfold yoshidaEndpointPotential
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
      Real.log_mul hsub hadd]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith only [sq_nonneg (Real.log (1 - x) - Real.log (1 + x))]

private theorem memLp_endpointPotential_mul_continuous
    (p : ℝ → ℝ) (hp : Continuous p) :
    MemLp (fun x : ℝ ↦ yoshidaEndpointPotential x * p x) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * p x)
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    apply Measurable.aestronglyMeasurable
    unfold yoshidaEndpointPotential
    exact ((Real.measurable_log.comp
      (measurable_const.sub (measurable_id.pow_const 2))).neg.div_const 2).mul
        hp.measurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hI : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x ^ 2 * p x ^ 2)
      volume (-1) 1 := by
    simpa only [mul_comm] using
      intervalIntegrable_endpointPotential_sq.continuousOn_mul
        (hp.pow 2).continuousOn
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hI
  apply hI.congr
  filter_upwards with x
  rw [Real.norm_eq_abs, sq_abs]
  ring

/-- The complete piecewise degree-eighteen P51 main row is genuinely in
`L²(0,1)`.  This includes the logarithmic endpoint source and the honest
jump of the supported upper-strip correction. -/
theorem memLp_fourCellOddP51Kernel18MainRepresenter_two_restrict :
    MemLp fourCellOddP51Kernel18MainRepresenter 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hendpointFull := memLp_endpointPotential_mul_continuous
    fourCellOddQ51 contDiff_fourCellOddQ51.continuous
  have hsubset : Ioc (0 : ℝ) 1 ⊆ Ioc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨(by linarith [hx.1]), hx.2⟩
  have hendpoint := hendpointFull.mono_measure
    (Measure.restrict_mono hsubset le_rfl)
  have hregularContinuous : Continuous
      (factorTwoContinuousLagK
        fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51) :=
    continuous_factorTwoContinuousLagK
      fourCellOddP51Polynomial18RegularLagKernel fourCellOddQ51
      continuous_fourCellOddP51Polynomial18RegularLagKernel
      contDiff_fourCellOddQ51.continuous
  have hregular := memLp_two_restrict_zero_one_of_continuous _
    hregularContinuous
  have hbase : MemLp fourCellOddP51Kernel18BaseRepresenter 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have hcomb := (hendpoint.const_mul (93 / 50)).sub
      (hregular.const_mul (2 * fourCellOperatorHalfWidth))
    apply (memLp_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)).mpr hcomb
    unfold fourCellOddP51Kernel18BaseRepresenter
    simp only [Pi.sub_apply]
    ring
  have hcorrection := memLp_two_restrict_zero_one_of_continuous
    fourCellOddQ51UpperEndpointCorrection
    continuous_fourCellOddQ51UpperEndpointCorrection
  have hsupported : MemLp
      ((Ioi (3 / 5 : ℝ)).indicator fourCellOddQ51UpperEndpointCorrection) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hcorrection.indicator measurableSet_Ioi
  apply (memLp_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)).mpr
    (hbase.add hsupported)
  unfold fourCellOddP51Kernel18MainRepresenter
  by_cases hx : x ≤ (3 / 5 : ℝ)
  · rw [if_pos hx]
    simp [not_lt.mpr hx]
  · rw [if_neg hx]
    simp [lt_of_not_ge hx]

/-- Square-integrability of the complete main row immediately gives
square-integrability of its canonical projection residual. -/
theorem memLp_fourCellOddP51Kernel18MainCanonicalResidual_of_main
    (hmain : MemLp fourCellOddP51Kernel18MainRepresenter 2
      (volume.restrict (Ioc (0 : ℝ) 1))) :
    MemLp
      (fourCellOddP51Kernel18MainSelectorResidual
        fourCellOddP51Kernel18MainCanonicalP1Coefficient
        fourCellOddP51Kernel18MainCanonicalRetainedCoefficients)
      2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hselector : MemLp
      (fourCellOddP51LowSelector
        fourCellOddP51Kernel18MainCanonicalP1Coefficient
        fourCellOddP51Kernel18MainCanonicalRetainedCoefficients)
      2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    memLp_two_restrict_zero_one_of_continuous _
      (continuous_fourCellOddP51LowSelector
        fourCellOddP51Kernel18MainCanonicalP1Coefficient
        fourCellOddP51Kernel18MainCanonicalRetainedCoefficients)
  simpa only [fourCellOddP51Kernel18MainSelectorResidual] using
    hmain.sub hselector

theorem memLp_fourCellOddP51Kernel18MainCanonicalResidual :
    MemLp
      (fourCellOddP51Kernel18MainSelectorResidual
        fourCellOddP51Kernel18MainCanonicalP1Coefficient
        fourCellOddP51Kernel18MainCanonicalRetainedCoefficients)
      2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  memLp_fourCellOddP51Kernel18MainCanonicalResidual_of_main
    memLp_fourCellOddP51Kernel18MainRepresenter_two_restrict

/-- The explicit reciprocal-diagonal coefficients satisfy all twenty-six
normal equations.  This is the structural existence theorem for the optimal
low selector; no matrix inversion or coordinate enumeration occurs. -/
theorem fourCellOddP51Kernel18MainCanonicalSelector_normalEquations
    (hmain : MemLp fourCellOddP51Kernel18MainRepresenter 2
      (volume.restrict (Ioc (0 : ℝ) 1))) :
    FourCellOddP51MainSelectorNormalEquations
      fourCellOddP51Kernel18MainCanonicalP1Coefficient
      fourCellOddP51Kernel18MainCanonicalRetainedCoefficients := by
  let M := fourCellOddP51Kernel18MainRepresenter
  let c := fourCellOddP51Kernel18MainCanonicalP1Coefficient
  let a := fourCellOddP51Kernel18MainCanonicalRetainedCoefficients
  have hP1Lp : MemLp centeredP1 2
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    memLp_two_restrict_zero_one_of_continuous centeredP1 (by
      unfold centeredP1
      fun_prop)
  have hMP1 : IntervalIntegrable (fun x : ℝ ↦ M x * centeredP1 x)
      volume 0 1 :=
    intervalIntegrable_zero_one_mul_of_memLp_two M centeredP1 hmain hP1Lp
  have hP1P1 : IntervalIntegrable (fun x : ℝ ↦ centeredP1 x ^ 2)
      volume 0 1 := by
    exact ((by unfold centeredP1; fun_prop : Continuous centeredP1).pow 2)
      |>.intervalIntegrable _ _
  have hprofile : Continuous (fourCellOddP51RetainedProfile a) :=
    (contDiff_fourCellOddFiniteRetainedProfile 24 a).continuous
  have hprofileP1 : IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddP51RetainedProfile a x * centeredP1 x)
      volume 0 1 :=
    (hprofile.mul (by unfold centeredP1; fun_prop)).intervalIntegrable _ _
  constructor
  · change (∫ x : ℝ in 0..1,
      (M x - (c * centeredP1 x + fourCellOddP51RetainedProfile a x)) *
        centeredP1 x) = 0
    rw [show (fun x : ℝ ↦
        (M x - (c * centeredP1 x + fourCellOddP51RetainedProfile a x)) *
          centeredP1 x) =
        fun x ↦ M x * centeredP1 x -
          (c * centeredP1 x ^ 2 +
            fourCellOddP51RetainedProfile a x * centeredP1 x) by
      funext x
      ring,
      intervalIntegral.integral_sub hMP1
        ((hP1P1.const_mul c).add hprofileP1),
      intervalIntegral.integral_add (hP1P1.const_mul c) hprofileP1,
      intervalIntegral.integral_const_mul,
      integral_zero_one_centeredP1_sq]
    have hcross := integral_zero_one_centeredP1_mul_finiteRetained_eq_zero
      24 a
    rw [show (fun x : ℝ ↦
        fourCellOddP51RetainedProfile a x * centeredP1 x) =
        fun x ↦ centeredP1 x *
          fourCellOddFiniteRetainedProfile 24 a x by
      funext x
      unfold fourCellOddP51RetainedProfile
      ring,
      hcross]
    unfold c fourCellOddP51Kernel18MainCanonicalP1Coefficient M
    ring
  · intro i
    change (∫ x : ℝ in 0..1,
      (M x - (c * centeredP1 x + fourCellOddP51RetainedProfile a x)) *
        fourCellOddFiniteRetainedBasis i x) = 0
    have hbasisLp : MemLp (fourCellOddFiniteRetainedBasis i) 2
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      memLp_two_restrict_zero_one_of_continuous _
        (contDiff_fourCellOddFiniteRetainedBasis i).continuous
    have hMbasis : IntervalIntegrable
        (fun x : ℝ ↦ M x * fourCellOddFiniteRetainedBasis i x)
        volume 0 1 :=
      intervalIntegrable_zero_one_mul_of_memLp_two M _ hmain hbasisLp
    have hP1basis : IntervalIntegrable
        (fun x : ℝ ↦ centeredP1 x * fourCellOddFiniteRetainedBasis i x)
        volume 0 1 :=
      ((by unfold centeredP1; fun_prop : Continuous centeredP1).mul
        (contDiff_fourCellOddFiniteRetainedBasis i).continuous)
        |>.intervalIntegrable _ _
    have hprofileBasis : IntervalIntegrable
        (fun x : ℝ ↦ fourCellOddP51RetainedProfile a x *
          fourCellOddFiniteRetainedBasis i x) volume 0 1 :=
      (hprofile.mul (contDiff_fourCellOddFiniteRetainedBasis i).continuous)
        |>.intervalIntegrable _ _
    rw [show (fun x : ℝ ↦
        (M x - (c * centeredP1 x + fourCellOddP51RetainedProfile a x)) *
          fourCellOddFiniteRetainedBasis i x) =
        fun x ↦ M x * fourCellOddFiniteRetainedBasis i x -
          (c * (centeredP1 x * fourCellOddFiniteRetainedBasis i x) +
            fourCellOddP51RetainedProfile a x *
              fourCellOddFiniteRetainedBasis i x) by
      funext x
      ring,
      intervalIntegral.integral_sub hMbasis
        ((hP1basis.const_mul c).add hprofileBasis),
      intervalIntegral.integral_add (hP1basis.const_mul c) hprofileBasis,
      intervalIntegral.integral_const_mul]
    have hP1basisZero : (∫ x : ℝ in 0..1,
        centeredP1 x * fourCellOddFiniteRetainedBasis i x) = 0 := by
      have hall := integral_zero_one_centeredP1_mul_finiteRetained_eq_zero
        24 (fun j ↦ if j = i then (1 : ℝ) else 0)
      have hunit : fourCellOddFiniteRetainedProfile 24
          (fun j ↦ if j = i then (1 : ℝ) else 0) =
          fourCellOddFiniteRetainedBasis i := by
        funext x
        unfold fourCellOddFiniteRetainedProfile
        simp only [Finset.sum_apply]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _hj hji
          rw [if_neg hji]
          ring
        · simp
      rw [hunit] at hall
      exact hall
    rw [hP1basisZero, mul_zero, zero_add,
      show (∫ x : ℝ in 0..1,
          fourCellOddP51RetainedProfile a x *
            fourCellOddFiniteRetainedBasis i x) =
        a i / (2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1) by
          rw [show (fun x : ℝ ↦ fourCellOddP51RetainedProfile a x *
              fourCellOddFiniteRetainedBasis i x) =
            fun x ↦ fourCellOddFiniteRetainedBasis i x *
              fourCellOddFiniteRetainedProfile 24 a x by
            funext x
            unfold fourCellOddP51RetainedProfile
            ring]
          exact integral_zero_one_fourCellOddFiniteRetainedBasis_mul_profile
            24 i a]
    have hden : 2 * (fourCellOddFiniteRetainedDegree i : ℝ) + 1 ≠ 0 := by
      positivity
    unfold a fourCellOddP51Kernel18MainCanonicalRetainedCoefficients M
    field_simp [hden]
    ring

theorem fourCellOddP51Kernel18MainCanonicalSelector_normalEquations_unconditional :
    FourCellOddP51MainSelectorNormalEquations
      fourCellOddP51Kernel18MainCanonicalP1Coefficient
      fourCellOddP51Kernel18MainCanonicalRetainedCoefficients :=
  fourCellOddP51Kernel18MainCanonicalSelector_normalEquations
    memLp_fourCellOddP51Kernel18MainRepresenter_two_restrict

/-- The twenty-six normal equations imply orthogonality to their complete
selector, without expanding any concrete row of the P51 solve. -/
theorem integral_mainSelectorResidual_mul_lowSelector_eq_zero
    (c : ℝ) (a : FourCellOddP51RetainedIndex → ℝ)
    (hres : MemLp (fourCellOddP51Kernel18MainSelectorResidual c a) 2
      (volume.restrict (Ioc (0 : ℝ) 1)))
    (hnormal : FourCellOddP51MainSelectorNormalEquations c a) :
    (∫ x : ℝ in 0..1,
      fourCellOddP51Kernel18MainSelectorResidual c a x *
        fourCellOddP51LowSelector c a x) = 0 := by
  classical
  let R := fourCellOddP51Kernel18MainSelectorResidual c a
  have hP1Lp : MemLp centeredP1 2
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    memLp_two_restrict_zero_one_of_continuous centeredP1 (by
      unfold centeredP1
      fun_prop)
  have hP1I : IntervalIntegrable (fun x : ℝ ↦ R x * centeredP1 x)
      volume 0 1 :=
    intervalIntegrable_zero_one_mul_of_memLp_two R centeredP1 hres hP1Lp
  have hbasisLp (i : FourCellOddP51RetainedIndex) :
      MemLp (fourCellOddFiniteRetainedBasis i) 2
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
    memLp_two_restrict_zero_one_of_continuous
      (fourCellOddFiniteRetainedBasis i)
      (contDiff_fourCellOddFiniteRetainedBasis i).continuous
  have hbasisI (i : FourCellOddP51RetainedIndex) :
      IntervalIntegrable
        (fun x : ℝ ↦ R x * fourCellOddFiniteRetainedBasis i x)
        volume 0 1 :=
    intervalIntegrable_zero_one_mul_of_memLp_two R
      (fourCellOddFiniteRetainedBasis i) hres (hbasisLp i)
  rw [show (fun x : ℝ ↦ R x * fourCellOddP51LowSelector c a x) =
      fun x ↦ c * (R x * centeredP1 x) +
        ∑ i : FourCellOddP51RetainedIndex,
          a i * (R x * fourCellOddFiniteRetainedBasis i x) by
    funext x
    unfold fourCellOddP51LowSelector fourCellOddP51RetainedProfile
      fourCellOddFiniteRetainedProfile
    simp only [Finset.sum_apply]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i hi
      ring,
    intervalIntegral.integral_add (hP1I.const_mul c)]
  · rw [intervalIntegral.integral_const_mul, hnormal.1, mul_zero,
      zero_add, intervalIntegral.integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro i hi
      rw [intervalIntegral.integral_const_mul, hnormal.2 i, mul_zero]
    · intro i hi
      exact (hbasisI i).const_mul (a i)
  · exact IntervalIntegrable.sum Finset.univ fun i _hi ↦
      (hbasisI i).const_mul (a i)

/-- Exact Pythagoras for the complete piecewise main row.  In particular,
all endpoint/polynomial/upper-strip cross terms remain inside the left-hand
source norm rather than being discarded by separate estimates. -/
theorem integral_mainSelectorResidual_sq_add_lowSelector_sq_eq_main_sq
    (c : ℝ) (a : FourCellOddP51RetainedIndex → ℝ)
    (hres : MemLp (fourCellOddP51Kernel18MainSelectorResidual c a) 2
      (volume.restrict (Ioc (0 : ℝ) 1)))
    (hnormal : FourCellOddP51MainSelectorNormalEquations c a) :
    (∫ x : ℝ in 0..1,
        fourCellOddP51Kernel18MainSelectorResidual c a x ^ 2) +
      (∫ x : ℝ in 0..1,
        fourCellOddP51LowSelector c a x ^ 2) =
      ∫ x : ℝ in 0..1,
        fourCellOddP51Kernel18MainRepresenter x ^ 2 := by
  let R := fourCellOddP51Kernel18MainSelectorResidual c a
  let S := fourCellOddP51LowSelector c a
  have hSLp : MemLp S 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    memLp_two_restrict_zero_one_of_continuous S
      (continuous_fourCellOddP51LowSelector c a)
  have hR2 : IntervalIntegrable (fun x : ℝ ↦ R x ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hres.integrable_sq
  have hS2 : IntervalIntegrable (fun x : ℝ ↦ S x ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hSLp.integrable_sq
  have hRS : IntervalIntegrable (fun x : ℝ ↦ R x * S x) volume 0 1 :=
    intervalIntegrable_zero_one_mul_of_memLp_two R S hres hSLp
  have horth : (∫ x : ℝ in 0..1, R x * S x) = 0 := by
    dsimp only [R, S]
    exact integral_mainSelectorResidual_mul_lowSelector_eq_zero
      c a hres hnormal
  rw [show (fun x : ℝ ↦ fourCellOddP51Kernel18MainRepresenter x ^ 2) =
      fun x ↦ R x ^ 2 + 2 * (R x * S x) + S x ^ 2 by
    funext x
    dsimp only [R, S]
    unfold fourCellOddP51Kernel18MainSelectorResidual
    ring,
    intervalIntegral.integral_add (hR2.add (hRS.const_mul 2)) hS2,
    intervalIntegral.integral_add hR2 (hRS.const_mul 2),
    intervalIntegral.integral_const_mul, horth]
  ring

/-- After the exact normal equations, the main certificate is reduced to a
single combined Pythagorean deficit bound. -/
theorem fourCellOddP51Kernel18MainSelectorCertificate_of_normal_projection
    (kappa c : ℝ) (a : FourCellOddP51RetainedIndex → ℝ)
    (hres : MemLp (fourCellOddP51Kernel18MainSelectorResidual c a) 2
      (volume.restrict (Ioc (0 : ℝ) 1)))
    (hnormal : FourCellOddP51MainSelectorNormalEquations c a)
    (hdeficit :
      (∫ x : ℝ in 0..1,
          fourCellOddP51Kernel18MainRepresenter x ^ 2) -
        (∫ x : ℝ in 0..1,
          fourCellOddP51LowSelector c a x ^ 2) ≤
        (9 / 10 : ℝ) * (fourCellOddP51GalerkinPivot * kappa)) :
    FourCellOddP51Kernel18MainSelectorCertificate kappa c a := by
  refine ⟨hres, ?_⟩
  have hpythagoras :=
    integral_mainSelectorResidual_sq_add_lowSelector_sq_eq_main_sq
      c a hres hnormal
  linarith

/-- The sole scalar left by the exact canonical projection of the complete
main row. -/
def FourCellOddP51Kernel18MainCanonicalProjectionDeficitBound
    (kappa : ℝ) : Prop :=
  (∫ x : ℝ in 0..1,
      fourCellOddP51Kernel18MainRepresenter x ^ 2) -
    (∫ x : ℝ in 0..1,
      fourCellOddP51LowSelector
        fourCellOddP51Kernel18MainCanonicalP1Coefficient
        fourCellOddP51Kernel18MainCanonicalRetainedCoefficients x ^ 2) ≤
    (9 / 10 : ℝ) * (fourCellOddP51GalerkinPivot * kappa)

/-- The canonical deficit bound supplies the full main-selector certificate
with its `MemLp` and all twenty-six normal equations discharged internally. -/
theorem fourCellOddP51Kernel18MainSelectorCertificate_of_canonicalProjectionDeficit
    (kappa : ℝ)
    (hdeficit : FourCellOddP51Kernel18MainCanonicalProjectionDeficitBound
      kappa) :
    FourCellOddP51Kernel18MainSelectorCertificate kappa
      fourCellOddP51Kernel18MainCanonicalP1Coefficient
      fourCellOddP51Kernel18MainCanonicalRetainedCoefficients := by
  exact fourCellOddP51Kernel18MainSelectorCertificate_of_normal_projection
    kappa fourCellOddP51Kernel18MainCanonicalP1Coefficient
    fourCellOddP51Kernel18MainCanonicalRetainedCoefficients
    memLp_fourCellOddP51Kernel18MainCanonicalResidual
    fourCellOddP51Kernel18MainCanonicalSelector_normalEquations_unconditional
    hdeficit

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51MainProjectionStructural
