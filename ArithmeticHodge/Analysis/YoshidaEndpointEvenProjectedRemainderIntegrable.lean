import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderMoments

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderIntegrable

open YoshidaEndpointEvenAtanhReciprocalMajorant
open YoshidaEndpointEvenAtanhTailWeight
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedDualIntegral
open YoshidaEndpointEvenProjectedRemainderMajorant
open YoshidaEndpointEvenProjectedRemainderMoments
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaRegularKernelBound

noncomputable section

/-!
# Integrability of the fixed projected remainder chain

The regular representers are only known here through their integral pairing,
not through a global continuity theorem.  A uniform kernel bound gives the
missing local `L∞` control.  It upgrades interval integrability of each
representer to integrability of the shifted remainder square.  The polynomial
majorant is then integrable, and domination on `Ioo (-1) 1` proves
integrability for the transformed and true denominator quotients without
making a false endpoint comparison.
-/

private theorem norm_regularRepresenter_le_half
    (p : ℝ → ℝ) (hp : ∀ y ∈ Icc (-1 : ℝ) 1, ‖p y‖ ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖yoshidaEndpointEvenRegularRepresenter p x‖ ≤ (1 / 2 : ℝ) := by
  unfold yoshidaEndpointEvenRegularRepresenter
  calc
    ‖∫ y : ℝ in Icc (-1) 1,
        yoshidaRegularKernel (yoshidaEndpointA * |x - y|) * p y‖ ≤
        (1 / 4 : ℝ) * volume.real (Icc (-1 : ℝ) 1) := by
      apply MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (measure_Icc_lt_top (a := (-1 : ℝ)) (b := 1))
      intro y hy
      have hdist : |x - y| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
      have harg0 : 0 ≤ yoshidaEndpointA * |x - y| :=
        mul_nonneg yoshidaEndpointA_pos.le (abs_nonneg _)
      have harg2 : yoshidaEndpointA * |x - y| ≤ Real.log 2 := by
        unfold yoshidaEndpointA
        nlinarith [mul_le_mul_of_nonneg_left hdist
          (by positivity : 0 ≤ Real.log 2 / 2)]
      have hkernel := yoshidaRegularKernel_mem_Icc harg0 harg2
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hkernel.1]
      calc
        yoshidaRegularKernel (yoshidaEndpointA * |x - y|) * ‖p y‖ ≤
            (1 / 4 : ℝ) * 1 :=
          mul_le_mul hkernel.2 (hp y hy) (norm_nonneg _) (by norm_num)
        _ = 1 / 4 := by ring
    _ = 1 / 2 := by
      norm_num [Measure.real, Real.volume_Icc]

private theorem norm_regularRepresenter0_le_half
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x‖ ≤
      (1 / 2 : ℝ) := by
  apply norm_regularRepresenter_le_half centeredEvenP0
  intro y _hy
  simp [centeredEvenP0]
  exact hx

private theorem norm_regularRepresenter2_le_half
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x‖ ≤
      (1 / 2 : ℝ) := by
  apply norm_regularRepresenter_le_half centeredEvenP2
  intro y hy
  rw [Real.norm_eq_abs, abs_le]
  unfold centeredEvenP2
  have hySq : y ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one, abs_le]
    exact hy
  constructor <;> nlinarith [sq_nonneg y]
  exact hx

private theorem intervalIntegrable_regularRepresenter
    (p : ℝ → ℝ) (hp : Continuous p) :
    IntervalIntegrable
      (yoshidaEndpointEvenRegularRepresenter p) volume (-1) 1 := by
  simpa using intervalIntegrable_regularRepresenter_mul p (fun _ : ℝ ↦ 1)
    hp continuous_const

private def fixedProjectedShiftedContinuousPart (c b x : ℝ) : ℝ :=
  2 * yoshidaEndpointA *
      (c * yoshidaEndpointCoshMoment centeredEvenP0 +
        b * yoshidaEndpointCoshMoment centeredEvenP2) *
      Real.cosh (yoshidaEndpointA * x / 2) -
    fixedProjectionPolynomial c b x -
    (41 / 60 : ℝ) * fixedEvenLowProfile c b x

private theorem continuous_fixedProjectedShiftedContinuousPart (c b : ℝ) :
    Continuous (fixedProjectedShiftedContinuousPart c b) := by
  unfold fixedProjectedShiftedContinuousPart fixedProjectionPolynomial
    fixedEvenLowProfile centeredEvenP0 centeredEvenP2
  fun_prop

private theorem fixedProjectedShiftedRemainder_eq_regular_add_continuous
    (c b x : ℝ) :
    fixedProjectedShiftedRemainder c b x =
      (-yoshidaEndpointA) *
          (c * yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x +
            b * yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x) +
        fixedProjectedShiftedContinuousPart c b x := by
  unfold fixedProjectedShiftedRemainder fixedProjectedBoundedRemainder
    fixedProjectedShiftedContinuousPart
  ring

private theorem intervalIntegrable_fixedProjectedShiftedRemainder (c b : ℝ) :
    IntervalIntegrable
      (fixedProjectedShiftedRemainder c b) volume (-1) 1 := by
  have hR0 := intervalIntegrable_regularRepresenter centeredEvenP0
    (by unfold centeredEvenP0; fun_prop)
  have hR2 := intervalIntegrable_regularRepresenter centeredEvenP2
    (by unfold centeredEvenP2; fun_prop)
  have hregular : IntervalIntegrable
      (fun x ↦ (-yoshidaEndpointA) *
        (c * yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x +
          b * yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x))
      volume (-1) 1 :=
    ((hR0.const_mul c).add (hR2.const_mul b)).const_mul
      (-yoshidaEndpointA)
  have hcontinuous : IntervalIntegrable
      (fixedProjectedShiftedContinuousPart c b) volume (-1) 1 :=
    (continuous_fixedProjectedShiftedContinuousPart c b).intervalIntegrable (-1) 1
  apply (hregular.add hcontinuous).congr
  intro x _hx
  exact (fixedProjectedShiftedRemainder_eq_regular_add_continuous c b x).symm

private theorem exists_norm_fixedProjectedShiftedRemainder_le
    (c b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      ‖fixedProjectedShiftedRemainder c b x‖ ≤ C := by
  have hcontinuous := continuous_fixedProjectedShiftedContinuousPart c b
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hcontinuous.norm.continuousOn
  let Q : ℝ := max 1 M
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one (le_max_left 1 M)
  have hQ : ∀ x ∈ Icc (-1 : ℝ) 1,
      ‖fixedProjectedShiftedContinuousPart c b x‖ ≤ Q := by
    intro x hx
    exact (hM (Set.mem_image_of_mem _ hx)).trans (le_max_right 1 M)
  refine ⟨‖yoshidaEndpointA‖ * ((‖c‖ + ‖b‖) / 2) + Q, ?_, ?_⟩
  · positivity
  · intro x hx
    rw [fixedProjectedShiftedRemainder_eq_regular_add_continuous]
    calc
      ‖(-yoshidaEndpointA) *
            (c * yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x +
              b * yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x) +
          fixedProjectedShiftedContinuousPart c b x‖ ≤
          ‖yoshidaEndpointA‖ *
              ‖c * yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x +
                b * yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x‖ +
            ‖fixedProjectedShiftedContinuousPart c b x‖ := by
        simpa only [norm_mul, norm_neg] using norm_add_le
          ((-yoshidaEndpointA) *
            (c * yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x +
              b * yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x))
          (fixedProjectedShiftedContinuousPart c b x)
      _ ≤ ‖yoshidaEndpointA‖ * ((‖c‖ + ‖b‖) / 2) + Q := by
        have hlin :
            ‖c * yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x +
              b * yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x‖ ≤
                (‖c‖ + ‖b‖) / 2 := by
          calc
            ‖c * yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x +
                b * yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x‖ ≤
                ‖c * yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x‖ +
                  ‖b * yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x‖ :=
              norm_add_le _ _
            _ = ‖c‖ *
                    ‖yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x‖ +
                  ‖b‖ *
                    ‖yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x‖ := by
              rw [norm_mul, norm_mul]
            _ ≤ ‖c‖ * (1 / 2 : ℝ) + ‖b‖ * (1 / 2 : ℝ) := by
              gcongr
              · exact norm_regularRepresenter0_le_half hx
              · exact norm_regularRepresenter2_le_half hx
            _ = (‖c‖ + ‖b‖) / 2 := by ring
        gcongr
        exact hQ x hx

private theorem exists_norm_atanhTailWeightReciprocalMajorant_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      ‖atanhTailWeightReciprocalMajorant x‖ ≤ C := by
  have hcontinuous : Continuous atanhTailWeightReciprocalMajorant := by
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial
    fun_prop
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hcontinuous.norm.continuousOn
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left 1 M), ?_⟩
  intro x hx
  exact (hM (Set.mem_image_of_mem _ hx)).trans (le_max_right 1 M)

/-- The nonsingular polynomial majorant is integrable for every fixed pair
of low-mode coefficients. -/
theorem intervalIntegrable_fixedProjectedPolynomialRemainderIntegrand
    (c b : ℝ) :
    IntervalIntegrable
      (fixedProjectedPolynomialRemainderIntegrand c b) volume (-1) 1 := by
  have hshift := intervalIntegrable_fixedProjectedShiftedRemainder c b
  have hshiftIoo : IntegrableOn
      (fixedProjectedShiftedRemainder c b) (Ioo (-1) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp hshift
  obtain ⟨C, _hCpos, hC⟩ := exists_norm_fixedProjectedShiftedRemainder_le c b
  have hCae : ∀ᵐ x ∂(volume.restrict (Ioo (-1 : ℝ) 1)),
      ‖fixedProjectedShiftedRemainder c b x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hC x ⟨hx.1.le, hx.2.le⟩
  have hsquare : IntegrableOn
      (fun x ↦ fixedProjectedShiftedRemainder c b x ^ 2)
      (Ioo (-1) 1) volume := by
    have hmul := hshiftIoo.mul_bdd hshiftIoo.aestronglyMeasurable hCae
    simpa only [pow_two] using hmul
  obtain ⟨D, _hDpos, hD⟩ := exists_norm_atanhTailWeightReciprocalMajorant_le
  have hDae : ∀ᵐ x ∂(volume.restrict (Ioo (-1 : ℝ) 1)),
      ‖atanhTailWeightReciprocalMajorant x‖ ≤ D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hD x ⟨hx.1.le, hx.2.le⟩
  have hmajorMeas : AEStronglyMeasurable atanhTailWeightReciprocalMajorant
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    apply Measurable.aestronglyMeasurable
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial
    fun_prop
  have hprod := hsquare.bdd_mul hmajorMeas hDae
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
  apply hprod.congr
  filter_upwards [] with x
  unfold fixedProjectedPolynomialRemainderIntegrand
  ring

/-- The rational transformed-weight remainder is integrable without any
additional hypothesis on the fixed low-mode coefficients. -/
theorem intervalIntegrable_fixedProjectedAtanhRemainderIntegrand
    (c b : ℝ) :
    IntervalIntegrable
      (fixedProjectedAtanhRemainderIntegrand c b) volume (-1) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
  have hpoly : IntegrableOn
      (fixedProjectedPolynomialRemainderIntegrand c b)
      (Ioo (-1) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp
      (intervalIntegrable_fixedProjectedPolynomialRemainderIntegrand c b)
  have hshift : IntegrableOn
      (fixedProjectedShiftedRemainder c b) (Ioo (-1) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp
      (intervalIntegrable_fixedProjectedShiftedRemainder c b)
  have hweightMeas : Measurable yoshidaEndpointEvenAtanhTailWeight := by
    unfold yoshidaEndpointEvenAtanhTailWeight
      YoshidaEndpointPotentialAtanhLower.yoshidaEndpointPotentialAtanhTwoTerm
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fixedProjectedAtanhRemainderIntegrand c b)
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    unfold fixedProjectedAtanhRemainderIntegrand
    simpa only [div_eq_mul_inv] using
      (hshift.aestronglyMeasurable.pow 2).mul
        hweightMeas.inv.aestronglyMeasurable
  apply hpoly.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hden := yoshidaEndpointEvenAtanhTailWeight_pos_on_Icc hxIcc
  have hatanhNonneg :
      0 ≤ fixedProjectedAtanhRemainderIntegrand c b x := by
    unfold fixedProjectedAtanhRemainderIntegrand
    exact div_nonneg (sq_nonneg _) hden.le
  have hle := fixedProjectedAtanhRemainder_le_polynomial c b hxIcc
  have hpolyNonneg :
      0 ≤ fixedProjectedPolynomialRemainderIntegrand c b x :=
    hatanhNonneg.trans hle
  simpa only [Real.norm_eq_abs, abs_of_nonneg hatanhNonneg,
    abs_of_nonneg hpolyNonneg] using hle

/-- The true logarithmic-tail remainder is integrable unconditionally; the
endpoint discrepancy is avoided by working on the measure-equivalent open
interval. -/
theorem intervalIntegrable_fixedProjectedTrueRemainderIntegrand
    (c b : ℝ) :
    IntervalIntegrable
      (fixedProjectedTrueRemainderIntegrand c b) volume (-1) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
  have hatanh : IntegrableOn
      (fixedProjectedAtanhRemainderIntegrand c b)
      (Ioo (-1) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp
      (intervalIntegrable_fixedProjectedAtanhRemainderIntegrand c b)
  have hshift : IntegrableOn
      (fixedProjectedShiftedRemainder c b) (Ioo (-1) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp
      (intervalIntegrable_fixedProjectedShiftedRemainder c b)
  have hweightMeas : Measurable yoshidaEndpointEvenTailWeight := by
    unfold yoshidaEndpointEvenTailWeight
      YoshidaEndpointPotentialBound.yoshidaEndpointPotential
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fixedProjectedTrueRemainderIntegrand c b)
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    unfold fixedProjectedTrueRemainderIntegrand
    simpa only [div_eq_mul_inv] using
      (hshift.aestronglyMeasurable.pow 2).mul
        hweightMeas.inv.aestronglyMeasurable
  apply hatanh.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have htrueDen := yoshidaEndpointEvenTailWeight_pos_on_Icc hxIcc
  have hatanhDen := yoshidaEndpointEvenAtanhTailWeight_pos_on_Icc hxIcc
  have htrueNonneg :
      0 ≤ fixedProjectedTrueRemainderIntegrand c b x := by
    unfold fixedProjectedTrueRemainderIntegrand
    exact div_nonneg (sq_nonneg _) htrueDen.le
  have hatanhNonneg :
      0 ≤ fixedProjectedAtanhRemainderIntegrand c b x := by
    unfold fixedProjectedAtanhRemainderIntegrand
    exact div_nonneg (sq_nonneg _) hatanhDen.le
  have hle : fixedProjectedTrueRemainderIntegrand c b x ≤
      fixedProjectedAtanhRemainderIntegrand c b x := by
    unfold fixedProjectedTrueRemainderIntegrand
      fixedProjectedAtanhRemainderIntegrand
    exact sq_div_tailWeight_le_sq_div_atanhTailWeight
      (fixedProjectedShiftedRemainder c b x) hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg htrueNonneg,
    abs_of_nonneg hatanhNonneg] using hle

/-- Integrability of the constant-basis polynomial remainder moment. -/
theorem intervalIntegrable_fixedProjectedPolynomialRemainderGram00Integrand :
    IntervalIntegrable
      (fun x ↦ atanhTailWeightReciprocalMajorant x *
        fixedProjectedShiftedRemainder0 x ^ 2) volume (-1) 1 := by
  simpa only [fixedProjectedPolynomialRemainderIntegrand,
    fixedProjectedShiftedRemainder0] using
      intervalIntegrable_fixedProjectedPolynomialRemainderIntegrand 1 0

/-- Integrability of the degree-two-basis polynomial remainder moment. -/
theorem intervalIntegrable_fixedProjectedPolynomialRemainderGram22Integrand :
    IntervalIntegrable
      (fun x ↦ atanhTailWeightReciprocalMajorant x *
        fixedProjectedShiftedRemainder2 x ^ 2) volume (-1) 1 := by
  simpa only [fixedProjectedPolynomialRemainderIntegrand,
    fixedProjectedShiftedRemainder2] using
      intervalIntegrable_fixedProjectedPolynomialRemainderIntegrand 0 1

/-- Integrability of the mixed polynomial remainder moment, obtained by
polarizing the already-integrable universal square. -/
theorem intervalIntegrable_fixedProjectedPolynomialRemainderGram02Integrand :
    IntervalIntegrable
      (fun x ↦ atanhTailWeightReciprocalMajorant x *
        fixedProjectedShiftedRemainder0 x *
          fixedProjectedShiftedRemainder2 x) volume (-1) 1 := by
  have h11 := intervalIntegrable_fixedProjectedPolynomialRemainderIntegrand 1 1
  have h10 := intervalIntegrable_fixedProjectedPolynomialRemainderIntegrand 1 0
  have h01 := intervalIntegrable_fixedProjectedPolynomialRemainderIntegrand 0 1
  apply (((h11.sub h10).sub h01).const_mul (1 / 2 : ℝ)).congr
  intro x _hx
  dsimp only
  rw [fixedProjectedPolynomialRemainderIntegrand_eq_gram 1 1 x,
    fixedProjectedPolynomialRemainderIntegrand_eq_gram 1 0 x,
    fixedProjectedPolynomialRemainderIntegrand_eq_gram 0 1 x]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderIntegrable
