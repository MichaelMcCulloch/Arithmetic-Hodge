import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedBaseIntegrable
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderIntegrable

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedWeightedLp

open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenProjectedBaseIntegrable
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedDualIntegral
open YoshidaEndpointEvenProjectedRemainderIntegrable
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointPotentialBound

noncomputable section

/-- The exact fixed projected dual square is integrable on the endpoint
interval. -/
theorem intervalIntegrable_fixedProjectedDualIntegrand (c b : ℝ) :
    IntervalIntegrable (fixedProjectedDualIntegrand c b)
      volume (-1) 1 := by
  have hbase := intervalIntegrable_fixedProjectedDualBaseIntegrand c b
  have hremainder :=
    intervalIntegrable_fixedProjectedTrueRemainderIntegrand c b
  apply (hbase.add hremainder).congr
  intro x hx
  have hxIoc : x ∈ Ioc (-1 : ℝ) 1 := by
    simpa only [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hxIoc.1.le, hxIoc.2⟩
  exact (fixedProjectedDual_pointwise_decomposition c b hxIcc).symm

private theorem aestronglyMeasurable_fixedProjectedTailRepresenter_linear
    (c b : ℝ) :
    AEStronglyMeasurable
      (fun x : ℝ ↦ c * fixedProjectedTailRepresenter0 x +
        b * fixedProjectedTailRepresenter2 x)
      (volume.restrict (Ioc (-1) 1)) := by
  have hraw0 := intervalIntegrable_evenTailRepresenter_mul
    centeredEvenP0 (fun _ : ℝ ↦ 1)
      (by unfold centeredEvenP0; fun_prop) continuous_const
  have hraw2 := intervalIntegrable_evenTailRepresenter_mul
    centeredEvenP2 (fun _ : ℝ ↦ 1)
      (by unfold centeredEvenP2; fun_prop) continuous_const
  have hprojected0 : IntervalIntegrable fixedProjectedTailRepresenter0
      volume (-1) 1 := by
    simpa only [fixedProjectedTailRepresenter0,
      yoshidaEndpointEvenProjectedTailRepresenter0, mul_one] using
      intervalIntegrable_projectedTailRepresenter_mul
        centeredEvenP0 (fun _ : ℝ ↦ 1) continuous_const
          (73 / 48) (35 / 48) hraw0
  have hprojected2 : IntervalIntegrable fixedProjectedTailRepresenter2
      volume (-1) 1 := by
    simpa only [fixedProjectedTailRepresenter2,
      yoshidaEndpointEvenProjectedTailRepresenter2, mul_one] using
      intervalIntegrable_projectedTailRepresenter_mul
        centeredEvenP2 (fun _ : ℝ ↦ 1) continuous_const
          (7 / 48) (1 / 2) hraw2
  exact ((hprojected0.const_mul c).add
    (hprojected2.const_mul b)).aestronglyMeasurable

private theorem measurable_yoshidaEndpointEvenTailWeight :
    Measurable yoshidaEndpointEvenTailWeight := by
  unfold yoshidaEndpointEvenTailWeight yoshidaEndpointPotential
  fun_prop

/-- Every fixed projected low representer belongs to the weighted dual
`L²` space required by the low/tail Schur argument. -/
theorem fixedProjectedTailRepresenter_div_sqrt_memLp_two (c b : ℝ) :
    MemLp (fun x : ℝ ↦
      (c * fixedProjectedTailRepresenter0 x +
        b * fixedProjectedTailRepresenter2 x) /
          Real.sqrt (yoshidaEndpointEvenTailWeight x)) 2
      (volume.restrict (Ioc (-1) 1)) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦
      (c * fixedProjectedTailRepresenter0 x +
        b * fixedProjectedTailRepresenter2 x) /
          Real.sqrt (yoshidaEndpointEvenTailWeight x))
      (volume.restrict (Ioc (-1) 1)) := by
    simpa only [div_eq_mul_inv] using
      (aestronglyMeasurable_fixedProjectedTailRepresenter_linear c b).mul
        measurable_yoshidaEndpointEvenTailWeight.sqrt.inv.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hdual : Integrable (fixedProjectedDualIntegrand c b)
      (volume.restrict (Ioc (-1) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (intervalIntegrable_fixedProjectedDualIntegrand c b)
  apply hdual.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hweightPos := yoshidaEndpointEvenTailWeight_pos_on_Icc
    (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
  unfold fixedProjectedDualIntegrand
  rw [Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt hweightPos.le]

/-- The retained endpoint tail weight is integrable against the square of
every continuous tail. -/
theorem intervalIntegrable_tailWeight_mul_sq
    (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenTailWeight x * r x ^ 2)
      volume (-1) 1 := by
  have hrSq : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2)
      volume (-1) 1 := (hr.pow 2).intervalIntegrable (-1) 1
  have hpotential := intervalIntegrable_endpointPotential_mul_sq r hr
  apply ((hrSq.const_mul (41 / 60 : ℝ)).add hpotential).congr
  intro x _hx
  unfold yoshidaEndpointEvenTailWeight
  ring

/-- A continuous tail belongs to the weighted primal `L²` space required by
the low/tail Schur argument. -/
theorem sqrt_tailWeight_mul_memLp_two
    (r : ℝ → ℝ) (hr : Continuous r) :
    MemLp (fun x : ℝ ↦
      Real.sqrt (yoshidaEndpointEvenTailWeight x) * r x) 2
      (volume.restrict (Ioc (-1) 1)) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦
      Real.sqrt (yoshidaEndpointEvenTailWeight x) * r x)
      (volume.restrict (Ioc (-1) 1)) :=
    (measurable_yoshidaEndpointEvenTailWeight.sqrt.mul
      hr.measurable).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hweight : Integrable
      (fun x ↦ yoshidaEndpointEvenTailWeight x * r x ^ 2)
      (volume.restrict (Ioc (-1) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (intervalIntegrable_tailWeight_mul_sq r hr)
  apply hweight.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hweightPos := yoshidaEndpointEvenTailWeight_pos_on_Icc
    (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
  rw [Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt hweightPos.le]

/-- The raw constant-mode tail representer pairs integrably with every
continuous tail. -/
theorem intervalIntegrable_yoshidaEndpointEvenTailRepresenter0_mul
    (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenTailRepresenter0 x * r x)
      volume (-1) 1 := by
  simpa only [yoshidaEndpointEvenTailRepresenter0] using
    intervalIntegrable_evenTailRepresenter_mul centeredEvenP0 r
      (by unfold centeredEvenP0; fun_prop) hr

/-- The raw degree-two tail representer pairs integrably with every
continuous tail. -/
theorem intervalIntegrable_yoshidaEndpointEvenTailRepresenter2_mul
    (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenTailRepresenter2 x * r x)
      volume (-1) 1 := by
  simpa only [yoshidaEndpointEvenTailRepresenter2] using
    intervalIntegrable_evenTailRepresenter_mul centeredEvenP2 r
      (by unfold centeredEvenP2; fun_prop) hr

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedWeightedLp
