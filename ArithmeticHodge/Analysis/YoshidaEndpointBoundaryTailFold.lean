import ArithmeticHodge.Analysis.YoshidaEndpointSingularCorrelation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointBoundaryTailFold

open YoshidaEndpointPotentialBound
open YoshidaEndpointSingularCorrelation

noncomputable section

/-!
# Endpoint boundary-tail fold

The endpoint tail is folded structurally by Fubini on the two triangular
regions.  For a fixed interior point `x`, the right triangle contributes
`∫ t in 1 - x..2, 1 / t`, hence `log 2 - log (1 - x)`; the left triangle is
its reflection.  The isolated singular section at `t = 0` and the logarithmic
endpoint conventions at `x = ±1` are discarded only as null sets.
-/

private theorem right_boundary_fold
    (w : ℝ → ℝ) (hw : Continuous w) :
    IntervalIntegrable
        (fun t : ℝ ↦ (∫ x : ℝ in 1 - t..1, w x ^ 2) / t)
        volume 0 2 ∧
      (∫ t : ℝ in 0..2, (∫ x : ℝ in 1 - t..1, w x ^ 2) / t) =
        Real.log 2 * (∫ x : ℝ in -1..1, w x ^ 2) -
          ∫ x : ℝ in -1..1, Real.log (1 - x) * w x ^ 2 := by
  let g : ℝ → ℝ := fun x ↦ w x ^ 2
  let R : ℝ × ℝ → ℝ := fun p ↦
    if p.1 ∈ Ioc (0 : ℝ) 2 ∧ p.2 ∈ Ioc (1 - p.1) 1 then
      g p.2 / p.1
    else 0
  let Q : ℝ → ℝ := fun x ↦
    (Ioo (-1 : ℝ) 1).indicator
      (fun y ↦ g y * (Real.log 2 - Real.log (1 - y))) x
  have hg : Continuous g := hw.pow 2
  have hRMeas : Measurable R := by
    dsimp only [R]
    apply Measurable.ite
    · simp only [Set.mem_Ioc]
      exact ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const)).inter
          ((measurableSet_lt (measurable_const.sub measurable_fst) measurable_snd).inter
            (measurableSet_le measurable_snd measurable_const))
    · fun_prop
    · fun_prop
  have hlog : IntervalIntegrable Real.log volume 0 2 :=
    intervalIntegral.intervalIntegrable_log'
  have hlogMinus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 - x)) volume (-1) 1 := by
    convert (hlog.comp_sub_left 1).symm using 1 <;> norm_num
  have hlogMinusG : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 - x) * g x) volume (-1) 1 :=
    by simpa only [mul_comm] using
      hlogMinus.continuousOn_mul hg.continuousOn
  have hconstG : IntervalIntegrable
      (fun x : ℝ ↦ Real.log 2 * g x) volume (-1) 1 :=
    (hg.const_mul (Real.log 2)).intervalIntegrable (-1) 1
  have hQInterval : IntervalIntegrable
      (fun x : ℝ ↦ g x * (Real.log 2 - Real.log (1 - x)))
      volume (-1) 1 := by
    have h := hconstG.sub hlogMinusG
    simpa only [mul_sub, mul_comm] using h
  have hQInt : Integrable Q := by
    have hQOnIoc : IntegrableOn
        (fun x : ℝ ↦ g x * (Real.log 2 - Real.log (1 - x)))
        (Ioc (-1) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hQInterval
    have hQOnIoo := hQOnIoc.mono_set Ioo_subset_Ioc_self
    simpa only [Q] using hQOnIoo.integrable_indicator measurableSet_Ioo
  have hsection (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
      (fun t : ℝ ↦ R (t, x)) =
        (Ioc (1 - x) 2).indicator (fun t ↦ g x / t) := by
    funext t
    by_cases ht : t ∈ Ioc (1 - x) 2
    · have ht0 : t ∈ Ioc (0 : ℝ) 2 :=
        ⟨by linarith [hx.2, ht.1], ht.2⟩
      have hxt : x ∈ Ioc (1 - t) 1 := ⟨by linarith [ht.1], hx.2.le⟩
      simp only [R, ht0, hxt, and_self, if_true, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      simp only [R]
      split_ifs with h
      · exfalso
        apply ht
        exact ⟨by linarith [h.2.1], h.1.2⟩
      · rfl
  have hsectionInt (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
      Integrable (fun t : ℝ ↦ R (t, x)) := by
    rw [hsection x hx]
    apply IntegrableOn.integrable_indicator
    · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [hx.1])]
      apply ContinuousOn.intervalIntegrable
      intro t ht
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.div continuousAt_const continuousAt_id
      have hle : 1 - x ≤ 2 := by linarith [hx.1]
      rw [uIcc_of_le hle] at ht
      exact ne_of_gt (lt_of_lt_of_le (by linarith [hx.2]) ht.1)
    · exact measurableSet_Ioc
  have hsectionNorm (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
      (∫ t : ℝ, ‖R (t, x)‖) =
        g x * (Real.log 2 - Real.log (1 - x)) := by
    have hnormfun : (fun t : ℝ ↦ ‖R (t, x)‖) =
        fun t ↦ ‖(Ioc (1 - x) 2).indicator (fun u ↦ g x / u) t‖ := by
      funext t
      rw [show R (t, x) = (Ioc (1 - x) 2).indicator
          (fun u ↦ g x / u) t from congrFun (hsection x hx) t]
    rw [hnormfun]
    have hg0 : 0 ≤ g x := by
      exact sq_nonneg (w x)
    have hpos : 0 < 1 - x := by linarith [hx.2]
    have hle : 1 - x ≤ 2 := by linarith [hx.1]
    rw [show (fun t : ℝ ↦ ‖(Ioc (1 - x) 2).indicator
          (fun u ↦ g x / u) t‖) =
        (Ioc (1 - x) 2).indicator (fun t ↦ g x / t) by
      funext t
      by_cases ht : t ∈ Ioc (1 - x) 2
      · simp only [Set.indicator_of_mem ht]
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact div_nonneg hg0 (lt_trans hpos ht.1).le
      · simp [Set.indicator_of_notMem ht]]
    rw [integral_indicator measurableSet_Ioc]
    rw [← intervalIntegral.integral_of_le hle]
    rw [show (fun t : ℝ ↦ g x / t) = fun t ↦ g x * t⁻¹ by
      funext t
      rw [div_eq_mul_inv]]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_inv_of_pos hpos (by norm_num)]
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt hpos)]
  have hsectionZero (x : ℝ) (hx : x ∉ Ioo (-1 : ℝ) 1)
      (hxneg : x ≠ -1) (hxpos : x ≠ 1) :
      (fun t : ℝ ↦ R (t, x)) = 0 := by
    funext t
    simp only [R, Pi.zero_apply]
    split_ifs with h
    · exfalso
      have hxgt : -1 < x := by linarith [h.1.2, h.2.1]
      have hxle : x ≤ 1 := h.2.2
      apply hx
      exact ⟨hxgt, lt_of_le_of_ne hxle hxpos⟩
    · rfl
  have hRInt : Integrable R ((volume : Measure ℝ).prod volume) := by
    rw [integrable_prod_iff' hRMeas.aestronglyMeasurable]
    constructor
    · filter_upwards [MeasureTheory.Measure.ae_ne volume (-1 : ℝ),
        MeasureTheory.Measure.ae_ne volume (1 : ℝ)] with x hxneg hxpos
      by_cases hx : x ∈ Ioo (-1 : ℝ) 1
      · exact hsectionInt x hx
      · rw [hsectionZero x hx hxneg hxpos]
        exact integrable_zero ℝ ℝ volume
    · apply hQInt.congr
      filter_upwards [MeasureTheory.Measure.ae_ne volume (-1 : ℝ),
        MeasureTheory.Measure.ae_ne volume (1 : ℝ)] with x hxneg hxpos
      by_cases hx : x ∈ Ioo (-1 : ℝ) 1
      · rw [hsectionNorm x hx]
        simp [Q, hx]
      · have hzero := hsectionZero x hx hxneg hxpos
        have hnormzero : (fun t : ℝ ↦ ‖R (t, x)‖) = 0 := by
          funext t
          rw [show R (t, x) = 0 from congrFun hzero t]
          simp
        rw [hnormzero]
        simp [Q, hx]
  have hinner (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 2) :
      (∫ x : ℝ, R (t, x)) = (∫ x : ℝ in 1 - t..1, g x) / t := by
    have hle : 1 - t ≤ 1 := by linarith [ht.1]
    rw [show (fun x : ℝ ↦ R (t, x)) =
        (Ioc (1 - t) 1).indicator (fun x ↦ g x / t) by
      funext x
      by_cases hx : x ∈ Ioc (1 - t) 1
      · simp only [Set.indicator_of_mem hx, R, ht, hx, and_self, if_true]
      · rw [Set.indicator_of_notMem hx]
        simp only [R]
        split_ifs with h
        · exact False.elim (hx h.2)
        · rfl]
    rw [integral_indicator measurableSet_Ioc]
    rw [← intervalIntegral.integral_of_le hle]
    rw [intervalIntegral.integral_div]
  have houterEq :
      (∫ t : ℝ in 0..2, (∫ x : ℝ in 1 - t..1, g x) / t) =
        ∫ t : ℝ, ∫ x : ℝ, R (t, x) := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t ∈ Ioc (0 : ℝ) 2
    · rw [Set.indicator_of_mem ht, hinner t ht]
    · rw [Set.indicator_of_notMem ht]
      have hzero : (fun x : ℝ ↦ R (t, x)) = 0 := by
        funext x
        simp only [R, Pi.zero_apply]
        split_ifs with h
        · exact False.elim (ht h.1)
        · rfl
      rw [hzero]
      simp
  have houterIndicatorInt : Integrable
      ((Ioc (0 : ℝ) 2).indicator
        (fun t : ℝ ↦ (∫ x : ℝ in 1 - t..1, g x) / t)) := by
    have hiter := hRInt.integral_prod_left
    apply hiter.congr
    filter_upwards [] with t
    by_cases ht : t ∈ Ioc (0 : ℝ) 2
    · rw [Set.indicator_of_mem ht]
      exact hinner t ht
    · rw [Set.indicator_of_notMem ht]
      have hzero : (fun x : ℝ ↦ R (t, x)) = 0 := by
        funext x
        simp only [R, Pi.zero_apply]
        split_ifs with h
        · exact False.elim (ht h.1)
        · rfl
      rw [hzero]
      simp
  have hrightInterval : IntervalIntegrable
      (fun t : ℝ ↦ (∫ x : ℝ in 1 - t..1, g x) / t)
      volume 0 2 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    rw [← integrable_indicator_iff measurableSet_Ioc]
    exact houterIndicatorInt
  have hswapped :
      (∫ t : ℝ, ∫ x : ℝ, R (t, x)) =
        ∫ x : ℝ, ∫ t : ℝ, R (t, x) :=
    integral_integral_swap hRInt
  have hswappedValue :
      (∫ x : ℝ, ∫ t : ℝ, R (t, x)) =
        ∫ x : ℝ in -1..1,
          g x * (Real.log 2 - Real.log (1 - x)) := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (-1 : ℝ),
      MeasureTheory.Measure.ae_ne volume (1 : ℝ)] with x hxneg hxpos
    by_cases hx : x ∈ Ioo (-1 : ℝ) 1
    · have hnorm := hsectionNorm x hx
      have hnonneg : ∀ t, 0 ≤ R (t, x) := by
        intro t
        simp only [R]
        split_ifs with h
        · exact div_nonneg (sq_nonneg (w x)) h.1.1.le
        · exact le_rfl
      have hval : (∫ t : ℝ, R (t, x)) =
          g x * (Real.log 2 - Real.log (1 - x)) := by
        rw [← hnorm]
        apply integral_congr_ae
        filter_upwards [] with t
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t)]
      have hxIoc : x ∈ Ioc (-1 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
      rw [Set.indicator_of_mem hxIoc, hval]
    · have hxIoc : x ∉ Ioc (-1 : ℝ) 1 := by
        intro hmem
        apply hx
        exact ⟨hmem.1, lt_of_le_of_ne hmem.2 hxpos⟩
      rw [Set.indicator_of_notMem hxIoc, hsectionZero x hx hxneg hxpos]
      simp
  refine ⟨?_, ?_⟩
  · simpa only [g] using hrightInterval
  · calc
      (∫ t : ℝ in 0..2, (∫ x : ℝ in 1 - t..1, w x ^ 2) / t) =
          ∫ t : ℝ, ∫ x : ℝ, R (t, x) := by simpa only [g] using houterEq
      _ = ∫ x : ℝ, ∫ t : ℝ, R (t, x) := hswapped
      _ = ∫ x : ℝ in -1..1,
          g x * (Real.log 2 - Real.log (1 - x)) := hswappedValue
      _ = Real.log 2 * (∫ x : ℝ in -1..1, w x ^ 2) -
          ∫ x : ℝ in -1..1, Real.log (1 - x) * w x ^ 2 := by
        rw [show (fun x : ℝ ↦ g x * (Real.log 2 - Real.log (1 - x))) =
            fun x ↦ Real.log 2 * w x ^ 2 - Real.log (1 - x) * w x ^ 2 by
          funext x
          simp only [g]
          ring]
        rw [intervalIntegral.integral_sub hconstG hlogMinusG,
          intervalIntegral.integral_const_mul]

/-- The boundary-tail quotient is interval integrable.  At `t = 0` its
written value uses Lean's totalized division, but the proof passes through the
punctured interval `Ioc 0 2`, so no singular point is assigned analytic
weight. -/
theorem intervalIntegrable_centeredEndpointBoundaryTail_div
    (w : ℝ → ℝ) (hw : Continuous w) :
    IntervalIntegrable
      (fun t : ℝ ↦ centeredEndpointBoundaryTail w t / t)
      volume 0 2 := by
  let v : ℝ → ℝ := fun x ↦ w (-x)
  have hv : Continuous v := by
    dsimp only [v]
    fun_prop
  have hright := (right_boundary_fold w hw).1
  have hleftReflected := (right_boundary_fold v hv).1
  have hreflect (t : ℝ) :
      (∫ x : ℝ in 1 - t..1, v x ^ 2) =
        ∫ x : ℝ in -1..-1 + t, w x ^ 2 := by
    calc
      (∫ x : ℝ in 1 - t..1, v x ^ 2) =
          ∫ x : ℝ in -1..-(1 - t), w x ^ 2 := by
        simpa only [v, neg_neg] using
          (intervalIntegral.integral_comp_neg
            (f := fun x : ℝ ↦ w x ^ 2) (a := 1 - t) (b := 1))
      _ = ∫ x : ℝ in -1..-1 + t, w x ^ 2 := by
        congr 1
        ring
  have hleft : IntervalIntegrable
      (fun t : ℝ ↦ (∫ x : ℝ in -1..-1 + t, w x ^ 2) / t)
      volume 0 2 := by
    apply hleftReflected.congr
    intro t _ht
    change (∫ x : ℝ in 1 - t..1, v x ^ 2) / t =
      (∫ x : ℝ in -1..-1 + t, w x ^ 2) / t
    rw [hreflect t]
  have hsum := hright.add hleft
  apply hsum.congr
  intro t _ht
  unfold centeredEndpointBoundaryTail
  ring

/-- Folding both endpoint triangles gives the endpoint potential plus the
constant `log 2` mass.  The identity
`log (1 - x^2) = log (1 - x) + log (1 + x)` is used only almost everywhere;
the exceptional endpoint conventions at `x = ±1` therefore play no role. -/
theorem half_integral_centeredEndpointBoundaryTail_div_eq
    (w : ℝ → ℝ) (hw : Continuous w) :
    (1 / 2 : ℝ) *
        (∫ t : ℝ in 0..2, centeredEndpointBoundaryTail w t / t) =
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) +
        Real.log 2 * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let v : ℝ → ℝ := fun x ↦ w (-x)
  have hv : Continuous v := by
    dsimp only [v]
    fun_prop
  have hright := (right_boundary_fold w hw).2
  have hleftRaw := (right_boundary_fold v hv).2
  have hmassReflect : (∫ x : ℝ in -1..1, v x ^ 2) =
      ∫ x : ℝ in -1..1, w x ^ 2 := by
    simpa only [v, neg_neg] using
      (intervalIntegral.integral_comp_neg
        (f := fun x : ℝ ↦ w x ^ 2) (a := (-1 : ℝ)) (b := 1))
  have hlogReflect :
      (∫ x : ℝ in -1..1, Real.log (1 - x) * v x ^ 2) =
        ∫ x : ℝ in -1..1, Real.log (1 + x) * w x ^ 2 := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun x : ℝ ↦ Real.log (1 + x) * w x ^ 2)
      (a := (-1 : ℝ)) (b := 1)
    simpa only [v, neg_neg, add_neg_cancel_left] using h
  have hreflect (t : ℝ) :
      (∫ x : ℝ in 1 - t..1, v x ^ 2) =
        ∫ x : ℝ in -1..-1 + t, w x ^ 2 := by
    calc
      (∫ x : ℝ in 1 - t..1, v x ^ 2) =
          ∫ x : ℝ in -1..-(1 - t), w x ^ 2 := by
        simpa only [v, neg_neg] using
          (intervalIntegral.integral_comp_neg
            (f := fun x : ℝ ↦ w x ^ 2) (a := 1 - t) (b := 1))
      _ = ∫ x : ℝ in -1..-1 + t, w x ^ 2 := by
        congr 1
        ring
  have hleft :
      (∫ t : ℝ in 0..2, (∫ x : ℝ in -1..-1 + t, w x ^ 2) / t) =
        Real.log 2 * (∫ x : ℝ in -1..1, w x ^ 2) -
          ∫ x : ℝ in -1..1, Real.log (1 + x) * w x ^ 2 := by
    rw [← hmassReflect, ← hlogReflect, ← hleftRaw]
    apply intervalIntegral.integral_congr
    intro t _ht
    change (∫ x : ℝ in -1..-1 + t, w x ^ 2) / t =
      (∫ x : ℝ in 1 - t..1, v x ^ 2) / t
    rw [hreflect t]
  have hrightInt := (right_boundary_fold w hw).1
  have hleftInt : IntervalIntegrable
      (fun t : ℝ ↦ (∫ x : ℝ in -1..-1 + t, w x ^ 2) / t)
      volume 0 2 := by
    have href := (right_boundary_fold v hv).1
    apply href.congr
    intro t _ht
    change (∫ x : ℝ in 1 - t..1, v x ^ 2) / t =
      (∫ x : ℝ in -1..-1 + t, w x ^ 2) / t
    rw [hreflect t]
  have hsplit :
      (∫ t : ℝ in 0..2, centeredEndpointBoundaryTail w t / t) =
        (∫ t : ℝ in 0..2, (∫ x : ℝ in 1 - t..1, w x ^ 2) / t) +
          ∫ t : ℝ in 0..2, (∫ x : ℝ in -1..-1 + t, w x ^ 2) / t := by
    calc
      _ = ∫ t : ℝ in 0..2,
          ((∫ x : ℝ in 1 - t..1, w x ^ 2) / t +
            (∫ x : ℝ in -1..-1 + t, w x ^ 2) / t) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        unfold centeredEndpointBoundaryTail
        ring
      _ = _ := intervalIntegral.integral_add hrightInt hleftInt
  have hpotential :
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) =
        -(1 / 2 : ℝ) *
          ((∫ x : ℝ in -1..1, Real.log (1 - x) * w x ^ 2) +
            ∫ x : ℝ in -1..1, Real.log (1 + x) * w x ^ 2) := by
    have hminusBase : IntervalIntegrable
        (fun x : ℝ ↦ Real.log (1 - x)) volume (-1) 1 := by
      have hlog : IntervalIntegrable Real.log volume 0 2 :=
        intervalIntegral.intervalIntegrable_log'
      convert (hlog.comp_sub_left 1).symm using 1 <;> norm_num
    have hplusBase : IntervalIntegrable
        (fun x : ℝ ↦ Real.log (1 + x)) volume (-1) 1 := by
      have hlog : IntervalIntegrable Real.log volume 0 2 :=
        intervalIntegral.intervalIntegrable_log'
      convert hlog.comp_add_left 1 using 1 <;> norm_num
    have hwSq : Continuous (fun x : ℝ ↦ w x ^ 2) := hw.pow 2
    have hminus : IntervalIntegrable
        (fun x : ℝ ↦ Real.log (1 - x) * w x ^ 2) volume (-1) 1 := by
      simpa only [mul_comm] using
        hminusBase.continuousOn_mul hwSq.continuousOn
    have hplus : IntervalIntegrable
        (fun x : ℝ ↦ Real.log (1 + x) * w x ^ 2) volume (-1) 1 := by
      simpa only [mul_comm] using
        hplusBase.continuousOn_mul hwSq.continuousOn
    rw [← intervalIntegral.integral_add hminus hplus,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-1 : ℝ)] with x hx1 hxneg1
    have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    have hadd : 1 + x ≠ 0 := by
      intro hzero
      apply hxneg1
      linarith
    intro _hx
    unfold yoshidaEndpointPotential
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
      Real.log_mul hsub hadd]
    ring
  rw [hsplit, hright, hleft, hpotential]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointBoundaryTailFold
