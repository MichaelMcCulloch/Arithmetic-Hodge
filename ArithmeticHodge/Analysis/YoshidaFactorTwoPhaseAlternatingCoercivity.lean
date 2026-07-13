import ArithmeticHodge.Analysis.EndpointParityCarleman
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailCoercivity
import ArithmeticHodge.Analysis.YoshidaEndpointTriangleInterchange

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseAlternatingCoercivity

noncomputable section

open EndpointParityCarleman
open YoshidaEndpointTriangleInterchange
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseTailCoercivity

/-!
# Unconditional coercivity of the factor-two alternating channel

Reflection parity turns the ordered correlation difference into one ordered
even--odd correlation.  Folding its overlap triangle at the origin then puts
the endpoint pole on the parity Carleman kernel over the positive unit square.
The two half-profile energies are exactly half of the centered energies, so
the folded `pi` estimate costs only `pi / 2` in centered normalization.
-/

/-- For an even--odd pair, the ordered correlation difference is exactly
`-2` times the even--odd ordering. -/
theorem factorTwo_crossDifference_eq_neg_two_cross_of_even_odd
    {e o : ℝ → ℝ} (he : Function.Even e) (ho : Function.Odd o)
    (t : ℝ) :
    factorTwoCenteredCrossCorrelation o e t -
        factorTwoCenteredCrossCorrelation e o t =
      -2 * factorTwoCenteredCrossCorrelation e o t := by
  rw [factorTwoCenteredCrossCorrelation_swap_of_even_odd he ho]
  ring

/-- Reflection parity halves the energy after either endpoint is transported
to the positive unit interval. -/
theorem endpoint_half_energy_of_even_or_odd
    (w : ℝ → ℝ) (hw : Continuous w)
    (hparity : Function.Even w ∨ Function.Odd w) :
    (∫ p : ℝ in 0..1, w (1 - p) ^ 2) =
      (1 / 2 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let f : ℝ → ℝ := fun x ↦ w x ^ 2
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    rcases hparity with he | ho
    · rw [he x]
    · rw [ho x]
      ring
  have hleft : (∫ x : ℝ in -1..0, f x) = ∫ x : ℝ in 0..1, f x := by
    have hreflect := intervalIntegral.integral_comp_neg
      (f := f) (a := (-1 : ℝ)) (b := 0)
    rw [show (fun x : ℝ ↦ f (-x)) = f by
      funext x
      exact hfeven x] at hreflect
    simpa using hreflect
  have hsplit : (∫ x : ℝ in -1..1, f x) =
      (∫ x : ℝ in -1..0, f x) + ∫ x : ℝ in 0..1, f x := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-1) 0) (hf.intervalIntegrable 0 1)).symm
  have hshift : (∫ p : ℝ in 0..1, f (1 - p)) =
      ∫ x : ℝ in 0..1, f x := by
    simpa only [sub_self, sub_zero] using intervalIntegral.integral_comp_sub_left
      (f := f) (a := (0 : ℝ)) (b := 1) 1
  dsimp only [f] at hleft hsplit hshift ⊢
  rw [hshift]
  rw [hleft] at hsplit
  linarith

/-! ## The parity triangle fold -/

/-- The punctured positive-distance triangle.  Removing its three boundary
segments is measure-theoretically harmless and makes the reciprocal overlap
length pointwise positive on every section used below. -/
private def openPositiveDistanceTriangle : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Ioo (0 : ℝ) 2 ∧ z.2 ∈ Icc (-1) (1 - z.1)}

private theorem measurableSet_openPositiveDistanceTriangle :
    MeasurableSet openPositiveDistanceTriangle := by
  unfold openPositiveDistanceTriangle
  measurability

/-- The bare reciprocal-overlap density is product-integrable on the
positive-distance triangle: each nonexceptional row has integral exactly
one. -/
private theorem integrable_openPositiveDistanceTriangle_pole :
    Integrable
      (openPositiveDistanceTriangle.indicator
        (fun z : ℝ × ℝ ↦ 1 / (2 - z.1)))
      ((volume : Measure ℝ).prod volume) := by
  let B : ℝ × ℝ → ℝ :=
    openPositiveDistanceTriangle.indicator
      (fun z : ℝ × ℝ ↦ 1 / (2 - z.1))
  have hBmeas : Measurable B := by
    dsimp only [B]
    exact (by fun_prop : Measurable (fun z : ℝ × ℝ ↦
      1 / (2 - z.1))).indicator measurableSet_openPositiveDistanceTriangle
  have hrow (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 2) :
      (fun x : ℝ ↦ B (t, x)) =
        (Icc (-1 : ℝ) (1 - t)).indicator
          (fun _x : ℝ ↦ 1 / (2 - t)) := by
    funext x
    by_cases hx : x ∈ Icc (-1 : ℝ) (1 - t)
    · rw [Set.indicator_of_mem hx]
      change openPositiveDistanceTriangle.indicator
          (fun z : ℝ × ℝ ↦ 1 / (2 - z.1)) (t, x) = _
      have hmem : (t, x) ∈ openPositiveDistanceTriangle := ⟨ht, hx⟩
      rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hx]
      change openPositiveDistanceTriangle.indicator
          (fun z : ℝ × ℝ ↦ 1 / (2 - z.1)) (t, x) = 0
      rw [Set.indicator_of_notMem]
      exact fun hmem ↦ hx hmem.2
  have hrowZero (t : ℝ) (ht : t ∉ Ioo (0 : ℝ) 2) :
      (fun x : ℝ ↦ B (t, x)) = 0 := by
    funext x
    change openPositiveDistanceTriangle.indicator
        (fun z : ℝ × ℝ ↦ 1 / (2 - z.1)) (t, x) = 0
    rw [Set.indicator_of_notMem]
    exact fun hmem ↦ ht hmem.1
  have hrowInt : ∀ᵐ t : ℝ ∂volume,
      Integrable (fun x : ℝ ↦ B (t, x)) := by
    filter_upwards [] with t
    by_cases ht : t ∈ Ioo (0 : ℝ) 2
    · rw [hrow t ht]
      exact (integrableOn_const (measure_Icc_lt_top.ne)).integrable_indicator
        measurableSet_Icc
    · rw [hrowZero t ht]
      exact integrable_zero ℝ ℝ volume
  have hrowNorm : ∀ᵐ t : ℝ ∂volume,
      (∫ x : ℝ, ‖B (t, x)‖) =
        (Ioo (0 : ℝ) 2).indicator (fun _t : ℝ ↦ 1) t := by
    filter_upwards [] with t
    by_cases ht : t ∈ Ioo (0 : ℝ) 2
    · rw [Set.indicator_of_mem ht]
      have hnormeq : (fun x : ℝ ↦ ‖B (t, x)‖) =
          fun x : ℝ ↦ ‖(Icc (-1 : ℝ) (1 - t)).indicator
            (fun _x : ℝ ↦ 1 / (2 - t)) x‖ := by
        funext x
        exact congrArg norm (congrFun (hrow t ht) x)
      rw [hnormeq]
      have htlen : 0 < 2 - t := by linarith [ht.2]
      rw [show (fun x : ℝ ↦
          ‖(Icc (-1 : ℝ) (1 - t)).indicator
            (fun _x : ℝ ↦ 1 / (2 - t)) x‖) =
          (Icc (-1 : ℝ) (1 - t)).indicator
            (fun _x : ℝ ↦ 1 / (2 - t)) by
        funext x
        by_cases hx : x ∈ Icc (-1 : ℝ) (1 - t)
        · simp only [Set.indicator_of_mem hx, Real.norm_eq_abs,
            abs_of_pos (one_div_pos.mpr htlen)]
        · simp [Set.indicator_of_notMem hx],
        integral_indicator measurableSet_Icc,
        integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith [ht.1]),
        intervalIntegral.integral_const, smul_eq_mul]
      field_simp [htlen.ne']
      ring
    · rw [Set.indicator_of_notMem ht]
      have hnormeq : (fun x : ℝ ↦ ‖B (t, x)‖) = 0 := by
        funext x
        rw [congrFun (hrowZero t ht) x]
        simp
      rw [hnormeq]
      simp
  have houter : Integrable
      (fun t : ℝ ↦ ∫ x : ℝ, ‖B (t, x)‖) := by
    have hindicator : Integrable
        ((Ioo (0 : ℝ) 2).indicator (fun _t : ℝ ↦ (1 : ℝ))) := by
      have hone : IntegrableOn (fun _t : ℝ ↦ (1 : ℝ)) (Ioo 0 2) :=
        integrableOn_const (by simp)
      exact hone.integrable_indicator measurableSet_Ioo
    apply hindicator.congr
    filter_upwards [hrowNorm] with t ht
    exact ht.symm
  change Integrable B ((volume : Measure ℝ).prod volume)
  exact (integrable_prod_iff hBmeas.aestronglyMeasurable).2
    ⟨hrowInt, houter⟩

/-- A continuous profile product divided by the overlap length is product
integrable on the punctured positive-distance triangle. -/
private theorem integrable_openPositiveDistanceTriangle_profileDensity
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    Integrable
      (openPositiveDistanceTriangle.indicator
        (fun z : ℝ × ℝ ↦ |u (z.1 + z.2) * v z.2| / (2 - z.1)))
      ((volume : Measure ℝ).prod volume) := by
  let H : ℝ × ℝ → ℝ :=
    openPositiveDistanceTriangle.indicator
      (fun z : ℝ × ℝ ↦ |u (z.1 + z.2) * v z.2| / (2 - z.1))
  let B : ℝ × ℝ → ℝ :=
    openPositiveDistanceTriangle.indicator
      (fun z : ℝ × ℝ ↦ 1 / (2 - z.1))
  obtain ⟨Cu, hCu⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)) hu.continuousOn
  obtain ⟨Cv, hCv⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)) hv.continuousOn
  let C : ℝ := |Cu| * |Cv|
  have hC0 : 0 ≤ C := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hB : Integrable B ((volume : Measure ℝ).prod volume) := by
    simpa only [B] using integrable_openPositiveDistanceTriangle_pole
  have hCB : Integrable (fun z ↦ C * B z)
      ((volume : Measure ℝ).prod volume) := hB.const_mul C
  have hHmeas : Measurable H := by
    dsimp only [H]
    exact (by fun_prop : Measurable (fun z : ℝ × ℝ ↦
      |u (z.1 + z.2) * v z.2| / (2 - z.1))).indicator
        measurableSet_openPositiveDistanceTriangle
  change Integrable H ((volume : Measure ℝ).prod volume)
  apply hCB.mono' hHmeas.aestronglyMeasurable
  filter_upwards [] with z
  by_cases hz : z ∈ openPositiveDistanceTriangle
  · have ht0 : 0 < z.1 := hz.1.1
    have ht2 : z.1 < 2 := hz.1.2
    have hx : z.2 ∈ Icc (-1 : ℝ) 1 :=
      ⟨hz.2.1, by linarith [hz.2.2, ht0]⟩
    have hy : z.1 + z.2 ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hz.2.1, ht0], by linarith [hz.2.2]⟩
    have huBound : |u (z.1 + z.2)| ≤ |Cu| := by
      have h := (hCu _ hy).trans (le_abs_self Cu)
      simpa only [Real.norm_eq_abs] using h
    have hvBound : |v z.2| ≤ |Cv| := by
      have h := (hCv _ hx).trans (le_abs_self Cv)
      simpa only [Real.norm_eq_abs] using h
    have hprod : |u (z.1 + z.2) * v z.2| ≤ C := by
      rw [abs_mul]
      exact mul_le_mul huBound hvBound (abs_nonneg _) (abs_nonneg _)
    have hden : 0 < 2 - z.1 := by linarith
    dsimp only [H, B]
    rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    rw [div_eq_mul_inv, one_div]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (abs_nonneg _) (inv_nonneg.mpr hden.le))]
    exact mul_le_mul_of_nonneg_right hprod (inv_nonneg.mpr hden.le)
  · dsimp only [H, B]
    simp [Set.indicator_of_notMem hz]

/-- Fubini identifies the absolute ordered-correlation majorant with the
reciprocal density on the positive-distance triangle. -/
private theorem integral_abs_cross_div_two_sub_eq_openTriangle
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2,
      factorTwoCenteredCrossCorrelation
          (fun x ↦ |u x|) (fun x ↦ |v x|) t / (2 - t)) =
      ∫ z : ℝ × ℝ in openPositiveDistanceTriangle,
        |u (z.1 + z.2) * v z.2| / (2 - z.1) := by
  let ua : ℝ → ℝ := fun x ↦ |u x|
  let va : ℝ → ℝ := fun x ↦ |v x|
  let q : ℝ → ℝ := fun t ↦
    factorTwoCenteredCrossCorrelation ua va t / (2 - t)
  let H : ℝ × ℝ → ℝ :=
    openPositiveDistanceTriangle.indicator
      (fun z : ℝ × ℝ ↦ |u (z.1 + z.2) * v z.2| / (2 - z.1))
  have hua : Continuous ua := by
    dsimp only [ua]
    fun_prop
  have hva : Continuous va := by
    dsimp only [va]
    fun_prop
  have hH : Integrable H ((volume : Measure ℝ).prod volume) := by
    simpa only [H] using
      integrable_openPositiveDistanceTriangle_profileDensity u v hu hv
  have hinner (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 2) :
      (∫ x : ℝ, H (t, x)) = q t := by
    have hrow : (fun x : ℝ ↦ H (t, x)) =
        (Icc (-1 : ℝ) (1 - t)).indicator
          (fun x ↦ |u (t + x) * v x| / (2 - t)) := by
      funext x
      by_cases hx : x ∈ Icc (-1 : ℝ) (1 - t)
      · rw [Set.indicator_of_mem hx]
        change openPositiveDistanceTriangle.indicator
            (fun z : ℝ × ℝ ↦ |u (z.1 + z.2) * v z.2| / (2 - z.1))
              (t, x) = _
        have hmem : (t, x) ∈ openPositiveDistanceTriangle := ⟨ht, hx⟩
        rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hx]
        change openPositiveDistanceTriangle.indicator
            (fun z : ℝ × ℝ ↦ |u (z.1 + z.2) * v z.2| / (2 - z.1))
              (t, x) = 0
        rw [Set.indicator_of_notMem]
        exact fun hmem ↦ hx hmem.2
    rw [show (∫ x : ℝ, H (t, x)) =
        ∫ x : ℝ,
          (Icc (-1 : ℝ) (1 - t)).indicator
            (fun x ↦ |u (t + x) * v x| / (2 - t)) x by
      apply integral_congr_ae
      filter_upwards [] with x
      exact congrFun hrow x,
      integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [ht.2]),
      intervalIntegral.integral_div]
    dsimp only [q]
    congr 1
    unfold factorTwoCenteredCrossCorrelation
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [ua, va]
    rw [abs_mul]
  have hwhole :
      (∫ t : ℝ, (Ioc (0 : ℝ) 2).indicator q t) =
        ∫ t : ℝ, ∫ x : ℝ, H (t, x) := by
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ)] with t ht2
    by_cases ht : t ∈ Ioc (0 : ℝ) 2
    · rw [Set.indicator_of_mem ht]
      exact (hinner t ⟨ht.1, lt_of_le_of_ne ht.2 ht2⟩).symm
    · rw [Set.indicator_of_notMem ht]
      have htOpen : t ∉ Ioo (0 : ℝ) 2 := by
        intro hmem
        exact ht ⟨hmem.1, hmem.2.le⟩
      have hzero : (fun x : ℝ ↦ H (t, x)) = 0 := by
        funext x
        change openPositiveDistanceTriangle.indicator
            (fun z : ℝ × ℝ ↦ |u (z.1 + z.2) * v z.2| / (2 - z.1))
              (t, x) = 0
        rw [Set.indicator_of_notMem]
        exact fun hmem ↦ htOpen hmem.1
      rw [hzero]
      simp
  calc
    (∫ t : ℝ in 0..2,
        factorTwoCenteredCrossCorrelation
            (fun x ↦ |u x|) (fun x ↦ |v x|) t / (2 - t)) =
        ∫ t : ℝ, (Ioc (0 : ℝ) 2).indicator q t := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_indicator measurableSet_Ioc]
    _ = ∫ t : ℝ, ∫ x : ℝ, H (t, x) := hwhole
    _ = ∫ z : ℝ × ℝ, H z := by
      rw [Measure.volume_eq_prod ℝ ℝ]
      rw [← MeasureTheory.integral_prod H hH]
    _ = ∫ z : ℝ × ℝ in openPositiveDistanceTriangle,
        |u (z.1 + z.2) * v z.2| / (2 - z.1) := by
      rw [← integral_indicator measurableSet_openPositiveDistanceTriangle]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseAlternatingCoercivity
