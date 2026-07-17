import ArithmeticHodge.Analysis.YoshidaFactorTwoContinuousLagRepresenterStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoIntegrableLagRepresenterStructural

open YoshidaEndpointTriangleInterchange
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaRegularKernelBound

noncomputable section

/-!
# Representers for bounded measurable lag kernels

The removable analytic lag kernels in the factor-two decomposition are
bounded and measurable on the physical lag interval, but their global
continuity would require a separate removable-singularity theorem.  This
module derives the same one-variable representers directly from Fubini.
-/

/-- The ordered density in centered upper-triangle coordinates. -/
def factorTwoLagUpperDensity
    (q u v : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  q (z.1 - z.2) * u z.1 * v z.2

/-- The same ordered density in positive-distance coordinates. -/
def factorTwoLagDistanceDensity
    (q u v : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  q z.1 * u (z.1 + z.2) * v z.2

/-- A measurable lag kernel bounded on `[0,2]` gives an integrable ordered
density on the centered upper triangle for continuous profiles. -/
theorem integrableOn_factorTwoLagUpperDensity_of_bounded
    (q u v : ℝ → ℝ) (hq : Measurable q)
    (hu : Continuous u) (hv : Continuous v)
    (C : ℝ)
    (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    IntegrableOn (factorTwoLagUpperDensity q u v)
      centeredUpperTriangle ((volume : Measure ℝ).prod volume) := by
  let S : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
  let g : ℝ × ℝ → ℝ := fun z ↦ C * |u z.1| * |v z.2|
  have hgS : IntegrableOn g S ((volume : Measure ℝ).prod volume) := by
    apply ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
    exact ((continuous_const.mul (hu.comp continuous_fst).abs).mul
      (hv.comp continuous_snd).abs).continuousOn
  have hUS : centeredUpperTriangle ⊆ S := by
    intro z hz
    unfold centeredUpperTriangle at hz
    exact ⟨⟨by linarith [hz.1, hz.2.1], hz.2.2⟩,
      ⟨hz.1, by linarith [hz.2.1, hz.2.2]⟩⟩
  have hgU : IntegrableOn g centeredUpperTriangle
      ((volume : Measure ℝ).prod volume) := hgS.mono_set hUS
  apply hgU.mono'
  · unfold factorTwoLagUpperDensity
    exact (((hq.comp (measurable_fst.sub measurable_snd)).mul
      (hu.measurable.comp measurable_fst)).mul
        (hv.measurable.comp measurable_snd)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (by
        unfold centeredUpperTriangle
        measurability : MeasurableSet centeredUpperTriangle)] with z hz
    have hlag : z.1 - z.2 ∈ Icc (0 : ℝ) 2 := by
      unfold centeredUpperTriangle at hz
      exact ⟨by linarith [hz.2.1], by linarith [hz.1, hz.2.2]⟩
    have hqbound := hqC (z.1 - z.2) hlag
    dsimp only [factorTwoLagUpperDensity, g]
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hqbound (abs_nonneg (u z.1)))
      (abs_nonneg (v z.2))

/-- The corresponding positive-distance density is integrable under the
same bounded-measurable hypothesis. -/
theorem integrableOn_factorTwoLagDistanceDensity_of_bounded
    (q u v : ℝ → ℝ) (hq : Measurable q)
    (hu : Continuous u) (hv : Continuous v)
    (C : ℝ)
    (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    IntegrableOn (factorTwoLagDistanceDensity q u v)
      positiveDistanceTriangle ((volume : Measure ℝ).prod volume) := by
  let S : Set (ℝ × ℝ) := Icc (0 : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1
  let g : ℝ × ℝ → ℝ := fun z ↦ C * |u (z.1 + z.2)| * |v z.2|
  have hgS : IntegrableOn g S ((volume : Measure ℝ).prod volume) := by
    apply ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
    exact ((continuous_const.mul (hu.comp (continuous_fst.add continuous_snd)).abs).mul
      (hv.comp continuous_snd).abs).continuousOn
  have hTS : positiveDistanceTriangle ⊆ S := by
    intro z hz
    unfold positiveDistanceTriangle at hz
    exact ⟨⟨hz.1, hz.2.1⟩,
      ⟨hz.2.2.1, by linarith [hz.1, hz.2.2.2]⟩⟩
  have hgT : IntegrableOn g positiveDistanceTriangle
      ((volume : Measure ℝ).prod volume) := hgS.mono_set hTS
  apply hgT.mono'
  · unfold factorTwoLagDistanceDensity
    exact (((hq.comp measurable_fst).mul
      (hu.measurable.comp (measurable_fst.add measurable_snd))).mul
        (hv.measurable.comp measurable_snd)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (by
        unfold positiveDistanceTriangle
        measurability : MeasurableSet positiveDistanceTriangle)] with z hz
    have hlag : z.1 ∈ Icc (0 : ℝ) 2 := ⟨hz.1, hz.2.1⟩
    have hqbound := hqC z.1 hlag
    dsimp only [factorTwoLagDistanceDensity, g]
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hqbound (abs_nonneg (u (z.1 + z.2))))
      (abs_nonneg (v z.2))

/-- Fubini and the unit-Jacobian shear identify the lag integral with the
upper-triangle density without any continuity assumption on the lag kernel. -/
theorem integral_weight_mul_crossCorrelation_eq_upperTriangle_of_bounded
    (q u v : ℝ → ℝ) (hq : Measurable q)
    (hu : Continuous u) (hv : Continuous v)
    (C : ℝ)
    (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    (∫ t : ℝ in 0..2,
        q t * factorTwoCenteredCrossCorrelation u v t) =
      ∫ z : ℝ × ℝ in centeredUpperTriangle,
        factorTwoLagUpperDensity q u v z := by
  let H : ℝ × ℝ → ℝ := factorTwoLagDistanceDensity q u v
  have hTmeas : MeasurableSet positiveDistanceTriangle := by
    unfold positiveDistanceTriangle
    measurability
  have hHTriangle : IntegrableOn H positiveDistanceTriangle
      ((volume : Measure ℝ).prod volume) := by
    simpa only [H] using
      integrableOn_factorTwoLagDistanceDensity_of_bounded
        q u v hq hu hv C hqC
  have hHIndicator : Integrable
      (positiveDistanceTriangle.indicator H)
      ((volume : Measure ℝ).prod volume) :=
    hHTriangle.integrable_indicator hTmeas
  have hOuter :
      (∫ t : ℝ in 0..2,
          q t * factorTwoCenteredCrossCorrelation u v t) =
        ∫ t : ℝ in 0..2, ∫ x : ℝ in -1..1 - t, H (t, x) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    unfold factorTwoCenteredCrossCorrelation
    change q t * (∫ x : ℝ in -1..1 - t, u (t + x) * v x) =
      ∫ x : ℝ in -1..1 - t, q t * u (t + x) * v x
    rw [show (fun x : ℝ ↦ q t * u (t + x) * v x) =
        fun x ↦ q t * (u (t + x) * v x) by
      funext x
      ring,
      intervalIntegral.integral_const_mul]
  have hTriangleFold :
      (∫ t : ℝ in 0..2, ∫ x : ℝ in -1..1 - t, H (t, x)) =
        ∫ z : ℝ × ℝ in positiveDistanceTriangle, H z := by
    rw [← integral_indicator hTmeas,
      Measure.volume_eq_prod ℝ ℝ,
      integral_prod _ hHIndicator]
    rw [intervalIntegral.integral_of_le (by norm_num),
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with t ht0
    by_cases ht : t ∈ Ioc (0 : ℝ) 2
    · rw [Set.indicator_of_mem ht]
      calc
        (∫ x : ℝ in -1..1 - t, H (t, x)) =
            ∫ x : ℝ,
              (Icc (-1 : ℝ) (1 - t)).indicator (fun x ↦ H (t, x)) x := by
          rw [intervalIntegral.integral_of_le (by linarith [ht.2]),
            ← integral_Icc_eq_integral_Ioc,
            ← integral_indicator measurableSet_Icc]
        _ = ∫ x : ℝ,
            positiveDistanceTriangle.indicator H (t, x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          by_cases hx : x ∈ Icc (-1 : ℝ) (1 - t)
          · have hp : (t, x) ∈ positiveDistanceTriangle :=
                ⟨ht.1.le, ht.2, hx.1, hx.2⟩
            rw [Set.indicator_of_mem hx, Set.indicator_of_mem hp]
          · have hp : (t, x) ∉ positiveDistanceTriangle := by
              intro hp
              exact hx ⟨hp.2.2.1, hp.2.2.2⟩
            rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hp]
    · rw [Set.indicator_of_notMem ht]
      have hrow : (fun x : ℝ ↦
          positiveDistanceTriangle.indicator H (t, x)) = 0 := by
        funext x
        by_cases hp : (t, x) ∈ positiveDistanceTriangle
        · exfalso
          apply ht
          exact ⟨lt_of_le_of_ne hp.1 (Ne.symm ht0), hp.2.1⟩
        · rw [Set.indicator_of_notMem hp]
          rfl
      rw [hrow]
      simp
  calc
    (∫ t : ℝ in 0..2,
        q t * factorTwoCenteredCrossCorrelation u v t) =
        ∫ t : ℝ in 0..2, ∫ x : ℝ in -1..1 - t, H (t, x) := hOuter
    _ = ∫ z : ℝ × ℝ in positiveDistanceTriangle, H z := hTriangleFold
    _ = ∫ z : ℝ × ℝ in centeredUpperTriangle,
        factorTwoLagUpperDensity q u v z := by
      simpa only [H, factorTwoLagDistanceDensity,
        factorTwoLagUpperDensity, add_sub_cancel_right] using
        setIntegral_positiveDistanceTriangle_shear
          (factorTwoLagUpperDensity q u v)

/-! ## Integrable disintegration and ordered representers -/

/-- Fubini makes the right-coordinate iterated integral interval-integrable
whenever the original upper-triangle density is integrable. -/
theorem intervalIntegrable_iterated_right_of_integrable
    (F : ℝ × ℝ → ℝ)
    (hFUpper : IntegrableOn F centeredUpperTriangle
      ((volume : Measure ℝ).prod volume)) :
    IntervalIntegrable (fun x : ℝ ↦ ∫ y : ℝ in x..1, F (y, x))
      volume (-1) 1 := by
  let U : Set (ℝ × ℝ) := centeredUpperTriangle
  have hUmeas : MeasurableSet U := by
    dsimp only [U]
    unfold centeredUpperTriangle
    measurability
  have hFU : IntegrableOn F U ((volume : Measure ℝ).prod volume) := by
    simpa only [U] using hFUpper
  have hFI : Integrable (U.indicator F)
      ((volume : Measure ℝ).prod volume) :=
    hFU.integrable_indicator hUmeas
  have houter := hFI.integral_prod_right
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  change Integrable _ (volume.restrict (Ioc (-1 : ℝ) 1))
  apply (houter.mono_measure Measure.restrict_le_self).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hrow : (fun y : ℝ ↦ U.indicator F (y, x)) =
      (Icc x 1).indicator (fun y ↦ F (y, x)) := by
    funext y
    have hmem : (y, x) ∈ U ↔ y ∈ Icc x 1 := by
      dsimp only [U]
      unfold centeredUpperTriangle
      constructor
      · intro h
        exact ⟨h.2.1, h.2.2⟩
      · intro h
        exact ⟨hx.1.le, h.1, h.2⟩
    by_cases hy : y ∈ Icc x 1
    · rw [Set.indicator_of_mem hy,
        Set.indicator_of_mem (hmem.mpr hy)]
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (mt hmem.mp hy)]
  rw [hrow, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hx.2]

/-- Left-coordinate version of
`intervalIntegrable_iterated_right_of_integrable`. -/
theorem intervalIntegrable_iterated_left_of_integrable
    (F : ℝ × ℝ → ℝ)
    (hFUpper : IntegrableOn F centeredUpperTriangle
      ((volume : Measure ℝ).prod volume)) :
    IntervalIntegrable (fun x : ℝ ↦ ∫ y : ℝ in -1..x, F (x, y))
      volume (-1) 1 := by
  let U : Set (ℝ × ℝ) := centeredUpperTriangle
  have hUmeas : MeasurableSet U := by
    dsimp only [U]
    unfold centeredUpperTriangle
    measurability
  have hFU : IntegrableOn F U ((volume : Measure ℝ).prod volume) := by
    simpa only [U] using hFUpper
  have hFI : Integrable (U.indicator F)
      ((volume : Measure ℝ).prod volume) :=
    hFU.integrable_indicator hUmeas
  have houter := hFI.integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  change Integrable _ (volume.restrict (Ioc (-1 : ℝ) 1))
  apply (houter.mono_measure Measure.restrict_le_self).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hrow : (fun y : ℝ ↦ U.indicator F (x, y)) =
      (Icc (-1) x).indicator (fun y ↦ F (x, y)) := by
    funext y
    have hmem : (x, y) ∈ U ↔ y ∈ Icc (-1 : ℝ) x := by
      dsimp only [U]
      unfold centeredUpperTriangle
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hx.2⟩
    by_cases hy : y ∈ Icc (-1 : ℝ) x
    · rw [Set.indicator_of_mem hy,
        Set.indicator_of_mem (hmem.mpr hy)]
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (mt hmem.mp hy)]
  rw [hrow, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hx.1.le]

/-- A bounded measurable lag times a continuous scalar profile is interval
integrable on the physical lag interval. -/
theorem intervalIntegrable_boundedLag_mul_continuous
    (q f : ℝ → ℝ) (hq : Measurable q) (hf : Continuous f)
    (C : ℝ) (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    IntervalIntegrable (fun t ↦ q t * f t) volume 0 2 := by
  let g : ℝ → ℝ := fun t ↦ C * |f t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hf.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hqfmeas : AEStronglyMeasurable (fun t ↦ q t * f t)
      (volume.restrict (Ioc (0 : ℝ) 2)) :=
    (hq.mul hf.measurable).aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖q t * f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hqt := hqC t ⟨ht.1.le, ht.2⟩
    dsimp only [g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hqt (abs_nonneg (f t))
  constructor
  · exact Integrable.mono' hg hqfmeas hbound
  · simp

/-- Ordered correlation represented in its second coordinate for a bounded
measurable lag kernel. -/
theorem integral_boundedLag_mul_crossCorrelation_eq_right
    (q u v : ℝ → ℝ) (hq : Measurable q)
    (hu : Continuous u) (hv : Continuous v)
    (C : ℝ) (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    (∫ t : ℝ in 0..2,
        q t * factorTwoCenteredCrossCorrelation u v t) =
      ∫ x : ℝ in -1..1,
        v x * factorTwoContinuousLagRightRepresenter q u x := by
  let F : ℝ × ℝ → ℝ := factorTwoLagUpperDensity q u v
  have hFUpper : IntegrableOn F centeredUpperTriangle
      ((volume : Measure ℝ).prod volume) := by
    simpa only [F] using
      integrableOn_factorTwoLagUpperDensity_of_bounded
        q u v hq hu hv C hqC
  rw [integral_weight_mul_crossCorrelation_eq_upperTriangle_of_bounded
      q u v hq hu hv C hqC,
    setIntegral_centeredUpperTriangle_eq_iterated_right_of_integrable
      F hFUpper]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoContinuousLagRightRepresenter
  change (∫ y : ℝ in x..1, F (y, x)) =
    v x * ∫ y : ℝ in x..1, q (y - x) * u y
  rw [show (fun y : ℝ ↦ F (y, x)) = fun y ↦
      (q (y - x) * u y) * v x by
    funext y
    rfl,
    intervalIntegral.integral_mul_const]
  ring

/-- Ordered correlation represented in its first coordinate. -/
theorem integral_boundedLag_mul_crossCorrelation_eq_left
    (q u v : ℝ → ℝ) (hq : Measurable q)
    (hu : Continuous u) (hv : Continuous v)
    (C : ℝ) (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    (∫ t : ℝ in 0..2,
        q t * factorTwoCenteredCrossCorrelation u v t) =
      ∫ x : ℝ in -1..1,
        u x * factorTwoContinuousLagLeftRepresenter q v x := by
  let F : ℝ × ℝ → ℝ := factorTwoLagUpperDensity q u v
  have hFUpper : IntegrableOn F centeredUpperTriangle
      ((volume : Measure ℝ).prod volume) := by
    simpa only [F] using
      integrableOn_factorTwoLagUpperDensity_of_bounded
        q u v hq hu hv C hqC
  rw [integral_weight_mul_crossCorrelation_eq_upperTriangle_of_bounded
      q u v hq hu hv C hqC,
    setIntegral_centeredUpperTriangle_eq_iterated_left_of_integrable
      F hFUpper]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoContinuousLagLeftRepresenter
  change (∫ y : ℝ in -1..x, F (x, y)) =
    u x * ∫ y : ℝ in -1..x, q (x - y) * v y
  rw [show (fun y : ℝ ↦ F (x, y)) = fun y ↦
      u x * (q (x - y) * v y) by
    funext y
    dsimp only [F, factorTwoLagUpperDensity]
    ring,
    intervalIntegral.integral_const_mul]

/-- The right ordered pairing is interval-integrable. -/
theorem intervalIntegrable_mul_factorTwoContinuousLagRightRepresenter_of_bounded
    (q u v : ℝ → ℝ) (hq : Measurable q)
    (hu : Continuous u) (hv : Continuous v)
    (C : ℝ) (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    IntervalIntegrable
      (fun x ↦ v x * factorTwoContinuousLagRightRepresenter q u x)
      volume (-1) 1 := by
  let F : ℝ × ℝ → ℝ := factorTwoLagUpperDensity q u v
  have hFUpper : IntegrableOn F centeredUpperTriangle
      ((volume : Measure ℝ).prod volume) := by
    simpa only [F] using
      integrableOn_factorTwoLagUpperDensity_of_bounded
        q u v hq hu hv C hqC
  have hraw := intervalIntegrable_iterated_right_of_integrable F hFUpper
  apply hraw.congr
  intro x _hx
  unfold factorTwoContinuousLagRightRepresenter
  change (∫ y : ℝ in x..1, F (y, x)) =
    v x * ∫ y : ℝ in x..1, q (y - x) * u y
  rw [show (fun y : ℝ ↦ F (y, x)) = fun y ↦
      (q (y - x) * u y) * v x by
    funext y
    rfl,
    intervalIntegral.integral_mul_const]
  ring

/-- The left ordered pairing is interval-integrable. -/
theorem intervalIntegrable_mul_factorTwoContinuousLagLeftRepresenter_of_bounded
    (q u v : ℝ → ℝ) (hq : Measurable q)
    (hu : Continuous u) (hv : Continuous v)
    (C : ℝ) (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    IntervalIntegrable
      (fun x ↦ u x * factorTwoContinuousLagLeftRepresenter q v x)
      volume (-1) 1 := by
  let F : ℝ × ℝ → ℝ := factorTwoLagUpperDensity q u v
  have hFUpper : IntegrableOn F centeredUpperTriangle
      ((volume : Measure ℝ).prod volume) := by
    simpa only [F] using
      integrableOn_factorTwoLagUpperDensity_of_bounded
        q u v hq hu hv C hqC
  have hraw := intervalIntegrable_iterated_left_of_integrable F hFUpper
  apply hraw.congr
  intro x _hx
  unfold factorTwoContinuousLagLeftRepresenter
  change (∫ y : ℝ in -1..x, F (x, y)) =
    u x * ∫ y : ℝ in -1..x, q (x - y) * v y
  rw [show (fun y : ℝ ↦ F (x, y)) = fun y ↦
      u x * (q (x - y) * v y) by
    funext y
    dsimp only [F, factorTwoLagUpperDensity]
    ring,
    intervalIntegral.integral_const_mul]

/-! ## Symmetric and alternating pairings -/

/-- The sum of the right and left transforms represents the symmetric
correlation polarization for a bounded measurable lag kernel. -/
theorem integral_boundedLag_mul_correlationBilinear_eq_K
    (q u v : ℝ → ℝ) (hq : Measurable q)
    (hu : Continuous u) (hv : Continuous v)
    (C : ℝ) (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    (∫ t : ℝ in 0..2,
        q t * factorTwoCenteredCorrelationBilinear u v t) =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        v x * factorTwoContinuousLagK q u x := by
  have huvI := intervalIntegrable_boundedLag_mul_continuous q
    (factorTwoCenteredCrossCorrelation u v) hq
    (continuous_factorTwoCenteredCrossCorrelation u v hu hv) C hqC
  have hvuI := intervalIntegrable_boundedLag_mul_continuous q
    (factorTwoCenteredCrossCorrelation v u) hq
    (continuous_factorTwoCenteredCrossCorrelation v u hv hu) C hqC
  have hrightI :=
    intervalIntegrable_mul_factorTwoContinuousLagRightRepresenter_of_bounded
      q u v hq hu hv C hqC
  have hleftI :=
    intervalIntegrable_mul_factorTwoContinuousLagLeftRepresenter_of_bounded
      q v u hq hv hu C hqC
  rw [show (fun t : ℝ ↦
      q t * factorTwoCenteredCorrelationBilinear u v t) = fun t ↦
        (1 / 2 : ℝ) *
          (q t * factorTwoCenteredCrossCorrelation u v t +
            q t * factorTwoCenteredCrossCorrelation v u t) by
    funext t
    unfold factorTwoCenteredCorrelationBilinear
    ring,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add huvI hvuI,
    integral_boundedLag_mul_crossCorrelation_eq_right
      q u v hq hu hv C hqC,
    integral_boundedLag_mul_crossCorrelation_eq_left
      q v u hq hv hu C hqC,
    ← intervalIntegral.integral_add hrightI hleftI]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoContinuousLagK
  ring

/-- The right-minus-left transform represents the alternating ordered
cross-difference for a bounded measurable lag kernel. -/
theorem integral_boundedLag_mul_crossDifference_eq_J
    (q e o : ℝ → ℝ) (hq : Measurable q)
    (he : Continuous e) (ho : Continuous o)
    (C : ℝ) (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    (∫ t : ℝ in 0..2,
        q t * (factorTwoCenteredCrossCorrelation o e t -
          factorTwoCenteredCrossCorrelation e o t)) =
      ∫ x : ℝ in -1..1,
        e x * factorTwoContinuousLagJ q o x := by
  have hoeI := intervalIntegrable_boundedLag_mul_continuous q
    (factorTwoCenteredCrossCorrelation o e) hq
    (continuous_factorTwoCenteredCrossCorrelation o e ho he) C hqC
  have heoI := intervalIntegrable_boundedLag_mul_continuous q
    (factorTwoCenteredCrossCorrelation e o) hq
    (continuous_factorTwoCenteredCrossCorrelation e o he ho) C hqC
  have hrightI :=
    intervalIntegrable_mul_factorTwoContinuousLagRightRepresenter_of_bounded
      q o e hq ho he C hqC
  have hleftI :=
    intervalIntegrable_mul_factorTwoContinuousLagLeftRepresenter_of_bounded
      q e o hq he ho C hqC
  rw [show (fun t : ℝ ↦
      q t * (factorTwoCenteredCrossCorrelation o e t -
        factorTwoCenteredCrossCorrelation e o t)) = fun t ↦
      q t * factorTwoCenteredCrossCorrelation o e t -
        q t * factorTwoCenteredCrossCorrelation e o t by
    funext t
    ring,
    intervalIntegral.integral_sub hoeI heoI,
    integral_boundedLag_mul_crossCorrelation_eq_right
      q o e hq ho he C hqC,
    integral_boundedLag_mul_crossCorrelation_eq_left
      q e o hq he ho C hqC,
    ← intervalIntegral.integral_sub hrightI hleftI]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoContinuousLagJ
  ring

/-- Equivalent alternating representation in the other profile, with the
opposite sign. -/
theorem integral_boundedLag_mul_crossDifference_eq_neg_J
    (q e o : ℝ → ℝ) (hq : Measurable q)
    (he : Continuous e) (ho : Continuous o)
    (C : ℝ) (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    (∫ t : ℝ in 0..2,
        q t * (factorTwoCenteredCrossCorrelation o e t -
          factorTwoCenteredCrossCorrelation e o t)) =
      -(∫ x : ℝ in -1..1,
        o x * factorTwoContinuousLagJ q e x) := by
  have hswap := integral_boundedLag_mul_crossDifference_eq_J
    q o e hq ho he C hqC
  rw [show (fun t : ℝ ↦
      q t * (factorTwoCenteredCrossCorrelation e o t -
        factorTwoCenteredCrossCorrelation o e t)) = fun t ↦
      -(q t * (factorTwoCenteredCrossCorrelation o e t -
        factorTwoCenteredCrossCorrelation e o t)) by
    funext t
    ring,
    intervalIntegral.integral_neg] at hswap
  linarith

/-! ## The two analytic factor-two lag remainders -/

/-- Symmetric removable analytic remainder after subtracting its degree-six
polynomial model. -/
def factorTwoSymmetricAnalyticLag (t : ℝ) : ℝ :=
  oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t

/-- Alternating removable analytic remainder after subtracting its linear
model. -/
def factorTwoAlternatingAnalyticLag (t : ℝ) : ℝ :=
  yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t - t / 10

theorem measurable_yoshidaRegularKernel :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

theorem measurable_factorTwoCenteredSymmetricRegularWeight :
    Measurable factorTwoCenteredSymmetricRegularWeight := by
  unfold factorTwoCenteredSymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).add
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel.comp (by fun_prop))).sub
        (measurable_yoshidaRegularKernel.comp (by fun_prop))

theorem measurable_factorTwoCenteredAntisymmetricRegularWeight :
    Measurable factorTwoCenteredAntisymmetricRegularWeight := by
  unfold factorTwoCenteredAntisymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).sub
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel.comp (by fun_prop))).add
        (measurable_yoshidaRegularKernel.comp (by fun_prop))

theorem measurable_factorTwoSymmetricAnalyticLag :
    Measurable factorTwoSymmetricAnalyticLag := by
  unfold factorTwoSymmetricAnalyticLag oddLowPoleFreeKernel
  exact (measurable_const.mul
    measurable_factorTwoCenteredSymmetricRegularWeight).sub
      continuous_poleFreeKernelPolynomial6.measurable

theorem measurable_factorTwoAlternatingAnalyticLag :
    Measurable factorTwoAlternatingAnalyticLag := by
  unfold factorTwoAlternatingAnalyticLag
  exact (measurable_const.mul
    measurable_factorTwoCenteredAntisymmetricRegularWeight).sub
      (measurable_id.div_const 10)

theorem abs_factorTwoSymmetricAnalyticLag_le
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    |factorTwoSymmetricAnalyticLag t| ≤ (3 / 8000 : ℝ) := by
  unfold factorTwoSymmetricAnalyticLag
  exact (abs_poleFreeKernel_sub_polynomial_lt ht).le

theorem abs_factorTwoAlternatingAnalyticLag_le
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    |factorTwoAlternatingAnalyticLag t| ≤ (1 / 1000 : ℝ) := by
  unfold factorTwoAlternatingAnalyticLag
  exact
    abs_yoshidaEndpointA_mul_factorTwoCenteredAntisymmetricRegularWeight_sub_linear_le_one_thousand
      ht.1 ht.2

/-- Exact symmetric representer for the removable analytic remainder. -/
theorem integral_factorTwoSymmetricAnalyticLag_mul_correlationBilinear_eq_K
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2,
        factorTwoSymmetricAnalyticLag t *
          factorTwoCenteredCorrelationBilinear u v t) =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        v x * factorTwoContinuousLagK factorTwoSymmetricAnalyticLag u x := by
  exact integral_boundedLag_mul_correlationBilinear_eq_K
    factorTwoSymmetricAnalyticLag u v
    measurable_factorTwoSymmetricAnalyticLag hu hv (3 / 8000)
    (fun _t ht ↦ abs_factorTwoSymmetricAnalyticLag_le ht)

/-- Exact alternating representer for the removable analytic remainder. -/
theorem integral_factorTwoAlternatingAnalyticLag_mul_crossDifference_eq_J
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o) :
    (∫ t : ℝ in 0..2,
        factorTwoAlternatingAnalyticLag t *
          (factorTwoCenteredCrossCorrelation o e t -
            factorTwoCenteredCrossCorrelation e o t)) =
      ∫ x : ℝ in -1..1,
        e x * factorTwoContinuousLagJ factorTwoAlternatingAnalyticLag o x := by
  exact integral_boundedLag_mul_crossDifference_eq_J
    factorTwoAlternatingAnalyticLag e o
    measurable_factorTwoAlternatingAnalyticLag he ho (1 / 1000)
    (fun _t ht ↦ abs_factorTwoAlternatingAnalyticLag_le ht)

/-- Alternating analytic representer in the other profile, with the opposite
sign. -/
theorem integral_factorTwoAlternatingAnalyticLag_mul_crossDifference_eq_neg_J
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o) :
    (∫ t : ℝ in 0..2,
        factorTwoAlternatingAnalyticLag t *
          (factorTwoCenteredCrossCorrelation o e t -
            factorTwoCenteredCrossCorrelation e o t)) =
      -(∫ x : ℝ in -1..1,
        o x * factorTwoContinuousLagJ factorTwoAlternatingAnalyticLag e x) := by
  exact integral_boundedLag_mul_crossDifference_eq_neg_J
    factorTwoAlternatingAnalyticLag e o
    measurable_factorTwoAlternatingAnalyticLag he ho (1 / 1000)
    (fun _t ht ↦ abs_factorTwoAlternatingAnalyticLag_le ht)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoIntegrableLagRepresenterStructural
