import ArithmeticHodge.Analysis.YoshidaFactorTwoContinuousLagRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseAlternatingCoercivity

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoReflectedPoleRepresenterStructural

open YoshidaEndpointTriangleInterchange
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoPhaseAlternatingCoercivity

noncomputable section

/-!
# Representers for the reflected endpoint pole

The kernel `1 / (2 - t)` is integrable only after multiplication by the
shrinking ordered correlation.  Its one-variable right and left transforms
therefore exclude precisely their singular endpoint rows.  Those endpoints
are null in the outer pairing, while this convention keeps every pointwise
statement honest.
-/

/-- Right reflected-pole transform.  Its singular row `x = -1` is excluded;
the degenerate row `x = 1` is retained. -/
def factorTwoReflectedPoleRightRepresenter
    (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Ioc (-1 : ℝ) 1).indicator
    (fun z ↦ ∫ y : ℝ in z..1, p y / (2 - y + z)) x

/-- Left reflected-pole transform.  Its singular row `x = 1` is excluded;
the degenerate row `x = -1` is retained. -/
def factorTwoReflectedPoleLeftRepresenter
    (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Ico (-1 : ℝ) 1).indicator
    (fun z ↦ ∫ y : ℝ in -1..z, p y / (2 - z + y)) x

/-- Symmetric reflected-pole representer. -/
def factorTwoReflectedPoleK (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  factorTwoReflectedPoleRightRepresenter p x +
    factorTwoReflectedPoleLeftRepresenter p x

/-- Alternating reflected-pole representer, with right-minus-left sign. -/
def factorTwoReflectedPoleJ (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  factorTwoReflectedPoleRightRepresenter p x -
    factorTwoReflectedPoleLeftRepresenter p x

/-! ## Ordered pairing identities -/

/-- The reflected pole represented in the second, right-triangle
coordinate. -/
theorem integral_cross_div_two_sub_eq_reflectedPoleRight
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2,
      factorTwoCenteredCrossCorrelation u v t / (2 - t)) =
      ∫ x : ℝ in -1..1,
        v x * factorTwoReflectedPoleRightRepresenter u x := by
  let F : ℝ × ℝ → ℝ := fun z ↦
    u z.1 * v z.2 / (2 - z.1 + z.2)
  have hFUpper : IntegrableOn F centeredUpperTriangle
      ((volume : Measure ℝ).prod volume) := by
    simpa only [F] using integrableOn_centeredUpper_density u v hu hv
  rw [integral_cross_div_two_sub_eq_centeredUpperTriangle u v hu hv,
    setIntegral_centeredUpperTriangle_eq_iterated_right_of_integrable
      F hFUpper]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with x
  intro hx
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  unfold factorTwoReflectedPoleRightRepresenter
  rw [Set.indicator_of_mem hx]
  change (∫ y : ℝ in x..1, u y * v x / (2 - y + x)) =
    v x * ∫ y : ℝ in x..1, u y / (2 - y + x)
  rw [show (fun y : ℝ ↦ u y * v x / (2 - y + x)) =
      fun y ↦ v x * (u y / (2 - y + x)) by
    funext y
    ring,
    intervalIntegral.integral_const_mul]

/-- The reflected pole represented in the first, left-triangle
coordinate. -/
theorem integral_cross_div_two_sub_eq_reflectedPoleLeft
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2,
      factorTwoCenteredCrossCorrelation u v t / (2 - t)) =
      ∫ x : ℝ in -1..1,
        u x * factorTwoReflectedPoleLeftRepresenter v x := by
  let F : ℝ × ℝ → ℝ := fun z ↦
    u z.1 * v z.2 / (2 - z.1 + z.2)
  have hFUpper : IntegrableOn F centeredUpperTriangle
      ((volume : Measure ℝ).prod volume) := by
    simpa only [F] using integrableOn_centeredUpper_density u v hu hv
  rw [integral_cross_div_two_sub_eq_centeredUpperTriangle u v hu hv,
    setIntegral_centeredUpperTriangle_eq_iterated_left_of_integrable
      F hFUpper]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ)] with x hx1
  intro hx
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  have hxIco : x ∈ Ico (-1 : ℝ) 1 :=
    ⟨hx.1.le, lt_of_le_of_ne hx.2 hx1⟩
  unfold factorTwoReflectedPoleLeftRepresenter
  rw [Set.indicator_of_mem hxIco]
  change (∫ y : ℝ in -1..x, u x * v y / (2 - x + y)) =
    u x * ∫ y : ℝ in -1..x, v y / (2 - x + y)
  rw [show (fun y : ℝ ↦ u x * v y / (2 - x + y)) =
      fun y ↦ u x * (v y / (2 - x + y)) by
    funext y
    ring,
    intervalIntegral.integral_const_mul]

/-! ## Outer integrability -/

/-- The right reflected-pole pairing is interval-integrable.  This is the
outer-integrability conclusion of Fubini for the signed upper-triangle
density. -/
theorem intervalIntegrable_mul_factorTwoReflectedPoleRightRepresenter
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    IntervalIntegrable
      (fun x ↦ v x * factorTwoReflectedPoleRightRepresenter u x)
      volume (-1) 1 := by
  let U : Set (ℝ × ℝ) := centeredUpperTriangle
  let F : ℝ × ℝ → ℝ := fun z ↦
    u z.1 * v z.2 / (2 - z.1 + z.2)
  have hUmeas : MeasurableSet U := by
    dsimp only [U]
    unfold centeredUpperTriangle
    measurability
  have hFU : IntegrableOn F U ((volume : Measure ℝ).prod volume) := by
    simpa only [F, U] using integrableOn_centeredUpper_density u v hu hv
  have hFI : Integrable (U.indicator F)
      ((volume : Measure ℝ).prod volume) :=
    hFU.integrable_indicator hUmeas
  have houter := hFI.integral_prod_right
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  change Integrable _ (volume.restrict (Ioc (-1 : ℝ) 1))
  apply (houter.mono_measure Measure.restrict_le_self).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  unfold factorTwoReflectedPoleRightRepresenter
  rw [Set.indicator_of_mem hx]
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
  change (∫ y : ℝ in x..1, u y * v x / (2 - y + x)) =
    v x * ∫ y : ℝ in x..1, u y / (2 - y + x)
  rw [show (fun y : ℝ ↦ u y * v x / (2 - y + x)) =
      fun y ↦ v x * (u y / (2 - y + x)) by
    funext y
    ring,
    intervalIntegral.integral_const_mul]

/-- The left reflected-pole pairing is interval-integrable. -/
theorem intervalIntegrable_mul_factorTwoReflectedPoleLeftRepresenter
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    IntervalIntegrable
      (fun x ↦ u x * factorTwoReflectedPoleLeftRepresenter v x)
      volume (-1) 1 := by
  let U : Set (ℝ × ℝ) := centeredUpperTriangle
  let F : ℝ × ℝ → ℝ := fun z ↦
    u z.1 * v z.2 / (2 - z.1 + z.2)
  have hUmeas : MeasurableSet U := by
    dsimp only [U]
    unfold centeredUpperTriangle
    measurability
  have hFU : IntegrableOn F U ((volume : Measure ℝ).prod volume) := by
    simpa only [F, U] using integrableOn_centeredUpper_density u v hu hv
  have hFI : Integrable (U.indicator F)
      ((volume : Measure ℝ).prod volume) :=
    hFU.integrable_indicator hUmeas
  have houter := hFI.integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  change Integrable _ (volume.restrict (Ioc (-1 : ℝ) 1))
  apply (houter.mono_measure Measure.restrict_le_self).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    MeasureTheory.ae_restrict_of_ae
      (MeasureTheory.Measure.ae_ne volume (1 : ℝ))] with x hx hx1
  have hxIco : x ∈ Ico (-1 : ℝ) 1 :=
    ⟨hx.1.le, lt_of_le_of_ne hx.2 hx1⟩
  unfold factorTwoReflectedPoleLeftRepresenter
  rw [Set.indicator_of_mem hxIco]
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
    ← intervalIntegral.integral_of_le hxIco.1]
  change (∫ y : ℝ in -1..x, u x * v y / (2 - x + y)) =
    u x * ∫ y : ℝ in -1..x, v y / (2 - x + y)
  rw [show (fun y : ℝ ↦ u x * v y / (2 - x + y)) =
      fun y ↦ u x * (v y / (2 - x + y)) by
    funext y
    ring,
    intervalIntegral.integral_const_mul]

/-! ## Symmetric and alternating representers -/

/-- The symmetric correlation polarization against the reflected pole is
represented by `K = right + left`. -/
theorem integral_correlationBilinear_div_two_sub_eq_reflectedPoleK
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2,
      factorTwoCenteredCorrelationBilinear u v t / (2 - t)) =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        v x * factorTwoReflectedPoleK u x := by
  have huvI :=
    intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
      u v hu hv
  have hvuI :=
    intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
      v u hv hu
  have hrightI :=
    intervalIntegrable_mul_factorTwoReflectedPoleRightRepresenter
      u v hu hv
  have hleftI :=
    intervalIntegrable_mul_factorTwoReflectedPoleLeftRepresenter
      v u hv hu
  rw [show (fun t : ℝ ↦
      factorTwoCenteredCorrelationBilinear u v t / (2 - t)) =
      fun t ↦ (1 / 2 : ℝ) *
        (factorTwoCenteredCrossCorrelation u v t / (2 - t) +
          factorTwoCenteredCrossCorrelation v u t / (2 - t)) by
    funext t
    unfold factorTwoCenteredCorrelationBilinear
    ring,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add huvI hvuI,
    integral_cross_div_two_sub_eq_reflectedPoleRight u v hu hv,
    integral_cross_div_two_sub_eq_reflectedPoleLeft v u hv hu,
    ← intervalIntegral.integral_add hrightI hleftI]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoReflectedPoleK
  ring

/-- The ordered cross-difference against the reflected pole is represented
by `J = right - left` in the second profile. -/
theorem integral_crossDifference_div_two_sub_eq_reflectedPoleJ
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o) :
    (∫ t : ℝ in 0..2,
      (factorTwoCenteredCrossCorrelation o e t -
        factorTwoCenteredCrossCorrelation e o t) / (2 - t)) =
      ∫ x : ℝ in -1..1,
        e x * factorTwoReflectedPoleJ o x := by
  have hoeI :=
    intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
      o e ho he
  have heoI :=
    intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
      e o he ho
  have hrightI :=
    intervalIntegrable_mul_factorTwoReflectedPoleRightRepresenter
      o e ho he
  have hleftI :=
    intervalIntegrable_mul_factorTwoReflectedPoleLeftRepresenter
      e o he ho
  rw [show (fun t : ℝ ↦
      (factorTwoCenteredCrossCorrelation o e t -
        factorTwoCenteredCrossCorrelation e o t) / (2 - t)) =
      fun t ↦ factorTwoCenteredCrossCorrelation o e t / (2 - t) -
        factorTwoCenteredCrossCorrelation e o t / (2 - t) by
    funext t
    ring,
    intervalIntegral.integral_sub hoeI heoI,
    integral_cross_div_two_sub_eq_reflectedPoleRight o e ho he,
    integral_cross_div_two_sub_eq_reflectedPoleLeft e o he ho,
    ← intervalIntegral.integral_sub hrightI hleftI]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoReflectedPoleJ
  ring

/-- Equivalent alternating representation with the represented function in
the first profile, carrying the opposite sign. -/
theorem integral_crossDifference_div_two_sub_eq_neg_reflectedPoleJ
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o) :
    (∫ t : ℝ in 0..2,
      (factorTwoCenteredCrossCorrelation o e t -
        factorTwoCenteredCrossCorrelation e o t) / (2 - t)) =
      -(∫ x : ℝ in -1..1,
        o x * factorTwoReflectedPoleJ e x) := by
  have hswap :=
    integral_crossDifference_div_two_sub_eq_reflectedPoleJ o e ho he
  rw [show (fun t : ℝ ↦
      (factorTwoCenteredCrossCorrelation e o t -
        factorTwoCenteredCrossCorrelation o e t) / (2 - t)) =
      fun t ↦ -((factorTwoCenteredCrossCorrelation o e t -
        factorTwoCenteredCrossCorrelation e o t) / (2 - t)) by
    funext t
    ring,
    intervalIntegral.integral_neg] at hswap
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoReflectedPoleRepresenterStructural
