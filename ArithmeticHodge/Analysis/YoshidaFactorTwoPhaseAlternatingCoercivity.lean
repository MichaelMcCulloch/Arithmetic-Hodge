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
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical

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

/-- A fixed first coordinate is null for planar Lebesgue measure. -/
private theorem ae_fst_ne (c : ℝ) :
    ∀ᵐ z : ℝ × ℝ ∂((volume : Measure ℝ).prod volume), z.1 ≠ c := by
  apply (MeasureTheory.Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [MeasureTheory.Measure.ae_ne volume c] with x hx
  exact Filter.Eventually.of_forall (fun _y ↦ hx)

private theorem measurableSet_positiveDistanceTriangle :
    MeasurableSet positiveDistanceTriangle := by
  unfold positiveDistanceTriangle
  measurability

private theorem openPositiveDistanceTriangle_ae_eq :
    openPositiveDistanceTriangle =ᵐ[((volume : Measure ℝ).prod volume)]
      positiveDistanceTriangle := by
  filter_upwards [ae_fst_ne 0, ae_fst_ne 2] with z hz0 hz2
  apply propext
  constructor
  · intro hmem
    exact ⟨hmem.1.1.le, hmem.1.2.le, hmem.2⟩
  · intro hmem
    exact ⟨⟨lt_of_le_of_ne hmem.1 (Ne.symm hz0),
      lt_of_le_of_ne hmem.2.1 hz2⟩, hmem.2.2⟩

/-- The punctured and closed distance triangles have the same integral. -/
private theorem setIntegral_openTriangle_eq_closedTriangle
    (F : ℝ × ℝ → ℝ) :
    (∫ z : ℝ × ℝ in openPositiveDistanceTriangle, F z) =
      ∫ z : ℝ × ℝ in positiveDistanceTriangle, F z := by
  rw [← integral_indicator measurableSet_openPositiveDistanceTriangle,
    ← integral_indicator measurableSet_positiveDistanceTriangle]
  rw [Measure.volume_eq_prod ℝ ℝ]
  apply integral_congr_ae
  filter_upwards [openPositiveDistanceTriangle_ae_eq] with z hz
  have hziff : z ∈ openPositiveDistanceTriangle ↔
      z ∈ positiveDistanceTriangle := iff_of_eq hz
  by_cases hmem : z ∈ openPositiveDistanceTriangle
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hziff.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (mt hziff.mpr hmem)]

/-- The positive-distance shear turns the absolute correlation majorant into
the corresponding density on the centered upper triangle. -/
theorem integral_abs_cross_div_two_sub_eq_centeredUpperTriangle
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (∫ t : ℝ in 0..2,
      factorTwoCenteredCrossCorrelation
          (fun x ↦ |u x|) (fun x ↦ |v x|) t / (2 - t)) =
      ∫ z : ℝ × ℝ in centeredUpperTriangle,
        |u z.1 * v z.2| / (2 - z.1 + z.2) := by
  let F : ℝ × ℝ → ℝ := fun z ↦
    |u z.1 * v z.2| / (2 - z.1 + z.2)
  rw [integral_abs_cross_div_two_sub_eq_openTriangle u v hu hv,
    setIntegral_openTriangle_eq_closedTriangle]
  calc
    (∫ z : ℝ × ℝ in positiveDistanceTriangle,
        |u (z.1 + z.2) * v z.2| / (2 - z.1)) =
        ∫ z : ℝ × ℝ in positiveDistanceTriangle,
          F (z.1 + z.2, z.2) := by
      apply setIntegral_congr_fun measurableSet_positiveDistanceTriangle
      intro z _hz
      dsimp only [F]
      congr 2
      ring
    _ = ∫ z : ℝ × ℝ in centeredUpperTriangle, F z :=
      setIntegral_positiveDistanceTriangle_shear F
    _ = ∫ z : ℝ × ℝ in centeredUpperTriangle,
        |u z.1 * v z.2| / (2 - z.1 + z.2) := by rfl

/-- Reusable set-integral transport under a measure-preserving measurable
embedding whose preimage identifies the two domains. -/
theorem setIntegral_comp_measurePreserving
    (S : ℝ × ℝ → ℝ × ℝ)
    (hS : MeasurePreserving S
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume))
    (hSemb : MeasurableEmbedding S)
    (A B : Set (ℝ × ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hpre : S ⁻¹' B = A) (F : ℝ × ℝ → ℝ) :
    (∫ z : ℝ × ℝ in A, F (S z)) = ∫ z : ℝ × ℝ in B, F z := by
  rw [Measure.volume_eq_prod ℝ ℝ]
  have hmem (z : ℝ × ℝ) : S z ∈ B ↔ z ∈ A := by
    change z ∈ S ⁻¹' B ↔ z ∈ A
    rw [hpre]
  have hcomp := hS.integral_comp hSemb (B.indicator F)
  calc
    (∫ z : ℝ × ℝ in A, F (S z)
        ∂((volume : Measure ℝ).prod volume)) =
        ∫ z : ℝ × ℝ, A.indicator (fun z ↦ F (S z)) z :=
      (integral_indicator hA).symm
    _ = ∫ z : ℝ × ℝ, (B.indicator F) (S z) := by
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ A
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hmem z).2 hz)]
      · rw [Set.indicator_of_notMem hz,
          Set.indicator_of_notMem (mt (hmem z).1 hz)]
    _ = ∫ z : ℝ × ℝ, B.indicator F z := hcomp
    _ = ∫ z : ℝ × ℝ in B, F z := integral_indicator hB

private def centeredNegativeTriangle : Set (ℝ × ℝ) :=
  {z | -1 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 < 0}

private def centeredCrossRectangle : Set (ℝ × ℝ) :=
  {z | -1 ≤ z.2 ∧ z.2 ≤ 0 ∧ 0 ≤ z.1 ∧ z.1 ≤ 1}

private def centeredPositiveTriangle : Set (ℝ × ℝ) :=
  {z | 0 < z.2 ∧ z.2 ≤ z.1 ∧ z.1 ≤ 1}

private def unitSquare : Set (ℝ × ℝ) :=
  Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

private def unitLowerTriangle : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 < 1}

private def unitUpperTriangle : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 < 1}

private theorem measurableSet_centeredNegativeTriangle :
    MeasurableSet centeredNegativeTriangle := by
  unfold centeredNegativeTriangle
  measurability

private theorem measurableSet_centeredCrossRectangle :
    MeasurableSet centeredCrossRectangle := by
  unfold centeredCrossRectangle
  measurability

private theorem measurableSet_centeredPositiveTriangle :
    MeasurableSet centeredPositiveTriangle := by
  unfold centeredPositiveTriangle
  measurability

private theorem measurableSet_unitSquare : MeasurableSet unitSquare := by
  unfold unitSquare
  exact measurableSet_Icc.prod measurableSet_Icc

private theorem measurableSet_unitLowerTriangle :
    MeasurableSet unitLowerTriangle := by
  unfold unitLowerTriangle
  measurability

private theorem measurableSet_unitUpperTriangle :
    MeasurableSet unitUpperTriangle := by
  unfold unitUpperTriangle
  measurability

/-- Product integrability survives the distance shear, so the centered upper
triangle may be split into its three sign regions. -/
private theorem integrableOn_centeredUpper_absDensity
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    IntegrableOn
      (fun z : ℝ × ℝ ↦ |u z.1 * v z.2| / (2 - z.1 + z.2))
      centeredUpperTriangle ((volume : Measure ℝ).prod volume) := by
  let S : ℝ × ℝ → ℝ × ℝ := fun z ↦ (z.1 + z.2, z.2)
  let F : ℝ × ℝ → ℝ := fun z ↦ |u z.1 * v z.2| / (2 - z.1 + z.2)
  let G : ℝ × ℝ → ℝ := fun z ↦
    |u (z.1 + z.2) * v z.2| / (2 - z.1)
  have hGIndicator : Integrable
      (openPositiveDistanceTriangle.indicator G)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [G] using
      integrable_openPositiveDistanceTriangle_profileDensity u v hu hv
  have hGOpen : IntegrableOn G openPositiveDistanceTriangle
      ((volume : Measure ℝ).prod volume) := by
    rw [← integrable_indicator_iff measurableSet_openPositiveDistanceTriangle]
    exact hGIndicator
  have hGClosed : IntegrableOn G positiveDistanceTriangle
      ((volume : Measure ℝ).prod volume) :=
    hGOpen.congr_set_ae openPositiveDistanceTriangle_ae_eq.symm
  have hcomp : (fun z ↦ F (S z)) = G := by
    funext z
    dsimp only [F, G, S]
    rw [show 2 - (z.1 + z.2) + z.2 = 2 - z.1 by ring]
  have hpre : S ⁻¹' centeredUpperTriangle = positiveDistanceTriangle := by
    ext z
    change (-1 ≤ z.2 ∧ z.2 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 1) ↔
      (0 ≤ z.1 ∧ z.1 ≤ 2 ∧ -1 ≤ z.2 ∧ z.2 ≤ 1 - z.1)
    constructor
    · rintro ⟨hxlow, hxy, hyhigh⟩
      exact ⟨by linarith, by linarith, hxlow, by linarith⟩
    · rintro ⟨htlow, _hthigh, hxlow, hxhigh⟩
      exact ⟨hxlow, by linarith, by linarith⟩
  have hmeasure : MeasurePreserving S
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
    measurePreserving_add_prod volume volume
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    MeasurableEquiv.prodComm.trans
      ((MeasurableEquiv.shearAddRight ℝ).trans MeasurableEquiv.prodComm)
  have he_apply (z : ℝ × ℝ) : e z = S z := by
    change (z.2 + z.1, z.2) = (z.1 + z.2, z.2)
    congr 1
    ring
  have hSemb : MeasurableEmbedding S := by
    rw [← funext he_apply]
    exact e.measurableEmbedding
  have hpreInt : IntegrableOn (fun z ↦ F (S z))
      (S ⁻¹' centeredUpperTriangle) ((volume : Measure ℝ).prod volume) := by
    rw [hpre, hcomp]
    exact hGClosed
  exact (hmeasure.integrableOn_comp_preimage hSemb).1 hpreInt

private theorem centeredUpperTriangle_eq_sign_regions :
    centeredUpperTriangle =
      centeredNegativeTriangle ∪
        (centeredCrossRectangle ∪ centeredPositiveTriangle) := by
  ext z
  change (-1 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 ≤ 1) ↔
    ((-1 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 < 0) ∨
      ((-1 ≤ z.2 ∧ z.2 ≤ 0 ∧ 0 ≤ z.1 ∧ z.1 ≤ 1) ∨
        (0 < z.2 ∧ z.2 ≤ z.1 ∧ z.1 ≤ 1)))
  constructor
  · intro hz
    by_cases hy : z.1 < 0
    · exact Or.inl ⟨hz.1, hz.2.1, hy⟩
    · by_cases hx : z.2 ≤ 0
      · exact Or.inr (Or.inl ⟨hz.1, hx, le_of_not_gt hy, hz.2.2⟩)
      · exact Or.inr (Or.inr ⟨lt_of_not_ge hx, hz.2.1, hz.2.2⟩)
  · rintro (hz | hz | hz)
    · exact ⟨hz.1, hz.2.1, hz.2.2.le.trans (by norm_num)⟩
    · exact ⟨hz.1, hz.2.1.trans hz.2.2.1, hz.2.2.2⟩
    · exact ⟨by linarith [hz.1], hz.2.1, hz.2.2⟩

private theorem disjoint_centeredNegative_sign_rest :
    Disjoint centeredNegativeTriangle
      (centeredCrossRectangle ∪ centeredPositiveTriangle) := by
  rw [Set.disjoint_left]
  intro z hn hrest
  rcases hrest with hx | hp
  · exact (not_lt_of_ge hx.2.2.1) hn.2.2
  · linarith [hn.2.1, hn.2.2, hp.1]

private theorem disjoint_centeredCross_positive :
    Disjoint centeredCrossRectangle centeredPositiveTriangle := by
  rw [Set.disjoint_left]
  intro z hx hp
  linarith [hx.2.1, hp.1]

private theorem setIntegral_centeredNegative_eq_unitLower
    (e o : ℝ → ℝ) (he : Function.Even e) (ho : Function.Odd o) :
    (∫ z : ℝ × ℝ in centeredNegativeTriangle,
      |e z.1 * o z.2| / (2 - z.1 + z.2)) =
      ∫ z : ℝ × ℝ in unitLowerTriangle,
        |e (1 - z.1) * o (1 - z.2)| / (2 - z.1 + z.2) := by
  let S : ℝ × ℝ → ℝ × ℝ := fun z ↦ (z.1 - 1, z.2 - 1)
  let F : ℝ × ℝ → ℝ := fun z ↦ |e z.1 * o z.2| / (2 - z.1 + z.2)
  have hmeasure : MeasurePreserving S
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
    (measurePreserving_sub_right (volume : Measure ℝ) (1 : ℝ)).prod
      (measurePreserving_sub_right (volume : Measure ℝ) (1 : ℝ))
  let E : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.prodCongr
    (MeasurableEquiv.subRight (1 : ℝ)) (MeasurableEquiv.subRight (1 : ℝ))
  have hE (z : ℝ × ℝ) : E z = S z := rfl
  have hSemb : MeasurableEmbedding S := by
    rw [← funext hE]
    exact E.measurableEmbedding
  have hpre : S ⁻¹' centeredNegativeTriangle = unitLowerTriangle := by
    ext z
    change (-1 ≤ z.2 - 1 ∧ z.2 - 1 ≤ z.1 - 1 ∧ z.1 - 1 < 0) ↔
      (0 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 < 1)
    constructor <;> intro hz <;> constructor
    · linarith [hz.1]
    · exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    · linarith [hz.1]
    · exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have htransport := setIntegral_comp_measurePreserving S hmeasure hSemb
    unitLowerTriangle centeredNegativeTriangle
    measurableSet_unitLowerTriangle measurableSet_centeredNegativeTriangle
    hpre F
  calc
    (∫ z : ℝ × ℝ in centeredNegativeTriangle,
        |e z.1 * o z.2| / (2 - z.1 + z.2)) =
        ∫ z : ℝ × ℝ in unitLowerTriangle, F (S z) := htransport.symm
    _ = ∫ z : ℝ × ℝ in unitLowerTriangle,
        |e (1 - z.1) * o (1 - z.2)| / (2 - z.1 + z.2) := by
      apply setIntegral_congr_fun measurableSet_unitLowerTriangle
      intro z _hz
      dsimp only [F, S]
      rw [show 2 - (z.1 - 1) + (z.2 - 1) = 2 - z.1 + z.2 by ring]
      rw [show z.1 - 1 = -(1 - z.1) by ring,
        show z.2 - 1 = -(1 - z.2) by ring, he, ho]
      simp only [mul_neg, abs_neg]

private theorem setIntegral_centeredCross_eq_unitSquare
    (e o : ℝ → ℝ) (ho : Function.Odd o) :
    (∫ z : ℝ × ℝ in centeredCrossRectangle,
      |e z.1 * o z.2| / (2 - z.1 + z.2)) =
      ∫ z : ℝ × ℝ in unitSquare,
        |e (1 - z.1) * o (1 - z.2)| / (z.1 + z.2) := by
  let S : ℝ × ℝ → ℝ × ℝ := fun z ↦ (1 - z.1, z.2 - 1)
  let F : ℝ × ℝ → ℝ := fun z ↦ |e z.1 * o z.2| / (2 - z.1 + z.2)
  have hmeasure : MeasurePreserving S
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
    ((volume : Measure ℝ).measurePreserving_sub_left (1 : ℝ)).prod
      (measurePreserving_sub_right (volume : Measure ℝ) (1 : ℝ))
  let E : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.prodCongr
    (MeasurableEquiv.subLeft (1 : ℝ)) (MeasurableEquiv.subRight (1 : ℝ))
  have hE (z : ℝ × ℝ) : E z = S z := rfl
  have hSemb : MeasurableEmbedding S := by
    rw [← funext hE]
    exact E.measurableEmbedding
  have hpre : S ⁻¹' centeredCrossRectangle = unitSquare := by
    ext z
    change (-1 ≤ z.2 - 1 ∧ z.2 - 1 ≤ 0 ∧
      0 ≤ 1 - z.1 ∧ 1 - z.1 ≤ 1) ↔
      (z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1)
    constructor
    · intro hz
      exact ⟨⟨by linarith [hz.2.2.2], by linarith [hz.2.2.1]⟩,
        ⟨by linarith [hz.1], by linarith [hz.2.1]⟩⟩
    · intro hz
      exact ⟨by linarith [hz.2.1], by linarith [hz.2.2],
        by linarith [hz.1.2], by linarith [hz.1.1]⟩
  have htransport := setIntegral_comp_measurePreserving S hmeasure hSemb
    unitSquare centeredCrossRectangle
    measurableSet_unitSquare measurableSet_centeredCrossRectangle hpre F
  calc
    (∫ z : ℝ × ℝ in centeredCrossRectangle,
        |e z.1 * o z.2| / (2 - z.1 + z.2)) =
        ∫ z : ℝ × ℝ in unitSquare, F (S z) := htransport.symm
    _ = ∫ z : ℝ × ℝ in unitSquare,
        |e (1 - z.1) * o (1 - z.2)| / (z.1 + z.2) := by
      apply setIntegral_congr_fun measurableSet_unitSquare
      intro z _hz
      dsimp only [F, S]
      rw [show 2 - (1 - z.1) + (z.2 - 1) = z.1 + z.2 by ring]
      rw [show z.2 - 1 = -(1 - z.2) by ring, ho]
      simp only [mul_neg, abs_neg]

private theorem setIntegral_centeredPositive_eq_unitUpper
    (e o : ℝ → ℝ) :
    (∫ z : ℝ × ℝ in centeredPositiveTriangle,
      |e z.1 * o z.2| / (2 - z.1 + z.2)) =
      ∫ z : ℝ × ℝ in unitUpperTriangle,
        |e (1 - z.1) * o (1 - z.2)| / (2 + z.1 - z.2) := by
  let S : ℝ × ℝ → ℝ × ℝ := fun z ↦ (1 - z.1, 1 - z.2)
  let F : ℝ × ℝ → ℝ := fun z ↦ |e z.1 * o z.2| / (2 - z.1 + z.2)
  have hmeasure : MeasurePreserving S
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
    ((volume : Measure ℝ).measurePreserving_sub_left (1 : ℝ)).prod
      ((volume : Measure ℝ).measurePreserving_sub_left (1 : ℝ))
  let E : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.prodCongr
    (MeasurableEquiv.subLeft (1 : ℝ)) (MeasurableEquiv.subLeft (1 : ℝ))
  have hE (z : ℝ × ℝ) : E z = S z := rfl
  have hSemb : MeasurableEmbedding S := by
    rw [← funext hE]
    exact E.measurableEmbedding
  have hpre : S ⁻¹' centeredPositiveTriangle = unitUpperTriangle := by
    ext z
    change (0 < 1 - z.2 ∧ 1 - z.2 ≤ 1 - z.1 ∧ 1 - z.1 ≤ 1) ↔
      (0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 < 1)
    constructor
    · intro hz
      exact ⟨by linarith [hz.2.2], by linarith [hz.2.1], by linarith [hz.1]⟩
    · intro hz
      exact ⟨by linarith [hz.2.2], by linarith [hz.2.1], by linarith [hz.1]⟩
  have htransport := setIntegral_comp_measurePreserving S hmeasure hSemb
    unitUpperTriangle centeredPositiveTriangle
    measurableSet_unitUpperTriangle measurableSet_centeredPositiveTriangle hpre F
  calc
    (∫ z : ℝ × ℝ in centeredPositiveTriangle,
        |e z.1 * o z.2| / (2 - z.1 + z.2)) =
        ∫ z : ℝ × ℝ in unitUpperTriangle, F (S z) := htransport.symm
    _ = ∫ z : ℝ × ℝ in unitUpperTriangle,
        |e (1 - z.1) * o (1 - z.2)| / (2 + z.1 - z.2) := by
      apply setIntegral_congr_fun measurableSet_unitUpperTriangle
      intro z _hz
      dsimp only [F, S]
      rw [show 2 - (1 - z.1) + (1 - z.2) = 2 + z.1 - z.2 by ring]

private theorem integral_abs_cross_div_two_sub_eq_sign_foldedPieces
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o) :
    (∫ t : ℝ in 0..2,
      factorTwoCenteredCrossCorrelation
          (fun x ↦ |e x|) (fun x ↦ |o x|) t / (2 - t)) =
      (∫ z : ℝ × ℝ in unitLowerTriangle,
        |e (1 - z.1) * o (1 - z.2)| / (2 - z.1 + z.2)) +
      ((∫ z : ℝ × ℝ in unitSquare,
        |e (1 - z.1) * o (1 - z.2)| / (z.1 + z.2)) +
      ∫ z : ℝ × ℝ in unitUpperTriangle,
        |e (1 - z.1) * o (1 - z.2)| / (2 + z.1 - z.2)) := by
  let F : ℝ × ℝ → ℝ := fun z ↦
    |e z.1 * o z.2| / (2 - z.1 + z.2)
  have hupper : IntegrableOn F centeredUpperTriangle
      ((volume : Measure ℝ).prod volume) := by
    simpa only [F] using integrableOn_centeredUpper_absDensity e o hec hoc
  have hnSub : centeredNegativeTriangle ⊆ centeredUpperTriangle := by
    rw [centeredUpperTriangle_eq_sign_regions]
    exact subset_union_left
  have hxSub : centeredCrossRectangle ⊆ centeredUpperTriangle := by
    rw [centeredUpperTriangle_eq_sign_regions]
    exact fun z hz ↦ Or.inr (Or.inl hz)
  have hpSub : centeredPositiveTriangle ⊆ centeredUpperTriangle := by
    rw [centeredUpperTriangle_eq_sign_regions]
    exact fun z hz ↦ Or.inr (Or.inr hz)
  have hn := hupper.mono_set hnSub
  have hx := hupper.mono_set hxSub
  have hp := hupper.mono_set hpSub
  have hrest : IntegrableOn F
      (centeredCrossRectangle ∪ centeredPositiveTriangle)
      ((volume : Measure ℝ).prod volume) := hx.union hp
  have hsplitOuter := setIntegral_union
    disjoint_centeredNegative_sign_rest
    (measurableSet_centeredCrossRectangle.union
      measurableSet_centeredPositiveTriangle) hn hrest
  have hsplitInner := setIntegral_union disjoint_centeredCross_positive
    measurableSet_centeredPositiveTriangle hx hp
  rw [← centeredUpperTriangle_eq_sign_regions] at hsplitOuter
  calc
    (∫ t : ℝ in 0..2,
        factorTwoCenteredCrossCorrelation
            (fun x ↦ |e x|) (fun x ↦ |o x|) t / (2 - t)) =
        ∫ z : ℝ × ℝ in centeredUpperTriangle, F z := by
      simpa only [F] using
        integral_abs_cross_div_two_sub_eq_centeredUpperTriangle e o hec hoc
    _ = (∫ z : ℝ × ℝ in centeredNegativeTriangle, F z) +
        ∫ z : ℝ × ℝ in centeredCrossRectangle ∪ centeredPositiveTriangle,
          F z := hsplitOuter
    _ = (∫ z : ℝ × ℝ in centeredNegativeTriangle, F z) +
        ((∫ z : ℝ × ℝ in centeredCrossRectangle, F z) +
          ∫ z : ℝ × ℝ in centeredPositiveTriangle, F z) := by
      rw [Measure.volume_eq_prod ℝ ℝ]
      rw [hsplitInner]
    _ = (∫ z : ℝ × ℝ in unitLowerTriangle,
          |e (1 - z.1) * o (1 - z.2)| / (2 - z.1 + z.2)) +
        ((∫ z : ℝ × ℝ in unitSquare,
          |e (1 - z.1) * o (1 - z.2)| / (z.1 + z.2)) +
        ∫ z : ℝ × ℝ in unitUpperTriangle,
          |e (1 - z.1) * o (1 - z.2)| / (2 + z.1 - z.2)) := by
      rw [setIntegral_centeredNegative_eq_unitLower e o he ho,
        setIntegral_centeredCross_eq_unitSquare e o ho,
        setIntegral_centeredPositive_eq_unitUpper e o]

private theorem ae_snd_ne (c : ℝ) :
    ∀ᵐ z : ℝ × ℝ ∂((volume : Measure ℝ).prod volume), z.2 ≠ c := by
  apply (MeasureTheory.Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [] with _x
  exact MeasureTheory.Measure.ae_ne volume c

private theorem ae_fst_ne_snd :
    ∀ᵐ z : ℝ × ℝ ∂((volume : Measure ℝ).prod volume), z.1 ≠ z.2 := by
  apply (MeasureTheory.Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [] with x
  filter_upwards [MeasureTheory.Measure.ae_ne volume x] with y hy
  exact Ne.symm hy

private theorem unitTriangles_aedisjoint :
    AEDisjoint ((volume : Measure ℝ).prod volume)
      unitLowerTriangle unitUpperTriangle := by
  rw [AEDisjoint, measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_fst_ne_snd] with z hne
  rintro ⟨hl, hu⟩
  exact hne (le_antisymm hu.2.1 hl.2.1)

private theorem unitTriangles_union_ae_eq_square :
    (unitLowerTriangle ∪ unitUpperTriangle : Set (ℝ × ℝ)) =ᵐ[
      ((volume : Measure ℝ).prod volume)] unitSquare := by
  filter_upwards [ae_fst_ne 1, ae_snd_ne 1] with z hp1 hq1
  apply propext
  change ((0 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 < 1) ∨
      (0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 < 1)) ↔
    (z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1)
  constructor
  · rintro (hl | hu)
    · exact ⟨⟨hl.1.trans hl.2.1, hl.2.2.le⟩,
        ⟨hl.1, hl.2.1.trans hl.2.2.le⟩⟩
    · exact ⟨⟨hu.1, hu.2.1.trans hu.2.2.le⟩,
        ⟨hu.1.trans hu.2.1, hu.2.2.le⟩⟩
  · intro hsquare
    have hp_lt : z.1 < 1 := lt_of_le_of_ne hsquare.1.2 hp1
    have hq_lt : z.2 < 1 := lt_of_le_of_ne hsquare.2.2 hq1
    rcases le_total z.2 z.1 with hqp | hpq
    · exact Or.inl ⟨hsquare.2.1, hqp, hp_lt⟩
    · exact Or.inr ⟨hsquare.1.1, hpq, hq_lt⟩

private theorem integrableOn_unitSquare_parityFoldedComponents
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    IntegrableOn
        (fun z : ℝ × ℝ ↦ |f z.1 * g z.2| / (z.1 + z.2))
        unitSquare ((volume : Measure ℝ).prod volume) ∧
      IntegrableOn
        (fun z : ℝ × ℝ ↦
          |f z.1 * g z.2| / (2 - |z.1 - z.2|))
        unitSquare ((volume : Measure ℝ).prod volume) := by
  have hfold := integrable_parityFoldedTriangleAbsBilinearDensity
    f g hf hg
  rw [Measure.prod_restrict] at hfold
  have hfoldSquare : IntegrableOn
      (parityFoldedTriangleAbsBilinearDensity f g) unitSquare
      ((volume : Measure ℝ).prod volume) := by
    have hfoldIoc : IntegrableOn
        (parityFoldedTriangleAbsBilinearDensity f g)
        (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)
        ((volume : Measure ℝ).prod volume) := hfold
    exact hfoldIoc.congr_set_ae
      (Measure.set_prod_ae_eq Ioc_ae_eq_Icc Ioc_ae_eq_Icc).symm
  have hmeasFirst : AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦ |f z.1 * g z.2| / (z.1 + z.2))
      (((volume : Measure ℝ).prod volume).restrict unitSquare) :=
    (by fun_prop : Measurable (fun z : ℝ × ℝ ↦
      |f z.1 * g z.2| / (z.1 + z.2))).aestronglyMeasurable
  have hmeasSecond : AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦ |f z.1 * g z.2| / (2 - |z.1 - z.2|))
      (((volume : Measure ℝ).prod volume).restrict unitSquare) :=
    (by fun_prop : Measurable (fun z : ℝ × ℝ ↦
      |f z.1 * g z.2| / (2 - |z.1 - z.2|))).aestronglyMeasurable
  constructor
  · apply hfoldSquare.mono' hmeasFirst
    filter_upwards [ae_restrict_mem measurableSet_unitSquare] with z hz
    have habs : |z.1 - z.2| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
    have hdenFirst : 0 ≤ z.1 + z.2 := add_nonneg hz.1.1 hz.2.1
    have hfirst : 0 ≤ 1 / (z.1 + z.2) := one_div_nonneg.mpr hdenFirst
    have hsecond : 0 ≤ 1 / (2 - |z.1 - z.2|) :=
      one_div_nonneg.mpr (by linarith)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (abs_nonneg _) hdenFirst)]
    unfold parityFoldedTriangleAbsBilinearDensity parityFoldedTriangleKernel
    rw [div_eq_mul_inv]
    have hfirst_le : (z.1 + z.2)⁻¹ ≤
        1 / (z.1 + z.2) + 1 / (2 - |z.1 - z.2|) := by
      simpa only [one_div] using
        (le_add_of_nonneg_right hsecond :
          1 / (z.1 + z.2) ≤
            1 / (z.1 + z.2) + 1 / (2 - |z.1 - z.2|))
    exact mul_le_mul_of_nonneg_left hfirst_le (abs_nonneg _)
  · apply hfoldSquare.mono' hmeasSecond
    filter_upwards [ae_restrict_mem measurableSet_unitSquare] with z hz
    have habs : |z.1 - z.2| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
    have hden : 0 ≤ 2 - |z.1 - z.2| := by linarith
    have hfirst : 0 ≤ 1 / (z.1 + z.2) :=
      one_div_nonneg.mpr (add_nonneg hz.1.1 hz.2.1)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (abs_nonneg _) hden)]
    unfold parityFoldedTriangleAbsBilinearDensity parityFoldedTriangleKernel
    rw [div_eq_mul_inv]
    have hsecond_le : (2 - |z.1 - z.2|)⁻¹ ≤
        1 / (z.1 + z.2) + 1 / (2 - |z.1 - z.2|) := by
      simpa only [one_div] using
        (le_add_of_nonneg_left hfirst :
          1 / (2 - |z.1 - z.2|) ≤
            1 / (z.1 + z.2) + 1 / (2 - |z.1 - z.2|))
    exact mul_le_mul_of_nonneg_left hsecond_le (abs_nonneg _)

private theorem sum_unitTriangles_eq_second_foldedIntegral
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o) :
    (∫ z : ℝ × ℝ in unitLowerTriangle,
        |e (1 - z.1) * o (1 - z.2)| / (2 - z.1 + z.2)) +
      (∫ z : ℝ × ℝ in unitUpperTriangle,
        |e (1 - z.1) * o (1 - z.2)| / (2 + z.1 - z.2)) =
      ∫ z : ℝ × ℝ in unitSquare,
        |e (1 - z.1) * o (1 - z.2)| /
          (2 - |z.1 - z.2|) := by
  let f : ℝ → ℝ := fun p ↦ e (1 - p)
  let g : ℝ → ℝ := fun q ↦ o (1 - q)
  let K : ℝ × ℝ → ℝ := fun z ↦
    |f z.1 * g z.2| / (2 - |z.1 - z.2|)
  have hfc : Continuous f := by
    dsimp only [f]
    fun_prop
  have hgc : Continuous g := by
    dsimp only [g]
    fun_prop
  have hK : IntegrableOn K unitSquare
      ((volume : Measure ℝ).prod volume) := by
    simpa only [K] using
      (integrableOn_unitSquare_parityFoldedComponents f g hfc hgc).2
  have hKL := hK.mono_set (show unitLowerTriangle ⊆ unitSquare by
    intro z hz
    exact ⟨⟨hz.1.trans hz.2.1, hz.2.2.le⟩,
      ⟨hz.1, hz.2.1.trans hz.2.2.le⟩⟩)
  have hKU := hK.mono_set (show unitUpperTriangle ⊆ unitSquare by
    intro z hz
    exact ⟨⟨hz.1, hz.2.1.trans hz.2.2.le⟩,
      ⟨hz.1.trans hz.2.1, hz.2.2.le⟩⟩)
  have hsplit := setIntegral_union₀ unitTriangles_aedisjoint
    measurableSet_unitUpperTriangle.nullMeasurableSet hKL hKU
  have hunion := setIntegral_congr_set
    (f := K) unitTriangles_union_ae_eq_square
  calc
    (∫ z : ℝ × ℝ in unitLowerTriangle,
        |e (1 - z.1) * o (1 - z.2)| / (2 - z.1 + z.2)) +
        (∫ z : ℝ × ℝ in unitUpperTriangle,
          |e (1 - z.1) * o (1 - z.2)| / (2 + z.1 - z.2)) =
        (∫ z : ℝ × ℝ in unitLowerTriangle, K z) +
          ∫ z : ℝ × ℝ in unitUpperTriangle, K z := by
      congr 1
      · apply setIntegral_congr_fun measurableSet_unitLowerTriangle
        intro z hz
        dsimp only [K, f, g]
        rw [abs_of_nonneg (sub_nonneg.mpr hz.2.1)]
        congr 1
        ring
      · apply setIntegral_congr_fun measurableSet_unitUpperTriangle
        intro z hz
        dsimp only [K, f, g]
        rw [abs_of_nonpos (sub_nonpos.mpr hz.2.1)]
        congr 1
        ring
    _ = ∫ z : ℝ × ℝ in unitLowerTriangle ∪ unitUpperTriangle,
        K z := hsplit.symm
    _ = ∫ z : ℝ × ℝ in unitSquare, K z := hunion
    _ = ∫ z : ℝ × ℝ in unitSquare,
        |e (1 - z.1) * o (1 - z.2)| /
          (2 - |z.1 - z.2|) := by rfl

/-- Exact parity fold of the absolute even--odd correlation pole into the
endpoint Carleman density on the positive unit square. -/
theorem integral_abs_cross_div_two_sub_eq_parityFoldedTriangleDensity
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o) :
    (∫ t : ℝ in 0..2,
      factorTwoCenteredCrossCorrelation
          (fun x ↦ |e x|) (fun x ↦ |o x|) t / (2 - t)) =
      ∫ z : ℝ × ℝ,
        parityFoldedTriangleAbsBilinearDensity
          (fun p ↦ e (1 - p)) (fun q ↦ o (1 - q)) z
        ∂((volume.restrict (Ioc 0 1)).prod
          (volume.restrict (Ioc 0 1))) := by
  let f : ℝ → ℝ := fun p ↦ e (1 - p)
  let g : ℝ → ℝ := fun q ↦ o (1 - q)
  let K₁ : ℝ × ℝ → ℝ := fun z ↦ |f z.1 * g z.2| / (z.1 + z.2)
  let K₂ : ℝ × ℝ → ℝ := fun z ↦
    |f z.1 * g z.2| / (2 - |z.1 - z.2|)
  have hfc : Continuous f := by
    dsimp only [f]
    fun_prop
  have hgc : Continuous g := by
    dsimp only [g]
    fun_prop
  have hcomponents :=
    integrableOn_unitSquare_parityFoldedComponents f g hfc hgc
  have hK₁ : IntegrableOn K₁ unitSquare
      ((volume : Measure ℝ).prod volume) := by
    simpa only [K₁] using hcomponents.1
  have hK₂ : IntegrableOn K₂ unitSquare
      ((volume : Measure ℝ).prod volume) := by
    simpa only [K₂] using hcomponents.2
  have hsum :
      (∫ z : ℝ × ℝ in unitSquare, K₁ z) +
          (∫ z : ℝ × ℝ in unitSquare, K₂ z) =
        ∫ z : ℝ × ℝ in unitSquare,
          parityFoldedTriangleAbsBilinearDensity f g z := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    rw [← integral_add hK₁ hK₂]
    apply setIntegral_congr_fun measurableSet_unitSquare
    intro z _hz
    dsimp only [K₁, K₂]
    unfold parityFoldedTriangleAbsBilinearDensity parityFoldedTriangleKernel
    rw [div_eq_mul_inv, div_eq_mul_inv, one_div]
    ring
  have hmeasure :
      (∫ z : ℝ × ℝ in unitSquare,
        parityFoldedTriangleAbsBilinearDensity f g z) =
      ∫ z : ℝ × ℝ, parityFoldedTriangleAbsBilinearDensity f g z
        ∂((volume.restrict (Ioc 0 1)).prod
          (volume.restrict (Ioc 0 1))) := by
    rw [Measure.prod_restrict]
    rw [Measure.volume_eq_prod ℝ ℝ]
    unfold unitSquare
    exact setIntegral_congr_set
      (Measure.set_prod_ae_eq Ioc_ae_eq_Icc Ioc_ae_eq_Icc).symm
  have hpieces := integral_abs_cross_div_two_sub_eq_sign_foldedPieces
    e o hec hoc he ho
  have hsecond := sum_unitTriangles_eq_second_foldedIntegral e o hec hoc
  calc
    (∫ t : ℝ in 0..2,
        factorTwoCenteredCrossCorrelation
            (fun x ↦ |e x|) (fun x ↦ |o x|) t / (2 - t)) =
        (∫ z : ℝ × ℝ in unitLowerTriangle,
          |e (1 - z.1) * o (1 - z.2)| / (2 - z.1 + z.2)) +
        ((∫ z : ℝ × ℝ in unitSquare,
          |e (1 - z.1) * o (1 - z.2)| / (z.1 + z.2)) +
        ∫ z : ℝ × ℝ in unitUpperTriangle,
          |e (1 - z.1) * o (1 - z.2)| / (2 + z.1 - z.2)) := hpieces
    _ = (∫ z : ℝ × ℝ in unitSquare,
          |e (1 - z.1) * o (1 - z.2)| / (z.1 + z.2)) +
        ((∫ z : ℝ × ℝ in unitLowerTriangle,
          |e (1 - z.1) * o (1 - z.2)| / (2 - z.1 + z.2)) +
        ∫ z : ℝ × ℝ in unitUpperTriangle,
          |e (1 - z.1) * o (1 - z.2)| / (2 + z.1 - z.2)) := by ring
    _ = (∫ z : ℝ × ℝ in unitSquare, K₁ z) +
        ∫ z : ℝ × ℝ in unitSquare, K₂ z := by
      rw [hsecond]
    _ = ∫ z : ℝ × ℝ in unitSquare,
        parityFoldedTriangleAbsBilinearDensity f g z := hsum
    _ = ∫ z : ℝ × ℝ,
        parityFoldedTriangleAbsBilinearDensity
          (fun p ↦ e (1 - p)) (fun q ↦ o (1 - q)) z
        ∂((volume.restrict (Ioc 0 1)).prod
          (volume.restrict (Ioc 0 1))) := by
      simpa only [f, g] using hmeasure

/-- The absolute even--odd endpoint pole costs `π / 2` after centered-energy
normalization. -/
theorem integral_abs_cross_div_two_sub_le_pi_half_sqrt_energy
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o) :
    (∫ t : ℝ in 0..2,
      |factorTwoCenteredCrossCorrelation e o t| / (2 - t)) ≤
      (Real.pi / 2) * Real.sqrt
        ((∫ x : ℝ in -1..1, e x ^ 2) *
          (∫ x : ℝ in -1..1, o x ^ 2)) := by
  let C : ℝ → ℝ := factorTwoCenteredCrossCorrelation e o
  let Ca : ℝ → ℝ := factorTwoCenteredCrossCorrelation
    (fun x ↦ |e x|) (fun x ↦ |o x|)
  have hCint :=
    intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
      e o hec hoc
  have hCaint :=
    intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
      (fun x ↦ |e x|) (fun x ↦ |o x|) hec.abs hoc.abs
  have habsEq :
      (∫ t : ℝ in 0..2, |C t| / (2 - t)) =
        ∫ t : ℝ in 0..2, |C t / (2 - t)| := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ)] with t ht2
    intro htmem
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at htmem
    have hden : 0 ≤ 2 - t := sub_nonneg.mpr htmem.2
    rw [abs_div, abs_of_nonneg hden]
  have hmono :
      (∫ t : ℝ in 0..2, |C t / (2 - t)|) ≤
        ∫ t : ℝ in 0..2, Ca t / (2 - t) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num : (0 : ℝ) ≤ 2) hCint.abs hCaint
    intro t ht
    have hden : 0 < 2 - t := by linarith [ht.2]
    have htriangle : |C t| ≤ Ca t := by
      dsimp only [C, Ca]
      unfold factorTwoCenteredCrossCorrelation
      have habsIntegral := intervalIntegral.abs_integral_le_integral_abs
        (μ := volume)
        (show (-1 : ℝ) ≤ 1 - t by linarith [ht.2])
        (f := fun x : ℝ ↦ e (t + x) * o x)
      simpa only [abs_mul] using habsIntegral
    rw [abs_div, abs_of_pos hden]
    exact div_le_div_of_nonneg_right htriangle hden.le
  let f : ℝ → ℝ := fun p ↦ e (1 - p)
  let g : ℝ → ℝ := fun q ↦ o (1 - q)
  have hfc : Continuous f := by
    dsimp only [f]
    fun_prop
  have hgc : Continuous g := by
    dsimp only [g]
    fun_prop
  have hcarleman :=
    integral_parityFoldedTriangleAbsBilinearDensity_le_pi_mul_sqrt_energy
      f g hfc hgc
  have hfold :=
    integral_abs_cross_div_two_sub_eq_parityFoldedTriangleDensity
      e o hec hoc he ho
  have hhalfE := endpoint_half_energy_of_even_or_odd e hec (Or.inl he)
  have hhalfO := endpoint_half_energy_of_even_or_odd o hoc (Or.inr ho)
  have hnormalize :
      Real.pi * Real.sqrt
          ((∫ p : ℝ in 0..1, f p ^ 2) *
            (∫ q : ℝ in 0..1, g q ^ 2)) =
        (Real.pi / 2) * Real.sqrt
          ((∫ x : ℝ in -1..1, e x ^ 2) *
            (∫ x : ℝ in -1..1, o x ^ 2)) := by
    dsimp only [f, g]
    rw [hhalfE, hhalfO]
    rw [show ((1 / 2 : ℝ) * (∫ x : ℝ in -1..1, e x ^ 2)) *
        ((1 / 2 : ℝ) * (∫ x : ℝ in -1..1, o x ^ 2)) =
        (1 / 4 : ℝ) *
          ((∫ x : ℝ in -1..1, e x ^ 2) *
            (∫ x : ℝ in -1..1, o x ^ 2)) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    norm_num
    ring
  calc
    (∫ t : ℝ in 0..2, |factorTwoCenteredCrossCorrelation e o t| /
        (2 - t)) = ∫ t : ℝ in 0..2, |C t| / (2 - t) := by rfl
    _ = ∫ t : ℝ in 0..2, |C t / (2 - t)| := habsEq
    _ ≤ ∫ t : ℝ in 0..2, Ca t / (2 - t) := hmono
    _ = ∫ z : ℝ × ℝ,
        parityFoldedTriangleAbsBilinearDensity f g z
          ∂((volume.restrict (Ioc 0 1)).prod
            (volume.restrict (Ioc 0 1))) := by
      simpa only [Ca, f, g] using hfold
    _ ≤ Real.pi * Real.sqrt
        ((∫ p : ℝ in 0..1, f p ^ 2) *
          (∫ q : ℝ in 0..1, g q ^ 2)) := hcarleman
    _ = (Real.pi / 2) * Real.sqrt
        ((∫ x : ℝ in -1..1, e x ^ 2) *
          (∫ x : ℝ in -1..1, o x ^ 2)) := hnormalize

private theorem intervalIntegrable_abs_cross_div_two_sub
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    IntervalIntegrable
      (fun t : ℝ ↦ |factorTwoCenteredCrossCorrelation u v t| / (2 - t))
      volume 0 2 := by
  have hbase :=
    (intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
      u v hu hv).abs
  apply hbase.congr
  intro t ht
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
  change |factorTwoCenteredCrossCorrelation u v t / (2 - t)| =
    |factorTwoCenteredCrossCorrelation u v t| / (2 - t)
  rw [abs_div, abs_of_nonneg (sub_nonneg.mpr ht.2)]

/-- The complete archimedean part of the alternating channel is bounded by
`27π/40` times the geometric mean of the centered parity energies. -/
theorem abs_factorTwo_alternating_archimedean_le_pi_sqrt_energy
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o) :
    |yoshidaEndpointA *
        (∫ t : ℝ in 0..2,
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            (factorTwoCenteredCrossCorrelation o e t -
              factorTwoCenteredCrossCorrelation e o t))| ≤
      (27 * Real.pi / 40) * Real.sqrt
        ((∫ x : ℝ in -1..1, e x ^ 2) *
          (∫ x : ℝ in -1..1, o x ^ 2)) := by
  let D : ℝ → ℝ := fun t ↦
    factorTwoCenteredCrossCorrelation o e t -
      factorTwoCenteredCrossCorrelation e o t
  let H : ℝ → ℝ := fun t ↦
    factorTwoAntisymmetricWeight (yoshidaEndpointA * t) * D t
  let Q : ℝ → ℝ := fun t ↦
    |factorTwoCenteredCrossCorrelation e o t| / (2 - t)
  let R : ℝ := Real.sqrt
    ((∫ x : ℝ in -1..1, e x ^ 2) *
      (∫ x : ℝ in -1..1, o x ^ 2))
  have hH : IntervalIntegrable H volume 0 2 := by
    simpa only [H, D] using
      intervalIntegrable_factorTwoCenteredAlternatingKernel e o hec hoc
  have hQ : IntervalIntegrable Q volume 0 2 := by
    simpa only [Q] using intervalIntegrable_abs_cross_div_two_sub e o hec hoc
  have hAH : IntervalIntegrable
      (fun t ↦ yoshidaEndpointA * H t) volume 0 2 :=
    hH.const_mul yoshidaEndpointA
  have habsIntegral :
      |∫ t : ℝ in 0..2, yoshidaEndpointA * H t| ≤
        ∫ t : ℝ in 0..2, |yoshidaEndpointA * H t| :=
    intervalIntegral.abs_integral_le_integral_abs
      (μ := volume) (by norm_num)
  have hpoint : ∀ t ∈ Ioo (0 : ℝ) 2,
      |yoshidaEndpointA * H t| ≤ (27 / 20 : ℝ) * Q t := by
    intro t ht
    have hscalar := factorTwo_complete_antisymmetric_scalar_bounds
      ht.1.le ht.2
    have hdiff :=
      factorTwo_crossDifference_eq_neg_two_cross_of_even_odd he ho t
    dsimp only [H, D, Q]
    rw [hdiff]
    rw [show yoshidaEndpointA *
          (factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            (-2 * factorTwoCenteredCrossCorrelation e o t)) =
        (yoshidaEndpointA *
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t)) *
            (-2 * factorTwoCenteredCrossCorrelation e o t) by ring,
      abs_mul, abs_of_nonneg hscalar.1, abs_mul, abs_neg]
    norm_num
    calc
      (yoshidaEndpointA *
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t)) *
          (2 * |factorTwoCenteredCrossCorrelation e o t|) ≤
        ((27 / 40 : ℝ) / (2 - t)) *
          (2 * |factorTwoCenteredCrossCorrelation e o t|) :=
        mul_le_mul_of_nonneg_right hscalar.2
          (mul_nonneg (by norm_num) (abs_nonneg _))
      _ = (27 / 20 : ℝ) *
          (|factorTwoCenteredCrossCorrelation e o t| / (2 - t)) := by ring
  have hmono :
      (∫ t : ℝ in 0..2, |yoshidaEndpointA * H t|) ≤
        ∫ t : ℝ in 0..2, (27 / 20 : ℝ) * Q t := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num : (0 : ℝ) ≤ 2) hAH.abs
      (hQ.const_mul (27 / 20 : ℝ))
    exact hpoint
  have hQbound : (∫ t : ℝ in 0..2, Q t) ≤
      (Real.pi / 2) * R := by
    simpa only [Q, R] using
      integral_abs_cross_div_two_sub_le_pi_half_sqrt_energy
        e o hec hoc he ho
  have hscale : yoshidaEndpointA * (∫ t : ℝ in 0..2, H t) =
      ∫ t : ℝ in 0..2, yoshidaEndpointA * H t := by
    rw [intervalIntegral.integral_const_mul]
  calc
    |yoshidaEndpointA *
        (∫ t : ℝ in 0..2,
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            (factorTwoCenteredCrossCorrelation o e t -
              factorTwoCenteredCrossCorrelation e o t))| =
        |yoshidaEndpointA * (∫ t : ℝ in 0..2, H t)| := by rfl
    _ = |∫ t : ℝ in 0..2, yoshidaEndpointA * H t| :=
      congrArg abs hscale
    _ ≤ ∫ t : ℝ in 0..2, |yoshidaEndpointA * H t| := habsIntegral
    _ ≤ ∫ t : ℝ in 0..2, (27 / 20 : ℝ) * Q t := hmono
    _ = (27 / 20 : ℝ) * (∫ t : ℝ in 0..2, Q t) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (27 / 20 : ℝ) * ((Real.pi / 2) * R) :=
      mul_le_mul_of_nonneg_left hQbound (by norm_num)
    _ = (27 * Real.pi / 40) * Real.sqrt
        ((∫ x : ℝ in -1..1, e x ^ 2) *
          (∫ x : ℝ in -1..1, o x ^ 2)) := by
      dsimp only [R]
      ring

/-- The full alternating coupling, including the retained `p = 3` atom, is
bounded by `25/8` times the geometric mean of the parity energies. -/
theorem abs_factorTwoCenteredAlternatingCoupling_le_sqrt_energy
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o) :
    |factorTwoCenteredAlternatingCoupling e o| ≤
      (25 / 8 : ℝ) * Real.sqrt
        ((∫ x : ℝ in -1..1, e x ^ 2) *
          (∫ x : ℝ in -1..1, o x ^ 2)) := by
  let E : ℝ :=
    (∫ x : ℝ in -1..1, e x ^ 2) *
      (∫ x : ℝ in -1..1, o x ^ 2)
  let R : ℝ := Real.sqrt E
  let Aterm : ℝ := yoshidaEndpointA *
    (∫ t : ℝ in 0..2,
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation o e t -
          factorTwoCenteredCrossCorrelation e o t))
  let Pterm : ℝ := -(Real.log 3 / Real.sqrt 3) *
    (factorTwoCenteredCrossCorrelation o e
        (factorTwoPrimeShift / yoshidaEndpointA) -
      factorTwoCenteredCrossCorrelation e o
        (factorTwoPrimeShift / yoshidaEndpointA))
  have hdecomp : factorTwoCenteredAlternatingCoupling e o =
      Aterm + Pterm := by
    unfold factorTwoCenteredAlternatingCoupling
    dsimp only [Aterm, Pterm]
    ring
  have harch : |Aterm| ≤ (27 * Real.pi / 40) * R := by
    simpa only [Aterm, R, E] using
      abs_factorTwo_alternating_archimedean_le_pi_sqrt_energy
        e o hec hoc he ho
  have hprime : |Pterm| ≤ R := by
    simpa only [Pterm, R, E] using
      abs_factorTwo_alternating_prime_le_sqrt_energy e o hec hoc he ho
  have htriangle : |factorTwoCenteredAlternatingCoupling e o| ≤
      ((27 / 40 : ℝ) * Real.pi + 1) * R := by
    rw [hdecomp]
    calc
      |Aterm + Pterm| ≤ |Aterm| + |Pterm| := abs_add_le Aterm Pterm
      _ ≤ (27 * Real.pi / 40) * R + R := add_le_add harch hprime
      _ = ((27 / 40 : ℝ) * Real.pi + 1) * R := by ring
  have hbudget : ((27 / 40 : ℝ) * Real.pi + 1) * R ≤
      (25 / 8 : ℝ) * R :=
    mul_le_mul_of_nonneg_right carleman_prime_budget_lt_cross_constant.le
      (Real.sqrt_nonneg E)
  calc
    |factorTwoCenteredAlternatingCoupling e o| ≤
        ((27 / 40 : ℝ) * Real.pi + 1) * R := htriangle
    _ ≤ (25 / 8 : ℝ) * R := hbudget
    _ = (25 / 8 : ℝ) * Real.sqrt
        ((∫ x : ℝ in -1..1, e x ^ 2) *
          (∫ x : ℝ in -1..1, o x ^ 2)) := by rfl

/-- Unconditional concrete cross-channel estimate required by the factor-two
phase square: `J² ≤ 625/64 · E_even · E_odd`. -/
theorem factorTwoCenteredAlternatingCoupling_sq_le_energy_mul
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o) :
    factorTwoCenteredAlternatingCoupling e o ^ 2 ≤
      (625 / 64 : ℝ) *
        ((∫ x : ℝ in -1..1, e x ^ 2) *
          (∫ x : ℝ in -1..1, o x ^ 2)) := by
  let E : ℝ :=
    (∫ x : ℝ in -1..1, e x ^ 2) *
      (∫ x : ℝ in -1..1, o x ^ 2)
  have hEe : 0 ≤ ∫ x : ℝ in -1..1, e x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (e x))
  have hEo : 0 ≤ ∫ x : ℝ in -1..1, o x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (o x))
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg hEe hEo
  have habs : |factorTwoCenteredAlternatingCoupling e o| ≤
      (25 / 8 : ℝ) * Real.sqrt E := by
    simpa only [E] using
      abs_factorTwoCenteredAlternatingCoupling_le_sqrt_energy
        e o hec hoc he ho
  have hsq : |factorTwoCenteredAlternatingCoupling e o| ^ 2 ≤
      ((25 / 8 : ℝ) * Real.sqrt E) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg E))).2 habs
  calc
    factorTwoCenteredAlternatingCoupling e o ^ 2 =
        |factorTwoCenteredAlternatingCoupling e o| ^ 2 := by
      rw [sq_abs]
    _ ≤ ((25 / 8 : ℝ) * Real.sqrt E) ^ 2 := hsq
    _ = (625 / 64 : ℝ) * E := by
      rw [mul_pow, Real.sq_sqrt hE]
      norm_num
    _ = (625 / 64 : ℝ) *
        ((∫ x : ℝ in -1..1, e x ^ 2) *
          (∫ x : ℝ in -1..1, o x ^ 2)) := by rfl

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseAlternatingCoercivity
