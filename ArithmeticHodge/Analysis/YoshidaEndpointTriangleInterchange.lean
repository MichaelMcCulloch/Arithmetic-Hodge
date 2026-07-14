import ArithmeticHodge.Analysis.YoshidaEndpointPositiveDistanceFold
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointTriangleInterchange

open UnitIntervalLogEnergyAffine
open YoshidaEndpointPositiveDistanceFold

noncomputable section

/-!
# Triangle-to-square interchange

The positive-distance shear `(t,x) ↦ (x+t,x)` identifies the overlap
triangle with the upper half of the centered square.  Symmetry of the
logarithmic difference kernel then supplies the factor `1/2`.
-/

/-- Positive-distance coordinates in the `(t,x)` plane. -/
def positiveDistanceTriangle : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 2 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 - p.1}

/-- The upper half of the centered `(y,x)` square. -/
def centeredUpperTriangle : Set (ℝ × ℝ) :=
  {p | -1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1}

/-- The unit-Jacobian shear sends the positive-distance triangle to the
upper centered triangle. -/
theorem setIntegral_positiveDistanceTriangle_shear
    (F : ℝ × ℝ → ℝ) :
    (∫ p : ℝ × ℝ in positiveDistanceTriangle,
      F (p.1 + p.2, p.2)) =
      ∫ p : ℝ × ℝ in centeredUpperTriangle, F p := by
  let S : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1 + p.2, p.2)
  have hpre : S ⁻¹' centeredUpperTriangle = positiveDistanceTriangle := by
    ext p
    change (-1 ≤ p.2 ∧ p.2 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 1) ↔
      (0 ≤ p.1 ∧ p.1 ≤ 2 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 - p.1)
    constructor
    · rintro ⟨hxlow, hxy, hyhigh⟩
      constructor
      · linarith
      constructor
      · linarith
      exact ⟨hxlow, by linarith⟩
    · rintro ⟨htlow, _hthigh, hxlow, hxhigh⟩
      exact ⟨hxlow, by linarith, by linarith⟩
  have hmem (p : ℝ × ℝ) :
      S p ∈ centeredUpperTriangle ↔ p ∈ positiveDistanceTriangle := by
    change p ∈ S ⁻¹' centeredUpperTriangle ↔ _
    rw [hpre]
  have hmeasure : MeasurePreserving S
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) := by
    exact measurePreserving_add_prod volume volume
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    MeasurableEquiv.prodComm.trans
      ((MeasurableEquiv.shearAddRight ℝ).trans MeasurableEquiv.prodComm)
  have he_apply (p : ℝ × ℝ) : e p = S p := by
    change (p.2 + p.1, p.2) = (p.1 + p.2, p.2)
    congr 1
    ring
  have hTmeas : MeasurableSet positiveDistanceTriangle := by
    unfold positiveDistanceTriangle
    measurability
  have hUmeas : MeasurableSet centeredUpperTriangle := by
    unfold centeredUpperTriangle
    measurability
  have hcomp := hmeasure.integral_comp
    (by
      rw [← funext he_apply]
      exact e.measurableEmbedding)
    (centeredUpperTriangle.indicator F)
  calc
    _ = ∫ p : ℝ × ℝ,
        positiveDistanceTriangle.indicator (fun p ↦ F (p.1 + p.2, p.2)) p :=
      (integral_indicator hTmeas).symm
    _ = ∫ p : ℝ × ℝ, (centeredUpperTriangle.indicator F) (S p) := by
      apply integral_congr_ae
      filter_upwards [] with p
      by_cases hp : p ∈ positiveDistanceTriangle
      · rw [Set.indicator_of_mem hp,
          Set.indicator_of_mem ((hmem p).2 hp)]
      · rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (mt (hmem p).1 hp)]
    _ = _ := hcomp
    _ = _ := integral_indicator hUmeas

/-- Iterated centered interval integration is the set integral over the
centered square. -/
theorem setIntegral_centeredSquare_eq_iterated
    (K : ℝ × ℝ → ℝ) (hK : Continuous K) :
    (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, K p) =
      ∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1, K (y, x) := by
  have hKSquare : IntegrableOn K
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    hK.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  symm
  calc
    (∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1, K (y, x)) =
        ∫ y : ℝ in Icc (-1) 1,
          ∫ x : ℝ in Icc (-1) 1, K (y, x) := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro y _hy
      change (∫ x : ℝ in -1..1, K (y, x)) =
        ∫ x : ℝ in Icc (-1) 1, K (y, x)
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, K p :=
      (setIntegral_prod K hKSquare).symm

/-- A swap-invariant continuous kernel integrates over the centered square as
twice its integral over the upper triangle.  The diagonal is discarded only
as a product-null set; no pointwise condition on the kernel is needed there. -/
theorem two_mul_setIntegral_centeredUpperTriangle_eq_centeredSquare
    (K : ℝ × ℝ → ℝ) (hK : Continuous K)
    (hKswap : ∀ p : ℝ × ℝ, K p.swap = K p) :
    2 * (∫ p : ℝ × ℝ in centeredUpperTriangle, K p) =
      ∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, K p := by
  let S : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
  let U : Set (ℝ × ℝ) := centeredUpperTriangle
  have hSmeas : MeasurableSet S := by
    dsimp only [S]
    exact measurableSet_Icc.prod measurableSet_Icc
  have hUmeas : MeasurableSet U := by
    dsimp only [U]
    unfold centeredUpperTriangle
    measurability
  have hKSquare : IntegrableOn K S
      ((volume : Measure ℝ).prod volume) := by
    apply hK.continuousOn.integrableOn_compact
    dsimp only [S]
    exact isCompact_Icc.prod isCompact_Icc
  have hUsub : U ⊆ S := by
    intro p hp
    dsimp only [U, S] at hp ⊢
    unfold centeredUpperTriangle at hp
    exact ⟨⟨by linarith [hp.1, hp.2.1], hp.2.2⟩,
      ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩⟩
  have hKUpper : IntegrableOn K U
      ((volume : Measure ℝ).prod volume) :=
    hKSquare.mono_set hUsub
  have hIU : Integrable (U.indicator K)
      ((volume : Measure ℝ).prod volume) :=
    hKUpper.integrable_indicator hUmeas
  have haeNe : ∀ᵐ p : ℝ × ℝ
      ∂((volume : Measure ℝ).prod volume), p.1 ≠ p.2 := by
    apply (MeasureTheory.Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [] with y
    filter_upwards [MeasureTheory.Measure.ae_ne volume y] with x hx
    exact Ne.symm hx
  have hIndicatorSplit : ∀ᵐ p : ℝ × ℝ
      ∂((volume : Measure ℝ).prod volume),
      S.indicator K p = U.indicator K p + U.indicator K p.swap := by
    filter_upwards [haeNe] with p hpne
    by_cases hpS : p ∈ S
    · rcases lt_or_gt_of_ne hpne with hlt | hgt
      · have hpU : p ∉ U := by
          intro hpU
          dsimp only [U] at hpU
          unfold centeredUpperTriangle at hpU
          linarith [hpU.2.1]
        have hswapU : p.swap ∈ U := by
          rcases p with ⟨y, x⟩
          dsimp only [S, U, Prod.swap_prod_mk] at hpS ⊢
          unfold centeredUpperTriangle
          exact ⟨hpS.1.1, hlt.le, hpS.2.2⟩
        rw [Set.indicator_of_mem hpS, Set.indicator_of_notMem hpU,
          Set.indicator_of_mem hswapU, hKswap]
        ring
      · have hpU : p ∈ U := by
          rcases p with ⟨y, x⟩
          dsimp only [S, U] at hpS ⊢
          unfold centeredUpperTriangle
          exact ⟨hpS.2.1, hgt.le, hpS.1.2⟩
        have hswapU : p.swap ∉ U := by
          intro hswapU
          rcases p with ⟨y, x⟩
          dsimp only [U, Prod.swap_prod_mk] at hswapU
          unfold centeredUpperTriangle at hswapU
          linarith [hswapU.2.1]
        rw [Set.indicator_of_mem hpS, Set.indicator_of_mem hpU,
          Set.indicator_of_notMem hswapU]
        ring
    · have hpU : p ∉ U := fun hpU ↦ hpS (hUsub hpU)
      have hswapU : p.swap ∉ U := by
        intro hswapU
        have hsS := hUsub hswapU
        apply hpS
        rcases p with ⟨y, x⟩
        dsimp only [S, Prod.swap_prod_mk] at hsS ⊢
        exact ⟨hsS.2, hsS.1⟩
      rw [Set.indicator_of_notMem hpS, Set.indicator_of_notMem hpU,
        Set.indicator_of_notMem hswapU]
      ring
  have hswapIntegral :
      (∫ p : ℝ × ℝ, U.indicator K p.swap) =
        ∫ p : ℝ × ℝ, U.indicator K p := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact integral_prod_swap (U.indicator K)
  rw [← integral_indicator hSmeas, ← integral_indicator hUmeas]
  calc
    2 * (∫ p : ℝ × ℝ, U.indicator K p) =
        (∫ p : ℝ × ℝ, U.indicator K p) +
          ∫ p : ℝ × ℝ, U.indicator K p.swap := by
      rw [hswapIntegral]
      ring
    _ = ∫ p : ℝ × ℝ,
        (U.indicator K p + U.indicator K p.swap) := by
      simpa only [Pi.add_apply, Function.comp_apply] using
        (integral_add hIU hIU.swap).symm
    _ = ∫ p : ℝ × ℝ, S.indicator K p := by
      exact integral_congr_ae (hIndicatorSplit.mono fun _ hp ↦ hp.symm)

end

end ArithmeticHodge.Analysis.YoshidaEndpointTriangleInterchange
