import ArithmeticHodge.Analysis.YoshidaEndpointTriangleInterchange
import ArithmeticHodge.Analysis.YoshidaEndpointPositiveDistanceFold
import ArithmeticHodge.Analysis.UnitIntervalLogEnergyLipschitz
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointTriangleFoldLipschitz

open UnitIntervalLogEnergyAffine
open YoshidaEndpointPositiveDistanceFold
open YoshidaEndpointTriangleInterchange
open YoshidaEndpointSingularCorrelation

noncomputable section

/-!
# Lipschitz positive-distance triangle fold

Lipschitz regularity makes the logarithmic difference kernel integrable on
the centered square.  Fubini, the determinant-one shear, and symmetry then
identify the positive-distance triangle with one half of the square.
-/

/-- The centered logarithmic difference kernel is genuinely product
integrable on the square for a Lipschitz profile. -/
theorem integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith
    {C : NNReal} (w : ℝ → ℝ)
    (hw : LipschitzOnWith C w (Icc (-1) 1)) :
    IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w p.1 p.2)
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) := by
  obtain ⟨W, hW, hW_eq⟩ := hw.extend_real
  let K : ℝ × ℝ → ℝ := fun p ↦
    centeredLogDifferenceKernel W p.1 p.2
  let D : ℝ × ℝ → ℝ := fun p ↦
    (C : ℝ) ^ 2 * |p.1 - p.2|
  let S : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
  have hSmeas : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hDcont : Continuous D := by
    dsimp only [D]
    fun_prop
  have hDint : IntegrableOn D S ((volume : Measure ℝ).prod volume) := by
    exact hDcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hKmeas : AEStronglyMeasurable K
      (((volume : Measure ℝ).prod volume).restrict S) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [K]
    unfold centeredLogDifferenceKernel
    have hWmeas : Measurable W := hW.continuous.measurable
    exact ((hWmeas.comp measurable_fst).sub
      (hWmeas.comp measurable_snd)).pow_const 2 |>.div (by fun_prop)
  have hKint : IntegrableOn K S ((volume : Measure ℝ).prod volume) := by
    refine hDint.mono' hKmeas ?_
    filter_upwards [ae_restrict_mem hSmeas] with p hp
    dsimp only [K, D]
    unfold centeredLogDifferenceKernel
    have hdist : |W p.1 - W p.2| ≤
        (C : ℝ) * |p.1 - p.2| := by
      simpa only [Real.dist_eq] using hW.dist_le_mul p.1 p.2
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (sq_nonneg _) (abs_nonneg _))]
    by_cases hxy : |p.1 - p.2| = 0
    · simp [hxy]
    · have hxyPos : 0 < |p.1 - p.2| :=
        lt_of_le_of_ne (abs_nonneg _) (Ne.symm hxy)
      rw [div_le_iff₀ hxyPos]
      have hCnonneg : 0 ≤ (C : ℝ) := C.property
      have hsq := (sq_le_sq₀ (abs_nonneg (W p.1 - W p.2))
        (mul_nonneg hCnonneg (abs_nonneg _))).2 hdist
      rw [sq_abs, mul_pow] at hsq
      nlinarith
  apply hKint.congr
  filter_upwards [ae_restrict_mem hSmeas] with p hp
  dsimp only [K, S] at hp ⊢
  unfold centeredLogDifferenceKernel
  rw [hW_eq hp.1, hW_eq hp.2]

private theorem intervalIntegral_integral_eq_setIntegral_centeredSquare
    (F : ℝ × ℝ → ℝ)
    (hF : IntegrableOn F (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume)) :
    (∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, F (x, y)) =
      ∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, F p := by
  calc
    (∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, F (x, y)) =
        ∫ x : ℝ in Icc (-1) 1, ∫ y : ℝ in Icc (-1) 1, F (x, y) := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _hx
      change (∫ y : ℝ in -1..1, F (x, y)) =
        ∫ y : ℝ in Icc (-1) 1, F (x, y)
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, F p := by
      exact (setIntegral_prod F hF).symm

/-- The positive-distance kernel is product integrable on its triangular
domain.  This is the precise Fubini hypothesis behind the fold. -/
theorem integrableOn_centeredPositiveTriangleKernel_of_lipschitzOnWith
    {C : NNReal} (w : ℝ → ℝ)
    (hw : LipschitzOnWith C w (Icc (-1) 1)) :
    IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w (p.1 + p.2) p.2)
      positiveDistanceTriangle ((volume : Measure ℝ).prod volume) := by
  let K : ℝ × ℝ → ℝ := fun p ↦
    centeredLogDifferenceKernel w p.1 p.2
  let shear : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1 + p.2, p.2)
  have hKSquare : IntegrableOn K
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [K] using
      integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith w hw
  have hUpperSubset : centeredUpperTriangle ⊆
      Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    intro p hp
    unfold centeredUpperTriangle at hp
    exact ⟨⟨by linarith [hp.1, hp.2.1], hp.2.2⟩,
      ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩⟩
  have hKUpper : IntegrableOn K centeredUpperTriangle
      ((volume : Measure ℝ).prod volume) :=
    hKSquare.mono_set hUpperSubset
  have hpre : shear ⁻¹' centeredUpperTriangle = positiveDistanceTriangle := by
    ext p
    change (-1 ≤ p.2 ∧ p.2 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 1) ↔
      (0 ≤ p.1 ∧ p.1 ≤ 2 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 - p.1)
    constructor
    · rintro ⟨hxlow, hxy, hyhigh⟩
      exact ⟨by linarith, by linarith, hxlow, by linarith⟩
    · rintro ⟨htlow, _hthigh, hxlow, hxhigh⟩
      exact ⟨hxlow, by linarith, by linarith⟩
  have hShearMeasure : MeasurePreserving shear
      ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
    exact measurePreserving_add_prod volume volume
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    MeasurableEquiv.prodComm.trans
      ((MeasurableEquiv.shearAddRight ℝ).trans MeasurableEquiv.prodComm)
  have he_apply (p : ℝ × ℝ) : e p = shear p := by
    change (p.2 + p.1, p.2) = (p.1 + p.2, p.2)
    congr 1
    ring
  have hShearEmbedding : MeasurableEmbedding shear := by
    rw [← funext he_apply]
    exact e.measurableEmbedding
  have htransport :=
    (hShearMeasure.integrableOn_comp_preimage hShearEmbedding).2 hKUpper
  rw [hpre] at htransport
  simpa only [K, shear, Function.comp_apply] using htransport

/-- A Lipschitz profile satisfies the positive-distance triangular
interchange required by the singular-correlation fold. -/
theorem positiveDistanceTriangleInterchange_of_lipschitzOnWith
    {C : NNReal} (w : ℝ → ℝ)
    (hw : LipschitzOnWith C w (Icc (-1) 1)) :
    PositiveDistanceTriangleInterchange w := by
  let K : ℝ × ℝ → ℝ := fun p ↦
    centeredLogDifferenceKernel w p.1 p.2
  let H : ℝ × ℝ → ℝ := fun p ↦ K (p.1 + p.2, p.2)
  have hUpperMeas : MeasurableSet centeredUpperTriangle := by
    unfold centeredUpperTriangle
    measurability
  have hTriangleMeas : MeasurableSet positiveDistanceTriangle := by
    unfold positiveDistanceTriangle
    measurability
  have hKSquare : IntegrableOn K
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [K] using
      integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith w hw
  have hUpperSubset : centeredUpperTriangle ⊆
      Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    intro p hp
    change (-1 ≤ p.1 ∧ p.1 ≤ 1) ∧ (-1 ≤ p.2 ∧ p.2 ≤ 1)
    unfold centeredUpperTriangle at hp
    exact ⟨⟨by linarith [hp.1, hp.2.1], hp.2.2⟩,
      ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩⟩
  have hKUpper : IntegrableOn K centeredUpperTriangle
      ((volume : Measure ℝ).prod volume) :=
    hKSquare.mono_set hUpperSubset
  have hTriangleIndicator : Integrable
      (positiveDistanceTriangle.indicator H)
      ((volume : Measure ℝ).prod volume) := by
    apply IntegrableOn.integrable_indicator
    · simpa only [H, K] using
        integrableOn_centeredPositiveTriangleKernel_of_lipschitzOnWith w hw
    · exact hTriangleMeas
  have hTriangleFold : centeredPositiveTriangleEnergy w =
      ∫ p : ℝ × ℝ in positiveDistanceTriangle, H p := by
    rw [← integral_indicator hTriangleMeas,
      Measure.volume_eq_prod ℝ ℝ,
      integral_prod _ hTriangleIndicator]
    unfold centeredPositiveTriangleEnergy
    rw [intervalIntegral.integral_of_le (by norm_num),
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with t ht0
    by_cases ht : t ∈ Ioc (0 : ℝ) 2
    · rw [Set.indicator_of_mem ht]
      calc
        (∫ x : ℝ in -1..1 - t,
            centeredLogDifferenceKernel w (x + t) x) =
            ∫ x : ℝ,
              (Icc (-1 : ℝ) (1 - t)).indicator
                (fun x ↦ centeredLogDifferenceKernel w (x + t) x) x := by
          rw [intervalIntegral.integral_of_le (by linarith [ht.2]),
            ← integral_Icc_eq_integral_Ioc,
            ← integral_indicator measurableSet_Icc]
        _ = ∫ x : ℝ, positiveDistanceTriangle.indicator H (t, x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          by_cases hx : x ∈ Icc (-1 : ℝ) (1 - t)
          · have hp : (t, x) ∈ positiveDistanceTriangle :=
              ⟨ht.1.le, ht.2, hx.1, hx.2⟩
            rw [Set.indicator_of_mem hx, Set.indicator_of_mem hp]
            dsimp only [H, K]
            rw [add_comm]
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
  let lowerTriangle : Set (ℝ × ℝ) :=
    {p | -1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1}
  let openUpperTriangle : Set (ℝ × ℝ) :=
    {p | -1 ≤ p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 1}
  have hLowerMeas : MeasurableSet lowerTriangle := by
    dsimp only [lowerTriangle]
    measurability
  have hOpenUpperMeas : MeasurableSet openUpperTriangle := by
    dsimp only [openUpperTriangle]
    measurability
  have hLowerSubset : lowerTriangle ⊆
      Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    intro p hp
    change (-1 ≤ p.1 ∧ p.1 ≤ 1) ∧ (-1 ≤ p.2 ∧ p.2 ≤ 1)
    dsimp only [lowerTriangle] at hp
    exact ⟨⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩,
      ⟨by linarith [hp.1, hp.2.1], hp.2.2⟩⟩
  have hOpenUpperSubset : openUpperTriangle ⊆ centeredUpperTriangle := by
    intro p hp
    dsimp only [openUpperTriangle] at hp
    exact ⟨hp.1, hp.2.1.le, hp.2.2⟩
  have hKLower : IntegrableOn K lowerTriangle
      ((volume : Measure ℝ).prod volume) :=
    hKSquare.mono_set hLowerSubset
  have hSwapMem (p : ℝ × ℝ) :
      p.swap ∈ lowerTriangle ↔ p ∈ openUpperTriangle := by
    rcases p with ⟨x, y⟩
    rfl
  have hKSwap (p : ℝ × ℝ) : K p.swap = K p := by
    rcases p with ⟨x, y⟩
    dsimp only [K, Prod.swap_prod_mk]
    unfold centeredLogDifferenceKernel
    rw [abs_sub_comm]
    ring
  have hLowerEqOpenUpper :
      (∫ p : ℝ × ℝ in lowerTriangle, K p) =
        ∫ p : ℝ × ℝ in openUpperTriangle, K p := by
    calc
      (∫ p : ℝ × ℝ in lowerTriangle, K p) =
          ∫ p : ℝ × ℝ, lowerTriangle.indicator K p :=
        (integral_indicator hLowerMeas).symm
      _ = ∫ p : ℝ × ℝ, lowerTriangle.indicator K p.swap := by
        rw [Measure.volume_eq_prod ℝ ℝ]
        exact (integral_prod_swap (lowerTriangle.indicator K)).symm
      _ = ∫ p : ℝ × ℝ, openUpperTriangle.indicator K p := by
        apply integral_congr_ae
        filter_upwards [] with p
        by_cases hp : p ∈ openUpperTriangle
        · have hps : p.swap ∈ lowerTriangle := (hSwapMem p).2 hp
          rw [Set.indicator_of_mem hp, Set.indicator_of_mem hps, hKSwap]
        · have hps : p.swap ∉ lowerTriangle := mt (hSwapMem p).1 hp
          rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hps]
      _ = ∫ p : ℝ × ℝ in openUpperTriangle, K p :=
        integral_indicator hOpenUpperMeas
  have hOpenUpperEqUpper :
      (∫ p : ℝ × ℝ in centeredUpperTriangle, K p) =
        ∫ p : ℝ × ℝ in openUpperTriangle, K p := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
      hUpperMeas hOpenUpperSubset
    intro p hp
    have heq : p.2 = p.1 := by
      apply le_antisymm hp.1.2.1
      apply le_of_not_gt
      intro hlt
      exact hp.2 ⟨hp.1.1, hlt, hp.1.2.2⟩
    dsimp only [K]
    unfold centeredLogDifferenceKernel
    rw [heq]
    simp
  have hSquareUnion :
      Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 =
        centeredUpperTriangle ∪ lowerTriangle := by
    ext p
    change (((-1 : ℝ) ≤ p.1 ∧ p.1 ≤ 1) ∧
        (-1 ≤ p.2 ∧ p.2 ≤ 1)) ↔
      ((-1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1) ∨
        (-1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1))
    constructor
    · intro hp
      rcases le_or_gt p.2 p.1 with hle | hlt
      · exact Or.inl ⟨hp.2.1, hle, hp.1.2⟩
      · exact Or.inr ⟨hp.1.1, hlt, hp.2.2⟩
    · rintro (hp | hp)
      · exact ⟨⟨by linarith [hp.1, hp.2.1], hp.2.2⟩,
          ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩⟩
      · exact ⟨⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩,
          ⟨by linarith [hp.1, hp.2.1], hp.2.2⟩⟩
  have hUpperLowerDisjoint :
      Disjoint centeredUpperTriangle lowerTriangle := by
    rw [Set.disjoint_left]
    intro p hpU hpL
    unfold centeredUpperTriangle at hpU
    dsimp only [lowerTriangle] at hpL
    linarith [hpU.2.1, hpL.2.1]
  have hSquareHalf :
      (∫ p : ℝ × ℝ in centeredUpperTriangle, K p) =
        (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, K p) / 2 := by
    have hsplit := setIntegral_union hUpperLowerDisjoint hLowerMeas
      hKUpper hKLower
    rw [← hSquareUnion] at hsplit
    rw [Measure.volume_eq_prod ℝ ℝ] at hLowerEqOpenUpper hOpenUpperEqUpper
    rw [hLowerEqOpenUpper, ← hOpenUpperEqUpper] at hsplit
    rw [Measure.volume_eq_prod ℝ ℝ]
    linarith
  have hShearFold :
      (∫ p : ℝ × ℝ in positiveDistanceTriangle, H p) =
        ∫ p : ℝ × ℝ in centeredUpperTriangle, K p := by
    simpa only [H] using setIntegral_positiveDistanceTriangle_shear K
  have hRawSet : centeredRawLogEnergy w =
      ∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, K p := by
    unfold centeredRawLogEnergy
    simpa only [K] using
      intervalIntegral_integral_eq_setIntegral_centeredSquare K hKSquare
  unfold PositiveDistanceTriangleInterchange
  calc
    centeredPositiveTriangleEnergy w =
        ∫ p : ℝ × ℝ in positiveDistanceTriangle, H p := hTriangleFold
    _ = ∫ p : ℝ × ℝ in centeredUpperTriangle, K p := hShearFold
    _ = (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, K p) / 2 :=
      hSquareHalf
    _ = centeredRawLogEnergy w / 2 := by rw [hRawSet]

/-- The outer positive-distance quotient is interval integrable under the
same Lipschitz hypothesis.  The `t = 0` row is removed explicitly almost
everywhere rather than assigned a singular value. -/
theorem intervalIntegrable_centeredPositiveDistanceEnergy_div_of_lipschitzOnWith
    {C : NNReal} (w : ℝ → ℝ)
    (hw : LipschitzOnWith C w (Icc (-1) 1)) :
    IntervalIntegrable
      (fun t : ℝ ↦ centeredPositiveDistanceEnergy w t / t)
      volume 0 2 := by
  let H : ℝ × ℝ → ℝ := fun p ↦
    centeredLogDifferenceKernel w (p.1 + p.2) p.2
  have hTriangleMeas : MeasurableSet positiveDistanceTriangle := by
    unfold positiveDistanceTriangle
    measurability
  have hHOn : IntegrableOn H positiveDistanceTriangle
      ((volume : Measure ℝ).prod volume) := by
    simpa only [H] using
      integrableOn_centeredPositiveTriangleKernel_of_lipschitzOnWith w hw
  have hHIndicator : Integrable (positiveDistanceTriangle.indicator H)
      ((volume : Measure ℝ).prod volume) :=
    hHOn.integrable_indicator hTriangleMeas
  have hrow (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 2) :
      (∫ x : ℝ, positiveDistanceTriangle.indicator H (t, x)) =
        centeredPositiveDistanceEnergy w t / t := by
    calc
      (∫ x : ℝ, positiveDistanceTriangle.indicator H (t, x)) =
          ∫ x : ℝ, (Icc (-1 : ℝ) (1 - t)).indicator
            (fun x ↦ centeredLogDifferenceKernel w (x + t) x) x := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ Icc (-1 : ℝ) (1 - t)
        · have hp : (t, x) ∈ positiveDistanceTriangle :=
            ⟨ht.1.le, ht.2, hx.1, hx.2⟩
          rw [Set.indicator_of_mem hp, Set.indicator_of_mem hx]
          dsimp only [H]
          rw [add_comm]
        · have hp : (t, x) ∉ positiveDistanceTriangle := by
            intro hp
            exact hx ⟨hp.2.2.1, hp.2.2.2⟩
          rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hx]
      _ = ∫ x : ℝ in Icc (-1 : ℝ) (1 - t),
          centeredLogDifferenceKernel w (x + t) x :=
        integral_indicator measurableSet_Icc
      _ = ∫ x : ℝ in -1..1 - t,
          centeredLogDifferenceKernel w (x + t) x := by
        rw [intervalIntegral.integral_of_le (by linarith [ht.2]),
          ← integral_Icc_eq_integral_Ioc]
      _ = centeredPositiveDistanceEnergy w t / t :=
        (positiveDistanceEnergy_div_eq_triangle_section w ht.1.le).symm
  have hiter := hHIndicator.integral_prod_left
  have houterIndicator : Integrable
      ((Ioc (0 : ℝ) 2).indicator
        (fun t : ℝ ↦ centeredPositiveDistanceEnergy w t / t)) := by
    apply hiter.congr
    filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with t ht0
    by_cases ht : t ∈ Ioc (0 : ℝ) 2
    · rw [Set.indicator_of_mem ht]
      exact hrow t ht
    · rw [Set.indicator_of_notMem ht]
      have hzero : (fun x : ℝ ↦
          positiveDistanceTriangle.indicator H (t, x)) = 0 := by
        funext x
        by_cases hp : (t, x) ∈ positiveDistanceTriangle
        · exfalso
          apply ht
          exact ⟨lt_of_le_of_ne hp.1 (Ne.symm ht0), hp.2.1⟩
        · rw [Set.indicator_of_notMem hp]
          rfl
      rw [hzero]
      simp
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  rw [← integrable_indicator_iff measurableSet_Ioc]
  exact houterIndicator

/-- The exact positive-distance fold required by
`integral_correlation_defect_div_eq_centered_energy_add_potential`. -/
theorem half_integral_positiveDistanceEnergy_eq_centeredRaw_of_lipschitzOnWith
    {C : NNReal} (w : ℝ → ℝ)
    (hw : LipschitzOnWith C w (Icc (-1) 1)) :
    (1 / 2 : ℝ) *
        (∫ t : ℝ in 0..2, centeredPositiveDistanceEnergy w t / t) =
      centeredRawLogEnergy w / 4 := by
  exact half_integral_positiveDistanceEnergy_eq_centeredRaw_of_interchange
    w (positiveDistanceTriangleInterchange_of_lipschitzOnWith w hw)

/-- Local Lipschitz regularity on the compact centered interval supplies the
global constant needed by the structural triangle fold. -/
theorem positiveDistanceTriangleInterchange_of_locallyLipschitzOn
    (w : ℝ → ℝ) (hw : LocallyLipschitzOn (Icc (-1) 1) w) :
    PositiveDistanceTriangleInterchange w := by
  obtain ⟨C, hC⟩ := hw.exists_lipschitzOnWith_of_compact isCompact_Icc
  exact positiveDistanceTriangleInterchange_of_lipschitzOnWith w hC

/-- Local Lipschitz form of the outer integrability hypothesis used by the
singular-correlation theorem. -/
theorem intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
    (w : ℝ → ℝ) (hw : LocallyLipschitzOn (Icc (-1) 1) w) :
    IntervalIntegrable
      (fun t : ℝ ↦ centeredPositiveDistanceEnergy w t / t)
      volume 0 2 := by
  obtain ⟨C, hC⟩ := hw.exists_lipschitzOnWith_of_compact isCompact_Icc
  exact intervalIntegrable_centeredPositiveDistanceEnergy_div_of_lipschitzOnWith
    w hC

/-- Local Lipschitz form of the exact positive-distance fold. -/
theorem half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
    (w : ℝ → ℝ) (hw : LocallyLipschitzOn (Icc (-1) 1) w) :
    (1 / 2 : ℝ) *
        (∫ t : ℝ in 0..2, centeredPositiveDistanceEnergy w t / t) =
      centeredRawLogEnergy w / 4 := by
  obtain ⟨C, hC⟩ := hw.exists_lipschitzOnWith_of_compact isCompact_Icc
  exact half_integral_positiveDistanceEnergy_eq_centeredRaw_of_lipschitzOnWith
    w hC

end

end ArithmeticHodge.Analysis.YoshidaEndpointTriangleFoldLipschitz
