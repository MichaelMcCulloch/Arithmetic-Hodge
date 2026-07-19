import ArithmeticHodge.Analysis.YoshidaFactorTwoIntegrableLagRepresenterStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelSquareStructural

open CenteredEndpointCorrelation
open YoshidaEndpointTriangleInterchange
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaRegularKernelBound

noncomputable section

/-!
# Wide regular-kernel square

The removable Yoshida regular kernel is available as a bounded measurable
function, rather than through a global continuity theorem.  The lemmas below
therefore fill the two centered triangles using integrability and swap
symmetry only.  This gives the full-square form throughout the wider
four-cell range `0 <= a <= log 3 / 2`.
-/

/-- A swap-invariant integrable kernel fills the centered square from its
upper triangle.  No continuity at the diagonal is required. -/
private theorem two_mul_setIntegral_centeredUpperTriangle_eq_centeredSquare_of_integrable
    (K : ℝ × ℝ → ℝ)
    (hKSquare : IntegrableOn K
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume))
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
  have hUsub : U ⊆ S := by
    intro p hp
    dsimp only [U, S] at hp ⊢
    unfold centeredUpperTriangle at hp
    exact ⟨⟨by linarith [hp.1, hp.2.1], hp.2.2⟩,
      ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩⟩
  have hKUpper : IntegrableOn K U
      ((volume : Measure ℝ).prod volume) := by
    exact hKSquare.mono_set hUsub
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

/-- Fubini converts an integrable measurable kernel on the centered square to
the corresponding iterated interval integral. -/
private theorem setIntegral_centeredSquare_eq_iterated_of_integrable
    (K : ℝ × ℝ → ℝ)
    (hKSquare : IntegrableOn K
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ((volume : Measure ℝ).prod volume)) :
    (∫ p : ℝ × ℝ in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, K p) =
      ∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1, K (y, x) := by
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

/-- Throughout `0 <= a <= log 3 / 2`, the one-sided regular-kernel
autocorrelation is exactly half of the corresponding full centered-square
quadratic.  The proof uses only bounded measurability at the removable
diagonal singularity. -/
theorem two_mul_integral_yoshidaRegularKernel_mul_centeredCorrelation_eq_fullSquare
    (w : ℝ → ℝ) (hw : Continuous w) (a : ℝ)
    (ha0 : 0 ≤ a) (ha3 : a ≤ Real.log 3 / 2) :
    2 * (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (a * t) * centeredEndpointCorrelation w t) =
      ∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1,
        yoshidaRegularKernel (a * |y - x|) * w y * w x := by
  let q : ℝ → ℝ := fun t ↦ yoshidaRegularKernel (a * t)
  let K : ℝ × ℝ → ℝ := fun p ↦
    yoshidaRegularKernel (a * |p.1 - p.2|) * w p.1 * w p.2
  let S : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
  have hregularMeas : Measurable yoshidaRegularKernel := by
    unfold yoshidaRegularKernel
    apply Measurable.ite (measurableSet_singleton 0)
    · fun_prop
    · fun_prop
  have hqMeas : Measurable q := by
    dsimp only [q]
    exact hregularMeas.comp (measurable_const.mul measurable_id)
  have hqBound : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ (1 / 4 : ℝ) := by
    intro t ht
    have harg0 : 0 ≤ a * t := mul_nonneg ha0 ht.1
    have harg3 : a * t ≤ Real.log 3 := by
      have hat : a * t ≤ a * 2 := mul_le_mul_of_nonneg_left ht.2 ha0
      linarith
    have hnonneg := yoshidaRegularKernel_nonneg_of_le_log_three harg0 harg3
    rw [abs_of_nonneg hnonneg]
    exact yoshidaRegularKernel_le_quarter harg0
  have hUpper :
      (∫ t : ℝ in 0..2,
          q t * centeredEndpointCorrelation w t) =
        ∫ p : ℝ × ℝ in centeredUpperTriangle,
          factorTwoLagUpperDensity q w w p := by
    simpa only [factorTwoCenteredCrossCorrelation_self] using
      integral_weight_mul_crossCorrelation_eq_upperTriangle_of_bounded
        q w w hqMeas hw hw (1 / 4) hqBound
  have hKMeas : Measurable K := by
    dsimp only [K]
    exact ((hregularMeas.comp
      (measurable_const.mul ((measurable_fst.sub measurable_snd).abs))).mul
        (hw.measurable.comp measurable_fst)).mul
          (hw.measurable.comp measurable_snd)
  let g : ℝ × ℝ → ℝ := fun p ↦
    (1 / 4 : ℝ) * |w p.1| * |w p.2|
  have hgSquare : IntegrableOn g S
      ((volume : Measure ℝ).prod volume) := by
    apply ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
    exact ((continuous_const.mul (hw.comp continuous_fst).abs).mul
      (hw.comp continuous_snd).abs).continuousOn
  have hKSquare : IntegrableOn K S
      ((volume : Measure ℝ).prod volume) := by
    apply hgSquare.mono'
    · exact hKMeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem
          (measurableSet_Icc.prod measurableSet_Icc)] with p hp
      have hdiff : |p.1 - p.2| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
      have harg0 : 0 ≤ a * |p.1 - p.2| :=
        mul_nonneg ha0 (abs_nonneg _)
      have harg3 : a * |p.1 - p.2| ≤ Real.log 3 := by
        have hat := mul_le_mul_of_nonneg_left hdiff ha0
        linarith
      have hnonneg := yoshidaRegularKernel_nonneg_of_le_log_three harg0 harg3
      have hupper := yoshidaRegularKernel_le_quarter harg0
      dsimp only [K, g]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hnonneg]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hupper (abs_nonneg (w p.1)))
        (abs_nonneg (w p.2))
  have hKswap : ∀ p : ℝ × ℝ, K p.swap = K p := by
    intro p
    rcases p with ⟨y, x⟩
    dsimp only [K, Prod.swap_prod_mk]
    rw [show x - y = -(y - x) by ring, abs_neg]
    ring
  have hUpperK :
      (∫ p : ℝ × ℝ in centeredUpperTriangle,
          factorTwoLagUpperDensity q w w p) =
        ∫ p : ℝ × ℝ in centeredUpperTriangle, K p := by
    apply setIntegral_congr_fun (by
      unfold centeredUpperTriangle
      measurability)
    intro p hp
    have hdiff0 : 0 ≤ p.1 - p.2 := by
      unfold centeredUpperTriangle at hp
      linarith [hp.2.1]
    dsimp only [factorTwoLagUpperDensity, q, K]
    rw [abs_of_nonneg hdiff0]
  have hfill :=
    two_mul_setIntegral_centeredUpperTriangle_eq_centeredSquare_of_integrable
      K (by simpa only [S] using hKSquare) hKswap
  have hiter :=
    setIntegral_centeredSquare_eq_iterated_of_integrable K
      (by simpa only [S] using hKSquare)
  change 2 * (∫ t : ℝ in 0..2,
      q t * centeredEndpointCorrelation w t) = _
  rw [hUpper, hUpperK, hfill, hiter]

end

end ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelSquareStructural
