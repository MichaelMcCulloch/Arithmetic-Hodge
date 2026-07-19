import ArithmeticHodge.Analysis.YoshidaEndpointEvenCleanPositive
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowPotential
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowProfile
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowHyperbolic
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCarleman
import ArithmeticHodge.Analysis.YoshidaFourCellCompletedParityOperatorStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenCapacityStructural
import ArithmeticHodge.Analysis.YoshidaFourCellWidthPerturbationStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenCapacityClosureStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaConstantBounds
open YoshidaEndpointEvenCleanPositive
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenP2LogEnergy
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFourCellEvenCapacityStructural
open YoshidaFourCellCompletedParityOperatorStructural
open YoshidaFourCellEndpointHalfFoldStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRegularKernelSquareStructural
open YoshidaFourCellWidthPerturbationStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaRegularKernelBound
open YoshidaRegularKernelLowerBound

/-!
# Closure of the even four-cell endpoint capacity

The target is the sharp universal nonnegativity of the post-prime operator.
We keep the clean endpoint form and the full coupled width/prime perturbation
together; neither signed perturbation is discarded termwise.
-/

/-- Exact reduction of the even four-cell bracket to clean coercivity plus
the coupled width/prime perturbation. -/
theorem fourCell_evenBracket_eq_clean_add_widthPrime
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w =
      yoshidaEndpointOddCleanQuadratic w +
        fourCellWidthPrimePerturbation w := by
  simpa only [fourCellOperatorHalfWidth] using
    fourCell_centeredPhysical_sub_pairing_eq_clean_add_perturbation w hw

/-- On the even form domain the post-prime operator is exactly the physical
four-cell quadratic with `99/100` of each reflected strip potential removed.
This identity is useful for adversarial testing: it contains no estimated
prime term. -/
theorem fourCellEvenPostPrimeLowerOperator_eq_physical_sub_strip
    (w : ℝ → ℝ) (hw : Continuous w)
    (heven : Function.Even w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w) :
    fourCellEvenPostPrimeLowerOperator w =
      centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
        (99 / 50 : ℝ) *
          (∫ x : ℝ in 3 / 5..1,
            yoshidaEndpointPotential x * w x ^ 2) := by
  have hbracket := fourCellBracket_eq_evenParityOperator w hw hlocal heven
  have hcompleted := fourCellEvenParityOperator_eq_completed w hw heven
  have hprime := neg_primePairing_eq_halfAntimatched_sub_mass_of_even
    w hw heven
  rw [hcompleted] at hbracket
  unfold fourCellEvenCompletedParityOperator at hbracket
  unfold fourCellEvenPostPrimeLowerOperator
  linear_combination -hbracket + hprime

/-- A coupled lower bound of the width/prime perturbation by the clean
endpoint reserve closes the exact even four-cell bracket. -/
theorem fourCell_evenBracket_nonnegative_of_widthPrime_bound
    (w : ℝ → ℝ) (hw : Continuous w)
    (hperturb :
      -yoshidaEndpointOddCleanQuadratic w ≤
        fourCellWidthPrimePerturbation w) :
    0 ≤ centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  rw [fourCell_evenBracket_eq_clean_add_widthPrime w hw]
  linarith

/-! ## A structural counterexample to the universal post-prime target -/

private theorem centeredEvenP2_continuous : Continuous centeredEvenP2 := by
  unfold centeredEvenP2
  fun_prop

private theorem centeredEvenP2_even : Function.Even centeredEvenP2 := by
  intro x
  unfold centeredEvenP2
  ring

private theorem centeredEvenP2_locallyLipschitzOn :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) centeredEvenP2 := by
  have hdiff : ContDiff ℝ 1 centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  exact hdiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)

private theorem centeredEndpointCorrelation_centeredEvenP2 (t : ℝ) :
    centeredEndpointCorrelation centeredEvenP2 t =
      -(t - 2) *
        (3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40 := by
  have h := centeredEndpointCorrelation_evenStructuralProfile 0 1 t
  have hp : factorTwoEvenStructuralLowProfile 0 1 = centeredEvenP2 := by
    funext x
    unfold factorTwoEvenStructuralLowProfile centeredEvenP0
    ring
  rw [hp] at h
  norm_num [evenStructuralCorrelation22] at h ⊢
  exact h

private theorem centeredEndpointCorrelation_centeredEvenP2_continuous :
    Continuous (centeredEndpointCorrelation centeredEvenP2) := by
  rw [show centeredEndpointCorrelation centeredEvenP2 = fun t : ℝ ↦
      -(t - 2) *
        (3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40 by
    funext t
    exact centeredEndpointCorrelation_centeredEvenP2 t]
  fun_prop

private theorem centeredEndpointCorrelation_centeredEvenP2_nonneg_tail
    {t : ℝ} (ht : t ∈ Icc (8 / 5 : ℝ) 2) :
    0 ≤ centeredEndpointCorrelation centeredEvenP2 t := by
  let u : ℝ := 2 - t
  let v : ℝ := (5 / 2) * u
  have hu0 : 0 ≤ u := by dsimp only [u]; linarith [ht.2]
  have hu1 : u ≤ 2 / 5 := by dsimp only [u]; linarith [ht.1]
  have hv0 : 0 ≤ v := mul_nonneg (by norm_num) hu0
  have hv1 : v ≤ 1 := by dsimp only [v]; nlinarith
  have hvcomp : 0 ≤ 1 - v := sub_nonneg.mpr hv1
  have hpoly :
      0 ≤ 3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8 := by
    have h0 : 0 ≤ 40 * (1 - v) ^ 4 := by positivity
    have h1 : 0 ≤ 4 * 28 * v * (1 - v) ^ 3 := by positivity
    have h2 : 0 ≤
        6 * (56 / 3 : ℝ) * v ^ 2 * (1 - v) ^ 2 := by positivity
    have h3 : 0 ≤
        4 * (288 / 25 : ℝ) * v ^ 3 * (1 - v) := by positivity
    have h4 : 0 ≤ (3848 / 625 : ℝ) * v ^ 4 := by positivity
    rw [show 3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8 =
        40 * (1 - v) ^ 4 +
          4 * 28 * v * (1 - v) ^ 3 +
          6 * (56 / 3 : ℝ) * v ^ 2 * (1 - v) ^ 2 +
          4 * (288 / 25 : ℝ) * v ^ 3 * (1 - v) +
          (3848 / 625 : ℝ) * v ^ 4 by
      dsimp only [u, v]
      ring]
    positivity
  rw [centeredEndpointCorrelation_centeredEvenP2]
  exact div_nonneg (mul_nonneg (by linarith [ht.2]) hpoly) (by norm_num)

private theorem intervalIntegrable_fourCellKernel_mul_centeredEvenP2Correlation :
    IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation centeredEvenP2 t)
      volume 0 2 := by
  let C : ℝ → ℝ := centeredEndpointCorrelation centeredEvenP2
  let f : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 4 : ℝ) * |C t|
  have hC : Continuous C := centeredEndpointCorrelation_centeredEvenP2_continuous
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact (measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1.le
    have harg :
        fourCellOperatorHalfWidth * t ≤ 5 * Real.log 2 / 4 := by
      unfold fourCellOperatorHalfWidth
      have := mul_le_mul_of_nonneg_left ht.2
        (by positivity : 0 ≤ 5 * Real.log 2 / 8)
      linarith
    have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg
    have hk1 := yoshidaRegularKernel_le_quarter harg0
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
    exact mul_le_mul_of_nonneg_right hk1 (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

/-- A one-dimensional structural lower bound for the smooth regular
quadratic on `P₂`.  On lags at most `8/5` the kernel lies within `1/64`
of `15/64`; on the remaining lags the `P₂` autocorrelation is nonnegative.
-/
private theorem fourCellRegularFullSquare_centeredEvenP2_lower :
    (-7 / 250 : ℝ) ≤ fourCellRegularFullSquare centeredEvenP2 := by
  let C : ℝ → ℝ := centeredEndpointCorrelation centeredEvenP2
  let K : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t)
  let E : ℝ → ℝ := fun t ↦ (K t - 15 / 64) * C t
  have hC : Continuous C := centeredEndpointCorrelation_centeredEvenP2_continuous
  have hKfull : IntervalIntegrable (fun t ↦ K t * C t) volume 0 2 := by
    simpa only [K, C] using
      intervalIntegrable_fourCellKernel_mul_centeredEvenP2Correlation
  have hsubset : uIcc (0 : ℝ) (8 / 5) ⊆ uIcc (0 : ℝ) 2 := by
    norm_num
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hKnear : IntervalIntegrable (fun t ↦ K t * C t)
      volume 0 (8 / 5) := hKfull.mono_set hsubset
  have hCnearInt : IntervalIntegrable C volume 0 (8 / 5) :=
    hC.intervalIntegrable _ _
  have hEint : IntervalIntegrable E volume 0 (8 / 5) := by
    dsimp only [E]
    have hconst : IntervalIntegrable (fun t ↦ (15 / 64 : ℝ) * C t)
        volume 0 (8 / 5) := hCnearInt.const_mul (15 / 64)
    convert hKnear.sub hconst using 1
    funext t
    dsimp only
    ring
  have hpointError {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (8 / 5)) :
      -(1 / 64 : ℝ) * |C t| ≤ E t := by
    have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
      unfold fourCellOperatorHalfWidth
      positivity
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg ha0 ht.1
    have harg2 : fourCellOperatorHalfWidth * t ≤ Real.log 2 := by
      unfold fourCellOperatorHalfWidth
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by positivity : 0 ≤ 5 * Real.log 2 / 8)
      nlinarith
    have hlo := seven_div_thirty_two_le_yoshidaRegularKernel harg0 harg2
    have hhi := yoshidaRegularKernel_le_quarter harg0
    have herr :
        |yoshidaRegularKernel (fourCellOperatorHalfWidth * t) - 15 / 64| ≤
          (1 / 64 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith
    dsimp only [E, K]
    by_cases hCt : 0 ≤ C t
    · rw [abs_of_nonneg hCt]
      have he := (abs_le.mp herr).1
      nlinarith
    · have hCt' : C t ≤ 0 := le_of_not_ge hCt
      rw [abs_of_nonpos hCt']
      have he := (abs_le.mp herr).2
      nlinarith
  have habsNearInt : IntervalIntegrable (fun t ↦ |C t|)
      volume 0 (8 / 5) := hC.abs.intervalIntegrable _ _
  have herrorLower :
      -(1 / 64 : ℝ) * (∫ t : ℝ in 0..8 / 5, |C t|) ≤
        ∫ t : ℝ in 0..8 / 5, E t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num)
      (habsNearInt.const_mul (-(1 / 64 : ℝ))) hEint
    intro t ht
    exact hpointError ht
  have habsFarInt : IntervalIntegrable (fun t ↦ |C t|)
      volume (8 / 5) 2 := hC.abs.intervalIntegrable _ _
  have habsFarNonneg :
      0 ≤ ∫ t : ℝ in 8 / 5..2, |C t| := by
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ abs_nonneg _)
  have habsTotal :=
    integral_abs_centeredEndpointCorrelation_le_energy
      centeredEvenP2 centeredEvenP2_continuous
  have habsSplit := intervalIntegral.integral_add_adjacent_intervals
    habsNearInt habsFarInt
  have hmass : (∫ x : ℝ in -1..1, centeredEvenP2 x ^ 2) = 2 / 5 := by
    exact integral_centeredEvenP2_sq
  have habsNear : (∫ t : ℝ in 0..8 / 5, |C t|) ≤ 2 / 5 := by
    dsimp only [C] at habsTotal habsSplit ⊢
    rw [hmass] at habsTotal
    linarith
  have herror : (-1 / 160 : ℝ) ≤ ∫ t : ℝ in 0..8 / 5, E t := by
    nlinarith [herrorLower]
  have hCnear : (∫ t : ℝ in 0..8 / 5, C t) = -2384 / 78125 := by
    rw [show C = fun t : ℝ ↦
        -(t - 2) *
          (3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40 by
      funext t
      exact centeredEndpointCorrelation_centeredEvenP2 t]
    let F : ℝ → ℝ := fun t ↦
      -t ^ 6 / 80 + t ^ 4 / 8 - t ^ 2 / 2 + 2 * t / 5
    have hderiv (t : ℝ) : HasDerivAt F
        (-(t - 2) *
          (3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40) t := by
      dsimp only [F]
      convert (((((hasDerivAt_id t).pow 6).neg.div_const 80).add
        (((hasDerivAt_id t).pow 4).div_const 8)).sub
          (((hasDerivAt_id t).pow 2).div_const 2)).add
            (((hasDerivAt_id t).const_mul 2).div_const 5) using 1
      simp only [id_eq, Nat.cast_ofNat]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ht ↦ hderiv t)
      ((by fun_prop : Continuous (fun t : ℝ ↦
        -(t - 2) *
          (3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40))
        |>.intervalIntegrable 0 (8 / 5))]
    norm_num [F]
  have hnearDecomp :
      (∫ t : ℝ in 0..8 / 5, K t * C t) =
        (15 / 64 : ℝ) * (∫ t : ℝ in 0..8 / 5, C t) +
          ∫ t : ℝ in 0..8 / 5, E t := by
    have hconst := hCnearInt.const_mul (15 / 64 : ℝ)
    calc
      (∫ t : ℝ in 0..8 / 5, K t * C t) =
          ∫ t : ℝ in 0..8 / 5, (15 / 64 : ℝ) * C t + E t := by
        apply intervalIntegral.integral_congr
        intro t _ht
        dsimp only [E]
        ring
      _ = (∫ t : ℝ in 0..8 / 5, (15 / 64 : ℝ) * C t) +
          ∫ t : ℝ in 0..8 / 5, E t :=
        intervalIntegral.integral_add hconst hEint
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have hnear : (-27 / 2000 : ℝ) ≤
      ∫ t : ℝ in 0..8 / 5, K t * C t := by
    rw [hnearDecomp, hCnear]
    nlinarith
  have hKfar : IntervalIntegrable (fun t ↦ K t * C t)
      volume (8 / 5) 2 := by
    exact hKfull.mono_set (by
      norm_num
      intro x hx
      constructor <;> linarith [hx.1, hx.2])
  have hfar : 0 ≤ ∫ t : ℝ in 8 / 5..2, K t * C t := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t := by
      exact mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity)
        (by linarith [ht.1])
    have harg : fourCellOperatorHalfWidth * t ≤ 5 * Real.log 2 / 4 := by
      unfold fourCellOperatorHalfWidth
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by positivity : 0 ≤ 5 * Real.log 2 / 8)
      linarith
    exact mul_nonneg
      (yoshidaRegularKernel_nonneg_fourCellRange harg0 harg)
      (centeredEndpointCorrelation_centeredEvenP2_nonneg_tail ht)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hKnear hKfar
  have hI : (-27 / 2000 : ℝ) ≤
      ∫ t : ℝ in 0..2, K t * C t := by
    linarith
  have hfull :=
    two_mul_integral_yoshidaRegularKernel_mul_centeredCorrelation_eq_fullSquare
      centeredEvenP2 centeredEvenP2_continuous fourCellOperatorHalfWidth
      (by unfold fourCellOperatorHalfWidth; positivity)
      (by
        have h := five_mul_log_two_div_four_lt_log_three
        unfold fourCellOperatorHalfWidth
        linarith)
  change 2 * (∫ t : ℝ in 0..2, K t * C t) =
    fourCellRegularFullSquare centeredEvenP2 at hfull
  rw [← hfull]
  nlinarith

private theorem endpointPotential_le_twentyFive_div_thirtyTwo_mul_sq
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (3 / 5)) :
    yoshidaEndpointPotential x ≤ (25 / 32 : ℝ) * x ^ 2 := by
  have hxSq0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hxSq : x ^ 2 ≤ 9 / 25 := by nlinarith [hx.1, hx.2]
  have hden : 0 < 1 - x ^ 2 := by nlinarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hden)
  rw [Real.log_inv] at hlog
  have hinv : (1 - x ^ 2)⁻¹ - 1 = x ^ 2 / (1 - x ^ 2) := by
    field_simp [hden.ne']
    ring
  rw [hinv] at hlog
  have hfrac : x ^ 2 / (1 - x ^ 2) ≤ (25 / 16 : ℝ) * x ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith
  unfold yoshidaEndpointPotential
  nlinarith

private theorem endpointPotential_centeredEvenP2_low_upper :
    (∫ x : ℝ in 0..3 / 5,
      yoshidaEndpointPotential x * centeredEvenP2 x ^ 2) ≤
        (2007 / 700000 : ℝ) := by
  let f : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * centeredEvenP2 x ^ 2
  let g : ℝ → ℝ := fun x ↦
    (25 / 32 : ℝ) * x ^ 2 * centeredEvenP2 x ^ 2
  have hfull := intervalIntegrable_endpointPotential_mul_sq
    centeredEvenP2 centeredEvenP2_continuous
  have hsub : uIcc (0 : ℝ) (3 / 5) ⊆ uIcc (-1 : ℝ) 1 := by
    norm_num
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hf : IntervalIntegrable f volume 0 (3 / 5) := by
    dsimp only [f]
    exact hfull.mono_set hsub
  have hg : IntervalIntegrable g volume 0 (3 / 5) := by
    dsimp only [g]
    apply Continuous.intervalIntegrable
    unfold centeredEvenP2
    fun_prop
  have hmono : (∫ x : ℝ in 0..3 / 5, f x) ≤
      ∫ x : ℝ in 0..3 / 5, g x := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf hg
    intro x hx
    dsimp only [f, g]
    exact mul_le_mul_of_nonneg_right
      (endpointPotential_le_twentyFive_div_thirtyTwo_mul_sq hx)
      (sq_nonneg _)
  have hgValue : (∫ x : ℝ in 0..3 / 5, g x) =
      (2007 / 700000 : ℝ) := by
    let F : ℝ → ℝ := fun x ↦
      225 * x ^ 7 / 896 - 15 * x ^ 5 / 64 + 25 * x ^ 3 / 384
    have hderiv (x : ℝ) : HasDerivAt F (g x) x := by
      dsimp only [F, g]
      unfold centeredEvenP2
      convert (((((hasDerivAt_id x).pow 7).const_mul 225).div_const 896).sub
        ((((hasDerivAt_id x).pow 5).const_mul 15).div_const 64)).add
          ((((hasDerivAt_id x).pow 3).const_mul 25).div_const 384) using 1
      simp only [id_eq, Nat.cast_ofNat]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _hx ↦ hderiv x) hg]
    norm_num [F]
  dsimp only [f] at hmono ⊢
  rw [hgValue] at hmono
  exact hmono

/-- The strip charge on `P₂` has a rational lower bound.  It comes from
the exact full endpoint-potential moment and a structural logarithmic upper
bound on the short interval `[0,3/5]`. -/
private theorem endpointStripPotential_centeredEvenP2_lower :
    (1317 / 10000 : ℝ) <
      ∫ x : ℝ in 3 / 5..1,
        yoshidaEndpointPotential x * centeredEvenP2 x ^ 2 := by
  let f : ℝ → ℝ := fun x ↦
    yoshidaEndpointPotential x * centeredEvenP2 x ^ 2
  have hfull := intervalIntegrable_endpointPotential_mul_sq
    centeredEvenP2 centeredEvenP2_continuous
  have hpos : IntervalIntegrable f volume 0 1 := by
    dsimp only [f]
    exact hfull.mono_set (by
      norm_num
      intro x hx
      constructor <;> linarith [hx.1, hx.2])
  have hlow : IntervalIntegrable f volume 0 (3 / 5) := by
    exact hpos.mono_set (by
      norm_num
      intro x hx
      constructor <;> linarith [hx.1, hx.2])
  have hstrip : IntervalIntegrable f volume (3 / 5) 1 := by
    exact hpos.mono_set (by
      norm_num
      intro x hx
      constructor <;> linarith [hx.1, hx.2])
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hlow hstrip
  have hhalfFold := endpointPotential_eq_two_mul_positiveHalf
    centeredEvenP2 centeredEvenP2_continuous (Or.inl centeredEvenP2_even)
  have hhalf : (∫ x : ℝ in 0..1, f x) =
      41 / 150 - (1 / 5 : ℝ) * Real.log 2 := by
    dsimp only [f]
    rw [integral_endpointPotential_mul_centeredEvenP2_sq] at hhalfFold
    linarith
  have hlowUpper := endpointPotential_centeredEvenP2_low_upper
  have hlog := strict_log_two_bounds.2
  dsimp only [f] at hsplit hhalf
  rw [hhalf] at hsplit
  nlinarith

private theorem cosh_sub_one_le_sq_of_abs_le_one
    {z : ℝ} (hz : |z| ≤ 1) :
    Real.cosh z - 1 ≤ z ^ 2 := by
  have hzSq0 : 0 ≤ z ^ 2 := sq_nonneg z
  have hzSq : z ^ 2 ≤ 1 := by
    have hpow := pow_le_pow_left₀ (abs_nonneg z) hz 2
    simpa only [sq_abs, one_pow] using hpow
  let u : ℝ := z ^ 2 / 2
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hu1 : u < 1 := by dsimp only [u]; nlinarith
  have hexp := Real.exp_bound_div_one_sub_of_interval hu0 hu1
  have hfrac : 1 / (1 - u) - 1 ≤ z ^ 2 := by
    have hden : 0 < 1 - u := sub_pos.mpr hu1
    rw [show 1 / (1 - u) - 1 = u / (1 - u) by
      field_simp [hden.ne']
      ring]
    rw [div_le_iff₀ hden]
    dsimp only [u]
    nlinarith
  have hcosh := Real.cosh_le_exp_half_sq z
  change Real.cosh z ≤ Real.exp u at hcosh
  linarith

private theorem centeredCoshMoment_centeredEvenP2_sq_lt :
    centeredCoshMoment centeredEvenP2
        (fourCellOperatorHalfWidth / 2) ^ 2 < 1 / 1000 := by
  let lambda : ℝ := fourCellOperatorHalfWidth / 2
  let q : ℝ → ℝ := fun x ↦
    (Real.cosh (lambda * x) - 1) * centeredEvenP2 x
  have hlambda0 : 0 ≤ lambda := by
    dsimp only [lambda]
    unfold fourCellOperatorHalfWidth
    positivity
  have hlambda : lambda < 217 / 1000 := by
    have hlog := strict_log_two_bounds.2
    dsimp only [lambda]
    unfold fourCellOperatorHalfWidth
    nlinarith
  have hmean : (∫ x : ℝ in -1..1, centeredEvenP2 x) = 0 := by
    simpa only [centeredEvenP0, one_mul] using integral_centeredEvenP0_mul_p2
  have hq : IntervalIntegrable q volume (-1) 1 := by
    dsimp only [q, lambda]
    apply Continuous.intervalIntegrable
    unfold centeredEvenP2
    fun_prop
  have hp : IntervalIntegrable centeredEvenP2 volume (-1) 1 :=
    centeredEvenP2_continuous.intervalIntegrable _ _
  have hmoment : centeredCoshMoment centeredEvenP2 lambda =
      ∫ x : ℝ in -1..1, q x := by
    unfold centeredCoshMoment
    rw [show (fun x : ℝ ↦ Real.cosh (lambda * x) * centeredEvenP2 x) =
        fun x ↦ q x + centeredEvenP2 x by
      funext x
      dsimp only [q]
      ring,
      intervalIntegral.integral_add hq hp, hmean, add_zero]
  have hqabs : IntervalIntegrable (fun x ↦ |q x|) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [q]
    unfold centeredEvenP2
    fun_prop
  have hsqInt : IntervalIntegrable (fun x : ℝ ↦ lambda ^ 2 * x ^ 2)
      volume (-1) 1 := (by fun_prop : Continuous
        (fun x : ℝ ↦ lambda ^ 2 * x ^ 2)).intervalIntegrable _ _
  have hpoint {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
      |q x| ≤ lambda ^ 2 * x ^ 2 := by
    have hxAbs : |x| ≤ 1 := abs_le.mpr hx
    have hlambdaLe : lambda ≤ 1 := hlambda.le.trans (by norm_num)
    have hzAbs : |lambda * x| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hlambda0]
      calc
        lambda * |x| ≤ lambda * 1 :=
          mul_le_mul_of_nonneg_left hxAbs hlambda0
        _ ≤ 1 := by simpa only [mul_one] using hlambdaLe
    have hcosh0 : 0 ≤ Real.cosh (lambda * x) - 1 :=
      sub_nonneg.mpr (Real.one_le_cosh _)
    have hcosh := cosh_sub_one_le_sq_of_abs_le_one hzAbs
    have hxSq : x ^ 2 ≤ 1 := by
      have hpow := pow_le_pow_left₀ (abs_nonneg x) hxAbs 2
      simpa only [sq_abs, one_pow] using hpow
    have hpAbs : |centeredEvenP2 x| ≤ 1 := by
      unfold centeredEvenP2
      rw [abs_le]
      constructor <;> nlinarith
    dsimp only [q]
    rw [abs_mul, abs_of_nonneg hcosh0]
    have hmul := mul_le_mul hcosh hpAbs (abs_nonneg _)
      (sq_nonneg (lambda * x))
    simpa only [one_mul, mul_one, mul_pow] using hmul
  have habsIntegral :
      |∫ x : ℝ in -1..1, q x| ≤
        ∫ x : ℝ in -1..1, |q x| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have hmono : (∫ x : ℝ in -1..1, |q x|) ≤
      ∫ x : ℝ in -1..1, lambda ^ 2 * x ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num) hqabs hsqInt
    intro x hx
    exact hpoint hx
  have hpoly : (∫ x : ℝ in -1..1, lambda ^ 2 * x ^ 2) =
      (2 / 3 : ℝ) * lambda ^ 2 := by
    rw [intervalIntegral.integral_const_mul]
    norm_num
    ring
  have habsMoment : |centeredCoshMoment centeredEvenP2 lambda| ≤
      (2 / 3 : ℝ) * lambda ^ 2 := by
    rw [hmoment]
    rw [hpoly] at hmono
    exact habsIntegral.trans hmono
  have hbound0 : 0 ≤ (2 / 3 : ℝ) * lambda ^ 2 := by positivity
  have hsq := sq_le_sq₀ (abs_nonneg _) hbound0 |>.2 habsMoment
  rw [sq_abs] at hsq
  have hrational : ((2 / 3 : ℝ) * (217 / 1000) ^ 2) ^ 2 <
      (1 / 1000 : ℝ) := by norm_num
  have hlambdaSq : lambda ^ 2 < (217 / 1000 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg lambda, sq_nonneg (217 / 1000 : ℝ)]
  have hupper : ((2 / 3 : ℝ) * lambda ^ 2) ^ 2 < 1 / 1000 := by
    nlinarith
  simpa only [lambda] using hsq.trans_lt hupper

private theorem physicalPolar_centeredEvenP2_lt_one_thousandth :
    2 * fourCellOperatorHalfWidth *
        (∫ x : ℝ in -1..1,
          Real.exp (-fourCellOperatorHalfWidth * x / 2) * centeredEvenP2 x) *
        (∫ x : ℝ in -1..1,
          Real.exp (fourCellOperatorHalfWidth * x / 2) * centeredEvenP2 x) <
      (1 / 1000 : ℝ) := by
  have hpolar := centeredPolarMoments_mul_eq_cosh_sq_sub_sinh_sq
    centeredEvenP2 centeredEvenP2_continuous fourCellOperatorHalfWidth
  rw [centeredSinhMoment_eq_zero_of_even centeredEvenP2_even] at hpolar
  norm_num at hpolar
  have hneg :
      (∫ x : ℝ in -1..1,
        Real.exp (-fourCellOperatorHalfWidth * x / 2) * centeredEvenP2 x) =
      ∫ x : ℝ in -1..1,
        Real.exp (-(fourCellOperatorHalfWidth * x) / 2) * centeredEvenP2 x := by
    apply intervalIntegral.integral_congr
    intro x _hx
    change Real.exp (-fourCellOperatorHalfWidth * x / 2) * centeredEvenP2 x =
      Real.exp (-(fourCellOperatorHalfWidth * x) / 2) * centeredEvenP2 x
    rw [show -fourCellOperatorHalfWidth * x / 2 =
        -(fourCellOperatorHalfWidth * x) / 2 by ring]
  rw [hneg]
  rw [show 2 * fourCellOperatorHalfWidth *
        (∫ x : ℝ in -1..1,
          Real.exp (-(fourCellOperatorHalfWidth * x) / 2) * centeredEvenP2 x) *
        (∫ x : ℝ in -1..1,
          Real.exp (fourCellOperatorHalfWidth * x / 2) * centeredEvenP2 x) =
      2 * fourCellOperatorHalfWidth *
        ((∫ x : ℝ in -1..1,
          Real.exp (-(fourCellOperatorHalfWidth * x) / 2) * centeredEvenP2 x) *
        (∫ x : ℝ in -1..1,
          Real.exp (fourCellOperatorHalfWidth * x / 2) * centeredEvenP2 x)) by
      ring,
    hpolar]
  have hC := centeredCoshMoment_centeredEvenP2_sq_lt
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha : fourCellOperatorHalfWidth < 217 / 500 := by
    have hlog := strict_log_two_bounds.2
    unfold fourCellOperatorHalfWidth
    nlinarith
  have hCsq0 : 0 ≤ centeredCoshMoment centeredEvenP2
      (fourCellOperatorHalfWidth / 2) ^ 2 := sq_nonneg _
  nlinarith

private theorem log_five_four_gt_2231_div_10000 :
    (2231 / 10000 : ℝ) < Real.log (5 / 4 : ℝ) := by
  have h := Real.sum_range_le_log_div (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem fourCellScalar_gt_15783_div_10000 :
    (15783 / 10000 : ℝ) <
      Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hwidth :
      Real.log (2 * fourCellOperatorHalfWidth) =
        Real.log (5 / 4 : ℝ) + Real.log (Real.log 2) := by
    rw [show 2 * fourCellOperatorHalfWidth =
        (5 / 4 : ℝ) * Real.log 2 by
      unfold fourCellOperatorHalfWidth
      ring,
      Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  rw [hwidth]
  have hfive := log_five_four_gt_2231_div_10000
  have hloglog := strict_log_log_two_bounds.1
  have hgamma := strict_euler_gamma_bounds.1
  have hpi := strict_log_pi_bounds.1
  linarith

private theorem regularTerm_centeredEvenP2_lt_61_div_5000 :
    -2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation centeredEvenP2 t) <
      (61 / 5000 : ℝ) := by
  have hfull :=
    two_mul_integral_yoshidaRegularKernel_mul_centeredCorrelation_eq_fullSquare
      centeredEvenP2 centeredEvenP2_continuous fourCellOperatorHalfWidth
      (by unfold fourCellOperatorHalfWidth; positivity)
      (by
        have h := five_mul_log_two_div_four_lt_log_three
        unfold fourCellOperatorHalfWidth
        linarith)
  have hlower := fourCellRegularFullSquare_centeredEvenP2_lower
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha : fourCellOperatorHalfWidth < 217 / 500 := by
    have hlog := strict_log_two_bounds.2
    unfold fourCellOperatorHalfWidth
    nlinarith
  change 2 *
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation centeredEvenP2 t) =
    fourCellRegularFullSquare centeredEvenP2 at hfull
  nlinarith

/-- The universal even post-prime lower operator is false already on the
centered quadratic Legendre mode.  This is a kernel-checked analytic
counterexample, not a floating-point certificate. -/
theorem fourCellEvenPostPrimeLowerOperator_centeredEvenP2_neg :
    fourCellEvenPostPrimeLowerOperator centeredEvenP2 < 0 := by
  have hpost :=
    fourCellEvenPostPrimeLowerOperator_eq_physical_sub_strip
      centeredEvenP2 centeredEvenP2_continuous centeredEvenP2_even
        centeredEvenP2_locallyLipschitzOn
  rw [hpost]
  unfold centeredClippedPhysicalQuadratic
  rw [centeredRawLogEnergy_centeredEvenP2,
    integral_endpointPotential_mul_centeredEvenP2_sq,
    integral_centeredEvenP2_sq]
  have hscalar := fourCellScalar_gt_15783_div_10000
  have hregular := regularTerm_centeredEvenP2_lt_61_div_5000
  have hpolar := physicalPolar_centeredEvenP2_lt_one_thousandth
  have hstrip := endpointStripPotential_centeredEvenP2_lower
  have hlog := strict_log_two_bounds.1
  nlinarith

/-- Explicit refutation of universal post-prime nonnegativity on the stated
`ContDiff ℝ 1`, even domain. -/
theorem not_forall_even_contDiff_fourCellEvenPostPrimeLowerOperator_nonneg :
    ¬ (∀ w : ℝ → ℝ, ContDiff ℝ 1 w → Function.Even w →
        0 ≤ fourCellEvenPostPrimeLowerOperator w) := by
  intro h
  have hdiff : ContDiff ℝ 1 centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  have := h centeredEvenP2 hdiff centeredEvenP2_even
  linarith [fourCellEvenPostPrimeLowerOperator_centeredEvenP2_neg]

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenCapacityClosureStructural
