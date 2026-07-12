import ArithmeticHodge.Analysis.YoshidaClippedEvenMomentBridge
import ArithmeticHodge.Analysis.YoshidaCauchyPairing
import ArithmeticHodge.Analysis.YoshidaRenormalizedGeometricKernel

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ComplexConjugate Convolution

namespace ArithmeticHodge.Analysis.YoshidaEvenDistributionReduction

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCauchyPairing
open YoshidaClippedEvenMomentBridge
open YoshidaClippedMomentBridge
open YoshidaEvenIntervalCertificate
open YoshidaMomentIntegrability
open YoshidaOddGramPrefix
open YoshidaRenormalizedGeometricKernel

/-!
# Exact reduction of the clipped even distribution bridge

The clipped even modes have nonzero endpoint traces.  Consequently their
zero extensions are not continuous and their Fourier transforms have only
`O(1 / |v|)` decay.  This module deliberately does not reuse the stronger
odd-mode distribution interface, whose weighted `(1 + v^2)` hypothesis is
false in the even case.

Instead, the module proves the support, real-correlation, symmetry, and polar
parts of the even assembly directly.  The final bridge is reduced to the
single genuinely spectral statement identifying the normalized digamma
cross integral with its renormalized real-space geometric value.
-/

/-- The natural-frequency version of the production even low mode. -/
def clippedEvenUnifiedMode (n : ℕ) : YoshidaClippedSmooth yoshidaHalfLength :=
  if n = 0 then yoshidaClippedEvenZeroMode yoshidaHalfLength
  else yoshidaClippedEvenMode yoshidaHalfLength n

/-- The zero-extended function underlying `clippedEvenUnifiedMode`. -/
def evenModeFunction (n : ℕ) : ℝ → ℂ :=
  (clippedEvenUnifiedMode n : ℝ → ℂ)

/-- Real representative of the unified even mode on the clipping interval. -/
def clippedEvenUnifiedRealMode (n : ℕ) : ℝ → ℝ :=
  if n = 0 then clippedEvenZeroRealMode yoshidaHalfLength
  else clippedEvenRealMode yoshidaHalfLength n

theorem clippedEvenUnifiedMode_eq_lowMode (i : YoshidaEvenIndex) :
    clippedEvenUnifiedMode i.1 =
      yoshidaClippedEvenLowMode yoshidaHalfLength i := by
  rw [clippedEvenUnifiedMode, yoshidaClippedEvenLowMode]

theorem evenModeFunction_apply_of_mem
    (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-yoshidaHalfLength) yoshidaHalfLength) :
    evenModeFunction n x = (clippedEvenUnifiedRealMode n x : ℂ) := by
  by_cases hn : n = 0
  · subst n
    rw [evenModeFunction, clippedEvenUnifiedMode,
      clippedEvenUnifiedRealMode, if_pos rfl, if_pos rfl,
      yoshidaClippedEvenZeroMode_apply_of_mem hx]
    rfl
  · rw [evenModeFunction, clippedEvenUnifiedMode,
      clippedEvenUnifiedRealMode, if_neg hn, if_neg hn,
      yoshidaClippedEvenMode_apply_of_mem yoshidaHalfLength_pos n hx]
    rfl

theorem evenModeFunction_apply_all (n : ℕ) (x : ℝ) :
    evenModeFunction n x =
      if x ∈ Set.Icc (-yoshidaHalfLength) yoshidaHalfLength then
        (clippedEvenUnifiedRealMode n x : ℂ)
      else 0 := by
  by_cases hx : x ∈ Set.Icc (-yoshidaHalfLength) yoshidaHalfLength
  · rw [if_pos hx, evenModeFunction_apply_of_mem n hx]
  · rw [if_neg hx, evenModeFunction]
    exact yoshidaClippedSmooth_eq_zero_outside _ hx

theorem star_evenModeFunction (n : ℕ) (x : ℝ) :
    star (evenModeFunction n x) = evenModeFunction n x := by
  rw [evenModeFunction_apply_all]
  by_cases hx : x ∈ Set.Icc (-yoshidaHalfLength) yoshidaHalfLength
  · rw [if_pos hx]
    simp
  · simp [hx]

theorem evenModeFunction_even (n : ℕ) :
    Function.Even (evenModeFunction n) := by
  intro x
  rw [evenModeFunction_apply_all, evenModeFunction_apply_all]
  have hmem :
      -x ∈ Set.Icc (-yoshidaHalfLength) yoshidaHalfLength ↔
        x ∈ Set.Icc (-yoshidaHalfLength) yoshidaHalfLength := by
    constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
  by_cases hx : x ∈ Set.Icc (-yoshidaHalfLength) yoshidaHalfLength
  · have hnegx : -x ∈
        Set.Icc (-yoshidaHalfLength) yoshidaHalfLength := hmem.mpr hx
    rw [if_pos hx, if_pos hnegx]
    by_cases hn : n = 0
    · simp [clippedEvenUnifiedRealMode, hn, clippedEvenZeroRealMode]
    · simp only [clippedEvenUnifiedRealMode, if_neg hn,
        clippedEvenRealMode]
      rw [show Real.pi * (n : ℝ) * -x / yoshidaHalfLength =
          -(Real.pi * (n : ℝ) * x / yoshidaHalfLength) by ring,
        Real.cos_neg]
  · have hnegx : -x ∉
        Set.Icc (-yoshidaHalfLength) yoshidaHalfLength := by
      exact fun h ↦ hx (hmem.mp h)
    simp [hx, hnegx]

theorem evenModeFunction_integrable (n : ℕ) :
    Integrable (evenModeFunction n) := by
  have hOn : IntegrableOn (evenModeFunction n)
      (Set.Icc (-yoshidaHalfLength) yoshidaHalfLength) := by
    exact (clippedEvenUnifiedMode n).property.1.continuousOn
      |>.integrableOn_compact isCompact_Icc
  exact hOn.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
    rw [evenModeFunction]
    exact yoshidaClippedSmooth_eq_zero_outside _ hx)

theorem evenModeFunction_hasCompactSupport (n : ℕ) :
    HasCompactSupport (evenModeFunction n) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  by_contra hmem
  exact hx (by
    rw [evenModeFunction]
    exact yoshidaClippedSmooth_eq_zero_outside _ hmem)

theorem clippedEvenUnifiedCorrelation_eq_realIntegral
    (n m : ℕ) (u : ℝ) :
    clippedEvenUnifiedCorrelation n m u =
      ∫ x in -yoshidaHalfLength..yoshidaHalfLength - u,
        clippedEvenUnifiedRealMode n (u + x) *
          clippedEvenUnifiedRealMode m x := by
  by_cases hn : n = 0
  · subst n
    by_cases hm : m = 0
    · subst m
      rfl
    · simp [clippedEvenUnifiedCorrelation, clippedEvenUnifiedRealMode,
        clippedEvenZeroPositiveCorrelation, hm]
  · by_cases hm : m = 0
    · subst m
      simp [clippedEvenUnifiedCorrelation, clippedEvenUnifiedRealMode,
        clippedEvenPositiveZeroCorrelation, hn]
    · simp [clippedEvenUnifiedCorrelation, clippedEvenUnifiedRealMode,
        clippedEvenCorrelation, hn, hm]

theorem clippedEvenUnifiedCorrelation_comm (n m : ℕ) (u : ℝ) :
    clippedEvenUnifiedCorrelation n m u =
      clippedEvenUnifiedCorrelation m n u := by
  by_cases hn : n = 0
  · subst n
    by_cases hm : m = 0
    · subst m
      rfl
    · rw [clippedEvenUnifiedCorrelation, clippedEvenUnifiedCorrelation,
        if_pos rfl, if_neg hm, if_neg hm, if_pos rfl,
        clippedEvenZeroPositiveCorrelation_half hm,
        clippedEvenPositiveZeroCorrelation_half hm]
  · by_cases hm : m = 0
    · subst m
      rw [clippedEvenUnifiedCorrelation, clippedEvenUnifiedCorrelation,
        if_neg hn, if_pos rfl, if_pos rfl, if_neg hn,
        clippedEvenPositiveZeroCorrelation_half hn,
        clippedEvenZeroPositiveCorrelation_half hn]
    · by_cases hnm : n = m
      · subst m
        rfl
      · rw [clippedEvenUnifiedCorrelation, clippedEvenUnifiedCorrelation,
          if_neg hn, if_neg hm, if_neg hm, if_neg hn,
          clippedEvenCorrelation_half_offdiag hn hm hnm,
          clippedEvenCorrelation_half_offdiag hm hn (Ne.symm hnm),
          add_comm m n]
        rw [show yoshidaKappa n * Real.sin (yoshidaKappa n * u) -
            yoshidaKappa m * Real.sin (yoshidaKappa m * u) =
            -(yoshidaKappa m * Real.sin (yoshidaKappa m * u) -
              yoshidaKappa n * Real.sin (yoshidaKappa n * u)) by ring]
        rw [show yoshidaKappa m ^ 2 - yoshidaKappa n ^ 2 =
            -(yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2) by ring]
        rw [mul_neg, neg_div_neg_eq]

theorem evenCrossCorrelation_eq_clippedEvenUnifiedCorrelation_swap
    {u : ℝ} (hu0 : 0 ≤ u) (huL : u ≤ yoshidaLength)
    (n m : ℕ) :
    crossCorrelation (evenModeFunction n) (evenModeFunction m) u =
      (clippedEvenUnifiedCorrelation m n u : ℂ) := by
  rw [crossCorrelation_apply]
  have hle : -yoshidaHalfLength ≤ yoshidaHalfLength - u := by
    rw [show yoshidaLength = 2 * yoshidaHalfLength by
      exact two_mul_yoshidaHalfLength.symm] at huL
    linarith
  have hsupport :
      (∫ x : ℝ,
        star (evenModeFunction n x) * evenModeFunction m (u + x)) =
        ∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength - u,
          star (evenModeFunction n x) * evenModeFunction m (u + x) := by
    rw [intervalIntegral.integral_of_le hle,
      ← integral_Icc_eq_integral_Ioc]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      by_cases hxn : x ∈ Set.Icc (-yoshidaHalfLength) yoshidaHalfLength
      · have hxgt : yoshidaHalfLength - u < x := by
          by_contra hnot
          exact hx ⟨hxn.1, le_of_not_gt hnot⟩
        have hout : u + x ∉
            Set.Icc (-yoshidaHalfLength) yoshidaHalfLength := by
          intro hmem
          linarith [hmem.2]
        rw [evenModeFunction_apply_all m (u + x), if_neg hout, mul_zero]
      · rw [evenModeFunction_apply_all n x, if_neg hxn, star_zero, zero_mul])).symm
  rw [hsupport]
  calc
    (∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength - u,
        star (evenModeFunction n x) * evenModeFunction m (u + x)) =
        ∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength - u,
          ((clippedEvenUnifiedRealMode m (u + x) *
            clippedEvenUnifiedRealMode n x : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈
          Set.Icc (-yoshidaHalfLength) (yoshidaHalfLength - u) := by
        simpa only [uIcc_of_le hle] using hx
      have hxIcc : x ∈
          Set.Icc (-yoshidaHalfLength) yoshidaHalfLength := by
        constructor
        · exact hx'.1
        · linarith [hx'.2, hu0]
      have huxIcc : u + x ∈
          Set.Icc (-yoshidaHalfLength) yoshidaHalfLength := by
        constructor <;> linarith [hx'.1, hx'.2, hu0]
      simp only
      rw [star_evenModeFunction,
        evenModeFunction_apply_of_mem n hxIcc,
        evenModeFunction_apply_of_mem m huxIcc]
      push_cast
      ring
    _ = (∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength - u,
          clippedEvenUnifiedRealMode m (u + x) *
            clippedEvenUnifiedRealMode n x : ℝ) := by
      rw [intervalIntegral.integral_ofReal]
    _ = (clippedEvenUnifiedCorrelation m n u : ℂ) := by
      rw [clippedEvenUnifiedCorrelation_eq_realIntegral]

theorem evenCrossCorrelation_eq_clippedEvenUnifiedCorrelation
    {u : ℝ} (hu0 : 0 ≤ u) (huL : u ≤ yoshidaLength)
    (n m : ℕ) :
    crossCorrelation (evenModeFunction n) (evenModeFunction m) u =
      (clippedEvenUnifiedCorrelation n m u : ℂ) := by
  rw [evenCrossCorrelation_eq_clippedEvenUnifiedCorrelation_swap hu0 huL]
  rw [clippedEvenUnifiedCorrelation_comm]

theorem evenCrossCorrelation_neg_eq_swap (u : ℝ) (n m : ℕ) :
    crossCorrelation (evenModeFunction n) (evenModeFunction m) (-u) =
      crossCorrelation (evenModeFunction m) (evenModeFunction n) u := by
  rw [crossCorrelation_apply, crossCorrelation_apply]
  let G : ℝ → ℂ := fun y ↦
    star (evenModeFunction n (y + u)) * evenModeFunction m y
  calc
    (∫ x : ℝ, star (evenModeFunction n x) * evenModeFunction m (-u + x)) =
        ∫ x : ℝ, G (x + (-u)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [G]
      congr 2 <;> ring_nf
    _ = ∫ y : ℝ, G y := MeasureTheory.integral_add_right_eq_self G (-u)
    _ = ∫ y : ℝ,
        star (evenModeFunction m y) * evenModeFunction n (u + y) := by
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp only [G]
      rw [star_evenModeFunction, star_evenModeFunction]
      rw [add_comm y u, mul_comm]

theorem evenCrossCorrelation_eq_zero_of_length_lt
    {u : ℝ} (hu : yoshidaLength < u) (n m : ℕ) :
    crossCorrelation (evenModeFunction n) (evenModeFunction m) u = 0 := by
  rw [crossCorrelation_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Set.Icc (-yoshidaHalfLength) yoshidaHalfLength
  · have hux : u + x ∉
        Set.Icc (-yoshidaHalfLength) yoshidaHalfLength := by
      intro hmem
      rw [← two_mul_yoshidaHalfLength] at hu
      linarith [hx.1, hmem.2]
    rw [evenModeFunction_apply_all m (u + x), if_neg hux, mul_zero]
    simp
  · rw [evenModeFunction_apply_all n x, if_neg hx, star_zero, zero_mul]
    simp

private theorem evenCrossCorrelation_comm_of_nonneg
    {u : ℝ} (hu : 0 ≤ u) (n m : ℕ) :
    crossCorrelation (evenModeFunction n) (evenModeFunction m) u =
      crossCorrelation (evenModeFunction m) (evenModeFunction n) u := by
  by_cases huL : u ≤ yoshidaLength
  · rw [evenCrossCorrelation_eq_clippedEvenUnifiedCorrelation hu huL,
      evenCrossCorrelation_eq_clippedEvenUnifiedCorrelation hu huL,
      clippedEvenUnifiedCorrelation_comm]
  · have hLt : yoshidaLength < u := lt_of_not_ge huL
    rw [evenCrossCorrelation_eq_zero_of_length_lt hLt,
      evenCrossCorrelation_eq_zero_of_length_lt hLt]

theorem evenCrossCorrelation_comm (u : ℝ) (n m : ℕ) :
    crossCorrelation (evenModeFunction n) (evenModeFunction m) u =
      crossCorrelation (evenModeFunction m) (evenModeFunction n) u := by
  by_cases hu : 0 ≤ u
  · exact evenCrossCorrelation_comm_of_nonneg hu n m
  · have hneg : 0 ≤ -u := by linarith
    calc
      crossCorrelation (evenModeFunction n) (evenModeFunction m) u =
          crossCorrelation (evenModeFunction m) (evenModeFunction n) (-u) := by
        simpa only [neg_neg] using
          evenCrossCorrelation_neg_eq_swap (-u) n m
      _ = crossCorrelation (evenModeFunction n) (evenModeFunction m) (-u) :=
        evenCrossCorrelation_comm_of_nonneg hneg m n
      _ = crossCorrelation (evenModeFunction m) (evenModeFunction n) u :=
        evenCrossCorrelation_neg_eq_swap u n m

theorem evenCrossCorrelation_even (n m : ℕ) :
    Function.Even (crossCorrelation (evenModeFunction n) (evenModeFunction m)) := by
  intro u
  rw [evenCrossCorrelation_neg_eq_swap]
  exact evenCrossCorrelation_comm u m n

private theorem starReflection_evenModeFunction_integrable (n : ℕ) :
    Integrable (starReflection (evenModeFunction n)) := by
  have hneg : Integrable (fun x : ℝ ↦ evenModeFunction n (-x)) :=
    (evenModeFunction_integrable n).comp_neg
  simpa only [starReflection, RCLike.star_def] using
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hneg

theorem evenCrossCorrelation_integrable (n m : ℕ) :
    Integrable (crossCorrelation (evenModeFunction n) (evenModeFunction m)) := by
  exact (starReflection_evenModeFunction_integrable n).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (evenModeFunction_integrable m)

private def weightedRight (s : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((Real.exp (s * x) : ℝ) : ℂ) * evenModeFunction n x

private def weightedLeft (s : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((Real.exp (s * x) : ℝ) : ℂ) * starReflection (evenModeFunction n) x

private theorem weightedRight_integrable (s : ℝ) (n : ℕ) :
    Integrable (weightedRight s n) := by
  have hOn : IntegrableOn (weightedRight s n)
      (Set.Icc (-yoshidaHalfLength) yoshidaHalfLength) := by
    have hexp : Continuous (fun x : ℝ ↦
        ((Real.exp (s * x) : ℝ) : ℂ)) := by fun_prop
    exact (hexp.continuousOn.mul
      (clippedEvenUnifiedMode n).property.1.continuousOn)
        |>.integrableOn_compact isCompact_Icc
  exact hOn.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by
    unfold weightedRight
    rw [evenModeFunction_apply_all n x, if_neg hx, mul_zero])

private theorem weightedLeft_integrable (s : ℝ) (n : ℕ) :
    Integrable (weightedLeft s n) := by
  have hneg : Integrable (fun x : ℝ ↦ weightedRight (-s) n (-x)) :=
    (weightedRight_integrable (-s) n).comp_neg
  have hstar : Integrable (fun x : ℝ ↦
      star (weightedRight (-s) n (-x))) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hneg
  apply hstar.congr
  filter_upwards [] with x
  simp only [weightedLeft, weightedRight, starReflection, neg_mul,
    RCLike.star_def, map_mul, conj_ofReal]
  congr 2
  congr 1
  ring

private theorem weighted_convolution_eq
    (s : ℝ) (n m : ℕ) (u : ℝ) :
    (weightedLeft s n ⋆[ContinuousLinearMap.mul ℂ ℂ]
        weightedRight s m) u =
      ((Real.exp (s * u) : ℝ) : ℂ) *
        crossCorrelation (evenModeFunction n) (evenModeFunction m) u := by
  rw [MeasureTheory.convolution_def]
  calc
    (∫ t : ℝ,
        ContinuousLinearMap.mul ℂ ℂ (weightedLeft s n t)
          (weightedRight s m (u - t))) =
        ∫ t : ℝ, ((Real.exp (s * u) : ℝ) : ℂ) *
          (starReflection (evenModeFunction n) t *
            evenModeFunction m (u - t)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hexp : Real.exp (s * t) * Real.exp (s * (u - t)) =
          Real.exp (s * u) := by
        rw [← Real.exp_add]
        congr 1
        ring
      dsimp only [weightedLeft, weightedRight]
      calc
        (((Real.exp (s * t) : ℝ) : ℂ) *
              starReflection (evenModeFunction n) t) *
            (((Real.exp (s * (u - t)) : ℝ) : ℂ) *
              evenModeFunction m (u - t)) =
            ((((Real.exp (s * t) * Real.exp (s * (u - t)) : ℝ)) : ℂ) *
              (starReflection (evenModeFunction n) t *
                evenModeFunction m (u - t))) := by
          push_cast
          ring
        _ = (((Real.exp (s * u) : ℝ) : ℂ) *
              (starReflection (evenModeFunction n) t *
                evenModeFunction m (u - t))) := by
          rw [hexp]
    _ = ((Real.exp (s * u) : ℝ) : ℂ) *
        ∫ t : ℝ, starReflection (evenModeFunction n) t *
          evenModeFunction m (u - t) := by
      exact MeasureTheory.integral_const_mul
        (((Real.exp (s * u) : ℝ) : ℂ)) _
    _ = _ := by
      rw [crossCorrelation, MeasureTheory.convolution_def]
      congr 1

private theorem integral_weightedLeft (s : ℝ) (n : ℕ) :
    (∫ x : ℝ, weightedLeft s n x) =
      star (∫ x : ℝ, weightedRight (-s) n x) := by
  calc
    (∫ x : ℝ, weightedLeft s n x) =
        ∫ x : ℝ, weightedLeft s n (-x) := by
      exact (MeasureTheory.integral_neg_eq_self (weightedLeft s n) volume).symm
    _ = ∫ x : ℝ, star (weightedRight (-s) n x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [weightedLeft, weightedRight, starReflection, neg_mul,
        neg_neg, RCLike.star_def, map_mul, conj_ofReal]
      congr 2
      congr 1
      ring
    _ = star (∫ x : ℝ, weightedRight (-s) n x) := by
      simpa only [RCLike.star_def] using
        (integral_conj (f := weightedRight (-s) n))

private theorem integral_exp_mul_evenCrossCorrelation
    (s : ℝ) (n m : ℕ) :
    (∫ u : ℝ, ((Real.exp (s * u) : ℝ) : ℂ) *
      crossCorrelation (evenModeFunction n) (evenModeFunction m) u) =
      star (∫ x : ℝ, weightedRight (-s) n x) *
        ∫ x : ℝ, weightedRight s m x := by
  have hconv := MeasureTheory.integral_convolution
    (ContinuousLinearMap.mul ℂ ℂ)
    (weightedLeft_integrable s n) (weightedRight_integrable s m)
  calc
    (∫ u : ℝ, ((Real.exp (s * u) : ℝ) : ℂ) *
        crossCorrelation (evenModeFunction n) (evenModeFunction m) u) =
        ∫ u : ℝ,
          (weightedLeft s n ⋆[ContinuousLinearMap.mul ℂ ℂ]
            weightedRight s m) u := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact (weighted_convolution_eq s n m u).symm
    _ = (∫ x : ℝ, weightedLeft s n x) *
          ∫ x : ℝ, weightedRight s m x := by
      simpa using hconv
    _ = _ := by rw [integral_weightedLeft]

private theorem exp_mul_evenCrossCorrelation_integrable
    (s : ℝ) (n m : ℕ) :
    Integrable (fun u : ℝ ↦ ((Real.exp (s * u) : ℝ) : ℂ) *
      crossCorrelation (evenModeFunction n) (evenModeFunction m) u) := by
  have hconv := (weightedLeft_integrable s n).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (weightedRight_integrable s m)
  apply hconv.congr
  filter_upwards [] with u
  exact weighted_convolution_eq s n m u

private theorem positivePolar_evenMode_eq_integral (n : ℕ) :
    yoshidaPositivePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
        (clippedEvenUnifiedMode n) =
      ∫ x : ℝ, weightedRight (-(1 / 2)) n x := by
  rw [yoshidaPositivePolarLinear, yoshidaCenteredLaplaceLinear_apply]
  have hpoint (x : ℝ) :
      Complex.exp (-((1 / 2 : ℂ) * (x : ℂ))) *
          clippedEvenUnifiedMode n x =
        weightedRight (-(1 / 2)) n x := by
    unfold weightedRight evenModeFunction
    rw [show -((1 / 2 : ℂ) * (x : ℂ)) =
        (((-(1 / 2)) * x : ℝ) : ℂ) by push_cast; ring]
    rw [(Complex.ofReal_exp ((-(1 / 2)) * x)).symm]
  calc
    (∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength,
        Complex.exp (-((1 / 2 : ℂ) * (x : ℂ))) *
          clippedEvenUnifiedMode n x) =
        ∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength,
          weightedRight (-(1 / 2)) n x := by
      apply intervalIntegral.integral_congr
      intro x _
      exact hpoint x
    _ = ∫ x : ℝ, weightedRight (-(1 / 2)) n x := by
      rw [intervalIntegral.integral_of_le
          (by linarith [yoshidaHalfLength_pos]),
        ← integral_Icc_eq_integral_Ioc]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
        unfold weightedRight evenModeFunction
        rw [yoshidaClippedSmooth_eq_zero_outside _ hx, mul_zero])

private theorem negativePolar_evenMode_eq_integral (n : ℕ) :
    yoshidaNegativePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
        (clippedEvenUnifiedMode n) =
      ∫ x : ℝ, weightedRight (1 / 2) n x := by
  rw [yoshidaNegativePolarLinear, yoshidaCenteredLaplaceLinear_apply]
  have hpoint (x : ℝ) :
      Complex.exp (-((-1 / 2 : ℂ) * (x : ℂ))) *
          clippedEvenUnifiedMode n x =
        weightedRight (1 / 2) n x := by
    unfold weightedRight evenModeFunction
    rw [show -((-1 / 2 : ℂ) * (x : ℂ)) =
        (((1 / 2) * x : ℝ) : ℂ) by push_cast; ring]
    rw [(Complex.ofReal_exp ((1 / 2) * x)).symm]
  calc
    (∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength,
        Complex.exp (-((-1 / 2 : ℂ) * (x : ℂ))) *
          clippedEvenUnifiedMode n x) =
        ∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength,
          weightedRight (1 / 2) n x := by
      apply intervalIntegral.integral_congr
      intro x _
      exact hpoint x
    _ = ∫ x : ℝ, weightedRight (1 / 2) n x := by
      rw [intervalIntegral.integral_of_le
          (by linarith [yoshidaHalfLength_pos]),
        ← integral_Icc_eq_integral_Ioc]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
        unfold weightedRight evenModeFunction
        rw [yoshidaClippedSmooth_eq_zero_outside _ hx, mul_zero])

def clippedEvenRealPolarCorrelationValue (n m : ℕ) : ℝ :=
  2 * ∫ u : ℝ in 0..yoshidaLength,
    (Real.exp (u / 2) + Real.exp (-u / 2)) *
      clippedEvenUnifiedCorrelation n m u

theorem integral_polarWeight_evenCrossCorrelation_eq_two_integral_correlation
    (n m : ℕ) :
    (∫ u : ℝ,
      (((Real.exp (u / 2) + Real.exp (-u / 2) : ℝ) : ℂ) *
        crossCorrelation (evenModeFunction n) (evenModeFunction m) u)) =
      2 * ∫ u : ℝ in 0..yoshidaLength,
        (((Real.exp (u / 2) + Real.exp (-u / 2) : ℝ) : ℂ) *
          (clippedEvenUnifiedCorrelation n m u : ℂ)) := by
  let W : ℝ → ℂ := fun u ↦
    (((Real.exp (u / 2) + Real.exp (-u / 2) : ℝ) : ℂ) *
      crossCorrelation (evenModeFunction n) (evenModeFunction m) u)
  have hplus : Integrable (fun u : ℝ ↦
      ((Real.exp ((1 / 2 : ℝ) * u) : ℝ) : ℂ) *
        crossCorrelation (evenModeFunction n) (evenModeFunction m) u) :=
    exp_mul_evenCrossCorrelation_integrable (1 / 2) n m
  have hminus : Integrable (fun u : ℝ ↦
      ((Real.exp ((-1 / 2 : ℝ) * u) : ℝ) : ℂ) *
        crossCorrelation (evenModeFunction n) (evenModeFunction m) u) :=
    exp_mul_evenCrossCorrelation_integrable (-1 / 2) n m
  have hWint : Integrable W := by
    apply (hplus.add hminus).congr
    filter_upwards [] with u
    simp only [Pi.add_apply]
    dsimp only [W]
    push_cast
    ring_nf
  have hWeven : Function.Even W := by
    intro u
    dsimp only [W]
    rw [evenCrossCorrelation_even]
    congr 1
    push_cast
    simp only [neg_div, neg_neg]
    rw [add_comm]
  have hleft : (∫ u : ℝ in Set.Iic 0, W u) =
      ∫ u : ℝ in Set.Ioi 0, W u := by
    calc
      (∫ u : ℝ in Set.Iic 0, W u) =
          ∫ u : ℝ in Set.Iic 0, W (-u) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro u _
        exact (hWeven u).symm
      _ = ∫ u : ℝ in Set.Ioi 0, W u := by
        simpa only [neg_zero] using integral_comp_neg_Iic 0 W
  have hwhole : (∫ u : ℝ, W u) =
      2 * ∫ u : ℝ in Set.Ioi 0, W u := by
    rw [← intervalIntegral.integral_Iic_add_Ioi
        hWint.integrableOn hWint.integrableOn,
      hleft]
    ring
  have hpositive : (∫ u : ℝ in Set.Ioi 0, W u) =
      ∫ u : ℝ in 0..yoshidaLength, W u := by
    rw [intervalIntegral.integral_of_le yoshidaLength_pos.le]
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self
    intro u hu
    have huLt : yoshidaLength < u := by
      rcases hu with ⟨hu0, huNot⟩
      simp only [mem_Ioi] at hu0
      simp only [mem_Ioc, not_and, not_le] at huNot
      exact huNot hu0
    dsimp only [W]
    rw [evenCrossCorrelation_eq_zero_of_length_lt huLt, mul_zero]
  have hinterval : (∫ u : ℝ in 0..yoshidaLength, W u) =
      ∫ u : ℝ in 0..yoshidaLength,
        (((Real.exp (u / 2) + Real.exp (-u / 2) : ℝ) : ℂ) *
          (clippedEvenUnifiedCorrelation n m u : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc (0 : ℝ) yoshidaLength := by
      simpa only [uIcc_of_le yoshidaLength_pos.le] using hu
    dsimp only [W]
    rw [evenCrossCorrelation_eq_clippedEvenUnifiedCorrelation
      hu'.1 hu'.2]
  change (∫ u : ℝ, W u) = _
  rw [hwhole, hpositive, hinterval]

theorem evenPolarCrossTerm_eq_ofReal (n m : ℕ) :
    star (yoshidaPositivePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
        (clippedEvenUnifiedMode n)) *
        yoshidaNegativePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
          (clippedEvenUnifiedMode m) +
      star (yoshidaNegativePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
        (clippedEvenUnifiedMode n)) *
        yoshidaPositivePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
          (clippedEvenUnifiedMode m) =
      (clippedEvenRealPolarCorrelationValue n m : ℂ) := by
  have hpos := integral_exp_mul_evenCrossCorrelation (1 / 2) n m
  have hneg := integral_exp_mul_evenCrossCorrelation (-(1 / 2)) n m
  simp only [neg_neg] at hneg
  rw [← positivePolar_evenMode_eq_integral n,
    ← negativePolar_evenMode_eq_integral m] at hpos
  rw [← negativePolar_evenMode_eq_integral n,
    ← positivePolar_evenMode_eq_integral m] at hneg
  have hplusInt := exp_mul_evenCrossCorrelation_integrable (1 / 2) n m
  have hminusInt := exp_mul_evenCrossCorrelation_integrable (-(1 / 2)) n m
  calc
    star (yoshidaPositivePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
          (clippedEvenUnifiedMode n)) *
          yoshidaNegativePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
            (clippedEvenUnifiedMode m) +
        star (yoshidaNegativePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
          (clippedEvenUnifiedMode n)) *
          yoshidaPositivePolarLinear yoshidaHalfLength yoshidaHalfLength_pos
            (clippedEvenUnifiedMode m) =
        (∫ u : ℝ, ((Real.exp ((1 / 2 : ℝ) * u) : ℝ) : ℂ) *
            crossCorrelation (evenModeFunction n) (evenModeFunction m) u) +
          ∫ u : ℝ, ((Real.exp ((-(1 / 2) : ℝ) * u) : ℝ) : ℂ) *
            crossCorrelation (evenModeFunction n) (evenModeFunction m) u := by
      rw [hpos, hneg]
    _ = ∫ u : ℝ,
        (((Real.exp (u / 2) + Real.exp (-u / 2) : ℝ) : ℂ) *
          crossCorrelation (evenModeFunction n) (evenModeFunction m) u) := by
      rw [← integral_add hplusInt hminusInt]
      apply integral_congr_ae
      filter_upwards [] with u
      push_cast
      ring_nf
    _ = 2 * ∫ u : ℝ in 0..yoshidaLength,
        (((Real.exp (u / 2) + Real.exp (-u / 2) : ℝ) : ℂ) *
          (clippedEvenUnifiedCorrelation n m u : ℂ)) :=
      integral_polarWeight_evenCrossCorrelation_eq_two_integral_correlation n m
    _ = (clippedEvenRealPolarCorrelationValue n m : ℂ) := by
      rw [clippedEvenRealPolarCorrelationValue]
      push_cast
      rw [← intervalIntegral.integral_ofReal]
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      push_cast
      rfl

/-- The real digamma/distribution contribution after the now-proved polar
piece has been removed from the exact admissible real-space value. -/
def clippedEvenRealDigammaDistributionValue (n m : ℕ) : ℝ :=
  clippedEvenAdmissibleRealSpaceGram n m -
    clippedEvenRealPolarCorrelationValue n m

/-- Away from the removable point, subtracting the polar integrand from the
stable admissible integrand gives exactly the negated geometric kernel plus
the zero-correlation counterterm.  This records the analytic content of
`clippedEvenRealDigammaDistributionValue` without pretending that the even
spectral series interchange has already been proved. -/
theorem clippedEvenStable_sub_polar_eq_negatedGeometric_of_ne_zero
    (n m : ℕ) {u : ℝ} (hu : u ≠ 0) :
    clippedEvenStableCorrelationIntegrand n m u -
        2 * (Real.exp (u / 2) + Real.exp (-u / 2)) *
          clippedEvenUnifiedCorrelation n m u =
      -oddKernel u * clippedEvenUnifiedCorrelation n m u +
        clippedEvenUnifiedCorrelation n m 0 / u := by
  rw [clippedEvenStableCorrelationIntegrand,
    yoshidaWeightPlus, if_neg hu, yoshidaWeight, oddKernel]
  ring

theorem clippedEvenRealPolar_add_digamma_eq_admissible (n m : ℕ) :
    clippedEvenRealPolarCorrelationValue n m +
        clippedEvenRealDigammaDistributionValue n m =
      clippedEvenAdmissibleRealSpaceGram n m := by
  rw [clippedEvenRealDigammaDistributionValue]
  ring

/-- The actual angular spectral product for two unified even modes. -/
def evenAngularSpectralProduct (n m : ℕ) (v : ℝ) : ℂ :=
  star (yoshidaCriticalSampleLinear
      yoshidaHalfLength yoshidaHalfLength_pos v (clippedEvenUnifiedMode n)) *
    yoshidaCriticalSampleLinear
      yoshidaHalfLength yoshidaHalfLength_pos v (clippedEvenUnifiedMode m)

private theorem continuous_evenCriticalSample (n : ℕ) :
    Continuous (fun v : ℝ ↦ yoshidaCriticalSampleLinear
      yoshidaHalfLength yoshidaHalfLength_pos v (clippedEvenUnifiedMode n)) := by
  rw [show (fun v : ℝ ↦ yoshidaCriticalSampleLinear
      yoshidaHalfLength yoshidaHalfLength_pos v (clippedEvenUnifiedMode n)) =
      fun v : ℝ ↦ FourierTransform.fourier (evenModeFunction n)
        (v / (2 * Real.pi)) by
    funext v
    exact yoshidaCriticalSample_eq_fourier
      yoshidaHalfLength_pos v (clippedEvenUnifiedMode n)]
  have hfourier : Continuous
      (FourierTransform.fourier (evenModeFunction n)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner (evenModeFunction_integrable n)
  exact hfourier.comp (by fun_prop)

theorem continuous_evenAngularSpectralProduct (n m : ℕ) :
    Continuous (evenAngularSpectralProduct n m) := by
  exact (continuous_evenCriticalSample n).star.mul
    (continuous_evenCriticalSample m)

/-- Endpoint jumps leave only `O(v⁻²)` decay for the product, but that is
still enough for ordinary spectral-product integrability.  It is not the
stronger weighted integrability assumed by the odd digamma interface. -/
theorem evenAngularSpectralProduct_integrable (n m : ℕ) :
    Integrable (evenAngularSpectralProduct n m) := by
  let Cn : ℝ := yoshidaCriticalDecayConstant yoshidaHalfLength
    (clippedEvenUnifiedMode n)
  let Cm : ℝ := yoshidaCriticalDecayConstant yoshidaHalfLength
    (clippedEvenUnifiedMode m)
  let K : ℝ := 2 * Cn * Cm
  let q : ℝ → ℝ := fun v ↦ (1 + v ^ 2)⁻¹
  let S : Set ℝ := Set.Icc (-1 : ℝ) 1
  have hcompact : IntegrableOn (evenAngularSpectralProduct n m) S :=
    (continuous_evenAngularSpectralProduct n m).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hCn : 0 ≤ Cn := by
    exact yoshidaCriticalDecayConstant_nonneg yoshidaHalfLength_pos _
  have hCm : 0 ≤ Cm := by
    exact yoshidaCriticalDecayConstant_nonneg yoshidaHalfLength_pos _
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hmajor : Integrable (fun v ↦ K * q v) := by
    exact integrable_inv_one_add_sq.const_mul K
  have htail : IntegrableOn (evenAngularSpectralProduct n m) Sᶜ := by
    apply hmajor.integrableOn.mono'
    · exact (continuous_evenAngularSpectralProduct n m)
        |>.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
      have habs : 1 < |v| := by
        by_contra h
        apply hv
        exact abs_le.mp (le_of_not_gt h)
      have hvne : v ≠ 0 := abs_pos.mp (zero_lt_one.trans habs)
      have hsq : 1 < v ^ 2 := by
        rw [← sq_abs]
        nlinarith
      have hf := yoshidaCriticalSample_norm_le_inv_abs
        yoshidaHalfLength_pos v hvne (clippedEvenUnifiedMode n)
      have hg := yoshidaCriticalSample_norm_le_inv_abs
        yoshidaHalfLength_pos v hvne (clippedEvenUnifiedMode m)
      have hrecip : 1 / v ^ 2 ≤ 2 / (1 + v ^ 2) := by
        rw [div_le_div_iff₀ (by positivity : 0 < v ^ 2)
          (by positivity : 0 < 1 + v ^ 2)]
        nlinarith
      calc
        ‖evenAngularSpectralProduct n m v‖ =
            ‖yoshidaCriticalSampleLinear yoshidaHalfLength
                yoshidaHalfLength_pos v (clippedEvenUnifiedMode n)‖ *
              ‖yoshidaCriticalSampleLinear yoshidaHalfLength
                yoshidaHalfLength_pos v (clippedEvenUnifiedMode m)‖ := by
          simp [evenAngularSpectralProduct]
        _ ≤ (Cn / |v|) * (Cm / |v|) := by
          exact mul_le_mul hf hg (norm_nonneg _) (by positivity)
        _ = Cn * Cm * (1 / v ^ 2) := by
          field_simp [hvne, abs_ne_zero.mpr hvne]
          rw [sq_abs]
          ring
        _ ≤ Cn * Cm * (2 / (1 + v ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hrecip (mul_nonneg hCn hCm)
        _ = K * q v := by
          dsimp [K, q]
          ring
  rw [← integrableOn_univ]
  simpa only [S, union_compl_self] using hcompact.union htail

/-- The sole remaining spectral/distribution obligation after the exact
mode, support, correlation, and polar calculations in this module.

Unlike the odd bridge, this proposition does not demand the false stronger
condition that `(1 + v^2)` times the even spectral-product norm is integrable.
Its proof needs an endpoint-jump-compatible Cauchy identity and a digamma
interchange tailored to a spectral product with `O(v⁻²)` decay. -/
def ClippedEvenCriticalCrossDistributionBridge : Prop :=
  ∀ n m : ℕ,
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ,
        yoshidaClippedCriticalCrossIntegrand
          yoshidaHalfLength yoshidaHalfLength_pos
          (clippedEvenUnifiedMode n) (clippedEvenUnifiedMode m) v) =
      (clippedEvenRealDigammaDistributionValue n m : ℂ)

/-- The exact local critical pairing is the admissible real-space value once
the one remaining even critical-cross distribution identity is supplied. -/
theorem yoshidaClippedLocalCriticalPairing_even_eq_admissible
    (hdist : ClippedEvenCriticalCrossDistributionBridge)
    (n m : ℕ) :
    yoshidaClippedLocalCriticalPairing
        yoshidaHalfLength yoshidaHalfLength_pos
        (clippedEvenUnifiedMode n) (clippedEvenUnifiedMode m) =
      (clippedEvenAdmissibleRealSpaceGram n m : ℂ) := by
  rw [yoshidaClippedLocalCriticalPairing]
  rw [evenPolarCrossTerm_eq_ofReal n m]
  rw [hdist n m]
  rw [← Complex.ofReal_add]
  rw [clippedEvenRealPolar_add_digamma_eq_admissible]

/-- Sharp reduction of the original 40,000-entry production proposition to
the endpoint-jump-compatible critical-cross distribution identity above. -/
theorem clippedEvenFullAdmissibleDistributionBridge_of_criticalCrossBridge
    (hdist : ClippedEvenCriticalCrossDistributionBridge) :
    ClippedEvenFullAdmissibleDistributionBridge := by
  intro i j
  unfold clippedEvenFullGram yoshidaClippedEvenGram
  rw [show yoshidaClippedEvenLowMode yoshidaHalfLength i =
      clippedEvenUnifiedMode i.1 by
    exact (clippedEvenUnifiedMode_eq_lowMode i).symm]
  rw [show yoshidaClippedEvenLowMode yoshidaHalfLength j =
      clippedEvenUnifiedMode j.1 by
    exact (clippedEvenUnifiedMode_eq_lowMode j).symm]
  rw [yoshidaClippedLocalCriticalForm_apply]
  exact yoshidaClippedLocalCriticalPairing_even_eq_admissible
    hdist i.1 j.1

theorem clippedEvenFullMomentBridge_of_criticalCrossBridge
    (hdist : ClippedEvenCriticalCrossDistributionBridge) :
    ClippedEvenFullMomentBridge :=
  clippedEvenFullMomentBridge_of_admissibleDistributionBridge
    (clippedEvenFullAdmissibleDistributionBridge_of_criticalCrossBridge hdist)

end

end ArithmeticHodge.Analysis.YoshidaEvenDistributionReduction
