import ArithmeticHodge.Analysis.YoshidaEvenTailReduction
import ArithmeticHodge.Analysis.YoshidaOddDigammaSplit
import ArithmeticHodge.Analysis.YoshidaOddDigammaIntegralCertificate
import ArithmeticHodge.Analysis.YoshidaOddHomogeneousCoercivity
import Mathlib.Analysis.Fourier.LpSpace

set_option autoImplicit false

noncomputable section

open AddCircle Complex MeasureTheory Real Set
open scoped BigOperators ComplexConjugate FourierTransform

namespace ArithmeticHodge.Analysis.YoshidaEvenHomogeneousCoercivity

open YoshidaClippedCircleBridge
open YoshidaClippedCircleFaithful
open YoshidaCoercivityNumerics
open YoshidaEvenTailReduction
open YoshidaInfiniteCriticalSample
open YoshidaOddDigammaIntegralCertificate
open YoshidaOddDigammaLoss
open YoshidaOddDigammaSplit
open YoshidaOddHomogeneousCoercivity
open YoshidaOddSpectralMassBridge
open YoshidaOddTailPaired
open YoshidaSectionSixAnalytic
open YoshidaTZeroTailBounds
open YoshidaWeightedTailBounds

/-!
# Homogeneous coercivity on Yoshida's canonical even tail

This module promotes the Section 6 estimate to the actual periodic even tail
whose positive Fourier modes start at `200`.  In particular, the endpoint
jump of the clipped representative is handled by `L²` Plancherel rather than
by assuming that the zero extension is continuous.
-/

/-- `L²` Plancherel for the clipped critical sample.  This proof permits the
endpoint jumps carried by even periodic functions. -/
theorem clippedSpectralMass_eq_intervalEnergy
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    clippedSpectralMass a ha f =
      ∫ x : ℝ in -a..a,
        ‖(f : ℝ → ℂ) x‖ ^ 2 := by
  let g : ℝ → ℂ := f
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 := by
    dsimp only [c]
    positivity
  have hgInt : Integrable g := by
    exact f.property.1.continuousOn.integrableOn_Icc
      |>.integrable_of_forall_notMem_eq_zero
        (fun x hx ↦ yoshidaClippedSmooth_eq_zero_outside
          f hx)
  have hgSqInt : Integrable (fun x : ℝ ↦ ‖g x‖ ^ 2) := by
    have hcont : ContinuousOn (fun x : ℝ ↦ ‖g x‖ ^ 2)
        (Set.Icc (-a) a) := by
      have hfcont : ContinuousOn
          (fun x : ℝ ↦ (f : ℝ → ℂ) x)
          (Set.Icc (-a) a) :=
        f.property.1.continuousOn
      dsimp only [g]
      exact (continuous_norm.comp_continuousOn hfcont).pow 2
    exact hcont.integrableOn_Icc.integrable_of_forall_notMem_eq_zero
      (fun x hx ↦ by
        have hg0 : g x = 0 := yoshidaClippedSmooth_eq_zero_outside
          f hx
        rw [hg0]
        norm_num)
  have hgMemTwo : MemLp g 2 :=
    (memLp_two_iff_integrable_sq_norm hgInt.aestronglyMeasurable).2 hgSqInt
  have hFourierSq : Integrable (fun w : ℝ ↦
      ‖FourierTransform.fourier g w‖ ^ 2) := by
    have hscaled :=
      (YoshidaSectionSixAnalytic.integrable_normSq_yoshidaCriticalSample ha
        f).comp_mul_left' (R := c) hc
    apply hscaled.congr
    filter_upwards [] with w
    have harg : c * w / (2 * Real.pi) = w := by
      dsimp only [c]
      field_simp [Real.pi_ne_zero]
    rw [yoshidaCriticalSample_eq_fourier ha (c * w)
      f, harg]
    exact Complex.normSq_eq_norm_sq _
  have hFourierContinuous : Continuous (FourierTransform.fourier g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hgInt
  have hFourierMemTwo : MemLp (FourierTransform.fourier g) 2 :=
    (memLp_two_iff_integrable_sq_norm
      hFourierContinuous.aestronglyMeasurable).2 hFourierSq
  let G : Lp ℂ 2 (volume : Measure ℝ) := hgMemTwo.toLp g
  let H : Lp ℂ 2 (volume : Measure ℝ) :=
    hFourierMemTwo.toLp (FourierTransform.fourier g)
  have hGae : (G : ℝ → ℂ) =ᵐ[volume] g := by
    simpa only [G] using hgMemTwo.coeFn_toLp
  have hHae : (H : ℝ → ℂ) =ᵐ[volume]
      FourierTransform.fourier g := by
    simpa only [H] using hFourierMemTwo.coeFn_toLp
  have hdist :
      FourierTransform.fourier (G : TemperedDistribution ℝ ℂ) =
        (H : TemperedDistribution ℝ ℂ) := by
    ext φ
    rw [TemperedDistribution.fourier_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply]
    calc
      (∫ x : ℝ, (FourierTransform.fourier φ) x • (G : ℝ → ℂ) x) =
          ∫ x : ℝ, (FourierTransform.fourier φ) x • g x := by
        apply integral_congr_ae
        filter_upwards [hGae] with x hx
        exact congrArg (fun z : ℂ ↦ (FourierTransform.fourier φ) x • z) hx
      _ = ∫ x : ℝ, φ x • FourierTransform.fourier g x := by
        have hraw := VectorFourier.integral_fourierIntegral_smul_eq_flip
          (𝕜 := ℝ) (V := ℝ) (W := ℝ) (F := ℂ)
          (e := Real.fourierChar) (μ := volume) (ν := volume)
          (L := (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ))
          Real.continuous_fourierChar continuous_inner
          φ.integrable hgInt
        rw [flip_innerₗ] at hraw
        exact hraw
      _ = ∫ x : ℝ, φ x • (H : ℝ → ℂ) x := by
        apply integral_congr_ae
        filter_upwards [hHae] with x hx
        exact congrArg (fun z : ℂ ↦ φ x • z) hx.symm
  have hdist' :
      ((FourierTransform.fourier G : Lp ℂ 2 (volume : Measure ℝ)) :
          TemperedDistribution ℝ ℂ) =
        (H : TemperedDistribution ℝ ℂ) := by
    rw [← MeasureTheory.Lp.fourier_toTemperedDistribution_eq G]
    exact hdist
  have hGH : FourierTransform.fourier G = H := by
    have hinj : Function.Injective
        (MeasureTheory.Lp.toTemperedDistributionCLM ℂ
          (volume : Measure ℝ) 2) := by
      intro u v huv
      apply sub_eq_zero.mp
      have hz : MeasureTheory.Lp.toTemperedDistributionCLM ℂ
          (volume : Measure ℝ) 2 (u - v) = 0 := by
        rw [map_sub, huv, sub_self]
      have hmem : u - v ∈
          (MeasureTheory.Lp.toTemperedDistributionCLM ℂ
            (volume : Measure ℝ) 2).ker := hz
      rw [MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot] at hmem
      exact hmem
    exact hinj hdist'
  have hnorm : ‖H‖ = ‖G‖ := by
    rw [← hGH, MeasureTheory.Lp.norm_fourier_eq]
  have integral_norm_sq_eq_norm_sq
      (u : Lp ℂ 2 (volume : Measure ℝ)) :
      (∫ x : ℝ, ‖(u : ℝ → ℂ) x‖ ^ 2) = ‖u‖ ^ 2 := by
    have h := congrArg RCLike.re
      (@MeasureTheory.L2.inner_def ℝ ℂ ℂ _ _ _ _ _ u u)
    rw [← integral_re] at h
    · simpa only [← norm_sq_eq_re_inner] using h.symm
    · exact MeasureTheory.L2.integrable_inner u u
  have hPlancherel :
      (∫ w : ℝ, ‖FourierTransform.fourier g w‖ ^ 2) =
        ∫ x : ℝ, ‖g x‖ ^ 2 := by
    calc
      (∫ w : ℝ, ‖FourierTransform.fourier g w‖ ^ 2) =
          ∫ w : ℝ, ‖(H : ℝ → ℂ) w‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hHae] with w hw
        rw [hw]
      _ = ‖H‖ ^ 2 := integral_norm_sq_eq_norm_sq H
      _ = ‖G‖ ^ 2 := by rw [hnorm]
      _ = ∫ x : ℝ, ‖(G : ℝ → ℂ) x‖ ^ 2 :=
        (integral_norm_sq_eq_norm_sq G).symm
      _ = ∫ x : ℝ, ‖g x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hGae] with x hx
        rw [hx]
  have hsource : (∫ x : ℝ, ‖g x‖ ^ 2) =
      ∫ x : ℝ in -a..a, ‖g x‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith : -a ≤ a),
      ← integral_Icc_eq_integral_Ioc]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hg0 : g x = 0 := yoshidaClippedSmooth_eq_zero_outside
      f hx
    rw [hg0, norm_zero]
    norm_num
  let q : ℝ → ℝ := fun v ↦
    Complex.normSq (yoshidaCriticalSampleLinear a ha v
      f)
  have hscale := Measure.integral_comp_mul_left q c
  unfold clippedSpectralMass
  calc
    (1 / (2 * Real.pi)) * ∫ v : ℝ,
        Complex.normSq (yoshidaCriticalSampleLinear a ha v
          f) =
        |c⁻¹| • ∫ v : ℝ, q v := by
      rw [smul_eq_mul, abs_of_pos (inv_pos.mpr (by
        dsimp only [c]
        positivity))]
      dsimp only [c, q]
      rw [one_div]
    _ = ∫ w : ℝ, q (c * w) := hscale.symm
    _ = ∫ w : ℝ, ‖FourierTransform.fourier g w‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with w
      have harg : c * w / (2 * Real.pi) = w := by
        dsimp only [c]
        field_simp [Real.pi_ne_zero]
      dsimp only [q, g]
      rw [yoshidaCriticalSample_eq_fourier ha (c * w)
        f, harg]
      exact Complex.normSq_eq_norm_sq _
    _ = ∫ x : ℝ, ‖g x‖ ^ 2 := hPlancherel
    _ = ∫ x : ℝ in -a..a, ‖g x‖ ^ 2 := hsource

private def clippedReflection {a : ℝ} (f : YoshidaClippedSmooth a) :
    YoshidaClippedSmooth a := by
  refine ⟨fun x ↦ f (-x), ?_, ?_⟩
  · simpa only [Function.comp_def] using
      f.property.1.comp contDiff_neg.contDiffOn (by
        intro x hx
        exact ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  · intro x hx
    apply yoshidaClippedSmooth_eq_zero_outside f
    intro hneg
    apply hx
    exact ⟨by linarith [hneg.2], by linarith [hneg.1]⟩

private theorem periodicCore_endpoint_eq
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedPeriodicCore a) :
    (f : YoshidaClippedSmooth a) (-a) =
      (f : YoshidaClippedSmooth a) a := by
  have hperiod := periodicExtension_periodic f (-a)
  rw [show -a + 2 * a = a by ring] at hperiod
  calc
    (f : YoshidaClippedSmooth a) (-a) = periodicExtension f (-a) :=
      (periodicExtension_apply_of_mem f ⟨le_rfl, by linarith⟩).symm
    _ = periodicExtension f a := hperiod.symm
    _ = (f : YoshidaClippedSmooth a) a :=
      periodicExtension_apply_of_mem f ⟨by linarith, le_rfl⟩

private theorem centeredLift_clippedReflection_ae
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedPeriodicCore a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    centeredLift a
        (clippedReflection (f : YoshidaClippedSmooth a) : ℝ → ℂ) =ᵐ[
          AddCircle.haarAddCircle]
      fun x ↦ centeredLift a
        ((f : YoshidaClippedSmooth a) : ℝ → ℂ) (-x) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  filter_upwards [] with x
  let r := AddCircle.equivIoc (2 * a) (-a) x
  have hr : (r : ℝ) ∈ Set.Ioc (-a) a := by
    simpa only [show -a + 2 * a = a by ring] using r.property
  have hrepr : (((r : ℝ) : CenteredAddCircle a)) = x := by
    exact (AddCircle.equivIoc (2 * a) (-a)).symm_apply_apply x
  rw [← hrepr, centeredLift_apply_Ioc _ hr]
  change (f : YoshidaClippedSmooth a) (-(r : ℝ)) = centeredLift a
    ((f : YoshidaClippedSmooth a) : ℝ → ℂ)
    (-(((r : ℝ) : CenteredAddCircle a)))
  by_cases hra : (r : ℝ) = a
  · have hcircle : -(((r : ℝ) : CenteredAddCircle a)) =
        ((a : ℝ) : CenteredAddCircle a) := by
      rw [hra]
      change (((-a : ℝ) : CenteredAddCircle a)) =
        ((a : ℝ) : CenteredAddCircle a)
      calc
        (((-a : ℝ) : CenteredAddCircle a)) =
            (((-a + 2 * a : ℝ) : CenteredAddCircle a)) :=
          (AddCircle.coe_add_period (2 * a) (-a)).symm
        _ = ((a : ℝ) : CenteredAddCircle a) := by ring_nf
    rw [hcircle, centeredLift_apply_Ioc _ ⟨by linarith, le_rfl⟩, hra]
    exact periodicCore_endpoint_eq ha f
  · have hrlt : (r : ℝ) < a := lt_of_le_of_ne hr.2 hra
    have hneg : (-(r : ℝ)) ∈ Set.Ioc (-a) a :=
      ⟨by linarith, by linarith [hr.1]⟩
    rw [show -(((r : ℝ) : CenteredAddCircle a)) =
        ((-(r : ℝ) : ℝ) : CenteredAddCircle a) by rfl]
    rw [centeredLift_apply_Ioc _ hneg]

private theorem yoshidaClippedCircleL2_clippedReflection
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedPeriodicCore a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    yoshidaClippedCircleL2 ha
        (clippedReflection (f : YoshidaClippedSmooth a)) =
      reflectionL2 (T := 2 * a)
        (yoshidaClippedCircleL2 ha (f : YoshidaClippedSmooth a)) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  apply Lp.ext
  have href := reflectionL2_ae
    (yoshidaClippedCircleL2 ha (f : YoshidaClippedSmooth a))
  have hleft := (centeredLift_memLp ha
    (yoshidaClippedSmooth_memLp_two
      (clippedReflection (f : YoshidaClippedSmooth a)))).coeFn_toLp
  have hright := (centeredLift_memLp ha
    (yoshidaClippedSmooth_memLp_two
      (f : YoshidaClippedSmooth a))).coeFn_toLp
  have hleft' : (yoshidaClippedCircleL2 ha
      (clippedReflection (f : YoshidaClippedSmooth a)) :
      CenteredAddCircle a → ℂ) =ᵐ[AddCircle.haarAddCircle]
      centeredLift a
        (clippedReflection (f : YoshidaClippedSmooth a) : ℝ → ℂ) := by
    simpa only [yoshidaClippedCircleL2] using hleft
  have hright' : (yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) : CenteredAddCircle a → ℂ) =ᵐ[
        AddCircle.haarAddCircle]
      centeredLift a ((f : YoshidaClippedSmooth a) : ℝ → ℂ) := by
    simpa only [yoshidaClippedCircleL2] using hright
  have hrightNeg :=
    (circleNegMeasurePreserving (T := 2 * a)).quasiMeasurePreserving
      |>.ae_eq_comp hright'
  filter_upwards [hleft', href, hrightNeg,
    centeredLift_clippedReflection_ae ha f] with x hl hrefx hr hreflect
  rw [hl, hrefx]
  have hr' : (yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) : CenteredAddCircle a → ℂ) (-x) =
      centeredLift a ((f : YoshidaClippedSmooth a) : ℝ → ℂ) (-x) := by
    simpa only [Function.comp_apply] using hr
  rw [hr']
  exact hreflect

private theorem clippedReflection_eq_of_evenTail
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreEvenTailSubmodule ha N) :
    clippedReflection (f : YoshidaClippedSmooth a) =
      (f : YoshidaClippedSmooth a) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  let F := yoshidaClippedCircleL2 ha (f : YoshidaClippedSmooth a)
  have htail : F ∈ evenFourierTailSubmodule (T := 2 * a) N :=
    (mem_yoshidaPeriodicCoreEvenTailSubmodule_iff ha N f).mp hf
  have heven : reflectionL2 (T := 2 * a) F = F :=
    (mem_evenL2Submodule_iff F).mp htail.1
  apply yoshidaClippedCircleL2_injective ha
  calc
    yoshidaClippedCircleL2 ha
        (clippedReflection (f : YoshidaClippedSmooth a)) =
        reflectionL2 (T := 2 * a) F :=
      yoshidaClippedCircleL2_clippedReflection ha f
    _ = F := heven

/-- Actual even-tail membership upgrades from `L²` parity to pointwise parity
of the clipped representative. -/
theorem evenTail_pointwise_even
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreEvenTailSubmodule ha N) (x : ℝ) :
    (f : YoshidaClippedSmooth a) (-x) =
      (f : YoshidaClippedSmooth a) x := by
  have hreflect := clippedReflection_eq_of_evenTail ha N f hf
  have hfun := congrArg Subtype.val hreflect
  have h := congrFun hfun x
  simpa only [clippedReflection] using h

/-! ## Infinite paired sampling on the even tail -/

/-- The paired denominator for equal positive and negative even coefficients. -/
def evenPairedDenominator (x : ℝ) (n : ℕ) : ℝ :=
  1 / (x - (n : ℝ)) + 1 / (x + (n : ℝ))

/-- The exact removable critical sample, paired across an actual even Fourier
tail. -/
theorem hasSum_criticalSample_evenTail_paired_exact
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreEvenTailSubmodule ha N)
    (v : ℝ) :
    HasSum
      (fun k : ℕ ↦
        let n : ℕ := N + 1 + k
        centeredFourierCoeff ha
            ((f : YoshidaClippedSmooth a) : ℝ → ℂ) (n : ℤ) *
          (yoshidaIntervalExpQuotient a
              (yoshidaModeLaplaceExponent a (n : ℤ) (v * Complex.I)) +
            yoshidaIntervalExpQuotient a
              (yoshidaModeLaplaceExponent a (-(n : ℤ)) (v * Complex.I))))
      (yoshidaCriticalSampleLinear a ha v
        (f : YoshidaClippedSmooth a)) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  let F := yoshidaClippedCircleL2 ha (f : YoshidaClippedSmooth a)
  let c : ℤ → ℂ := fun n ↦ centeredFourierCoeff ha
    ((f : YoshidaClippedSmooth a) : ℝ → ℂ) n
  let q : ℤ → ℂ := fun n ↦ yoshidaIntervalExpQuotient a
    (yoshidaModeLaplaceExponent a n (v * Complex.I))
  have htail : F ∈ evenFourierTailSubmodule (T := 2 * a) N :=
    (mem_yoshidaPeriodicCoreEvenTailSubmodule_iff ha N f).mp hf
  have heven : F ∈ evenL2Submodule (T := 2 * a) := htail.1
  have hzero : F ∈ fourierTailSubmodule (T := 2 * a) N := htail.2
  have hcneg (n : ℤ) : c (-n) = c n := by
    dsimp only [c, F]
    rw [← fourierCoeff_yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) (-n)]
    rw [← fourierCoeff_yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) n]
    exact fourierCoeff_even_of_mem heven n
  have hc_of_nat_le (n : ℕ) (hn : n ≤ N) : c (n : ℤ) = 0 := by
    dsimp only [c, F]
    rw [← fourierCoeff_yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) (n : ℤ)]
    exact (mem_fourierTailSubmodule_iff N F).mp hzero (n : ℤ) (by
      simp only [Finset.mem_Icc]
      constructor <;> omega)
  have hc0 : c 0 = 0 := by
    simpa using hc_of_nat_le 0 (Nat.zero_le N)
  have hall : HasSum (fun n : ℤ ↦ c n * q n)
      (yoshidaCriticalSampleLinear a ha v
        (f : YoshidaClippedSmooth a)) := by
    simpa only [c, q] using hasSum_criticalSample_intervalExpQuotient
      ha v (f : YoshidaClippedSmooth a)
  let p : ℕ → ℂ := fun n ↦ c (n : ℤ) *
    (q (n : ℤ) + q (-(n : ℤ)))
  have hpaired : HasSum p
      (yoshidaCriticalSampleLinear a ha v
        (f : YoshidaClippedSmooth a)) := by
    have hraw := hall.nat_add_neg
    rw [hc0] at hraw
    simp only [zero_mul, add_zero] at hraw
    refine hraw.congr_fun ?_
    intro n
    dsimp only [p]
    rw [hcneg]
    ring
  have hhead : ∑ n ∈ Finset.range (N + 1), p n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnlt : n < N + 1 := Finset.mem_range.mp hn
    have hnle : n ≤ N := by omega
    dsimp only [p]
    rw [hc_of_nat_le n hnle, zero_mul]
  have hshift : HasSum (fun k : ℕ ↦ p (k + (N + 1)))
      (yoshidaCriticalSampleLinear a ha v
        (f : YoshidaClippedSmooth a)) := by
    apply (hasSum_nat_add_iff (f := p) (N + 1)).mpr
    rw [hhead, add_zero]
    exact hpaired
  simpa only [p, c, q, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hshift

/-- Positive-frequency coefficient mass is exactly one half of the nonzero
even tail's Parseval mass. -/
theorem hasSum_sq_centeredFourierCoeff_evenTail_positive
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreEvenTailSubmodule ha N) :
    HasSum
      (fun k : ℕ ↦
        ‖centeredFourierCoeff ha
          ((f : YoshidaClippedSmooth a) : ℝ → ℂ)
          ((N + 1 + k : ℕ) : ℤ)‖ ^ 2)
      ((1 / (4 * a)) *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  let F := yoshidaClippedCircleL2 ha (f : YoshidaClippedSmooth a)
  let c : ℤ → ℂ := fun n ↦ centeredFourierCoeff ha
    ((f : YoshidaClippedSmooth a) : ℝ → ℂ) n
  have htail : F ∈ evenFourierTailSubmodule (T := 2 * a) N :=
    (mem_yoshidaPeriodicCoreEvenTailSubmodule_iff ha N f).mp hf
  have heven : F ∈ evenL2Submodule (T := 2 * a) := htail.1
  have hzero : F ∈ fourierTailSubmodule (T := 2 * a) N := htail.2
  have hcneg (n : ℤ) : c (-n) = c n := by
    dsimp only [c, F]
    rw [← fourierCoeff_yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) (-n)]
    rw [← fourierCoeff_yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) n]
    exact fourierCoeff_even_of_mem heven n
  have hc_of_nat_le (n : ℕ) (hn : n ≤ N) : c (n : ℤ) = 0 := by
    dsimp only [c, F]
    rw [← fourierCoeff_yoshidaClippedCircleL2 ha
      (f : YoshidaClippedSmooth a) (n : ℤ)]
    exact (mem_fourierTailSubmodule_iff N F).mp hzero (n : ℤ) (by
      simp only [Finset.mem_Icc]
      constructor <;> omega)
  have hc0 : c 0 = 0 := by
    simpa using hc_of_nat_le 0 (Nat.zero_le N)
  have hall : HasSum (fun n : ℤ ↦ ‖c n‖ ^ 2)
      ((2 * a)⁻¹ *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) := by
    simpa only [c, centeredFourierCoeff,
      show a - -a = 2 * a by ring, smul_eq_mul] using
        (hasSum_sq_fourierCoeffOn (neg_lt_self ha)
          (yoshidaClippedSmooth_memLp_two (f : YoshidaClippedSmooth a)))
  let p : ℕ → ℝ := fun n ↦ 2 * ‖c (n : ℤ)‖ ^ 2
  have hpaired : HasSum p
      ((2 * a)⁻¹ *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) := by
    have hraw := hall.nat_add_neg
    have hc0norm : ‖c 0‖ ^ 2 = 0 := by rw [hc0, norm_zero]; norm_num
    rw [hc0norm, add_zero] at hraw
    refine hraw.congr_fun ?_
    intro n
    dsimp only [p]
    rw [hcneg]
    ring
  have hhead : ∑ n ∈ Finset.range (N + 1), p n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnlt : n < N + 1 := Finset.mem_range.mp hn
    have hnle : n ≤ N := by omega
    dsimp only [p]
    rw [hc_of_nat_le n hnle, norm_zero]
    norm_num
  have hshift : HasSum (fun k : ℕ ↦ p (k + (N + 1)))
      ((2 * a)⁻¹ *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) := by
    apply (hasSum_nat_add_iff (f := p) (N + 1)).mpr
    rw [hhead, add_zero]
    exact hpaired
  have hhalf := hshift.mul_left (1 / 2 : ℝ)
  have hhalf' : HasSum
      (fun k : ℕ ↦ ‖c ((N + 1 + k : ℕ) : ℤ)‖ ^ 2)
      ((1 / 2 : ℝ) * ((2 * a)⁻¹ *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2)) := by
    refine hhalf.congr_fun ?_
    intro k
    dsimp only [p]
    rw [show (k + (N + 1) : ℕ) = N + 1 + k by omega]
    ring
  have hvalue : (1 / 2 : ℝ) * ((2 * a)⁻¹ *
      ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) =
      (1 / (4 * a)) *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2 := by
    field_simp [ha.ne']
    ring
  rw [hvalue] at hhalf'
  simpa only [c] using hhalf'

theorem summable_sq_evenPairedDenominator (x : ℝ) (N : ℕ) :
    Summable (fun k : ℕ ↦
      evenPairedDenominator x (N + 1 + k) ^ 2) := by
  have hminusBase :=
    (Real.summable_one_div_nat_add_rpow ((N + 1 : ℕ) - x) 2).mpr (by norm_num)
  have hplusBase :=
    (Real.summable_one_div_nat_add_rpow ((N + 1 : ℕ) + x) 2).mpr (by norm_num)
  have hminus : Summable (fun k : ℕ ↦
      1 / (x - ((N + 1 + k : ℕ) : ℝ)) ^ 2) := by
    apply hminusBase.congr
    intro k
    rw [Real.rpow_two, sq_abs]
    push_cast
    ring_nf
  have hplus : Summable (fun k : ℕ ↦
      1 / (x + ((N + 1 + k : ℕ) : ℝ)) ^ 2) := by
    apply hplusBase.congr
    intro k
    rw [Real.rpow_two, sq_abs]
    push_cast
    ring_nf
  have hmajor : Summable (fun k : ℕ ↦
      2 * (1 / (x - ((N + 1 + k : ℕ) : ℝ)) ^ 2 +
        1 / (x + ((N + 1 + k : ℕ) : ℝ)) ^ 2)) :=
    (hminus.add hplus).mul_left 2
  apply hmajor.of_nonneg_of_le
  · intro k
    positivity
  · intro k
    unfold evenPairedDenominator
    rw [← one_div_pow, ← one_div_pow]
    nlinarith [sq_nonneg
      (1 / (x - ((N + 1 + k : ℕ) : ℝ)) -
        1 / (x + ((N + 1 + k : ℕ) : ℝ)))]

private theorem negOne_zpow_neg_nat (n : ℕ) :
    (-1 : ℝ) ^ (-(n : ℤ)) = (-1 : ℝ) ^ (n : ℤ) := by
  rw [← Int.cast_negOnePow, ← Int.cast_negOnePow]
  simp

private theorem negOne_zpow_sq (z : ℤ) :
    ((-1 : ℝ) ^ z) ^ 2 = 1 := by
  rw [← zpow_natCast]
  rw [← zpow_mul]
  change (-1 : ℝ) ^ (z * (2 : ℤ)) = 1
  rw [show z * (2 : ℤ) = 2 * z by ring]
  rw [zpow_mul]
  norm_num

theorem intervalExpQuotient_critical_even_pair_eq
    {a : ℝ} (ha : 0 < a) (v : ℝ) (n : ℕ)
    (hminus : a * v - Real.pi * (n : ℝ) ≠ 0)
    (hplus : a * v + Real.pi * (n : ℝ) ≠ 0) :
    yoshidaIntervalExpQuotient a
          (yoshidaModeLaplaceExponent a (n : ℤ) (v * Complex.I)) +
        yoshidaIntervalExpQuotient a
          (yoshidaModeLaplaceExponent a (-(n : ℤ)) (v * Complex.I)) =
      (((2 * a / Real.pi * (-1 : ℝ) ^ (n : ℤ) * Real.sin (a * v) *
        evenPairedDenominator (a * v / Real.pi) n : ℝ) : ℂ)) := by
  rw [intervalExpQuotient_critical_eq_section6 ha v (n : ℤ) hminus]
  rw [intervalExpQuotient_critical_eq_section6 ha v (-(n : ℤ))]
  · norm_num only [Int.cast_neg, Int.cast_natCast]
    rw [negOne_zpow_neg_nat]
    norm_cast
    norm_num only [Int.cast_neg, Int.cast_natCast]
    unfold evenPairedDenominator
    field_simp [hminus, hplus, Real.pi_ne_zero]
    ring_nf
  · norm_num only [Int.cast_neg, Int.cast_natCast]
    simpa [sub_eq_add_neg] using hplus

/-- Infinite Cauchy--Schwarz sampling bound for the actual even tail. -/
theorem evenTail_paired_pointwise_estimate
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreEvenTailSubmodule ha N)
    {v : ℝ} (hwindow : a * |v| < Real.pi * (N + 1 : ℕ)) :
    Complex.normSq (yoshidaCriticalSampleLinear a ha v
        (f : YoshidaClippedSmooth a)) ≤
      a / Real.pi ^ 2 * Real.sin (a * v) ^ 2 *
        (∑' k : ℕ,
          evenPairedDenominator (a * v / Real.pi) (N + 1 + k) ^ 2) *
        (∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) := by
  let c : ℕ → ℂ := fun k ↦ centeredFourierCoeff ha
    ((f : YoshidaClippedSmooth a) : ℝ → ℂ)
      ((N + 1 + k : ℕ) : ℤ)
  let K : ℝ := 2 * a / Real.pi * Real.sin (a * v)
  let d : ℕ → ℝ := fun k ↦
    evenPairedDenominator (a * v / Real.pi) (N + 1 + k)
  let w : ℕ → ℂ := fun k ↦
    ((K * (-1 : ℝ) ^ ((N + 1 + k : ℕ) : ℤ) * d k : ℝ) : ℂ)
  have hz : HasSum (fun k ↦ c k * w k)
      (yoshidaCriticalSampleLinear a ha v
        (f : YoshidaClippedSmooth a)) := by
    have h := hasSum_criticalSample_evenTail_paired_exact ha N f hf v
    refine h.congr_fun ?_
    intro k
    obtain ⟨hminus, hplus⟩ := oddTail_denominators_ne ha N k hwindow
    dsimp only [c, w, K, d]
    rw [intervalExpQuotient_critical_even_pair_eq ha v (N + 1 + k)
      hminus hplus]
    ring_nf
  have hc : HasSum (fun k ↦ ‖c k‖ ^ 2)
      ((1 / (4 * a)) *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) := by
    simpa only [c] using
      hasSum_sq_centeredFourierCoeff_evenTail_positive ha N f hf
  have hdsum : Summable (fun k ↦ d k ^ 2) := by
    simpa only [d] using
      summable_sq_evenPairedDenominator (a * v / Real.pi) N
  have hd : HasSum (fun k ↦ d k ^ 2) (∑' k, d k ^ 2) := hdsum.hasSum
  have hw : HasSum (fun k ↦ ‖w k‖ ^ 2)
      (K ^ 2 * ∑' k, d k ^ 2) := by
    have hscaled := hd.mul_left (K ^ 2)
    refine hscaled.congr_fun ?_
    intro k
    dsimp only [w]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    calc
      (K * (-1 : ℝ) ^ ((N + 1 + k : ℕ) : ℤ) * d k) ^ 2 =
          K ^ 2 * (((-1 : ℝ) ^ ((N + 1 + k : ℕ) : ℤ)) ^ 2) *
            d k ^ 2 := by ring
      _ = K ^ 2 * d k ^ 2 := by rw [negOne_zpow_sq]; ring
  have hcs := normSq_hasSum_mul_le hz hc hw
  calc
    Complex.normSq (yoshidaCriticalSampleLinear a ha v
        (f : YoshidaClippedSmooth a)) ≤
      ((1 / (4 * a)) *
        ∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) *
        (K ^ 2 * ∑' k, d k ^ 2) := hcs
    _ = a / Real.pi ^ 2 * Real.sin (a * v) ^ 2 *
        (∑' k : ℕ,
          evenPairedDenominator (a * v / Real.pi) (N + 1 + k) ^ 2) *
        (∫ x : ℝ in -a..a, ‖(f : YoshidaClippedSmooth a) x‖ ^ 2) := by
      dsimp only [K, d]
      field_simp [ha.ne', Real.pi_ne_zero]
      ring

theorem abs_evenPairedDenominator_le_weightedRoot
    {y c : ℝ} {n : ℕ} (hn : 0 < n)
    (hy : |y| ≤ c) (hcden : c < Real.pi * (n : ℝ)) :
    |evenPairedDenominator (y / Real.pi) n| ≤
      1 / (n : ℝ) *
        (1 + Real.pi * n / (Real.pi * n - c)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let P : ℝ := Real.pi * (n : ℝ)
  have hP : 0 < P := by dsimp [P]; positivity
  have hylo : -c ≤ y := (abs_le.mp hy).1
  have hyhi : y ≤ c := (abs_le.mp hy).2
  have hdenC : 0 < P - c := sub_pos.mpr hcden
  have hminus : 0 < P - y := by linarith
  have hplus : 0 < P + y := by linarith
  have hxminus : y / Real.pi - (n : ℝ) < 0 := by
    rw [sub_neg]
    apply (div_lt_iff₀ Real.pi_pos).2
    dsimp only [P] at hminus
    nlinarith [Real.pi_pos]
  have hxplus : 0 < y / Real.pi + (n : ℝ) := by
    have hlt : -(n : ℝ) < y / Real.pi := by
      apply (lt_div_iff₀ Real.pi_pos).2
      dsimp only [P] at hplus
      nlinarith [Real.pi_pos]
    linarith
  have habsMinus : |1 / (y / Real.pi - (n : ℝ))| =
      Real.pi / (P - y) := by
    rw [abs_of_neg (one_div_neg.mpr hxminus)]
    have hym : y - Real.pi * (n : ℝ) ≠ 0 := by
      dsimp only [P] at hminus
      linarith
    have hmy : Real.pi * (n : ℝ) - y ≠ 0 := by
      dsimp only [P] at hminus
      linarith
    dsimp only [P]
    field_simp [Real.pi_ne_zero, hym, hmy]
    ring
  have habsPlus : |1 / (y / Real.pi + (n : ℝ))| =
      Real.pi / (P + y) := by
    rw [abs_of_pos (one_div_pos.mpr hxplus)]
    dsimp only [P]
    field_simp [Real.pi_ne_zero]
    ring
  have htriangle : |evenPairedDenominator (y / Real.pi) n| ≤
      Real.pi / (P - y) + Real.pi / (P + y) := by
    unfold evenPairedDenominator
    calc
      |1 / (y / Real.pi - (n : ℝ)) +
          1 / (y / Real.pi + (n : ℝ))| ≤
          |1 / (y / Real.pi - (n : ℝ))| +
            |1 / (y / Real.pi + (n : ℝ))| := abs_add_le _ _
      _ = Real.pi / (P - y) + Real.pi / (P + y) := by
        rw [habsMinus, habsPlus]
  have hroot : 1 / (n : ℝ) *
      (1 + Real.pi * n / (Real.pi * n - c)) =
      1 / (n : ℝ) + Real.pi / (P - c) := by
    dsimp only [P]
    field_simp [hnR.ne', hdenC.ne']
  rw [hroot]
  apply htriangle.trans
  by_cases hy0 : 0 ≤ y
  · have hfirst : Real.pi / (P - y) ≤ Real.pi / (P - c) :=
      div_le_div_of_nonneg_left Real.pi_pos.le hdenC (by linarith)
    have hsecond : Real.pi / (P + y) ≤ 1 / (n : ℝ) := by
      calc
        Real.pi / (P + y) ≤ Real.pi / P :=
          div_le_div_of_nonneg_left Real.pi_pos.le hP (by linarith)
        _ = 1 / (n : ℝ) := by
          dsimp only [P]
          field_simp [Real.pi_ne_zero, hnR.ne']
    linarith
  · have hyneg : y < 0 := lt_of_not_ge hy0
    have hfirst : Real.pi / (P - y) ≤ 1 / (n : ℝ) := by
      calc
        Real.pi / (P - y) ≤ Real.pi / P :=
          div_le_div_of_nonneg_left Real.pi_pos.le hP (by linarith)
        _ = 1 / (n : ℝ) := by
          dsimp only [P]
          field_simp [Real.pi_ne_zero, hnR.ne']
    have hsecond : Real.pi / (P + y) ≤ Real.pi / (P - c) :=
      div_le_div_of_nonneg_left Real.pi_pos.le hdenC (by linarith)
    linarith

theorem evenPairedDenominator_sq_le_weightedTermR
    {y c : ℝ} {n : ℕ} (hn : 0 < n)
    (hy : |y| ≤ c) (hcden : c < Real.pi * (n : ℝ)) :
    evenPairedDenominator (y / Real.pi) n ^ 2 ≤
      weightedTermR Real.pi c n := by
  have hroot := abs_evenPairedDenominator_le_weightedRoot hn hy hcden
  have hroot0 : 0 ≤ 1 / (n : ℝ) *
      (1 + Real.pi * n / (Real.pi * n - c)) := by
    have hden : 0 < Real.pi * (n : ℝ) - c := sub_pos.mpr hcden
    positivity
  have hsq := (sq_le_sq₀ (abs_nonneg _) hroot0).mpr hroot
  rw [sq_abs] at hsq
  unfold weightedTermR
  calc
    evenPairedDenominator (y / Real.pi) n ^ 2 ≤
        (1 / (n : ℝ) *
          (1 + Real.pi * n / (Real.pi * n - c))) ^ 2 := hsq
    _ = 1 / (n : ℝ) ^ 2 *
        (1 + Real.pi * n / (Real.pi * n - c)) ^ 2 := by ring

theorem tsum_sq_evenPairedDenominator_le_weightedTail
    {N : ℕ} (hN : 0 < N) {T v : ℝ} (hT : 0 ≤ T)
    (hv : |v| ≤ T)
    (hwindow : yoshidaA * T < piLowerR * (N + 1 : ℕ)) :
    (∑' k : ℕ,
      evenPairedDenominator (yoshidaA * v / Real.pi) (N + 1 + k) ^ 2) ≤
      weightedTail N T := by
  have ha : 0 < yoshidaA := yoshidaA_pos
  have hy : |yoshidaA * v| ≤ yoshidaA * T := by
    rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left hv ha.le
  have hpoint (k : ℕ) :
      evenPairedDenominator (yoshidaA * v / Real.pi) (N + 1 + k) ^ 2 ≤
        weightedTermR Real.pi (yoshidaA * T) (N + k + 1) := by
    have hn : 0 < N + k + 1 := by omega
    have hcast : ((N + 1 : ℕ) : ℝ) ≤ (N + k + 1 : ℕ) := by
      exact_mod_cast (show N + 1 ≤ N + k + 1 by omega)
    have hpiBase : piLowerR * (N + 1 : ℕ) ≤
        Real.pi * (N + 1 : ℕ) :=
      mul_le_mul_of_nonneg_right piLowerR_le_pi (by positivity)
    have hpiTail : Real.pi * (N + 1 : ℕ) ≤
        Real.pi * (N + k + 1 : ℕ) :=
      mul_le_mul_of_nonneg_left hcast Real.pi_pos.le
    have hden : yoshidaA * T < Real.pi * (N + k + 1 : ℕ) :=
      hwindow.trans_le (hpiBase.trans hpiTail)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      evenPairedDenominator_sq_le_weightedTermR hn hy hden
  have hleft :=
    summable_sq_evenPairedDenominator (yoshidaA * v / Real.pi) N
  have hright := summable_weightedTail_of_piLower_window hN hT hwindow
  unfold weightedTail
  exact hleft.tsum_le_tsum hpoint hright

theorem evenTail_paired_pointwise_estimate_weightedTail
    {N : ℕ} (hN : 0 < N)
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos N)
    (henergy :
      (∫ x : ℝ in -yoshidaA..yoshidaA,
        ‖((f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) x‖ ^ 2) = 1)
    {T v : ℝ} (hT : 0 ≤ T) (hv : |v| ≤ T)
    (hwindow : yoshidaA * T < piLowerR * (N + 1 : ℕ)) :
    Complex.normSq (yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v
        (f : YoshidaClippedSmooth yoshidaA)) ≤
      yoshidaA / Real.pi ^ 2 * Real.sin (yoshidaA * v) ^ 2 *
        weightedTail N T := by
  have hpiBase : piLowerR * (N + 1 : ℕ) ≤
      Real.pi * (N + 1 : ℕ) :=
    mul_le_mul_of_nonneg_right piLowerR_le_pi (by positivity)
  have hnonres : yoshidaA * |v| < Real.pi * (N + 1 : ℕ) :=
    (mul_le_mul_of_nonneg_left hv yoshidaA_pos.le).trans_lt
      (hwindow.trans_le hpiBase)
  have hraw := evenTail_paired_pointwise_estimate
    yoshidaA_pos N f hf hnonres
  rw [henergy, mul_one] at hraw
  have hmass := tsum_sq_evenPairedDenominator_le_weightedTail
    hN hT hv hwindow
  have hscale : 0 ≤ yoshidaA / Real.pi ^ 2 *
      Real.sin (yoshidaA * v) ^ 2 :=
    mul_nonneg (div_nonneg yoshidaA_pos.le (sq_nonneg _)) (sq_nonneg _)
  exact hraw.trans (mul_le_mul_of_nonneg_left hmass hscale)

theorem evenTail_paired_central_energy_estimate6_6
    {N : ℕ} (hN : 0 < N) {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos N)
    (henergy :
      (∫ x : ℝ in -yoshidaA..yoshidaA,
        ‖((f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) x‖ ^ 2) = 1)
    (hwindow : yoshidaA * T < piLowerR * (N + 1 : ℕ)) :
    C / (2 * Real.pi) *
        clippedCentralEnergy yoshidaA yoshidaA_pos
          (f : YoshidaClippedSmooth yoshidaA) T ≤
      yoshidaA * C / (2 * Real.pi ^ 3) *
        (T - Real.sin (2 * yoshidaA * T) / (2 * yoshidaA)) *
          weightedTail N T := by
  apply paired_central_energy_estimate6_6 yoshidaA_pos hC hT
    (f : YoshidaClippedSmooth yoshidaA)
  intro v hv
  apply evenTail_paired_pointwise_estimate_weightedTail hN f hf henergy hT
  · exact abs_le.mpr ⟨by linarith [hv.1], hv.2⟩
  · exact hwindow

/-! ## Complete Section 6 estimate -/

theorem evenOneNinetyNineTail_low_digamma_loss_le
    {tZero : ℝ} (ht : IsYoshidaTZero tZero)
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)
    (henergy :
      (∫ x : ℝ in -yoshidaA..yoshidaA,
        ‖((f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) x‖ ^ 2) = 1) :
    -(1 / (2 * Real.pi)) *
        (∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v *
            Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
              yoshidaA_pos v (f : YoshidaClippedSmooth yoshidaA))) ≤
      lowIntervalPenalty 199 tZero := by
  let q : ℝ → ℝ := fun v ↦
    Complex.normSq (yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v
      (f : YoshidaClippedSmooth yoshidaA))
  let K : ℝ := yoshidaA / Real.pi ^ 2 * weightedTail 199 tZero
  have htUpper : tZero ≤ (51 / 25 : ℝ) := yoshidaTZero_le_51_div_25 ht
  have hwindow : yoshidaA * tZero < piLowerR * (199 + 1 : ℕ) := by
    calc
      yoshidaA * tZero ≤ yoshidaA * (51 / 25 : ℝ) :=
        mul_le_mul_of_nonneg_left htUpper yoshidaA_pos.le
      _ ≤ (((lowCUpperQ : ℚ) : ℝ)) :=
        yoshidaA_mul_51_div_25_le_lowCUpper
      _ < piLowerR * (199 + 1 : ℕ) := by
        norm_num [lowCUpperQ, piLowerR]
  have htail0 : 0 ≤ weightedTail 199 tZero := weightedTail_nonneg 199 tZero
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (div_nonneg yoshidaA_pos.le (sq_nonneg Real.pi)) htail0
  have hqpoint {v : ℝ} (hv : v ∈ Set.Icc (-tZero) tZero) : q v ≤ K := by
    have habs : |v| ≤ tZero := abs_le.mpr ⟨by linarith [hv.1], hv.2⟩
    have hsample := evenTail_paired_pointwise_estimate_weightedTail
      (N := 199) (by norm_num) f hf henergy ht.1.le habs hwindow
    dsimp only [q, K]
    calc
      Complex.normSq (yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v
          (f : YoshidaClippedSmooth yoshidaA)) ≤
        yoshidaA / Real.pi ^ 2 * Real.sin (yoshidaA * v) ^ 2 *
          weightedTail 199 tZero := hsample
      _ = (yoshidaA / Real.pi ^ 2 * weightedTail 199 tZero) *
          Real.sin (yoshidaA * v) ^ 2 := by ring
      _ ≤ (yoshidaA / Real.pi ^ 2 * weightedTail 199 tZero) * 1 := by
        exact mul_le_mul_of_nonneg_left (Real.sin_sq_le_one _) hK0
      _ = yoshidaA / Real.pi ^ 2 * weightedTail 199 tZero := by ring
  have hpoint {v : ℝ} (hv : v ∈ Set.Icc (-tZero) tZero) :
      -digammaQuarterVerticalRe v * q v ≤
        -digammaQuarterVerticalRe v * K := by
    exact mul_le_mul_of_nonneg_left (hqpoint hv)
      (neg_nonneg.mpr
        (digammaQuarterVerticalRe_nonpos_of_abs_le_yoshidaTZero ht
          (abs_le.mpr ⟨by linarith [hv.1], hv.2⟩)))
  have hqCont : Continuous q := by
    dsimp only [q]
    exact Complex.continuous_normSq.comp
      (continuous_yoshidaCriticalSample yoshidaA_pos
        (f : YoshidaClippedSmooth yoshidaA))
  have hgCont : Continuous digammaQuarterVerticalRe :=
    continuous_re_digamma_quarter_vertical
  have hmono :
      (∫ v : ℝ in -tZero..tZero,
        -digammaQuarterVerticalRe v * q v) ≤
      ∫ v : ℝ in -tZero..tZero,
        -digammaQuarterVerticalRe v * K := by
    exact intervalIntegral.integral_mono_on (by linarith [ht.1])
      ((hgCont.neg.mul hqCont).intervalIntegrable (-tZero) tZero)
      ((hgCont.neg.mul continuous_const).intervalIntegrable (-tZero) tZero)
      (fun v hv ↦ hpoint hv)
  have hhalf := lowDigammaHalfIntegralBound_of_isYoshidaTZero ht
  have hhalf' :
      -(∫ v : ℝ in -tZero..tZero, digammaQuarterVerticalRe v) ≤
        2 * (2773 / 1000 : ℝ) := by
    unfold LowDigammaHalfIntegralBound at hhalf
    linarith
  have hscaled :
      K * (-(∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v)) ≤
        K * (2 * (2773 / 1000 : ℝ)) :=
    mul_le_mul_of_nonneg_left hhalf' hK0
  have hnegIntegral :
      -(∫ v : ℝ in -tZero..tZero,
        digammaQuarterVerticalRe v * q v) ≤
        K * (2 * (2773 / 1000 : ℝ)) := by
    calc
      -(∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v * q v) =
        ∫ v : ℝ in -tZero..tZero,
          -digammaQuarterVerticalRe v * q v := by
            rw [← intervalIntegral.integral_neg]
            apply intervalIntegral.integral_congr
            intro v _
            ring
      _ ≤ ∫ v : ℝ in -tZero..tZero,
          -digammaQuarterVerticalRe v * K := hmono
      _ = K * (-(∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v)) := by
            rw [← intervalIntegral.integral_neg]
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro v _
            ring
      _ ≤ K * (2 * (2773 / 1000 : ℝ)) := hscaled
  calc
    -(1 / (2 * Real.pi)) *
        (∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v *
            Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
              yoshidaA_pos v (f : YoshidaClippedSmooth yoshidaA))) =
      (1 / (2 * Real.pi)) *
        (-(∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v * q v)) := by
            dsimp only [q]
            ring
    _ ≤ (1 / (2 * Real.pi)) *
        (K * (2 * (2773 / 1000 : ℝ))) :=
      mul_le_mul_of_nonneg_left hnegIntegral (by positivity)
    _ = lowIntervalPenalty 199 tZero := by
      dsimp only [K]
      unfold lowIntervalPenalty
      field_simp [Real.pi_ne_zero]

theorem evenOneNinetyNineTail_clippedSection6DigammaLowerEstimate
    {tZero : ℝ} (ht : IsYoshidaTZero tZero)
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)
    (henergy :
      (∫ x : ℝ in -yoshidaA..yoshidaA,
        ‖((f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) x‖ ^ 2) = 1)
    (hMassInt : Integrable (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v
        (f : YoshidaClippedSmooth yoshidaA))))
    (hDigammaInt : Integrable (fun v : ℝ ↦
      digammaQuarterVerticalRe v *
        Complex.normSq (yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v
          (f : YoshidaClippedSmooth yoshidaA))))
    (hParseval : clippedSpectralMass yoshidaA yoshidaA_pos
      (f : YoshidaClippedSmooth yoshidaA) = 1) :
    ClippedSection6DigammaLowerEstimate 199 tZero 700
      yoshidaA yoshidaA_pos (f : YoshidaClippedSmooth yoshidaA) := by
  have hC50 : 0 ≤ digammaQuarterVerticalRe 50 := by
    have h : (1609 / 500 : ℝ) ≤ digammaQuarterVerticalRe 50 := by
      simpa [digammaQuarterVerticalRe] using
        DigammaNumericBounds.digamma_quarter_vertical_re_fifty_lower
    exact (by norm_num : (0 : ℝ) ≤ 1609 / 500).trans h
  have hmono := re_digamma_quarter_vertical_monotoneOn
    (show (50 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (700 : ℝ) ∈ Set.Ici 0 by norm_num)
    (by norm_num : (50 : ℝ) ≤ 700)
  change digammaQuarterVerticalRe 50 ≤
    digammaQuarterVerticalRe 700 at hmono
  have hC0 : 0 ≤ digammaQuarterVerticalRe 700 := hC50.trans hmono
  have hwindow : yoshidaA * 700 < piLowerR * (199 + 1 : ℕ) := by
    calc
      yoshidaA * 700 < (347 / 1000 : ℝ) * 700 := by
        exact mul_lt_mul_of_pos_right yoshidaA_lt_347_div_1000 (by norm_num)
      _ < piLowerR * (199 + 1 : ℕ) := by
        norm_num [piLowerR]
  have hHigh := evenTail_paired_central_energy_estimate6_6
    (N := 199) (C := digammaQuarterVerticalRe 700) (T := 700)
    (by norm_num) hC0 (by norm_num) f hf henergy hwindow
  apply clippedSection6DigammaLowerEstimate_of_split yoshidaA_pos ht
    (by norm_num) (by linarith [yoshidaTZero_le_51_div_25 ht])
    (f : YoshidaClippedSmooth yoshidaA) hMassInt hDigammaInt hParseval
  · simpa [highFrequencyPenalty, oscillatoryWindow] using hHigh
  · exact evenOneNinetyNineTail_low_digamma_loss_le ht f hf henergy

/-- The normalized actual even tail satisfies the source coercivity threshold
with all Section 6 analytic obligations discharged. -/
theorem evenOneNinetyNineTail_clipped_form_value_ge_102_div_25_of_unit_energy
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)
    (henergy :
      (∫ x : ℝ in -yoshidaA..yoshidaA,
        ‖((f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) x‖ ^ 2) = 1) :
    (102 / 25 : ℝ) ≤ clippedCriticalFormValue yoshidaA yoshidaA_pos
      (f : YoshidaClippedSmooth yoshidaA) := by
  have hMassInt :=
    YoshidaSectionSixAnalytic.integrable_normSq_yoshidaCriticalSample yoshidaA_pos
    (f : YoshidaClippedSmooth yoshidaA)
  have hDigammaInt :=
    integrable_digammaQuarterVerticalRe_mul_normSq_yoshidaCriticalSample
      yoshidaA_pos (f : YoshidaClippedSmooth yoshidaA)
  have hParseval : clippedSpectralMass yoshidaA yoshidaA_pos
      (f : YoshidaClippedSmooth yoshidaA) = 1 := by
    rw [clippedSpectralMass_eq_intervalEnergy yoshidaA_pos
      (f : YoshidaClippedSmooth yoshidaA), henergy]
  have hDigamma := evenOneNinetyNineTail_clippedSection6DigammaLowerEstimate
    isYoshidaTZero_yoshidaTZero f hf henergy hMassInt hDigammaInt hParseval
  have hDigammaInt' : Integrable (fun v : ℝ ↦
      (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re *
        Complex.normSq (yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v
          (f : YoshidaClippedSmooth yoshidaA))) := by
    simpa only [digammaQuarterVerticalRe] using hDigammaInt
  have hArch := clippedSection6ArchLowerEstimate_of_digamma_parseval
    yoshidaA_pos (f : YoshidaClippedSmooth yoshidaA)
    hDigammaInt' hMassInt hParseval hDigamma
  have hPolar := even_polar_section6_lower_bound yoshidaA_pos
    (f : YoshidaClippedSmooth yoshidaA)
    (evenTail_pointwise_even yoshidaA_pos 199 f hf)
  exact even_canonical_clipped_form_value_ge_102_div_25
    (f : YoshidaClippedSmooth yoshidaA) hPolar hArch

/-- Homogeneous source coercivity on the actual canonical even tail. -/
theorem evenOneNinetyNineTail_clipped_form_value_coercive
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199) :
    (102 / 25 : ℝ) * clippedIntervalEnergy
        (f : YoshidaClippedSmooth yoshidaA) ≤
      clippedCriticalFormValue yoshidaA yoshidaA_pos
        (f : YoshidaClippedSmooth yoshidaA) := by
  let E : ℝ := clippedIntervalEnergy (f : YoshidaClippedSmooth yoshidaA)
  have hEnonneg : 0 ≤ E := by
    dsimp only [E, clippedIntervalEnergy]
    exact intervalIntegral.integral_nonneg (by linarith [yoshidaA_pos])
      (fun _ _ ↦ sq_nonneg _)
  by_cases hEzero : E = 0
  · have hfSmoothZero : (f : YoshidaClippedSmooth yoshidaA) = 0 :=
      eq_zero_of_clippedIntervalEnergy_eq_zero yoshidaA_pos
        (f : YoshidaClippedSmooth yoshidaA) (by simpa only [E] using hEzero)
    have hfZero : f = 0 := Subtype.ext hfSmoothZero
    subst f
    simp [clippedIntervalEnergy, clippedCriticalFormValue]
  · have hEpos : 0 < E := lt_of_le_of_ne hEnonneg (Ne.symm hEzero)
    let c : ℂ := (((Real.sqrt E)⁻¹ : ℝ) : ℂ)
    let g : YoshidaClippedPeriodicCore yoshidaA := c • f
    have hgf : g ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199 := by
      dsimp only [g]
      exact (yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199).smul_mem c hf
    have hscale : E * ‖c‖ ^ 2 = 1 := by
      dsimp only [c]
      rw [Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg E)),
        inv_pow, Real.sq_sqrt hEpos.le]
      exact mul_inv_cancel₀ hEpos.ne'
    have hgEnergy : clippedIntervalEnergy
        (g : YoshidaClippedSmooth yoshidaA) = 1 := by
      change clippedIntervalEnergy
          (c • (f : YoshidaClippedSmooth yoshidaA)) = 1
      rw [clippedIntervalEnergy_smul, mul_comm, hscale]
    have hunit : (102 / 25 : ℝ) ≤
        clippedCriticalFormValue yoshidaA yoshidaA_pos
          (g : YoshidaClippedSmooth yoshidaA) := by
      apply evenOneNinetyNineTail_clipped_form_value_ge_102_div_25_of_unit_energy
        g hgf
      simpa only [clippedIntervalEnergy] using hgEnergy
    have hmul := mul_le_mul_of_nonneg_left hunit hEnonneg
    dsimp only [E] at hmul ⊢
    calc
      (102 / 25 : ℝ) * clippedIntervalEnergy
          (f : YoshidaClippedSmooth yoshidaA) =
          clippedIntervalEnergy (f : YoshidaClippedSmooth yoshidaA) *
            (102 / 25 : ℝ) := by ring
      _ ≤ clippedIntervalEnergy (f : YoshidaClippedSmooth yoshidaA) *
          clippedCriticalFormValue yoshidaA yoshidaA_pos
            (g : YoshidaClippedSmooth yoshidaA) := hmul
      _ = clippedIntervalEnergy (f : YoshidaClippedSmooth yoshidaA) *
          (‖c‖ ^ 2 * clippedCriticalFormValue yoshidaA yoshidaA_pos
            (f : YoshidaClippedSmooth yoshidaA)) := by
        congr 1
        change clippedCriticalFormValue yoshidaA yoshidaA_pos
            (c • (f : YoshidaClippedSmooth yoshidaA)) = _
        exact clippedCriticalFormValue_smul yoshidaA_pos c
          (f : YoshidaClippedSmooth yoshidaA)
      _ = clippedCriticalFormValue yoshidaA yoshidaA_pos
          (f : YoshidaClippedSmooth yoshidaA) := by
        rw [← mul_assoc]
        change E * ‖c‖ ^ 2 * _ = _
        rw [hscale, one_mul]

/-! ## Bundled positive Hermitian form -/

/-- The actual periodic even tail beginning at mode `200`. -/
abbrev YoshidaEvenOneNinetyNineTail :=
  yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199

instance evenOneNinetyNineTailAddCommGroup :
    AddCommGroup YoshidaEvenOneNinetyNineTail := by
  change AddCommGroup
    ↥(yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)
  exact Submodule.addCommGroup
    (R := ℂ) (M := YoshidaClippedPeriodicCore yoshidaA)
    (yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)

instance evenOneNinetyNineTailModule :
    @Module ℂ YoshidaEvenOneNinetyNineTail Complex.instSemiring
      (@AddCommGroup.toAddCommMonoid YoshidaEvenOneNinetyNineTail
        evenOneNinetyNineTailAddCommGroup) := by
  letI : AddCommGroup YoshidaEvenOneNinetyNineTail :=
    evenOneNinetyNineTailAddCommGroup
  exact Submodule.module
    (R := ℂ) (M := YoshidaClippedPeriodicCore yoshidaA)
    (yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)

/-- Canonical inclusion of the even tail into the clipped smooth carrier. -/
def evenOneNinetyNineTailToClippedSmooth :
    YoshidaEvenOneNinetyNineTail →ₗ[ℂ] YoshidaClippedSmooth yoshidaA :=
  (yoshidaClippedPeriodicCoreSubmodule yoshidaA).subtype.comp
    (yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199).subtype

@[simp] theorem evenOneNinetyNineTailToClippedSmooth_apply
    (f : YoshidaEvenOneNinetyNineTail) :
    evenOneNinetyNineTailToClippedSmooth f =
      ((f : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) :=
  rfl

/-- The production critical form restricted to the actual even tail. -/
def evenOneNinetyNineTailCriticalForm :
    YoshidaEvenOneNinetyNineTail →ₗ⋆[ℂ]
      YoshidaEvenOneNinetyNineTail →ₗ[ℂ] ℂ :=
  (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos).comp
      evenOneNinetyNineTailToClippedSmooth
    |>.compl₂ evenOneNinetyNineTailToClippedSmooth

@[simp] theorem evenOneNinetyNineTailCriticalForm_apply
    (f g : YoshidaEvenOneNinetyNineTail) :
    evenOneNinetyNineTailCriticalForm f g =
      yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f)
        (evenOneNinetyNineTailToClippedSmooth g) :=
  rfl

theorem evenOneNinetyNineTailCriticalForm_coercive
    (f : YoshidaEvenOneNinetyNineTail) :
    (102 / 25 : ℝ) * clippedIntervalEnergy
        (evenOneNinetyNineTailToClippedSmooth f) ≤
      (evenOneNinetyNineTailCriticalForm f f).re := by
  exact evenOneNinetyNineTail_clipped_form_value_coercive
    (f : YoshidaClippedPeriodicCore yoshidaA) f.property

private theorem evenOneNinetyNineTailIntervalEnergy_nonneg
    (f : YoshidaEvenOneNinetyNineTail) :
    0 ≤ clippedIntervalEnergy (evenOneNinetyNineTailToClippedSmooth f) := by
  unfold clippedIntervalEnergy
  exact intervalIntegral.integral_nonneg (by linarith [yoshidaA_pos])
    (fun _ _ ↦ sq_nonneg _)

/-- The actual even tail carries a positive definite critical form, obtained
from the proved `102 / 25` coercivity and source faithfulness. -/
def evenOneNinetyNineTailPositiveHermitianForm :
    @PositiveHermitianForm YoshidaEvenOneNinetyNineTail
      evenOneNinetyNineTailAddCommGroup evenOneNinetyNineTailModule where
  form := evenOneNinetyNineTailCriticalForm
  conj_apply f g := by
    exact yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos
      (evenOneNinetyNineTailToClippedSmooth f)
      (evenOneNinetyNineTailToClippedSmooth g)
  re_apply_self_nonneg f := by
    have hcoercive := evenOneNinetyNineTailCriticalForm_coercive f
    have henergy := evenOneNinetyNineTailIntervalEnergy_nonneg f
    have hC : 0 < (102 / 25 : ℝ) := by norm_num
    exact (mul_nonneg hC.le henergy).trans hcoercive
  definite f hform := by
    have hcoercive := evenOneNinetyNineTailCriticalForm_coercive f
    have henergy := evenOneNinetyNineTailIntervalEnergy_nonneg f
    have hC : 0 < (102 / 25 : ℝ) := by norm_num
    have hformRe : (evenOneNinetyNineTailCriticalForm f f).re = 0 := by
      simpa using congrArg Complex.re hform
    have henergyZero : clippedIntervalEnergy
        (evenOneNinetyNineTailToClippedSmooth f) = 0 := by
      apply le_antisymm
      · apply nonpos_of_mul_nonpos_right
        · simpa only [hformRe] using hcoercive
        · exact hC
      · exact henergy
    have hfSmooth : evenOneNinetyNineTailToClippedSmooth f = 0 :=
      eq_zero_of_clippedIntervalEnergy_eq_zero yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f) henergyZero
    apply Subtype.ext
    apply Subtype.ext
    exact hfSmooth

theorem evenOneNinetyNineTailPositiveHermitianForm_coercive
    (f : YoshidaEvenOneNinetyNineTail) :
    (102 / 25 : ℝ) * clippedIntervalEnergy
        (evenOneNinetyNineTailToClippedSmooth f) ≤
      ((@PositiveHermitianForm.form YoshidaEvenOneNinetyNineTail
        evenOneNinetyNineTailAddCommGroup evenOneNinetyNineTailModule
        evenOneNinetyNineTailPositiveHermitianForm) f f).re := by
  simpa [evenOneNinetyNineTailPositiveHermitianForm] using
    evenOneNinetyNineTailCriticalForm_coercive f

end ArithmeticHodge.Analysis.YoshidaEvenHomogeneousCoercivity
