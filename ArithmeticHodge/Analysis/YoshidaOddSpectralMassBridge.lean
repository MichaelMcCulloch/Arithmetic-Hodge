import ArithmeticHodge.Analysis.YoshidaClippedCriticalForm
import ArithmeticHodge.Analysis.YoshidaClippedCircleFaithful
import ArithmeticHodge.Analysis.YoshidaCauchyPairing
import ArithmeticHodge.Analysis.YoshidaOddTailPaired

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Real Set
open scoped ComplexConjugate Convolution FourierTransform

namespace ArithmeticHodge.Analysis.YoshidaOddSpectralMassBridge

open DigammaTrapezoid
open YoshidaCoercivityNumerics
open YoshidaClippedCircleBridge
open YoshidaClippedCircleFaithful
open YoshidaCauchyPairing
open YoshidaSectionSixAnalytic

/-!
# Spectral mass for Yoshida's clipped periodic odd tail

The clipped critical sample has an endpoint-aware `O(1 / |v|)` estimate on
the whole algebraic carrier.  This makes its norm square integrable.  For the
periodic odd tail, autocorrelation Fourier inversion then identifies the
normalized spectral mass with the interval energy.
-/

/-- The unweighted critical-line norm square is integrable for every clipped
smooth function. -/
theorem integrable_normSq_yoshidaCriticalSample
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    Integrable (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) := by
  let D : ℝ := yoshidaCriticalDecayConstant a f
  let K : ℝ := 2 * D ^ 2
  let q : ℝ → ℝ := fun v ↦ (1 + v ^ 2)⁻¹
  let S : Set ℝ := Set.Icc (-1 : ℝ) 1
  have hD : 0 ≤ D := by
    exact yoshidaCriticalDecayConstant_nonneg ha f
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hcontinuous : Continuous (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) :=
    Complex.continuous_normSq.comp
      (continuous_yoshidaCriticalSample ha f)
  have hcompact : IntegrableOn (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) S := by
    exact hcontinuous.continuousOn.integrableOn_compact isCompact_Icc
  have hq : Integrable q := by
    simpa only [q] using integrable_inv_one_add_sq
  have hmajor : Integrable (fun v ↦ K * q v) := hq.const_mul K
  have htail : IntegrableOn (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) Sᶜ := by
    apply hmajor.integrableOn.mono'
    · exact hcontinuous.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
      have habs : 1 < |v| := by
        by_contra h
        apply hv
        exact abs_le.mp (le_of_not_gt h)
      have hv0 : v ≠ 0 := abs_pos.mp (zero_lt_one.trans habs)
      have hs := yoshidaCriticalSample_norm_le_inv_abs ha v hv0 f
      have hsSq :
          Complex.normSq (yoshidaCriticalSampleLinear a ha v f) ≤
            D ^ 2 / v ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        have habs0 : 0 < |v| := abs_pos.mpr hv0
        have hs' :
            ‖yoshidaCriticalSampleLinear a ha v f‖ ≤ D / |v| := by
          simpa only [D] using hs
        have hright : 0 ≤ D / |v| := div_nonneg hD (abs_nonneg v)
        have hsq := sq_le_sq₀ (norm_nonneg _) hright |>.2 hs'
        simpa only [div_pow, sq_abs] using hsq
      have hrecip : 1 / v ^ 2 ≤ 2 / (1 + v ^ 2) := by
        have hvSq : 1 < v ^ 2 := by
          rw [← sq_abs]
          nlinarith
        rw [div_le_div_iff₀ (by positivity : 0 < v ^ 2)
          (by positivity : 0 < 1 + v ^ 2)]
        nlinarith
      have htailBound :
          Complex.normSq (yoshidaCriticalSampleLinear a ha v f) ≤
            K * q v := by
        calc
          Complex.normSq (yoshidaCriticalSampleLinear a ha v f) ≤
              D ^ 2 / v ^ 2 := hsSq
          _ ≤ D ^ 2 * (2 / (1 + v ^ 2)) := by
            have hmul := mul_le_mul_of_nonneg_left hrecip (sq_nonneg D)
            calc
              D ^ 2 / v ^ 2 = D ^ 2 * (1 / v ^ 2) := by ring
              _ ≤ D ^ 2 * (2 / (1 + v ^ 2)) := hmul
          _ = K * q v := by
            dsimp only [K, q]
            ring
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
      exact htailBound
  rw [← integrableOn_univ]
  simpa only [S, union_compl_self] using hcompact.union htail

/-- The quarter-line digamma kernel times the critical-line norm square is
integrable on the whole clipped carrier. -/
theorem integrable_digammaQuarterVerticalRe_mul_normSq_yoshidaCriticalSample
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    Integrable (fun v : ℝ ↦
      digammaQuarterVerticalRe v *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) := by
  have hcross := yoshidaClippedCriticalCrossIntegrand_integrable ha f f
  have harchC : Integrable (fun v : ℝ ↦
      ((((digammaQuarterVerticalRe v - Real.log Real.pi) *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f) : ℝ) : ℂ))) := by
    apply hcross.congr
    filter_upwards [] with v
    simpa only [digammaQuarterVerticalRe] using
      criticalCrossIntegrand_self_eq_ofReal ha f v
  have harchR : Integrable (fun v : ℝ ↦
      (digammaQuarterVerticalRe v - Real.log Real.pi) *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) := by
    simpa using harchC.re
  have hlog : Integrable (fun v : ℝ ↦
      Real.log Real.pi *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) :=
    (integrable_normSq_yoshidaCriticalSample ha f).const_mul _
  apply (harchR.add hlog).congr
  filter_upwards [] with v
  simp only [Pi.add_apply]
  ring

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
    have hneg : (-(r : ℝ)) ∈ Set.Ioc (-a) a := by
      exact ⟨by linarith, by linarith [hr.1]⟩
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
      (f : YoshidaClippedSmooth a) :
      CenteredAddCircle a → ℂ) =ᵐ[AddCircle.haarAddCircle]
      centeredLift a ((f : YoshidaClippedSmooth a) : ℝ → ℂ) := by
    simpa only [yoshidaClippedCircleL2] using hright
  have hrightNeg := (circleNegMeasurePreserving (T := 2 * a)).quasiMeasurePreserving
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

private theorem clippedReflection_eq_neg_of_oddTail
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule ha N) :
    clippedReflection (f : YoshidaClippedSmooth a) =
      -(f : YoshidaClippedSmooth a) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  let F := yoshidaClippedCircleL2 ha (f : YoshidaClippedSmooth a)
  have htail : F ∈ oddFourierTailSubmodule (T := 2 * a) N :=
    (mem_yoshidaPeriodicCoreOddTailSubmodule_iff ha N f).mp hf
  have hodd : reflectionL2 (T := 2 * a) F = -F :=
    (mem_oddL2Submodule_iff F).mp htail.1
  apply yoshidaClippedCircleL2_injective ha
  calc
    yoshidaClippedCircleL2 ha
        (clippedReflection (f : YoshidaClippedSmooth a)) =
        reflectionL2 (T := 2 * a) F :=
      yoshidaClippedCircleL2_clippedReflection ha f
    _ = -F := hodd
    _ = yoshidaClippedCircleL2 ha
        (-(f : YoshidaClippedSmooth a)) := by
      change -(yoshidaClippedCircleL2Linear ha
        (f : YoshidaClippedSmooth a)) =
        yoshidaClippedCircleL2Linear ha
          (-(f : YoshidaClippedSmooth a))
      exact (map_neg (yoshidaClippedCircleL2Linear ha)
        (f : YoshidaClippedSmooth a)).symm

/-- Membership in the periodic-core odd tail is genuine pointwise oddness on
the clipped representative, not merely an `L²` parity statement. -/
theorem oddTail_pointwise_odd
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule ha N) (x : ℝ) :
    (f : YoshidaClippedSmooth a) (-x) =
      -(f : YoshidaClippedSmooth a) x := by
  have hreflect := clippedReflection_eq_neg_of_oddTail ha N f hf
  have hfun := congrArg Subtype.val hreflect
  have h := congrFun hfun x
  simpa only [clippedReflection, Submodule.coe_neg, Pi.neg_apply] using h

private theorem oddTail_endpoint_zero
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule ha N) :
    (f : YoshidaClippedSmooth a) (-a) = 0 ∧
      (f : YoshidaClippedSmooth a) a = 0 := by
  have hodd : (f : YoshidaClippedSmooth a) (-a) =
      -(f : YoshidaClippedSmooth a) a :=
    oddTail_pointwise_odd ha N f hf a
  have hperiod := periodicCore_endpoint_eq ha f
  have hzero : (f : YoshidaClippedSmooth a) a = 0 := by
    have htwo : (2 : ℂ) * (f : YoshidaClippedSmooth a) a = 0 := by
      calc
        (2 : ℂ) * (f : YoshidaClippedSmooth a) a =
            (f : YoshidaClippedSmooth a) a +
              (f : YoshidaClippedSmooth a) a := two_mul _
        _ = (f : YoshidaClippedSmooth a) (-a) +
              (f : YoshidaClippedSmooth a) a := by rw [hperiod]
        _ = -(f : YoshidaClippedSmooth a) a +
              (f : YoshidaClippedSmooth a) a := by rw [hodd]
        _ = 0 := neg_add_cancel _
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact ⟨hperiod.trans hzero, hzero⟩

private theorem continuous_oddTail_clippedFunction
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule ha N) :
    Continuous ((f : YoshidaClippedSmooth a) : ℝ → ℂ) := by
  obtain ⟨hneg, hpos⟩ := oddTail_endpoint_zero ha N f hf
  let S : Set ℝ := Set.Icc (-a) a
  have hfront : ∀ x ∈ frontier S,
      ((f : YoshidaClippedSmooth a) : ℝ → ℂ) x = 0 := by
    intro x hx
    have hx' : x ∈ ({-a, a} : Set ℝ) := by
      simpa only [S, frontier_Icc (by linarith : -a ≤ a)] using hx
    rcases hx' with (rfl | rfl)
    · exact hneg
    · exact hpos
  have hpiece : Continuous (S.piecewise
      ((f : YoshidaClippedSmooth a) : ℝ → ℂ) 0) := by
    apply continuous_piecewise hfront
    · simpa only [S, isClosed_Icc.closure_eq] using
        (f : YoshidaClippedSmooth a).property.1.continuousOn
    · exact continuousOn_const
  have heq : ((f : YoshidaClippedSmooth a) : ℝ → ℂ) =
      S.piecewise ((f : YoshidaClippedSmooth a) : ℝ → ℂ) 0 := by
    funext x
    by_cases hx : x ∈ S
    · simp only [Set.piecewise, hx, if_true]
    · rw [yoshidaClippedSmooth_eq_zero_outside
        (f : YoshidaClippedSmooth a) (by simpa only [S] using hx)]
      simp only [Set.piecewise, hx, if_false, Pi.zero_apply]
  rw [heq]
  exact hpiece

private theorem hasCompactSupport_clippedFunction
    {a : ℝ} (f : YoshidaClippedSmooth a) :
    HasCompactSupport (f : ℝ → ℂ) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  by_contra hmem
  exact hx (yoshidaClippedSmooth_eq_zero_outside f hmem)

/-- Fourier inversion of the autocorrelation gives exact Plancherel mass for
the actual infinite periodic odd tail. -/
theorem clippedSpectralMass_eq_intervalEnergy_of_oddTail
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule ha N) :
    clippedSpectralMass a ha (f : YoshidaClippedSmooth a) =
      ∫ x : ℝ in -a..a,
        ‖((f : YoshidaClippedSmooth a) : ℝ → ℂ) x‖ ^ 2 := by
  let g : ℝ → ℂ := (f : YoshidaClippedSmooth a)
  let c : ℝ := 2 * Real.pi
  let q : ℝ → ℝ := fun v ↦
    Complex.normSq (yoshidaCriticalSampleLinear a ha v
      (f : YoshidaClippedSmooth a))
  let H : ℝ → ℂ := crossCorrelation g g
  have hc : c ≠ 0 := by
    dsimp only [c]
    positivity
  have hgInt : Integrable g := by
    exact (f : YoshidaClippedSmooth a).property.1.continuousOn.integrableOn_Icc
      |>.integrable_of_forall_notMem_eq_zero
        (fun x hx ↦ yoshidaClippedSmooth_eq_zero_outside
          (f : YoshidaClippedSmooth a) hx)
  have hgCont : Continuous g := by
    simpa only [g] using continuous_oddTail_clippedFunction ha N f hf
  have hgCompact : HasCompactSupport g := by
    simpa only [g] using
      hasCompactSupport_clippedFunction (f : YoshidaClippedSmooth a)
  have hstarInt : Integrable (starReflection g) := by
    have hneg : Integrable (fun x : ℝ ↦ g (-x)) := hgInt.comp_neg
    simpa only [starReflection, RCLike.star_def] using
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hneg
  have hHInt : Integrable H := by
    exact hstarInt.integrable_convolution
      (ContinuousLinearMap.mul ℂ ℂ) hgInt
  have hHCont : Continuous H := by
    exact hgCompact.continuous_convolution_right
      (ContinuousLinearMap.mul ℂ ℂ)
      hstarInt.locallyIntegrable hgCont
  have hFourierSq : Integrable (fun w : ℝ ↦
      Complex.normSq (FourierTransform.fourier g w)) := by
    have hscaled :=
      (integrable_normSq_yoshidaCriticalSample ha
        (f : YoshidaClippedSmooth a)).comp_mul_left' (R := c) hc
    apply hscaled.congr
    filter_upwards [] with w
    have harg : c * w / (2 * Real.pi) = w := by
      dsimp only [c]
      field_simp [Real.pi_ne_zero]
    rw [yoshidaCriticalSample_eq_fourier ha (c * w)
      (f : YoshidaClippedSmooth a), harg]
  have hprod : Integrable (fun w : ℝ ↦
      star (FourierTransform.fourier g w) *
        FourierTransform.fourier g w) := by
    have hFourierSqC : Integrable (fun w : ℝ ↦
        ((Complex.normSq (FourierTransform.fourier g w) : ℝ) : ℂ)) :=
      hFourierSq.ofReal
    apply hFourierSqC.congr
    filter_upwards [] with w
    simpa only [starRingEnd_apply] using
      (Complex.normSq_eq_conj_mul_self
        (z := FourierTransform.fourier g w))
  have hFH : Integrable (FourierTransform.fourier H) := by
    apply hprod.congr
    filter_upwards [] with w
    exact (fourier_crossCorrelation hgInt hgInt hgCont hgCont w).symm
  have hinv : FourierTransform.fourierInv
      (FourierTransform.fourier H) 0 = H 0 :=
    hHInt.fourierInv_fourier_eq hFH hHCont.continuousAt
  have hzero : (∫ w : ℝ, FourierTransform.fourier H w) = H 0 := by
    rw [Real.fourierInv_eq] at hinv
    simpa using hinv
  have hPlancherelC :
      (((∫ w : ℝ,
        Complex.normSq (FourierTransform.fourier g w) : ℝ)) : ℂ) =
      (((∫ x : ℝ, Complex.normSq (g x) : ℝ)) : ℂ) := by
    calc
      (((∫ w : ℝ,
          Complex.normSq (FourierTransform.fourier g w) : ℝ)) : ℂ) =
          ∫ w : ℝ,
            ((Complex.normSq (FourierTransform.fourier g w) : ℝ) : ℂ) :=
        integral_complex_ofReal.symm
      _ = ∫ w : ℝ,
          star (FourierTransform.fourier g w) *
            FourierTransform.fourier g w := by
        apply integral_congr_ae
        filter_upwards [] with w
        simpa only [starRingEnd_apply] using
          (Complex.normSq_eq_conj_mul_self
            (z := FourierTransform.fourier g w))
      _ = ∫ w : ℝ, FourierTransform.fourier H w := by
        apply integral_congr_ae
        filter_upwards [] with w
        exact (fourier_crossCorrelation hgInt hgInt hgCont hgCont w).symm
      _ = H 0 := hzero
      _ = ∫ x : ℝ, star (g x) * g x := by
        simpa only [H, zero_add] using crossCorrelation_apply g g 0
      _ = ∫ x : ℝ, ((Complex.normSq (g x) : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simpa only [starRingEnd_apply] using
          (Complex.normSq_eq_conj_mul_self (z := g x)).symm
      _ = (((∫ x : ℝ, Complex.normSq (g x) : ℝ)) : ℂ) :=
        integral_complex_ofReal
  have hPlancherel :
      (∫ w : ℝ, Complex.normSq (FourierTransform.fourier g w)) =
        ∫ x : ℝ, Complex.normSq (g x) :=
    Complex.ofReal_injective hPlancherelC
  have hsource : (∫ x : ℝ, Complex.normSq (g x)) =
      ∫ x : ℝ in -a..a, ‖g x‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith : -a ≤ a),
      ← integral_Icc_eq_integral_Ioc]
    calc
      (∫ x : ℝ, Complex.normSq (g x)) =
          ∫ x : ℝ in Set.Icc (-a) a, Complex.normSq (g x) := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        have hg0 : g x = 0 := by
          exact yoshidaClippedSmooth_eq_zero_outside
            (f : YoshidaClippedSmooth a) hx
        rw [hg0, Complex.normSq_zero]
      _ = ∫ x : ℝ in Set.Icc (-a) a, ‖g x‖ ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x _
        exact Complex.normSq_eq_norm_sq (g x)
  have hscale := Measure.integral_comp_mul_left q c
  unfold clippedSpectralMass
  calc
    (1 / (2 * Real.pi)) * ∫ v : ℝ,
        Complex.normSq (yoshidaCriticalSampleLinear a ha v
          (f : YoshidaClippedSmooth a)) =
        |c⁻¹| • ∫ v : ℝ, q v := by
      rw [smul_eq_mul, abs_of_pos (inv_pos.mpr (by
        dsimp only [c]
        positivity))]
      dsimp only [c, q]
      rw [one_div]
    _ = ∫ w : ℝ, q (c * w) := hscale.symm
    _ = ∫ w : ℝ,
        Complex.normSq (FourierTransform.fourier g w) := by
      apply integral_congr_ae
      filter_upwards [] with w
      have harg : c * w / (2 * Real.pi) = w := by
        dsimp only [c]
        field_simp [Real.pi_ne_zero]
      dsimp only [q, g]
      rw [yoshidaCriticalSample_eq_fourier ha (c * w)
        (f : YoshidaClippedSmooth a), harg]
    _ = ∫ x : ℝ, Complex.normSq (g x) := hPlancherel
    _ = ∫ x : ℝ in -a..a, ‖g x‖ ^ 2 := hsource

/-- Unit interval energy gives unit spectral mass for the actual periodic odd
tail used by the Section 6 split. -/
theorem oddTail_clippedSpectralMass_eq_one
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule ha N)
    (henergy :
      (∫ x : ℝ in -a..a,
        ‖((f : YoshidaClippedSmooth a) : ℝ → ℂ) x‖ ^ 2) = 1) :
    clippedSpectralMass a ha (f : YoshidaClippedSmooth a) = 1 := by
  rw [clippedSpectralMass_eq_intervalEnergy_of_oddTail ha N f hf,
    henergy]

end ArithmeticHodge.Analysis.YoshidaOddSpectralMassBridge
