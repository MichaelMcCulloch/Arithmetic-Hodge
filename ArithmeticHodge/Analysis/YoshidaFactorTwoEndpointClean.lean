import ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeDomination
import ArithmeticHodge.Analysis.YoshidaEndpointBoundaryTailFold
import ArithmeticHodge.Analysis.YoshidaEndpointClippedArchBridge
import ArithmeticHodge.Analysis.YoshidaEndpointZeroTracePolarPhysical
import ArithmeticHodge.Analysis.YoshidaRestrictedEndpointCoreBridge

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointClean

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeil
open YoshidaCauchyPairing
open YoshidaClippedEndpointContinuous
open YoshidaEndpointClippedArchBridge
open YoshidaEndpointBoundaryTailFold
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPhysicalRealQuadratic
open YoshidaEndpointPotentialBound
open YoshidaEndpointScaledCorrelation
open YoshidaEndpointSingularCorrelation
open YoshidaEndpointZeroTracePolarPhysical
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoDiagonalGeometric
open YoshidaFactorTwoDiagonalPhysical
open YoshidaFactorTwoParityRealification
open YoshidaRenormalizedGeometricKernel
open YoshidaRegularKernelBound
open YoshidaSectionSixAnalytic

/-!
# Centered clean form of the factor-two endpoint

This file keeps the smooth archimedean correlation and the two retained prime
atoms in one centered functional.  The resulting identities are exact; in
particular, they do not replace the prime terms by separate scalar bounds.
-/

/-- The factor-two logarithmic length is twice the endpoint half-width. -/
theorem factorTwoLogLength_eq_two_mul_yoshidaEndpointA :
    factorTwoLogLength = 2 * yoshidaEndpointA := by
  unfold factorTwoLogLength yoshidaEndpointA
  ring

/-- The retained prime lag lies in the full endpoint correlation interval. -/
theorem factorTwoPrimeShift_mem_endpointInterval :
    factorTwoPrimeShift ∈ Set.Icc 0 (2 * yoshidaEndpointA) := by
  have hpos : 0 < (3 / 2 : ℝ) := by norm_num
  have hle : (3 / 2 : ℝ) ≤ 2 := by norm_num
  constructor
  · unfold factorTwoPrimeShift
    exact Real.log_nonneg (by norm_num)
  · rw [← factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
    unfold factorTwoPrimeShift factorTwoLogLength
    exact Real.log_le_log hpos hle

/-- A supported real Schwartz autocorrelation is the one-sided endpoint
correlation on every nonnegative shift in the overlap interval. -/
theorem crossCorrelation_re_eq_realEndpointCorrelation_of_supported_real
    {a u : ℝ} (F : SchwartzMap ℝ ℂ)
    (hsupport : ∀ x ∉ Set.Icc (-a) a, F x = 0)
    (hreal : ∀ x : ℝ, (F x).im = 0)
    (huL : u ≤ 2 * a) :
    (crossCorrelation (F : ℝ → ℂ) (F : ℝ → ℂ) u).re =
      realEndpointCorrelation a (fun x ↦ (F x).re) u := by
  have hFreal (x : ℝ) : F x = ((F x).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hreal x
  rw [crossCorrelation_apply]
  have hle : -a ≤ a - u := by linarith
  have hrestrict :
      (∫ x : ℝ, star (F x) * F (u + x)) =
        ∫ x : ℝ in -a..a - u, star (F x) * F (u + x) := by
    rw [intervalIntegral.integral_of_le hle,
      ← integral_Icc_eq_integral_Ioc]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      by_cases hxf : x ∈ Icc (-a) a
      · have hxgt : a - u < x := by
          by_contra hnot
          exact hx ⟨hxf.1, le_of_not_gt hnot⟩
        have hux : u + x ∉ Icc (-a) a := by
          intro hmem
          linarith [hmem.2]
        rw [hsupport (u + x) hux, mul_zero]
      · rw [hsupport x hxf, star_zero, zero_mul])).symm
  rw [hrestrict]
  have hrealIntegral :
      (∫ x : ℝ in -a..a - u, star (F x) * F (u + x)) =
        ((∫ x : ℝ in -a..a - u,
          (F (u + x)).re * (F x).re : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    change star (F x) * F (u + x) =
      (((F (u + x)).re * (F x).re : ℝ) : ℂ)
    rw [hFreal x, hFreal (u + x)]
    simp
    ring
  rw [hrealIntegral]
  unfold realEndpointCorrelation
  rfl

/-- The critical real pullback profile rescaled to `[-1,1]`. -/
def factorTwoCenteredProfile (g : BombieriTest) (x : ℝ) : ℝ :=
  (g.logarithmicPullbackSchwartz (1 / 2) (yoshidaEndpointA * x)).re

/-- The exact centered perturbation added to the clean local critical
quadratic by the symmetric factor-two coordinate. -/
def factorTwoCenteredSymmetricPerturbation (w : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA *
      (∫ t : ℝ in 0..2,
        factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          centeredEndpointCorrelation w t) -
    (Real.log 2 / Real.sqrt 2) * centeredEndpointCorrelation w 0 -
    (Real.log 3 / Real.sqrt 3) *
      centeredEndpointCorrelation w
        (factorTwoPrimeShift / yoshidaEndpointA)

/-- For a real critical pullback supported on the endpoint interval, the
symmetric factor-two coordinate is exactly the endpoint scale times the
centered perturbation. -/
theorem factorTwoSymmetricCoordinate_eq_endpoint_mul_perturbation
    (g : BombieriTest)
    (hsupport : YoshidaCriticalPullbackSupported yoshidaEndpointA g)
    (hreal : ∀ x : ℝ,
      (g.logarithmicPullbackSchwartz (1 / 2) x).im = 0) :
    factorTwoSymmetricCoordinate g =
      yoshidaEndpointA * factorTwoCenteredSymmetricPerturbation
        (factorTwoCenteredProfile g) := by
  let F : SchwartzMap ℝ ℂ :=
    g.logarithmicPullbackSchwartz (1 / 2)
  let f : ℝ → ℝ := fun x ↦ (F x).re
  let w : ℝ → ℝ := centeredRescale yoshidaEndpointA f
  have hw : w = factorTwoCenteredProfile g := by
    funext x
    rfl
  have hcorr {s : ℝ} (hs : s ∈ Set.Icc 0 (2 * yoshidaEndpointA)) :
      (factorTwoSelfCorrelation g s).re =
        realEndpointCorrelation yoshidaEndpointA f s := by
    exact crossCorrelation_re_eq_realEndpointCorrelation_of_supported_real
      F hsupport hreal hs.2
  have hintegral :
      (∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoSymmetricWeight s *
            (factorTwoSelfCorrelation g s).re) =
        yoshidaEndpointA ^ 2 *
          ∫ t : ℝ in 0..2,
            factorTwoSymmetricWeight (yoshidaEndpointA * t) *
              centeredEndpointCorrelation w t := by
    rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
    calc
      (∫ s : ℝ in 0..2 * yoshidaEndpointA,
          factorTwoSymmetricWeight s *
            (factorTwoSelfCorrelation g s).re) =
          ∫ s : ℝ in 0..2 * yoshidaEndpointA,
            factorTwoSymmetricWeight s *
              realEndpointCorrelation yoshidaEndpointA f s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le
          (mul_nonneg (by norm_num) yoshidaEndpointA_pos.le)] at hs
        change factorTwoSymmetricWeight s *
            (factorTwoSelfCorrelation g s).re =
          factorTwoSymmetricWeight s *
            realEndpointCorrelation yoshidaEndpointA f s
        rw [hcorr hs]
      _ = _ := integral_weight_mul_realEndpointCorrelation
        yoshidaEndpointA_pos f factorTwoSymmetricWeight
  have hzero :
      (factorTwoSelfCorrelation g 0).re =
        yoshidaEndpointA * centeredEndpointCorrelation w 0 := by
    rw [hcorr ⟨le_rfl,
      mul_nonneg (by norm_num) yoshidaEndpointA_pos.le⟩]
    simpa using realEndpointCorrelation_mul yoshidaEndpointA_pos f 0
  have hprime :
      (factorTwoSelfCorrelation g factorTwoPrimeShift).re =
        yoshidaEndpointA * centeredEndpointCorrelation w
          (factorTwoPrimeShift / yoshidaEndpointA) := by
    rw [hcorr factorTwoPrimeShift_mem_endpointInterval]
    have harg : yoshidaEndpointA *
        (factorTwoPrimeShift / yoshidaEndpointA) = factorTwoPrimeShift := by
      field_simp [yoshidaEndpointA_pos.ne']
    have hscale := realEndpointCorrelation_mul yoshidaEndpointA_pos f
      (factorTwoPrimeShift / yoshidaEndpointA)
    rw [harg] at hscale
    simpa only [w] using hscale
  unfold factorTwoSymmetricCoordinate
  rw [hintegral, hzero, hprime, hw]
  unfold factorTwoCenteredSymmetricPerturbation
  ring

/-- A continuous critical pullback supported in a closed endpoint interval
has zero traces at both endpoints. -/
theorem criticalPullback_endpoints_zero_of_supported
    {a : ℝ} (g : BombieriTest)
    (hsupport : YoshidaCriticalPullbackSupported a g) :
    g.logarithmicPullbackSchwartz (1 / 2) (-a) = 0 ∧
      g.logarithmicPullbackSchwartz (1 / 2) a = 0 := by
  let F : ℝ → ℂ := g.logarithmicPullbackSchwartz (1 / 2)
  have hF : Continuous F :=
    (g.logarithmicPullback_contDiff (1 / 2)).continuous
  have hpos : F a = 0 := by
    have hzero : Set.EqOn F (fun _ : ℝ ↦ (0 : ℂ)) (Set.Ioi a) := by
      intro y hy
      exact hsupport y (by
        simp only [Set.mem_Icc, not_and_or]
        exact Or.inr (not_le.mpr hy))
    exact hzero.closure hF continuous_const (by simp)
  have hneg : F (-a) = 0 := by
    have hzero : Set.EqOn F (fun _ : ℝ ↦ (0 : ℂ)) (Set.Iio (-a)) := by
      intro y hy
      exact hsupport y (by
        simp only [Set.mem_Icc, not_and_or]
        exact Or.inl (not_le.mpr hy))
    exact hzero.closure hF continuous_const (by simp)
  exact ⟨hneg, hpos⟩

/-- Every real endpoint periodic profile with zero traces has local critical
value equal to the endpoint scale times the clean centered quadratic. -/
theorem clippedCriticalFormValue_eq_endpoint_mul_clean_of_real_endpoints_zero
    (r : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (hreal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hneg : (r : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hpos : (r : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0) :
    clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
        (r : YoshidaClippedSmooth yoshidaEndpointA) =
      yoshidaEndpointA * yoshidaEndpointOddCleanQuadratic
        (centeredRescale yoshidaEndpointA (fun x ↦
          ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re)) := by
  let f : ℝ → ℝ := fun x ↦
    ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re
  have hpolar :=
    clippedPolarEnergy_eq_physical_polar_product_of_endpoints_zero
      r hreal hneg hpos
  have hbridge :=
    clippedArchEnergy_add_polar_eq_physicalRealQuadratic_of_endpoints_zero
      r (fun x _hx ↦ hreal x) hneg hpos
  have hphysical :
      clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
          (r : YoshidaClippedSmooth yoshidaEndpointA) =
        yoshidaEndpointPhysicalRealQuadratic f := by
    rw [clippedCriticalFormValue_eq_polar_add_arch, hpolar]
    dsimp only [f] at hbridge ⊢
    linarith
  have hrcont : Continuous
      ((r : YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) :=
    continuous_yoshidaClippedSmooth_of_endpoints_zero
      yoshidaEndpointA_pos _ hneg hpos
  have hfcont : Continuous f := Complex.continuous_re.comp hrcont
  have hprofile : ContDiffOn ℝ 1 f
      (Icc (-yoshidaEndpointA) yoshidaEndpointA) := by
    exact Complex.reCLM.contDiff.comp_contDiffOn
      ((r : YoshidaClippedSmooth yoshidaEndpointA).property.1.of_le (by simp))
  have hscale : ContDiffOn ℝ 1
      (fun x : ℝ ↦ yoshidaEndpointA * x) (Icc (-1) 1) := by
    fun_prop
  have hmaps : MapsTo (fun x : ℝ ↦ yoshidaEndpointA * x)
      (Icc (-1) 1) (Icc (-yoshidaEndpointA) yoshidaEndpointA) := by
    intro x hx
    constructor <;> nlinarith [hx.1, hx.2, yoshidaEndpointA_pos]
  have hlocal : LocallyLipschitzOn (Icc (-1) 1)
      (centeredRescale yoshidaEndpointA f) := by
    have hcomp := hprofile.comp hscale hmaps
    simpa only [centeredRescale, Function.comp_apply] using
      hcomp.locallyLipschitzOn (convex_Icc (-1) 1)
  rw [hphysical]
  exact yoshidaEndpointPhysicalRealQuadratic_eq_clean f hfcont hlocal

/-- The real local critical self-form of a supported real pullback is exactly
the clean centered endpoint quadratic. -/
theorem bombieriLocalCriticalForm_re_eq_endpoint_mul_clean
    (g : BombieriTest)
    (hsupport : YoshidaCriticalPullbackSupported yoshidaEndpointA g)
    (hreal : ∀ x : ℝ,
      (g.logarithmicPullbackSchwartz (1 / 2) x).im = 0) :
    (bombieriLocalCriticalForm g g).re =
      yoshidaEndpointA * yoshidaEndpointOddCleanQuadratic
        (factorTwoCenteredProfile g) := by
  let crop : YoshidaClippedSmooth yoshidaEndpointA :=
    yoshidaCriticalPullbackCropLinear yoshidaEndpointA g
  have hmem : crop ∈ yoshidaClippedPeriodicCoreSubmodule yoshidaEndpointA := by
    simpa only [crop] using
      yoshidaCriticalPullbackCrop_mem_periodicCore_structural
        yoshidaEndpointA_pos g hsupport
  let r : YoshidaClippedPeriodicCore yoshidaEndpointA := ⟨crop, hmem⟩
  have hcrop : (crop : ℝ → ℂ) =
      g.logarithmicPullbackSchwartz (1 / 2) := by
    simpa only [crop] using
      yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hsupport
  have hrreal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0 := by
    intro x
    change (crop x).im = 0
    rw [show crop x = g.logarithmicPullbackSchwartz (1 / 2) x by
      exact congrFun hcrop x]
    exact hreal x
  obtain ⟨hpullNeg, hpullPos⟩ :=
    criticalPullback_endpoints_zero_of_supported
      g hsupport
  have hrneg : (r : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0 := by
    change crop (-yoshidaEndpointA) = 0
    rw [show crop (-yoshidaEndpointA) =
        g.logarithmicPullbackSchwartz (1 / 2) (-yoshidaEndpointA) by
      exact congrFun hcrop (-yoshidaEndpointA), hpullNeg]
  have hrpos : (r : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0 := by
    change crop yoshidaEndpointA = 0
    rw [show crop yoshidaEndpointA =
        g.logarithmicPullbackSchwartz (1 / 2) yoshidaEndpointA by
      exact congrFun hcrop yoshidaEndpointA, hpullPos]
  have hclean :=
    clippedCriticalFormValue_eq_endpoint_mul_clean_of_real_endpoints_zero
      r hrreal hrneg hrpos
  have hform := congrArg Complex.re
    (yoshidaClippedLocalCriticalForm_crop_eq_bombieriLocalCriticalForm
      yoshidaEndpointA_pos g g hsupport hsupport)
  change clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos crop =
      (bombieriLocalCriticalForm g g).re at hform
  rw [← hform]
  change clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos crop = _
  rw [show clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos crop =
      yoshidaEndpointA * yoshidaEndpointOddCleanQuadratic
        (centeredRescale yoshidaEndpointA (fun x ↦ (crop x).re)) by
    simpa only [r] using hclean]
  congr 2
  funext x
  unfold centeredRescale factorTwoCenteredProfile
  change (crop (yoshidaEndpointA * x)).re =
    (g.logarithmicPullbackSchwartz (1 / 2) (yoshidaEndpointA * x)).re
  rw [show crop (yoshidaEndpointA * x) =
      g.logarithmicPullbackSchwartz (1 / 2) (yoshidaEndpointA * x) by
    exact congrFun hcrop (yoshidaEndpointA * x)]

/-! The previous two identities are deliberately separate: their sum keeps
the archimedean-prime cancellation visible in the final profile functional. -/

/-- Exact centered formula for the symmetric endpoint channel. -/
theorem factorTwoDiagonal_add_symmetric_eq_endpoint_mul_clean_perturbation
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hmulSupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcriticalSupport :
      YoshidaCriticalPullbackSupported yoshidaEndpointA g)
    (hreal : ∀ x : ℝ,
      (g.logarithmicPullbackSchwartz (1 / 2) x).im = 0) :
    factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g =
      yoshidaEndpointA *
        (yoshidaEndpointOddCleanQuadratic (factorTwoCenteredProfile g) +
          factorTwoCenteredSymmetricPerturbation
            (factorTwoCenteredProfile g)) := by
  rw [YoshidaFactorTwoPrimeDomination.factorTwoDiagonalCoordinate_eq_localCriticalForm
      g ha hab hmulSupport hratio,
    bombieriLocalCriticalForm_re_eq_endpoint_mul_clean
      g hcriticalSupport hreal,
    factorTwoSymmetricCoordinate_eq_endpoint_mul_perturbation
      g hcriticalSupport hreal]
  ring

/-- Exact centered formula for the antisymmetric endpoint channel. -/
theorem factorTwoDiagonal_sub_symmetric_eq_endpoint_mul_clean_sub_perturbation
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hmulSupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcriticalSupport :
      YoshidaCriticalPullbackSupported yoshidaEndpointA g)
    (hreal : ∀ x : ℝ,
      (g.logarithmicPullbackSchwartz (1 / 2) x).im = 0) :
    factorTwoDiagonalCoordinate g - factorTwoSymmetricCoordinate g =
      yoshidaEndpointA *
        (yoshidaEndpointOddCleanQuadratic (factorTwoCenteredProfile g) -
          factorTwoCenteredSymmetricPerturbation
            (factorTwoCenteredProfile g)) := by
  rw [YoshidaFactorTwoPrimeDomination.factorTwoDiagonalCoordinate_eq_localCriticalForm
      g ha hab hmulSupport hratio,
    bombieriLocalCriticalForm_re_eq_endpoint_mul_clean
      g hcriticalSupport hreal,
    factorTwoSymmetricCoordinate_eq_endpoint_mul_perturbation
      g hcriticalSupport hreal]
  ring

/-- The critical pullback of the coefficient-real projection is the real
part of the original critical pullback. -/
theorem bombieriRealPartTest_logarithmicPullbackSchwartz_critical
    (g : BombieriTest) (x : ℝ) :
    (bombieriRealPartTest g).logarithmicPullbackSchwartz (1 / 2) x =
      ((g.logarithmicPullbackSchwartz (1 / 2) x).re : ℂ) := by
  simp only [BombieriTest.logarithmicPullbackSchwartz_apply,
    BombieriTest.logarithmicPullback, bombieriRealPartTest_apply]
  norm_cast
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- The critical pullback of the coefficient-imaginary projection is the
imaginary part of the original critical pullback. -/
theorem bombieriImagPartTest_logarithmicPullbackSchwartz_critical
    (g : BombieriTest) (x : ℝ) :
    (bombieriImagPartTest g).logarithmicPullbackSchwartz (1 / 2) x =
      ((g.logarithmicPullbackSchwartz (1 / 2) x).im : ℂ) := by
  simp only [BombieriTest.logarithmicPullbackSchwartz_apply,
    BombieriTest.logarithmicPullback, bombieriImagPartTest_apply]
  norm_cast
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]

theorem bombieriRealPartTest_criticalPullbackSupported
    {a : ℝ} (g : BombieriTest)
    (hsupport : YoshidaCriticalPullbackSupported a g) :
    YoshidaCriticalPullbackSupported a (bombieriRealPartTest g) := by
  intro x hx
  rw [bombieriRealPartTest_logarithmicPullbackSchwartz_critical]
  rw [hsupport x hx]
  simp

theorem bombieriImagPartTest_criticalPullbackSupported
    {a : ℝ} (g : BombieriTest)
    (hsupport : YoshidaCriticalPullbackSupported a g) :
    YoshidaCriticalPullbackSupported a (bombieriImagPartTest g) := by
  intro x hx
  rw [bombieriImagPartTest_logarithmicPullbackSchwartz_critical]
  rw [hsupport x hx]
  simp

theorem bombieriRealPartTest_criticalPullback_im_eq_zero
    (g : BombieriTest) (x : ℝ) :
    ((bombieriRealPartTest g).logarithmicPullbackSchwartz
      (1 / 2) x).im = 0 := by
  rw [bombieriRealPartTest_logarithmicPullbackSchwartz_critical]
  simp

theorem bombieriImagPartTest_criticalPullback_im_eq_zero
    (g : BombieriTest) (x : ℝ) :
    ((bombieriImagPartTest g).logarithmicPullbackSchwartz
      (1 / 2) x).im = 0 := by
  rw [bombieriImagPartTest_logarithmicPullbackSchwartz_critical]
  simp

/-- Exact centered symmetric-channel identity for a possibly complex test.
Both real profile channels retain their complete smooth-plus-prime
perturbation. -/
theorem factorTwoDiagonal_add_symmetric_eq_endpoint_mul_two_profiles
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hmulSupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcriticalSupport :
      YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g =
      yoshidaEndpointA *
        ((yoshidaEndpointOddCleanQuadratic
              (factorTwoCenteredProfile (bombieriRealPartTest g)) +
            factorTwoCenteredSymmetricPerturbation
              (factorTwoCenteredProfile (bombieriRealPartTest g))) +
          (yoshidaEndpointOddCleanQuadratic
              (factorTwoCenteredProfile (bombieriImagPartTest g)) +
            factorTwoCenteredSymmetricPerturbation
              (factorTwoCenteredProfile (bombieriImagPartTest g)))) := by
  have huSupport :
      tsupport (bombieriRealPartTest g : ℝ → ℂ) ⊆ Set.Icc a b :=
    (bombieriRealPartTest_tsupport_subset g).trans hmulSupport
  have hvSupport :
      tsupport (bombieriImagPartTest g : ℝ → ℂ) ⊆ Set.Icc a b :=
    (bombieriImagPartTest_tsupport_subset g).trans hmulSupport
  have huCritical := bombieriRealPartTest_criticalPullbackSupported
    g hcriticalSupport
  have hvCritical := bombieriImagPartTest_criticalPullbackSupported
    g hcriticalSupport
  have hu := factorTwoDiagonal_add_symmetric_eq_endpoint_mul_clean_perturbation
    (bombieriRealPartTest g) ha hab huSupport hratio huCritical
      (bombieriRealPartTest_criticalPullback_im_eq_zero g)
  have hv := factorTwoDiagonal_add_symmetric_eq_endpoint_mul_clean_perturbation
    (bombieriImagPartTest g) ha hab hvSupport hratio hvCritical
      (bombieriImagPartTest_criticalPullback_im_eq_zero g)
  rw [factorTwoDiagonalCoordinate_eq_realImag g,
    factorTwoSymmetricCoordinate_eq_realImag
      g ha hab hmulSupport hratio]
  calc
    factorTwoDiagonalCoordinate (bombieriRealPartTest g) +
          factorTwoDiagonalCoordinate (bombieriImagPartTest g) +
        (factorTwoSymmetricCoordinate (bombieriRealPartTest g) +
          factorTwoSymmetricCoordinate (bombieriImagPartTest g)) =
        (factorTwoDiagonalCoordinate (bombieriRealPartTest g) +
            factorTwoSymmetricCoordinate (bombieriRealPartTest g)) +
          (factorTwoDiagonalCoordinate (bombieriImagPartTest g) +
            factorTwoSymmetricCoordinate (bombieriImagPartTest g)) := by ring
    _ = _ := by rw [hu, hv]; ring

/-- Exact centered antisymmetric-channel identity for a possibly complex
test. -/
theorem factorTwoDiagonal_sub_symmetric_eq_endpoint_mul_two_profiles
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hmulSupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcriticalSupport :
      YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    factorTwoDiagonalCoordinate g - factorTwoSymmetricCoordinate g =
      yoshidaEndpointA *
        ((yoshidaEndpointOddCleanQuadratic
              (factorTwoCenteredProfile (bombieriRealPartTest g)) -
            factorTwoCenteredSymmetricPerturbation
              (factorTwoCenteredProfile (bombieriRealPartTest g))) +
          (yoshidaEndpointOddCleanQuadratic
              (factorTwoCenteredProfile (bombieriImagPartTest g)) -
            factorTwoCenteredSymmetricPerturbation
              (factorTwoCenteredProfile (bombieriImagPartTest g)))) := by
  have huSupport :
      tsupport (bombieriRealPartTest g : ℝ → ℂ) ⊆ Set.Icc a b :=
    (bombieriRealPartTest_tsupport_subset g).trans hmulSupport
  have hvSupport :
      tsupport (bombieriImagPartTest g : ℝ → ℂ) ⊆ Set.Icc a b :=
    (bombieriImagPartTest_tsupport_subset g).trans hmulSupport
  have huCritical := bombieriRealPartTest_criticalPullbackSupported
    g hcriticalSupport
  have hvCritical := bombieriImagPartTest_criticalPullbackSupported
    g hcriticalSupport
  have hu :=
    factorTwoDiagonal_sub_symmetric_eq_endpoint_mul_clean_sub_perturbation
      (bombieriRealPartTest g) ha hab huSupport hratio huCritical
        (bombieriRealPartTest_criticalPullback_im_eq_zero g)
  have hv :=
    factorTwoDiagonal_sub_symmetric_eq_endpoint_mul_clean_sub_perturbation
      (bombieriImagPartTest g) ha hab hvSupport hratio hvCritical
        (bombieriImagPartTest_criticalPullback_im_eq_zero g)
  rw [factorTwoDiagonalCoordinate_eq_realImag g,
    factorTwoSymmetricCoordinate_eq_realImag
      g ha hab hmulSupport hratio]
  calc
    factorTwoDiagonalCoordinate (bombieriRealPartTest g) +
          factorTwoDiagonalCoordinate (bombieriImagPartTest g) -
        (factorTwoSymmetricCoordinate (bombieriRealPartTest g) +
          factorTwoSymmetricCoordinate (bombieriImagPartTest g)) =
        (factorTwoDiagonalCoordinate (bombieriRealPartTest g) -
            factorTwoSymmetricCoordinate (bombieriRealPartTest g)) +
          (factorTwoDiagonalCoordinate (bombieriImagPartTest g) -
            factorTwoSymmetricCoordinate (bombieriImagPartTest g)) := by ring
    _ = _ := by rw [hu, hv]; ring

/-- The exact profile inequality left by the centered symmetric endpoint
formula.  This is only an algebraic reformulation; no prime term is bounded
separately. -/
theorem clean_add_symmetricPerturbation_nonneg_iff
    (w : ℝ → ℝ) :
    0 ≤ yoshidaEndpointOddCleanQuadratic w +
        factorTwoCenteredSymmetricPerturbation w ↔
      (Real.log 2 / Real.sqrt 2) * centeredEndpointCorrelation w 0 +
          (Real.log 3 / Real.sqrt 3) * centeredEndpointCorrelation w
            (factorTwoPrimeShift / yoshidaEndpointA) ≤
        yoshidaEndpointOddCleanQuadratic w +
          yoshidaEndpointA *
            (∫ t : ℝ in 0..2,
              factorTwoSymmetricWeight (yoshidaEndpointA * t) *
                centeredEndpointCorrelation w t) := by
  unfold factorTwoCenteredSymmetricPerturbation
  constructor <;> intro h <;> linarith

/-- For one supported real profile, symmetric endpoint positivity is exactly
the cancellation-preserving dimensionless inequality above. -/
theorem factorTwoDiagonal_add_symmetric_nonneg_iff_clean_perturbation
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hmulSupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcriticalSupport :
      YoshidaCriticalPullbackSupported yoshidaEndpointA g)
    (hreal : ∀ x : ℝ,
      (g.logarithmicPullbackSchwartz (1 / 2) x).im = 0) :
    0 ≤ factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g ↔
      0 ≤ yoshidaEndpointOddCleanQuadratic (factorTwoCenteredProfile g) +
        factorTwoCenteredSymmetricPerturbation
          (factorTwoCenteredProfile g) := by
  rw [factorTwoDiagonal_add_symmetric_eq_endpoint_mul_clean_perturbation
    g ha hab hmulSupport hratio hcriticalSupport hreal]
  exact mul_nonneg_iff_of_pos_left yoshidaEndpointA_pos

/-- The cancellation-preserving terminal inequality for the antisymmetric
profile endpoint. -/
theorem clean_sub_symmetricPerturbation_nonneg_iff
    (w : ℝ → ℝ) :
    0 ≤ yoshidaEndpointOddCleanQuadratic w -
        factorTwoCenteredSymmetricPerturbation w ↔
      yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoSymmetricWeight (yoshidaEndpointA * t) *
              centeredEndpointCorrelation w t) ≤
        yoshidaEndpointOddCleanQuadratic w +
          (Real.log 2 / Real.sqrt 2) * centeredEndpointCorrelation w 0 +
          (Real.log 3 / Real.sqrt 3) * centeredEndpointCorrelation w
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  unfold factorTwoCenteredSymmetricPerturbation
  constructor <;> intro h <;> linarith

/-- For one supported real profile, antisymmetric endpoint positivity is
exactly `0 ≤ clean - perturbation`. -/
theorem factorTwoDiagonal_sub_symmetric_nonneg_iff_clean_sub_perturbation
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hmulSupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcriticalSupport :
      YoshidaCriticalPullbackSupported yoshidaEndpointA g)
    (hreal : ∀ x : ℝ,
      (g.logarithmicPullbackSchwartz (1 / 2) x).im = 0) :
    0 ≤ factorTwoDiagonalCoordinate g - factorTwoSymmetricCoordinate g ↔
      0 ≤ yoshidaEndpointOddCleanQuadratic (factorTwoCenteredProfile g) -
        factorTwoCenteredSymmetricPerturbation
          (factorTwoCenteredProfile g) := by
  rw [factorTwoDiagonal_sub_symmetric_eq_endpoint_mul_clean_sub_perturbation
    g ha hab hmulSupport hratio hcriticalSupport hreal]
  exact mul_nonneg_iff_of_pos_left yoshidaEndpointA_pos

/-- The correlation at the opposite endpoint is controlled by the two
boundary tails left by an overlap of length `t`.  This is the exact
one-square estimate needed by the pole at `factorTwoLogLength - s`. -/
theorem two_mul_abs_centeredEndpointCorrelation_two_sub_le_boundaryTail
    (w : ℝ → ℝ) (hw : Continuous w) {t : ℝ}
    (ht0 : 0 ≤ t) :
    2 * |centeredEndpointCorrelation w (2 - t)| ≤
      centeredEndpointBoundaryTail w t := by
  let p : ℝ → ℝ := fun x ↦ w (2 - t + x) * w x
  let q : ℝ → ℝ := fun x ↦ w x ^ 2
  have hbounds : (-1 : ℝ) ≤ -1 + t := by linarith
  have hpcont : Continuous p := by
    dsimp only [p]
    exact (hw.comp (continuous_const.add continuous_id)).mul hw
  have hqcont : Continuous q := by
    dsimp only [q]
    fun_prop
  have hpint : IntervalIntegrable p volume (-1) (-1 + t) :=
    hpcont.intervalIntegrable _ _
  have hqleft : IntervalIntegrable q volume (-1) (-1 + t) :=
    hqcont.intervalIntegrable _ _
  have hqshift : IntervalIntegrable (fun x ↦ q (2 - t + x))
      volume (-1) (-1 + t) :=
    (hqcont.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  unfold centeredEndpointCorrelation centeredEndpointBoundaryTail
  rw [show 1 - (2 - t) = -1 + t by ring]
  change 2 * |∫ x : ℝ in -1..-1 + t, p x| ≤
    (∫ x : ℝ in 1 - t..1, q x) + ∫ x : ℝ in -1..-1 + t, q x
  calc
    2 * |∫ x : ℝ in -1..-1 + t, p x| =
        2 * ‖∫ x : ℝ in -1..-1 + t, p x‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ 2 * ∫ x : ℝ in -1..-1 + t, ‖p x‖ := by
      gcongr
      exact intervalIntegral.norm_integral_le_integral_norm hbounds
    _ = ∫ x : ℝ in -1..-1 + t, 2 * ‖p x‖ := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ x : ℝ in -1..-1 + t, q (2 - t + x) + q x := by
      apply intervalIntegral.integral_mono_on hbounds
      · exact (hpint.norm.const_mul 2)
      · exact hqshift.add hqleft
      · intro x _hx
        dsimp only [p, q]
        rw [Real.norm_eq_abs, abs_mul]
        nlinarith [sq_nonneg (|w (2 - t + x)| - |w x|),
          sq_abs (w (2 - t + x)), sq_abs (w x)]
    _ = (∫ x : ℝ in -1..-1 + t, q (2 - t + x)) +
          ∫ x : ℝ in -1..-1 + t, q x := by
      rw [intervalIntegral.integral_add hqshift hqleft]
    _ = (∫ x : ℝ in 1 - t..1, q x) +
          ∫ x : ℝ in -1..-1 + t, q x := by
      rw [intervalIntegral.integral_comp_add_left]
      congr 2 <;> ring

/-- The signed opposite-endpoint correlation obeys the same boundary-tail
upper bound. -/
theorem two_mul_centeredEndpointCorrelation_two_sub_le_boundaryTail
    (w : ℝ → ℝ) (hw : Continuous w) {t : ℝ}
    (ht0 : 0 ≤ t) :
    2 * centeredEndpointCorrelation w (2 - t) ≤
      centeredEndpointBoundaryTail w t := by
  calc
    2 * centeredEndpointCorrelation w (2 - t) ≤
        2 * |centeredEndpointCorrelation w (2 - t)| := by
      gcongr
      exact le_abs_self _
    _ ≤ _ :=
      two_mul_abs_centeredEndpointCorrelation_two_sub_le_boundaryTail
        w hw ht0

/-- The centered one-sided correlation of a continuous profile is continuous
in its shift.  A fixed-unit-interval affine parametrization also records the
vanishing overlap factor `2 - t`. -/
theorem continuous_centeredEndpointCorrelation_of_continuous
    (w : ℝ → ℝ) (hw : Continuous w) :
    Continuous (centeredEndpointCorrelation w) := by
  let phi : ℝ → ℝ → ℝ := fun t y ↦
    w (t - 1 + (2 - t) * y) * w (-1 + (2 - t) * y)
  let J : ℝ → ℝ := fun t ↦ ∫ y : ℝ in 0..1, phi t y
  have hphi : Continuous phi.uncurry := by
    dsimp only [phi, Function.uncurry]
    fun_prop
  have hJcont : Continuous J := by
    have hset : Continuous (fun t : ℝ ↦
        ∫ y : ℝ in Set.Icc (0 : ℝ) 1, phi t y) :=
      continuous_parametric_integral_of_continuous
        (μ := volume) hphi isCompact_Icc
    have heq : J = fun t : ℝ ↦
        ∫ y : ℝ in Set.Icc (0 : ℝ) 1, phi t y := by
      funext t
      dsimp only [J]
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
    rw [heq]
    exact hset
  have htransport (t : ℝ) :
      centeredEndpointCorrelation w t = (2 - t) * J t := by
    let p : ℝ → ℝ := fun x ↦ w (t + x) * w x
    have hsubst := intervalIntegral.smul_integral_comp_mul_add
      (a := (0 : ℝ)) (b := 1) p (2 - t) (-1)
    unfold centeredEndpointCorrelation
    change (∫ x : ℝ in -1..1 - t, p x) = (2 - t) * J t
    symm
    calc
      (2 - t) * J t =
          (2 - t) * ∫ y : ℝ in 0..1, p ((2 - t) * y + -1) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro y _hy
        dsimp only [J, phi, p]
        congr 2 <;> ring
      _ = ∫ x : ℝ in (2 - t) * 0 + -1..(2 - t) * 1 + -1, p x := by
        simpa only [smul_eq_mul] using hsubst
      _ = ∫ x : ℝ in -1..1 - t, p x := by
        simp only [mul_zero, zero_add, mul_one]
        congr 1
        ring
  rw [show centeredEndpointCorrelation w =
      fun t : ℝ ↦ (2 - t) * J t by
    funext t
    exact htransport t]
  exact (continuous_const.sub continuous_id).mul hJcont

/-- Critical self-correlation is invariant under normalized multiplicative
dilation, since the critical pullback changes only by translation. -/
theorem factorTwoSelfCorrelation_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda)
    (g : BombieriTest) (s : ℝ) :
    factorTwoSelfCorrelation (normalizedDilation lambda hlambda g) s =
      factorTwoSelfCorrelation g s := by
  let F : ℝ → ℂ := g.logarithmicPullbackSchwartz (1 / 2)
  let H : ℝ → ℂ := fun y ↦ star (F y) * F (s + y)
  unfold factorTwoSelfCorrelation
  rw [crossCorrelation_apply, crossCorrelation_apply]
  simp_rw [normalizedDilation_logarithmicPullbackSchwartz_critical]
  calc
    (∫ x : ℝ,
        star (F (x - Real.log lambda)) *
          F (s + x - Real.log lambda)) =
        ∫ x : ℝ, H (x + (-Real.log lambda)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [H]
      congr 2
      ring
    _ = ∫ x : ℝ, H x :=
      MeasureTheory.integral_add_right_eq_self H (-Real.log lambda)

/-- The physical diagonal coordinate is normalized-dilation invariant. -/
theorem factorTwoDiagonalCoordinate_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    factorTwoDiagonalCoordinate (normalizedDilation lambda hlambda g) =
      factorTwoDiagonalCoordinate g := by
  unfold factorTwoDiagonalCoordinate factorTwoDiagonalPhysicalIntegrand
    factorTwoSelfCorrelationRe
  simp_rw [factorTwoSelfCorrelation_normalizedDilation lambda hlambda g]

/-- The symmetric folded coordinate is normalized-dilation invariant. -/
theorem factorTwoSymmetricCoordinate_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    factorTwoSymmetricCoordinate (normalizedDilation lambda hlambda g) =
      factorTwoSymmetricCoordinate g := by
  unfold factorTwoSymmetricCoordinate
  simp_rw [factorTwoSelfCorrelation_normalizedDilation lambda hlambda g]

/-- Every multiplicative ratio-two seed has an exact centered two-profile
formula after its canonical normalized logarithmic centering. -/
theorem factorTwoDiagonal_add_symmetric_eq_logCentered_two_profiles
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    let gc := normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g
    factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g =
      yoshidaEndpointA *
        ((yoshidaEndpointOddCleanQuadratic
              (factorTwoCenteredProfile (bombieriRealPartTest gc)) +
            factorTwoCenteredSymmetricPerturbation
              (factorTwoCenteredProfile (bombieriRealPartTest gc))) +
          (yoshidaEndpointOddCleanQuadratic
              (factorTwoCenteredProfile (bombieriImagPartTest gc)) +
            factorTwoCenteredSymmetricPerturbation
              (factorTwoCenteredProfile (bombieriImagPartTest gc)))) := by
  let lambda : ℝ := logarithmicCenter a b
  have hlambda : 0 < lambda := logarithmicCenter_pos a b
  let gc : BombieriTest := normalizedDilation lambda hlambda g
  have haC : 0 < a / lambda := div_pos ha hlambda
  have habC : a / lambda ≤ b / lambda := by
    exact div_le_div_of_nonneg_right hab hlambda.le
  have hsupportC : tsupport gc ⊆ Set.Icc (a / lambda) (b / lambda) := by
    exact normalizedDilation_tsupport_subset_Icc lambda hlambda g hsupport
  have hratioC : (b / lambda) / (a / lambda) ≤ 2 := by
    rw [div_div_div_cancel_right₀ hlambda.ne' b a]
    exact hratio
  have hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA gc := by
    simpa only [gc, lambda, hlambda] using
      logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaEndpointA
        g ha hab hsupport hratio
  have hcentered :=
    factorTwoDiagonal_add_symmetric_eq_endpoint_mul_two_profiles
      gc haC habC hsupportC hratioC hcritical
  dsimp only
  rw [← factorTwoDiagonalCoordinate_normalizedDilation lambda hlambda g,
    ← factorTwoSymmetricCoordinate_normalizedDilation lambda hlambda g]
  simpa only [gc, lambda, hlambda] using hcentered

/-- Canonically centered two-profile formula for the antisymmetric endpoint
of every ratio-two seed. -/
theorem factorTwoDiagonal_sub_symmetric_eq_logCentered_two_profiles
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    let gc := normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g
    factorTwoDiagonalCoordinate g - factorTwoSymmetricCoordinate g =
      yoshidaEndpointA *
        ((yoshidaEndpointOddCleanQuadratic
              (factorTwoCenteredProfile (bombieriRealPartTest gc)) -
            factorTwoCenteredSymmetricPerturbation
              (factorTwoCenteredProfile (bombieriRealPartTest gc))) +
          (yoshidaEndpointOddCleanQuadratic
              (factorTwoCenteredProfile (bombieriImagPartTest gc)) -
            factorTwoCenteredSymmetricPerturbation
              (factorTwoCenteredProfile (bombieriImagPartTest gc)))) := by
  let lambda : ℝ := logarithmicCenter a b
  have hlambda : 0 < lambda := logarithmicCenter_pos a b
  let gc : BombieriTest := normalizedDilation lambda hlambda g
  have haC : 0 < a / lambda := div_pos ha hlambda
  have habC : a / lambda ≤ b / lambda := by
    exact div_le_div_of_nonneg_right hab hlambda.le
  have hsupportC : tsupport gc ⊆ Set.Icc (a / lambda) (b / lambda) := by
    exact normalizedDilation_tsupport_subset_Icc lambda hlambda g hsupport
  have hratioC : (b / lambda) / (a / lambda) ≤ 2 := by
    rw [div_div_div_cancel_right₀ hlambda.ne' b a]
    exact hratio
  have hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA gc := by
    simpa only [gc, lambda, hlambda] using
      logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaEndpointA
        g ha hab hsupport hratio
  have hcentered :=
    factorTwoDiagonal_sub_symmetric_eq_endpoint_mul_two_profiles
      gc haC habC hsupportC hratioC hcritical
  dsimp only
  rw [← factorTwoDiagonalCoordinate_normalizedDilation lambda hlambda g,
    ← factorTwoSymmetricCoordinate_normalizedDilation lambda hlambda g]
  simpa only [gc, lambda, hlambda] using hcentered

/-- Away from its removable endpoint, the adjacent smooth kernel is its
regular part plus the explicit Cauchy pole. -/
theorem factorTwoAdjacentSmoothKernel_eq_cosh_sub_regular_sub_pole
    {u : ℝ} (hu : u ≠ 0) :
    factorTwoAdjacentSmoothKernel u =
      2 * Real.cosh (u / 2) - yoshidaRegularKernel u - 1 / (2 * u) := by
  have hden : Real.exp u - Real.exp (-u) ≠ 0 := by
    intro h
    have heq : Real.exp u = Real.exp (-u) := sub_eq_zero.mp h
    have heqArg : u = -u := Real.exp_injective heq
    exact hu (by linarith)
  rw [factorTwoAdjacentSmoothKernel, oddKernel, yoshidaRegularKernel,
    if_neg hu, Real.sinh_eq]
  field_simp [hu, hden]
  ring

/-- On the open centered interval the symmetric factor-two weight splits
into two regular hyperbolic kernels and two explicit endpoint poles. -/
theorem factorTwoSymmetricWeight_eq_regular_poles
    {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2) :
    factorTwoSymmetricWeight (yoshidaEndpointA * t) =
      2 * Real.cosh (yoshidaEndpointA * (2 + t) / 2) +
        2 * Real.cosh (yoshidaEndpointA * (2 - t) / 2) -
        yoshidaRegularKernel (yoshidaEndpointA * (2 + t)) -
        yoshidaRegularKernel (yoshidaEndpointA * (2 - t)) -
        1 / (2 * yoshidaEndpointA * (2 + t)) -
        1 / (2 * yoshidaEndpointA * (2 - t)) := by
  have hplus : yoshidaEndpointA * (2 + t) ≠ 0 :=
    mul_ne_zero yoshidaEndpointA_pos.ne' (by linarith)
  have hminus : yoshidaEndpointA * (2 - t) ≠ 0 :=
    mul_ne_zero yoshidaEndpointA_pos.ne' (by linarith)
  unfold factorTwoSymmetricWeight
  rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
  rw [show 2 * yoshidaEndpointA + yoshidaEndpointA * t =
        yoshidaEndpointA * (2 + t) by ring,
    show 2 * yoshidaEndpointA - yoshidaEndpointA * t =
        yoshidaEndpointA * (2 - t) by ring,
    factorTwoAdjacentSmoothKernel_eq_cosh_sub_regular_sub_pole hplus,
    factorTwoAdjacentSmoothKernel_eq_cosh_sub_regular_sub_pole hminus]
  ring

/-- The nonsingular hyperbolic-regular part of the centered symmetric
weight. -/
def factorTwoCenteredSymmetricRegularWeight (t : ℝ) : ℝ :=
  2 * Real.cosh (yoshidaEndpointA * (2 + t) / 2) +
    2 * Real.cosh (yoshidaEndpointA * (2 - t) / 2) -
    yoshidaRegularKernel (yoshidaEndpointA * (2 + t)) -
    yoshidaRegularKernel (yoshidaEndpointA * (2 - t))

/-- After multiplying by the endpoint scale, the symmetric weight has two
dimensionless Cauchy poles. -/
theorem yoshidaEndpointA_mul_factorTwoSymmetricWeight_eq_regular_poles
    {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2) :
    yoshidaEndpointA *
        factorTwoSymmetricWeight (yoshidaEndpointA * t) =
      yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
        1 / (2 * (2 + t)) - 1 / (2 * (2 - t)) := by
  rw [factorTwoSymmetricWeight_eq_regular_poles ht0 ht2]
  unfold factorTwoCenteredSymmetricRegularWeight
  have hplus : 2 + t ≠ 0 := by linarith
  have hminus : 2 - t ≠ 0 := by linarith
  field_simp [yoshidaEndpointA_pos.ne', hplus, hminus]

/-- The centered symmetric integrand with both endpoint poles exposed. -/
def factorTwoCenteredSymmetricDesingularizedIntegrand
    (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
      1 / (2 * (2 + t)) - 1 / (2 * (2 - t))) *
    centeredEndpointCorrelation w t

/-- The scaled smooth symmetric integral equals its regular-plus-two-poles
presentation.  Endpoint values are discarded only as a null set. -/
theorem endpoint_mul_integral_symmetricWeight_eq_desingularized
    (w : ℝ → ℝ) :
    yoshidaEndpointA *
        (∫ t : ℝ in 0..2,
          factorTwoSymmetricWeight (yoshidaEndpointA * t) *
            centeredEndpointCorrelation w t) =
      ∫ t : ℝ in 0..2,
        factorTwoCenteredSymmetricDesingularizedIntegrand w t := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [
      (Set.countable_singleton (2 : ℝ)).ae_notMem
        (volume.restrict (Set.uIoc (0 : ℝ) 2)),
      ae_restrict_mem measurableSet_uIoc] with t ht2 ht
  have ht' : t ∈ Set.Ioc (0 : ℝ) 2 := by
    simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have htne : t ≠ 2 := by simpa using ht2
  have htlt : t < 2 := lt_of_le_of_ne ht'.2 htne
  unfold factorTwoCenteredSymmetricDesingularizedIntegrand
  calc
    yoshidaEndpointA *
        (factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          centeredEndpointCorrelation w t) =
      (yoshidaEndpointA *
          factorTwoSymmetricWeight (yoshidaEndpointA * t)) *
        centeredEndpointCorrelation w t := by ring
    _ = _ := by
      rw [yoshidaEndpointA_mul_factorTwoSymmetricWeight_eq_regular_poles
        ht'.1 htlt]

/-- Exact perturbation formula with the reflected endpoint pole visible. -/
theorem factorTwoCenteredSymmetricPerturbation_eq_desingularized
    (w : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbation w =
      (∫ t : ℝ in 0..2,
        factorTwoCenteredSymmetricDesingularizedIntegrand w t) -
      (Real.log 2 / Real.sqrt 2) * centeredEndpointCorrelation w 0 -
      (Real.log 3 / Real.sqrt 3) * centeredEndpointCorrelation w
        (factorTwoPrimeShift / yoshidaEndpointA) := by
  unfold factorTwoCenteredSymmetricPerturbation
  rw [endpoint_mul_integral_symmetricWeight_eq_desingularized]

/-- The reflected endpoint-correlation quotient is interval-integrable for
every continuous profile.  An affine overlap parametrization turns it,
away from the null point `t = 0`, into an integral over the fixed unit
interval. -/
theorem intervalIntegrable_centeredEndpointCorrelation_two_sub_div
    (w : ℝ → ℝ) (hw : Continuous w) :
    IntervalIntegrable
      (fun t : ℝ ↦ centeredEndpointCorrelation w (2 - t) / t)
      volume 0 2 := by
  let phi : ℝ → ℝ → ℝ := fun t y ↦
    w (1 - t + t * y) * w (-1 + t * y)
  let J : ℝ → ℝ := fun t ↦ ∫ y : ℝ in 0..1, phi t y
  have hphi : Continuous phi.uncurry := by
    dsimp only [phi, Function.uncurry]
    fun_prop
  have hJcont : Continuous J := by
    have hset : Continuous (fun t : ℝ ↦
        ∫ y : ℝ in Set.Icc (0 : ℝ) 1, phi t y) :=
      continuous_parametric_integral_of_continuous
        (μ := volume) hphi isCompact_Icc
    have heq : J = fun t : ℝ ↦
        ∫ y : ℝ in Set.Icc (0 : ℝ) 1, phi t y := by
      funext t
      dsimp only [J]
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
    rw [heq]
    exact hset
  have hquot (t : ℝ) (ht : t ≠ 0) :
      centeredEndpointCorrelation w (2 - t) / t = J t := by
    let p : ℝ → ℝ := fun x ↦ w (2 - t + x) * w x
    have hsubst := intervalIntegral.smul_integral_comp_mul_add
      (a := (0 : ℝ)) (b := 1) p t (-1)
    have htransport :
        t * J t = ∫ x : ℝ in -1..-1 + t, p x := by
      calc
        t * J t = t * ∫ y : ℝ in 0..1, p (t * y + -1) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro y _hy
          dsimp only [J, phi, p]
          congr 2 <;> ring
        _ = ∫ x : ℝ in t * 0 + -1..t * 1 + -1, p x := by
          simpa only [smul_eq_mul] using hsubst
        _ = ∫ x : ℝ in -1..-1 + t, p x := by
          simp only [mul_zero, zero_add, mul_one]
          congr 1
          ring
    unfold centeredEndpointCorrelation
    rw [show 1 - (2 - t) = -1 + t by ring]
    change (∫ x : ℝ in -1..-1 + t, p x) / t = J t
    rw [← htransport]
    field_simp [ht]
  apply (hJcont.intervalIntegrable 0 2).congr_ae
  refine ae_restrict_of_ae ?_
  filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 0 by
    simp [ae_iff, measure_singleton]] with t ht
  exact (hquot t ht).symm

/-- Reflection exchanges the two endpoint-pole presentations exactly. -/
theorem integral_centeredEndpointCorrelation_div_two_sub_eq_reflected
    (w : ℝ → ℝ) :
    (∫ t : ℝ in 0..2,
        centeredEndpointCorrelation w t / (2 - t)) =
      ∫ t : ℝ in 0..2,
        centeredEndpointCorrelation w (2 - t) / t := by
  have hreflect := intervalIntegral.integral_comp_sub_left
    (f := fun u : ℝ ↦ centeredEndpointCorrelation w u / (2 - u))
    (a := (0 : ℝ)) (b := 2) 2
  simpa only [sub_zero, sub_self, sub_sub_cancel] using hreflect.symm

/-- The original opposite-endpoint pole quotient is interval-integrable as
well. -/
theorem intervalIntegrable_centeredEndpointCorrelation_div_two_sub
    (w : ℝ → ℝ) (hw : Continuous w) :
    IntervalIntegrable
      (fun t : ℝ ↦ centeredEndpointCorrelation w t / (2 - t))
      volume 0 2 := by
  have hreflect :=
    (intervalIntegrable_centeredEndpointCorrelation_two_sub_div w hw).comp_sub_left 2
  convert hreflect.symm using 1 <;> norm_num

/-- Once the reflected-pole quotient is known interval-integrable, its whole
contribution is bounded by the exact endpoint potential and `log 2` mass.
The pointwise estimate above supplies the sharp factor `1/2`. -/
theorem integral_centeredEndpointCorrelation_two_sub_div_le_potential_mass
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ t : ℝ in 0..2,
        centeredEndpointCorrelation w (2 - t) / t) ≤
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) +
        Real.log 2 * (∫ x : ℝ in -1..1, w x ^ 2) := by
  have hcorr :=
    intervalIntegrable_centeredEndpointCorrelation_two_sub_div w hw
  have hboundary :=
    intervalIntegrable_centeredEndpointBoundaryTail_div w hw
  have hhalfBoundary : IntervalIntegrable
      (fun t : ℝ ↦ (1 / 2 : ℝ) *
        (centeredEndpointBoundaryTail w t / t)) volume 0 2 :=
    hboundary.const_mul (1 / 2 : ℝ)
  have hmono :
      (∫ t : ℝ in 0..2,
          centeredEndpointCorrelation w (2 - t) / t) ≤
        ∫ t : ℝ in 0..2,
          (1 / 2 : ℝ) * (centeredEndpointBoundaryTail w t / t) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hcorr hhalfBoundary
    intro t ht
    by_cases htzero : t = 0
    · simp [htzero]
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
      have hpoint :=
        two_mul_centeredEndpointCorrelation_two_sub_le_boundaryTail
          w hw ht.1
      rw [div_le_iff₀ htpos]
      calc
        centeredEndpointCorrelation w (2 - t) ≤
            centeredEndpointBoundaryTail w t / 2 := by linarith
        _ = (1 / 2 : ℝ) * (centeredEndpointBoundaryTail w t / t) * t := by
          field_simp [htzero]
  calc
    (∫ t : ℝ in 0..2,
        centeredEndpointCorrelation w (2 - t) / t) ≤
        ∫ t : ℝ in 0..2,
          (1 / 2 : ℝ) * (centeredEndpointBoundaryTail w t / t) := hmono
    _ = (1 / 2 : ℝ) *
        (∫ t : ℝ in 0..2, centeredEndpointBoundaryTail w t / t) := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := half_integral_centeredEndpointBoundaryTail_div_eq w hw

/-- The same potential-mass bound in the original `1 / (2 - t)` pole
coordinate. -/
theorem integral_centeredEndpointCorrelation_div_two_sub_le_potential_mass
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ t : ℝ in 0..2,
        centeredEndpointCorrelation w t / (2 - t)) ≤
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) +
        Real.log 2 * (∫ x : ℝ in -1..1, w x ^ 2) := by
  rw [integral_centeredEndpointCorrelation_div_two_sub_eq_reflected]
  exact integral_centeredEndpointCorrelation_two_sub_div_le_potential_mass w hw

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointClean
