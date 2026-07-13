import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointBilinear
import ArithmeticHodge.Analysis.YoshidaPointwiseParityCore

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointParityPencil

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeil
open YoshidaCauchyPairing
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoEndpointClean
open YoshidaEndpointHyperbolicBound
open YoshidaRenormalizedGeometricKernel
open YoshidaPointwiseParityCore
open YoshidaSectionSixAnalytic
open YoshidaStructuralKernelIntegrability

/-!
# Reflection parity of the centered factor-two pencil

The alternating endpoint channel only couples opposite reflection parities.
This file records that fact directly on centered real profiles, before any
finite-dimensional estimate is imposed on the remaining scalar pencil.
-/

/-- Reflection of a centered real profile through the origin. -/
def factorTwoProfileReflection (w : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ w (-x)

@[simp] theorem factorTwoProfileReflection_involutive (w : ℝ → ℝ) :
    factorTwoProfileReflection (factorTwoProfileReflection w) = w := by
  funext x
  unfold factorTwoProfileReflection
  simp

/-- The reflection-even part of a centered real profile. -/
def factorTwoReflectionEvenPart (w : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ (w x + w (-x)) / 2

/-- The reflection-odd part of a centered real profile. -/
def factorTwoReflectionOddPart (w : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ (w x - w (-x)) / 2

theorem factorTwoReflectionEvenPart_even (w : ℝ → ℝ) :
    Function.Even (factorTwoReflectionEvenPart w) := by
  intro x
  unfold factorTwoReflectionEvenPart
  simp only [neg_neg]
  ring

theorem factorTwoReflectionOddPart_odd (w : ℝ → ℝ) :
    Function.Odd (factorTwoReflectionOddPart w) := by
  intro x
  unfold factorTwoReflectionOddPart
  simp only [neg_neg]
  ring

theorem factorTwoReflectionEvenPart_add_oddPart (w : ℝ → ℝ) :
    factorTwoReflectionEvenPart w + factorTwoReflectionOddPart w = w := by
  funext x
  unfold factorTwoReflectionEvenPart factorTwoReflectionOddPart
  simp only [Pi.add_apply]
  ring

theorem continuous_factorTwoReflectionEvenPart
    {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (factorTwoReflectionEvenPart w) := by
  unfold factorTwoReflectionEvenPart
  fun_prop

theorem continuous_factorTwoReflectionOddPart
    {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (factorTwoReflectionOddPart w) := by
  unfold factorTwoReflectionOddPart
  fun_prop

/-- On the actual endpoint-zero periodic core, the clean quadratic splits
exactly across reflection parity.  This uses production-form orthogonality,
not a termwise split of the singular raw logarithmic energy. -/
theorem yoshidaEndpointOddCleanQuadratic_centeredRescale_eq_evenPart_add_oddPart
    (r : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (hreal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hneg : (r : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hpos : (r : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0) :
    let w := centeredRescale yoshidaEndpointA (fun x ↦
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re)
    yoshidaEndpointOddCleanQuadratic w =
      yoshidaEndpointOddCleanQuadratic (factorTwoReflectionEvenPart w) +
        yoshidaEndpointOddCleanQuadratic (factorTwoReflectionOddPart w) := by
  let e : YoshidaClippedPeriodicCore yoshidaEndpointA :=
    periodicCoreEvenPart r
  let o : YoshidaClippedPeriodicCore yoshidaEndpointA :=
    periodicCoreOddPart r
  have hereal : ∀ x : ℝ,
      ((e : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0 := by
    intro x
    dsimp only [e]
    simp only [periodicCoreEvenPart_apply]
    norm_num [Complex.mul_im, hreal x, hreal (-x)]
  have horeal : ∀ x : ℝ,
      ((o : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0 := by
    intro x
    dsimp only [o]
    simp only [periodicCoreOddPart_apply]
    norm_num [Complex.mul_im, hreal x, hreal (-x)]
  have heneg : (e : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0 := by
    dsimp only [e]
    simp only [periodicCoreEvenPart_apply, neg_neg]
    rw [hneg, hpos]
    simp
  have hepos : (e : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0 := by
    dsimp only [e]
    simp only [periodicCoreEvenPart_apply]
    rw [hpos, hneg]
    simp
  have honeg : (o : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0 := by
    dsimp only [o]
    simp only [periodicCoreOddPart_apply, neg_neg]
    rw [hneg, hpos]
    simp
  have hopos : (o : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0 := by
    dsimp only [o]
    simp only [periodicCoreOddPart_apply]
    rw [hpos, hneg]
    simp
  have heProfile :
      centeredRescale yoshidaEndpointA (fun x ↦
        ((e : YoshidaClippedSmooth yoshidaEndpointA) x).re) =
        factorTwoReflectionEvenPart
          (centeredRescale yoshidaEndpointA (fun x ↦
            ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re)) := by
    funext x
    unfold centeredRescale factorTwoReflectionEvenPart
    dsimp only [e]
    simp only [periodicCoreEvenPart_apply]
    rw [show yoshidaEndpointA * -x = -(yoshidaEndpointA * x) by ring]
    norm_num [Complex.mul_re]
    ring
  have hoProfile :
      centeredRescale yoshidaEndpointA (fun x ↦
        ((o : YoshidaClippedSmooth yoshidaEndpointA) x).re) =
        factorTwoReflectionOddPart
          (centeredRescale yoshidaEndpointA (fun x ↦
            ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re)) := by
    funext x
    unfold centeredRescale factorTwoReflectionOddPart
    dsimp only [o]
    simp only [periodicCoreOddPart_apply]
    rw [show yoshidaEndpointA * -x = -(yoshidaEndpointA * x) by ring]
    norm_num [Complex.mul_re]
    ring
  have hsplit := yoshidaClippedLocalCriticalForm_self_eq_even_add_odd
    yoshidaEndpointA_pos r
  have hsplitRe := congrArg Complex.re hsplit
  change clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
      (r : YoshidaClippedSmooth yoshidaEndpointA) =
    clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
        (e : YoshidaClippedSmooth yoshidaEndpointA) +
      clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
        (o : YoshidaClippedSmooth yoshidaEndpointA) at hsplitRe
  have hcleanR :=
    clippedCriticalFormValue_eq_endpoint_mul_clean_of_real_endpoints_zero
      r hreal hneg hpos
  have hcleanE :=
    clippedCriticalFormValue_eq_endpoint_mul_clean_of_real_endpoints_zero
      e hereal heneg hepos
  have hcleanO :=
    clippedCriticalFormValue_eq_endpoint_mul_clean_of_real_endpoints_zero
      o horeal honeg hopos
  rw [hcleanR, hcleanE, hcleanO, heProfile, hoProfile] at hsplitRe
  dsimp only
  nlinarith [yoshidaEndpointA_pos]

/-- Every supported real canonical Bombieri profile inherits the exact clean
reflection-parity split from its endpoint-zero periodic crop. -/
theorem yoshidaEndpointOddCleanQuadratic_factorTwoCenteredProfile_eq_parity
    (g : BombieriTest)
    (hsupport : YoshidaCriticalPullbackSupported yoshidaEndpointA g)
    (hreal : ∀ x : ℝ,
      (g.logarithmicPullbackSchwartz (1 / 2) x).im = 0) :
    yoshidaEndpointOddCleanQuadratic (factorTwoCenteredProfile g) =
      yoshidaEndpointOddCleanQuadratic
          (factorTwoReflectionEvenPart (factorTwoCenteredProfile g)) +
        yoshidaEndpointOddCleanQuadratic
          (factorTwoReflectionOddPart (factorTwoCenteredProfile g)) := by
  let crop : YoshidaClippedSmooth yoshidaEndpointA :=
    yoshidaCriticalPullbackCropLinear yoshidaEndpointA g
  have hmem : crop ∈ yoshidaClippedPeriodicCoreSubmodule
      yoshidaEndpointA := by
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
    criticalPullback_endpoints_zero_of_supported g hsupport
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
  have hprofile :
      centeredRescale yoshidaEndpointA (fun x ↦
        ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re) =
        factorTwoCenteredProfile g := by
    funext x
    unfold centeredRescale factorTwoCenteredProfile
    change (crop (yoshidaEndpointA * x)).re =
      (g.logarithmicPullbackSchwartz
        (1 / 2) (yoshidaEndpointA * x)).re
    rw [show crop (yoshidaEndpointA * x) =
        g.logarithmicPullbackSchwartz
          (1 / 2) (yoshidaEndpointA * x) by
      exact congrFun hcrop (yoshidaEndpointA * x)]
  have hsplit :=
    yoshidaEndpointOddCleanQuadratic_centeredRescale_eq_evenPart_add_oddPart
      r hrreal hrneg hrpos
  dsimp only at hsplit
  rwa [hprofile] at hsplit

/-- Simultaneous reflection reverses the order of centered cross-correlation. -/
theorem factorTwoCenteredCrossCorrelation_reflect_reflect
    (u v : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCrossCorrelation
        (factorTwoProfileReflection u) (factorTwoProfileReflection v) t =
      factorTwoCenteredCrossCorrelation v u t := by
  unfold factorTwoCenteredCrossCorrelation factorTwoProfileReflection
  let f : ℝ → ℝ := fun x ↦ u x * v (t + x)
  have hreflect := intervalIntegral.integral_comp_sub_left
    (f := f) (a := (-1 : ℝ)) (b := 1 - t) (-t)
  have hleft : -t - (1 - t) = (-1 : ℝ) := by ring
  have hright : -t - (-1) = 1 - t := by ring
  calc
    (∫ x : ℝ in -1..1 - t, u (-(t + x)) * v (-x)) =
        ∫ x : ℝ in -1..1 - t, f (-t - x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [f]
      congr 2 <;> ring
    _ = ∫ x : ℝ in -1..1 - t, f x := by
      simpa only [hleft, hright] using hreflect
    _ = ∫ x : ℝ in -1..1 - t, v (t + x) * u x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [f]
      ring

/-- Reflection signs determine the order-reversal sign of centered cross
correlation.  The substitution `x ↦ -t-x` preserves the overlap interval. -/
theorem factorTwoCenteredCrossCorrelation_swap_of_reflection_sign
    (u v : ℝ → ℝ) (eu ev : ℝ)
    (hu : ∀ x : ℝ, u (-x) = eu * u x)
    (hv : ∀ x : ℝ, v (-x) = ev * v x)
    (t : ℝ) :
    factorTwoCenteredCrossCorrelation v u t =
      (eu * ev) * factorTwoCenteredCrossCorrelation u v t := by
  unfold factorTwoCenteredCrossCorrelation
  let f : ℝ → ℝ := fun x ↦ v (t + x) * u x
  have hreflect := intervalIntegral.integral_comp_sub_left
    (f := f) (a := (-1 : ℝ)) (b := 1 - t) (-t)
  have hreflect' :
      (∫ x : ℝ in -1..1 - t, f (-t - x)) =
        ∫ x : ℝ in -1..1 - t, f x := by
    have hleft : -t - (1 - t) = (-1 : ℝ) := by ring
    have hright : -t - (-1) = 1 - t := by ring
    simpa only [hleft, hright] using hreflect
  calc
    (∫ x : ℝ in -1..1 - t, v (t + x) * u x) =
        ∫ x : ℝ in -1..1 - t, f (-t - x) := by
      rw [hreflect']
    _ = ∫ x : ℝ in -1..1 - t,
          (eu * ev) * (u (t + x) * v x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [f]
      rw [show t + (-t - x) = -x by ring,
        show -t - x = -(t + x) by ring, hu, hv]
      ring
    _ = (eu * ev) *
          ∫ x : ℝ in -1..1 - t, u (t + x) * v x := by
      rw [intervalIntegral.integral_const_mul]

theorem factorTwoCenteredCrossCorrelation_swap_of_even_even
    {u v : ℝ → ℝ} (hu : Function.Even u) (hv : Function.Even v)
    (t : ℝ) :
    factorTwoCenteredCrossCorrelation v u t =
      factorTwoCenteredCrossCorrelation u v t := by
  simpa using factorTwoCenteredCrossCorrelation_swap_of_reflection_sign
    u v 1 1 (fun x ↦ by simpa using hu x) (fun x ↦ by simpa using hv x) t

theorem factorTwoCenteredCrossCorrelation_swap_of_odd_odd
    {u v : ℝ → ℝ} (hu : Function.Odd u) (hv : Function.Odd v)
    (t : ℝ) :
    factorTwoCenteredCrossCorrelation v u t =
      factorTwoCenteredCrossCorrelation u v t := by
  simpa using factorTwoCenteredCrossCorrelation_swap_of_reflection_sign
    u v (-1) (-1) (fun x ↦ by simpa using hu x)
      (fun x ↦ by simpa using hv x) t

theorem factorTwoCenteredCrossCorrelation_swap_of_even_odd
    {u v : ℝ → ℝ} (hu : Function.Even u) (hv : Function.Odd v)
    (t : ℝ) :
    factorTwoCenteredCrossCorrelation v u t =
      -factorTwoCenteredCrossCorrelation u v t := by
  simpa using factorTwoCenteredCrossCorrelation_swap_of_reflection_sign
    u v 1 (-1) (fun x ↦ by simpa using hu x)
      (fun x ↦ by simpa using hv x) t

theorem factorTwoCenteredCrossCorrelation_swap_of_odd_even
    {u v : ℝ → ℝ} (hu : Function.Odd u) (hv : Function.Even v)
    (t : ℝ) :
    factorTwoCenteredCrossCorrelation v u t =
      -factorTwoCenteredCrossCorrelation u v t := by
  simpa using factorTwoCenteredCrossCorrelation_swap_of_reflection_sign
    u v (-1) 1 (fun x ↦ by simpa using hu x)
      (fun x ↦ by simpa using hv x) t

/-- The complete symmetric cross kernel is interval-integrable on continuous
profiles.  The shrinking overlap cancels the pole at `t = 2`. -/
theorem intervalIntegrable_factorTwoCenteredSymmetricKernel
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    IntervalIntegrable
      (fun t : ℝ ↦
        factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          factorTwoCenteredCorrelationBilinear u v t)
      volume 0 2 := by
  let d : ℝ → ℝ := fun t ↦
    factorTwoCenteredCorrelationBilinear u v t
  let D : ℝ → ℝ := fun r ↦
    (factorTwoCenteredCrossEndpointQuotient u v r +
      factorTwoCenteredCrossEndpointQuotient v u r) / 2
  have hd : Continuous d := by
    dsimp only [d, factorTwoCenteredCorrelationBilinear]
    exact ((continuous_factorTwoCenteredCrossCorrelation u v hu hv).add
      (continuous_factorTwoCenteredCrossCorrelation v u hv hu)).div_const 2
  have hD : Continuous D := by
    dsimp only [D]
    exact ((continuous_factorTwoCenteredCrossEndpointQuotient u v hu hv).add
      (continuous_factorTwoCenteredCrossEndpointQuotient v u hv hu)).div_const 2
  have hdEndpoint (r : ℝ) : d (2 - r) = r * D r := by
    dsimp only [d, D, factorTwoCenteredCorrelationBilinear]
    rw [factorTwoCenteredCrossCorrelation_two_sub_eq_mul_quotient,
      factorTwoCenteredCrossCorrelation_two_sub_eq_mul_quotient]
    ring
  have hregular : IntervalIntegrable
      (fun t : ℝ ↦
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + t)) * d t)
      volume 0 2 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have harg : yoshidaEndpointA * (2 + t) ≠ 0 :=
      mul_ne_zero yoshidaEndpointA_pos.ne'
        (by nlinarith [ht.1] : 2 + t ≠ 0)
    have hkernelMul : ContinuousAt (fun z : ℝ ↦
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * z)) (2 + t) :=
      (continuousAt_factorTwoAdjacentSmoothKernel_of_ne_zero harg).comp'
        (continuousAt_const.mul continuousAt_id)
    have hkernel : ContinuousAt (fun x : ℝ ↦
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + x))) t :=
      hkernelMul.comp' (continuousAt_const.add continuousAt_id)
    exact (hkernel.mul hd.continuousAt).continuousWithinAt
  let E : ℝ → ℝ := fun z ↦ D (z / yoshidaEndpointA) / yoshidaEndpointA
  have hE : Continuous E := by
    dsimp only [E]
    exact (hD.comp (continuous_id.div_const yoshidaEndpointA)).div_const
      yoshidaEndpointA
  have hoddBase := oddKernel_mul_u_intervalIntegrable hE
    (2 * yoshidaEndpointA)
  have hoddScaled := hoddBase.comp_mul_left (c := yoshidaEndpointA)
  have hoddScaled' : IntervalIntegrable
      (fun r : ℝ ↦
        oddKernel (yoshidaEndpointA * r) *
          (yoshidaEndpointA * r * E (yoshidaEndpointA * r)))
      volume 0 2 := by
    have hright : 2 * yoshidaEndpointA / yoshidaEndpointA = 2 := by
      field_simp [yoshidaEndpointA_pos.ne']
    simpa only [zero_div, hright] using hoddScaled
  have hodd : IntervalIntegrable
      (fun r : ℝ ↦
        oddKernel (yoshidaEndpointA * r) * (r * D r))
      volume 0 2 := by
    apply hoddScaled'.congr
    intro r _hr
    dsimp only [E]
    have hdiv : yoshidaEndpointA * r / yoshidaEndpointA = r := by
      field_simp [yoshidaEndpointA_pos.ne']
    rw [hdiv]
    field_simp [yoshidaEndpointA_pos.ne']
  have hcosh : IntervalIntegrable
      (fun r : ℝ ↦
        2 * Real.cosh (yoshidaEndpointA * r / 2) * (r * D r))
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.mul
      (Real.continuous_cosh.comp
        ((continuous_const.mul continuous_id).div_const 2))).mul
      (continuous_id.mul hD)
  have hreflectedKernel : IntervalIntegrable
      (fun r : ℝ ↦
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * r) *
          (r * D r))
      volume 0 2 := by
    have hsplit := hcosh.sub (hodd.const_mul (1 / 2 : ℝ))
    apply hsplit.congr
    intro r _hr
    unfold factorTwoAdjacentSmoothKernel
    ring
  have hreflected := hreflectedKernel.comp_sub_left 2
  have hreflected' : IntervalIntegrable
      (fun t : ℝ ↦
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 - t)) *
          ((2 - t) * D (2 - t)))
      volume 0 2 := by
    simpa only [sub_zero, sub_self] using hreflected.symm
  have hsingular : IntervalIntegrable
      (fun t : ℝ ↦
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 - t)) * d t)
      volume 0 2 := by
    apply hreflected'.congr
    intro t _ht
    have hfactor := hdEndpoint (2 - t)
    rw [show 2 - (2 - t) = t by ring] at hfactor
    change factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 - t)) *
        ((2 - t) * D (2 - t)) =
      factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 - t)) * d t
    rw [hfactor]
  have hsplit := hregular.add hsingular
  apply hsplit.congr
  intro t _ht
  dsimp only [d]
  unfold factorTwoSymmetricWeight
  rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
  ring_nf

/-- The genuine symmetric polarization of the complete factor-two endpoint
perturbation, with the singular integral and both prime atoms kept together. -/
def factorTwoCenteredSymmetricPerturbationBilinear
    (u v : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA *
      (∫ t : ℝ in 0..2,
        factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          factorTwoCenteredCorrelationBilinear u v t) -
    (Real.log 2 / Real.sqrt 2) *
      factorTwoCenteredCorrelationBilinear u v 0 -
    (Real.log 3 / Real.sqrt 3) *
      factorTwoCenteredCorrelationBilinear u v
        (factorTwoPrimeShift / yoshidaEndpointA)

theorem factorTwoCenteredSymmetricPerturbationBilinear_self
    (w : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear w w =
      factorTwoCenteredSymmetricPerturbation w := by
  unfold factorTwoCenteredSymmetricPerturbationBilinear
    factorTwoCenteredSymmetricPerturbation
  simp_rw [factorTwoCenteredCorrelationBilinear_self]

/-- On its continuous form domain, the complete symmetric perturbation has
the advertised bilinear polarization. -/
theorem factorTwoCenteredSymmetricPerturbation_add_eq_bilinear
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    factorTwoCenteredSymmetricPerturbation (u + v) =
      factorTwoCenteredSymmetricPerturbation u +
        2 * factorTwoCenteredSymmetricPerturbationBilinear u v +
      factorTwoCenteredSymmetricPerturbation v := by
  have huu0 := intervalIntegrable_factorTwoCenteredSymmetricKernel
    u u hu hu
  have huv := intervalIntegrable_factorTwoCenteredSymmetricKernel
    u v hu hv
  have hvv0 := intervalIntegrable_factorTwoCenteredSymmetricKernel
    v v hv hv
  have huu : IntervalIntegrable
      (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        centeredEndpointCorrelation u t) volume 0 2 := by
    simpa only [factorTwoCenteredCorrelationBilinear_self] using huu0
  have hvv : IntervalIntegrable
      (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        centeredEndpointCorrelation v t) volume 0 2 := by
    simpa only [factorTwoCenteredCorrelationBilinear_self] using hvv0
  have htwo : IntervalIntegrable
      (fun t : ℝ ↦ 2 *
        (factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          factorTwoCenteredCorrelationBilinear u v t)) volume 0 2 :=
    huv.const_mul 2
  have hfun :
      (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        centeredEndpointCorrelation (u + v) t) =
      fun t ↦
        (factorTwoSymmetricWeight (yoshidaEndpointA * t) *
            centeredEndpointCorrelation u t +
          2 * (factorTwoSymmetricWeight (yoshidaEndpointA * t) *
            factorTwoCenteredCorrelationBilinear u v t)) +
        factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          centeredEndpointCorrelation v t := by
    funext t
    rw [centeredEndpointCorrelation_add u v hu hv t]
    ring
  unfold factorTwoCenteredSymmetricPerturbation
    factorTwoCenteredSymmetricPerturbationBilinear
  rw [hfun,
    intervalIntegral.integral_add (huu.add htwo) hvv,
    intervalIntegral.integral_add huu htwo,
    intervalIntegral.integral_const_mul,
    centeredEndpointCorrelation_add u v hu hv 0,
    centeredEndpointCorrelation_add u v hu hv
      (factorTwoPrimeShift / yoshidaEndpointA)]
  ring

theorem factorTwoCenteredSymmetricPerturbationBilinear_eq_polarization
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    factorTwoCenteredSymmetricPerturbationBilinear u v =
      factorTwoCenteredSymmetricPerturbationPolarization u v := by
  have hadd := factorTwoCenteredSymmetricPerturbation_add_eq_bilinear
    u v hu hv
  unfold factorTwoCenteredSymmetricPerturbationPolarization
  linarith

theorem factorTwoCenteredCorrelationBilinear_eq_zero_of_even_odd
    {e o : ℝ → ℝ} (he : Function.Even e) (ho : Function.Odd o)
    (t : ℝ) :
    factorTwoCenteredCorrelationBilinear e o t = 0 := by
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_swap_of_even_odd he ho]
  ring

theorem factorTwoCenteredSymmetricPerturbationBilinear_eq_zero_of_even_odd
    {e o : ℝ → ℝ} (he : Function.Even e) (ho : Function.Odd o) :
    factorTwoCenteredSymmetricPerturbationBilinear e o = 0 := by
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_eq_zero_of_even_odd he ho]
  simp

/-- The complete symmetric perturbation splits across continuous opposite
reflection parities. -/
theorem factorTwoCenteredSymmetricPerturbation_add_of_even_odd
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o) :
    factorTwoCenteredSymmetricPerturbation (e + o) =
      factorTwoCenteredSymmetricPerturbation e +
        factorTwoCenteredSymmetricPerturbation o := by
  rw [factorTwoCenteredSymmetricPerturbation_add_eq_bilinear
      e o hec hoc,
    factorTwoCenteredSymmetricPerturbationBilinear_eq_zero_of_even_odd he ho]
  ring

/-- Every continuous profile's symmetric perturbation is the sum of its even
and odd reflection sectors. -/
theorem factorTwoCenteredSymmetricPerturbation_eq_evenPart_add_oddPart
    (w : ℝ → ℝ) (hw : Continuous w) :
    factorTwoCenteredSymmetricPerturbation w =
      factorTwoCenteredSymmetricPerturbation
          (factorTwoReflectionEvenPart w) +
        factorTwoCenteredSymmetricPerturbation
          (factorTwoReflectionOddPart w) := by
  let e := factorTwoReflectionEvenPart w
  let o := factorTwoReflectionOddPart w
  have hec : Continuous e := continuous_factorTwoReflectionEvenPart hw
  have hoc : Continuous o := continuous_factorTwoReflectionOddPart hw
  have hsplit : e + o = w := factorTwoReflectionEvenPart_add_oddPart w
  calc
    factorTwoCenteredSymmetricPerturbation w =
        factorTwoCenteredSymmetricPerturbation (e + o) := by rw [hsplit]
    _ = factorTwoCenteredSymmetricPerturbation e +
        factorTwoCenteredSymmetricPerturbation o :=
      factorTwoCenteredSymmetricPerturbation_add_of_even_odd e o hec hoc
        (factorTwoReflectionEvenPart_even w)
        (factorTwoReflectionOddPart_odd w)
    _ = _ := by rfl

/-- The positive signed endpoint energy of a supported real canonical profile
splits exactly across reflection parity. -/
theorem factorTwoCenteredEndpointPlus_factorTwoCenteredProfile_eq_parity
    (g : BombieriTest)
    (hsupport : YoshidaCriticalPullbackSupported yoshidaEndpointA g)
    (hreal : ∀ x : ℝ,
      (g.logarithmicPullbackSchwartz (1 / 2) x).im = 0) :
    factorTwoCenteredEndpointPlus (factorTwoCenteredProfile g) =
      factorTwoCenteredEndpointPlus
          (factorTwoReflectionEvenPart (factorTwoCenteredProfile g)) +
        factorTwoCenteredEndpointPlus
          (factorTwoReflectionOddPart (factorTwoCenteredProfile g)) := by
  have hQ :=
    yoshidaEndpointOddCleanQuadratic_factorTwoCenteredProfile_eq_parity
      g hsupport hreal
  have hw : Continuous (factorTwoCenteredProfile g) := by
    unfold factorTwoCenteredProfile
    fun_prop
  have hP :=
    factorTwoCenteredSymmetricPerturbation_eq_evenPart_add_oddPart
      (factorTwoCenteredProfile g) hw
  unfold factorTwoCenteredEndpointPlus
  rw [hQ, hP]
  ring

/-- The negative signed endpoint energy of a supported real canonical profile
splits exactly across reflection parity. -/
theorem factorTwoCenteredEndpointMinus_factorTwoCenteredProfile_eq_parity
    (g : BombieriTest)
    (hsupport : YoshidaCriticalPullbackSupported yoshidaEndpointA g)
    (hreal : ∀ x : ℝ,
      (g.logarithmicPullbackSchwartz (1 / 2) x).im = 0) :
    factorTwoCenteredEndpointMinus (factorTwoCenteredProfile g) =
      factorTwoCenteredEndpointMinus
          (factorTwoReflectionEvenPart (factorTwoCenteredProfile g)) +
        factorTwoCenteredEndpointMinus
          (factorTwoReflectionOddPart (factorTwoCenteredProfile g)) := by
  have hQ :=
    yoshidaEndpointOddCleanQuadratic_factorTwoCenteredProfile_eq_parity
      g hsupport hreal
  have hw : Continuous (factorTwoCenteredProfile g) := by
    unfold factorTwoCenteredProfile
    fun_prop
  have hP :=
    factorTwoCenteredSymmetricPerturbation_eq_evenPart_add_oddPart
      (factorTwoCenteredProfile g) hw
  unfold factorTwoCenteredEndpointMinus
  rw [hQ, hP]
  ring

/-- The positive diagonal coefficient after exact reflection decomposition. -/
def factorTwoReflectionParityEndpointPlusSum
    (u v : ℝ → ℝ) : ℝ :=
  (factorTwoCenteredEndpointPlus (factorTwoReflectionEvenPart u) +
      factorTwoCenteredEndpointPlus (factorTwoReflectionOddPart u)) +
    (factorTwoCenteredEndpointPlus (factorTwoReflectionEvenPart v) +
      factorTwoCenteredEndpointPlus (factorTwoReflectionOddPart v))

/-- The negative diagonal coefficient after exact reflection decomposition. -/
def factorTwoReflectionParityEndpointMinusSum
    (u v : ℝ → ℝ) : ℝ :=
  (factorTwoCenteredEndpointMinus (factorTwoReflectionEvenPart u) +
      factorTwoCenteredEndpointMinus (factorTwoReflectionOddPart u)) +
    (factorTwoCenteredEndpointMinus (factorTwoReflectionEvenPart v) +
      factorTwoCenteredEndpointMinus (factorTwoReflectionOddPart v))

/-- The two opposite-parity channels comprising the alternating coefficient. -/
def factorTwoReflectionParityAlternatingSum
    (u v : ℝ → ℝ) : ℝ :=
  factorTwoCenteredAlternatingCoupling
      (factorTwoReflectionEvenPart u) (factorTwoReflectionOddPart v) +
    factorTwoCenteredAlternatingCoupling
      (factorTwoReflectionOddPart u) (factorTwoReflectionEvenPart v)

/-- The exact scalar pencil in reflection-parity block coordinates. -/
def factorTwoReflectionParityPencil
    (u v : ℝ → ℝ) (r s : ℝ) : ℝ :=
  factorTwoReflectionParityEndpointPlusSum u v * r ^ 2 +
    2 * factorTwoReflectionParityAlternatingSum u v * r * s +
    factorTwoReflectionParityEndpointMinusSum u v * s ^ 2

/-- The channel coupling the even part of the first profile to the odd part
of the second. -/
def factorTwoReflectionEvenOddChannelPencil
    (u v : ℝ → ℝ) (r s : ℝ) : ℝ :=
  (factorTwoCenteredEndpointPlus (factorTwoReflectionEvenPart u) +
      factorTwoCenteredEndpointPlus (factorTwoReflectionOddPart v)) * r ^ 2 +
    2 * factorTwoCenteredAlternatingCoupling
        (factorTwoReflectionEvenPart u) (factorTwoReflectionOddPart v) *
      r * s +
    (factorTwoCenteredEndpointMinus (factorTwoReflectionEvenPart u) +
      factorTwoCenteredEndpointMinus (factorTwoReflectionOddPart v)) * s ^ 2

/-- The channel coupling the odd part of the first profile to the even part
of the second. -/
def factorTwoReflectionOddEvenChannelPencil
    (u v : ℝ → ℝ) (r s : ℝ) : ℝ :=
  (factorTwoCenteredEndpointPlus (factorTwoReflectionOddPart u) +
      factorTwoCenteredEndpointPlus (factorTwoReflectionEvenPart v)) * r ^ 2 +
    2 * factorTwoCenteredAlternatingCoupling
        (factorTwoReflectionOddPart u) (factorTwoReflectionEvenPart v) *
      r * s +
    (factorTwoCenteredEndpointMinus (factorTwoReflectionOddPart u) +
      factorTwoCenteredEndpointMinus (factorTwoReflectionEvenPart v)) * s ^ 2

/-- The reflection-parity pencil is exactly the sum of its two
opposite-parity channel pencils. -/
theorem factorTwoReflectionParityPencil_eq_channel_sum
    (u v : ℝ → ℝ) (r s : ℝ) :
    factorTwoReflectionParityPencil u v r s =
      factorTwoReflectionEvenOddChannelPencil u v r s +
        factorTwoReflectionOddEvenChannelPencil u v r s := by
  unfold factorTwoReflectionParityPencil
    factorTwoReflectionParityEndpointPlusSum
    factorTwoReflectionParityEndpointMinusSum
    factorTwoReflectionParityAlternatingSum
    factorTwoReflectionEvenOddChannelPencil
    factorTwoReflectionOddEvenChannelPencil
  ring

/-- Nonnegativity of both canonical opposite-parity channel pencils is a
sufficient structural route to nonnegativity of the complete pencil. -/
theorem factorTwoReflectionParityPencil_nonneg_of_channels
    (u v : ℝ → ℝ)
    (hEvenOdd : ∀ r s : ℝ,
      0 ≤ factorTwoReflectionEvenOddChannelPencil u v r s)
    (hOddEven : ∀ r s : ℝ,
      0 ≤ factorTwoReflectionOddEvenChannelPencil u v r s) :
    ∀ r s : ℝ, 0 ≤ factorTwoReflectionParityPencil u v r s := by
  intro r s
  rw [factorTwoReflectionParityPencil_eq_channel_sum]
  exact add_nonneg (hEvenOdd r s) (hOddEven r s)

/-- Simultaneous reflection negates the complete alternating channel. -/
theorem factorTwoCenteredAlternatingCoupling_reflect_reflect
    (u v : ℝ → ℝ) :
    factorTwoCenteredAlternatingCoupling
        (factorTwoProfileReflection u) (factorTwoProfileReflection v) =
      -factorTwoCenteredAlternatingCoupling u v := by
  unfold factorTwoCenteredAlternatingCoupling
  rw [show (fun t : ℝ ↦
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation
            (factorTwoProfileReflection v) (factorTwoProfileReflection u) t -
          factorTwoCenteredCrossCorrelation
            (factorTwoProfileReflection u) (factorTwoProfileReflection v) t)) =
      fun t ↦ -(factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation v u t -
          factorTwoCenteredCrossCorrelation u v t)) by
    funext t
    rw [factorTwoCenteredCrossCorrelation_reflect_reflect,
      factorTwoCenteredCrossCorrelation_reflect_reflect]
    ring,
    intervalIntegral.integral_neg,
    factorTwoCenteredCrossCorrelation_reflect_reflect,
    factorTwoCenteredCrossCorrelation_reflect_reflect]
  ring

/-- The alternating channel anticommutes with profile reflection. -/
theorem factorTwoCenteredAlternatingCoupling_reflection_anticommutes
    (u v : ℝ → ℝ) :
    factorTwoCenteredAlternatingCoupling (factorTwoProfileReflection u) v =
      -factorTwoCenteredAlternatingCoupling u (factorTwoProfileReflection v) := by
  have hreflect := factorTwoCenteredAlternatingCoupling_reflect_reflect
    u (factorTwoProfileReflection v)
  simpa using hreflect

theorem factorTwoCenteredAlternatingCoupling_eq_zero_of_even_even
    {u v : ℝ → ℝ} (hu : Function.Even u) (hv : Function.Even v) :
    factorTwoCenteredAlternatingCoupling u v = 0 := by
  have hintegral :
      (∫ t : ℝ in 0..2,
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation v u t -
          factorTwoCenteredCrossCorrelation u v t)) = 0 := by
    calc
      _ = ∫ _t : ℝ in 0..2, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        change factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            (factorTwoCenteredCrossCorrelation v u t -
              factorTwoCenteredCrossCorrelation u v t) = 0
        rw [factorTwoCenteredCrossCorrelation_swap_of_even_even hu hv]
        ring
      _ = 0 := intervalIntegral.integral_zero
  unfold factorTwoCenteredAlternatingCoupling
  rw [hintegral,
    factorTwoCenteredCrossCorrelation_swap_of_even_even hu hv]
  ring

theorem factorTwoCenteredAlternatingCoupling_eq_zero_of_odd_odd
    {u v : ℝ → ℝ} (hu : Function.Odd u) (hv : Function.Odd v) :
    factorTwoCenteredAlternatingCoupling u v = 0 := by
  have hintegral :
      (∫ t : ℝ in 0..2,
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation v u t -
          factorTwoCenteredCrossCorrelation u v t)) = 0 := by
    calc
      _ = ∫ _t : ℝ in 0..2, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        change factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            (factorTwoCenteredCrossCorrelation v u t -
              factorTwoCenteredCrossCorrelation u v t) = 0
        rw [factorTwoCenteredCrossCorrelation_swap_of_odd_odd hu hv]
        ring
      _ = 0 := intervalIntegral.integral_zero
  unfold factorTwoCenteredAlternatingCoupling
  rw [hintegral,
    factorTwoCenteredCrossCorrelation_swap_of_odd_odd hu hv]
  ring

/-- The exact alternating coupling of arbitrary continuous profiles is the
sum of its two opposite-parity channels. -/
theorem factorTwoCenteredAlternatingCoupling_eq_evenOdd_add_oddEven
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    factorTwoCenteredAlternatingCoupling u v =
      factorTwoCenteredAlternatingCoupling
          (factorTwoReflectionEvenPart u) (factorTwoReflectionOddPart v) +
        factorTwoCenteredAlternatingCoupling
          (factorTwoReflectionOddPart u) (factorTwoReflectionEvenPart v) := by
  let ue := factorTwoReflectionEvenPart u
  let uo := factorTwoReflectionOddPart u
  let ve := factorTwoReflectionEvenPart v
  let vo := factorTwoReflectionOddPart v
  have hue : Continuous ue := continuous_factorTwoReflectionEvenPart hu
  have huo : Continuous uo := continuous_factorTwoReflectionOddPart hu
  have hve : Continuous ve := continuous_factorTwoReflectionEvenPart hv
  have hvo : Continuous vo := continuous_factorTwoReflectionOddPart hv
  have hu_split : ue + uo = u := factorTwoReflectionEvenPart_add_oddPart u
  have hv_split : ve + vo = v := factorTwoReflectionEvenPart_add_oddPart v
  have hJee : factorTwoCenteredAlternatingCoupling ue ve = 0 :=
    factorTwoCenteredAlternatingCoupling_eq_zero_of_even_even
      (factorTwoReflectionEvenPart_even u)
      (factorTwoReflectionEvenPart_even v)
  have hJoo : factorTwoCenteredAlternatingCoupling uo vo = 0 :=
    factorTwoCenteredAlternatingCoupling_eq_zero_of_odd_odd
      (factorTwoReflectionOddPart_odd u)
      (factorTwoReflectionOddPart_odd v)
  calc
    factorTwoCenteredAlternatingCoupling u v =
        factorTwoCenteredAlternatingCoupling (ue + uo) (ve + vo) := by
      rw [hu_split, hv_split]
    _ = (factorTwoCenteredAlternatingCoupling ue ve +
          factorTwoCenteredAlternatingCoupling ue vo) +
        (factorTwoCenteredAlternatingCoupling uo ve +
          factorTwoCenteredAlternatingCoupling uo vo) := by
      rw [factorTwoCenteredAlternatingCoupling_add_left
          ue uo (ve + vo) hue huo (hve.add hvo),
        factorTwoCenteredAlternatingCoupling_add_right ue ve vo hue hve hvo,
        factorTwoCenteredAlternatingCoupling_add_right uo ve vo huo hve hvo]
    _ = factorTwoCenteredAlternatingCoupling ue vo +
        factorTwoCenteredAlternatingCoupling uo ve := by
      rw [hJee, hJoo]
      ring
    _ = _ := by rfl

/-- For two supported real canonical profiles, the original scalar pencil is
exactly its reflection-parity block presentation. -/
theorem factorTwoCenteredPencil_eq_reflectionParity
    (gu gv : BombieriTest)
    (huSupport : YoshidaCriticalPullbackSupported yoshidaEndpointA gu)
    (hvSupport : YoshidaCriticalPullbackSupported yoshidaEndpointA gv)
    (huReal : ∀ x : ℝ,
      (gu.logarithmicPullbackSchwartz (1 / 2) x).im = 0)
    (hvReal : ∀ x : ℝ,
      (gv.logarithmicPullbackSchwartz (1 / 2) x).im = 0)
    (r s : ℝ) :
    let u := factorTwoCenteredProfile gu
    let v := factorTwoCenteredProfile gv
    (factorTwoCenteredEndpointPlus u +
          factorTwoCenteredEndpointPlus v) * r ^ 2 +
        2 * factorTwoCenteredAlternatingCoupling u v * r * s +
        (factorTwoCenteredEndpointMinus u +
          factorTwoCenteredEndpointMinus v) * s ^ 2 =
      factorTwoReflectionParityPencil u v r s := by
  let u := factorTwoCenteredProfile gu
  let v := factorTwoCenteredProfile gv
  have hplusU :=
    factorTwoCenteredEndpointPlus_factorTwoCenteredProfile_eq_parity
      gu huSupport huReal
  have hplusV :=
    factorTwoCenteredEndpointPlus_factorTwoCenteredProfile_eq_parity
      gv hvSupport hvReal
  have hminusU :=
    factorTwoCenteredEndpointMinus_factorTwoCenteredProfile_eq_parity
      gu huSupport huReal
  have hminusV :=
    factorTwoCenteredEndpointMinus_factorTwoCenteredProfile_eq_parity
      gv hvSupport hvReal
  have hu : Continuous u := by
    dsimp only [u]
    unfold factorTwoCenteredProfile
    fun_prop
  have hv : Continuous v := by
    dsimp only [v]
    unfold factorTwoCenteredProfile
    fun_prop
  have hJ :=
    factorTwoCenteredAlternatingCoupling_eq_evenOdd_add_oddEven u v hu hv
  dsimp only
  unfold factorTwoReflectionParityPencil
    factorTwoReflectionParityEndpointPlusSum
    factorTwoReflectionParityEndpointMinusSum
    factorTwoReflectionParityAlternatingSum
  rw [hplusU, hplusV, hminusU, hminusV, hJ]

/-- Universal production two-bump positivity is exactly nonnegativity of the
reflection-parity block pencil for the canonical real/imaginary profile pair. -/
theorem bombieriFunctional_twoBump_nonneg_iff_logCentered_reflectionParityPencil
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
      let gc := normalizedDilation (logarithmicCenter a b)
        (logarithmicCenter_pos a b) g
      let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
      let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
      ∀ r s : ℝ, 0 ≤ factorTwoReflectionParityPencil u v r s := by
  let gc := normalizedDilation (logarithmicCenter a b)
    (logarithmicCenter_pos a b) g
  let gu := bombieriRealPartTest gc
  let gv := bombieriImagPartTest gc
  have hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA gc := by
    simpa only [gc] using
      logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaEndpointA
        g ha hab hsupport hratio
  have huSupport : YoshidaCriticalPullbackSupported yoshidaEndpointA gu := by
    exact bombieriRealPartTest_criticalPullbackSupported gc hcritical
  have hvSupport : YoshidaCriticalPullbackSupported yoshidaEndpointA gv := by
    exact bombieriImagPartTest_criticalPullbackSupported gc hcritical
  have huReal : ∀ x : ℝ,
      (gu.logarithmicPullbackSchwartz (1 / 2) x).im = 0 :=
    bombieriRealPartTest_criticalPullback_im_eq_zero gc
  have hvReal : ∀ x : ℝ,
      (gv.logarithmicPullbackSchwartz (1 / 2) x).im = 0 :=
    bombieriImagPartTest_criticalPullback_im_eq_zero gc
  have hscalar0 :=
    bombieriFunctional_twoBump_nonneg_iff_logCentered_scalarPencil
      g ha hab hsupport hratio
  have hscalar :
      (∀ c : ℂ,
        0 ≤ (bombieriFunctional
          (bombieriQuadraticTest
            (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
        ∀ r s : ℝ,
          0 ≤ (factorTwoCenteredEndpointPlus (factorTwoCenteredProfile gu) +
                factorTwoCenteredEndpointPlus (factorTwoCenteredProfile gv)) *
              r ^ 2 +
            2 * factorTwoCenteredAlternatingCoupling
                (factorTwoCenteredProfile gu) (factorTwoCenteredProfile gv) *
              r * s +
            (factorTwoCenteredEndpointMinus (factorTwoCenteredProfile gu) +
                factorTwoCenteredEndpointMinus (factorTwoCenteredProfile gv)) *
              s ^ 2 := by
    simpa only [gc, gu, gv] using hscalar0
  have hrewrite (r s : ℝ) :=
    factorTwoCenteredPencil_eq_reflectionParity
      gu gv huSupport hvSupport huReal hvReal r s
  change
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
      ∀ r s : ℝ,
        0 ≤ factorTwoReflectionParityPencil
          (factorTwoCenteredProfile gu) (factorTwoCenteredProfile gv) r s
  constructor
  · intro hfamily r s
    rw [← hrewrite r s]
    exact hscalar.mp hfamily r s
  · intro hpencil
    apply hscalar.mpr
    intro r s
    rw [hrewrite r s]
    exact hpencil r s

/-- A negative production member exists exactly when the canonical
reflection-parity block pencil has a strict negative real direction. -/
theorem exists_bombieriFunctional_twoBump_neg_iff_logCentered_reflectionParityPencil
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∃ c : ℂ,
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re < 0) ↔
      let gc := normalizedDilation (logarithmicCenter a b)
        (logarithmicCenter_pos a b) g
      let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
      let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
      ∃ r s : ℝ, factorTwoReflectionParityPencil u v r s < 0 := by
  let gc := normalizedDilation (logarithmicCenter a b)
    (logarithmicCenter_pos a b) g
  let gu := bombieriRealPartTest gc
  let gv := bombieriImagPartTest gc
  have hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA gc := by
    simpa only [gc] using
      logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaEndpointA
        g ha hab hsupport hratio
  have huSupport : YoshidaCriticalPullbackSupported yoshidaEndpointA gu := by
    exact bombieriRealPartTest_criticalPullbackSupported gc hcritical
  have hvSupport : YoshidaCriticalPullbackSupported yoshidaEndpointA gv := by
    exact bombieriImagPartTest_criticalPullbackSupported gc hcritical
  have huReal : ∀ x : ℝ,
      (gu.logarithmicPullbackSchwartz (1 / 2) x).im = 0 :=
    bombieriRealPartTest_criticalPullback_im_eq_zero gc
  have hvReal : ∀ x : ℝ,
      (gv.logarithmicPullbackSchwartz (1 / 2) x).im = 0 :=
    bombieriImagPartTest_criticalPullback_im_eq_zero gc
  have hnegative0 :=
    exists_bombieriFunctional_twoBump_neg_iff_logCentered_scalarPencil
      g ha hab hsupport hratio
  have hnegative :
      (∃ c : ℂ,
        (bombieriFunctional
          (bombieriQuadraticTest
            (g + c • normalizedDilation 2 (by norm_num) g))).re < 0) ↔
        ∃ r s : ℝ,
          (factorTwoCenteredEndpointPlus (factorTwoCenteredProfile gu) +
                factorTwoCenteredEndpointPlus (factorTwoCenteredProfile gv)) *
              r ^ 2 +
            2 * factorTwoCenteredAlternatingCoupling
                (factorTwoCenteredProfile gu) (factorTwoCenteredProfile gv) *
              r * s +
            (factorTwoCenteredEndpointMinus (factorTwoCenteredProfile gu) +
                factorTwoCenteredEndpointMinus (factorTwoCenteredProfile gv)) *
              s ^ 2 < 0 := by
    simpa only [gc, gu, gv] using hnegative0
  have hrewrite (r s : ℝ) :=
    factorTwoCenteredPencil_eq_reflectionParity
      gu gv huSupport hvSupport huReal hvReal r s
  change
    (∃ c : ℂ,
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re < 0) ↔
      ∃ r s : ℝ,
        factorTwoReflectionParityPencil
          (factorTwoCenteredProfile gu) (factorTwoCenteredProfile gv) r s < 0
  constructor
  · intro hmember
    obtain ⟨r, s, hrs⟩ := hnegative.mp hmember
    refine ⟨r, s, ?_⟩
    rw [← hrewrite r s]
    exact hrs
  · rintro ⟨r, s, hrs⟩
    apply hnegative.mpr
    refine ⟨r, s, ?_⟩
    rw [hrewrite r s]
    exact hrs

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointParityPencil
