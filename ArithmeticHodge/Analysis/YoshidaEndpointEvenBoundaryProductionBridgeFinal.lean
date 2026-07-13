import ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryProductionBridge
import ArithmeticHodge.Analysis.YoshidaClippedRealImagEnergySplit
import ArithmeticHodge.Analysis.YoshidaEndpointClippedArchBridge
import ArithmeticHodge.Analysis.YoshidaEndpointEvenCleanPositive
import ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualProduction
import ArithmeticHodge.Analysis.YoshidaEndpointPhysicalRealQuadratic
import ArithmeticHodge.Analysis.YoshidaEndpointScaledCorrelation
import ArithmeticHodge.Analysis.YoshidaPointwiseEvenRealImag
import ArithmeticHodge.Analysis.YoshidaPointwiseOddRealImag

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set Topology

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryProductionBridge

open ArithmeticHodge.Analysis
open YoshidaClippedRealImag
open YoshidaClippedRealImagEnergySplit
open YoshidaClippedEndpointContinuous
open YoshidaEndpointClippedArchBridge
open YoshidaEndpointClippedPolarBridge
open YoshidaEndpointEvenBoundaryResidual
open YoshidaEndpointEvenCleanPositive
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenResidualProduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPhysicalRealQuadratic
open YoshidaEndpointPolarScaling
open YoshidaEndpointScaledCorrelation
open YoshidaPointwiseOddRealImag
open YoshidaPointwiseEvenRealImag
open YoshidaPointwiseParityCore
open YoshidaRenormalizedGeometricKernel
open YoshidaRegularKernelBound
open YoshidaSectionSixAnalytic
open YoshidaStructuralKernelIntegrability

noncomputable section

/-! ## The clipped constant diagonal -/

private theorem neg_stableGeometricIntegrand_eq_boundary_integrand
    (C0 : ℝ) (C : ℝ → ℝ) {u : ℝ} (hu : u ≠ 0) :
    -stableGeometricIntegrand C0 C u =
      (C0 - C u) / u - 2 * yoshidaRegularKernel u * C u := by
  have hden : Real.exp u - Real.exp (-u) ≠ 0 := by
    intro h
    have heq : Real.exp u = Real.exp (-u) := sub_eq_zero.mp h
    have : u = -u := Real.exp_injective heq
    exact hu (by linarith)
  rw [stableGeometricIntegrand, oddKernel, yoshidaRegularKernel,
    if_neg hu, Real.sinh_eq]
  field_simp [hu, hden]
  ring

private theorem constant_defect_intervalIntegrable :
    IntervalIntegrable
      (fun u : ℝ ↦
        (constantEndpointCorrelation yoshidaEndpointA 0 -
          constantEndpointCorrelation yoshidaEndpointA u) / u)
      volume 0 (2 * yoshidaEndpointA) := by
  have hone : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume
      0 (2 * yoshidaEndpointA) := continuous_const.intervalIntegrable _ _
  apply hone.congr_ae
  refine ae_restrict_of_ae ?_
  filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
    simp [ae_iff, measure_singleton]] with u hu
  unfold constantEndpointCorrelation
  field_simp [hu]
  ring

private theorem constant_boundary_integrand_intervalIntegrable :
    IntervalIntegrable
      (fun u : ℝ ↦
        (constantEndpointCorrelation yoshidaEndpointA 0 -
            constantEndpointCorrelation yoshidaEndpointA u) / u -
          2 * yoshidaRegularKernel u *
            constantEndpointCorrelation yoshidaEndpointA u)
      volume 0 (2 * yoshidaEndpointA) := by
  let C : ℝ → ℝ := constantEndpointCorrelation yoshidaEndpointA
  let D : ℝ → ℝ := fun _ ↦ -1
  have hstable : IntervalIntegrable
      (stableGeometricIntegrand (C 0) C) volume
        0 (2 * yoshidaEndpointA) :=
    stableGeometricIntegrand_intervalIntegrable_of_removable
      (C := C) (D := D) continuous_const (C 0)
      (2 * yoshidaEndpointA) (fun u ↦ by
        dsimp only [C, D]
        unfold constantEndpointCorrelation
        ring)
  apply hstable.neg.congr_ae
  refine ae_restrict_of_ae ?_
  filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
    simp [ae_iff, measure_singleton]] with u hu
  simpa only [C] using
    neg_stableGeometricIntegrand_eq_boundary_integrand (C 0) C hu

private theorem constant_twice_regular_intervalIntegrable :
    IntervalIntegrable
      (fun u : ℝ ↦ 2 * yoshidaRegularKernel u *
        constantEndpointCorrelation yoshidaEndpointA u)
      volume 0 (2 * yoshidaEndpointA) := by
  have h := constant_defect_intervalIntegrable.sub
    constant_boundary_integrand_intervalIntegrable
  apply h.congr
  intro u _hu
  ring

private theorem boundaryArchCorrelation_constant_eq_split :
    boundaryArchCorrelation (2 * yoshidaEndpointA)
        (constantEndpointCorrelation yoshidaEndpointA) =
      ( ∫ u : ℝ in 0..2 * yoshidaEndpointA,
          (constantEndpointCorrelation yoshidaEndpointA 0 -
            constantEndpointCorrelation yoshidaEndpointA u) / u) -
      2 * (∫ u : ℝ in 0..2 * yoshidaEndpointA,
        yoshidaRegularKernel u *
          constantEndpointCorrelation yoshidaEndpointA u) -
      (Real.log (2 * yoshidaEndpointA) +
        Real.eulerMascheroniConstant + Real.log 2 + Real.log Real.pi) *
          constantEndpointCorrelation yoshidaEndpointA 0 := by
  have htwice :
      (∫ u : ℝ in 0..2 * yoshidaEndpointA,
          2 * yoshidaRegularKernel u *
            constantEndpointCorrelation yoshidaEndpointA u) =
        2 * (∫ u : ℝ in 0..2 * yoshidaEndpointA,
          yoshidaRegularKernel u *
            constantEndpointCorrelation yoshidaEndpointA u) := by
    calc
      _ = ∫ u : ℝ in 0..2 * yoshidaEndpointA,
          2 * (yoshidaRegularKernel u *
            constantEndpointCorrelation yoshidaEndpointA u) := by
        apply intervalIntegral.integral_congr
        intro u _hu
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  unfold boundaryArchCorrelation
  rw [intervalIntegral.integral_sub constant_defect_intervalIntegrable
    constant_twice_regular_intervalIntegrable, htwice]

private theorem realEndpointCorrelation_one_eq_constant :
    realEndpointCorrelation yoshidaEndpointA (fun _ : ℝ ↦ (1 : ℝ)) =
      constantEndpointCorrelation yoshidaEndpointA := by
  funext u
  unfold realEndpointCorrelation constantEndpointCorrelation
  norm_num
  ring

private theorem boundaryArchCorrelation_constant_add_polar_eq_physical :
    boundaryArchCorrelation (2 * yoshidaEndpointA)
        (constantEndpointCorrelation yoshidaEndpointA) +
      2 *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2)) *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (y / 2)) =
      yoshidaEndpointPhysicalRealQuadratic (fun _ : ℝ ↦ (1 : ℝ)) := by
  rw [boundaryArchCorrelation_constant_eq_split]
  unfold yoshidaEndpointPhysicalRealQuadratic
  rw [realEndpointCorrelation_one_eq_constant]
  ring

/-- The production diagonal of the clipped constant is exactly the endpoint
scale times the clean constant diagonal. -/
theorem clippedCriticalFormValue_periodicCoreOne_eq_clean :
    clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
        (yoshidaClippedOne yoshidaEndpointA) =
      yoshidaEndpointA *
        yoshidaEndpointOddCleanQuadratic (fun _ : ℝ ↦ 1) := by
  let one : YoshidaClippedSmooth yoshidaEndpointA :=
    yoshidaClippedOne yoshidaEndpointA
  have hreal : ∀ y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      one y = ((one y).re : ℂ) := by
    intro y hy
    dsimp only [one]
    change (if y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA then
        (1 : ℂ) else 0) =
      (((if y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA then
        (1 : ℂ) else 0)).re : ℂ)
    rw [if_pos hy]
    norm_num
  have hpolar := clippedPolarEnergy_eq_endpointHyperbolicQuadratic one hreal
  have hhyper :
      yoshidaEndpointHyperbolicQuadratic
          (fun x ↦ ((one (yoshidaEndpointA * x)).re : ℂ)) =
        yoshidaEndpointHyperbolicQuadratic (fun _ : ℝ ↦ (1 : ℂ)) := by
    have hcosh :
        (∫ x : ℝ in -1..1,
          (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) *
            ((one (yoshidaEndpointA * x)).re : ℂ)) =
        ∫ x : ℝ in -1..1,
          (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
      have hAx : yoshidaEndpointA * x ∈
          Icc (-yoshidaEndpointA) yoshidaEndpointA := by
        constructor <;>
          nlinarith [hxIcc.1, hxIcc.2, yoshidaEndpointA_pos]
      change (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) *
          ((if yoshidaEndpointA * x ∈
            Icc (-yoshidaEndpointA) yoshidaEndpointA then
              (1 : ℂ) else 0).re : ℂ) = _
      rw [if_pos hAx]
      simp
    have hsinh :
        (∫ x : ℝ in -1..1,
          (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) *
            ((one (yoshidaEndpointA * x)).re : ℂ)) =
        ∫ x : ℝ in -1..1,
          (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
      have hAx : yoshidaEndpointA * x ∈
          Icc (-yoshidaEndpointA) yoshidaEndpointA := by
        constructor <;>
          nlinarith [hxIcc.1, hxIcc.2, yoshidaEndpointA_pos]
      change (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) *
          ((if yoshidaEndpointA * x ∈
            Icc (-yoshidaEndpointA) yoshidaEndpointA then
              (1 : ℂ) else 0).re : ℂ) = _
      rw [if_pos hAx]
      simp
    unfold yoshidaEndpointHyperbolicQuadratic
    rw [hcosh, hsinh]
    simp only [mul_one]
  have hphysicalPolar :=
    two_mul_rescaledPolarMoments_eq_endpointHyperbolicQuadratic
      (fun _ : ℝ ↦ (1 : ℝ)) continuous_const
  have hpolar' : clippedPolarEnergy yoshidaEndpointA yoshidaEndpointA_pos one =
      2 *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2)) *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (y / 2)) := by
    rw [hpolar]
    rw [hhyper]
    simpa using hphysicalPolar.symm
  have harch : clippedArchEnergy yoshidaEndpointA yoshidaEndpointA_pos one =
      boundaryArchCorrelation (2 * yoshidaEndpointA)
        (constantEndpointCorrelation yoshidaEndpointA) := by
    have hint : (∫ v : ℝ,
        yoshidaClippedCriticalCrossIntegrand yoshidaEndpointA
          yoshidaEndpointA_pos one one v) =
        (↑(∫ v : ℝ,
        ((Complex.digamma
          ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re - Real.log Real.pi) *
          Complex.normSq
            (yoshidaCriticalSampleLinear yoshidaEndpointA
              yoshidaEndpointA_pos v one)) : ℂ) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards [] with v
      exact criticalCrossIntegrand_self_eq_ofReal
        yoshidaEndpointA_pos one v
    have hcore := normalized_arch_periodicCoreOne_eq_boundaryArch
    rw [hint] at hcore
    unfold clippedArchEnergy
    apply Complex.ofReal_injective
    change (((1 / (2 * Real.pi)) *
      (∫ v : ℝ,
        ((Complex.digamma
          ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re - Real.log Real.pi) *
          Complex.normSq
            (yoshidaCriticalSampleLinear yoshidaEndpointA
              yoshidaEndpointA_pos v one)) : ℝ) : ℂ) = _
    rw [ofReal_mul]
    simpa only [one] using hcore
  rw [clippedCriticalFormValue_eq_polar_add_arch, hpolar', harch]
  calc
    2 * (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2)) *
          (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
            Real.exp (y / 2)) +
        boundaryArchCorrelation (2 * yoshidaEndpointA)
          (constantEndpointCorrelation yoshidaEndpointA) =
        boundaryArchCorrelation (2 * yoshidaEndpointA)
            (constantEndpointCorrelation yoshidaEndpointA) +
          2 * (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
            Real.exp (-y / 2)) *
            (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
              Real.exp (y / 2)) := by ring
    _ = yoshidaEndpointPhysicalRealQuadratic (fun _ : ℝ ↦ (1 : ℝ)) :=
      boundaryArchCorrelation_constant_add_polar_eq_physical
    _ = yoshidaEndpointA *
        yoshidaEndpointOddCleanQuadratic (fun _ : ℝ ↦ (1 : ℝ)) := by
      exact yoshidaEndpointPhysicalRealQuadratic_eq_clean
        (fun _ : ℝ ↦ (1 : ℝ)) continuous_const (by
          exact (contDiffOn_const : ContDiffOn ℝ 1
            (fun _ : ℝ ↦ (1 : ℝ)) (Icc (-1 : ℝ) 1))
              |>.locallyLipschitzOn (convex_Icc (-1 : ℝ) 1))

/-! ## The constant--zero-trace cross term -/

/-- The real symmetric cross term associated with the production form. -/
def clippedCriticalFormSymmetricCross
    (f g : YoshidaClippedSmooth yoshidaEndpointA) : ℝ :=
  (yoshidaClippedLocalCriticalForm yoshidaEndpointA yoshidaEndpointA_pos f g +
    yoshidaClippedLocalCriticalForm yoshidaEndpointA yoshidaEndpointA_pos g f).re

/-- The ordered real polar cross between the clipped constant and a real
physical profile. -/
def endpointConstantResidualPolarCross (g : ℝ → ℝ) : ℝ :=
  (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
      Real.exp (-y / 2)) *
      (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
        Real.exp (y / 2) * g y) +
    (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
      Real.exp (y / 2)) *
      (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
        Real.exp (-y / 2) * g y)

private theorem exists_continuous_residualEndpointSlope_final
    (r : YoshidaClippedSmooth yoshidaEndpointA)
    (hrcont : Continuous (r : ℝ → ℂ)) :
    ∃ D : ℝ → ℝ, Continuous D ∧
      ∀ u : ℝ, residualEndpointCorrelation r u =
        residualEndpointCorrelation r 0 + u * D u := by
  let g : ℝ → ℝ := fun x ↦ (r x).re
  let C : ℝ → ℝ := residualEndpointCorrelation r
  have hg : Continuous g := Complex.continuous_re.comp hrcont
  have hderiv (u : ℝ) : HasDerivAt C (-g (yoshidaEndpointA - u)) u := by
    have hFTC := intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable (-yoshidaEndpointA) (yoshidaEndpointA - u))
      hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
    have hinner : HasDerivAt
        (fun v : ℝ ↦ yoshidaEndpointA - v) (-1) u := by
      convert (hasDerivAt_const u yoshidaEndpointA).sub
        (hasDerivAt_id u) using 1
      all_goals simp
    dsimp only [C]
    convert hFTC.comp u hinner using 1
    all_goals simp [g]
  have hC : ContDiff ℝ 1 C := by
    rw [contDiff_one_iff_deriv]
    constructor
    · intro u
      exact (hderiv u).differentiableAt
    · rw [show deriv C = fun u ↦ -g (yoshidaEndpointA - u) by
        funext u
        exact (hderiv u).deriv]
      fun_prop
  let Q : ℝ → ℝ := fun u ↦ (C u - C 0) / u
  let D : ℝ → ℝ := Function.update Q 0 (deriv C 0)
  have hderiv0 : HasDerivAt C (deriv C 0) 0 :=
    (hC.differentiable (by norm_num) 0).hasDerivAt
  have hQzero : Tendsto Q (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (deriv C 0)) := by
    have h := hderiv0.tendsto_slope_zero
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    dsimp only [Q]
    simp only [zero_add, smul_eq_mul, div_eq_inv_mul]
  have hD : Continuous D := by
    rw [continuous_iff_continuousAt]
    intro u
    by_cases hu : u = 0
    · subst u
      rw [show D = Function.update Q 0 (deriv C 0) by rfl,
        continuousAt_update_same]
      exact hQzero
    · rw [show D = Function.update Q 0 (deriv C 0) by rfl,
        continuousAt_update_of_ne hu]
      exact ((hC.continuous.continuousAt.sub continuousAt_const).div
        continuousAt_id hu)
  refine ⟨D, hD, ?_⟩
  intro u
  by_cases hu : u = 0
  · subst u
    simp
  · rw [show D u = Q u by simp [D, hu]]
    dsimp only [Q]
    field_simp [hu]
    ring

private theorem residual_defect_intervalIntegrable
    (r : YoshidaClippedSmooth yoshidaEndpointA)
    (hrcont : Continuous (r : ℝ → ℂ)) :
    IntervalIntegrable
      (fun u : ℝ ↦
        (residualEndpointCorrelation r 0 -
          residualEndpointCorrelation r u) / u)
      volume 0 (2 * yoshidaEndpointA) := by
  obtain ⟨D, hD, hrem⟩ :=
    exists_continuous_residualEndpointSlope_final r hrcont
  have hnegD : IntervalIntegrable (fun u : ℝ ↦ -D u) volume
      0 (2 * yoshidaEndpointA) := hD.neg.intervalIntegrable _ _
  apply hnegD.congr_ae
  refine ae_restrict_of_ae ?_
  filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
    simp [ae_iff, measure_singleton]] with u hu
  rw [hrem u]
  field_simp [hu]
  ring

private theorem residual_boundary_integrand_intervalIntegrable
    (r : YoshidaClippedSmooth yoshidaEndpointA)
    (hrcont : Continuous (r : ℝ → ℂ)) :
    IntervalIntegrable
      (fun u : ℝ ↦
        (residualEndpointCorrelation r 0 -
            residualEndpointCorrelation r u) / u -
          2 * yoshidaRegularKernel u * residualEndpointCorrelation r u)
      volume 0 (2 * yoshidaEndpointA) := by
  let C : ℝ → ℝ := residualEndpointCorrelation r
  obtain ⟨D, hD, hrem⟩ :=
    exists_continuous_residualEndpointSlope_final r hrcont
  have hstable : IntervalIntegrable
      (stableGeometricIntegrand (C 0) C) volume
        0 (2 * yoshidaEndpointA) :=
    stableGeometricIntegrand_intervalIntegrable_of_removable
      hD (C 0) (2 * yoshidaEndpointA) (by
        intro u
        simpa only [C] using hrem u)
  apply hstable.neg.congr_ae
  refine ae_restrict_of_ae ?_
  filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
    simp [ae_iff, measure_singleton]] with u hu
  simpa only [C] using
    neg_stableGeometricIntegrand_eq_boundary_integrand (C 0) C hu

private theorem residual_regular_intervalIntegrable
    (r : YoshidaClippedSmooth yoshidaEndpointA)
    (hrcont : Continuous (r : ℝ → ℂ)) :
    IntervalIntegrable
      (fun u : ℝ ↦ yoshidaRegularKernel u *
        residualEndpointCorrelation r u)
      volume 0 (2 * yoshidaEndpointA) := by
  have htwice := (residual_defect_intervalIntegrable r hrcont).sub
    (residual_boundary_integrand_intervalIntegrable r hrcont)
  have htwice' : IntervalIntegrable
      (fun u : ℝ ↦ 2 * yoshidaRegularKernel u *
        residualEndpointCorrelation r u)
      volume 0 (2 * yoshidaEndpointA) := by
    apply htwice.congr
    intro u _hu
    ring
  have hhalf := htwice'.const_mul (1 / 2 : ℝ)
  apply hhalf.congr
  intro u _hu
  ring

private theorem boundaryArchCorrelation_residual_eq_split
    (r : YoshidaClippedSmooth yoshidaEndpointA)
    (hrcont : Continuous (r : ℝ → ℂ)) :
    boundaryArchCorrelation (2 * yoshidaEndpointA)
        (residualEndpointCorrelation r) =
      (∫ u : ℝ in 0..2 * yoshidaEndpointA,
        (residualEndpointCorrelation r 0 -
          residualEndpointCorrelation r u) / u) -
      2 * (∫ u : ℝ in 0..2 * yoshidaEndpointA,
        yoshidaRegularKernel u * residualEndpointCorrelation r u) -
      (Real.log (2 * yoshidaEndpointA) +
        Real.eulerMascheroniConstant + Real.log 2 + Real.log Real.pi) *
          residualEndpointCorrelation r 0 := by
  unfold boundaryArchCorrelation
  have htwice := (residual_regular_intervalIntegrable r hrcont).const_mul 2
  rw [intervalIntegral.integral_sub
    (residual_defect_intervalIntegrable r hrcont) (by
      apply htwice.congr
      intro u _hu
      ring)]
  rw [show (∫ u : ℝ in 0..2 * yoshidaEndpointA,
      2 * yoshidaRegularKernel u * residualEndpointCorrelation r u) =
      2 * (∫ u : ℝ in 0..2 * yoshidaEndpointA,
        yoshidaRegularKernel u * residualEndpointCorrelation r u) by
    calc
      _ = ∫ u : ℝ in 0..2 * yoshidaEndpointA,
          2 * (yoshidaRegularKernel u *
            residualEndpointCorrelation r u) := by
        apply intervalIntegral.integral_congr
        intro u _hu
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]]

private theorem integral_shift_eq_self_of_even
    (g : ℝ → ℝ) (hgEven : Function.Even g)
    (u : ℝ) :
    (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA - u,
        g (u + x)) =
      ∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA - u, g x := by
  have hshift :
      (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA - u,
          g (u + x)) =
        ∫ x : ℝ in -yoshidaEndpointA + u..yoshidaEndpointA, g x := by
    rw [show (fun x : ℝ ↦ g (u + x)) = fun x ↦ g (x + u) by
      funext x
      rw [add_comm]]
    rw [intervalIntegral.integral_comp_add_right]
    congr 1
    all_goals ring
  have hneg :
      (∫ x : ℝ in -yoshidaEndpointA + u..yoshidaEndpointA, g x) =
        ∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA - u,
          g (-x) := by
    rw [intervalIntegral.integral_comp_neg]
    congr 1
    all_goals ring
  have heven :
      (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA - u,
          g (-x)) =
        ∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA - u, g x := by
    apply intervalIntegral.integral_congr
    intro x _hx
    exact hgEven x
  rw [hshift, hneg, heven]

private theorem realEndpointCorrelation_one_add_even
    (r : YoshidaClippedSmooth yoshidaEndpointA)
    (hrcont : Continuous (r : ℝ → ℂ))
    (hgEven : Function.Even (fun x : ℝ ↦ (r x).re))
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (2 * yoshidaEndpointA)) :
    realEndpointCorrelation yoshidaEndpointA
        (fun x ↦ 1 + (r x).re) u =
      constantEndpointCorrelation yoshidaEndpointA u +
        2 * residualEndpointCorrelation r u +
        realEndpointCorrelation yoshidaEndpointA
          (fun x ↦ (r x).re) u := by
  let g : ℝ → ℝ := fun x ↦ (r x).re
  have hle : -yoshidaEndpointA ≤ yoshidaEndpointA - u := by
    linarith [hu.2]
  have h1 : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume
      (-yoshidaEndpointA) (yoshidaEndpointA - u) :=
    continuous_const.intervalIntegrable _ _
  have hleft : IntervalIntegrable (fun x : ℝ ↦ g (u + x)) volume
      (-yoshidaEndpointA) (yoshidaEndpointA - u) :=
    ((Complex.continuous_re.comp hrcont).comp
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hright : IntervalIntegrable g volume
      (-yoshidaEndpointA) (yoshidaEndpointA - u) :=
    (Complex.continuous_re.comp hrcont).intervalIntegrable _ _
  have hprod : IntervalIntegrable (fun x ↦ g (u + x) * g x) volume
      (-yoshidaEndpointA) (yoshidaEndpointA - u) :=
    (((Complex.continuous_re.comp hrcont).comp
      (continuous_const.add continuous_id)).mul
        (Complex.continuous_re.comp hrcont)).intervalIntegrable _ _
  unfold realEndpointCorrelation
  rw [show (fun x : ℝ ↦ (1 + g (u + x)) * (1 + g x)) =
      fun x ↦ 1 + (g (u + x) + g x) + g (u + x) * g x by
    funext x
    ring]
  rw [intervalIntegral.integral_add (h1.add (hleft.add hright)) hprod,
    intervalIntegral.integral_add h1 (hleft.add hright),
    intervalIntegral.integral_add hleft hright,
    integral_shift_eq_self_of_even g hgEven u]
  dsimp only [g]
  unfold constantEndpointCorrelation residualEndpointCorrelation
  norm_num
  ring

private theorem constant_regular_intervalIntegrable :
    IntervalIntegrable
      (fun u : ℝ ↦ yoshidaRegularKernel u *
        constantEndpointCorrelation yoshidaEndpointA u)
      volume 0 (2 * yoshidaEndpointA) := by
  have hhalf := constant_twice_regular_intervalIntegrable.const_mul
    (1 / 2 : ℝ)
  apply hhalf.congr
  intro u _hu
  ring

private def endpointPhysicalArchPart (g : ℝ → ℝ) : ℝ :=
  let C := realEndpointCorrelation yoshidaEndpointA g
  (∫ u : ℝ in 0..2 * yoshidaEndpointA, (C 0 - C u) / u) -
    2 * (∫ u : ℝ in 0..2 * yoshidaEndpointA,
      yoshidaRegularKernel u * C u) -
    (Real.log (2 * yoshidaEndpointA) +
      Real.eulerMascheroniConstant + Real.log 2 + Real.log Real.pi) * C 0

private def endpointPhysicalPolarPart (g : ℝ → ℝ) : ℝ :=
  2 *
    (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
      Real.exp (-y / 2) * g y) *
    (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
      Real.exp (y / 2) * g y)

private theorem yoshidaEndpointPhysicalRealQuadratic_eq_parts
    (g : ℝ → ℝ) :
    yoshidaEndpointPhysicalRealQuadratic g =
      endpointPhysicalArchPart g + endpointPhysicalPolarPart g := by
  rfl

private theorem endpointPhysicalArchPart_one_add_residual
    (r : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (hrcont : Continuous
      ((r : YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ))
    (hr_real : ∀ x ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hneg : (r : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hpos : (r : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0)
    (hrEven : Function.Even
      (((r : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ)) :
    endpointPhysicalArchPart
        (fun x ↦ 1 + ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re) =
      endpointPhysicalArchPart (fun _ : ℝ ↦ 1) +
        endpointPhysicalArchPart
          (fun x ↦ ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re) +
        2 * boundaryArchCorrelation (2 * yoshidaEndpointA)
          (residualEndpointCorrelation
            (r : YoshidaClippedSmooth yoshidaEndpointA)) := by
  let fs : YoshidaClippedSmooth yoshidaEndpointA :=
    (r : YoshidaClippedSmooth yoshidaEndpointA)
  let g : ℝ → ℝ := fun x ↦ (fs x).re
  let C1 : ℝ → ℝ := constantEndpointCorrelation yoshidaEndpointA
  let Cx : ℝ → ℝ := residualEndpointCorrelation fs
  let Cg : ℝ → ℝ := realEndpointCorrelation yoshidaEndpointA g
  let Cs : ℝ → ℝ :=
    realEndpointCorrelation yoshidaEndpointA (fun x ↦ 1 + g x)
  have hgcont : Continuous g := Complex.continuous_re.comp hrcont
  have hgeven : Function.Even g := by
    intro x
    exact congrArg Complex.re (hrEven x)
  have hzeroMem : (0 : ℝ) ∈ Icc 0 (2 * yoshidaEndpointA) :=
    ⟨le_rfl, (mul_pos (by norm_num) yoshidaEndpointA_pos).le⟩
  have horder : (0 : ℝ) ≤ 2 * yoshidaEndpointA :=
    (mul_pos (by norm_num) yoshidaEndpointA_pos).le
  have hcorr (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (2 * yoshidaEndpointA)) :
      Cs u = C1 u + 2 * Cx u + Cg u := by
    simpa only [Cs, C1, Cx, Cg, fs, g] using
      realEndpointCorrelation_one_add_even fs hrcont hgeven hu
  obtain ⟨hdefg, hregg⟩ :=
    endpointClippedArchCorrelation_terms_intervalIntegrable_of_endpoints_zero
      r hr_real hneg hpos
  have hdefg' : IntervalIntegrable
      (fun u : ℝ ↦ (Cg 0 - Cg u) / u) volume
      0 (2 * yoshidaEndpointA) := by
    simpa only [Cg, g, fs] using hdefg
  have hregg' : IntervalIntegrable
      (fun u : ℝ ↦ yoshidaRegularKernel u * Cg u) volume
      0 (2 * yoshidaEndpointA) := by
    simpa only [Cg, g, fs] using hregg
  have hdefx := residual_defect_intervalIntegrable fs hrcont
  have hregx := residual_regular_intervalIntegrable fs hrcont
  have hdefSum :
      (∫ u : ℝ in 0..2 * yoshidaEndpointA, (Cs 0 - Cs u) / u) =
        (∫ u : ℝ in 0..2 * yoshidaEndpointA, (C1 0 - C1 u) / u) +
        2 * (∫ u : ℝ in 0..2 * yoshidaEndpointA,
          (Cx 0 - Cx u) / u) +
        (∫ u : ℝ in 0..2 * yoshidaEndpointA,
          (Cg 0 - Cg u) / u) := by
    have htwo : IntervalIntegrable
        (fun u : ℝ ↦ 2 * ((Cx 0 - Cx u) / u)) volume
        0 (2 * yoshidaEndpointA) := hdefx.const_mul 2
    calc
      _ = ∫ u : ℝ in 0..2 * yoshidaEndpointA,
          (C1 0 - C1 u) / u +
            (2 * ((Cx 0 - Cx u) / u) + (Cg 0 - Cg u) / u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have huIcc : u ∈ Icc (0 : ℝ) (2 * yoshidaEndpointA) := by
          simpa only [uIcc_of_le horder] using hu
        change (Cs 0 - Cs u) / u =
          (C1 0 - C1 u) / u +
            (2 * ((Cx 0 - Cx u) / u) + (Cg 0 - Cg u) / u)
        rw [hcorr 0 hzeroMem, hcorr u huIcc]
        ring
      _ = (∫ u : ℝ in 0..2 * yoshidaEndpointA,
          (C1 0 - C1 u) / u) +
          ∫ u : ℝ in 0..2 * yoshidaEndpointA,
            2 * ((Cx 0 - Cx u) / u) + (Cg 0 - Cg u) / u := by
        rw [intervalIntegral.integral_add constant_defect_intervalIntegrable
          (htwo.add hdefg')]
      _ = _ := by
        rw [intervalIntegral.integral_add htwo hdefg',
          intervalIntegral.integral_const_mul]
        ring
  have hregSum :
      (∫ u : ℝ in 0..2 * yoshidaEndpointA,
          yoshidaRegularKernel u * Cs u) =
        (∫ u : ℝ in 0..2 * yoshidaEndpointA,
          yoshidaRegularKernel u * C1 u) +
        2 * (∫ u : ℝ in 0..2 * yoshidaEndpointA,
          yoshidaRegularKernel u * Cx u) +
        (∫ u : ℝ in 0..2 * yoshidaEndpointA,
          yoshidaRegularKernel u * Cg u) := by
    have htwo : IntervalIntegrable
        (fun u : ℝ ↦ 2 *
          (yoshidaRegularKernel u * Cx u)) volume
        0 (2 * yoshidaEndpointA) := hregx.const_mul 2
    calc
      _ = ∫ u : ℝ in 0..2 * yoshidaEndpointA,
          yoshidaRegularKernel u * C1 u +
            (2 * (yoshidaRegularKernel u * Cx u) +
              yoshidaRegularKernel u * Cg u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have huIcc : u ∈ Icc (0 : ℝ) (2 * yoshidaEndpointA) := by
          simpa only [uIcc_of_le horder] using hu
        change yoshidaRegularKernel u * Cs u =
          yoshidaRegularKernel u * C1 u +
            (2 * (yoshidaRegularKernel u * Cx u) +
              yoshidaRegularKernel u * Cg u)
        rw [hcorr u huIcc]
        ring
      _ = (∫ u : ℝ in 0..2 * yoshidaEndpointA,
          yoshidaRegularKernel u * C1 u) +
          ∫ u : ℝ in 0..2 * yoshidaEndpointA,
            2 * (yoshidaRegularKernel u * Cx u) +
              yoshidaRegularKernel u * Cg u := by
        rw [intervalIntegral.integral_add constant_regular_intervalIntegrable
          (htwo.add hregg')]
      _ = _ := by
        rw [intervalIntegral.integral_add htwo hregg',
          intervalIntegral.integral_const_mul]
        ring
  have hmass : Cs 0 = C1 0 + 2 * Cx 0 + Cg 0 := hcorr 0 hzeroMem
  change endpointPhysicalArchPart (fun x ↦ 1 + g x) =
    endpointPhysicalArchPart (fun _ : ℝ ↦ 1) +
      endpointPhysicalArchPart g +
      2 * boundaryArchCorrelation (2 * yoshidaEndpointA) Cx
  unfold endpointPhysicalArchPart
  dsimp only
  rw [show realEndpointCorrelation yoshidaEndpointA (fun _ : ℝ ↦ 1) = C1 by
      simpa only [C1] using realEndpointCorrelation_one_eq_constant,
    show realEndpointCorrelation yoshidaEndpointA g = Cg by rfl,
    show realEndpointCorrelation yoshidaEndpointA (fun x ↦ 1 + g x) = Cs by
      rfl,
    hdefSum, hregSum, hmass,
    boundaryArchCorrelation_residual_eq_split fs hrcont]
  ring

private theorem endpointPhysicalPolarPart_one_add
    (g : ℝ → ℝ) (hg : Continuous g) :
    endpointPhysicalPolarPart (fun x ↦ 1 + g x) =
      endpointPhysicalPolarPart (fun _ : ℝ ↦ 1) +
        endpointPhysicalPolarPart g +
        2 * endpointConstantResidualPolarCross g := by
  have hneg1 : IntervalIntegrable
      (fun y : ℝ ↦ Real.exp (-y / 2)) volume
      (-yoshidaEndpointA) yoshidaEndpointA :=
    (by fun_prop : Continuous (fun y : ℝ ↦ Real.exp (-y / 2)))
      |>.intervalIntegrable _ _
  have hpos1 : IntervalIntegrable
      (fun y : ℝ ↦ Real.exp (y / 2)) volume
      (-yoshidaEndpointA) yoshidaEndpointA :=
    (by fun_prop : Continuous (fun y : ℝ ↦ Real.exp (y / 2)))
      |>.intervalIntegrable _ _
  have hnegg : IntervalIntegrable
      (fun y : ℝ ↦ Real.exp (-y / 2) * g y) volume
      (-yoshidaEndpointA) yoshidaEndpointA :=
    (by fun_prop : Continuous (fun y : ℝ ↦ Real.exp (-y / 2) * g y))
      |>.intervalIntegrable _ _
  have hposg : IntervalIntegrable
      (fun y : ℝ ↦ Real.exp (y / 2) * g y) volume
      (-yoshidaEndpointA) yoshidaEndpointA :=
    (by fun_prop : Continuous (fun y : ℝ ↦ Real.exp (y / 2) * g y))
      |>.intervalIntegrable _ _
  have hneg :
      (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2) * (1 + g y)) =
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2)) +
        ∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2) * g y := by
    rw [show (fun y : ℝ ↦ Real.exp (-y / 2) * (1 + g y)) =
      fun y ↦ Real.exp (-y / 2) + Real.exp (-y / 2) * g y by
        funext y
        ring,
      intervalIntegral.integral_add hneg1 hnegg]
  have hpos :
      (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (y / 2) * (1 + g y)) =
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (y / 2)) +
        ∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (y / 2) * g y := by
    rw [show (fun y : ℝ ↦ Real.exp (y / 2) * (1 + g y)) =
      fun y ↦ Real.exp (y / 2) + Real.exp (y / 2) * g y by
        funext y
        ring,
      intervalIntegral.integral_add hpos1 hposg]
  unfold endpointPhysicalPolarPart endpointConstantResidualPolarCross
  rw [hneg, hpos]
  simp only [mul_one]
  ring

private theorem yoshidaEndpointPhysicalRealQuadratic_one_add_residual
    (r : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (hrcont : Continuous
      ((r : YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ))
    (hr_real : ∀ x ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hneg : (r : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hpos : (r : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0)
    (hrEven : Function.Even
      (((r : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ)) :
    yoshidaEndpointPhysicalRealQuadratic
        (fun x ↦ 1 + ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re) =
      yoshidaEndpointPhysicalRealQuadratic (fun _ : ℝ ↦ 1) +
        yoshidaEndpointPhysicalRealQuadratic
          (fun x ↦ ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re) +
        2 * (boundaryArchCorrelation (2 * yoshidaEndpointA)
            (residualEndpointCorrelation
              (r : YoshidaClippedSmooth yoshidaEndpointA)) +
          endpointConstantResidualPolarCross
            (fun x ↦ ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re)) := by
  let g : ℝ → ℝ := fun x ↦
    ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re
  have hg : Continuous g := Complex.continuous_re.comp hrcont
  rw [yoshidaEndpointPhysicalRealQuadratic_eq_parts,
    yoshidaEndpointPhysicalRealQuadratic_eq_parts,
    yoshidaEndpointPhysicalRealQuadratic_eq_parts]
  change endpointPhysicalArchPart (fun x ↦ 1 + g x) +
      endpointPhysicalPolarPart (fun x ↦ 1 + g x) = _
  rw [endpointPhysicalArchPart_one_add_residual r hrcont hr_real hneg hpos
      hrEven,
    endpointPhysicalPolarPart_one_add g hg]
  ring

private theorem boundaryArch_add_polar_eq_cleanCross
    (r : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (hrcont : Continuous
      ((r : YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ))
    (hr_real : ∀ x ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hneg : (r : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hpos : (r : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0)
    (hrEven : Function.Even
      (((r : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ)) :
    (let g : ℝ → ℝ := fun x ↦
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re
    let w : ℝ → ℝ := centeredRescale yoshidaEndpointA g
    boundaryArchCorrelation (2 * yoshidaEndpointA)
          (residualEndpointCorrelation
            (r : YoshidaClippedSmooth yoshidaEndpointA)) +
        endpointConstantResidualPolarCross g =
      yoshidaEndpointA * yoshidaEndpointEvenConstantCrossFunctional w) := by
  let g : ℝ → ℝ := fun x ↦
    ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re
  let w : ℝ → ℝ := centeredRescale yoshidaEndpointA g
  dsimp only
  have hgcont : Continuous g := Complex.continuous_re.comp hrcont
  have hwcont : Continuous w := by
    dsimp only [w, centeredRescale]
    exact hgcont.comp (continuous_const.mul continuous_id)
  have hprofile : ContDiffOn ℝ 1 g
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
  have hwlocal : LocallyLipschitzOn (Icc (-1) 1) w := by
    have hcomp := hprofile.comp hscale hmaps
    simpa only [w, centeredRescale, Function.comp_apply] using
      hcomp.locallyLipschitzOn (convex_Icc (-1) 1)
  have hsumcont : Continuous (fun x ↦ 1 + g x) :=
    continuous_const.add hgcont
  have hsumlocal : LocallyLipschitzOn (Icc (-1) 1)
      (centeredRescale yoshidaEndpointA (fun x ↦ 1 + g x)) := by
    have hsumProfile : ContDiffOn ℝ 1 (fun x ↦ 1 + g x)
        (Icc (-yoshidaEndpointA) yoshidaEndpointA) :=
      contDiffOn_const.add hprofile
    have hcomp := hsumProfile.comp hscale hmaps
    simpa only [centeredRescale, Function.comp_apply] using
      hcomp.locallyLipschitzOn (convex_Icc (-1) 1)
  have hphys := yoshidaEndpointPhysicalRealQuadratic_one_add_residual
    r hrcont hr_real hneg hpos hrEven
  have hsum := yoshidaEndpointPhysicalRealQuadratic_eq_clean
    (fun x ↦ 1 + g x) hsumcont hsumlocal
  have hone := yoshidaEndpointPhysicalRealQuadratic_eq_clean
    (fun _ : ℝ ↦ (1 : ℝ)) continuous_const (by
      exact (contDiffOn_const : ContDiffOn ℝ 1
        (fun _ : ℝ ↦ (1 : ℝ)) (Icc (-1 : ℝ) 1))
          |>.locallyLipschitzOn (convex_Icc (-1 : ℝ) 1))
  have hg := yoshidaEndpointPhysicalRealQuadratic_eq_clean
    g hgcont hwlocal
  have hcleanAdd := yoshidaEndpointOddCleanQuadratic_add_constant
    w hwcont 1
  change _ = _ at hphys
  rw [hsum, hone, hg] at hphys
  have hscaleAdd : centeredRescale yoshidaEndpointA (fun x ↦ 1 + g x) =
      fun x ↦ 1 + w x := by
    funext x
    rfl
  have hscaleOne : centeredRescale yoshidaEndpointA
      (fun _ : ℝ ↦ (1 : ℝ)) = fun _ : ℝ ↦ (1 : ℝ) := by
    rfl
  have hscaleG : centeredRescale yoshidaEndpointA g = w := by
    rfl
  rw [hscaleAdd, hscaleOne, hscaleG, hcleanAdd] at hphys
  linarith

private theorem yoshidaPositivePolarLinear_eq_realIntegral
    (f : YoshidaClippedSmooth yoshidaEndpointA)
    (hf_real : ∀ y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      f y = ((f y).re : ℂ)) :
    yoshidaPositivePolarLinear yoshidaEndpointA yoshidaEndpointA_pos f =
      ((∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
        Real.exp (-y / 2) * (f y).re : ℝ) : ℂ) := by
  rw [yoshidaPositivePolarLinear, yoshidaCenteredLaplaceLinear_apply,
    ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro y hy
  have hyIcc : y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA := by
    simpa only [uIcc_of_le (by linarith [yoshidaEndpointA_pos] :
      -yoshidaEndpointA ≤ yoshidaEndpointA)] using hy
  change Complex.exp (-((1 / 2 : ℂ) * (y : ℂ))) * f y =
    ((Real.exp (-y / 2) * (f y).re : ℝ) : ℂ)
  rw [hf_real y hyIcc]
  rw [show -((1 / 2 : ℂ) * (y : ℂ)) = ((-y / 2 : ℝ) : ℂ) by
    push_cast
    ring,
    ← Complex.ofReal_exp]
  push_cast
  rfl

private theorem yoshidaNegativePolarLinear_eq_realIntegral
    (f : YoshidaClippedSmooth yoshidaEndpointA)
    (hf_real : ∀ y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      f y = ((f y).re : ℂ)) :
    yoshidaNegativePolarLinear yoshidaEndpointA yoshidaEndpointA_pos f =
      ((∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
        Real.exp (y / 2) * (f y).re : ℝ) : ℂ) := by
  rw [yoshidaNegativePolarLinear, yoshidaCenteredLaplaceLinear_apply,
    ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro y hy
  have hyIcc : y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA := by
    simpa only [uIcc_of_le (by linarith [yoshidaEndpointA_pos] :
      -yoshidaEndpointA ≤ yoshidaEndpointA)] using hy
  change Complex.exp (-((-1 / 2 : ℂ) * (y : ℂ))) * f y =
    ((Real.exp (y / 2) * (f y).re : ℝ) : ℂ)
  rw [hf_real y hyIcc]
  rw [show -((-1 / 2 : ℂ) * (y : ℂ)) = ((y / 2 : ℝ) : ℂ) by
    push_cast
    ring,
    ← Complex.ofReal_exp]
  push_cast
  rfl

private theorem productionPolarCross_one_residual_eq
    (r : YoshidaClippedSmooth yoshidaEndpointA)
    (hr_real : ∀ y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      r y = ((r y).re : ℂ)) :
    (star (yoshidaPositivePolarLinear yoshidaEndpointA
          yoshidaEndpointA_pos (yoshidaClippedOne yoshidaEndpointA)) *
        yoshidaNegativePolarLinear yoshidaEndpointA yoshidaEndpointA_pos r +
      star (yoshidaNegativePolarLinear yoshidaEndpointA
          yoshidaEndpointA_pos (yoshidaClippedOne yoshidaEndpointA)) *
        yoshidaPositivePolarLinear yoshidaEndpointA yoshidaEndpointA_pos r).re =
      endpointConstantResidualPolarCross (fun x ↦ (r x).re) := by
  have honeReal : ∀ y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      yoshidaClippedOne yoshidaEndpointA y =
        (((yoshidaClippedOne yoshidaEndpointA y).re : ℝ) : ℂ) := by
    intro y hy
    change (if y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA then
      (1 : ℂ) else 0) =
      (((if y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA then
        (1 : ℂ) else 0)).re : ℂ)
    rw [if_pos hy]
    norm_num
  rw [yoshidaPositivePolarLinear_eq_realIntegral
      (yoshidaClippedOne yoshidaEndpointA) honeReal,
    yoshidaNegativePolarLinear_eq_realIntegral
      (yoshidaClippedOne yoshidaEndpointA) honeReal,
    yoshidaPositivePolarLinear_eq_realIntegral r hr_real,
    yoshidaNegativePolarLinear_eq_realIntegral r hr_real]
  unfold endpointConstantResidualPolarCross
  have hone (y : ℝ) (hy : y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA) :
      (yoshidaClippedOne yoshidaEndpointA y).re = 1 := by
    change (if y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA then
      (1 : ℂ) else 0).re = 1
    rw [if_pos hy]
    norm_num
  have hneg :
      (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
        Real.exp (-y / 2) *
          (yoshidaClippedOne yoshidaEndpointA y).re) =
      ∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
        Real.exp (-y / 2) := by
    apply intervalIntegral.integral_congr
    intro y hy
    change Real.exp (-y / 2) *
      (yoshidaClippedOne yoshidaEndpointA y).re = Real.exp (-y / 2)
    rw [hone y (by
      simpa only [uIcc_of_le (by linarith [yoshidaEndpointA_pos] :
        -yoshidaEndpointA ≤ yoshidaEndpointA)] using hy)]
    ring
  have hpos :
      (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
        Real.exp (y / 2) *
          (yoshidaClippedOne yoshidaEndpointA y).re) =
      ∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
        Real.exp (y / 2) := by
    apply intervalIntegral.integral_congr
    intro y hy
    change Real.exp (y / 2) *
      (yoshidaClippedOne yoshidaEndpointA y).re = Real.exp (y / 2)
    rw [hone y (by
      simpa only [uIcc_of_le (by linarith [yoshidaEndpointA_pos] :
        -yoshidaEndpointA ≤ yoshidaEndpointA)] using hy)]
    ring
  rw [hneg, hpos]
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.add_re,
    Complex.mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]

/-- Exact full symmetric production cross between the clipped constant and
an arbitrary real, even, continuous zero-trace periodic residual. -/
theorem clippedCriticalForm_symmetricCross_periodicCoreOne_eq_clean
    (r : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (hr_real : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0)
    (hrEven : Function.Even
      (((r : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ))
    (hneg : (r : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hpos : (r : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0) :
    clippedCriticalFormSymmetricCross
        (yoshidaClippedOne yoshidaEndpointA)
        (r : YoshidaClippedSmooth yoshidaEndpointA) =
      2 * yoshidaEndpointA * yoshidaEndpointEvenConstantCrossFunctional
        (centeredRescale yoshidaEndpointA
          (fun x ↦ ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re)) := by
  let one : YoshidaClippedSmooth yoshidaEndpointA :=
    yoshidaClippedOne yoshidaEndpointA
  let fs : YoshidaClippedSmooth yoshidaEndpointA :=
    (r : YoshidaClippedSmooth yoshidaEndpointA)
  let g : ℝ → ℝ := fun x ↦ (fs x).re
  have hrcont : Continuous (fs : ℝ → ℂ) :=
    continuous_yoshidaClippedSmooth_of_endpoints_zero
      yoshidaEndpointA_pos fs (by simpa only [fs] using hneg)
        (by simpa only [fs] using hpos)
  have hrreal : ∀ x ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      fs x = ((fs x).re : ℂ) := by
    intro x _hx
    apply Complex.ext
    · simp
    · simpa only [ofReal_im] using hr_real x
  have harch := normalized_arch_periodicCoreOne_residual_eq_boundaryArch
    fs hrcont hrreal (by simpa only [fs] using hrEven)
  have hpolar := productionPolarCross_one_residual_eq fs hrreal
  have hordered :
      (yoshidaClippedLocalCriticalForm yoshidaEndpointA
        yoshidaEndpointA_pos one fs).re =
      endpointConstantResidualPolarCross g +
        boundaryArchCorrelation (2 * yoshidaEndpointA)
          (residualEndpointCorrelation fs) := by
    rw [yoshidaClippedLocalCriticalForm_apply,
      yoshidaClippedLocalCriticalPairing]
    rw [show (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand
          yoshidaEndpointA yoshidaEndpointA_pos one fs v) =
        (boundaryArchCorrelation (2 * yoshidaEndpointA)
          (residualEndpointCorrelation fs) : ℂ) by
      simpa only [one] using harch]
    dsimp only [g]
    rw [← hpolar]
    simp only [add_re, ofReal_re]
    ring
  have hswap :
      (yoshidaClippedLocalCriticalForm yoshidaEndpointA
        yoshidaEndpointA_pos fs one).re =
      (yoshidaClippedLocalCriticalForm yoshidaEndpointA
        yoshidaEndpointA_pos one fs).re := by
    have hherm := yoshidaClippedLocalCriticalForm_conj_apply
      yoshidaEndpointA_pos one fs
    simpa using congrArg Complex.re hherm
  have hclean := boundaryArch_add_polar_eq_cleanCross
    r hrcont (fun x hx ↦ by simpa only [fs] using hr_real x)
      hneg hpos hrEven
  unfold clippedCriticalFormSymmetricCross
  rw [Complex.add_re, hswap, hordered]
  dsimp only [g, fs] at hclean ⊢
  linarith

/-! ## Full real-even production diagonal -/

/-- Exact production-to-clean bridge for a real pointwise-even periodic
source, including its nonzero endpoint boundary value. -/
theorem clippedCriticalFormValue_even_eq_clean_add_boundary
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaEndpointA)
    (hf_real : ∀ x : ℝ,
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) x).im = 0) :
    (let c : ℝ :=
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) yoshidaEndpointA).re)
    let r : YoshidaClippedPeriodicCore yoshidaEndpointA :=
      evenBoundaryResidual f
    let g : ℝ → ℝ := fun x ↦
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re
    let w : ℝ → ℝ := centeredRescale yoshidaEndpointA g
    clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
        ((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
          YoshidaClippedSmooth yoshidaEndpointA) =
      yoshidaEndpointA * yoshidaEndpointOddCleanQuadratic
        (fun x ↦ c + w x)) := by
  let fs : YoshidaClippedSmooth yoshidaEndpointA :=
    ((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
      YoshidaClippedSmooth yoshidaEndpointA)
  let one : YoshidaClippedSmooth yoshidaEndpointA :=
    yoshidaClippedOne yoshidaEndpointA
  let c : ℝ := (fs yoshidaEndpointA).re
  let r : YoshidaClippedPeriodicCore yoshidaEndpointA :=
    evenBoundaryResidual f
  let rs : YoshidaClippedSmooth yoshidaEndpointA :=
    (r : YoshidaClippedSmooth yoshidaEndpointA)
  let g : ℝ → ℝ := fun x ↦ (rs x).re
  let w : ℝ → ℝ := centeredRescale yoshidaEndpointA g
  dsimp only
  have hfA : fs yoshidaEndpointA = (c : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [fs, c, ofReal_im] using hf_real yoshidaEndpointA
  have hcore : (c : ℂ) • periodicCoreOne yoshidaEndpointA + r = f.1 := by
    have h := evenBoundaryConstantPart_add_residual f
    unfold evenBoundaryConstantPart at h
    change fs yoshidaEndpointA • periodicCoreOne yoshidaEndpointA + r = f.1 at h
    rw [hfA] at h
    exact h
  have hdecomp : (c : ℂ) • one + rs = fs := by
    have h := congrArg
      (fun q : YoshidaClippedPeriodicCore yoshidaEndpointA ↦
        (q : YoshidaClippedSmooth yoshidaEndpointA)) hcore
    simpa only [one, rs, fs, r] using h
  have hform :
      clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos fs =
        c ^ 2 * clippedCriticalFormValue yoshidaEndpointA
            yoshidaEndpointA_pos one +
          clippedCriticalFormValue yoshidaEndpointA
            yoshidaEndpointA_pos rs +
          c * clippedCriticalFormSymmetricCross one rs := by
    unfold clippedCriticalFormValue clippedCriticalFormSymmetricCross
    rw [← hdecomp]
    simp only [map_add, map_smul, LinearMap.add_apply,
      LinearMap.map_smulₛₗ₂, smul_eq_mul]
    simp only [Complex.conj_ofReal, Complex.add_re,
      Complex.mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    ring
  have hends : rs (-yoshidaEndpointA) = 0 ∧
      rs yoshidaEndpointA = 0 := by
    simpa only [rs, r] using
      evenBoundaryResidual_endpoints_zero yoshidaEndpointA_pos f
  have hrreal (x : ℝ) : (rs x).im = 0 := by
    simpa only [rs, r] using evenBoundaryResidual_im_zero f hf_real x
  have hcross := clippedCriticalForm_symmetricCross_periodicCoreOne_eq_clean
    r (by simpa only [rs] using hrreal)
      (by simpa only [r, rs] using evenBoundaryResidual_pointwise_even f)
      (by simpa only [rs] using hends.1)
      (by simpa only [rs] using hends.2)
  have hconst := clippedCriticalFormValue_periodicCoreOne_eq_clean
  have hresidual :=
    clippedCriticalFormValue_evenBoundaryResidual_eq_clean f hf_real
  have hrcont : Continuous (rs : ℝ → ℂ) :=
    continuous_yoshidaClippedSmooth_of_endpoints_zero
      yoshidaEndpointA_pos rs hends.1 hends.2
  have hgcont : Continuous g := Complex.continuous_re.comp hrcont
  have hwcont : Continuous w := by
    dsimp only [w, centeredRescale]
    exact hgcont.comp (continuous_const.mul continuous_id)
  have hcleanAdd := yoshidaEndpointOddCleanQuadratic_add_constant
    w hwcont c
  rw [hform, hconst]
  change clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos rs = _
    at hresidual
  rw [hresidual]
  change clippedCriticalFormSymmetricCross one rs = _ at hcross
  rw [hcross]
  rw [hcleanAdd]
  ring

/-- Unconditional production nonnegativity for every real pointwise-even
periodic source. -/
theorem clippedCriticalFormValue_even_nonneg_of_clean
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaEndpointA)
    (hf_real : ∀ x : ℝ,
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) x).im = 0) :
    0 ≤ clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
      ((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) := by
  let fs : YoshidaClippedSmooth yoshidaEndpointA :=
    ((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
      YoshidaClippedSmooth yoshidaEndpointA)
  let c : ℝ := (fs yoshidaEndpointA).re
  let r : YoshidaClippedPeriodicCore yoshidaEndpointA :=
    evenBoundaryResidual f
  let rs : YoshidaClippedSmooth yoshidaEndpointA :=
    (r : YoshidaClippedSmooth yoshidaEndpointA)
  let g : ℝ → ℝ := fun x ↦ (rs x).re
  let w : ℝ → ℝ := centeredRescale yoshidaEndpointA g
  let u : ℝ → ℝ := fun x ↦ c + w x
  have hbridge := clippedCriticalFormValue_even_eq_clean_add_boundary f hf_real
  have hends : rs (-yoshidaEndpointA) = 0 ∧
      rs yoshidaEndpointA = 0 := by
    simpa only [rs, r] using
      evenBoundaryResidual_endpoints_zero yoshidaEndpointA_pos f
  have hrcont : Continuous (rs : ℝ → ℂ) :=
    continuous_yoshidaClippedSmooth_of_endpoints_zero
      yoshidaEndpointA_pos rs hends.1 hends.2
  have hgcont : Continuous g := Complex.continuous_re.comp hrcont
  have hgeven : Function.Even g := by
    intro x
    have heven := evenBoundaryResidual_pointwise_even f x
    exact congrArg Complex.re heven
  have hwcont : Continuous w := by
    dsimp only [w, centeredRescale]
    exact hgcont.comp (continuous_const.mul continuous_id)
  have hweven : Function.Even w := by
    intro x
    dsimp only [w, centeredRescale]
    rw [show yoshidaEndpointA * -x = -(yoshidaEndpointA * x) by ring,
      hgeven]
  have hucont : Continuous u := continuous_const.add hwcont
  have hueven : Function.Even u := by
    intro x
    dsimp only [u]
    rw [hweven]
  have hprofile : ContDiffOn ℝ 1 g
      (Icc (-yoshidaEndpointA) yoshidaEndpointA) := by
    exact Complex.reCLM.contDiff.comp_contDiffOn
      (rs.property.1.of_le (by simp))
  have hscale : ContDiffOn ℝ 1
      (fun x : ℝ ↦ yoshidaEndpointA * x) (Icc (-1) 1) := by
    fun_prop
  have hmaps : MapsTo (fun x : ℝ ↦ yoshidaEndpointA * x)
      (Icc (-1) 1) (Icc (-yoshidaEndpointA) yoshidaEndpointA) := by
    intro x hx
    constructor <;> nlinarith [hx.1, hx.2, yoshidaEndpointA_pos]
  have hulocal : LocallyLipschitzOn (Icc (-1) 1) u := by
    have hsumProfile : ContDiffOn ℝ 1 (fun x ↦ c + g x)
        (Icc (-yoshidaEndpointA) yoshidaEndpointA) :=
      contDiffOn_const.add hprofile
    have hcomp := hsumProfile.comp hscale hmaps
    simpa only [u, w, centeredRescale, Function.comp_apply] using
      hcomp.locallyLipschitzOn (convex_Icc (-1) 1)
  have hQ : 0 ≤ yoshidaEndpointOddCleanQuadratic u :=
    yoshidaEndpointOddCleanQuadratic_nonneg_of_even_of_locallyLipschitzOn
      u hucont hueven hulocal
  change clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos fs = _
    at hbridge
  change 0 ≤ clippedCriticalFormValue yoshidaEndpointA
    yoshidaEndpointA_pos fs
  rw [hbridge]
  exact mul_nonneg yoshidaEndpointA_pos.le hQ

/-! ## Complex pointwise-even production diagonal -/

/-- Unconditional production nonnegativity for an arbitrary complex-valued
pointwise-even periodic source. -/
theorem yoshidaClippedLocalCriticalForm_re_nonneg_of_pointwiseEven
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaEndpointA) :
    0 ≤ (yoshidaClippedLocalCriticalForm yoshidaEndpointA
      yoshidaEndpointA_pos
      ((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA)
      ((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA)).re := by
  let fs : YoshidaClippedSmooth yoshidaEndpointA :=
    ((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
      YoshidaClippedSmooth yoshidaEndpointA)
  let fr : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaEndpointA :=
    pointwiseEvenPeriodicCoreRealPart f
  let fi : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaEndpointA :=
    pointwiseEvenPeriodicCoreImagPart f
  have hr : 0 ≤ clippedCriticalFormValue yoshidaEndpointA
      yoshidaEndpointA_pos
      ((fr.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) :=
    clippedCriticalFormValue_even_nonneg_of_clean fr
      (fun x ↦ by
        simpa only [fr] using pointwiseEvenPeriodicCoreRealPart_im_zero f)
  have hi : 0 ≤ clippedCriticalFormValue yoshidaEndpointA
      yoshidaEndpointA_pos
      ((fi.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) :=
    clippedCriticalFormValue_even_nonneg_of_clean fi
      (fun x ↦ by
        simpa only [fi] using pointwiseEvenPeriodicCoreImagPart_im_zero f)
  have hsplit := yoshidaClippedLocalCriticalForm_real_add_imag_re
    yoshidaEndpointA_pos fs
  change 0 ≤ (yoshidaClippedLocalCriticalForm yoshidaEndpointA
    yoshidaEndpointA_pos fs fs).re
  change (yoshidaClippedLocalCriticalForm yoshidaEndpointA
      yoshidaEndpointA_pos fs fs).re =
    (yoshidaClippedLocalCriticalForm yoshidaEndpointA yoshidaEndpointA_pos
      (((fr.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA))
      (((fr.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA))).re +
    (yoshidaClippedLocalCriticalForm yoshidaEndpointA yoshidaEndpointA_pos
      (((fi.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA))
      (((fi.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA))).re at hsplit
  rw [hsplit]
  exact add_nonneg hr hi

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryProductionBridge
