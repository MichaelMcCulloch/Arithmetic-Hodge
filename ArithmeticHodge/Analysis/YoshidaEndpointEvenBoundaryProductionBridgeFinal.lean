import ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryProductionBridge
import ArithmeticHodge.Analysis.YoshidaClippedRealImagEnergySplit
import ArithmeticHodge.Analysis.YoshidaPointwiseOddRealImag

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryProductionBridge

open ArithmeticHodge.Analysis
open YoshidaClippedRealImagEnergySplit
open YoshidaEndpointClippedPolarBridge
open YoshidaEndpointEvenBoundaryResidual
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenResidualProduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPhysicalRealQuadratic
open YoshidaEndpointPolarScaling
open YoshidaEndpointScaledCorrelation
open YoshidaPointwiseOddRealImag
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

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryProductionBridge
