import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedWeightedLp
import ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualRegularity

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedAssembly

open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedWeightedLp
open YoshidaEndpointEvenResidualRegularity
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOddCleanPositive

noncomputable section

/-!
# Assembly of the structural projected-even Schur argument

All form-domain, projection, integrability, low-Gram, and residual hypotheses
are discharged here.  The sole visible premise is the fixed projected-dual
inequality.  Once its explicit two-by-two determinant is positive, the
complete infinite even sector follows immediately.
-/

/-- Uniform control of the two fixed projected representers implies
nonnegativity of the clean endpoint quadratic for every continuous, even,
locally Lipschitz profile. -/
theorem yoshidaEndpointOddCleanQuadratic_nonneg_of_even_of_projectedDual
    (w : ℝ → ℝ) (hw : Continuous w) (hweven : Function.Even w)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) w)
    (hdualGram : ∀ c b : ℝ,
      (∫ x : ℝ in -1..1,
        (c * fixedProjectedTailRepresenter0 x +
          b * fixedProjectedTailRepresenter2 x) ^ 2 /
            yoshidaEndpointEvenTailWeight x) ≤
        yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * b +
          yoshidaEndpointEvenLowGram22 * b ^ 2) :
    0 ≤ yoshidaEndpointOddCleanQuadratic w := by
  let c : ℝ := centeredEvenP0Coefficient w
  let b : ℝ := centeredEvenP2Coefficient w
  let r : ℝ → ℝ := centeredEvenZeroTwoResidual w
  have hr : Continuous r := by
    simpa only [r] using continuous_centeredEvenZeroTwoResidual w hw
  have hre : Function.Even r := by
    simpa only [r] using centeredEvenZeroTwoResidual_even w hweven
  have hzero : centeredEvenP0Coefficient r = 0 := by
    simpa only [r] using
      centeredEvenP0Coefficient_zeroTwoResidual_eq_zero w hw
  have htwo : centeredEvenP2Coefficient r = 0 := by
    simpa only [r] using
      centeredEvenP2Coefficient_zeroTwoResidual_eq_zero w hw
  have hlocalR : LocallyLipschitzOn (Icc (-1) 1) r := by
    simpa only [r] using
      locallyLipschitzOn_centeredEvenZeroTwoResidual w hlocal
  have hdualLp : ∀ c b : ℝ,
      MemLp (fun x : ℝ ↦
        (c * yoshidaEndpointEvenProjectedTailRepresenter0
              (73 / 48) (35 / 48) x +
          b * yoshidaEndpointEvenProjectedTailRepresenter2
              (7 / 48) (1 / 2) x) /
            Real.sqrt (yoshidaEndpointEvenTailWeight x)) 2
        (volume.restrict (Ioc (-1) 1)) := by
    intro d e
    simpa only [fixedProjectedTailRepresenter0,
      fixedProjectedTailRepresenter2] using
      fixedProjectedTailRepresenter_div_sqrt_memLp_two d e
  have hprimal : MemLp (fun x : ℝ ↦
      Real.sqrt (yoshidaEndpointEvenTailWeight x) * r x) 2
      (volume.restrict (Ioc (-1) 1)) :=
    sqrt_tailWeight_mul_memLp_two r hr
  have hcross0 : IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenTailRepresenter0 x * r x)
      volume (-1) 1 :=
    intervalIntegrable_yoshidaEndpointEvenTailRepresenter0_mul r hr
  have hcross2 : IntervalIntegrable
      (fun x ↦ yoshidaEndpointEvenTailRepresenter2 x * r x)
      volume (-1) 1 :=
    intervalIntegrable_yoshidaEndpointEvenTailRepresenter2_mul r hr
  have hdual : ∀ d e : ℝ,
      (∫ x : ℝ in -1..1,
        (d * yoshidaEndpointEvenProjectedTailRepresenter0
              (73 / 48) (35 / 48) x +
          e * yoshidaEndpointEvenProjectedTailRepresenter2
              (7 / 48) (1 / 2) x) ^ 2 /
            yoshidaEndpointEvenTailWeight x) ≤
        yoshidaEndpointEvenLowGram00 * d ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * d * e +
          yoshidaEndpointEvenLowGram22 * e ^ 2 := by
    intro d e
    simpa only [fixedProjectedTailRepresenter0,
      fixedProjectedTailRepresenter2] using hdualGram d e
  have hform := yoshidaEndpointOddCleanQuadratic_fixed_low_tail_expansion
    r hr hre hzero htwo hlocalR c b
  have hnonneg :=
    cleanQuadratic_nonneg_of_fixed_lowGram_of_projected_weighted_dual
      r hr hre hzero htwo hlocalR c b
      (73 / 48) (35 / 48) (7 / 48) (1 / 2)
      yoshidaEndpointEvenLowGram00_pos
      yoshidaEndpointEvenLowGram_det_pos
      hdualLp hprimal hcross0 hcross2 hdual hform
  have hdecomp : (fun x ↦
      c * centeredEvenP0 x + b * centeredEvenP2 x + r x) = w := by
    simpa only [c, b, r] using low_add_zeroTwoResidual_eq w
  rw [hdecomp] at hnonneg
  exact hnonneg

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedAssembly
