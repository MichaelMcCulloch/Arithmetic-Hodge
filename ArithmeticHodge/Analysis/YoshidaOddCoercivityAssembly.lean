import ArithmeticHodge.Analysis.YoshidaOddDigammaSplit
import ArithmeticHodge.Analysis.YoshidaOddPolarBound

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaOddCoercivityAssembly

open YoshidaCoercivityNumerics
open YoshidaOddDigammaSplit
open YoshidaOddPolarBound
open YoshidaSectionSixAnalytic
open YoshidaTZeroTailBounds
open YoshidaWeightedTailBounds

/-!
# Odd Section 6 coercivity assembly

The certified low digamma loss, infinite high-frequency estimate, global
digamma split, exact polar loss, and numerical Section 6 substitution are
composed here for the actual periodic odd tail.  The only remaining analytic
inputs are pointwise oddness, the two spectral integrability facts, and the
unit Parseval identity.
-/

theorem oddTenTail_clipped_form_value_ge_38_div_25
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)
    (hodd : ∀ x : ℝ,
      (f : YoshidaClippedSmooth yoshidaA) (-x) =
        -(f : YoshidaClippedSmooth yoshidaA) x)
    (henergy :
      (∫ x : ℝ in -yoshidaA..yoshidaA,
        ‖((f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) x‖ ^ 2) = 1)
    (hMassInt : Integrable (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
        yoshidaA_pos v (f : YoshidaClippedSmooth yoshidaA))))
    (hDigammaInt : Integrable (fun v : ℝ ↦
      digammaQuarterVerticalRe v *
        Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
          yoshidaA_pos v (f : YoshidaClippedSmooth yoshidaA))))
    (hParseval : clippedSpectralMass yoshidaA yoshidaA_pos
      (f : YoshidaClippedSmooth yoshidaA) = 1) :
    (38 / 25 : ℝ) ≤
      clippedCriticalFormValue yoshidaA yoshidaA_pos
        (f : YoshidaClippedSmooth yoshidaA) := by
  have ht := isYoshidaTZero_yoshidaTZero
  have hDigamma := oddTenTail_clippedSection6DigammaLowerEstimate
    ht f hf henergy hMassInt hDigammaInt hParseval
  have hDigammaInt' : Integrable (fun v : ℝ ↦
      (Complex.digamma
        ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re *
        Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
          yoshidaA_pos v (f : YoshidaClippedSmooth yoshidaA))) := by
    simpa only [digammaQuarterVerticalRe] using hDigammaInt
  have hArch := clippedSection6ArchLowerEstimate_of_digamma_parseval
    yoshidaA_pos (f : YoshidaClippedSmooth yoshidaA)
    hDigammaInt' hMassInt hParseval hDigamma
  have hPolar := odd_polar_section6_lower_bound
    (f : YoshidaClippedSmooth yoshidaA) hodd henergy
  exact odd_canonical_clipped_form_value_ge_38_div_25
    (f : YoshidaClippedSmooth yoshidaA) hPolar hArch

end ArithmeticHodge.Analysis.YoshidaOddCoercivityAssembly
