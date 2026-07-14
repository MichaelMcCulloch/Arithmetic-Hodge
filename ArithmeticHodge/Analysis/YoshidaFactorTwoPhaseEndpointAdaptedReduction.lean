import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedDecomposition
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedTail
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddRealDecomposition

set_option autoImplicit false
set_option maxRecDepth 100000

open Complex Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedReduction

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaClippedMomentBridge
open YoshidaCoercivityNumerics
open YoshidaEvenHomogeneousCoercivity
open YoshidaEvenTailLowFunctional
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoPhaseEndpointAdaptedDecomposition
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseEndpointAdaptedTail
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseOddRealDecomposition
open YoshidaOddHomogeneousCoercivity
open YoshidaOddInfiniteSchur
open YoshidaOddSpectralMassBridge
open YoshidaParityRecombination
open YoshidaWeightedTailBounds

/-!
# Endpoint-adapted phase reduction

This combines the dimension-preserving real even decomposition and the real
odd decomposition with the phase-uniform tail theorem.  The finite vectors
and the actual Fourier tails remain explicit, so the remaining obligation is
precisely the finite-low and low--tail Schur block.
-/

/-- A pointwise-real even/odd pair admits simultaneous real finite Fourier
decompositions whose exposed pure-tail phase is nonnegative throughout the
closed phase disk.  The even finite basis is endpoint-adapted, while the odd
basis is the canonical ten-mode basis. -/
theorem exists_real_endpointAdapted_low_tails_with_phase_nonnegative
    (ge : YoshidaPeriodicEvenCore)
    (go : YoshidaPeriodicOddCore)
    (heReal : ∀ x : ℝ,
      ((((ge : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0)
    (heEndpoint :
      (((ge : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) yoshidaA = 0))
    (hoReal : ∀ x : ℝ,
      ((((go : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    ∃ ce : Fin 200 → ℝ, ∃ co : Fin 10 → ℝ,
      ∃ re : YoshidaEvenOneNinetyNineTail,
        ∃ ro : YoshidaOddTenTail,
          (((ge : YoshidaClippedPeriodicCore yoshidaA) :
              YoshidaClippedSmooth yoshidaA)) =
            (∑ i, ((ce i : ℝ) : ℂ) • endpointAdaptedEvenLowMode i) +
              evenOneNinetyNineTailToClippedSmooth re ∧
          (((go : YoshidaClippedPeriodicCore yoshidaA) :
              YoshidaClippedSmooth yoshidaA)) =
            (∑ i, ((co i : ℝ) : ℂ) •
              yoshidaClippedOddLowMode yoshidaA i) +
              oddTenTailToClippedSmooth ro ∧
          (∀ x : ℝ,
            (evenOneNinetyNineTailToClippedSmooth re x).im = 0) ∧
          evenOneNinetyNineTailToClippedSmooth re (-yoshidaA) = 0 ∧
          evenOneNinetyNineTailToClippedSmooth re yoshidaA = 0 ∧
          (∀ x : ℝ, (oddTenTailToClippedSmooth ro x).im = 0) ∧
          oddTenTailToClippedSmooth ro (-yoshidaA) = 0 ∧
          oddTenTailToClippedSmooth ro yoshidaA = 0 ∧
          (let eTail := centeredRescale yoshidaA (fun x ↦
              ((((re : YoshidaClippedPeriodicCore yoshidaA) :
                YoshidaClippedSmooth yoshidaA) x).re))
           let oTail := centeredRescale yoshidaA (fun x ↦
              ((((ro : YoshidaClippedPeriodicCore yoshidaA) :
                YoshidaClippedSmooth yoshidaA) x).re))
           0 ≤ factorTwoEndpointChannelPhase eTail oTail a b) := by
  classical
  obtain ⟨ce, re, heDecomp, heTailReal, heNeg, hePos⟩ :=
    exists_periodicEvenCore_real_endpointAdapted_low_add_tail
      ge heReal heEndpoint
  obtain ⟨co, ro, hoDecomp, hoTailReal, hoNeg, hoPos⟩ :=
    exists_periodicOddCore_real_low_add_tail go hoReal
  refine ⟨ce, co, re, ro, heDecomp, hoDecomp,
    heTailReal, heNeg, hePos, hoTailReal, hoNeg, hoPos, ?_⟩
  have heFixed :
      endpointAdaptedEvenTail
          (re : YoshidaClippedPeriodicCore yoshidaA) =
        (re : YoshidaClippedPeriodicCore yoshidaA) :=
    endpointAdaptedEvenTail_eq_self_of_apply_pos_eq_zero
      (re : YoshidaClippedPeriodicCore yoshidaA) (by
        simpa only [evenOneNinetyNineTailToClippedSmooth_apply] using hePos)
  have htail := endpointAdapted_tail_phase_uniform
    (re : YoshidaClippedPeriodicCore yoshidaA)
    (ro : YoshidaClippedPeriodicCore yoshidaA)
    re.property ro.property heTailReal hoTailReal a b hphase
  simpa only [heFixed] using htail

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedReduction
