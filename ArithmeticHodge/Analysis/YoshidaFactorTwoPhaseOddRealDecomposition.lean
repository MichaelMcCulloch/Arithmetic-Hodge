import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailRealification
import ArithmeticHodge.Analysis.YoshidaOddInfiniteSchur
import ArithmeticHodge.Analysis.YoshidaParityRecombination

set_option autoImplicit false

open Complex Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddRealDecomposition

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaClippedMomentBridge
open YoshidaCoercivityNumerics
open YoshidaFactorTwoPhaseTailRealification
open YoshidaOddHomogeneousCoercivity
open YoshidaOddInfiniteSchur
open YoshidaOddSpectralMassBridge
open YoshidaParityRecombination
open YoshidaPointwiseOddRealImag
open YoshidaWeightedTailBounds

/-!
# Real low/tail decomposition of the periodic odd carrier

A pointwise-real periodic odd core has a ten-mode Fourier decomposition with
real coefficients and a pointwise-real actual odd tail.  Oddness and
periodicity force the tail to vanish at both identified endpoints.
-/

/-- Pointwise realification, bundled back into the actual tenth odd tail. -/
def realifiedOddTenTail (f : YoshidaOddTenTail) : YoshidaOddTenTail :=
  ⟨periodicCoreRealPart
      (f : YoshidaClippedPeriodicCore yoshidaA),
    periodicCoreRealPart_mem_oddTail yoshidaA_pos 10
      (f : YoshidaClippedPeriodicCore yoshidaA) f.property⟩

@[simp] theorem realifiedOddTenTail_apply
    (f : YoshidaOddTenTail) (x : ℝ) :
    oddTenTailToClippedSmooth (realifiedOddTenTail f) x =
      ((((oddTenTailToClippedSmooth f x).re : ℝ) : ℂ)) :=
  rfl

/-- Every canonical odd low mode is pointwise real. -/
theorem oddLowMode_im_zero (i : YoshidaOddIndex) (x : ℝ) :
    (yoshidaClippedOddLowMode yoshidaA i x).im = 0 := by
  by_cases hx : x ∈ Set.Icc (-yoshidaA) yoshidaA
  · rw [yoshidaClippedOddLowMode,
      yoshidaClippedOddMode_apply_of_mem yoshidaA_pos (i.1 + 1) hx]
    exact Complex.ofReal_im _
  · rw [yoshidaClippedSmooth_eq_zero_outside
      (yoshidaClippedOddLowMode yoshidaA i) hx]
    exact Complex.zero_im

/-- Taking real parts of the complex Fourier coefficients and tail preserves
the decomposition of a pointwise-real periodic odd core. -/
private theorem realify_odd_low_add_tail
    (g : YoshidaPeriodicOddCore)
    (hgReal : ∀ x : ℝ,
      ((((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0)
    (c : YoshidaOddIndex → ℂ)
    (f : YoshidaOddTenTail)
    (hdecomp :
      (((g : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)) =
        (∑ i, c i • yoshidaClippedOddLowMode yoshidaA i) +
          oddTenTailToClippedSmooth f) :
    (((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA)) =
      (∑ i, (((c i).re : ℝ) : ℂ) •
        yoshidaClippedOddLowMode yoshidaA i) +
        oddTenTailToClippedSmooth (realifiedOddTenTail f) := by
  classical
  ext x
  apply Complex.ext
  · simp only [Submodule.coe_add, Submodule.coe_sum,
      Submodule.coe_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Complex.add_re, Complex.re_sum, Complex.mul_re,
      realifiedOddTenTail_apply, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    have hx := congrArg
      (fun h : YoshidaClippedSmooth yoshidaA ↦ (h x).re) hdecomp
    simpa [map_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Complex.mul_re, oddLowMode_im_zero,
      realifiedOddTenTail_apply] using hx
  · simp only [Submodule.coe_add, Submodule.coe_sum,
      Submodule.coe_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Complex.add_im, Complex.im_sum, Complex.mul_im,
      realifiedOddTenTail_apply, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    rw [hgReal x]
    simp [oddLowMode_im_zero]

/-- Every actual periodic odd Fourier tail vanishes at both identified
endpoints. -/
theorem oddTenTail_endpoints_zero (f : YoshidaOddTenTail) :
    oddTenTailToClippedSmooth f (-yoshidaA) = 0 ∧
      oddTenTailToClippedSmooth f yoshidaA = 0 := by
  let r : YoshidaClippedPeriodicCore yoshidaA := f
  have hodd : (r : YoshidaClippedSmooth yoshidaA) (-yoshidaA) =
      -(r : YoshidaClippedSmooth yoshidaA) yoshidaA :=
    oddTail_pointwise_odd yoshidaA_pos 10 r f.property yoshidaA
  have hperiod : (r : YoshidaClippedSmooth yoshidaA) (-yoshidaA) =
      (r : YoshidaClippedSmooth yoshidaA) yoshidaA :=
    periodicCore_endpoint_eq yoshidaA_pos r
  have hpos : (r : YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
    have htwo : (2 : ℂ) *
        (r : YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
      calc
        (2 : ℂ) * (r : YoshidaClippedSmooth yoshidaA) yoshidaA =
            (r : YoshidaClippedSmooth yoshidaA) yoshidaA +
              (r : YoshidaClippedSmooth yoshidaA) yoshidaA := by ring
        _ = (r : YoshidaClippedSmooth yoshidaA) (-yoshidaA) +
              (r : YoshidaClippedSmooth yoshidaA) yoshidaA := by
            rw [hperiod]
        _ = -(r : YoshidaClippedSmooth yoshidaA) yoshidaA +
              (r : YoshidaClippedSmooth yoshidaA) yoshidaA := by
            rw [hodd]
        _ = 0 := neg_add_cancel _
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact ⟨hperiod.trans hpos, hpos⟩

/-- Exact real ten-mode plus real-tail decomposition of every pointwise-real
periodic odd core, with endpoint cancellation recorded on the tail. -/
theorem exists_periodicOddCore_real_low_add_tail
    (g : YoshidaPeriodicOddCore)
    (hgReal : ∀ x : ℝ,
      ((((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0) :
    ∃ c : YoshidaOddIndex → ℝ, ∃ f : YoshidaOddTenTail,
      (((g : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)) =
        (∑ i, ((c i : ℝ) : ℂ) •
          yoshidaClippedOddLowMode yoshidaA i) +
          oddTenTailToClippedSmooth f ∧
      (∀ x : ℝ, (oddTenTailToClippedSmooth f x).im = 0) ∧
      oddTenTailToClippedSmooth f (-yoshidaA) = 0 ∧
      oddTenTailToClippedSmooth f yoshidaA = 0 := by
  classical
  obtain ⟨c, f, hdecomp⟩ :=
    exists_periodicOddCore_low_add_actualTail g
  let cr : YoshidaOddIndex → ℝ := fun i ↦ (c i).re
  let tail : YoshidaOddTenTail := realifiedOddTenTail f
  have hreal :
      (((g : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)) =
        (∑ i, (((c i).re : ℝ) : ℂ) •
          yoshidaClippedOddLowMode yoshidaA i) +
          oddTenTailToClippedSmooth (realifiedOddTenTail f) :=
    realify_odd_low_add_tail g hgReal c f hdecomp
  have htailReal : ∀ x : ℝ,
      (oddTenTailToClippedSmooth tail x).im = 0 := by
    intro x
    change (((periodicCoreRealPart
      (f : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) x).im = 0
    exact periodicCoreRealPart_im_zero
      (f : YoshidaClippedPeriodicCore yoshidaA)
  obtain ⟨hneg, hpos⟩ := oddTenTail_endpoints_zero tail
  refine ⟨cr, tail, ?_, htailReal, hneg, hpos⟩
  simpa only [cr, tail] using hreal

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddRealDecomposition
