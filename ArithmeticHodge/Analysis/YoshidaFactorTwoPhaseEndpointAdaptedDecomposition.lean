import ArithmeticHodge.Analysis.YoshidaEvenInfiniteSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedLow
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailRealification

set_option autoImplicit false
set_option maxRecDepth 100000

open Complex Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedDecomposition

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEvenHomogeneousCoercivity
open YoshidaEvenInfiniteSchur
open YoshidaEvenTailLowFunctional
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseTailRealification
open YoshidaParityRecombination
open YoshidaPointwiseOddRealImag
open YoshidaWeightedTailBounds

/-!
# Real endpoint-adapted Fourier decomposition

For a pointwise-real periodic even core whose endpoint trace vanishes, the
standard complex two-hundred-mode Fourier split can be realified without
changing its finite dimension.  The endpoint traces of the real low modes
are transferred to frequency `200`, which remains in the cutoff-`199` tail.
The resulting low basis and tail both vanish at the identified endpoints.
-/

/-- Pointwise realification, bundled back into the cutoff-`199` even tail. -/
def realifiedEvenOneNinetyNineTail
    (f : YoshidaEvenOneNinetyNineTail) :
    YoshidaEvenOneNinetyNineTail :=
  ⟨periodicCoreRealPart
      (f : YoshidaClippedPeriodicCore yoshidaA),
    periodicCoreRealPart_mem_evenTail yoshidaA_pos 199
      (f : YoshidaClippedPeriodicCore yoshidaA) f.property⟩

@[simp] theorem realifiedEvenOneNinetyNineTail_apply
    (f : YoshidaEvenOneNinetyNineTail) (x : ℝ) :
    evenOneNinetyNineTailToClippedSmooth
        (realifiedEvenOneNinetyNineTail f) x =
      ((((evenOneNinetyNineTailToClippedSmooth f) x).re : ℝ) : ℂ) :=
  rfl

/-- The total real endpoint trace of a two-hundred-coordinate low vector,
measured in units of the frequency-`200` endpoint trace. -/
def evenLowEndpointCorrectionCoefficient
    (c : YoshidaEvenIndex → ℝ) : ℝ :=
  ∑ i, c i * endpointEvenLowTraceRatio i

/-- Move the endpoint trace of a real low vector into the first mode of the
actual even tail. -/
def endpointAdaptedEvenRealTail
    (c : YoshidaEvenIndex → ℝ)
    (f : YoshidaEvenOneNinetyNineTail) :
    YoshidaEvenOneNinetyNineTail :=
  ⟨(realifiedEvenOneNinetyNineTail f :
      YoshidaClippedPeriodicCore yoshidaA) +
      (evenLowEndpointCorrectionCoefficient c : ℂ) •
        evenHighModePeriodicCore 0,
    (yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199).add_mem
      (realifiedEvenOneNinetyNineTail f).property
      ((yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199).smul_mem
        (evenLowEndpointCorrectionCoefficient c : ℂ)
        endpointEvenCorrectionMode_mem_tail)⟩

/-- Taking real parts of the complex Fourier coefficients and of the tail
preserves a decomposition of a pointwise-real even core. -/
private theorem realify_even_low_add_tail
    (g : YoshidaPeriodicEvenCore)
    (hgReal : ∀ x : ℝ,
      ((((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0)
    (c : YoshidaEvenIndex → ℂ)
    (f : YoshidaEvenOneNinetyNineTail)
    (hdecomp :
      (((g : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)) =
        (∑ i, c i • yoshidaClippedEvenLowMode yoshidaA i) +
          evenOneNinetyNineTailToClippedSmooth f) :
    (((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA)) =
      (∑ i, (((c i).re : ℝ) : ℂ) •
        yoshidaClippedEvenLowMode yoshidaA i) +
        evenOneNinetyNineTailToClippedSmooth
          (realifiedEvenOneNinetyNineTail f) := by
  classical
  ext x
  apply Complex.ext
  · simp only [Submodule.coe_add, Submodule.coe_sum,
      Submodule.coe_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Complex.add_re, Complex.re_sum, Complex.mul_re,
      realifiedEvenOneNinetyNineTail_apply, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have hx := congrArg
        (fun h : YoshidaClippedSmooth yoshidaA ↦ (h x).re) hdecomp
    simpa [map_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Complex.mul_re, evenLowMode_im_zero,
      realifiedEvenOneNinetyNineTail_apply] using hx
  · simp only [Submodule.coe_add, Submodule.coe_sum,
      Submodule.coe_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Complex.add_im, Complex.im_sum, Complex.mul_im,
      realifiedEvenOneNinetyNineTail_apply, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    rw [hgReal x]
    simp [evenLowMode_im_zero]

/-- Exact dimension-preserving real endpoint-adapted decomposition of a
pointwise-real even core with zero positive-endpoint trace. -/
theorem exists_periodicEvenCore_real_endpointAdapted_low_add_tail
    (g : YoshidaPeriodicEvenCore)
    (hgReal : ∀ x : ℝ,
      ((((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0)
    (hgEndpoint :
      (((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) yoshidaA = 0)) :
    ∃ c : YoshidaEvenIndex → ℝ,
      ∃ f : YoshidaEvenOneNinetyNineTail,
        (((g : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA)) =
          (∑ i, ((c i : ℝ) : ℂ) •
            endpointAdaptedEvenLowMode i) +
            evenOneNinetyNineTailToClippedSmooth f ∧
        (∀ x : ℝ,
          ((evenOneNinetyNineTailToClippedSmooth f x).im) = 0) ∧
        evenOneNinetyNineTailToClippedSmooth f (-yoshidaA) = 0 ∧
        evenOneNinetyNineTailToClippedSmooth f yoshidaA = 0 := by
  classical
  obtain ⟨c, f, hdecomp⟩ :=
    exists_periodicEvenCore_low_add_actualTail g
  let cr : YoshidaEvenIndex → ℝ := fun i ↦ (c i).re
  let tail : YoshidaEvenOneNinetyNineTail :=
    endpointAdaptedEvenRealTail cr f
  have hreal := realify_even_low_add_tail g hgReal c f hdecomp
  have hadapted :
      (((g : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)) =
        (∑ i, ((cr i : ℝ) : ℂ) •
          endpointAdaptedEvenLowMode i) +
          evenOneNinetyNineTailToClippedSmooth tail := by
    rw [hreal]
    simp_rw [evenLowMode_eq_endpointMode_add_endpointAdapted]
    simp only [smul_add, Finset.sum_add_distrib]
    change
      (∑ i, ((cr i : ℝ) : ℂ) •
          ((endpointEvenLowTraceRatio i : ℂ) •
            yoshidaClippedEvenMode yoshidaA 200) +
        ∑ i, ((cr i : ℝ) : ℂ) •
          endpointAdaptedEvenLowMode i) +
          evenOneNinetyNineTailToClippedSmooth
            (realifiedEvenOneNinetyNineTail f) =
        (∑ i, ((cr i : ℝ) : ℂ) •
          endpointAdaptedEvenLowMode i) +
          evenOneNinetyNineTailToClippedSmooth tail
    dsimp only [tail, endpointAdaptedEvenRealTail]
    change
      (∑ i, ((cr i : ℝ) : ℂ) •
          ((endpointEvenLowTraceRatio i : ℂ) •
            yoshidaClippedEvenMode yoshidaA 200) +
        ∑ i, ((cr i : ℝ) : ℂ) •
          endpointAdaptedEvenLowMode i) +
          evenOneNinetyNineTailToClippedSmooth
            (realifiedEvenOneNinetyNineTail f) =
        (∑ i, ((cr i : ℝ) : ℂ) •
          endpointAdaptedEvenLowMode i) +
          (evenOneNinetyNineTailToClippedSmooth
              (realifiedEvenOneNinetyNineTail f) +
            (evenLowEndpointCorrectionCoefficient cr : ℂ) •
              yoshidaClippedEvenMode yoshidaA 200)
    have hcorrection :
        (∑ i, ((cr i : ℝ) : ℂ) •
          ((endpointEvenLowTraceRatio i : ℂ) •
            yoshidaClippedEvenMode yoshidaA 200)) =
          (evenLowEndpointCorrectionCoefficient cr : ℂ) •
            yoshidaClippedEvenMode yoshidaA 200 := by
      simp_rw [smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      simp [evenLowEndpointCorrectionCoefficient]
    rw [hcorrection]
    abel
  have htailReal : ∀ x : ℝ,
      (evenOneNinetyNineTailToClippedSmooth tail x).im = 0 := by
    intro x
    change
      (((((evenOneNinetyNineTailToClippedSmooth
          (realifiedEvenOneNinetyNineTail f)) x) +
        (evenLowEndpointCorrectionCoefficient cr : ℂ) *
          yoshidaClippedEvenMode yoshidaA 200 x)).im) = 0
    rw [Complex.add_im, Complex.mul_im,
      realifiedEvenOneNinetyNineTail_apply,
      YoshidaFactorTwoPhaseEndpointAdaptedLow.evenMode_im_zero]
    simp
  have htailPos :
      evenOneNinetyNineTailToClippedSmooth tail yoshidaA = 0 := by
    have hpos := congrArg
      (fun h : YoshidaClippedSmooth yoshidaA ↦ h yoshidaA) hadapted
    have hzero :
        (∑ i, (((cr i : ℝ) : ℂ) •
          (endpointAdaptedEvenLowMode i : ℝ → ℂ)) yoshidaA) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Pi.smul_apply, endpointAdaptedEvenLowMode_apply_pos]
      simp
    have hsum :
        (∑ i, (((cr i : ℝ) : ℂ) •
          endpointAdaptedEvenLowMode i)) yoshidaA = 0 := by
      simpa [Finset.sum_apply] using hzero
    have hpos' :
        (((g : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) yoshidaA) =
          (∑ i, (((cr i : ℝ) : ℂ) •
            endpointAdaptedEvenLowMode i)) yoshidaA +
            evenOneNinetyNineTailToClippedSmooth tail yoshidaA := by
      simpa only [Submodule.coe_add, Pi.add_apply] using hpos
    rw [hgEndpoint, hsum, zero_add] at hpos'
    exact hpos'.symm
  have htailNeg :
      evenOneNinetyNineTailToClippedSmooth tail (-yoshidaA) = 0 := by
    have heven := evenTail_pointwise_even yoshidaA_pos 199
      (tail : YoshidaClippedPeriodicCore yoshidaA) tail.property yoshidaA
    change evenOneNinetyNineTailToClippedSmooth tail (-yoshidaA) =
      evenOneNinetyNineTailToClippedSmooth tail yoshidaA at heven
    exact heven.trans htailPos
  exact ⟨cr, tail, hadapted, htailReal, htailNeg, htailPos⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedDecomposition
