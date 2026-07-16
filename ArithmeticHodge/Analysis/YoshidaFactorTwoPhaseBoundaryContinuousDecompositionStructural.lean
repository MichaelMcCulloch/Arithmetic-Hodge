import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedDecomposition

set_option autoImplicit false
set_option maxRecDepth 100000

open Complex Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaClippedEvenMomentBridge
open YoshidaCoercivityNumerics
open YoshidaEvenHomogeneousCoercivity
open YoshidaEvenInfiniteSchur
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoPhaseEndpointAdaptedDecomposition
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseTailRealification
open YoshidaParityRecombination
open YoshidaPointwiseParityCore
open YoshidaPointwiseOddRealImag
open YoshidaWeightedTailBounds

/-!
# Canonical real even low--tail decomposition

The boundary-continuous carrier does not move endpoint trace into frequency
`200`.  Consequently its finite block is the original `Fin 200` Fourier block
and its tail is the original cutoff-`199` tail.  This file exposes the exact
realification of that canonical split, which was previously only an internal
step of the endpoint-adapted construction.
-/

/-- Taking real parts of the canonical Fourier coefficients and tail preserves
the exact low-plus-tail decomposition of a pointwise-real even core. -/
theorem realify_even_low_add_actualTail
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

/-- Every pointwise-real periodic even core admits the standard real
`Fin 200` low block plus a pointwise-real cutoff-`199` tail.  No endpoint
adaptation or finite-dimensional change of basis occurs. -/
theorem exists_periodicEvenCore_real_low_add_actualTail
    (g : YoshidaPeriodicEvenCore)
    (hgReal : ∀ x : ℝ,
      ((((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0) :
    ∃ c : YoshidaEvenIndex → ℝ,
      ∃ f : YoshidaEvenOneNinetyNineTail,
        (((g : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA)) =
          (∑ i, ((c i : ℝ) : ℂ) •
            yoshidaClippedEvenLowMode yoshidaA i) +
            evenOneNinetyNineTailToClippedSmooth f ∧
        (∀ x : ℝ,
          ((evenOneNinetyNineTailToClippedSmooth f x).im) = 0) := by
  obtain ⟨c, f, hdecomp⟩ :=
    exists_periodicEvenCore_low_add_actualTail g
  let cr : YoshidaEvenIndex → ℝ := fun i ↦ (c i).re
  let fr : YoshidaEvenOneNinetyNineTail :=
    realifiedEvenOneNinetyNineTail f
  refine ⟨cr, fr, ?_, ?_⟩
  · simpa only [cr, fr] using
      realify_even_low_add_actualTail g hgReal c f hdecomp
  · intro x
    simp only [fr, realifiedEvenOneNinetyNineTail_apply,
      Complex.ofReal_im]

/-! ## Globally continuous representative assembly -/

/-- A canonical retained even mode bundled in the periodic source core. -/
def canonicalEvenLowModePeriodicCore (i : YoshidaEvenIndex) :
    YoshidaClippedPeriodicCore yoshidaA :=
  ⟨yoshidaClippedEvenLowMode yoshidaA i,
    yoshidaClippedEvenLowMode_mem_periodicCore yoshidaA_pos i⟩

@[simp] theorem canonicalEvenLowModePeriodicCore_toSmooth
    (i : YoshidaEvenIndex) :
    ((canonicalEvenLowModePeriodicCore i :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) =
        yoshidaClippedEvenLowMode yoshidaA i := rfl

/-- Canonical retained even modes are literally even, not merely even as
circle `L²` classes. -/
theorem canonicalEvenLowMode_pointwise_even (i : YoshidaEvenIndex) :
    Function.Even
      (((canonicalEvenLowModePeriodicCore i :
        YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) := by
  intro x
  by_cases hx : x ∈ Icc (-yoshidaA) yoshidaA
  · have hnx : -x ∈ Icc (-yoshidaA) yoshidaA := by
      constructor <;> linarith [hx.1, hx.2]
    by_cases hi : i.1 = 0
    · rw [canonicalEvenLowModePeriodicCore_toSmooth,
        yoshidaClippedEvenLowMode, if_pos hi,
        yoshidaClippedEvenZeroMode_apply_of_mem hnx,
        yoshidaClippedEvenZeroMode_apply_of_mem hx]
    · rw [canonicalEvenLowModePeriodicCore_toSmooth,
        yoshidaClippedEvenLowMode, if_neg hi,
        yoshidaClippedEvenMode_apply_of_mem yoshidaA_pos i.1 hnx,
        yoshidaClippedEvenMode_apply_of_mem yoshidaA_pos i.1 hx]
      rw [show Real.pi * (i.1 : ℝ) * -x / yoshidaA =
          -(Real.pi * (i.1 : ℝ) * x / yoshidaA) by ring,
        Real.cos_neg]
  · have hnx : -x ∉ Icc (-yoshidaA) yoshidaA := by
      intro h
      apply hx
      constructor <;> linarith [h.1, h.2]
    rw [canonicalEvenLowModePeriodicCore_toSmooth,
      yoshidaClippedSmooth_eq_zero_outside _ hnx,
      yoshidaClippedSmooth_eq_zero_outside _ hx]

/-- The standard real `Fin 200` synthesis inside the periodic core. -/
def canonicalEvenRealLowPeriodicCore
    (c : YoshidaEvenIndex → ℝ) : YoshidaClippedPeriodicCore yoshidaA :=
  ∑ i, (c i : ℂ) • canonicalEvenLowModePeriodicCore i

@[simp] theorem canonicalEvenRealLowPeriodicCore_toSmooth
    (c : YoshidaEvenIndex → ℝ) :
    ((canonicalEvenRealLowPeriodicCore c :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) =
        ∑ i, (c i : ℂ) • yoshidaClippedEvenLowMode yoshidaA i := by
  classical
  simp [canonicalEvenRealLowPeriodicCore]

/-- The standard real low synthesis as a pointwise-even source profile. -/
def canonicalEvenRealLowPointwise
    (c : YoshidaEvenIndex → ℝ) :
    yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA := by
  classical
  refine ⟨canonicalEvenRealLowPeriodicCore c, ?_⟩
  intro x
  simp only [canonicalEvenRealLowPeriodicCore_toSmooth,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (c i : ℂ) *
      yoshidaClippedEvenLowMode yoshidaA i (-x) =
    (c i : ℂ) * yoshidaClippedEvenLowMode yoshidaA i x
  have hiEven : yoshidaClippedEvenLowMode yoshidaA i (-x) =
      yoshidaClippedEvenLowMode yoshidaA i x := by
    simpa only [canonicalEvenLowModePeriodicCore_toSmooth] using
      canonicalEvenLowMode_pointwise_even i x
  rw [hiEven]

/-- A standard cutoff-`199` tail bundled only with its literal even parity. -/
def canonicalEvenTailPointwise (f : YoshidaEvenOneNinetyNineTail) :
    yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA :=
  ⟨(f : YoshidaClippedPeriodicCore yoshidaA),
    evenTail_pointwise_even yoshidaA_pos 199
      (f : YoshidaClippedPeriodicCore yoshidaA) f.property⟩

/-- The boundary-continuous representatives of the canonical low and tail
pieces add globally to the raw centered profile of an endpoint-zero total.
This is the exact assembly identity needed before polarizing the complete
phase pencil. -/
theorem exists_periodicEvenCore_real_boundaryContinuous_low_add_tail
    (g : YoshidaPeriodicEvenCore)
    (hgReal : ∀ x : ℝ,
      ((((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0)
    (hgEndpoint :
      (((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) yoshidaA = 0)) :
    ∃ c : YoshidaEvenIndex → ℝ,
      ∃ f : YoshidaEvenOneNinetyNineTail,
        let low := canonicalEvenRealLowPointwise c
        let tail := canonicalEvenTailPointwise f
        (((g : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA)) =
          (((low + tail).1 : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) ∧
        (∀ x : ℝ,
          (((tail.1 : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) x).im = 0) ∧
        boundaryContinuousEvenProfile low +
            boundaryContinuousEvenProfile tail =
          centeredRescale yoshidaA (fun x ↦
            (((g : YoshidaClippedPeriodicCore yoshidaA) :
              YoshidaClippedSmooth yoshidaA) x).re) := by
  classical
  obtain ⟨c, f, hdecomp, htailReal⟩ :=
    exists_periodicEvenCore_real_low_add_actualTail g hgReal
  let low := canonicalEvenRealLowPointwise c
  let tail := canonicalEvenTailPointwise f
  have hsum :
      (((g : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)) =
        (((low + tail).1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) := by
    simpa only [low, tail, canonicalEvenRealLowPointwise,
      canonicalEvenTailPointwise, Submodule.coe_add,
      canonicalEvenRealLowPeriodicCore_toSmooth] using hdecomp
  have htotalEndpoint :
      ((((low + tail).1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) yoshidaA = 0) := by
    rw [← hsum]
    exact hgEndpoint
  refine ⟨c, f, hsum, ?_, ?_⟩
  · simpa only [tail, canonicalEvenTailPointwise] using htailReal
  calc
    boundaryContinuousEvenProfile low +
          boundaryContinuousEvenProfile tail =
        boundaryContinuousEvenProfile (low + tail) :=
      (boundaryContinuousEvenProfile_add low tail).symm
    _ = centeredRescale yoshidaA (fun x ↦
          ((((low + tail).1 : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) x).re) :=
      boundaryContinuousEvenProfile_eq_centeredRescale_of_endpoint_eq_zero
        (low + tail) htotalEndpoint
    _ = centeredRescale yoshidaA (fun x ↦
          (((g : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) x).re) := by
      funext x
      unfold centeredRescale
      rw [← hsum]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
