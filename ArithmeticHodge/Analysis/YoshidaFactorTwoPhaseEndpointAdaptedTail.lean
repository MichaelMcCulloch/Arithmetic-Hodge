import ArithmeticHodge.Analysis.YoshidaEvenTailLowFunctional
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDirectionalTail
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile
import ArithmeticHodge.Analysis.YoshidaParityRecombination

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedTail

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaClippedEvenMomentBridge
open YoshidaCoercivityNumerics
open YoshidaEvenHomogeneousCoercivity
open YoshidaEvenTailLowFunctional
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseDirectionalTail
open YoshidaFactorTwoPhaseFullProfile
open YoshidaOddSpectralMassBridge
open YoshidaParityRecombination
open YoshidaWeightedTailBounds

/-!
# Endpoint-adapted Fourier tails

The phase-tail theorem requires zero endpoint trace.  An odd periodic tail
has that trace automatically.  An even Fourier tail generally does not, but
one copy of its first allowed cosine mode (frequency `200`) removes it without
leaving the cutoff-`199` tail submodule.  Moving that mode into the finite
piece gives a direct `201`-mode split; an endpoint-adapted change of basis in
the original low block can instead preserve its dimension `200`.
-/

/-- The real coefficient of the frequency-`200` cosine needed to cancel the
positive endpoint of a real even tail. -/
def evenTailEndpointCoefficient
    (r : YoshidaClippedPeriodicCore yoshidaA) : ℝ :=
  Real.sqrt yoshidaA *
    ((r : YoshidaClippedSmooth yoshidaA) yoshidaA).re

/-- Remove the endpoint trace using the first mode which is still contained
in the cutoff-`199` even tail. -/
def endpointAdaptedEvenTail
    (r : YoshidaClippedPeriodicCore yoshidaA) :
    YoshidaClippedPeriodicCore yoshidaA :=
  r - (evenTailEndpointCoefficient r : ℂ) • evenHighModePeriodicCore 0

/-- Frequency `200` has value `1 / sqrt A` at the positive endpoint. -/
theorem evenHighModePeriodicCore_zero_apply_pos :
    (((evenHighModePeriodicCore 0 :
          YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) yoshidaA) =
      ((Real.sqrt yoshidaA)⁻¹ : ℝ) := by
  change yoshidaClippedEvenMode yoshidaA 200 yoshidaA = _
  rw [yoshidaClippedEvenMode_apply_of_mem yoshidaA_pos 200
    ⟨by linarith [yoshidaA_pos], le_rfl⟩]
  have harg : Real.pi * (200 : ℝ) * yoshidaA / yoshidaA =
      (200 : ℝ) * Real.pi := by
    field_simp [yoshidaA_pos.ne']
  rw [show Real.pi * ((200 : ℕ) : ℝ) * yoshidaA / yoshidaA =
      (200 : ℝ) * Real.pi by simpa using harg]
  have hcos : Real.cos ((200 : ℝ) * Real.pi) = 1 := by
    rw [show (200 : ℝ) * Real.pi =
      (100 : ℝ) * (2 * Real.pi) by ring]
    simpa using Real.cos_nat_mul_two_pi 100
  rw [hcos]
  norm_num

/-- The corrected vector remains in the same Fourier tail submodule. -/
theorem endpointAdaptedEvenTail_mem_tail
    (r : YoshidaClippedPeriodicCore yoshidaA)
    (hr : r ∈ yoshidaPeriodicCoreEvenTailSubmodule
      yoshidaA_pos 199) :
    endpointAdaptedEvenTail r ∈
      yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199 := by
  unfold endpointAdaptedEvenTail
  let S : Submodule ℂ (YoshidaClippedPeriodicCore yoshidaA) :=
    yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199
  change r - (evenTailEndpointCoefficient r : ℂ) •
    evenHighModePeriodicCore 0 ∈ S
  have hmode : (evenTailEndpointCoefficient r : ℂ) •
      evenHighModePeriodicCore 0 ∈ S :=
    S.smul_mem (evenTailEndpointCoefficient r : ℂ)
      (evenHighModePeriodicCore_mem_tail 0)
  change r ∈ S at hr
  let rS : S := ⟨r, hr⟩
  let modeS : S :=
    ⟨(evenTailEndpointCoefficient r : ℂ) • evenHighModePeriodicCore 0,
      hmode⟩
  have hsub : (((rS - modeS : S) :
      YoshidaClippedPeriodicCore yoshidaA)) ∈ S := (rS - modeS).property
  change r - (evenTailEndpointCoefficient r : ℂ) •
    evenHighModePeriodicCore 0 ∈ S at hsub
  exact hsub

/-- For a real tail, the corrected positive endpoint is exactly zero. -/
theorem endpointAdaptedEvenTail_apply_pos
    (r : YoshidaClippedPeriodicCore yoshidaA)
    (hrReal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaA) x).im = 0) :
    ((endpointAdaptedEvenTail r :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
  have hrEq :
      ((r : YoshidaClippedSmooth yoshidaA) yoshidaA) =
        ((((r : YoshidaClippedSmooth yoshidaA)
          yoshidaA).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hrReal yoshidaA
  change ((r : YoshidaClippedSmooth yoshidaA) yoshidaA) -
      (evenTailEndpointCoefficient r : ℂ) *
        (((evenHighModePeriodicCore 0 :
            YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) yoshidaA) = 0
  rw [hrEq, evenHighModePeriodicCore_zero_apply_pos]
  unfold evenTailEndpointCoefficient
  push_cast
  have hsqrt : Real.sqrt yoshidaA ≠ 0 :=
    (Real.sqrt_pos.2 yoshidaA_pos).ne'
  field_simp [hsqrt]
  ring

/-- The corrected negative endpoint vanishes by evenness of the retained
tail submodule. -/
theorem endpointAdaptedEvenTail_apply_neg
    (r : YoshidaClippedPeriodicCore yoshidaA)
    (hr : r ∈ yoshidaPeriodicCoreEvenTailSubmodule
      yoshidaA_pos 199)
    (hrReal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaA) x).im = 0) :
    ((endpointAdaptedEvenTail r :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0 := by
  have htail := endpointAdaptedEvenTail_mem_tail r hr
  have heven := evenTail_pointwise_even yoshidaA_pos 199
    (endpointAdaptedEvenTail r) htail yoshidaA
  rw [endpointAdaptedEvenTail_apply_pos r hrReal] at heven
  exact heven

/-- The frequency-`200` correction is pointwise real. -/
theorem evenHighModePeriodicCore_zero_im (x : ℝ) :
    ((((evenHighModePeriodicCore 0 :
          YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0 := by
  by_cases hx : x ∈ Set.Icc (-yoshidaA) yoshidaA
  · change (yoshidaClippedEvenMode yoshidaA 200 x).im = 0
    rw [yoshidaClippedEvenMode_apply_of_mem yoshidaA_pos 200 hx]
    exact Complex.ofReal_im _
  · have hzero := yoshidaClippedSmooth_eq_zero_outside
      (((evenHighModePeriodicCore 0 :
          YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA)) hx
    rw [hzero]
    simp

/-- Subtracting the endpoint correction preserves pointwise reality. -/
theorem endpointAdaptedEvenTail_real
    (r : YoshidaClippedPeriodicCore yoshidaA)
    (hrReal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (x : ℝ) :
    ((((endpointAdaptedEvenTail r :
          YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im) = 0 := by
  change (((r : YoshidaClippedSmooth yoshidaA) x) -
    (evenTailEndpointCoefficient r : ℂ) *
      (((evenHighModePeriodicCore 0 :
          YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x)).im = 0
  rw [Complex.sub_im, Complex.mul_im, hrReal x,
    evenHighModePeriodicCore_zero_im x]
  simp

/-- Exact endpoint-adapted decomposition of an even tail.  In the direct
correction, the first summand is moved into the finite-low block. -/
theorem evenTail_eq_endpointMode_add_endpointAdapted
    (r : YoshidaClippedPeriodicCore yoshidaA) :
    r = (evenTailEndpointCoefficient r : ℂ) •
          evenHighModePeriodicCore 0 + endpointAdaptedEvenTail r := by
  unfold endpointAdaptedEvenTail
  abel

/-- An already endpoint-zero even tail is fixed by the correction. -/
theorem endpointAdaptedEvenTail_eq_self_of_apply_pos_eq_zero
    (r : YoshidaClippedPeriodicCore yoshidaA)
    (hr : (r : YoshidaClippedSmooth yoshidaA) yoshidaA = 0) :
    endpointAdaptedEvenTail r = r := by
  unfold endpointAdaptedEvenTail evenTailEndpointCoefficient
  rw [hr]
  rw [Complex.zero_re, mul_zero]
  change r - (0 : ℂ) • evenHighModePeriodicCore 0 = r
  rw [zero_smul]
  exact sub_zero r

/-- Every periodic odd Fourier tail has zero trace at both endpoints. -/
theorem oddTail_endpoints_zero
    (r : YoshidaClippedPeriodicCore yoshidaA)
    (hr : r ∈ yoshidaPeriodicCoreOddTailSubmodule
      yoshidaA_pos 10) :
    ((r : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0) ∧
      ((r : YoshidaClippedSmooth yoshidaA) yoshidaA = 0) := by
  have hodd : (r : YoshidaClippedSmooth yoshidaA)
        (-yoshidaA) =
      -(r : YoshidaClippedSmooth yoshidaA) yoshidaA :=
    oddTail_pointwise_odd yoshidaA_pos 10 r hr yoshidaA
  have hperiod := periodicCore_endpoint_eq yoshidaA_pos r
  have hpos : (r : YoshidaClippedSmooth yoshidaA)
      yoshidaA = 0 := by
    have htwo : (2 : ℂ) *
        (r : YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
      calc
        (2 : ℂ) *
            (r : YoshidaClippedSmooth yoshidaA) yoshidaA =
          (r : YoshidaClippedSmooth yoshidaA) yoshidaA -
            (-(r : YoshidaClippedSmooth yoshidaA)
              yoshidaA) := by ring
        _ = 0 := by rw [← hodd, hperiod]; ring
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact ⟨by rw [hperiod, hpos], hpos⟩

/-- The endpoint correction discharges every trace hypothesis of the
directional tail theorem.  Thus any pointwise-real even/odd Fourier tails can
be placed in its phase-uniform nonnegative form after correcting the even
endpoint with frequency `200`. -/
theorem endpointAdapted_tail_phase_uniform
    (re ro : YoshidaClippedPeriodicCore yoshidaA)
    (heTail : re ∈ yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199)
    (hoTail : ro ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10)
    (heReal : ∀ x : ℝ,
      ((re : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoReal : ∀ x : ℝ,
      ((ro : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let e := centeredRescale yoshidaA (fun x ↦
      (((endpointAdaptedEvenTail re :
          YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).re)
    let o := centeredRescale yoshidaA (fun x ↦
      ((ro : YoshidaClippedSmooth yoshidaA) x).re)
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  have heTail0 := endpointAdaptedEvenTail_mem_tail re heTail
  have heReal0 := endpointAdaptedEvenTail_real re heReal
  have heNeg0 := endpointAdaptedEvenTail_apply_neg re heTail heReal
  have hePos0 := endpointAdaptedEvenTail_apply_pos re heReal
  obtain ⟨hoNeg0, hoPos0⟩ := oddTail_endpoints_zero ro hoTail
  have h := endpoint_tail_phase_uniform
    (re := endpointAdaptedEvenTail re) (ro := ro)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using heTail0)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hoTail)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using heReal0)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hoReal)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using heNeg0)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hePos0)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hoNeg0)
    (by simpa only [YoshidaWeightedTailBounds.yoshidaA,
        YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using hoPos0)
    a b hphase
  simpa only [factorTwoEndpointChannelPhase,
    factorTwoEndpointChannelCleanSum, factorTwoEndpointChannelSymmetricSum,
    YoshidaWeightedTailBounds.yoshidaA,
    YoshidaEndpointHyperbolicBound.yoshidaEndpointA] using h

/-- Swapping the even/odd arguments reverses only the alternating phase
coordinate.  Consequently one disk-uniform channel theorem handles the
opposite channel as well. -/
theorem factorTwoEndpointChannelPhase_swap
    (u v : ℝ → ℝ) (a b : ℝ) :
    factorTwoEndpointChannelPhase v u a b =
      factorTwoEndpointChannelPhase u v a (-b) := by
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
  rw [factorTwoCenteredAlternatingCoupling_comm]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedTail
