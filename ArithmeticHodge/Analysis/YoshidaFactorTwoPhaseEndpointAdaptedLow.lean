import ArithmeticHodge.Analysis.YoshidaEvenTailLowFunctional
import ArithmeticHodge.Analysis.YoshidaParityRecombination

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedLow

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaClippedEvenMomentBridge
open YoshidaCoercivityNumerics
open YoshidaEvenTailLowFunctional
open YoshidaParityRecombination
open YoshidaWeightedTailBounds

/-!
# Endpoint-adapted finite even modes

The canonical even low block has `200` coordinates: the zero mode and
frequencies `1, ..., 199`.  Subtracting the appropriate multiple of frequency
`200` from each coordinate makes every retained basis vector vanish at both
identified endpoints while preserving the `Fin 200` indexing.
-/

/-- The endpoint trace of a canonical low mode, measured in units of the
positive endpoint trace of frequency `200`. -/
def endpointEvenLowTraceRatio (i : YoshidaEvenIndex) : ℝ :=
  if i.1 = 0 then (Real.sqrt 2)⁻¹ else (-1 : ℝ) ^ i.1

/-- The dimension-preserving endpoint-adapted version of a canonical even
low mode. -/
def endpointAdaptedEvenLowMode (i : YoshidaEvenIndex) :
    YoshidaClippedSmooth yoshidaA :=
  yoshidaClippedEvenLowMode yoshidaA i -
    (endpointEvenLowTraceRatio i : ℂ) •
      yoshidaClippedEvenMode yoshidaA 200

/-- Frequency `200` has positive-endpoint trace `1 / sqrt A`. -/
theorem evenModeTwoHundred_endpoint :
    yoshidaClippedEvenMode yoshidaA 200 yoshidaA =
      ((Real.sqrt yoshidaA)⁻¹ : ℂ) := by
  rw [yoshidaClippedEvenMode_apply_of_mem yoshidaA_pos 200
    ⟨by linarith [yoshidaA_pos], le_rfl⟩]
  have harg : Real.pi * (200 : ℝ) * yoshidaA / yoshidaA =
      (200 : ℝ) * Real.pi := by
    field_simp [yoshidaA_pos.ne']
  norm_cast
  rw [harg]
  have hcos : Real.cos ((200 : ℝ) * Real.pi) = 1 := by
    rw [show (200 : ℝ) * Real.pi =
      (100 : ℝ) * (2 * Real.pi) by ring]
    simpa using Real.cos_nat_mul_two_pi 100
  rw [hcos]
  ring

/-- Exact positive-endpoint trace of every canonical even low mode. -/
theorem evenLowMode_endpoint (i : YoshidaEvenIndex) :
    yoshidaClippedEvenLowMode yoshidaA i yoshidaA =
      (((endpointEvenLowTraceRatio i *
        (Real.sqrt yoshidaA)⁻¹ : ℝ)) : ℂ) := by
  by_cases hi : i.1 = 0
  · rw [yoshidaClippedEvenLowMode, if_pos hi,
      yoshidaClippedEvenZeroMode_apply_of_mem
        (show yoshidaA ∈ Set.Icc (-yoshidaA) yoshidaA by
          constructor <;> linarith [yoshidaA_pos]),
      endpointEvenLowTraceRatio, if_pos hi]
    have hsqrt : Real.sqrt (2 * yoshidaA) =
        Real.sqrt 2 * Real.sqrt yoshidaA := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hsqrt]
    push_cast
    field_simp [show Real.sqrt 2 ≠ 0 by positivity,
      (Real.sqrt_pos.2 yoshidaA_pos).ne']
  · rw [yoshidaClippedEvenLowMode, if_neg hi,
      yoshidaClippedEvenMode_apply_of_mem yoshidaA_pos i.1
        (show yoshidaA ∈ Set.Icc (-yoshidaA) yoshidaA by
          constructor <;> linarith [yoshidaA_pos]),
      endpointEvenLowTraceRatio, if_neg hi]
    have harg : Real.pi * (i.1 : ℝ) * yoshidaA / yoshidaA =
        (i.1 : ℝ) * Real.pi := by
      field_simp [yoshidaA_pos.ne']
    rw [harg, Real.cos_nat_mul_pi]
    push_cast
    ring

/-- Every endpoint-adapted low mode vanishes at the positive endpoint. -/
theorem endpointAdaptedEvenLowMode_apply_pos (i : YoshidaEvenIndex) :
    endpointAdaptedEvenLowMode i yoshidaA = 0 := by
  change yoshidaClippedEvenLowMode yoshidaA i yoshidaA -
      (endpointEvenLowTraceRatio i : ℂ) *
        yoshidaClippedEvenMode yoshidaA 200 yoshidaA = 0
  rw [evenLowMode_endpoint,
    show yoshidaClippedEvenMode yoshidaA 200 yoshidaA =
        ((Real.sqrt yoshidaA)⁻¹ : ℂ) by
      exact evenModeTwoHundred_endpoint]
  push_cast
  ring

/-- The endpoint-adapted mode, bundled in the periodic source core. -/
def endpointAdaptedEvenLowModePeriodicCore (i : YoshidaEvenIndex) :
    YoshidaClippedPeriodicCore yoshidaA :=
  ⟨endpointAdaptedEvenLowMode i, by
    unfold endpointAdaptedEvenLowMode
    exact (yoshidaClippedPeriodicCoreSubmodule yoshidaA).sub_mem
      (yoshidaClippedEvenLowMode_mem_periodicCore yoshidaA_pos i)
      ((yoshidaClippedPeriodicCoreSubmodule yoshidaA).smul_mem
        (endpointEvenLowTraceRatio i : ℂ)
        (yoshidaClippedEvenMode_mem_periodicCore yoshidaA_pos 200))⟩

@[simp] theorem endpointAdaptedEvenLowModePeriodicCore_toSmooth
    (i : YoshidaEvenIndex) :
    ((endpointAdaptedEvenLowModePeriodicCore i :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) = endpointAdaptedEvenLowMode i :=
  rfl

/-- Periodicity transports the positive endpoint cancellation to the
negative endpoint. -/
theorem endpointAdaptedEvenLowMode_apply_neg (i : YoshidaEvenIndex) :
    endpointAdaptedEvenLowMode i (-yoshidaA) = 0 := by
  have hperiod := periodicCore_endpoint_eq yoshidaA_pos
    (endpointAdaptedEvenLowModePeriodicCore i)
  change endpointAdaptedEvenLowMode i (-yoshidaA) =
      endpointAdaptedEvenLowMode i yoshidaA at hperiod
  rw [endpointAdaptedEvenLowMode_apply_pos] at hperiod
  exact hperiod

/-- Both endpoint traces vanish exactly for every adapted low coordinate. -/
theorem endpointAdaptedEvenLowMode_endpoints_zero (i : YoshidaEvenIndex) :
    endpointAdaptedEvenLowMode i (-yoshidaA) = 0 ∧
      endpointAdaptedEvenLowMode i yoshidaA = 0 :=
  ⟨endpointAdaptedEvenLowMode_apply_neg i,
    endpointAdaptedEvenLowMode_apply_pos i⟩

/-- Every canonical even low mode is pointwise real. -/
theorem evenLowMode_im_zero (i : YoshidaEvenIndex) (x : ℝ) :
    (yoshidaClippedEvenLowMode yoshidaA i x).im = 0 := by
  by_cases hx : x ∈ Set.Icc (-yoshidaA) yoshidaA
  · by_cases hi : i.1 = 0
    · rw [yoshidaClippedEvenLowMode, if_pos hi,
        yoshidaClippedEvenZeroMode_apply_of_mem hx]
      exact Complex.ofReal_im _
    · rw [yoshidaClippedEvenLowMode, if_neg hi,
        yoshidaClippedEvenMode_apply_of_mem yoshidaA_pos i.1 hx]
      exact Complex.ofReal_im _
  · rw [yoshidaClippedSmooth_eq_zero_outside
      (yoshidaClippedEvenLowMode yoshidaA i) hx]
    exact Complex.zero_im

/-- Every positive-frequency canonical even mode is pointwise real. -/
theorem evenMode_im_zero (n : ℕ) (x : ℝ) :
    (yoshidaClippedEvenMode yoshidaA n x).im = 0 := by
  by_cases hx : x ∈ Set.Icc (-yoshidaA) yoshidaA
  · rw [yoshidaClippedEvenMode_apply_of_mem yoshidaA_pos n hx]
    exact Complex.ofReal_im _
  · rw [yoshidaClippedSmooth_eq_zero_outside
      (yoshidaClippedEvenMode yoshidaA n) hx]
    exact Complex.zero_im

/-- The endpoint-adapted low basis remains pointwise real. -/
theorem endpointAdaptedEvenLowMode_im_zero
    (i : YoshidaEvenIndex) (x : ℝ) :
    (endpointAdaptedEvenLowMode i x).im = 0 := by
  change (yoshidaClippedEvenLowMode yoshidaA i x -
    (endpointEvenLowTraceRatio i : ℂ) *
      yoshidaClippedEvenMode yoshidaA 200 x).im = 0
  rw [Complex.sub_im, Complex.mul_im, evenLowMode_im_zero,
    evenMode_im_zero]
  simp

/-- The original low mode is recovered by adding back its endpoint-trace
multiple of frequency `200`. -/
theorem evenLowMode_eq_endpointMode_add_endpointAdapted
    (i : YoshidaEvenIndex) :
    yoshidaClippedEvenLowMode yoshidaA i =
      (endpointEvenLowTraceRatio i : ℂ) •
          yoshidaClippedEvenMode yoshidaA 200 +
        endpointAdaptedEvenLowMode i := by
  unfold endpointAdaptedEvenLowMode
  abel

/-- The shared correction direction is the first member of the cutoff-`199`
even tail. -/
theorem endpointEvenCorrectionMode_mem_tail :
    evenHighModePeriodicCore 0 ∈
      yoshidaPeriodicCoreEvenTailSubmodule yoshidaA_pos 199 :=
  evenHighModePeriodicCore_mem_tail 0

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedLow
