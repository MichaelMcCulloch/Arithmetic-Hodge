import ArithmeticHodge.Analysis.YoshidaEvenCorrectionReality
import ArithmeticHodge.Analysis.YoshidaPointwiseOddRealImag

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ComplexConjugate InnerProductSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailRealification

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaClippedCircleBridge
open YoshidaEvenCorrectionReality
open YoshidaPointwiseOddRealImag

/-!
# Realification of periodic Fourier tails

Pointwise realification is the average of a periodic core and its complex
conjugate.  Since conjugation reverses Fourier indices, it preserves the
symmetric low-frequency cutoff and hence both parity-tail submodules.
-/

/-- The periodic-core real part is the average with pointwise conjugation. -/
theorem periodicCoreRealPart_eq_half_add_conj {a : ℝ}
    (f : YoshidaClippedPeriodicCore a) :
    periodicCoreRealPart f =
      (2 : ℂ)⁻¹ • (f + periodicCoreConj f) := by
  ext x
  apply Complex.ext
  · simp [periodicCoreRealPart, periodicCoreConj]
    ring
  · simp [periodicCoreRealPart, periodicCoreConj]

/-- Taking the pointwise real part preserves an even Fourier tail. -/
theorem periodicCoreRealPart_mem_evenTail {a : ℝ} (ha : 0 < a)
    (N : ℕ) (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreEvenTailSubmodule ha N) :
    periodicCoreRealPart f ∈
      yoshidaPeriodicCoreEvenTailSubmodule ha N := by
  rw [periodicCoreRealPart_eq_half_add_conj]
  exact (yoshidaPeriodicCoreEvenTailSubmodule ha N).smul_mem _
    ((yoshidaPeriodicCoreEvenTailSubmodule ha N).add_mem hf
      (periodicCoreConj_mem_evenTail ha N f hf))

/-- The realified periodic core is pointwise real. -/
theorem periodicCoreRealPart_im_zero {a x : ℝ}
    (f : YoshidaClippedPeriodicCore a) :
    ((((periodicCoreRealPart f : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) : ℝ → ℂ) x).im = 0 := by
  simp

/-- Pointwise complex conjugation preserves circle oddness. -/
theorem star_mem_oddL2Submodule {T : ℝ} [Fact (0 < T)]
    {f : CircleL2 (T := T)}
    (hf : f ∈ oddL2Submodule (T := T)) :
    star f ∈ oddL2Submodule (T := T) := by
  rw [mem_oddL2Submodule_iff]
  have hodd := reflectionL2_ae (T := T) f
  rw [(mem_oddL2Submodule_iff f).mp hf] at hodd
  have hstarNeg :=
    (circleNegMeasurePreserving (T := T)).quasiMeasurePreserving.tendsto_ae
      (Lp.coeFn_star f)
  apply Lp.ext
  filter_upwards [
    reflectionL2_ae (T := T) (star f),
    Lp.coeFn_star f,
    hstarNeg,
    Lp.coeFn_neg f,
    Lp.coeFn_neg (star f),
    hodd] with x href hstar hstarNegX hnegX hnegStarX hoddX
  calc
    (reflectionL2 (T := T) (star f) : CircleL2 (T := T)) x =
        (star f : CircleL2 (T := T)) (-x) := href
    _ = star ((f : CircleL2 (T := T)) (-x)) := hstarNegX
    _ = star ((-f : CircleL2 (T := T)) x) :=
      congrArg star hoddX.symm
    _ = star (-((f : CircleL2 (T := T)) x)) := congrArg star hnegX
    _ = -star ((f : CircleL2 (T := T)) x) := by simp
    _ = -((star f : CircleL2 (T := T)) x) := congrArg Neg.neg hstar.symm
    _ = (-star f : CircleL2 (T := T)) x := hnegStarX.symm

/-- Conjugation preserves an actual periodic odd Fourier tail. -/
theorem periodicCoreConj_mem_oddTail {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule ha N) :
    periodicCoreConj f ∈ yoshidaPeriodicCoreOddTailSubmodule ha N := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  rw [mem_yoshidaPeriodicCoreOddTailSubmodule_iff]
  have htail :
      yoshidaClippedCircleL2 ha (f : YoshidaClippedSmooth a) ∈
        oddFourierTailSubmodule (T := 2 * a) N :=
    (mem_yoshidaPeriodicCoreOddTailSubmodule_iff ha N f).mp hf
  constructor
  · rw [show
        yoshidaClippedCircleL2 ha
            ((periodicCoreConj f : YoshidaClippedPeriodicCore a) :
              YoshidaClippedSmooth a) =
          star (yoshidaClippedCircleL2 ha
            (f : YoshidaClippedSmooth a)) by
        exact yoshidaClippedCircleL2_clippedConj ha
          (f : YoshidaClippedSmooth a)]
    exact star_mem_oddL2Submodule htail.1
  · change
      yoshidaClippedCircleL2 ha
          ((periodicCoreConj f : YoshidaClippedPeriodicCore a) :
            YoshidaClippedSmooth a) ∈
        fourierTailSubmodule (T := 2 * a) N
    rw [mem_fourierTailSubmodule_iff]
    intro n hn
    have hneg := neg_mem_lowIndex hn
    have hzero :=
      (mem_fourierTailSubmodule_iff N
        (yoshidaClippedCircleL2 ha
          (f : YoshidaClippedSmooth a))).mp htail.2 (-n) hneg
    calc
      fourierCoeff
          (yoshidaClippedCircleL2 ha
            ((periodicCoreConj f : YoshidaClippedPeriodicCore a) :
              YoshidaClippedSmooth a)) n =
          centeredFourierCoeff ha
            (((periodicCoreConj f : YoshidaClippedPeriodicCore a) :
              YoshidaClippedSmooth a) : ℝ → ℂ) n :=
        fourierCoeff_yoshidaClippedCircleL2 ha _ n
      _ = star (centeredFourierCoeff ha
          (((f : YoshidaClippedPeriodicCore a) :
            YoshidaClippedSmooth a) : ℝ → ℂ) (-n)) := by
        exact centeredFourierCoeff_conj ha _ n
      _ = star (fourierCoeff
          (yoshidaClippedCircleL2 ha
            (f : YoshidaClippedSmooth a)) (-n)) := by
        rw [fourierCoeff_yoshidaClippedCircleL2]
      _ = 0 := by simpa using congrArg star hzero

/-- Taking the pointwise real part preserves an odd Fourier tail. -/
theorem periodicCoreRealPart_mem_oddTail {a : ℝ} (ha : 0 < a)
    (N : ℕ) (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule ha N) :
    periodicCoreRealPart f ∈
      yoshidaPeriodicCoreOddTailSubmodule ha N := by
  rw [periodicCoreRealPart_eq_half_add_conj]
  exact (yoshidaPeriodicCoreOddTailSubmodule ha N).smul_mem _
    ((yoshidaPeriodicCoreOddTailSubmodule ha N).add_mem hf
      (periodicCoreConj_mem_oddTail ha N f hf))

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailRealification
