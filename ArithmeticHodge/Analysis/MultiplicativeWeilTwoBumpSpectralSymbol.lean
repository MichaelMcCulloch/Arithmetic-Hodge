import ArithmeticHodge.Analysis.MultiplicativeWeilDilationMellin

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions SchwartzMap FourierTransform

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Cancellation-preserving spectral symbol for adjacent log cells

The local cross is kept as one exact Mellin-phase expression.  In particular,
the later subtraction of the two prime atoms can be analyzed without first
destroying the large cancellation between those pieces.
-/

def factorTwoMellinWeight (sigma : ℝ) : ℂ :=
  ((Real.sqrt 2 * Real.exp (-sigma * Real.log 2) : ℝ) : ℂ)

def factorTwoMellinPhase (t : ℝ) : ℂ :=
  (Real.fourierChar
    ((-Real.log 2) * (t / (2 * Real.pi))) : ℂ)

@[simp] theorem factorTwoMellinPhase_zero :
    factorTwoMellinPhase 0 = 1 := by
  simp [factorTwoMellinPhase]

@[simp] theorem factorTwoMellinWeight_zero :
    factorTwoMellinWeight 0 = ((Real.sqrt 2 : ℝ) : ℂ) := by
  simp [factorTwoMellinWeight]

@[simp] theorem factorTwoMellinWeight_half :
    factorTwoMellinWeight (1 / 2) = 1 := by
  unfold factorTwoMellinWeight
  have hsqrt : Real.sqrt 2 = Real.exp (Real.log 2 / 2) := by
    rw [← Real.exp_log (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)),
      Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hreal :
      Real.sqrt 2 * Real.exp (-(1 / 2 : ℝ) * Real.log 2) = 1 := by
    rw [hsqrt, ← Real.exp_add]
    rw [show Real.log 2 / 2 + -(1 / 2 : ℝ) * Real.log 2 = 0 by ring,
      Real.exp_zero]
  exact congrArg (fun x : ℝ ↦ (x : ℂ)) hreal

@[simp] theorem factorTwoMellinWeight_one :
    factorTwoMellinWeight 1 =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  unfold factorTwoMellinWeight
  have hsqrt : Real.sqrt 2 = Real.exp (Real.log 2 / 2) := by
    rw [← Real.exp_log (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)),
      Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hreal :
      Real.sqrt 2 * Real.exp (-(1 : ℝ) * Real.log 2) =
        (Real.sqrt 2)⁻¹ := by
    rw [hsqrt, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  exact congrArg (fun x : ℝ ↦ (x : ℂ)) hreal

theorem mellin_normalizedDilation_two_vertical
    (g : BombieriTest) (sigma t : ℝ) :
    mellin (normalizedDilation 2 (by norm_num) g : ℝ → ℂ)
        (sigma + t * Complex.I) =
      factorTwoMellinWeight sigma * factorTwoMellinPhase t *
        mellin (g : ℝ → ℂ) (sigma + t * Complex.I) := by
  exact mellin_normalizedDilation_vertical
    2 (by norm_num) g sigma t

/-- The exact local off-diagonal symbol before subtracting the prime atoms. -/
def factorTwoLocalCrossSpectralSymbol (g : BombieriTest) : ℂ :=
  starRingEnd ℂ (mellin (g : ℝ → ℂ) 1) *
      (factorTwoMellinWeight 0 * factorTwoMellinPhase 0 *
        mellin (g : ℝ → ℂ) 0) +
    starRingEnd ℂ (mellin (g : ℝ → ℂ) 0) *
      (factorTwoMellinWeight 1 * factorTwoMellinPhase 0 *
        mellin (g : ℝ → ℂ) 1) +
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ,
        bombieriLocalCriticalKernel v *
          starRingEnd ℂ
            (mellin (g : ℝ → ℂ)
              ((1 / 2 : ℝ) + v * Complex.I)) *
          (factorTwoMellinWeight (1 / 2) * factorTwoMellinPhase v *
            mellin (g : ℝ → ℂ)
              ((1 / 2 : ℝ) + v * Complex.I)))

theorem factorTwoLocalCrossSpectralSymbol_eq
    (g : BombieriTest) :
    factorTwoLocalCrossSpectralSymbol g =
      bombieriLocalCriticalForm g
        (normalizedDilation 2 (by norm_num) g) := by
  have hzero :
      mellin (normalizedDilation 2 (by norm_num) g : ℝ → ℂ) 0 =
        factorTwoMellinWeight 0 * factorTwoMellinPhase 0 *
          mellin (g : ℝ → ℂ) 0 := by
    simpa using mellin_normalizedDilation_two_vertical g 0 0
  have hone :
      mellin (normalizedDilation 2 (by norm_num) g : ℝ → ℂ) 1 =
        factorTwoMellinWeight 1 * factorTwoMellinPhase 0 *
          mellin (g : ℝ → ℂ) 1 := by
    simpa using mellin_normalizedDilation_two_vertical g 1 0
  rw [bombieriLocalCriticalForm_apply]
  unfold factorTwoLocalCrossSpectralSymbol
  unfold bombieriLocalCriticalPairing
  simp only [mellinLinearMap_apply, starRingEnd_apply]
  rw [hzero, hone]
  congr 1
  apply congrArg (fun z : ℂ ↦ (((1 / (2 * Real.pi) : ℝ) : ℂ) * z))
  apply integral_congr_ae
  filter_upwards [] with v
  unfold bombieriLocalCriticalCrossIntegrand
  simp only [mellinLinearMap_apply]
  rw [mellin_normalizedDilation_two_vertical g (1 / 2) v]

/-- The global symbol is the single spectral phase expression minus the two
structurally isolated prime atoms. -/
theorem factorTwoGlobalCrossSymbol_eq_spectral_sub_prime
    (g : BombieriTest) :
    factorTwoGlobalCrossSymbol g =
      factorTwoLocalCrossSpectralSymbol g - factorTwoPrimeCrossSymbol g := by
  unfold factorTwoGlobalCrossSymbol
  rw [factorTwoLocalCrossSpectralSymbol_eq]

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
