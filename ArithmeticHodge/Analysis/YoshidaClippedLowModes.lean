import ArithmeticHodge.Analysis.YoshidaClippedCriticalForm
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option autoImplicit false

open Matrix
open scoped ComplexConjugate

namespace ArithmeticHodge.Analysis

/-!
# Yoshida low modes in the clipped critical-form carrier

The Lebesgue-normalized sine and cosine modes are defined by the same
exponential combinations used by the circle `L²` model, now inside
`YoshidaClippedSmooth`.  Their critical and polar samples reduce linearly to
the exact clipped-exponential transforms, and the resulting finite local
critical-form Gram matrices are Hermitian.  No positivity claim is made.
-/

noncomputable section

/-- Yoshida's Lebesgue-normalized odd mode in the clipped smooth carrier. -/
def yoshidaClippedOddMode (a : ℝ) (n : ℕ) : YoshidaClippedSmooth a :=
  (-Complex.I / (Real.sqrt 2 : ℂ)) •
    (yoshidaClippedExponential a (n : ℤ) -
      yoshidaClippedExponential a (-(n : ℤ)))

/-- Yoshida's positive-frequency even mode in the clipped smooth carrier. -/
def yoshidaClippedEvenMode (a : ℝ) (n : ℕ) : YoshidaClippedSmooth a :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (yoshidaClippedExponential a (n : ℤ) +
      yoshidaClippedExponential a (-(n : ℤ)))

/-- Yoshida's zero-frequency even mode in the clipped smooth carrier. -/
def yoshidaClippedEvenZeroMode (a : ℝ) : YoshidaClippedSmooth a :=
  yoshidaClippedExponential a 0

def yoshidaClippedOddLowMode (a : ℝ) (i : YoshidaOddIndex) :
    YoshidaClippedSmooth a :=
  yoshidaClippedOddMode a (i.1 + 1)

def yoshidaClippedEvenLowMode (a : ℝ) (i : YoshidaEvenIndex) :
    YoshidaClippedSmooth a :=
  if i.1 = 0 then yoshidaClippedEvenZeroMode a
  else yoshidaClippedEvenMode a i.1

theorem yoshidaCriticalSample_clippedOddMode
    {a : ℝ} (ha : 0 < a) (v : ℝ) (n : ℕ) :
    yoshidaCriticalSampleLinear a ha v (yoshidaClippedOddMode a n) =
      (-Complex.I / (Real.sqrt 2 : ℂ)) *
        (yoshidaCriticalSampleLinear a ha v
            (yoshidaClippedExponential a (n : ℤ)) -
          yoshidaCriticalSampleLinear a ha v
            (yoshidaClippedExponential a (-(n : ℤ)))) := by
  simp [yoshidaClippedOddMode, map_sub, smul_eq_mul]

theorem yoshidaCriticalSample_clippedEvenMode
    {a : ℝ} (ha : 0 < a) (v : ℝ) (n : ℕ) :
    yoshidaCriticalSampleLinear a ha v (yoshidaClippedEvenMode a n) =
      ((Real.sqrt 2 : ℂ)⁻¹) *
        (yoshidaCriticalSampleLinear a ha v
            (yoshidaClippedExponential a (n : ℤ)) +
          yoshidaCriticalSampleLinear a ha v
            (yoshidaClippedExponential a (-(n : ℤ)))) := by
  simp [yoshidaClippedEvenMode, map_add, smul_eq_mul]
  ring

theorem yoshidaPositivePolar_clippedOddMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    yoshidaPositivePolarLinear a ha (yoshidaClippedOddMode a n) =
      (-Complex.I / (Real.sqrt 2 : ℂ)) *
        (yoshidaPositivePolarLinear a ha
            (yoshidaClippedExponential a (n : ℤ)) -
          yoshidaPositivePolarLinear a ha
            (yoshidaClippedExponential a (-(n : ℤ)))) := by
  simp [yoshidaClippedOddMode, map_sub, smul_eq_mul]

theorem yoshidaNegativePolar_clippedOddMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    yoshidaNegativePolarLinear a ha (yoshidaClippedOddMode a n) =
      (-Complex.I / (Real.sqrt 2 : ℂ)) *
        (yoshidaNegativePolarLinear a ha
            (yoshidaClippedExponential a (n : ℤ)) -
          yoshidaNegativePolarLinear a ha
            (yoshidaClippedExponential a (-(n : ℤ)))) := by
  simp [yoshidaClippedOddMode, map_sub, smul_eq_mul]

theorem yoshidaPositivePolar_clippedEvenMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    yoshidaPositivePolarLinear a ha (yoshidaClippedEvenMode a n) =
      ((Real.sqrt 2 : ℂ)⁻¹) *
        (yoshidaPositivePolarLinear a ha
            (yoshidaClippedExponential a (n : ℤ)) +
          yoshidaPositivePolarLinear a ha
            (yoshidaClippedExponential a (-(n : ℤ)))) := by
  simp [yoshidaClippedEvenMode, map_add, smul_eq_mul]
  ring

theorem yoshidaNegativePolar_clippedEvenMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    yoshidaNegativePolarLinear a ha (yoshidaClippedEvenMode a n) =
      ((Real.sqrt 2 : ℂ)⁻¹) *
        (yoshidaNegativePolarLinear a ha
            (yoshidaClippedExponential a (n : ℤ)) +
          yoshidaNegativePolarLinear a ha
            (yoshidaClippedExponential a (-(n : ℤ)))) := by
  simp [yoshidaClippedEvenMode, map_add, smul_eq_mul]
  ring

def yoshidaClippedOddGram (a : ℝ) (ha : 0 < a) :
    Matrix YoshidaOddIndex YoshidaOddIndex ℂ :=
  fun i j ↦ yoshidaClippedLocalCriticalForm a ha
    (yoshidaClippedOddLowMode a i) (yoshidaClippedOddLowMode a j)

def yoshidaClippedEvenGram (a : ℝ) (ha : 0 < a) :
    Matrix YoshidaEvenIndex YoshidaEvenIndex ℂ :=
  fun i j ↦ yoshidaClippedLocalCriticalForm a ha
    (yoshidaClippedEvenLowMode a i) (yoshidaClippedEvenLowMode a j)

theorem yoshidaClippedOddGram_isHermitian (a : ℝ) (ha : 0 < a) :
    (yoshidaClippedOddGram a ha).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  exact yoshidaClippedLocalCriticalForm_conj_apply ha
    (yoshidaClippedOddLowMode a i) (yoshidaClippedOddLowMode a j)

theorem yoshidaClippedEvenGram_isHermitian (a : ℝ) (ha : 0 < a) :
    (yoshidaClippedEvenGram a ha).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  exact yoshidaClippedLocalCriticalForm_conj_apply ha
    (yoshidaClippedEvenLowMode a i) (yoshidaClippedEvenLowMode a j)

end

end ArithmeticHodge.Analysis
