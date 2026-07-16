import ArithmeticHodge.Analysis.YoshidaClippedRealImagEnergySplit
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailRealification
import ArithmeticHodge.Analysis.YoshidaOddInfiniteSchur

set_option autoImplicit false

open Complex
open scoped InnerProductSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailRealImagStructural

noncomputable section

open ArithmeticHodge.Analysis
open FormSpace
open YoshidaClippedRealImagEnergySplit
open YoshidaCoercivityNumerics
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoPhaseTailRealification
open YoshidaOddHomogeneousCoercivity
open YoshidaPointwiseOddRealImag
open YoshidaWeightedTailBounds

/-!
# Real and imaginary coordinates of the canonical Fourier tails

The phase pencil is a real bilinear form.  To extend it on the full complex
critical-form completion, split every algebraic tail into pointwise-real and
pointwise-imaginary tails.  Both projections preserve the exact Fourier
cutoff, and the critical norm is the orthogonal sum of their two real norms.
-/

/-- Taking the pointwise imaginary coefficient preserves an even Fourier
tail. -/
theorem periodicCoreImagPart_mem_evenTail
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreEvenTailSubmodule ha N) :
    periodicCoreImagPart f ∈
      yoshidaPeriodicCoreEvenTailSubmodule ha N := by
  have hident : periodicCoreImagPart f =
      periodicCoreRealPart ((-Complex.I) • f) := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    apply Complex.ext <;>
      simp [periodicCoreImagPart_apply, periodicCoreRealPart_apply]
  rw [hident]
  exact periodicCoreRealPart_mem_evenTail ha N ((-Complex.I) • f)
    ((yoshidaPeriodicCoreEvenTailSubmodule ha N).smul_mem _ hf)

/-- Taking the pointwise imaginary coefficient preserves an odd Fourier
tail. -/
theorem periodicCoreImagPart_mem_oddTail
    {a : ℝ} (ha : 0 < a) (N : ℕ)
    (f : YoshidaClippedPeriodicCore a)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule ha N) :
    periodicCoreImagPart f ∈
      yoshidaPeriodicCoreOddTailSubmodule ha N := by
  have hident : periodicCoreImagPart f =
      periodicCoreRealPart ((-Complex.I) • f) := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    apply Complex.ext <;>
      simp [periodicCoreImagPart_apply, periodicCoreRealPart_apply]
  rw [hident]
  exact periodicCoreRealPart_mem_oddTail ha N ((-Complex.I) • f)
    ((yoshidaPeriodicCoreOddTailSubmodule ha N).smul_mem _ hf)

/-- Real coefficient of an algebraic cutoff-`199` even tail. -/
def evenTailRealPart (f : YoshidaEvenOneNinetyNineTail) :
    YoshidaEvenOneNinetyNineTail :=
  ⟨periodicCoreRealPart
      (f : YoshidaClippedPeriodicCore yoshidaA),
    periodicCoreRealPart_mem_evenTail yoshidaA_pos 199
      (f : YoshidaClippedPeriodicCore yoshidaA) f.property⟩

/-- Imaginary coefficient of an algebraic cutoff-`199` even tail. -/
def evenTailImagPart (f : YoshidaEvenOneNinetyNineTail) :
    YoshidaEvenOneNinetyNineTail :=
  ⟨periodicCoreImagPart
      (f : YoshidaClippedPeriodicCore yoshidaA),
    periodicCoreImagPart_mem_evenTail yoshidaA_pos 199
      (f : YoshidaClippedPeriodicCore yoshidaA) f.property⟩

/-- Real coefficient of an algebraic cutoff-`10` odd tail. -/
def oddTailRealPart (f : YoshidaOddTenTail) : YoshidaOddTenTail :=
  ⟨periodicCoreRealPart
      (f : YoshidaClippedPeriodicCore yoshidaA),
    periodicCoreRealPart_mem_oddTail yoshidaA_pos 10
      (f : YoshidaClippedPeriodicCore yoshidaA) f.property⟩

/-- Imaginary coefficient of an algebraic cutoff-`10` odd tail. -/
def oddTailImagPart (f : YoshidaOddTenTail) : YoshidaOddTenTail :=
  ⟨periodicCoreImagPart
      (f : YoshidaClippedPeriodicCore yoshidaA),
    periodicCoreImagPart_mem_oddTail yoshidaA_pos 10
      (f : YoshidaClippedPeriodicCore yoshidaA) f.property⟩

@[simp] theorem evenTailRealPart_apply
    (f : YoshidaEvenOneNinetyNineTail) (x : ℝ) :
    evenOneNinetyNineTailToClippedSmooth (evenTailRealPart f) x =
      (((evenOneNinetyNineTailToClippedSmooth f x).re : ℝ) : ℂ) := rfl

@[simp] theorem evenTailImagPart_apply
    (f : YoshidaEvenOneNinetyNineTail) (x : ℝ) :
    evenOneNinetyNineTailToClippedSmooth (evenTailImagPart f) x =
      (((evenOneNinetyNineTailToClippedSmooth f x).im : ℝ) : ℂ) := rfl

@[simp] theorem oddTailRealPart_apply
    (f : YoshidaOddTenTail) (x : ℝ) :
    oddTenTailToClippedSmooth (oddTailRealPart f) x =
      (((oddTenTailToClippedSmooth f x).re : ℝ) : ℂ) := rfl

@[simp] theorem oddTailImagPart_apply
    (f : YoshidaOddTenTail) (x : ℝ) :
    oddTenTailToClippedSmooth (oddTailImagPart f) x =
      (((oddTenTailToClippedSmooth f x).im : ℝ) : ℂ) := rfl

theorem evenTailCriticalForm_re_eq_real_add_imag
    (f : YoshidaEvenOneNinetyNineTail) :
    (evenOneNinetyNineTailCriticalForm f f).re =
      (evenOneNinetyNineTailCriticalForm
        (evenTailRealPart f) (evenTailRealPart f)).re +
      (evenOneNinetyNineTailCriticalForm
        (evenTailImagPart f) (evenTailImagPart f)).re := by
  simpa [evenOneNinetyNineTailCriticalForm_apply,
    evenTailRealPart, evenTailImagPart] using
      yoshidaClippedLocalCriticalForm_real_add_imag_re yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f)

theorem oddTailCriticalForm_re_eq_real_add_imag
    (f : YoshidaOddTenTail) :
    (oddTenTailCriticalForm f f).re =
      (oddTenTailCriticalForm
        (oddTailRealPart f) (oddTailRealPart f)).re +
      (oddTenTailCriticalForm
        (oddTailImagPart f) (oddTailImagPart f)).re := by
  simpa [oddTenTailCriticalForm_apply,
    oddTailRealPart, oddTailImagPart] using
      yoshidaClippedLocalCriticalForm_real_add_imag_re yoshidaA_pos
        (oddTenTailToClippedSmooth f)

/-- Pythagorean critical-norm splitting on the algebraic even form space. -/
theorem evenFormSpace_norm_sq_eq_real_add_imag
    (x : FormSpace evenOneNinetyNineTailPositiveHermitianForm) :
    ‖x‖ ^ 2 =
      ‖(FormSpace.of (evenTailRealPart x.toV) :
        FormSpace evenOneNinetyNineTailPositiveHermitianForm)‖ ^ 2 +
      ‖(FormSpace.of (evenTailImagPart x.toV) :
        FormSpace evenOneNinetyNineTailPositiveHermitianForm)‖ ^ 2 := by
  rw [FormSpace.norm_sq_eq_form_re,
    FormSpace.norm_sq_eq_form_re, FormSpace.norm_sq_eq_form_re]
  exact evenTailCriticalForm_re_eq_real_add_imag x.toV

/-- Pythagorean critical-norm splitting on the algebraic odd form space. -/
theorem oddFormSpace_norm_sq_eq_real_add_imag
    (x : FormSpace oddTenTailPositiveHermitianForm) :
    ‖x‖ ^ 2 =
      ‖(FormSpace.of (oddTailRealPart x.toV) :
        FormSpace oddTenTailPositiveHermitianForm)‖ ^ 2 +
      ‖(FormSpace.of (oddTailImagPart x.toV) :
        FormSpace oddTenTailPositiveHermitianForm)‖ ^ 2 := by
  rw [FormSpace.norm_sq_eq_form_re,
    FormSpace.norm_sq_eq_form_re, FormSpace.norm_sq_eq_form_re]
  exact oddTailCriticalForm_re_eq_real_add_imag x.toV

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailRealImagStructural
