import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailRealImagLinearStructural

noncomputable section

open ArithmeticHodge.Analysis
open FormSpace
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseTailRealImagStructural
open YoshidaOddHomogeneousCoercivity
open YoshidaPointwiseOddRealImag

/-!
# Real linearity of canonical tail coordinate projections

The pointwise real and imaginary coefficient maps are real-linear on each
algebraic critical-form space.  These bundled maps are the coordinate inputs
for the complete real bilinear phase form on the complex tail carrier.
-/

private theorem formSpace_eq_of_toV_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {q : PositiveHermitianForm V} {x y : FormSpace q}
    (h : x.toV = y.toV) : x = y := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  cases h
  rfl

@[simp] theorem evenTailRealPart_add
    (f g : YoshidaEvenOneNinetyNineTail) :
    evenTailRealPart (f + g) = evenTailRealPart f + evenTailRealPart g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change (((((evenOneNinetyNineTailToClippedSmooth (f + g) x).re :
      ℝ) : ℂ))) =
    ((((evenOneNinetyNineTailToClippedSmooth f x).re : ℝ) : ℂ)) +
      ((((evenOneNinetyNineTailToClippedSmooth g x).re : ℝ) : ℂ))
  simp

@[simp] theorem evenTailImagPart_add
    (f g : YoshidaEvenOneNinetyNineTail) :
    evenTailImagPart (f + g) = evenTailImagPart f + evenTailImagPart g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change (((((evenOneNinetyNineTailToClippedSmooth (f + g) x).im :
      ℝ) : ℂ))) =
    ((((evenOneNinetyNineTailToClippedSmooth f x).im : ℝ) : ℂ)) +
      ((((evenOneNinetyNineTailToClippedSmooth g x).im : ℝ) : ℂ))
  simp

@[simp] theorem oddTailRealPart_add (f g : YoshidaOddTenTail) :
    oddTailRealPart (f + g) = oddTailRealPart f + oddTailRealPart g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change (((((oddTenTailToClippedSmooth (f + g) x).re : ℝ) : ℂ))) =
    ((((oddTenTailToClippedSmooth f x).re : ℝ) : ℂ)) +
      ((((oddTenTailToClippedSmooth g x).re : ℝ) : ℂ))
  simp

@[simp] theorem oddTailImagPart_add (f g : YoshidaOddTenTail) :
    oddTailImagPart (f + g) = oddTailImagPart f + oddTailImagPart g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change (((((oddTenTailToClippedSmooth (f + g) x).im : ℝ) : ℂ))) =
    ((((oddTenTailToClippedSmooth f x).im : ℝ) : ℂ)) +
      ((((oddTenTailToClippedSmooth g x).im : ℝ) : ℂ))
  simp

@[simp] theorem evenTailRealPart_smul_real
    (r : ℝ) (f : YoshidaEvenOneNinetyNineTail) :
    evenTailRealPart ((r : ℂ) • f) = (r : ℂ) • evenTailRealPart f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change ((((((r : ℂ) *
      evenOneNinetyNineTailToClippedSmooth f x).re : ℝ) : ℂ))) =
    (r : ℂ) * ((((evenOneNinetyNineTailToClippedSmooth f x).re :
      ℝ) : ℂ))
  simp

@[simp] theorem evenTailImagPart_smul_real
    (r : ℝ) (f : YoshidaEvenOneNinetyNineTail) :
    evenTailImagPart ((r : ℂ) • f) = (r : ℂ) • evenTailImagPart f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change ((((((r : ℂ) *
      evenOneNinetyNineTailToClippedSmooth f x).im : ℝ) : ℂ))) =
    (r : ℂ) * ((((evenOneNinetyNineTailToClippedSmooth f x).im :
      ℝ) : ℂ))
  simp

@[simp] theorem oddTailRealPart_smul_real
    (r : ℝ) (f : YoshidaOddTenTail) :
    oddTailRealPart ((r : ℂ) • f) = (r : ℂ) • oddTailRealPart f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change ((((((r : ℂ) * oddTenTailToClippedSmooth f x).re : ℝ) :
      ℂ))) =
    (r : ℂ) * ((((oddTenTailToClippedSmooth f x).re : ℝ) : ℂ))
  simp

@[simp] theorem oddTailImagPart_smul_real
    (r : ℝ) (f : YoshidaOddTenTail) :
    oddTailImagPart ((r : ℂ) • f) = (r : ℂ) • oddTailImagPart f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change ((((((r : ℂ) * oddTenTailToClippedSmooth f x).im : ℝ) :
      ℂ))) =
    (r : ℂ) * ((((oddTenTailToClippedSmooth f x).im : ℝ) : ℂ))
  simp

/-- Real-coordinate projection on the algebraic even form space. -/
def evenFormSpaceRealPart :
    EvenPhaseTailFormSpace →ₗ[ℝ] EvenPhaseTailFormSpace where
  toFun x := FormSpace.of (evenTailRealPart x.toV)
  map_add' x y := by
    apply formSpace_eq_of_toV_eq
    exact evenTailRealPart_add x.toV y.toV
  map_smul' r x := by
    apply formSpace_eq_of_toV_eq
    change evenTailRealPart ((r : ℂ) • x.toV) =
      (r : ℂ) • evenTailRealPart x.toV
    exact evenTailRealPart_smul_real r x.toV

/-- Imaginary-coordinate projection on the algebraic even form space. -/
def evenFormSpaceImagPart :
    EvenPhaseTailFormSpace →ₗ[ℝ] EvenPhaseTailFormSpace where
  toFun x := FormSpace.of (evenTailImagPart x.toV)
  map_add' x y := by
    apply formSpace_eq_of_toV_eq
    exact evenTailImagPart_add x.toV y.toV
  map_smul' r x := by
    apply formSpace_eq_of_toV_eq
    change evenTailImagPart ((r : ℂ) • x.toV) =
      (r : ℂ) • evenTailImagPart x.toV
    exact evenTailImagPart_smul_real r x.toV

/-- Real-coordinate projection on the algebraic odd form space. -/
def oddFormSpaceRealPart :
    OddPhaseTailFormSpace →ₗ[ℝ] OddPhaseTailFormSpace where
  toFun x := FormSpace.of (oddTailRealPart x.toV)
  map_add' x y := by
    apply formSpace_eq_of_toV_eq
    exact oddTailRealPart_add x.toV y.toV
  map_smul' r x := by
    apply formSpace_eq_of_toV_eq
    change oddTailRealPart ((r : ℂ) • x.toV) =
      (r : ℂ) • oddTailRealPart x.toV
    exact oddTailRealPart_smul_real r x.toV

/-- Imaginary-coordinate projection on the algebraic odd form space. -/
def oddFormSpaceImagPart :
    OddPhaseTailFormSpace →ₗ[ℝ] OddPhaseTailFormSpace where
  toFun x := FormSpace.of (oddTailImagPart x.toV)
  map_add' x y := by
    apply formSpace_eq_of_toV_eq
    exact oddTailImagPart_add x.toV y.toV
  map_smul' r x := by
    apply formSpace_eq_of_toV_eq
    change oddTailImagPart ((r : ℂ) • x.toV) =
      (r : ℂ) • oddTailImagPart x.toV
    exact oddTailImagPart_smul_real r x.toV

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailRealImagLinearStructural
