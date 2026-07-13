import ArithmeticHodge.Analysis.YoshidaFactorTwoPhysicalSymbol

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoCenteredPhysical

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoAdjacentSchwartz
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoPhysicalSymbol
open YoshidaFactorTwoPrimeCorrelationSymbol
open YoshidaRenormalizedGeometricKernel

/-!
# The centered physical factor-two symbol

The one-sided adjacent-correlation formula is translated by `log 2`.  This
places the self-correlation on its natural symmetric interval and retains the
smooth archimedean kernel and both prime atoms exactly.
-/

def factorTwoCenteredIntegrand (g : BombieriTest) (s : ℝ) : ℂ :=
  ((factorTwoAdjacentSmoothKernel (factorTwoLogLength + s) : ℝ) : ℂ) *
    factorTwoSelfCorrelation g s

def factorTwoSymmetricWeight (s : ℝ) : ℝ :=
  factorTwoAdjacentSmoothKernel (factorTwoLogLength + s) +
    factorTwoAdjacentSmoothKernel (factorTwoLogLength - s)

def factorTwoAntisymmetricWeight (s : ℝ) : ℝ :=
  factorTwoAdjacentSmoothKernel (factorTwoLogLength + s) -
    factorTwoAdjacentSmoothKernel (factorTwoLogLength - s)

def factorTwoPrimeShift : ℝ := Real.log (3 / 2 : ℝ)

theorem factorTwoCenteredIntegrand_intervalIntegrable
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    IntervalIntegrable (factorTwoCenteredIntegrand g) volume
      (-factorTwoLogLength) factorTwoLogLength := by
  have hgrow : IntervalIntegrable (fun u : ℝ ↦
      ((Real.exp (u / 2) : ℝ) : ℂ) *
        factorTwoAdjacentCorrelation g u)
      volume 0 factorTwoPhysicalLength := by
    apply Continuous.intervalIntegrable
    have hexp : Continuous (fun u : ℝ ↦
        ((Real.exp (u / 2) : ℝ) : ℂ)) := by fun_prop
    exact hexp.mul
      (factorTwoAdjacentCorrelation_contDiff g 0).continuous
  have htail := factorTwoTailIntegrand_intervalIntegrable
    g ha hab hsupport hratio
  have hsmooth : IntervalIntegrable (fun u : ℝ ↦
      ((factorTwoAdjacentSmoothKernel u : ℝ) : ℂ) *
        factorTwoAdjacentCorrelation g u)
      volume 0 factorTwoPhysicalLength := by
    have hsub := hgrow.sub htail
    apply hsub.congr
    intro u _hu
    unfold factorTwoAdjacentSmoothKernel factorTwoTailKernel
    change ((Real.exp (u / 2) : ℝ) : ℂ) *
          factorTwoAdjacentCorrelation g u -
        (((oddKernel u / 2 - Real.exp (-u / 2) : ℝ)) : ℂ) *
          factorTwoAdjacentCorrelation g u =
      (((2 * Real.cosh (u / 2) - oddKernel u / 2 : ℝ)) : ℂ) *
        factorTwoAdjacentCorrelation g u
    rw [Real.cosh_eq]
    push_cast
    ring
  have hshift := hsmooth.comp_add_right factorTwoLogLength
  convert hshift using 1
  · funext s
    unfold factorTwoCenteredIntegrand
    rw [factorTwoAdjacentCorrelation_eq_shift]
    congr 3 <;> ring
  · ring
  · unfold factorTwoPhysicalLength
    ring

theorem factorTwoGlobalCrossSymbol_eq_centered_physical
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoGlobalCrossSymbol g =
      (∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength,
        factorTwoCenteredIntegrand g s) -
        factorTwoPrimeCorrelationSymbol g := by
  rw [factorTwoGlobalCrossSymbol_eq_physical
    g ha hab hsupport hratio]
  congr 1
  rw [show (fun u : ℝ ↦
      ((factorTwoAdjacentSmoothKernel u : ℝ) : ℂ) *
        factorTwoAdjacentCorrelation g u) =
      fun u : ℝ ↦
        ((factorTwoAdjacentSmoothKernel u : ℝ) : ℂ) *
          factorTwoSelfCorrelation g (u - factorTwoLogLength) by
    funext u
    rw [factorTwoAdjacentCorrelation_eq_shift]]
  have hshift := intervalIntegral.integral_comp_add_right
    (f := fun u : ℝ ↦
      ((factorTwoAdjacentSmoothKernel u : ℝ) : ℂ) *
        factorTwoSelfCorrelation g (u - factorTwoLogLength))
    (a := -factorTwoLogLength) (b := factorTwoLogLength)
    factorTwoLogLength
  rw [show (fun s : ℝ ↦ factorTwoCenteredIntegrand g s) =
      fun s : ℝ ↦
        (((factorTwoAdjacentSmoothKernel (s + factorTwoLogLength) : ℝ) : ℂ) *
          factorTwoSelfCorrelation g
            ((s + factorTwoLogLength) - factorTwoLogLength)) by
    funext s
    unfold factorTwoCenteredIntegrand
    congr 3 <;> ring]
  rw [hshift]
  congr 1
  · ring
  · unfold factorTwoPhysicalLength
    ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoCenteredPhysical
