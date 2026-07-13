import ArithmeticHodge.Analysis.YoshidaFactorTwoPhysicalSymbol

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoCenteredPhysical

noncomputable section

open MultiplicativeWeil
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoPhysicalSymbol
open YoshidaFactorTwoPrimeCorrelationSymbol

/-!
# The centered physical factor-two symbol

The one-sided adjacent-correlation formula is translated by `log 2`.  This
places the self-correlation on its natural symmetric interval and retains the
smooth archimedean kernel and both prime atoms exactly.
-/

theorem factorTwoGlobalCrossSymbol_eq_centered_physical
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoGlobalCrossSymbol g =
      (∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength,
        ((factorTwoAdjacentSmoothKernel (factorTwoLogLength + s) : ℝ) : ℂ) *
          factorTwoSelfCorrelation g s) -
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
  rw [show (fun s : ℝ ↦
      ((factorTwoAdjacentSmoothKernel (factorTwoLogLength + s) : ℝ) : ℂ) *
        factorTwoSelfCorrelation g s) =
      fun s : ℝ ↦
        (((factorTwoAdjacentSmoothKernel (s + factorTwoLogLength) : ℝ) : ℂ) *
          factorTwoSelfCorrelation g
            ((s + factorTwoLogLength) - factorTwoLogLength)) by
    funext s
    congr 3 <;> ring]
  rw [hshift]
  congr 1
  · ring
  · unfold factorTwoPhysicalLength
    ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoCenteredPhysical
