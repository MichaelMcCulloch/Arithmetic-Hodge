import ArithmeticHodge.Analysis.MultiplicativeWeilLocalCriticalForm

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Global Bombieri quadratic as local energy minus prime correlations

The support-ratio-at-most-two theorem is the special case in which the prime
term vanishes.  For arbitrary compact support the exact remaining obligation
is the domination of the prime correlations by the local critical form.
-/

/-- Unconditional global decomposition of Bombieri's quadratic functional.
The identity isolates the only term absent from the restricted-support
endpoint theorem. -/
theorem bombieriFunctional_quadratic_eq_localCritical_sub_prime
    (g : BombieriTest) :
    bombieriFunctional (bombieriQuadraticTest g) =
      bombieriLocalCriticalForm g g -
        primeSum (bombieriQuadraticTest g) := by
  rw [bombieriFunctional_apply, bombieriQuadratic_polar_eq_two_re,
    bombieriArchTerm_quadratic_eq_critical_normSq_integral,
    bombieriLocalCriticalForm_self]
  have hlocal : bombieriLocalCriticalQuadratic g =
      ((2 * (mellin (g : ℝ → ℂ) 1 *
        starRingEnd ℂ (mellin (g : ℝ → ℂ) 0)).re : ℝ) : ℂ) +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          (((Complex.digamma
            ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re -
              Real.log Real.pi : ℝ) : ℂ) *
            (Complex.normSq
              (mellin (g : ℝ → ℂ)
                ((1 / 2 : ℝ) + v * Complex.I)) : ℂ) := by
    rfl
  rw [hlocal]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
