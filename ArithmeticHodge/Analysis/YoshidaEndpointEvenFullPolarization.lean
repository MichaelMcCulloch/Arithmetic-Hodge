import ArithmeticHodge.Analysis.YoshidaEndpointEvenExactLowGramPositive

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization

open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter

noncomputable section

/-!
# Exact low/tail polarization in the even endpoint sector

This module keeps the fixed `P₀/P₂` block separate from the genuinely
infinite zero-two tail.  No finite-mode truncation occurs: the only analytic
hypothesis used by the logarithmic term is local Lipschitz regularity of the
whole tail.
-/

/-- The raw logarithmic cross term of the fixed low profile with a
`P₂`-orthogonal tail vanishes exactly.  The constant part cancels
pointwise, so only the structural `P₂` eigenfunction identity remains. -/
theorem centeredRawLogBilinear_fixedEvenLowProfile_tail_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r)
    (htwo : centeredEvenP2Coefficient r = 0)
    (c b : ℝ) :
    centeredRawLogBilinear (fun x ↦
      c * centeredEvenP0 x + b * centeredEvenP2 x) r = 0 := by
  have hpair : (∫ x : ℝ in -1..1, r x * centeredEvenP2 x) = 0 := by
    rw [integral_mul_centeredEvenP2_eq, htwo]
    ring
  have htwoRaw := centeredRawLogBilinear_centeredEvenP2_tail_eq_zero
    r hr hpair
  rw [show centeredRawLogBilinear (fun x ↦
      c * centeredEvenP0 x + b * centeredEvenP2 x) r =
      b * centeredRawLogBilinear centeredEvenP2 r by
    unfold centeredRawLogBilinear centeredEvenP0
    rw [show (fun x : ℝ ↦ ∫ y : ℝ in -1..1,
        (((c * 1 + b * centeredEvenP2 x) -
            (c * 1 + b * centeredEvenP2 y)) * (r x - r y)) /
              |x - y|) =
        fun x ↦ b * ∫ y : ℝ in -1..1,
          ((centeredEvenP2 x - centeredEvenP2 y) *
            (r x - r y)) / |x - y| by
      funext x
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _hy
      ring]
    exact intervalIntegral.integral_const_mul _ _]
  rw [htwoRaw, mul_zero]

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
