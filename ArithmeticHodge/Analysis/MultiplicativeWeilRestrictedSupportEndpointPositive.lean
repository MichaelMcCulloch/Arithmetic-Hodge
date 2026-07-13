import ArithmeticHodge.Analysis.MultiplicativeWeilRestrictedSupportStructural
import ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryProductionBridgeFinal
import ArithmeticHodge.Analysis.YoshidaEndpointOddProductionPositive

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilRestrictedSupportEndpointPositive

open ArithmeticHodge.Analysis
open MultiplicativeWeil
open MultiplicativeWeilRestrictedSupportStructural
open YoshidaEndpointHyperbolicBound
open YoshidaPointwiseParityCore

noncomputable section

/-!
# Structural endpoint positivity on the complete restricted-support class

The unconditional odd and even production theorems recombine on the complete
periodic source core.  Certificate-free support transport then proves the
Bombieri quadratic functional nonnegative for every test whose multiplicative
support ratio is at most two.
-/

/-- The actual production clipped form is nonnegative on the complete
endpoint periodic source core. -/
theorem yoshidaEndpointPeriodicCore_re_nonneg
    (f : YoshidaClippedPeriodicCore yoshidaEndpointA) :
    0 ≤ (yoshidaClippedLocalCriticalForm yoshidaEndpointA
      yoshidaEndpointA_pos
      (f : YoshidaClippedSmooth yoshidaEndpointA)
      (f : YoshidaClippedSmooth yoshidaEndpointA)).re := by
  exact yoshidaClippedLocalCriticalForm_re_nonneg_of_pointwise_parity
    yoshidaEndpointA_pos
    YoshidaEndpointEvenBoundaryProductionBridge.yoshidaClippedLocalCriticalForm_re_nonneg_of_pointwiseEven
    YoshidaEndpointOddProductionPositive.yoshidaClippedLocalCriticalForm_re_nonneg
    f

/-- Structural Bombieri nonnegativity for every quadratic test supported in a
multiplicative interval of ratio at most two. -/
theorem bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2) :
    0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re := by
  exact
    bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two_of_periodicCore
      yoshidaEndpointPeriodicCore_re_nonneg g hl hlr hsupport hratio

/-- Real-valued restricted-support positivity in the shape consumed by the
Bombieri criterion. -/
theorem bombieriFunctional_quadratic_nonneg_of_ratio_le_two
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2) :
    (bombieriFunctional (bombieriQuadraticTest g)).im = 0 ∧
      0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re := by
  exact ⟨bombieriFunctional_bombieriQuadraticTest_im_eq_zero g,
    bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two
      g hl hlr hsupport hratio⟩

end

end ArithmeticHodge.Analysis.MultiplicativeWeilRestrictedSupportEndpointPositive
