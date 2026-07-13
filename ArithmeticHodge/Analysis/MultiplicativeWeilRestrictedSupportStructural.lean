import ArithmeticHodge.Analysis.YoshidaPointwiseParityCore
import ArithmeticHodge.Analysis.YoshidaRestrictedEndpointCoreBridge

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilRestrictedSupportStructural

open ArithmeticHodge.Analysis
open MultiplicativeWeil
open YoshidaEndpointHyperbolicBound
open YoshidaPointwiseOddPeriodicCore
open YoshidaPointwiseParityCore

noncomputable section

/-!
# Structural restricted-support Bombieri transport

Nonnegativity of the production clipped form on the complete endpoint
periodic core transports exactly to every Bombieri quadratic test whose
multiplicative support ratio is at most two.  The support bridge imported here
is certificate-free; this module does not import a finite Gram or tail bound.
-/

/-- Periodic-core nonnegativity implies Bombieri nonnegativity for every test
with multiplicative support ratio at most two. -/
theorem bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two_of_periodicCore
    (hcore : ∀ f : YoshidaClippedPeriodicCore yoshidaEndpointA,
      0 ≤ (yoshidaClippedLocalCriticalForm yoshidaEndpointA
        yoshidaEndpointA_pos
        (f : YoshidaClippedSmooth yoshidaEndpointA)
        (f : YoshidaClippedSmooth yoshidaEndpointA)).re)
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2) :
    0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re := by
  let lambda : ℝ := logarithmicCenter l r
  have hlambda : 0 < lambda := logarithmicCenter_pos l r
  let g' : BombieriTest := normalizedDilation lambda hlambda g
  have hsupported : YoshidaCriticalPullbackSupported yoshidaEndpointA g' := by
    exact
      logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaEndpointA
        g hl hlr hsupport hratio
  have hmem : yoshidaCriticalPullbackCropLinear yoshidaEndpointA g' ∈
      yoshidaClippedPeriodicCoreSubmodule yoshidaEndpointA := by
    exact logCenteredNormalizedDilation_crop_mem_yoshidaEndpointPeriodicCore
      g hl hlr hsupport hratio
  let core : YoshidaClippedPeriodicCore yoshidaEndpointA :=
    ⟨yoshidaCriticalPullbackCropLinear yoshidaEndpointA g', hmem⟩
  have hclipped :
      0 ≤ (yoshidaClippedLocalCriticalForm yoshidaEndpointA
        yoshidaEndpointA_pos
        (yoshidaCriticalPullbackCropLinear yoshidaEndpointA g')
        (yoshidaCriticalPullbackCropLinear yoshidaEndpointA g')).re := by
    simpa only [core] using hcore core
  have hlocal : 0 ≤ (bombieriLocalCriticalForm g' g').re := by
    rw [← yoshidaClippedLocalCriticalForm_crop_eq_bombieriLocalCriticalForm
      yoshidaEndpointA_pos g' g' hsupported hsupported]
    exact hclipped
  have hsupport' : tsupport g' ⊆
      Set.Icc (l / lambda) (r / lambda) := by
    exact normalizedDilation_tsupport_subset_Icc
      lambda hlambda g hsupport
  have hl' : 0 < l / lambda := div_pos hl hlambda
  have hlr' : l / lambda ≤ r / lambda :=
    div_le_div_of_nonneg_right hlr hlambda.le
  have hratio' : (r / lambda) / (l / lambda) ≤ 2 := by
    rw [div_div_div_cancel_right₀ hlambda.ne' r l]
    exact hratio
  have hfunctional' :=
    bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
      g' hl' hlr' hsupport' hratio'
  have hinvariant :=
    bombieriFunctional_quadratic_normalizedDilation lambda hlambda g
  calc
    0 ≤ (bombieriLocalCriticalForm g' g').re := hlocal
    _ = (bombieriFunctional (bombieriQuadraticTest g')).re := by
      rw [hfunctional']
    _ = (bombieriFunctional (bombieriQuadraticTest g)).re := by
      rw [hinvariant]

/-- The same transport stated in the real-valued shape used by the Bombieri
criterion. -/
theorem bombieriFunctional_quadratic_nonneg_of_ratio_le_two_of_periodicCore
    (hcore : ∀ f : YoshidaClippedPeriodicCore yoshidaEndpointA,
      0 ≤ (yoshidaClippedLocalCriticalForm yoshidaEndpointA
        yoshidaEndpointA_pos
        (f : YoshidaClippedSmooth yoshidaEndpointA)
        (f : YoshidaClippedSmooth yoshidaEndpointA)).re)
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2) :
    (bombieriFunctional (bombieriQuadraticTest g)).im = 0 ∧
      0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re := by
  exact ⟨bombieriFunctional_bombieriQuadraticTest_im_eq_zero g,
    bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two_of_periodicCore
      hcore g hl hlr hsupport hratio⟩

/-- Literal even and odd production positivity are sufficient for structural
restricted-support Bombieri nonnegativity. -/
theorem bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two_of_parity
    (hEven : ∀ f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaEndpointA,
      0 ≤ (yoshidaClippedLocalCriticalForm yoshidaEndpointA
        yoshidaEndpointA_pos
        (f.1 : YoshidaClippedSmooth yoshidaEndpointA)
        (f.1 : YoshidaClippedSmooth yoshidaEndpointA)).re)
    (hOdd : ∀ f : yoshidaPointwiseOddPeriodicCoreSubmodule yoshidaEndpointA,
      0 ≤ (yoshidaClippedLocalCriticalForm yoshidaEndpointA
        yoshidaEndpointA_pos
        (f.1 : YoshidaClippedSmooth yoshidaEndpointA)
        (f.1 : YoshidaClippedSmooth yoshidaEndpointA)).re)
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2) :
    0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re := by
  refine
    bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two_of_periodicCore
      ?_ g hl hlr hsupport hratio
  intro f
  exact yoshidaClippedLocalCriticalForm_re_nonneg_of_pointwise_parity
    yoshidaEndpointA_pos hEven hOdd f

end

end ArithmeticHodge.Analysis.MultiplicativeWeilRestrictedSupportStructural
