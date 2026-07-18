import ArithmeticHodge.Analysis.MultiplicativeWeilFarPrimeShellStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFarSupportSeparationStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilGlobalCrossZeroExpansionStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

open MultiplicativeWeilFarSupportSeparationStructural
open YoshidaBombieriCrossDistribution

/-!
# Exact global cross between separated multiplicative cells

For strictly separated cells, the complete Bombieri cross is the endpoint
term minus the positive Cauchy tail and the surviving Mangoldt shell.  The
unconditional zero formula identifies that same expression with its oriented
zero-side series.  These are exact identities, not decay or positivity
estimates.
-/

/-- The exact local-minus-prime cross between strictly separated cells. -/
theorem bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_endpoint_sub_cauchyTail_sub_farPrimeShell
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    bombieriTwoBlockGlobalCrossSymbol f (normalizedDilation r hr g) =
      ((Real.sqrt r : ℝ) : ℂ) *
          starRingEnd ℂ (mellin (f : ℝ → ℂ) 1) *
            mellin (g : ℝ → ℂ) 0 -
        (∑' k : ℕ, bombieriCauchyCrossValue f
          (normalizedDilation r hr g) (k + 1)) -
        bombieriSeparatedFarPrimeShell f g r := by
  have hsepWeak : bg ≤ r * af := ((div_lt_iff₀ haf).mp hsep).le
  unfold bombieriTwoBlockGlobalCrossSymbol
  rw [bombieriLocalCriticalForm_dilation_eq_endpoint_sub_cauchyTail_of_support
      f g haf hag hbg hr hf hg hsepWeak,
    bombieriPolarizedPrimeCross_normalizedDilation_eq_farPrimeShell
      f g hr haf hf hg hsep]

/-- Arithmetic and spectral descriptions of the same separated global
cross.  This exposes the precise Mangoldt discrepancy whose positivity would
have to be controlled in any far-cell assembly argument. -/
theorem endpoint_sub_cauchyTail_sub_farPrimeShell_eq_zeroSum
    (zeros : ZetaZeroEnumeration)
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    ((Real.sqrt r : ℝ) : ℂ) *
          starRingEnd ℂ (mellin (f : ℝ → ℂ) 1) *
            mellin (g : ℝ → ℂ) 0 -
        (∑' k : ℕ, bombieriCauchyCrossValue f
          (normalizedDilation r hr g) (k + 1)) -
        bombieriSeparatedFarPrimeShell f g r =
      ∑' n,
        (r : ℂ) ^ ((1 / 2 : ℂ) - (zeros.zero n).val) *
          mellin (g : ℝ → ℂ) (zeros.zero n).val *
            coefficientConjugate (mellin (f : ℝ → ℂ))
              (1 - (zeros.zero n).val) := by
  rw [← bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_zeroSum
    zeros f g r hr]
  exact
    (bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_endpoint_sub_cauchyTail_sub_farPrimeShell
      f g hr haf hag hbg hf hg hsep).symm

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
