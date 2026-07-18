import ArithmeticHodge.Analysis.MultiplicativeWeilFarPrimeShellStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFarSupportSeparationStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFarCauchyMomentStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilGlobalCrossZeroExpansionStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

open MultiplicativeWeilFarSupportSeparationStructural
open MultiplicativeWeilFarCauchyMomentStructural
open YoshidaBombieriCrossDistribution
open YoshidaBombieriCrossMoments
open YoshidaRenormalizedGeometricKernel

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

/-- Fully undilated moment form of the separated global cross.  The local
Cauchy correction is now an explicitly summable rank-one series whose
`k`-th term carries the exact factor
`exp (-oddRate (k + 1) * log r)`. -/
theorem bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_farMomentExpansion
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    bombieriTwoBlockGlobalCrossSymbol f (normalizedDilation r hr g) =
      ((Real.sqrt r : ℝ) : ℂ) *
          starRingEnd ℂ (mellin (f : ℝ → ℂ) 1) *
            mellin (g : ℝ → ℂ) 0 -
        (∑' k : ℕ,
          ((Real.exp (-oddRate (k + 1) * Real.log r) : ℝ) : ℂ) *
            starRingEnd ℂ
              (bombieriCriticalMoment f (oddRate (k + 1))) *
            bombieriCriticalMoment g (-oddRate (k + 1))) -
        bombieriSeparatedFarPrimeShell f g r := by
  have hsepWeak : bg ≤ r * af := ((div_lt_iff₀ haf).mp hsep).le
  rw [bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_endpoint_sub_cauchyTail_sub_farPrimeShell
      f g hr haf hag hbg hf hg hsep,
    tsum_bombieriCauchyCrossValue_normalizedDilation_tail_eq_moments
      f g haf hag hbg hr hf hg hsepWeak]

/-- After multiplying by `sqrt r`, the endpoint and prime shell form the
normalized smoothed Mangoldt discrepancy.  The remaining Cauchy correction
is an explicitly summable moment series. -/
theorem sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_mangoldtDiscrepancy_sub_momentCorrection
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    ((Real.sqrt r : ℝ) : ℂ) *
        bombieriTwoBlockGlobalCrossSymbol f (normalizedDilation r hr g) =
      ((r : ℂ) * starRingEnd ℂ (mellin (f : ℝ → ℂ) 1) *
          mellin (g : ℝ → ℂ) 0 -
        ∑' n : ℕ, (ArithmeticFunction.vonMangoldt (n + 1) : ℂ) *
          starRingEnd ℂ (bombieriDirectedCorrelation f g
            (r⁻¹ * (n + 1 : ℕ)))) -
      ∑' k : ℕ,
        ((Real.sqrt r : ℝ) : ℂ) *
          (((Real.exp (-oddRate (k + 1) * Real.log r) : ℝ) : ℂ) *
            starRingEnd ℂ
              (bombieriCriticalMoment f (oddRate (k + 1))) *
            bombieriCriticalMoment g (-oddRate (k + 1))) := by
  rw [bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_farMomentExpansion
    f g hr haf hag hbg hf hg hsep]
  have hsqrt : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hr).ne'
  have hsqrtSq :
      ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ) = (r : ℂ) := by
    norm_cast
    simpa [pow_two] using Real.sq_sqrt hr.le
  have hsqrtInv :
      ((Real.sqrt r : ℝ) : ℂ) * ((((Real.sqrt r)⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [Complex.ofReal_inv]
    exact mul_inv_cancel₀ hsqrt
  have htail :
      ((Real.sqrt r : ℝ) : ℂ) *
          (∑' k : ℕ,
            ((Real.exp (-oddRate (k + 1) * Real.log r) : ℝ) : ℂ) *
              starRingEnd ℂ
                (bombieriCriticalMoment f (oddRate (k + 1))) *
              bombieriCriticalMoment g (-oddRate (k + 1))) =
        ∑' k : ℕ,
          ((Real.sqrt r : ℝ) : ℂ) *
            (((Real.exp (-oddRate (k + 1) * Real.log r) : ℝ) : ℂ) *
              starRingEnd ℂ
                (bombieriCriticalMoment f (oddRate (k + 1))) *
              bombieriCriticalMoment g (-oddRate (k + 1))) := by
    rw [tsum_mul_left]
  have hprime :
      ((Real.sqrt r : ℝ) : ℂ) * bombieriSeparatedFarPrimeShell f g r =
        ∑' n : ℕ, (ArithmeticFunction.vonMangoldt (n + 1) : ℂ) *
          starRingEnd ℂ (bombieriDirectedCorrelation f g
            (r⁻¹ * (n + 1 : ℕ))) := by
    unfold bombieriSeparatedFarPrimeShell
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    calc
      ((Real.sqrt r : ℝ) : ℂ) *
            ((ArithmeticFunction.vonMangoldt (n + 1) : ℂ) *
              ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) *
                starRingEnd ℂ (bombieriDirectedCorrelation f g
                  (r⁻¹ * (n + 1 : ℕ))))) =
          (((Real.sqrt r : ℝ) : ℂ) *
              ((((Real.sqrt r)⁻¹ : ℝ) : ℂ))) *
            ((ArithmeticFunction.vonMangoldt (n + 1) : ℂ) *
              starRingEnd ℂ (bombieriDirectedCorrelation f g
                (r⁻¹ * (n + 1 : ℕ)))) := by ring
      _ = _ := by rw [hsqrtInv, one_mul]
  have hendpoint :
      ((Real.sqrt r : ℝ) : ℂ) *
          (((Real.sqrt r : ℝ) : ℂ) *
              starRingEnd ℂ (mellin (f : ℝ → ℂ) 1) *
            mellin (g : ℝ → ℂ) 0) =
        (r : ℂ) * starRingEnd ℂ (mellin (f : ℝ → ℂ) 1) *
          mellin (g : ℝ → ℂ) 0 := by
    calc
      ((Real.sqrt r : ℝ) : ℂ) *
            (((Real.sqrt r : ℝ) : ℂ) *
                starRingEnd ℂ (mellin (f : ℝ → ℂ) 1) *
              mellin (g : ℝ → ℂ) 0) =
          (((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ)) *
            starRingEnd ℂ (mellin (f : ℝ → ℂ) 1) *
              mellin (g : ℝ → ℂ) 0 := by ring
      _ = _ := by rw [hsqrtSq]
  rw [mul_sub, mul_sub, htail, hprime]
  rw [hendpoint]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
