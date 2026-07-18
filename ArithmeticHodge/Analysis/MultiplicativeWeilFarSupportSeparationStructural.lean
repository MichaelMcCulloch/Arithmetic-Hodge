import ArithmeticHodge.Analysis.MultiplicativeWeilFarLocalCrossStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ComplexConjugate FourierTransform SchwartzMap

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFarSupportSeparationStructural

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaCauchyPairing
open MultiplicativeWeilFarLocalCrossStructural

/-!
# Concrete support separation for the far local cross

If `f` is supported in `[af, bf]` and `g` in `[ag, bg]`, then the critical
logarithmic support of `normalizedDilation r hr g` lies weakly to the right of
that of `f` exactly at the support-only threshold

`bg ≤ r * af`.

At equality the two logarithmic support intervals can meet at only one point.
That point is null for the correlation integral, so the cross-correlation
still vanishes on the complete nonpositive half-line, including zero.
-/

/-- The sharp physical endpoint inequality implies separation of the
corresponding logarithmic endpoints. -/
theorem log_support_separated_of_bg_le_r_mul_af
    {af bg r : ℝ} (haf : 0 < af) (hbg : 0 < bg)
    (hsep : bg ≤ r * af) :
    -Real.log af ≤ -Real.log bg + Real.log r := by
  have hdiv : bg / af ≤ r := (div_le_iff₀ haf).2 hsep
  have hlog : Real.log (bg / af) ≤ Real.log r :=
    Real.log_le_log (div_pos hbg haf) hdiv
  rw [Real.log_div hbg.ne' haf.ne'] at hlog
  linarith

/-- Concrete multiplicative support separation kills the critical cross on
the entire nonpositive logarithmic half-line.  The endpoint threshold
`bg ≤ r * af` permits equality: the possible contact is a singleton and hence
does not contribute to the integral. -/
theorem bombieriCriticalCrossCorrelation_normalizedDilation_eq_zero_of_nonpos
    (f g : BombieriTest) {af bf ag bg r u : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hr : 0 < r)
    (hfsupport : tsupport f ⊆ Set.Icc af bf)
    (hgsupport : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg ≤ r * af) (hu : u ≤ 0) :
    bombieriCriticalCrossCorrelation f (normalizedDilation r hr g) u = 0 := by
  let lf : ℝ := -Real.log bf
  let rf : ℝ := -Real.log af
  let lg : ℝ := -Real.log bg
  let rg : ℝ := -Real.log ag
  have hedge : rf - Real.log r ≤ lg := by
    have hlog := log_support_separated_of_bg_le_r_mul_af haf hbg hsep
    simpa only [rf, lg] using (show
      -Real.log af - Real.log r ≤ -Real.log bg by linarith)
  rw [bombieriCriticalCrossCorrelation, crossCorrelation_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [(countable_singleton rf).ae_notMem volume] with x hx
  by_cases hxf : x ∈ Set.Icc lf rf
  · have hxne : x ≠ rf := by
      simpa only [mem_singleton_iff] using hx
    have hxlt : x < rf := lt_of_le_of_ne hxf.2 hxne
    have harglt : u + x - Real.log r < lg := by linarith
    have hargout : u + x - Real.log r ∉ Set.Icc lg rg := by
      intro hmem
      exact (not_lt_of_ge hmem.1) harglt
    rw [normalizedDilation_logarithmicPullbackSchwartz_critical]
    have hgzero :
        g.logarithmicPullbackSchwartz (1 / 2)
            (u + x - Real.log r) = 0 :=
      logarithmicPullbackSchwartz_eq_zero_outside
        g hag hgsupport (by simpa only [lg, rg] using hargout)
    rw [hgzero, mul_zero]
    simp
  · have hfzero :
        f.logarithmicPullbackSchwartz (1 / 2) x = 0 :=
      logarithmicPullbackSchwartz_eq_zero_outside
        f haf hfsupport (by simpa only [lf, rf] using hxf)
    rw [hfzero, star_zero, zero_mul]
    simp

/-- The exact far-local formula with both abstract correlation-vanishing
hypotheses discharged solely by concrete support separation. -/
theorem bombieriLocalCriticalForm_dilation_eq_endpoint_sub_cauchyTail_of_support
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hr : 0 < r)
    (hfsupport : tsupport f ⊆ Set.Icc af bf)
    (hgsupport : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg ≤ r * af) :
    bombieriLocalCriticalForm f (normalizedDilation r hr g) =
      ((Real.sqrt r : ℝ) : ℂ) *
          starRingEnd ℂ (mellin (f : ℝ → ℂ) 1) *
            mellin (g : ℝ → ℂ) 0 -
        ∑' k : ℕ, bombieriCauchyCrossValue f
          (normalizedDilation r hr g) (k + 1) := by
  apply bombieriLocalCriticalForm_dilation_eq_endpoint_sub_cauchyTail
      f g r hr
  · intro u hu
    exact bombieriCriticalCrossCorrelation_normalizedDilation_eq_zero_of_nonpos
      f g haf hag hbg hr hfsupport hgsupport hsep hu.le
  · exact bombieriCriticalCrossCorrelation_normalizedDilation_eq_zero_of_nonpos
      f g haf hag hbg hr hfsupport hgsupport hsep le_rfl

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFarSupportSeparationStructural
