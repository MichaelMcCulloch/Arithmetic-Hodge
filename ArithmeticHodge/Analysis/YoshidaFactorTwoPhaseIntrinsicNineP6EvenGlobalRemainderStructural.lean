import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenGlobalRemainderStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
open YoshidaFactorTwoPhaseSymmetricCarleman

/-!
# A global energy charge for the pole-free analytic remainder

The translated degree-six kernel model has a single analytic remainder.  This
file packages its existing global envelope for the autocorrelation of an
arbitrary continuous real profile.  The proof uses the sharp pointwise
autocorrelation energy bound and the exact integrated mass of the analytic
envelope.  It does not subdivide the translation interval or sample the
profile.
-/

/-- The pointwise integrated envelope, specialized only to an arbitrary
autocorrelation.  This is the strongest reusable form before replacing the
correlation by its total energy. -/
theorem abs_poleFreeAnalyticError_centeredEndpointCorrelation_le_integratedWeight
    (e : ℝ → ℝ) (he : Continuous e) :
    |poleFreeAnalyticError (centeredEndpointCorrelation e)| ≤
      ∫ t : ℝ in 0..2,
        integratedPoleFreeWeight t * |centeredEndpointCorrelation e t| := by
  exact abs_poleFreeAnalyticError_le_integratedPoleFreeWeight
    (centeredEndpointCorrelation e)
    (continuous_centeredEndpointCorrelation_of_continuous e he)

/-- The global pole-free remainder costs at most `3 / 40000` of the centered
`L²` energy of any continuous real profile.  This is an energy-relative
bound on the full translation interval, with no finite-dimensional or parity
hypothesis. -/
theorem abs_poleFreeAnalyticError_centeredEndpointCorrelation_le_energy
    (e : ℝ → ℝ) (he : Continuous e) :
    |poleFreeAnalyticError (centeredEndpointCorrelation e)| ≤
      (3 / 40000 : ℝ) * (∫ x : ℝ in -1..1, e x ^ 2) := by
  let C : ℝ → ℝ := centeredEndpointCorrelation e
  let E : ℝ := ∫ x : ℝ in -1..1, e x ^ 2
  let W : ℝ → ℝ := integratedPoleFreeWeight
  have hC : Continuous C := by
    dsimp only [C]
    exact continuous_centeredEndpointCorrelation_of_continuous e he
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (e x))
  have hW : Continuous W := by
    simpa only [W] using continuous_integratedPoleFreeWeight
  have hbase : |poleFreeAnalyticError C| ≤
      ∫ t : ℝ in 0..2, W t * |C t| := by
    simpa only [W] using
      abs_poleFreeAnalyticError_le_integratedPoleFreeWeight C hC
  have hmono :
      (∫ t : ℝ in 0..2, W t * |C t|) ≤
        ∫ t : ℝ in 0..2, W t * E := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((hW.mul hC.abs).intervalIntegrable 0 2)
      ((hW.mul continuous_const).intervalIntegrable 0 2)
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ht
    have hcorr : |C t| ≤ E := by
      dsimp only [C, E]
      exact abs_centeredEndpointCorrelation_le_energy
        e he htIcc.1 htIcc.2
    exact mul_le_mul_of_nonneg_left hcorr
      (by simpa only [W] using integratedPoleFreeWeight_nonneg htIcc)
  have hWint : (∫ t : ℝ in 0..2, W t) < (3 / 40000 : ℝ) := by
    simpa only [W] using
      integratedPoleFreeWeight_integral_lt_three_div_40000
  have hfactor :
      (∫ t : ℝ in 0..2, W t * E) =
        E * (∫ t : ℝ in 0..2, W t) := by
    rw [show (fun t : ℝ ↦ W t * E) = fun t ↦ E * W t by
      funext t
      ring,
      intervalIntegral.integral_const_mul]
  have hscaled :
      E * (∫ t : ℝ in 0..2, W t) ≤ E * (3 / 40000 : ℝ) :=
    mul_le_mul_of_nonneg_left hWint.le hE
  change |poleFreeAnalyticError C| ≤ (3 / 40000 : ℝ) * E
  rw [mul_comm]
  exact hbase.trans (hmono.trans (hfactor.trans_le hscaled))

/-- The directly usable two-sided form of the global energy charge. -/
theorem poleFreeAnalyticError_centeredEndpointCorrelation_mem_energyInterval
    (e : ℝ → ℝ) (he : Continuous e) :
    -(3 / 40000 : ℝ) * (∫ x : ℝ in -1..1, e x ^ 2) ≤
        poleFreeAnalyticError (centeredEndpointCorrelation e) ∧
      poleFreeAnalyticError (centeredEndpointCorrelation e) ≤
        (3 / 40000 : ℝ) * (∫ x : ℝ in -1..1, e x ^ 2) := by
  simpa only [neg_mul] using
    (abs_le.mp
      (abs_poleFreeAnalyticError_centeredEndpointCorrelation_le_energy e he))

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenGlobalRemainderStructural
