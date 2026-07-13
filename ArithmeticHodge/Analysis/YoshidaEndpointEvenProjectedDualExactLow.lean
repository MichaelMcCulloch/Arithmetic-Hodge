import ArithmeticHodge.Analysis.YoshidaEndpointEvenExactLowGramPositive
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderMoments

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedDualExactLow

open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedDualIntegral
open YoshidaEndpointEvenProjectedRemainderMajorant
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOddCleanPositive

noncomputable section

/-- The polynomial-remainder route lands on the exact positive low Gram, not
the earlier coarse lower Gram. -/
theorem fixedProjectedDual_le_exactLowGram_of_polynomial_remainder
    (c b : ℝ)
    (hbase : IntervalIntegrable
      (fixedProjectedDualBaseIntegrand c b) volume (-1) 1)
    (htrue : IntervalIntegrable
      (fixedProjectedTrueRemainderIntegrand c b) volume (-1) 1)
    (hatanh : IntervalIntegrable
      (fixedProjectedAtanhRemainderIntegrand c b) volume (-1) 1)
    (hpoly : IntervalIntegrable
      (fixedProjectedPolynomialRemainderIntegrand c b) volume (-1) 1)
    (hbound :
      (∫ x : ℝ in -1..1,
          fixedProjectedPolynomialRemainderIntegrand c b x) ≤
        (yoshidaEndpointEvenLowGram00 * c ^ 2 +
            2 * yoshidaEndpointEvenLowGram02 * c * b +
            yoshidaEndpointEvenLowGram22 * b ^ 2) -
          ∫ x : ℝ in -1..1,
            fixedProjectedDualBaseIntegrand c b x) :
    (∫ x : ℝ in -1..1, fixedProjectedDualIntegrand c b x) ≤
      yoshidaEndpointEvenLowGram00 * c ^ 2 +
        2 * yoshidaEndpointEvenLowGram02 * c * b +
        yoshidaEndpointEvenLowGram22 * b ^ 2 := by
  have hclean :
      yoshidaEndpointOddCleanQuadratic
          (fun x ↦ fixedEvenLowProfile c b x) =
        yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * b +
          yoshidaEndpointEvenLowGram22 * b ^ 2 := by
    simpa only [fixedEvenLowProfile] using
      yoshidaEndpointEvenLowGram_quadratic_eq_clean c b
  have hboundClean :
      (∫ x : ℝ in -1..1,
          fixedProjectedPolynomialRemainderIntegrand c b x) ≤
        yoshidaEndpointOddCleanQuadratic
            (fun x ↦ fixedEvenLowProfile c b x) -
          ∫ x : ℝ in -1..1,
            fixedProjectedDualBaseIntegrand c b x := by
    rw [hclean]
    exact hbound
  have hdual :=
    fixedProjectedDual_integral_le_clean_of_polynomial_remainder
      c b hbase htrue hatanh hpoly hboundClean
  rw [hclean] at hdual
  exact hdual

/-- Same result in the literal weighted-dual syntax required by the final
low/tail Schur theorem. -/
theorem fixedProjectedWeightedDual_le_exactLowGram_of_polynomial_remainder
    (c b : ℝ)
    (hbase : IntervalIntegrable
      (fixedProjectedDualBaseIntegrand c b) volume (-1) 1)
    (htrue : IntervalIntegrable
      (fixedProjectedTrueRemainderIntegrand c b) volume (-1) 1)
    (hatanh : IntervalIntegrable
      (fixedProjectedAtanhRemainderIntegrand c b) volume (-1) 1)
    (hpoly : IntervalIntegrable
      (fixedProjectedPolynomialRemainderIntegrand c b) volume (-1) 1)
    (hbound :
      (∫ x : ℝ in -1..1,
          fixedProjectedPolynomialRemainderIntegrand c b x) ≤
        (yoshidaEndpointEvenLowGram00 * c ^ 2 +
            2 * yoshidaEndpointEvenLowGram02 * c * b +
            yoshidaEndpointEvenLowGram22 * b ^ 2) -
          ∫ x : ℝ in -1..1,
            fixedProjectedDualBaseIntegrand c b x) :
    (∫ x : ℝ in -1..1,
      (c * fixedProjectedTailRepresenter0 x +
        b * fixedProjectedTailRepresenter2 x) ^ 2 /
          yoshidaEndpointEvenTailWeight x) ≤
      yoshidaEndpointEvenLowGram00 * c ^ 2 +
        2 * yoshidaEndpointEvenLowGram02 * c * b +
        yoshidaEndpointEvenLowGram22 * b ^ 2 := by
  simpa only [fixedProjectedDualIntegrand] using
    fixedProjectedDual_le_exactLowGram_of_polynomial_remainder
      c b hbase htrue hatanh hpoly hbound

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedDualExactLow
