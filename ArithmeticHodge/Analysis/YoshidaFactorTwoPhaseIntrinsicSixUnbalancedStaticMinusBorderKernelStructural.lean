import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusBorderKernelStructural

noncomputable section

open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PerturbationStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural

/-!
# Generic negative-endpoint composite border kernel

The negative endpoint reverses only the even perturbation coordinates.  This
file records that sign change once, at the complete correlation-profile
boundary, and reuses the global joint-error machinery of the positive
determinant layer.  No correlation is subdivided or sampled.
-/

/-- Explicit negative-endpoint `P₀-P₄` core after insertion of the clean
degree-six model. -/
def minusBorderCompositeR04 : ℝ :=
  (1 / 10 : ℝ) + factorTwoIntrinsicP4CleanRemainderModel04 -
    poleFreeCoeff4 yoshidaEndpointA * (16 / 315) -
    poleFreeCoeff6 yoshidaEndpointA * (32 / 99) -
    187 / 3 + 90 * Real.log 2

/-- Explicit negative-endpoint `P₂-P₄` core after insertion of the clean
degree-six model. -/
def minusBorderCompositeR24 : ℝ :=
  (1 / 7 : ℝ) + factorTwoIntrinsicP4CleanRemainderModel24 -
    poleFreeCoeff6 yoshidaEndpointA * (32 / 315) -
    29 / 3 + 14 * Real.log 2

/-- Sum profile for the negative even border and the alternating tail. -/
def minusBorderCompositeP
    (u0 u2 k : ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  plusDetCompositeP (-u0) (-u2) k q t

/-- Difference profile for the negative even border and the alternating
tail. -/
def minusBorderCompositeM
    (u0 u2 k : ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  plusDetCompositeM (-u0) (-u2) k q t

/-- The clean pairing itself does not change endpoint sign. -/
def minusBorderCompositeCleanTransfer (u0 u2 : ℝ) : ℝ :=
  plusDetCompositeCleanTransfer u0 u2

/-- The negative even pole-free error and alternating sharp regular error,
kept as the same complete joint remainder used by the plus layer. -/
def minusBorderCompositeJointError
    (u0 u2 k : ℝ) (q : ℝ → ℝ) : ℝ :=
  plusDetCompositeJointError (-u0) (-u2) k q

/-- Shared explicit core of one complete negative-border affine model. -/
def minusBorderCompositeCore
    (C u0 u2 k : ℝ) (q : ℝ → ℝ) : ℝ :=
  C + u0 * minusBorderCompositeR04 +
    u2 * minusBorderCompositeR24 +
    k * intrinsicAlternatingSharpArchModel q -
    (Real.log 3 / Real.sqrt 3) *
      minusBorderCompositeP u0 u2 k q
        (factorTwoPrimeShift / yoshidaEndpointA)

set_option maxHeartbeats 800000 in
/-- Every negative-border affine model is exactly its explicit core, the
unchanged clean-model transfer, and one complete joint analytic error. -/
theorem minusBorderCompositeSharp_decomposition
    (C u0 u2 k : ℝ) (q : ℝ → ℝ) :
    C + u0 * factorTwoIntrinsicFourP45Cross04 (-1) +
        u2 * factorTwoIntrinsicFourP45Cross24 (-1) +
        k * plusDetAlternatingSharpModel q =
      minusBorderCompositeCore C u0 u2 k q +
        minusBorderCompositeCleanTransfer u0 u2 +
        minusBorderCompositeJointError u0 u2 k q := by
  have hclean04 :=
    factorTwoIntrinsicP4CleanCross04_eq_potential_add_remainder
  have hclean24 :=
    factorTwoIntrinsicP4CleanCross24_eq_potential_add_remainder
  rcases factorTwoIntrinsicP4_perturbation_structural_eq with
    ⟨hpert04, hpert24, _hpert44⟩
  have herror := poleFreeAnalyticError_plusDetCompositeCe (-u0) (-u2)
  unfold factorTwoIntrinsicFourP45Cross04
    factorTwoIntrinsicFourP45Cross24
  rw [hclean04, hclean24, hpert04, hpert24]
  unfold factorTwoIntrinsicP4PerturbationBase04
    factorTwoIntrinsicP4PerturbationBase24 plusDetAlternatingSharpModel
    minusBorderCompositeCore minusBorderCompositeCleanTransfer
    minusBorderCompositeJointError minusBorderCompositeR04
    minusBorderCompositeR24 minusBorderCompositeP
  unfold plusDetCompositeCleanTransfer plusDetCompositeJointError
  rw [herror]
  unfold plusDetCompositeP plusDetCompositeCe plusDetCompositeCa
  ring

/-- Fine structural box for the negative-endpoint constant-basis core. -/
theorem minusBorderCompositeR04_bounds :
    (7495469 / 50000000 : ℝ) < minusBorderCompositeR04 ∧
      minusBorderCompositeR04 < (14991239 / 100000000 : ℝ) := by
  have hmodel := factorTwoIntrinsicP4CleanRemainderModel04_bounds
  have hlog := strict_log_two_fine_bounds
  have h5 := log_two_pow_fine_bounds_plusDet 5 (by norm_num)
  have h6 := log_two_pow_fine_bounds_plusDet 6 (by norm_num)
  have h7 := log_two_pow_fine_bounds_plusDet 7 (by norm_num)
  unfold minusBorderCompositeR04 poleFreeCoeff4 poleFreeCoeff6
    yoshidaEndpointA
  constructor <;> nlinarith [hmodel.1, hmodel.2, hlog.1, hlog.2,
    h5.1, h5.2, h6.1, h6.2, h7.1, h7.2]

/-- Fine structural box for the negative-endpoint degree-two-basis core. -/
theorem minusBorderCompositeR24_bounds :
    (126195969 / 700000000 : ℝ) < minusBorderCompositeR24 ∧
      minusBorderCompositeR24 < (7887511 / 43750000 : ℝ) := by
  have hmodel := factorTwoIntrinsicP4CleanRemainderModel24_bounds
  have hlog := strict_log_two_fine_bounds
  have h7 := log_two_pow_fine_bounds_plusDet 7 (by norm_num)
  unfold minusBorderCompositeR24 poleFreeCoeff6 yoshidaEndpointA
  constructor <;> nlinarith [hmodel.1, hmodel.2, hlog.1, hlog.2,
    h7.1, h7.2]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusBorderKernelStructural
