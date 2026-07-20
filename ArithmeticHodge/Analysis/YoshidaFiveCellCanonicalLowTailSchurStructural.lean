import ArithmeticHodge.Analysis.YoshidaFiveCellHighTailCoercivityStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseHigherLegendreDecomposition
import ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellResidualFactorTwoStructural

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaFiveCellCanonicalLowTailSchurStructural

noncomputable section

open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFiveCellEndpointOperatorProbeStructural
open YoshidaFiveCellHighTailCoercivityStructural
open MultiplicativeWeilFiveCellSingleProfileStructural
open MultiplicativeWeilFiveCellResidualFactorTwoStructural
open MultiplicativeWeilAllLengthEndpointReserveStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeil
open MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# Canonical cutoff-nine low--tail Schur reduction

The infinite tail is now positive without a parity hypothesis.  This file
therefore isolates the exact remaining obstruction for an arbitrary profile:
the finite cutoff-nine diagonal and its one mixed Schur contraction against
the canonical higher residual.
-/

/-- Symmetric polarization of the complete five-cell operator. -/
def fiveCellEndpointOperatorCross (u v : ℝ → ℝ) : ℝ :=
  (fiveCellEndpointOperator (u + v) - fiveCellEndpointOperator u -
    fiveCellEndpointOperator v) / 2

/-- Exact low plus tail expansion, by the definition of polarization. -/
theorem fiveCellEndpointOperator_add
    (u v : ℝ → ℝ) :
    fiveCellEndpointOperator (u + v) =
      fiveCellEndpointOperator u +
        2 * fiveCellEndpointOperatorCross u v +
          fiveCellEndpointOperator v := by
  unfold fiveCellEndpointOperatorCross
  ring

private theorem add_two_cross_nonnegative_of_schur
    {L T C : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hC : C ^ 2 ≤ L * T) :
    0 ≤ L + 2 * C + T := by
  have hsum : 0 ≤ L + T := add_nonneg hL hT
  have hamgm : 4 * L * T ≤ (L + T) ^ 2 := by
    nlinarith [sq_nonneg (L - T)]
  have hsquares : (2 * |C|) ^ 2 ≤ (L + T) ^ 2 := by
    rw [mul_pow, sq_abs]
    nlinarith
  have habs0 : 0 ≤ 2 * |C| := mul_nonneg (by norm_num) (abs_nonneg C)
  have habs : 2 * |C| ≤ L + T :=
    (sq_le_sq₀ habs0 hsum).mp hsquares
  have hneg : -C ≤ |C| := neg_le_abs C
  nlinarith

/-- A genuine scalar Schur condition closes the sum of any two five-cell
profiles.  No positivity-definite inverse is used, so a semidefinite tail is
allowed. -/
theorem fiveCellEndpointOperator_add_nonnegative_of_schur
    (u v : ℝ → ℝ)
    (hu : 0 ≤ fiveCellEndpointOperator u)
    (hv : 0 ≤ fiveCellEndpointOperator v)
    (hcross : fiveCellEndpointOperatorCross u v ^ 2 ≤
      fiveCellEndpointOperator u * fiveCellEndpointOperator v) :
    0 ≤ fiveCellEndpointOperator (u + v) := by
  rw [fiveCellEndpointOperator_add]
  exact add_two_cross_nonnegative_of_schur hu hv hcross

/-- Canonical cutoff-nine low profile. -/
abbrev fiveCellCanonicalLow
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ → ℝ :=
  centeredLegendreLowProjection w hw 9

/-- Canonical residual above the ninth shifted-Legendre gap. -/
abbrev fiveCellCanonicalTail
    (w : ℝ → ℝ) (hw : Continuous w) : ℝ → ℝ :=
  centeredLegendreHigherResidual w hw 9

/-- The canonical higher residual is unconditionally positive for the
complete five-cell operator. -/
theorem fiveCellCanonicalTail_nonnegative
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w) :
    0 ≤ fiveCellEndpointOperator (fiveCellCanonicalTail w hw) := by
  apply fiveCellEndpointOperator_nonnegative_of_tailNine
  · exact continuous_centeredLegendreHigherResidual w hw 9
  · exact locallyLipschitzOn_centeredLegendreHigherResidual w hw hlocal 9
  · exact centeredLegendreHigherResidual_momentsVanishBelow w hw 9

/-- Exact canonical low--tail identity for the complete operator. -/
theorem fiveCellEndpointOperator_eq_canonicalLow_add_tail
    (w : ℝ → ℝ) (hw : Continuous w) :
    fiveCellEndpointOperator w =
      fiveCellEndpointOperator (fiveCellCanonicalLow w hw) +
        2 * fiveCellEndpointOperatorCross
          (fiveCellCanonicalLow w hw) (fiveCellCanonicalTail w hw) +
        fiveCellEndpointOperator (fiveCellCanonicalTail w hw) := by
  rw [← fiveCellEndpointOperator_add]
  rw [centeredLegendreLowProjection_add_higherResidual w hw 9]

/-- Exact remaining cutoff-nine criterion for one arbitrary profile: finite
low positivity plus the mixed scalar Schur contraction imply the full
five-cell operator inequality. -/
theorem fiveCellEndpointOperator_nonnegative_of_canonicalLowTailSchur
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (hlow : 0 ≤ fiveCellEndpointOperator (fiveCellCanonicalLow w hw))
    (hmixed : fiveCellEndpointOperatorCross
        (fiveCellCanonicalLow w hw) (fiveCellCanonicalTail w hw) ^ 2 ≤
      fiveCellEndpointOperator (fiveCellCanonicalLow w hw) *
        fiveCellEndpointOperator (fiveCellCanonicalTail w hw)) :
    0 ≤ fiveCellEndpointOperator w := by
  rw [← centeredLegendreLowProjection_add_higherResidual w hw 9]
  exact fiveCellEndpointOperator_add_nonnegative_of_schur
    (fiveCellCanonicalLow w hw) (fiveCellCanonicalTail w hw)
      hlow (fiveCellCanonicalTail_nonnegative w hw hlocal) hmixed

/-! ## Lossless return to five-cell production -/

/-- The normalized endpoint operator is exactly the five-cell Bombieri
functional after multiplication by the positive physical halfwidth. -/
theorem bombieriFunctional_fiveBlock_re_eq_halfWidth_mul_endpointOperator
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent) :
    (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterFiveBlock parent k))).re =
      fiveCellWholeHalfWidth k *
        fiveCellEndpointOperator (fiveCellNormalizedRealProfile parent k) := by
  rw [bombieriFunctional_fiveBlock_re_eq_centeredPhysical_sub_pairing
    parent k hparent]
  rw [fiveCellWholeHalfWidth_eq]
  rfl

/-- Universal positivity of the normalized endpoint operator on the actual
five-cell production profiles. -/
def RealFiveCellNormalizedEndpointOperatorNonnegative : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        0 ≤ fiveCellEndpointOperator
          (fiveCellNormalizedRealProfile parent k)

/-- The normalized endpoint formulation is losslessly equivalent to the
factor-two domination target, not merely a sufficient relaxation. -/
theorem realFiveCellNormalizedEndpointOperatorNonnegative_iff_factorTwoDomination :
    RealFiveCellNormalizedEndpointOperatorNonnegative ↔
      RealFiveCellFactorTwoDomination := by
  have hoperatorProduction :
      RealFiveCellNormalizedEndpointOperatorNonnegative ↔
        RealFiniteBlockProductionNonnegativeAtLength 5 := by
    constructor
    · intro h parent hparent k
      change 0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterFiveBlock parent k)
      unfold bombieriRealQuadraticValue
      rw [bombieriFunctional_fiveBlock_re_eq_halfWidth_mul_endpointOperator
        parent k hparent]
      exact mul_nonneg (fiveCellWholeHalfWidth_pos k).le
        (h parent hparent k)
    · intro h parent hparent k
      have hproduction := h parent hparent k
      change 0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterFiveBlock parent k) at hproduction
      unfold bombieriRealQuadraticValue at hproduction
      rw [bombieriFunctional_fiveBlock_re_eq_halfWidth_mul_endpointOperator
        parent k hparent] at hproduction
      exact (mul_nonneg_iff_of_pos_left (fiveCellWholeHalfWidth_pos k)).mp
        hproduction
  exact hoperatorProduction.trans
    realFiveCellFactorTwoDomination_iff_productionNonnegative.symm

/-- The exact remaining cutoff-nine Schur certificate, restricted to the
actual normalized five-cell production profiles. -/
def RealFiveCellProductionCanonicalLowTailSchur : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        let w := fiveCellNormalizedRealProfile parent k
        let hw : Continuous w :=
          (fiveCellNormalizedRealProfile_contDiff parent k).continuous
        0 ≤ fiveCellEndpointOperator (fiveCellCanonicalLow w hw) ∧
          fiveCellEndpointOperatorCross
              (fiveCellCanonicalLow w hw) (fiveCellCanonicalTail w hw) ^ 2 ≤
            fiveCellEndpointOperator (fiveCellCanonicalLow w hw) *
              fiveCellEndpointOperator (fiveCellCanonicalTail w hw)

/-- The production-restricted canonical Schur certificate closes the exact
five-cell factor-two domination statement. -/
theorem realFiveCellFactorTwoDomination_of_productionCanonicalLowTailSchur
    (hcert : RealFiveCellProductionCanonicalLowTailSchur) :
    RealFiveCellFactorTwoDomination := by
  apply realFiveCellNormalizedEndpointOperatorNonnegative_iff_factorTwoDomination.mp
  intro parent hparent k
  let w := fiveCellNormalizedRealProfile parent k
  let hw : Continuous w :=
    (fiveCellNormalizedRealProfile_contDiff parent k).continuous
  have hcert' := hcert parent hparent k
  change 0 ≤ fiveCellEndpointOperator w
  exact fiveCellEndpointOperator_nonnegative_of_canonicalLowTailSchur
    w hw (fiveCellNormalizedRealProfile_locallyLipschitzOn parent k)
      hcert'.1 hcert'.2

end

end ArithmeticHodge.Analysis.YoshidaFiveCellCanonicalLowTailSchurStructural
