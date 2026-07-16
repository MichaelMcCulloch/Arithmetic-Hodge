import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalTailDiagonalStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEndpointOddCleanPositive
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseTailRealImagStructural
open YoshidaOddHomogeneousCoercivity
open YoshidaWeightedTailBounds

/-!
# Coercive diagonal of the canonical complex phase-tail core

The complex carrier is treated as two real phase copies.  The standard-tail
reserve applies independently to its pointwise real and imaginary
coordinates.  The exact critical-norm identity then gives phase coercivity
and the matching flipped-phase upper bound with no endpoint adaptation.
-/

/-- Sum of the fixed-disk phase diagonals on the real and imaginary tail
coordinates. -/
def canonicalPhaseTailCoreDiagonal
    (x : CanonicalPhaseTailCore) (a b : ℝ) : ℝ :=
  factorTwoEndpointChannelPhase
      (canonicalPhaseTailEvenRealProfile x)
      (canonicalPhaseTailOddRealProfile x) a b +
    factorTwoEndpointChannelPhase
      (canonicalPhaseTailEvenImagProfile x)
      (canonicalPhaseTailOddImagProfile x) a b

private theorem canonicalPhaseTailCore_clean_reserve
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    (1 / 200 : ℝ) *
        (factorTwoEndpointChannelCleanSum
            (canonicalPhaseTailEvenRealProfile x)
            (canonicalPhaseTailOddRealProfile x) +
         factorTwoEndpointChannelCleanSum
            (canonicalPhaseTailEvenImagProfile x)
            (canonicalPhaseTailOddImagProfile x)) ≤
      canonicalPhaseTailCoreDiagonal x a b := by
  have hr := boundaryContinuous_tail_phase_uniform_clean_reserve
    (evenTailRealPart x.fst.toV : YoshidaClippedPeriodicCore yoshidaA)
    (oddTailRealPart x.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
    (evenTailRealPart x.fst.toV).property
    (oddTailRealPart x.snd.toV).property
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).re :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth x.snd.toV t).re :
        ℝ) : ℂ)).im) = 0
      simp)
    a b hphase
  have hi := boundaryContinuous_tail_phase_uniform_clean_reserve
    (evenTailImagPart x.fst.toV : YoshidaClippedPeriodicCore yoshidaA)
    (oddTailImagPart x.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
    (evenTailImagPart x.fst.toV).property
    (oddTailImagPart x.snd.toV).property
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).im :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth x.snd.toV t).im :
        ℝ) : ℂ)).im) = 0
      simp)
    a b hphase
  change (1 / 200 : ℝ) *
      factorTwoEndpointChannelCleanSum
          (canonicalPhaseTailEvenRealProfile x)
          (canonicalPhaseTailOddRealProfile x) ≤
    factorTwoEndpointChannelPhase
      (canonicalPhaseTailEvenRealProfile x)
      (canonicalPhaseTailOddRealProfile x) a b at hr
  change (1 / 200 : ℝ) *
      factorTwoEndpointChannelCleanSum
          (canonicalPhaseTailEvenImagProfile x)
          (canonicalPhaseTailOddImagProfile x) ≤
    factorTwoEndpointChannelPhase
      (canonicalPhaseTailEvenImagProfile x)
      (canonicalPhaseTailOddImagProfile x) a b at hi
  change (1 / 200 : ℝ) * (_ + _) ≤ _ + _
  calc
    (1 / 200 : ℝ) * (_ + _) =
        (1 / 200 : ℝ) *
            factorTwoEndpointChannelCleanSum
              (canonicalPhaseTailEvenRealProfile x)
              (canonicalPhaseTailOddRealProfile x) +
          (1 / 200 : ℝ) *
            factorTwoEndpointChannelCleanSum
              (canonicalPhaseTailEvenImagProfile x)
              (canonicalPhaseTailOddImagProfile x) := by ring
    _ ≤ _ := add_le_add hr hi

/-- Uniform coercivity of the complete complex phase-tail diagonal in the
critical product norm. -/
theorem canonicalPhaseTailCoreDiagonal_coercive
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    (1 / (200 * yoshidaA) : ℝ) * ‖x‖ ^ 2 ≤
      canonicalPhaseTailCoreDiagonal x a b := by
  have hreserve := canonicalPhaseTailCore_clean_reserve x a b hphase
  have hnorm := canonicalPhaseTailCore_norm_sq_eq_clean_real_add_imag x
  rw [hnorm]
  field_simp [yoshidaA_pos.ne']
  nlinarith [hreserve]

/-- Reversing the disk phase turns the lower reserve into a uniform upper
bound for the original phase. -/
theorem canonicalPhaseTailCoreDiagonal_upper
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    canonicalPhaseTailCoreDiagonal x a b ≤
      (399 / (200 * yoshidaA) : ℝ) * ‖x‖ ^ 2 := by
  have hphaseNeg : (-a) ^ 2 + (-b) ^ 2 ≤ 1 := by
    simpa only [neg_sq] using hphase
  have hneg := canonicalPhaseTailCore_clean_reserve x (-a) (-b) hphaseNeg
  have hsum : canonicalPhaseTailCoreDiagonal x a b +
      canonicalPhaseTailCoreDiagonal x (-a) (-b) =
      2 * (factorTwoEndpointChannelCleanSum
          (canonicalPhaseTailEvenRealProfile x)
          (canonicalPhaseTailOddRealProfile x) +
        factorTwoEndpointChannelCleanSum
          (canonicalPhaseTailEvenImagProfile x)
          (canonicalPhaseTailOddImagProfile x)) := by
    unfold canonicalPhaseTailCoreDiagonal factorTwoEndpointChannelPhase
      factorTwoEndpointChannelSymmetricSum
    ring
  have hclean := canonicalPhaseTailCore_norm_sq_eq_clean_real_add_imag x
  let Q := factorTwoEndpointChannelCleanSum
      (canonicalPhaseTailEvenRealProfile x)
      (canonicalPhaseTailOddRealProfile x) +
    factorTwoEndpointChannelCleanSum
      (canonicalPhaseTailEvenImagProfile x)
      (canonicalPhaseTailOddImagProfile x)
  have hneg' : (1 / 200 : ℝ) * Q ≤
      canonicalPhaseTailCoreDiagonal x (-a) (-b) := by
    simpa only [Q] using hneg
  have hsum' : canonicalPhaseTailCoreDiagonal x a b +
      canonicalPhaseTailCoreDiagonal x (-a) (-b) = 2 * Q := by
    simpa only [Q] using hsum
  have hnorm' : ‖x‖ ^ 2 = yoshidaA * Q := by
    simpa only [Q] using hclean
  rw [hnorm']
  field_simp [yoshidaA_pos.ne']
  nlinarith

theorem canonicalPhaseTailCoreDiagonal_nonneg
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ canonicalPhaseTailCoreDiagonal x a b := by
  have h := canonicalPhaseTailCoreDiagonal_coercive x a b hphase
  have hcoef : 0 ≤ (1 / (200 * yoshidaA) : ℝ) := by
    exact div_nonneg (by norm_num)
      (mul_nonneg (by norm_num) yoshidaA_pos.le)
  exact (mul_nonneg hcoef (sq_nonneg _)).trans h

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalTailDiagonalStructural
