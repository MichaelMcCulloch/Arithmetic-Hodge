import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailRadiusStructural

set_option autoImplicit false

open Complex Matrix Real
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailReserveGluingStructural

noncomputable section

open ArithmeticHodge.Analysis
open FormSpace
open TwoByTwoSchur
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyClosureStructural
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailRadiusStructural
open YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseTailRealImagStructural
open YoshidaOddHomogeneousCoercivity
open YoshidaWeightedTailBounds

/-!
# Gluing the canonical low block with the quantitative tail reserve

The cutoff tail theorem is stronger than mere nonnegativity: at every disk
phase it leaves `1 / 200` of the clean tail diagonal unused.  This file
separates that nonnegative residual from the full real low--tail phase.

Consequently, a proof using *only* the established tail theorem has one
sharp remaining target: the finite-low phase plus twice the physical mixed
functional plus `1 / 200` of the clean tail diagonal.  Homogenizing that
target gives the exact scalar Schur condition, with no numerical enclosure
or finite search.
-/

/-- The concrete finite-low phase at one disk point. -/
def canonicalPhasePhysicalRealLowValue
    (c : FactorTwoPhaseLowIndex → ℝ) (a b : ℝ) : ℝ :=
  c ⬝ᵥ (canonicalPhaseLowMatrix a b *ᵥ c)

/-- The clean diagonal of the pointwise-real canonical tail channel. -/
def canonicalPhasePhysicalRealTailCleanSum
    (x : CanonicalPhaseTailCore) : ℝ :=
  factorTwoEndpointChannelCleanSum
    (canonicalPhaseTailEvenRealProfile x)
    (canonicalPhaseTailOddRealProfile x)

/-- The complete pointwise-real canonical tail phase. -/
def canonicalPhasePhysicalRealTailValue
    (x : CanonicalPhaseTailCore) (a b : ℝ) : ℝ :=
  factorTwoEndpointChannelPhase
    (canonicalPhaseTailEvenRealProfile x)
    (canonicalPhaseTailOddRealProfile x) a b

/-- The part of the tail phase left after reserving exactly `1 / 200` of its
clean diagonal for gluing to the low block. -/
def canonicalPhasePhysicalRealTailReserveResidual
    (x : CanonicalPhaseTailCore) (a b : ℝ) : ℝ :=
  canonicalPhasePhysicalRealTailValue x a b -
    (1 / 200 : ℝ) * canonicalPhasePhysicalRealTailCleanSum x

/-- The weakest homogeneous low/mixed expression which can be proved
nonnegative using only the uniform `1 / 200` tail reserve. -/
def canonicalPhasePhysicalRealReserveReducedValue
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) : ℝ :=
  canonicalPhasePhysicalRealLowValue c a b +
    2 * canonicalPhaseLowTailRealMixed c x a b +
    (1 / 200 : ℝ) * canonicalPhasePhysicalRealTailCleanSum x

private theorem evenTailRealPart_is_real
    (x : CanonicalPhaseTailCore) (t : ℝ) :
    (evenOneNinetyNineTailToClippedSmooth
      (evenTailRealPart x.fst.toV) t).im = 0 := by
  change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).re : ℝ) :
    ℂ)).im) = 0
  simp

private theorem oddTailRealPart_is_real
    (x : CanonicalPhaseTailCore) (t : ℝ) :
    (oddTenTailToClippedSmooth (oddTailRealPart x.snd.toV) t).im = 0 := by
  change (((((oddTenTailToClippedSmooth x.snd.toV t).re : ℝ) : ℂ)).im) = 0
  simp

/-- The production tail theorem supplies the exact reserve used below. -/
theorem canonicalPhasePhysicalRealTail_reserve
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    (1 / 200 : ℝ) * canonicalPhasePhysicalRealTailCleanSum x ≤
      canonicalPhasePhysicalRealTailValue x a b := by
  simpa only [canonicalPhasePhysicalRealTailCleanSum,
    canonicalPhasePhysicalRealTailValue,
    canonicalPhaseTailEvenRealProfile,
    canonicalPhaseTailOddRealProfile,
    boundaryCanonicalEvenTailProfile, canonicalOddTailProfile] using
    boundaryContinuous_tail_phase_uniform_clean_reserve
      (evenTailRealPart x.fst.toV) (oddTailRealPart x.snd.toV)
      (evenTailRealPart x.fst.toV).property
      (oddTailRealPart x.snd.toV).property
      (evenTailRealPart_is_real x) (oddTailRealPart_is_real x)
      a b hphase

/-- In particular, the clean tail diagonal and its reserved fraction are
nonnegative. -/
theorem canonicalPhasePhysicalRealTailCleanSum_nonneg
    (x : CanonicalPhaseTailCore) :
    0 ≤ canonicalPhasePhysicalRealTailCleanSum x := by
  have h := canonicalPhasePhysicalRealTail_reserve x 0 0 (by norm_num)
  unfold canonicalPhasePhysicalRealTailValue factorTwoEndpointChannelPhase at h
  norm_num at h
  change (1 / 200 : ℝ) * canonicalPhasePhysicalRealTailCleanSum x ≤
    canonicalPhasePhysicalRealTailCleanSum x at h
  nlinarith

theorem canonicalPhasePhysicalRealTailReserve_nonneg
    (x : CanonicalPhaseTailCore) :
    0 ≤ (1 / 200 : ℝ) * canonicalPhasePhysicalRealTailCleanSum x := by
  exact mul_nonneg (by norm_num) (canonicalPhasePhysicalRealTailCleanSum_nonneg x)

/-- The tail residual remaining after the reserve is spent is nonnegative at
every disk phase. -/
theorem canonicalPhasePhysicalRealTailReserveResidual_nonneg
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ canonicalPhasePhysicalRealTailReserveResidual x a b := by
  unfold canonicalPhasePhysicalRealTailReserveResidual
  exact sub_nonneg.mpr (canonicalPhasePhysicalRealTail_reserve x a b hphase)

/-- Exact reserve decomposition of the full physical real channel.  The
first summand is the only unresolved one; the second is already nonnegative
by the tail theorem. -/
theorem canonicalPhasePhysicalRealLowTailValue_eq_reserveReduced_add_residual
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    canonicalPhasePhysicalRealLowTailValue c x a b =
      canonicalPhasePhysicalRealReserveReducedValue c x a b +
        canonicalPhasePhysicalRealTailReserveResidual x a b := by
  have hexpanded := canonicalPhasePhysicalRealLowTailValue_eq_expanded
    c x a b hphase
  unfold CanonicalPhasePhysicalRealLowTailAssembly at hexpanded
  rw [hexpanded]
  unfold canonicalPhaseRealLowTailExpandedValue
    canonicalPhasePhysicalRealReserveReducedValue
    canonicalPhasePhysicalRealTailReserveResidual
    canonicalPhasePhysicalRealLowValue
    canonicalPhasePhysicalRealTailValue
  rw [canonicalPhaseLowTailRealMixed_eq_completed_sum c x a b hphase]
  ring

/-- Reserve gluing: nonnegativity of the reserve-reduced form closes the
literal real low-plus-tail phase. -/
theorem canonicalPhasePhysicalRealLowTailValue_nonneg_of_reserveReduced
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hreduced : 0 ≤ canonicalPhasePhysicalRealReserveReducedValue c x a b) :
    0 ≤ canonicalPhasePhysicalRealLowTailValue c x a b := by
  rw [canonicalPhasePhysicalRealLowTailValue_eq_reserveReduced_add_residual
    c x a b hphase]
  exact add_nonneg hreduced
    (canonicalPhasePhysicalRealTailReserveResidual_nonneg x a b hphase)

/-- At fixed low and tail vectors, the reserve-reduced target is exactly the
one-sided lower bound on the mixed functional.  No smaller right-hand reserve
can be inferred from the current tail theorem alone. -/
theorem canonicalPhasePhysicalRealReserveReducedValue_nonneg_iff_mixed_lower
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) :
    0 ≤ canonicalPhasePhysicalRealReserveReducedValue c x a b ↔
      -(canonicalPhasePhysicalRealLowValue c a b +
          (1 / 200 : ℝ) * canonicalPhasePhysicalRealTailCleanSum x) / 2 ≤
        canonicalPhaseLowTailRealMixed c x a b := by
  unfold canonicalPhasePhysicalRealReserveReducedValue
  constructor <;> intro h <;> linarith

/-- Homogenizing the reserve-reduced target gives its exact, division-free
Schur criterion.  This is the weakest sign-insensitive mixed estimate
available from the `1 / 200` reserve. -/
theorem canonicalPhasePhysicalRealReservePencil_nonneg_iff
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) :
    (∀ r s : ℝ, 0 ≤
      canonicalPhasePhysicalRealLowValue c a b * r ^ 2 +
        2 * canonicalPhaseLowTailRealMixed c x a b * r * s +
        ((1 / 200 : ℝ) * canonicalPhasePhysicalRealTailCleanSum x) * s ^ 2) ↔
      0 ≤ canonicalPhasePhysicalRealLowValue c a b ∧
        canonicalPhaseLowTailRealMixed c x a b ^ 2 ≤
          canonicalPhasePhysicalRealLowValue c a b *
            ((1 / 200 : ℝ) * canonicalPhasePhysicalRealTailCleanSum x) := by
  rw [real_quadratic_pencil_nonneg_iff]
  constructor
  · rintro ⟨hLow, _hReserve, hMixed⟩
    exact ⟨hLow, hMixed⟩
  · rintro ⟨hLow, hMixed⟩
    exact ⟨hLow, canonicalPhasePhysicalRealTailReserve_nonneg x, hMixed⟩

/-- Concrete reserve-Schur closure.  Relative to the already-proved tail
theorem, these two inequalities are enough for the real low-plus-tail phase;
the second is the single remaining mixed estimate. -/
theorem canonicalPhasePhysicalRealLowTailValue_nonneg_of_reserveSchur
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hLow : 0 ≤ canonicalPhasePhysicalRealLowValue c a b)
    (hMixed : canonicalPhaseLowTailRealMixed c x a b ^ 2 ≤
      canonicalPhasePhysicalRealLowValue c a b *
        ((1 / 200 : ℝ) * canonicalPhasePhysicalRealTailCleanSum x)) :
    0 ≤ canonicalPhasePhysicalRealLowTailValue c x a b := by
  apply canonicalPhasePhysicalRealLowTailValue_nonneg_of_reserveReduced
    c x a b hphase
  unfold canonicalPhasePhysicalRealReserveReducedValue
  exact scalar_low_tail_nonneg _ _ _ hLow
    (canonicalPhasePhysicalRealTailReserve_nonneg x) hMixed

/-- Uniform reserve-reduced positivity is already enough for the exact
phase-free physical radius target. -/
theorem canonicalPhasePhysicalRealLowTail_radius_of_reserveReduced
    (hreduced : ∀ (c : FactorTwoPhaseLowIndex → ℝ)
        (x : CanonicalPhaseTailCore) (a b : ℝ),
      a ^ 2 + b ^ 2 ≤ 1 →
        0 ≤ canonicalPhasePhysicalRealReserveReducedValue c x a b) :
    ∀ (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore),
      0 ≤ canonicalPhasePhysicalRealLowTailCleanSum c x ∧
        Complex.normSq (canonicalPhasePhysicalRealLowTailCoordinate c x) ≤
          canonicalPhasePhysicalRealLowTailCleanSum c x ^ 2 := by
  intro c x
  let u := factorTwoBoundaryCanonicalEvenLowProfile
      (canonicalPhaseLowEvenCoefficients c) +
    canonicalPhaseTailEvenRealProfile x
  let v := factorTwoOddLowSynthesis (canonicalPhaseLowOddCoefficients c) +
    canonicalPhaseTailOddRealProfile x
  have hnonneg : ∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ 1 →
      0 ≤ factorTwoEndpointChannelCleanSum u v +
        a * factorTwoEndpointChannelSymmetricSum u v +
        b * factorTwoCenteredAlternatingCoupling u v := by
    intro a b hphase
    have hfull := canonicalPhasePhysicalRealLowTailValue_nonneg_of_reserveReduced
      c x a b hphase (hreduced c x a b hphase)
    simpa only [canonicalPhasePhysicalRealLowTailValue,
      factorTwoEndpointChannelPhase, u, v] using hfull
  have hradius :=
    (factorTwoEndpointChannel_phase_nonneg_iff_radius u v).1 hnonneg
  simpa only [canonicalPhasePhysicalRealLowTailCleanSum,
    canonicalPhasePhysicalRealLowTailCoordinate, u, v] using hradius

/-- Division-free reserve-Schur estimates for every disk phase therefore
close the physical real-channel radius. -/
theorem canonicalPhasePhysicalRealLowTail_radius_of_reserveSchur
    (hLow : ∀ (c : FactorTwoPhaseLowIndex → ℝ) (a b : ℝ),
      a ^ 2 + b ^ 2 ≤ 1 →
        0 ≤ canonicalPhasePhysicalRealLowValue c a b)
    (hMixed : ∀ (c : FactorTwoPhaseLowIndex → ℝ)
        (x : CanonicalPhaseTailCore) (a b : ℝ),
      a ^ 2 + b ^ 2 ≤ 1 →
        canonicalPhaseLowTailRealMixed c x a b ^ 2 ≤
          canonicalPhasePhysicalRealLowValue c a b *
            ((1 / 200 : ℝ) * canonicalPhasePhysicalRealTailCleanSum x)) :
    ∀ (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore),
      0 ≤ canonicalPhasePhysicalRealLowTailCleanSum c x ∧
        Complex.normSq (canonicalPhasePhysicalRealLowTailCoordinate c x) ≤
          canonicalPhasePhysicalRealLowTailCleanSum c x ^ 2 := by
  apply canonicalPhasePhysicalRealLowTail_radius_of_reserveReduced
  intro c x a b hphase
  unfold canonicalPhasePhysicalRealReserveReducedValue
  exact scalar_low_tail_nonneg _ _ _ (hLow c a b hphase)
    (canonicalPhasePhysicalRealTailReserve_nonneg x)
    (hMixed c x a b hphase)

/-- The same reserve-reduced target feeds directly into the production
corrected-Gram disk problem, with no additional analytic hypothesis. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_disk_posSemidef_of_reserveReduced
    (hreduced : ∀ (c : FactorTwoPhaseLowIndex → ℝ)
        (x : CanonicalPhaseTailCore) (a b : ℝ),
      a ^ 2 + b ^ 2 ≤ 1 →
        0 ≤ canonicalPhasePhysicalRealReserveReducedValue c x a b) :
    ∀ (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1),
      Matrix.PosSemidef
        (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) := by
  exact
    completedCanonicalPhaseLowTailRealCorrectedGram_disk_posSemidef_iff_real_radius.2
      (canonicalPhasePhysicalRealLowTail_radius_of_reserveReduced hreduced)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailReserveGluingStructural
