import ArithmeticHodge.Analysis.YoshidaClippedMomentBridge
import ArithmeticHodge.Analysis.YoshidaOddMomentTargets

set_option autoImplicit false

open Complex MeasureTheory
open scoped ComplexOrder

namespace ArithmeticHodge.Analysis.YoshidaClippedMomentBridgeFull

noncomputable section

open YoshidaClippedMomentBridge
open YoshidaOddGramPrefix
open YoshidaOddIntervalCertificate
open YoshidaOddMomentTargets

/-!
# Full odd clipped/moment bridge interface

The correlation and moment algebra proved for arbitrary positive frequencies
is assembled here for all ten odd low modes.  The two genuine analytic
boundaries remain explicit: the spectral-to-admissible-distribution identity
and integrability of the twenty removable scalar moment integrands.
-/

/-- Spectral-to-admissible-distribution boundary for all ten odd modes. -/
def ClippedOddFullAdmissibleDistributionBridge : Prop :=
  ∀ i j : YoshidaOddIndex,
    clippedOddFullGram i j =
      (clippedOddAdmissibleRealSpaceGram (i.1 + 1) (j.1 + 1) : ℂ)

/-- Removable-integrand boundary for all twenty scalar moment integrands. -/
def ClippedOddFullMomentIntegrable : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ 10 →
    IntervalIntegrable (yoshidaSineMomentIntegrand n)
        MeasureTheory.volume 0 yoshidaLength ∧
      IntervalIntegrable (yoshidaDiagonalMomentIntegrand n)
        MeasureTheory.volume 0 yoshidaLength

/-- The full production clipped/moment bridge follows from the remaining
spectral-to-distribution theorem and the twenty removable integrals. -/
theorem clippedOddFullMomentBridge_of_admissibleDistributionBridge
    (hdist : ClippedOddFullAdmissibleDistributionBridge)
    (hint : ClippedOddFullMomentIntegrable) :
    ClippedOddFullMomentBridge := by
  intro i j
  rw [hdist i j]
  norm_cast
  unfold oddMomentFullGram
  have hni : (i.1 + 1 : ℕ) ≠ 0 := by omega
  have hnj : (j.1 + 1 : ℕ) ≠ 0 := by omega
  have hiLe : i.1 + 1 ≤ 10 := by omega
  have hjLe : j.1 + 1 ≤ 10 := by omega
  have hiInt := hint (i.1 + 1) (by omega) hiLe
  have hjInt := hint (j.1 + 1) (by omega) hjLe
  by_cases hnm : i.1 + 1 = j.1 + 1
  · rw [← hnm]
    exact clippedOddAdmissibleRealSpaceGram_diag_eq_oddMomentGram
      hni hiInt.1 hiInt.2
  · exact clippedOddAdmissibleRealSpaceGram_offdiag_eq_oddMomentGram
      hni hnj hnm hiInt.1 hjInt.1

/-- The full admissible-distribution bridge, removable integrability, and
finite target moment enclosures imply positivity of the actual odd block. -/
theorem clippedOddFullGram_posDef_of_admissibleDistributionBridge
    (hdist : ClippedOddFullAdmissibleDistributionBridge)
    (hint : ClippedOddFullMomentIntegrable)
    (hS : YoshidaOddSineTargetEnclosures)
    (hD : YoshidaOddDiagonalTargetEnclosures) :
    clippedOddFullGram.PosDef :=
  clippedOddFullGram_posDef_of_bridge_and_target_enclosures
    (clippedOddFullMomentBridge_of_admissibleDistributionBridge hdist hint)
    hS hD

end

end ArithmeticHodge.Analysis.YoshidaClippedMomentBridgeFull
