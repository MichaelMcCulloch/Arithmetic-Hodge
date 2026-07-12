import ArithmeticHodge.Analysis.YoshidaOddIntervalCertificate

set_option autoImplicit false

open scoped ComplexOrder

namespace ArithmeticHodge.Analysis.YoshidaOddMomentTargets

noncomputable section

open RatInterval
open RationalIntervalSchur
open YoshidaOddGramPrefix
open YoshidaOddIntervalCertificate

/-!
# Kernel-checked targets for the full odd moment block

These rational boxes contain the independently evaluated values of Yoshida's
first ten sine and diagonal moments.  The sine boxes deliberately retain about
one centesimal of analytic slack: the finite arithmetic theorem below proves
that this still leaves every interval Schur pivot positive, while permitting a
shorter exact Cauchy-series certificate.  Containment of the analytic moments
in the boxes remains an explicit proof obligation.
-/

/-- Target enclosures for `S_1, ..., S_10`.  Values outside that finite range
are irrelevant to the full odd Gram and are set to the singleton zero. -/
def yoshidaOddSineIntervals : ℕ → RatInterval
  | 1 => ⟨-1461 / 1000, -1441 / 1000⟩
  | 2 => ⟨-1519 / 1000, -1498 / 1000⟩
  | 3 => ⟨-1540 / 1000, -1518 / 1000⟩
  | 4 => ⟨-1550 / 1000, -1528 / 1000⟩
  | 5 => ⟨-1556 / 1000, -1535 / 1000⟩
  | 6 => ⟨-1560 / 1000, -1539 / 1000⟩
  | 7 => ⟨-1563 / 1000, -1542 / 1000⟩
  | 8 => ⟨-1565 / 1000, -1544 / 1000⟩
  | 9 => ⟨-1567 / 1000, -1545 / 1000⟩
  | 10 => ⟨-1568 / 1000, -1547 / 1000⟩
  | _ => pure 0

/-- Target enclosures for `D_1, ..., D_10`. -/
def yoshidaOddDiagonalIntervals : ℕ → RatInterval
  | 1 => ⟨382 / 1000, 385 / 1000⟩
  | 2 => ⟨1063 / 1000, 1066 / 1000⟩
  | 3 => ⟨1466 / 1000, 1469 / 1000⟩
  | 4 => ⟨1753 / 1000, 1755 / 1000⟩
  | 5 => ⟨1975 / 1000, 1978 / 1000⟩
  | 6 => ⟨2157 / 1000, 2160 / 1000⟩
  | 7 => ⟨2311 / 1000, 2314 / 1000⟩
  | 8 => ⟨2445 / 1000, 2448 / 1000⟩
  | 9 => ⟨2563 / 1000, 2565 / 1000⟩
  | 10 => ⟨2668 / 1000, 2671 / 1000⟩
  | _ => pure 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Exact kernel evaluation: all ten interval Schur pivots are positive. -/
theorem yoshidaOddTarget_intervalPivots :
    PositivePivots oddPivotOrder
      (oddMomentIntervalGram yoshidaOddSineIntervals
        yoshidaOddDiagonalIntervals) := by
  decide +kernel

/-- The finite analytic sine-moment enclosure obligation. -/
def YoshidaOddSineTargetEnclosures : Prop :=
  ∀ n, 1 ≤ n → n ≤ 10 →
    (yoshidaOddSineIntervals n).Contains (yoshidaSineMoment n)

/-- The finite analytic diagonal-moment enclosure obligation. -/
def YoshidaOddDiagonalTargetEnclosures : Prop :=
  ∀ n, 1 ≤ n → n ≤ 10 →
    (yoshidaOddDiagonalIntervals n).Contains (yoshidaDiagonalMoment n)

/-- The clipped/moment bridge and the two finite enclosure packages imply
positive definiteness of the complete production odd block. -/
theorem clippedOddFullGram_posDef_of_bridge_and_target_enclosures
    (hbridge : ClippedOddFullMomentBridge)
    (hS : YoshidaOddSineTargetEnclosures)
    (hD : YoshidaOddDiagonalTargetEnclosures) :
    clippedOddFullGram.PosDef :=
  clippedOddFullGram_posDef_of_bridge_and_intervalPivots
    yoshidaOddSineIntervals yoshidaOddDiagonalIntervals
    hbridge hS hD yoshidaOddTarget_intervalPivots

end

end ArithmeticHodge.Analysis.YoshidaOddMomentTargets
