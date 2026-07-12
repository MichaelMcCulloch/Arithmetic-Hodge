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

These millesimal rational boxes contain the independently evaluated values of
Yoshida's first ten sine and diagonal moments.  The finite arithmetic theorem
below proves that the boxes are already narrow enough for every interval Schur
pivot to be positive.  Containment of the analytic moments in the boxes
remains an explicit proof obligation.
-/

/-- Target enclosures for `S_1, ..., S_10`.  Values outside that finite range
are irrelevant to the full odd Gram and are set to the singleton zero. -/
def yoshidaOddSineIntervals : ℕ → RatInterval
  | 1 => ⟨-1452 / 1000, -1450 / 1000⟩
  | 2 => ⟨-1510 / 1000, -1507 / 1000⟩
  | 3 => ⟨-1531 / 1000, -1528 / 1000⟩
  | 4 => ⟨-1541 / 1000, -1538 / 1000⟩
  | 5 => ⟨-1547 / 1000, -1544 / 1000⟩
  | 6 => ⟨-1551 / 1000, -1548 / 1000⟩
  | 7 => ⟨-1554 / 1000, -1551 / 1000⟩
  | 8 => ⟨-1557 / 1000, -1553 / 1000⟩
  | 9 => ⟨-1559 / 1000, -1555 / 1000⟩
  | 10 => ⟨-1560 / 1000, -1557 / 1000⟩
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
