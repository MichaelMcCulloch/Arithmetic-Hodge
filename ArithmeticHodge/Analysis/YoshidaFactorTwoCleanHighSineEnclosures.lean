import ArithmeticHodge.Analysis.RationalIntervalWidth
import ArithmeticHodge.Analysis.YoshidaEvenSineHighEnclosures

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoCleanHighSineEnclosures

noncomputable section

open RatInterval
open YoshidaEvenSineHighEnclosures
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures

/-!
# Fine clean sine-moment enclosures at frequencies 191 through 200

The cubic high-frequency digamma enclosure, with twenty dyadic correction
terms, is already narrower than `10⁻⁹` on this ten-mode band.  These explicit
outward-rounded targets include the extra frequency `200` introduced by the
endpoint-adapted factor-two clean block.
-/

/-- Outward-rounded `10⁻¹⁵`-grid targets for the ten highest clean sine
moments needed by the endpoint-adapted factor-two block. -/
def yoshidaFactorTwoCleanHighSineTargets : ℕ → RatInterval
  | 191 =>
      ⟨-1570136167416891 / 1000000000000000,
        -1570136166421259 / 1000000000000000⟩
  | 192 =>
      ⟨-1570139605730174 / 1000000000000000,
        -1570139604750018 / 1000000000000000⟩
  | 193 =>
      ⟨-1570143008413527 / 1000000000000000,
        -1570143007448526 / 1000000000000000⟩
  | 194 =>
      ⟨-1570146376017924 / 1000000000000000,
        -1570146375067767 / 1000000000000000⟩
  | 195 =>
      ⟨-1570149709083034 / 1000000000000000,
        -1570149708147419 / 1000000000000000⟩
  | 196 =>
      ⟨-1570153008137515 / 1000000000000000,
        -1570153007216147 / 1000000000000000⟩
  | 197 =>
      ⟨-1570156273699292 / 1000000000000000,
        -1570156272791882 / 1000000000000000⟩
  | 198 =>
      ⟨-1570159506275824 / 1000000000000000,
        -1570159505382092 / 1000000000000000⟩
  | 199 =>
      ⟨-1570162706364372 / 1000000000000000,
        -1570162705484045 / 1000000000000000⟩
  | 200 =>
      ⟨-1570165874452251 / 1000000000000000,
        -1570165873585062 / 1000000000000000⟩
  | _ => pure 0

/-- The exact high-frequency series interval at cutoff `20` lies in its
compact clean target throughout modes `191, ..., 200`. -/
theorem highSineSeriesInterval_twenty_sub_cleanTarget
    {n : ℕ} (hn191 : 191 ≤ n) (hn200 : n ≤ 200) :
    IsSubinterval (highSineSeriesInterval n 20)
      (yoshidaFactorTwoCleanHighSineTargets n) := by
  set_option maxRecDepth 1000000 in
    set_option maxHeartbeats 1000000000 in
      interval_cases n <;> decide +kernel

/-- Every high clean target has width at most `10⁻⁹`. -/
theorem yoshidaFactorTwoCleanHighSineTarget_width_le
    {n : ℕ} (hn191 : 191 ≤ n) (hn200 : n ≤ 200) :
    width (yoshidaFactorTwoCleanHighSineTargets n) ≤
      (1 / 1000000000 : ℚ) := by
  interval_cases n <;> decide +kernel

/-- The fine rational target at each mode `191, ..., 200` contains the actual
analytic sine moment. -/
theorem yoshidaFactorTwoCleanHighSineTarget_contains
    (n : ℕ) (hn191 : 191 ≤ n) (hn200 : n ≤ 200) :
    (yoshidaFactorTwoCleanHighSineTargets n).Contains
      (yoshidaSineMoment n) := by
  exact contains_of_subinterval
    (highSineSeriesInterval_twenty_sub_cleanTarget hn191 hn200)
    (highSineSeriesInterval_contains (by omega) 20)

/-- In particular, the new endpoint-adaptation moment `S₂₀₀` inhabits its
fine rational target. -/
theorem yoshidaFactorTwoCleanHighSineTarget_200_contains :
    (yoshidaFactorTwoCleanHighSineTargets 200).Contains
      (yoshidaSineMoment 200) := by
  exact yoshidaFactorTwoCleanHighSineTarget_contains 200 (by norm_num)
    (by norm_num)

/-- Complete fine-enclosure obligation for the ten high clean sine modes. -/
def YoshidaFactorTwoCleanHighSineTargetEnclosures : Prop :=
  ∀ n, 191 ≤ n → n ≤ 200 →
    (yoshidaFactorTwoCleanHighSineTargets n).Contains
      (yoshidaSineMoment n)

/-- The explicit targets discharge the complete high clean sine enclosure
package, including `S₂₀₀`. -/
theorem yoshidaFactorTwoCleanHighSineTargetEnclosures :
    YoshidaFactorTwoCleanHighSineTargetEnclosures := by
  intro n hn191 hn200
  exact yoshidaFactorTwoCleanHighSineTarget_contains n hn191 hn200

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoCleanHighSineEnclosures
