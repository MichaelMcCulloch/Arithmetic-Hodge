import ArithmeticHodge.Analysis.YoshidaOddHighSineBounds
import ArithmeticHodge.Analysis.YoshidaOddLowHighDecay

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaOddCouplingClosed

open YoshidaOddLowHighDecay
open YoshidaOddGramPrefix

/-!
# Unconditional closure of the odd low/high coupling budget

The analytic high sine-moment window is now a theorem, so the exact clipped
pairing decay and its complete infinite coupling budget no longer require a
premise.
-/

theorem highSineBounds : YoshidaOddHighSineBounds := by
  intro n hn
  exact YoshidaOddHighSineBounds.yoshida_high_sine_bounds n hn

theorem odd_low_high_pairing_decay
    (i : YoshidaOddIndex) (k : ℕ) :
    ‖yoshidaClippedLocalCriticalForm yoshidaHalfLength yoshidaHalfLength_pos
        (yoshidaClippedOddMode yoshidaHalfLength (11 + k))
        (yoshidaClippedOddLowMode yoshidaHalfLength i)‖ ^ 2 ≤
      (19 / 50 : ℝ) / (((11 + k : ℕ) : ℝ) ^ 2) :=
  odd_low_high_pairing_decay_of_high_sine_bounds highSineBounds i k

theorem oddLowTailCouplingEnergy_le (i : YoshidaOddIndex) :
    oddLowTailCouplingEnergy i ≤ 19 / 500 :=
  oddLowTailCouplingEnergy_le_of_high_sine_bounds highSineBounds i

end ArithmeticHodge.Analysis.YoshidaOddCouplingClosed
