import ArithmeticHodge.Analysis.DigammaTrapezoid
import ArithmeticHodge.Analysis.YoshidaDiagonalAcceleratedSeries

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaDiagonalUniformIdentity

noncomputable section

open DigammaTrapezoid
open YoshidaDiagonalSeriesTail
open YoshidaOddGramPrefix

def yoshidaY (n : ℕ) : ℝ := yoshidaKappa n / 2

def diagonalHighProfile (y t : ℝ) : ℝ :=
  reciprocalRealPart y (t + 1 / 4)

def diagonalHighProfileDeriv (y t : ℝ) : ℝ :=
  reciprocalRealPartDeriv y (t + 1 / 4)

theorem two_mul_diagonalRampClosed_eq_profile_add_deriv
    {L y k : ℝ} (hL : L ≠ 0) (hy : y ≠ 0) :
    2 * diagonalRampClosed L ((2 * y) ^ 2) (2 * k + 1 / 2) 0 =
      diagonalHighProfile y k + diagonalHighProfileDeriv y k / (2 * L) := by
  unfold diagonalRampClosed diagonalHighProfile diagonalHighProfileDeriv
    reciprocalRealPart reciprocalRealPartDeriv
  field_simp [hL, hy]
  ring

end

end ArithmeticHodge.Analysis.YoshidaDiagonalUniformIdentity
