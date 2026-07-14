import ArithmeticHodge.Analysis.TwoByTwoSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDiskSchur

noncomputable section

open TwoByTwoSchur
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseFullProfile

/-!
# Profile-level disk--Schur reduction

The factor-two endpoint phase is a two-profile scalar pencil.  For a fixed
symmetric phase coordinate `a`, each profile contributes its complete signed
diagonal, while the alternating coordinate is the sole cross term.  The
closed-disk constraint pays exactly the factor `1 - a^2` in the determinant.

Unlike the concrete Fourier certificate API, this reduction is stated on the
original profiles.  In particular, the archimedean head and tail and both
retained prime atoms remain inside the signed diagonals and cross coordinate.
-/

/-- The complete signed diagonal pencil of one centered profile. -/
def factorTwoEndpointPhaseDiagonal (w : ℝ → ℝ) (a : ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic w +
    a * factorTwoCenteredSymmetricPerturbation w

/-- Exact separation of the complete channel into its two signed diagonals
and its alternating cross coordinate. -/
theorem factorTwoEndpointChannelPhase_eq_diagonals
    (e o : ℝ → ℝ) (a b : ℝ) :
    factorTwoEndpointChannelPhase e o a b =
      factorTwoEndpointPhaseDiagonal e a +
        factorTwoEndpointPhaseDiagonal o a +
        b * factorTwoCenteredAlternatingCoupling e o := by
  unfold factorTwoEndpointChannelPhase
    factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
    factorTwoEndpointPhaseDiagonal
  ring

/-- Division-free profile-level Schur closure on the phase disk.  The
determinant hypothesis is independent of `b`; `a^2 + b^2 ≤ 1` supplies the
sharp comparison `b^2 ≤ 1 - a^2`. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_disk_schur
    (e o : ℝ → ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (he : 0 ≤ factorTwoEndpointPhaseDiagonal e a)
    (ho : 0 ≤ factorTwoEndpointPhaseDiagonal o a)
    (hdet :
      (1 - a ^ 2) * factorTwoCenteredAlternatingCoupling e o ^ 2 ≤
        4 * factorTwoEndpointPhaseDiagonal e a *
          factorTwoEndpointPhaseDiagonal o a) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  have hb : b ^ 2 ≤ 1 - a ^ 2 := by
    linarith
  have hcross :
      b ^ 2 * factorTwoCenteredAlternatingCoupling e o ^ 2 ≤
        (1 - a ^ 2) * factorTwoCenteredAlternatingCoupling e o ^ 2 :=
    mul_le_mul_of_nonneg_right hb
      (sq_nonneg (factorTwoCenteredAlternatingCoupling e o))
  have hmixed :
      (b * factorTwoCenteredAlternatingCoupling e o / 2) ^ 2 ≤
        factorTwoEndpointPhaseDiagonal e a *
          factorTwoEndpointPhaseDiagonal o a := by
    nlinarith
  have hnonneg := scalar_low_tail_nonneg
    (factorTwoEndpointPhaseDiagonal e a)
    (factorTwoEndpointPhaseDiagonal o a)
    (b * factorTwoCenteredAlternatingCoupling e o / 2)
    he ho hmixed
  rw [factorTwoEndpointChannelPhase_eq_diagonals]
  nlinarith

/-- A determinant estimate quantified only by `a` closes every second phase
coordinate in the unit disk. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_uniform_disk_schur
    (e o : ℝ → ℝ)
    (he : ∀ a : ℝ, a ^ 2 ≤ 1 →
      0 ≤ factorTwoEndpointPhaseDiagonal e a)
    (ho : ∀ a : ℝ, a ^ 2 ≤ 1 →
      0 ≤ factorTwoEndpointPhaseDiagonal o a)
    (hdet : ∀ a : ℝ, a ^ 2 ≤ 1 →
      (1 - a ^ 2) * factorTwoCenteredAlternatingCoupling e o ^ 2 ≤
        4 * factorTwoEndpointPhaseDiagonal e a *
          factorTwoEndpointPhaseDiagonal o a)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  have ha : a ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg b]
  exact factorTwoEndpointChannelPhase_nonneg_of_disk_schur
    e o a b hab (he a ha) (ho a ha) (hdet a ha)

/-- Structural blockwise disk--Schur closure.  A decomposition into two
analytic mechanisms may be proved one block at a time and then recombined
without taking absolute values of either cross coordinate.  Typical uses
split off the signed archimedean rank series from the clean/prime residual. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_split_disk_schur
    (e o : ℝ → ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (E₁ O₁ J₁ E₂ O₂ J₂ : ℝ)
    (hE : factorTwoEndpointPhaseDiagonal e a = E₁ + E₂)
    (hO : factorTwoEndpointPhaseDiagonal o a = O₁ + O₂)
    (hJ : factorTwoCenteredAlternatingCoupling e o = J₁ + J₂)
    (hE₁ : 0 ≤ E₁) (hO₁ : 0 ≤ O₁)
    (hE₂ : 0 ≤ E₂) (hO₂ : 0 ≤ O₂)
    (hdet₁ : (1 - a ^ 2) * J₁ ^ 2 ≤ 4 * E₁ * O₁)
    (hdet₂ : (1 - a ^ 2) * J₂ ^ 2 ≤ 4 * E₂ * O₂) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  have ha : a ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg b]
  have hdet :
      (1 - a ^ 2) * factorTwoCenteredAlternatingCoupling e o ^ 2 ≤
        4 * factorTwoEndpointPhaseDiagonal e a *
          factorTwoEndpointPhaseDiagonal o a := by
    rw [hE, hO, hJ]
    exact scaled_determinant_bound_add
      (1 - a ^ 2) E₁ O₁ J₁ E₂ O₂ J₂ (by linarith)
        hE₁ hO₁ hE₂ hO₂ hdet₁ hdet₂
  apply factorTwoEndpointChannelPhase_nonneg_of_disk_schur
    e o a b hab
  · rw [hE]
    positivity
  · rw [hO]
    positivity
  · exact hdet

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDiskSchur
