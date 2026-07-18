import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6RetainedRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6RetainedSingularStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailResidualStructural

noncomputable section

open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024Structural
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6CompleteRepresenterStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6RetainedRepresenterStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6RetainedSingularStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

/-!
# The honest retained endpoint tail for the direct `P6` border

The asymmetric singular split spends `1 / 2048` of the low half-singular
energy and `1 / 128` of the `P6` half-singular energy.  The latter must be
subtracted from the actual charged endpoint diagonal, not replaced by the
much smaller uniform rational floor which merely proves positivity.
-/

/-- Embed the endpoint-even `P0/P2/P4` coordinates into the direct six-mode
core order `(P0,P2,P4,P1,P3,P5)`. -/
def factorTwoIntrinsicNineDirectP024Embed
    (c : Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![c 0, c 1, c 2, 0, 0, 0]

/-- Low diagonal complement after retaining `1 / 2048` of the positive
half-singular Gram. -/
def factorTwoIntrinsicNineDirectP024ExactLowComplement
    (sigma : ℝ) (c : Fin 3 → ℝ) : ℝ :=
  factorTwoEndpointChannelPhase
      (factorTwoIntrinsicEvenP024Profile (c 0) (c 1) (c 2))
      (0 : ℝ → ℝ) sigma 0 -
    (1 / 2048 : ℝ) * ((1 / 2 : ℝ) *
      factorTwoPhaseSingularWeightedEnergy
        (factorTwoIntrinsicEvenP024Profile (c 0) (c 1) (c 2))
        (0 : ℝ → ℝ) sigma 0)

/-- Tail diagonal complement after retaining `1 / 128` of the positive
`P6` half-singular Gram. -/
def factorTwoIntrinsicNineDirectP6ExactTailComplement
    (sigma : ℝ) : ℝ :=
  factorTwoIntrinsicNineDirectP6RetainedDiagonal sigma 0 -
    (1 / 128 : ℝ) * ((1 / 2 : ℝ) *
      factorTwoPhaseSingularWeightedEnergy
        factorTwoCenteredP6 (0 : ℝ → ℝ) sigma 0)

/-- The direct endpoint border after losslessly removing the matching
`1 / 512` potential/reflected-pole row. -/
def factorTwoIntrinsicNineDirectP6ExactResidualBorder
    (sigma : ℝ) (c : Fin 3 → ℝ) : ℝ :=
  let x := factorTwoIntrinsicNineDirectP024Embed c
  factorTwoIntrinsicNineDirectP6BorderFunctional sigma 0 x -
    (1 / 512 : ℝ) * factorTwoPhasePotentialPoleMixed
      (factorTwoIntrinsicNineDirectP024Profile x)
      (factorTwoIntrinsicNineDirectP135Profile x)
      factorTwoCenteredP6 (0 : ℝ → ℝ) sigma 0

/-- Both endpoint low complements are strictly positive away from zero. -/
theorem factorTwoIntrinsicNineDirectP024ExactLowComplement_pos
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (c : Fin 3 → ℝ) (hc : c ≠ 0) :
    0 < factorTwoIntrinsicNineDirectP024ExactLowComplement sigma c := by
  have hcoord : c 0 ≠ 0 ∨ c 1 ≠ 0 ∨ c 2 ≠ 0 := by
    by_contra h
    push_neg at h
    rcases h with ⟨h0, h1, h2⟩
    apply hc
    funext i
    fin_cases i <;> assumption
  rcases hsigma with rfl | rfl
  · simpa only [factorTwoIntrinsicNineDirectP024ExactLowComplement] using
      factorTwoEndpointChannelPhase_sub_oneDiv2048_halfSingular_pos_plus
        (c 0) (c 1) (c 2) hcoord
  · simpa only [factorTwoIntrinsicNineDirectP024ExactLowComplement] using
      factorTwoEndpointChannelPhase_sub_oneDiv2048_halfSingular_pos_minus
        (c 0) (c 1) (c 2) hcoord

/-- The honest retained `P6` tail complement is uniformly strictly positive
on the phase disk.  The old rational quantity is used only as a certified
positive floor; no tail mass is discarded in the definition above. -/
theorem factorTwoIntrinsicNineDirectP6ExactTailComplement_pos
    (sigma : ℝ) (hsigma : sigma ^ 2 ≤ 1) :
    0 < factorTwoIntrinsicNineDirectP6ExactTailComplement sigma := by
  have hretain :=
    factorTwoIntrinsicNineDirectP6RetainedDiagonal_retain_one_div_128
      sigma 0 hsigma
  have henergy : 0 < factorTwoIntrinsicEnergy factorTwoCenteredP6 := by
    rw [factorTwoCenteredP6_energy]
    norm_num
  unfold factorTwoIntrinsicNineDirectP6ExactTailComplement
  nlinarith [mul_pos (by norm_num : (0 : ℝ) < 741739 / 46126080) henergy]

/-- The residual border is exactly one retained representer pairing against
`P6`; this is the analytic input for the forthcoming `3 x 3` selector Gram. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualBorder_eq_pairing
    (sigma : ℝ) (c : Fin 3 → ℝ) :
    factorTwoIntrinsicNineDirectP6ExactResidualBorder sigma c =
      ∫ z : ℝ in -1..1,
        factorTwoIntrinsicNineDirectP6RetainedWholeRepresenterAt
            (1 / 512 : ℝ) sigma 0
            (factorTwoIntrinsicNineDirectP024Embed c) z *
          factorTwoCenteredP6 z := by
  unfold factorTwoIntrinsicNineDirectP6ExactResidualBorder
  exact
    factorTwoIntrinsicNineDirectP6BorderFunctional_sub_one_div_512_potentialPole_eq_pairing
      sigma 0 (factorTwoIntrinsicNineDirectP024Embed c)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailResidualStructural
