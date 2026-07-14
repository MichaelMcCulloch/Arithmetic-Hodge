import ArithmeticHodge.Analysis.YoshidaEndpointEvenCleanPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRankLimit

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointReduction

noncomputable section

open ThreeByThreeConvexPencil
open ThreeByThreeRankOneSchur
open YoshidaEndpointEvenCleanPositive
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseRankLimit
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaRenormalizedGeometricKernel

/-!
# Rank-one reduction of the negative `P₀/P₂/P₄` endpoint

At symmetric phase `-1`, the only adverse archimedean term is the growing
cosh square.  Adding that one row back leaves the clean form, the complete
decaying square family, and the coupled prime block.  This favourable form
is positive definite for structural reasons.  Consequently the endpoint
determinant reduces to one exact dual-norm inequality for the growing row.
-/

def factorTwoIntrinsicP024GrowingWeight : ℝ :=
  yoshidaEndpointA * Real.exp yoshidaEndpointA

def factorTwoIntrinsicP024Growing0 : ℝ :=
  centeredCoshMoment centeredEvenP0 (yoshidaEndpointA / 2)

def factorTwoIntrinsicP024Growing2 : ℝ :=
  centeredCoshMoment centeredEvenP2 (yoshidaEndpointA / 2)

def factorTwoIntrinsicP024Growing4 : ℝ :=
  centeredCoshMoment factorTwoCenteredP4 (yoshidaEndpointA / 2)

def factorTwoIntrinsicP024Favourable00 : ℝ :=
  factorTwoStructuralPhaseLow00 (-1) +
    factorTwoIntrinsicP024GrowingWeight *
      factorTwoIntrinsicP024Growing0 ^ 2

def factorTwoIntrinsicP024Favourable02 : ℝ :=
  factorTwoStructuralPhaseLow02 (-1) +
    factorTwoIntrinsicP024GrowingWeight *
      factorTwoIntrinsicP024Growing0 * factorTwoIntrinsicP024Growing2

def factorTwoIntrinsicP024Favourable04 : ℝ :=
  factorTwoIntrinsicFourP45Cross04 (-1) +
    factorTwoIntrinsicP024GrowingWeight *
      factorTwoIntrinsicP024Growing0 * factorTwoIntrinsicP024Growing4

def factorTwoIntrinsicP024Favourable22 : ℝ :=
  factorTwoStructuralPhaseLow22 (-1) +
    factorTwoIntrinsicP024GrowingWeight *
      factorTwoIntrinsicP024Growing2 ^ 2

def factorTwoIntrinsicP024Favourable24 : ℝ :=
  factorTwoIntrinsicFourP45Cross24 (-1) +
    factorTwoIntrinsicP024GrowingWeight *
      factorTwoIntrinsicP024Growing2 * factorTwoIntrinsicP024Growing4

def factorTwoIntrinsicP024Favourable44 : ℝ :=
  factorTwoIntrinsicP4PhaseDiagonal (-1) +
    factorTwoIntrinsicP024GrowingWeight *
      factorTwoIntrinsicP024Growing4 ^ 2

/-- Exact orthogonal mass of the three-mode profile. -/
theorem integral_factorTwoIntrinsicEvenP024Profile_sq
    (c0 c2 c4 : ℝ) :
    (∫ x : ℝ in -1..1,
      factorTwoIntrinsicEvenP024Profile c0 c2 c4 x ^ 2) =
      2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
        (2 / 9 : ℝ) * c4 ^ 2 := by
  let low := factorTwoEvenStructuralLowProfile c0 c2
  have hlow : low = yoshidaEndpointEvenLowProfile c0 c2 := by
    funext x
    unfold low factorTwoEvenStructuralLowProfile
      yoshidaEndpointEvenLowProfile centeredEvenP0
    ring
  have hlowContinuous : Continuous low := by
    exact continuous_factorTwoEvenStructuralLowProfile c0 c2
  have hP4Continuous : Continuous factorTwoCenteredP4 :=
    continuous_factorTwoCenteredP4
  have hP2Continuous : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  have hcross :
      (∫ x : ℝ in -1..1, low x * factorTwoCenteredP4 x) = 0 := by
    rw [show (fun x : ℝ ↦ low x * factorTwoCenteredP4 x) =
        fun x ↦ c0 * factorTwoCenteredP4 x +
          c2 * (factorTwoCenteredP4 x * centeredEvenP2 x) by
      funext x
      unfold low factorTwoEvenStructuralLowProfile centeredEvenP0
      ring,
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
        (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_factorTwoCenteredP4,
      integral_factorTwoCenteredP4_mul_centeredEvenP2]
    ring
  have hlowMass :
      (∫ x : ℝ in -1..1, low x ^ 2) =
        2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 := by
    rw [hlow]
    exact integral_yoshidaEndpointEvenLowProfile_sq c0 c2
  unfold factorTwoIntrinsicEvenP024Profile
    factorTwoIntrinsicSixEvenTail
  rw [show (fun x : ℝ ↦
      (factorTwoEvenStructuralLowProfile c0 c2 +
        fun y ↦ c4 * factorTwoCenteredP4 y) x ^ 2) =
      fun x ↦ low x ^ 2 +
        (2 * c4) * (low x * factorTwoCenteredP4 x) +
        c4 ^ 2 * factorTwoCenteredP4 x ^ 2 by
    funext x
    dsimp only [low, Pi.add_apply]
    ring,
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    hlowMass, hcross, integral_factorTwoCenteredP4_sq]
  ring

theorem factorTwoIntrinsicEvenP024Profile_continuous
    (c0 c2 c4 : ℝ) :
    Continuous (factorTwoIntrinsicEvenP024Profile c0 c2 c4) := by
  unfold factorTwoIntrinsicEvenP024Profile
    factorTwoIntrinsicSixEvenTail
  exact (continuous_factorTwoEvenStructuralLowProfile c0 c2).add
    (continuous_const.mul continuous_factorTwoCenteredP4)

theorem factorTwoIntrinsicEvenP024Profile_even
    (c0 c2 c4 : ℝ) :
    Function.Even (factorTwoIntrinsicEvenP024Profile c0 c2 c4) := by
  intro x
  unfold factorTwoIntrinsicEvenP024Profile
    factorTwoIntrinsicSixEvenTail factorTwoEvenStructuralLowProfile
  simp only [Pi.add_apply]
  rw [even_factorTwoCenteredP4]
  unfold centeredEvenP0 centeredEvenP2
  ring

theorem factorTwoIntrinsicEvenP024Profile_locallyLipschitzOn
    (c0 c2 c4 : ℝ) :
    LocallyLipschitzOn (Icc (-1) 1)
      (factorTwoIntrinsicEvenP024Profile c0 c2 c4) := by
  have hdiff : ContDiff ℝ 1
      (factorTwoIntrinsicEvenP024Profile c0 c2 c4) := by
    change ContDiff ℝ 1 (fun x ↦
      c0 * centeredEvenP0 x + c2 * centeredEvenP2 x +
        c4 * factorTwoCenteredP4 x)
    unfold centeredEvenP0 centeredEvenP2 factorTwoCenteredP4
    fun_prop
  exact hdiff.locallyLipschitz.locallyLipschitzOn

theorem centeredCoshMoment_factorTwoIntrinsicEvenP024Profile_half
    (c0 c2 c4 : ℝ) :
    centeredCoshMoment
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
        (yoshidaEndpointA / 2) =
      factorTwoIntrinsicP024Growing0 * c0 +
        factorTwoIntrinsicP024Growing2 * c2 +
        factorTwoIntrinsicP024Growing4 * c4 := by
  let f0 : ℝ → ℝ := fun x ↦
    Real.cosh ((yoshidaEndpointA / 2) * x) * centeredEvenP0 x
  let f2 : ℝ → ℝ := fun x ↦
    Real.cosh ((yoshidaEndpointA / 2) * x) * centeredEvenP2 x
  let f4 : ℝ → ℝ := fun x ↦
    Real.cosh ((yoshidaEndpointA / 2) * x) * factorTwoCenteredP4 x
  have hf0 : Continuous f0 := by
    unfold f0 centeredEvenP0
    fun_prop
  have hf2 : Continuous f2 := by
    unfold f2 centeredEvenP2
    fun_prop
  have hf4 : Continuous f4 := by
    unfold f4 factorTwoCenteredP4
    fun_prop
  unfold centeredCoshMoment factorTwoIntrinsicEvenP024Profile
    factorTwoIntrinsicSixEvenTail factorTwoEvenStructuralLowProfile
  simp only [Pi.add_apply]
  rw [show (fun x : ℝ ↦
      Real.cosh ((yoshidaEndpointA / 2) * x) *
        (c0 * centeredEvenP0 x + c2 * centeredEvenP2 x +
          c4 * factorTwoCenteredP4 x)) =
      fun x ↦ c0 * f0 x + (c2 * f2 x + c4 * f4 x) by
    funext x
    dsimp only [f0, f2, f4]
    ring,
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  unfold factorTwoIntrinsicP024Growing0
    factorTwoIntrinsicP024Growing2 factorTwoIntrinsicP024Growing4
    centeredCoshMoment
  ring

/-- Adding back the adverse growing row leaves a strictly positive form.
The clean and decaying pieces are nonnegative, while the coupled prime block
is strictly positive off the coefficient origin. -/
theorem factorTwoIntrinsicP024Favourable_quadratic_pos
    (c0 c2 c4 : ℝ) (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0) :
    0 < symmetricQuadratic
      factorTwoIntrinsicP024Favourable00
      factorTwoIntrinsicP024Favourable02
      factorTwoIntrinsicP024Favourable04
      factorTwoIntrinsicP024Favourable22
      factorTwoIntrinsicP024Favourable24
      factorTwoIntrinsicP024Favourable44 c0 c2 c4 := by
  let w := factorTwoIntrinsicEvenP024Profile c0 c2 c4
  let tail : ℝ := ∑' m : ℕ,
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment w
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  have hw := factorTwoIntrinsicEvenP024Profile_continuous c0 c2 c4
  have hweven := factorTwoIntrinsicEvenP024Profile_even c0 c2 c4
  have hwlocal :=
    factorTwoIntrinsicEvenP024Profile_locallyLipschitzOn c0 c2 c4
  have hclean : 0 ≤ yoshidaEndpointOddCleanQuadratic w :=
    yoshidaEndpointOddCleanQuadratic_nonneg_of_even_of_locallyLipschitzOn
      w hw hweven hwlocal
  have htail : 0 ≤ tail := by
    dsimp only [tail]
    exact tsum_nonneg fun m ↦
      mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have henergy : 0 < ∫ x : ℝ in -1..1, w x ^ 2 := by
    dsimp only [w]
    rw [integral_factorTwoIntrinsicEvenP024Profile_sq]
    rcases hne with h0 | h2 | h4
    · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg c2, sq_nonneg c4]
    · nlinarith [sq_nonneg c0, sq_pos_of_ne_zero h2, sq_nonneg c4]
    · nlinarith [sq_nonneg c0, sq_nonneg c2, sq_pos_of_ne_zero h4]
  have hprimeLower := (primeBlock_mass_bounds w hw).1
  have hprimeCoeff : 0 < Real.log 2 / Real.sqrt 2 -
      (Real.log 3 / Real.sqrt 3) / 2 := by
    have hdyadic : 0 < Real.log 2 / Real.sqrt 2 := by positivity
    have hthree := primeThreeWeight_lt_two_mul_dyadicWeight
    linarith
  have hprime : 0 < factorTwoCenteredPrimeBlock w := by
    exact (mul_pos hprimeCoeff henergy).trans_le hprimeLower
  have harch := factorTwoCenteredArchBlock_eq_evenRankSquares w hw hweven
  have hmoment :=
    centeredCoshMoment_factorTwoIntrinsicEvenP024Profile_half c0 c2 c4
  have hphase :=
    factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic
      c0 c2 c4 (-1)
  have hphaseForm :
      factorTwoEndpointChannelPhase w (0 : ℝ → ℝ) (-1) 0 =
        yoshidaEndpointOddCleanQuadratic w -
          factorTwoCenteredSymmetricPerturbation w := by
    dsimp only [w]
    unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
      factorTwoEndpointChannelSymmetricSum
    have hcleanZero :
        yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
      simpa using
        (yoshidaEndpointOddCleanQuadratic_const_mul
          (0 : ℝ → ℝ) 0)
    have hsymZero :
        factorTwoCenteredSymmetricPerturbation (0 : ℝ → ℝ) = 0 := by
      simpa using factorTwoCenteredSymmetricPerturbation_smul
        0 (0 : ℝ → ℝ)
    rw [hcleanZero, hsymZero]
    ring
  have hfavourableExact :
      symmetricQuadratic
          factorTwoIntrinsicP024Favourable00
          factorTwoIntrinsicP024Favourable02
          factorTwoIntrinsicP024Favourable04
          factorTwoIntrinsicP024Favourable22
          factorTwoIntrinsicP024Favourable24
          factorTwoIntrinsicP024Favourable44 c0 c2 c4 =
        yoshidaEndpointOddCleanQuadratic w +
          yoshidaEndpointA * tail + factorTwoCenteredPrimeBlock w := by
    calc
      _ = symmetricQuadratic
            (factorTwoStructuralPhaseLow00 (-1))
            (factorTwoStructuralPhaseLow02 (-1))
            (factorTwoIntrinsicFourP45Cross04 (-1))
            (factorTwoStructuralPhaseLow22 (-1))
            (factorTwoIntrinsicFourP45Cross24 (-1))
            (factorTwoIntrinsicP4PhaseDiagonal (-1)) c0 c2 c4 +
          factorTwoIntrinsicP024GrowingWeight *
            (factorTwoIntrinsicP024Growing0 * c0 +
              factorTwoIntrinsicP024Growing2 * c2 +
              factorTwoIntrinsicP024Growing4 * c4) ^ 2 := by
        unfold factorTwoIntrinsicP024Favourable00
          factorTwoIntrinsicP024Favourable02
          factorTwoIntrinsicP024Favourable04
          factorTwoIntrinsicP024Favourable22
          factorTwoIntrinsicP024Favourable24
          factorTwoIntrinsicP024Favourable44 symmetricQuadratic
        ring
      _ = factorTwoEndpointChannelPhase w (0 : ℝ → ℝ) (-1) 0 +
          factorTwoIntrinsicP024GrowingWeight *
            centeredCoshMoment w (yoshidaEndpointA / 2) ^ 2 := by
        rw [← hphase, hmoment]
      _ = yoshidaEndpointOddCleanQuadratic w +
          yoshidaEndpointA * tail + factorTwoCenteredPrimeBlock w := by
        rw [hphaseForm, symmetricPerturbation_eq_arch_sub_primeBlock,
          harch]
        dsimp only [factorTwoIntrinsicP024GrowingWeight, tail]
        ring
  rw [hfavourableExact]
  exact add_pos_of_nonneg_of_pos
    (add_nonneg hclean (mul_nonneg yoshidaEndpointA_pos.le htail)) hprime

/-- The favourable `3 x 3` Gram is positive definite without an analytic
side condition. -/
theorem factorTwoIntrinsicP024Favourable_gates :
    0 < factorTwoIntrinsicP024Favourable00 ∧
      0 < leadingMinorTwo
        factorTwoIntrinsicP024Favourable00
        factorTwoIntrinsicP024Favourable02
        factorTwoIntrinsicP024Favourable22 ∧
      0 < symmetricDeterminant
        factorTwoIntrinsicP024Favourable00
        factorTwoIntrinsicP024Favourable02
        factorTwoIntrinsicP024Favourable04
        factorTwoIntrinsicP024Favourable22
        factorTwoIntrinsicP024Favourable24
        factorTwoIntrinsicP024Favourable44 := by
  exact leadingMinors_pos_of_symmetricQuadratic_pos
    factorTwoIntrinsicP024Favourable00
    factorTwoIntrinsicP024Favourable02
    factorTwoIntrinsicP024Favourable04
    factorTwoIntrinsicP024Favourable22
    factorTwoIntrinsicP024Favourable24
    factorTwoIntrinsicP024Favourable44
    factorTwoIntrinsicP024Favourable_quadratic_pos

/-- The sole remaining negative-endpoint analytic gate is the exact dual
norm of the growing row in the complete favourable Gram. -/
def factorTwoIntrinsicP024MinusDualGate : Prop :=
  factorTwoIntrinsicP024GrowingWeight *
      adjugateQuadratic
        factorTwoIntrinsicP024Favourable00
        factorTwoIntrinsicP024Favourable02
        factorTwoIntrinsicP024Favourable04
        factorTwoIntrinsicP024Favourable22
        factorTwoIntrinsicP024Favourable24
        factorTwoIntrinsicP024Favourable44
        factorTwoIntrinsicP024Growing0
        factorTwoIntrinsicP024Growing2
        factorTwoIntrinsicP024Growing4 <
    symmetricDeterminant
      factorTwoIntrinsicP024Favourable00
      factorTwoIntrinsicP024Favourable02
      factorTwoIntrinsicP024Favourable04
      factorTwoIntrinsicP024Favourable22
      factorTwoIntrinsicP024Favourable24
      factorTwoIntrinsicP024Favourable44

/-- The exact rank-one determinant lemma converts the dual gate into the
negative endpoint leading determinant. -/
theorem factorTwoIntrinsicSixP4SchurLeading_minus_pos_of_dualGate
    (hdual : factorTwoIntrinsicP024MinusDualGate) :
    0 < factorTwoIntrinsicSixP4SchurLeading (-1) := by
  rw [factorTwoIntrinsicSixP4SchurLeading_eq_P024Determinant]
  have hid :
      factorTwoIntrinsicP024Determinant (-1) =
        symmetricDeterminant
            factorTwoIntrinsicP024Favourable00
            factorTwoIntrinsicP024Favourable02
            factorTwoIntrinsicP024Favourable04
            factorTwoIntrinsicP024Favourable22
            factorTwoIntrinsicP024Favourable24
            factorTwoIntrinsicP024Favourable44 -
          factorTwoIntrinsicP024GrowingWeight *
            adjugateQuadratic
              factorTwoIntrinsicP024Favourable00
              factorTwoIntrinsicP024Favourable02
              factorTwoIntrinsicP024Favourable04
              factorTwoIntrinsicP024Favourable22
              factorTwoIntrinsicP024Favourable24
              factorTwoIntrinsicP024Favourable44
              factorTwoIntrinsicP024Growing0
              factorTwoIntrinsicP024Growing2
              factorTwoIntrinsicP024Growing4 := by
    unfold factorTwoIntrinsicP024Determinant
      factorTwoIntrinsicP024Favourable00
      factorTwoIntrinsicP024Favourable02
      factorTwoIntrinsicP024Favourable04
      factorTwoIntrinsicP024Favourable22
      factorTwoIntrinsicP024Favourable24
      factorTwoIntrinsicP024Favourable44
      symmetricDeterminant adjugateQuadratic
    ring
  rw [hid]
  exact sub_pos.mpr hdual

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointReduction
