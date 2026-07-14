import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLow
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseStructuralLowData
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankDominationObstruction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRankLimit

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive

noncomputable section

open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseCoupledRankDominationObstruction
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseRankLimit
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaRenormalizedGeometricKernel

/-!
# Structural endpoint gates for the intrinsic even block

The signed endpoint matrices are not evaluated entry by entry.  Instead we
identify their quadratic forms with the complete clean form plus or minus the
complete symmetric perturbation on the intrinsic `P₀/P₂` profile.  Strict
positivity of those two signed profile forms is exactly the four scalar gates
used by the intrinsic Schur argument.
-/

/-- The affine even pencil is exactly the signed clean/perturbation form on
the intrinsic `P₀/P₂` profile. -/
theorem factorTwoStructuralPhaseLow_endpoint_quadratic
    (sigma c d : ℝ) :
    factorTwoStructuralPhaseLow00 sigma * c ^ 2 +
        2 * factorTwoStructuralPhaseLow02 sigma * c * d +
        factorTwoStructuralPhaseLow22 sigma * d ^ 2 =
      yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) +
        sigma * factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d) := by
  have hclean :
      yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) =
        yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * d +
          yoshidaEndpointEvenLowGram22 * d ^ 2 := by
    simpa only [factorTwoEvenStructuralLowProfile] using
      yoshidaEndpointEvenLowGram_quadratic_eq_clean c d
  rw [hclean, factorTwoCenteredSymmetricPerturbation_structuralLow]
  unfold factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22
  ring

/-- A strict signed profile inequality yields both scalar Sylvester gates at
that endpoint. -/
theorem factorTwoIntrinsicEven_endpoint_gates_of_profile_pos
    (sigma : ℝ)
    (hpos : ∀ c d : ℝ, c ≠ 0 ∨ d ≠ 0 →
      0 < yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) +
        sigma * factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d)) :
    0 < factorTwoStructuralPhaseLow00 sigma ∧
      0 < factorTwoIntrinsicEvenPhaseDet sigma := by
  have hquadratic : ∀ c d : ℝ, c ≠ 0 ∨ d ≠ 0 →
      0 < factorTwoStructuralPhaseLow00 sigma * c ^ 2 +
        2 * factorTwoStructuralPhaseLow02 sigma * c * d +
        factorTwoStructuralPhaseLow22 sigma * d ^ 2 := by
    intro c d hne
    rw [factorTwoStructuralPhaseLow_endpoint_quadratic]
    exact hpos c d hne
  have hcoeff := real_twoByTwo_coefficients_pos_of_quadratic_pos
    (factorTwoStructuralPhaseLow00 sigma)
    (factorTwoStructuralPhaseLow02 sigma)
    (factorTwoStructuralPhaseLow22 sigma) hquadratic
  simpa only [factorTwoIntrinsicEvenPhaseDet] using hcoeff

/-- Conversely, the two scalar gates are precisely strict positivity of the
signed endpoint form on every nonzero intrinsic coefficient vector. -/
theorem factorTwoIntrinsicEven_endpoint_profile_pos_of_gates
    (sigma : ℝ)
    (h00 : 0 < factorTwoStructuralPhaseLow00 sigma)
    (hdet : 0 < factorTwoIntrinsicEvenPhaseDet sigma)
    (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
    0 < yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) +
        sigma * factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d) := by
  rw [← factorTwoStructuralPhaseLow_endpoint_quadratic]
  exact real_twoByTwo_quadratic_pos _ _ _ c d h00
    (by simpa only [factorTwoIntrinsicEvenPhaseDet] using hdet) hne

/-! ## Cancellation-preserving rank/prime normal form -/

/-- The single growing cosh square on the intrinsic even profile. -/
def factorTwoIntrinsicEvenGrowingHead (c d : ℝ) : ℝ :=
  yoshidaEndpointA * Real.exp yoshidaEndpointA *
    centeredCoshMoment (factorTwoEvenStructuralLowProfile c d)
      (yoshidaEndpointA / 2) ^ 2

/-- The complete, untruncated decaying cosh-square family. -/
def factorTwoIntrinsicEvenDecayingTail (c d : ℝ) : ℝ :=
  yoshidaEndpointA * ∑' m : ℕ,
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment (factorTwoEvenStructuralLowProfile c d)
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2

/-- The dyadic mass atom and translated `p = 3` atom, kept as their exact
joint quadratic block. -/
def factorTwoIntrinsicEvenPrimeBlock (c d : ℝ) : ℝ :=
  factorTwoCenteredPrimeBlock (factorTwoEvenStructuralLowProfile c d)

private theorem even_factorTwoEvenStructuralLowProfile (c d : ℝ) :
    Function.Even (factorTwoEvenStructuralLowProfile c d) := by
  intro x
  unfold factorTwoEvenStructuralLowProfile centeredEvenP0 centeredEvenP2
  ring

/-- Exact signed-square factorization of the intrinsic even perturbation.
No rank is discarded and the two prime atoms remain coupled. -/
theorem factorTwoIntrinsicEven_symmetricPerturbation_eq_head_sub_tail_sub_prime
    (c d : ℝ) :
    factorTwoCenteredSymmetricPerturbation
        (factorTwoEvenStructuralLowProfile c d) =
      factorTwoIntrinsicEvenGrowingHead c d -
        factorTwoIntrinsicEvenDecayingTail c d -
        factorTwoIntrinsicEvenPrimeBlock c d := by
  let w := factorTwoEvenStructuralLowProfile c d
  have harch := factorTwoCenteredArchBlock_eq_evenRankSquares w
    (continuous_factorTwoEvenStructuralLowProfile c d)
    (even_factorTwoEvenStructuralLowProfile c d)
  rw [symmetricPerturbation_eq_arch_sub_primeBlock, harch]
  unfold factorTwoIntrinsicEvenGrowingHead
    factorTwoIntrinsicEvenDecayingTail factorTwoIntrinsicEvenPrimeBlock
  dsimp only [w]
  ring_nf

/-- At the positive symmetric endpoint the growing square is retained while
the complete decaying family and joint prime block are spent. -/
theorem factorTwoIntrinsicEven_plus_endpoint_eq_rankPrime
    (c d : ℝ) :
    yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) +
        factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d) =
      yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) +
        factorTwoIntrinsicEvenGrowingHead c d -
        factorTwoIntrinsicEvenDecayingTail c d -
        factorTwoIntrinsicEvenPrimeBlock c d := by
  rw [factorTwoIntrinsicEven_symmetricPerturbation_eq_head_sub_tail_sub_prime]
  ring

/-- At the negative symmetric endpoint the signs of the entire head--tail
and retained-prime package reverse together. -/
theorem factorTwoIntrinsicEven_minus_endpoint_eq_rankPrime
    (c d : ℝ) :
    yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) -
        factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d) =
      yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) -
        factorTwoIntrinsicEvenGrowingHead c d +
        factorTwoIntrinsicEvenDecayingTail c d +
        factorTwoIntrinsicEvenPrimeBlock c d := by
  rw [factorTwoIntrinsicEven_symmetricPerturbation_eq_head_sub_tail_sub_prime]
  ring

/-- Sharp positive-endpoint gate in domination form.  This is an equivalence,
not a lossy sufficient estimate. -/
theorem factorTwoIntrinsicEven_plus_endpoint_pos_iff
    (c d : ℝ) :
    0 < yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) +
        factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d) ↔
      factorTwoIntrinsicEvenDecayingTail c d +
          factorTwoIntrinsicEvenPrimeBlock c d <
        yoshidaEndpointOddCleanQuadratic
            (factorTwoEvenStructuralLowProfile c d) +
          factorTwoIntrinsicEvenGrowingHead c d := by
  rw [factorTwoIntrinsicEven_plus_endpoint_eq_rankPrime]
  constructor <;> intro h <;> linarith

/-- Sharp negative-endpoint gate in domination form. -/
theorem factorTwoIntrinsicEven_minus_endpoint_pos_iff
    (c d : ℝ) :
    0 < yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) -
        factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d) ↔
      factorTwoIntrinsicEvenGrowingHead c d <
        yoshidaEndpointOddCleanQuadratic
            (factorTwoEvenStructuralLowProfile c d) +
          factorTwoIntrinsicEvenDecayingTail c d +
          factorTwoIntrinsicEvenPrimeBlock c d := by
  rw [factorTwoIntrinsicEven_minus_endpoint_eq_rankPrime]
  constructor <;> intro h <;> linarith

/-! ## Manifest signs retained by the normal form -/

/-- The complete clean intrinsic even form is strictly positive off the
origin.  This uses its exact Gram determinant, not an entry approximation. -/
theorem factorTwoIntrinsicEven_clean_pos
    (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
    0 < yoshidaEndpointOddCleanQuadratic
      (factorTwoEvenStructuralLowProfile c d) := by
  have hgram := real_twoByTwo_quadratic_pos
    yoshidaEndpointEvenLowGram00 yoshidaEndpointEvenLowGram02
    yoshidaEndpointEvenLowGram22 c d
    yoshidaEndpointEvenLowGram00_pos
    yoshidaEndpointEvenLowGram_det_pos hne
  have hexact :
      yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) =
        yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * d +
          yoshidaEndpointEvenLowGram22 * d ^ 2 := by
    simpa only [factorTwoEvenStructuralLowProfile] using
      yoshidaEndpointEvenLowGram_quadratic_eq_clean c d
  rw [hexact]
  exact hgram

theorem factorTwoIntrinsicEvenGrowingHead_nonneg (c d : ℝ) :
    0 ≤ factorTwoIntrinsicEvenGrowingHead c d := by
  unfold factorTwoIntrinsicEvenGrowingHead
  exact mul_nonneg
    (mul_nonneg yoshidaEndpointA_pos.le (Real.exp_pos _).le)
    (sq_nonneg _)

theorem factorTwoIntrinsicEvenDecayingTail_nonneg (c d : ℝ) :
    0 ≤ factorTwoIntrinsicEvenDecayingTail c d := by
  unfold factorTwoIntrinsicEvenDecayingTail
  exact mul_nonneg yoshidaEndpointA_pos.le
    (tsum_nonneg fun m ↦ mul_nonneg (Real.exp_pos _).le (sq_nonneg _))

/-- The retained dyadic/translated-prime package is nonnegative without
separating its two atoms. -/
theorem factorTwoIntrinsicEvenPrimeBlock_nonneg (c d : ℝ) :
    0 ≤ factorTwoIntrinsicEvenPrimeBlock c d := by
  let w := factorTwoEvenStructuralLowProfile c d
  have hlower := (primeBlock_mass_bounds w
    (continuous_factorTwoEvenStructuralLowProfile c d)).1
  have hcoeff : 0 < Real.log 2 / Real.sqrt 2 -
      (Real.log 3 / Real.sqrt 3) / 2 := by
    have hdyadic : 0 < Real.log 2 / Real.sqrt 2 := by positivity
    have hthree := primeThreeWeight_lt_two_mul_dyadicWeight
    linarith
  have henergy : 0 ≤ ∫ x : ℝ in -1..1, w x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    positivity
  unfold factorTwoIntrinsicEvenPrimeBlock
  exact (mul_nonneg hcoeff.le henergy).trans hlower

/-- Off the coefficient origin the joint prime block is strictly positive;
the half-mass contraction leaves a genuinely positive dyadic reserve. -/
theorem factorTwoIntrinsicEvenPrimeBlock_pos
    (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
    0 < factorTwoIntrinsicEvenPrimeBlock c d := by
  let w := factorTwoEvenStructuralLowProfile c d
  have hlower := (primeBlock_mass_bounds w
    (continuous_factorTwoEvenStructuralLowProfile c d)).1
  have hcoeff : 0 < Real.log 2 / Real.sqrt 2 -
      (Real.log 3 / Real.sqrt 3) / 2 := by
    have hdyadic : 0 < Real.log 2 / Real.sqrt 2 := by positivity
    have hthree := primeThreeWeight_lt_two_mul_dyadicWeight
    linarith
  have hprofile : w = yoshidaEndpointEvenLowProfile c d := by
    funext x
    unfold w factorTwoEvenStructuralLowProfile
      yoshidaEndpointEvenLowProfile centeredEvenP0
    ring
  have henergyEq :
      (∫ x : ℝ in -1..1, w x ^ 2) =
        2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2 := by
    rw [hprofile]
    exact integral_yoshidaEndpointEvenLowProfile_sq c d
  have henergy : 0 < ∫ x : ℝ in -1..1, w x ^ 2 := by
    rw [henergyEq]
    rcases hne with hc | hd
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (by norm_num) (sq_pos_of_ne_zero hc))
        (mul_nonneg (by norm_num) (sq_nonneg d))
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (by norm_num) (sq_nonneg c))
        (mul_pos (by norm_num) (sq_pos_of_ne_zero hd))
  have hstrict : 0 <
      (Real.log 2 / Real.sqrt 2 -
        (Real.log 3 / Real.sqrt 3) / 2) *
          (∫ x : ℝ in -1..1, w x ^ 2) :=
    mul_pos hcoeff henergy
  unfold factorTwoIntrinsicEvenPrimeBlock
  exact hstrict.trans_le hlower

/-! ## Exact four-gate equivalence -/

/-- The four scalar endpoint gates are equivalent to strict positivity of
the two exact signed profile forms on every nonzero intrinsic vector. -/
theorem factorTwoIntrinsicEven_four_endpoint_gates_iff :
    (0 < factorTwoStructuralPhaseLow00 1 ∧
        0 < factorTwoIntrinsicEvenPhaseDet 1) ∧
      (0 < factorTwoStructuralPhaseLow00 (-1) ∧
        0 < factorTwoIntrinsicEvenPhaseDet (-1)) ↔
    ∀ c d : ℝ, c ≠ 0 ∨ d ≠ 0 →
      (0 < yoshidaEndpointOddCleanQuadratic
            (factorTwoEvenStructuralLowProfile c d) +
          factorTwoCenteredSymmetricPerturbation
            (factorTwoEvenStructuralLowProfile c d)) ∧
      (0 < yoshidaEndpointOddCleanQuadratic
            (factorTwoEvenStructuralLowProfile c d) -
          factorTwoCenteredSymmetricPerturbation
            (factorTwoEvenStructuralLowProfile c d)) := by
  constructor
  · rintro ⟨hplus, hminus⟩ c d hne
    constructor
    · simpa only [one_mul] using
        factorTwoIntrinsicEven_endpoint_profile_pos_of_gates
          1 hplus.1 hplus.2 c d hne
    · have h := factorTwoIntrinsicEven_endpoint_profile_pos_of_gates
          (-1) hminus.1 hminus.2 c d hne
      simpa only [neg_one_mul, sub_eq_add_neg] using h
  · intro h
    constructor
    · apply factorTwoIntrinsicEven_endpoint_gates_of_profile_pos 1
      intro c d hne
      simpa only [one_mul] using (h c d hne).1
    · apply factorTwoIntrinsicEven_endpoint_gates_of_profile_pos (-1)
      intro c d hne
      simpa only [neg_one_mul, sub_eq_add_neg] using (h c d hne).2

/-! ## Why the present coarse bounds cannot close the gates -/

/-- On the constant intrinsic mode, replacing the perturbation by its
available structural lower bound `-3 E` leaves a strictly negative
surrogate.  Thus that bound cannot prove the positive endpoint gate. -/
theorem constant_even_coarse_plus_surrogate_neg :
    yoshidaEndpointOddCleanQuadratic (fun _ : ℝ ↦ 1) -
        3 * (∫ _x : ℝ in -1..1, (1 : ℝ) ^ 2) < 0 := by
  have hclean := constant_clean_lt_eight_fifths
  norm_num at ⊢
  linarith

/-- Likewise, replacing the perturbation by the generic upper bound `E`
leaves a negative constant-mode surrogate for the negative endpoint. -/
theorem constant_even_coarse_minus_surrogate_neg :
    yoshidaEndpointOddCleanQuadratic (fun _ : ℝ ↦ 1) -
        (∫ _x : ℝ in -1..1, (1 : ℝ) ^ 2) < 0 := by
  have hclean := constant_clean_lt_eight_fifths
  norm_num at ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
