import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankLimit
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticSplit

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoCenteredPhysical
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOcticPotential
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseCoupledRankLimit
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseOddLowSchur
open YoshidaFactorTwoPhaseOddLowEndpointPositive
open YoshidaFactorTwoPhaseOddStructuralPerturbation
open YoshidaFactorTwoPhaseProfileStaticSplit
open YoshidaFactorTwoPhaseRankLimit
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaRenormalizedGeometricKernel
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural static splits for the intrinsic four-mode block

The static parity reduction needs two `4 x 4` forms.  We keep each form as
one coupled quadratic rather than bounding its four alternating entries
separately.  The exact remaining condition is consequently a Cauchy
inequality between the complete signed endpoint forms.

No phase sampling, mode enumeration, interval subdivision, or numerical
certificate occurs in this reduction.
-/

/-- The signed intrinsic even endpoint form in coefficient coordinates. -/
def factorTwoIntrinsicStaticEvenQuadratic
    (sigma c0 c2 : ℝ) : ℝ :=
  factorTwoStructuralPhaseLow00 sigma * c0 ^ 2 +
    2 * factorTwoStructuralPhaseLow02 sigma * c0 * c2 +
    factorTwoStructuralPhaseLow22 sigma * c2 ^ 2

/-- The oppositely signed intrinsic odd endpoint form. -/
def factorTwoIntrinsicStaticOddQuadratic
    (sigma c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicOddPhaseQuadratic (-sigma) c1 c3

/-- The complete alternating coordinate on the two intrinsic planes. -/
def factorTwoIntrinsicStaticAlternating
    (c0 c2 c1 c3 : ℝ) : ℝ :=
  c0 * factorTwoIntrinsicAlternatingRow0 c1 c3 +
    c2 * factorTwoIntrinsicAlternatingRow2 c1 c3

/-- One of the two phase-free static parity splits.  `sigma = 1` is the
even-plus/odd-minus split and `sigma = -1` is the opposite split. -/
def factorTwoIntrinsicStaticSplit
    (sigma c0 c2 c1 c3 : ℝ) : ℝ :=
  factorTwoIntrinsicStaticEvenQuadratic sigma c0 c2 +
    factorTwoIntrinsicStaticOddQuadratic sigma c1 c3 +
    factorTwoIntrinsicStaticAlternating c0 c2 c1 c3

/-- Exact profile interpretation of the even diagonal. -/
theorem factorTwoIntrinsicStaticEvenQuadratic_eq_profile
    (sigma c0 c2 : ℝ) :
    factorTwoIntrinsicStaticEvenQuadratic sigma c0 c2 =
      factorTwoEndpointPhaseDiagonal
        (factorTwoEvenStructuralLowProfile c0 c2) sigma := by
  unfold factorTwoIntrinsicStaticEvenQuadratic
  rw [factorTwoStructuralPhaseLow_endpoint_quadratic]
  rfl

/-- Exact profile interpretation of the odd diagonal. -/
theorem factorTwoIntrinsicStaticOddQuadratic_eq_profile
    (sigma c1 c3 : ℝ) :
    factorTwoIntrinsicStaticOddQuadratic sigma c1 c3 =
      factorTwoEndpointPhaseDiagonal
        (factorTwoOddStructuralLowProfile c1 c3) (-sigma) := by
  unfold factorTwoIntrinsicStaticOddQuadratic
    factorTwoIntrinsicOddPhaseQuadratic
  change
    factorTwoOddStructuralPhaseLow11 (-sigma) * c1 ^ 2 +
          2 * factorTwoOddStructuralPhaseLow13 (-sigma) * c1 * c3 +
          factorTwoOddStructuralPhaseLow33 (-sigma) * c3 ^ 2 = _
  rw [factorTwoOddStructuralPhaseLow_quadratic]
  rfl

/-- Exact profile interpretation of the alternating bilinear coordinate. -/
theorem factorTwoIntrinsicStaticAlternating_eq_profile
    (c0 c2 c1 c3 : ℝ) :
    factorTwoIntrinsicStaticAlternating c0 c2 c1 c3 =
      factorTwoCenteredAlternatingCoupling
        (factorTwoEvenStructuralLowProfile c0 c2)
        (factorTwoOddStructuralLowProfile c1 c3) := by
  have hEven := factorTwoCenteredAlternatingCoupling_structuralLow
    c0 c2 (factorTwoOddStructuralLowProfile c1 c3)
      (continuous_factorTwoOddStructuralLowProfile c1 c3)
  have h0 := factorTwoCenteredAlternatingCoupling_oddStructuralLow_right
    centeredEvenP0 (by unfold centeredEvenP0; fun_prop) c1 c3
  have h2 := factorTwoCenteredAlternatingCoupling_oddStructuralLow_right
    centeredEvenP2 (by unfold centeredEvenP2; fun_prop) c1 c3
  unfold factorTwoIntrinsicStaticAlternating
  rw [hEven, h0, h2]
  unfold factorTwoIntrinsicAlternatingRow0
    factorTwoIntrinsicAlternatingRow2 factorTwoIntrinsicAlternating01
    factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating21
    factorTwoIntrinsicAlternating23
  ring

/-- Exact profile interpretation of either complete static split. -/
theorem factorTwoIntrinsicStaticSplit_eq_profile
    (sigma c0 c2 c1 c3 : ℝ) :
    factorTwoIntrinsicStaticSplit sigma c0 c2 c1 c3 =
      factorTwoEndpointPhaseDiagonal
          (factorTwoEvenStructuralLowProfile c0 c2) sigma +
        factorTwoEndpointPhaseDiagonal
          (factorTwoOddStructuralLowProfile c1 c3) (-sigma) +
        factorTwoCenteredAlternatingCoupling
          (factorTwoEvenStructuralLowProfile c0 c2)
          (factorTwoOddStructuralLowProfile c1 c3) := by
  rw [factorTwoIntrinsicStaticSplit,
    factorTwoIntrinsicStaticEvenQuadratic_eq_profile,
    factorTwoIntrinsicStaticOddQuadratic_eq_profile,
    factorTwoIntrinsicStaticAlternating_eq_profile]

/-! ## Full-series normal form for the thin split -/

/-- The favourable growing square in the even-plus/odd-minus split. -/
def factorTwoStaticPlusGrowingSquare (e o : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA * Real.exp yoshidaEndpointA *
    (centeredCoshMoment e (yoshidaEndpointA / 2) +
      centeredSinhMoment o (yoshidaEndpointA / 2)) ^ 2

/-- The complete adverse decaying family.  It remains one genuine infinite
Gram sum in the difference of the even and odd moment rows. -/
def factorTwoStaticPlusDecayingGram (e o : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA * ∑' m : ℕ,
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      (centeredCoshMoment e
          (yoshidaEndpointA * oddRate (m + 1)) -
        centeredSinhMoment o
          (yoshidaEndpointA * oddRate (m + 1))) ^ 2

/-- Both retained prime atoms in their exact static-split signs. -/
def factorTwoStaticPlusPrimeRemainder (e o : ℝ → ℝ) : ℝ :=
  -factorTwoCenteredPrimeBlock e + factorTwoCenteredPrimeBlock o -
    (Real.log 3 / Real.sqrt 3) *
      (factorTwoCenteredCrossCorrelation o e
          (factorTwoPrimeShift / yoshidaEndpointA) -
        factorTwoCenteredCrossCorrelation e o
          (factorTwoPrimeShift / yoshidaEndpointA))

theorem factorTwoStaticPlusDecayingGram_nonneg (e o : ℝ → ℝ) :
    0 ≤ factorTwoStaticPlusDecayingGram e o := by
  unfold factorTwoStaticPlusDecayingGram
  exact mul_nonneg yoshidaEndpointA_pos.le
    (tsum_nonneg fun m ↦ mul_nonneg (Real.exp_pos _).le (sq_nonneg _))

theorem factorTwoStaticPlusGrowingSquare_nonneg (e o : ℝ → ℝ) :
    0 ≤ factorTwoStaticPlusGrowingSquare e o := by
  unfold factorTwoStaticPlusGrowingSquare
  exact mul_nonneg
    (mul_nonneg yoshidaEndpointA_pos.le (Real.exp_pos _).le)
    (sq_nonneg _)

/-- Exact full-series identity for the thin static split.  The entire
decaying rank family is kept as one adverse Gram, while the growing row is
one favourable square and both prime atoms remain coupled. -/
theorem factorTwoStaticPlus_eq_clean_add_growing_sub_decaying_add_prime
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o) :
    factorTwoEndpointPhaseDiagonal e 1 +
        factorTwoEndpointPhaseDiagonal o (-1) +
        factorTwoCenteredAlternatingCoupling e o =
      yoshidaEndpointOddCleanQuadratic e +
        yoshidaEndpointOddCleanQuadratic o +
        factorTwoStaticPlusGrowingSquare e o -
        factorTwoStaticPlusDecayingGram e o +
        factorTwoStaticPlusPrimeRemainder e o := by
  let qe : ℕ → ℝ := fun m ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment e
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  let qo : ℕ → ℝ := fun m ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredSinhMoment o
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  let qj : ℕ → ℝ := fun m ↦
    2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment e
        (yoshidaEndpointA * oddRate (m + 1)) *
      centeredSinhMoment o
        (yoshidaEndpointA * oddRate (m + 1))
  have hqe : Summable qe := by
    simpa only [qe] using
      (hasSum_factorTwoCenteredArch_evenRankSquares e hec heven).summable
  have hqo : Summable qo := by
    simpa only [qo] using
      (hasSum_factorTwoCenteredArch_oddRankSquares o hoc hodd).summable
  have hqj : Summable qj := by
    simpa only [qj] using
      summable_factorTwoCenteredAlternatingRankProducts
        e o hec hoc heven hodd
  have hsq :
      (∑' m : ℕ,
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (centeredCoshMoment e
              (yoshidaEndpointA * oddRate (m + 1)) -
            centeredSinhMoment o
              (yoshidaEndpointA * oddRate (m + 1))) ^ 2) =
        (∑' m : ℕ, qe m) + (∑' m : ℕ, qo m) -
          ∑' m : ℕ, qj m := by
    rw [show (fun m : ℕ ↦
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          (centeredCoshMoment e
              (yoshidaEndpointA * oddRate (m + 1)) -
            centeredSinhMoment o
              (yoshidaEndpointA * oddRate (m + 1))) ^ 2) =
      fun m ↦ qe m + qo m - qj m by
        funext m
        dsimp only [qe, qo, qj]
        ring]
    rw [(hqe.add hqo).tsum_sub hqj, hqe.tsum_add hqo]
  have heArch := factorTwoCenteredArchBlock_eq_evenRankSquares
    e hec heven
  have hoArch := factorTwoCenteredArchBlock_eq_oddRankSquares
    o hoc hodd
  have hjArch := factorTwoCenteredAlternatingArch_eq_rankProducts
    e o hec hoc heven hodd
  unfold factorTwoEndpointPhaseDiagonal
  rw [symmetricPerturbation_eq_arch_sub_primeBlock,
    symmetricPerturbation_eq_arch_sub_primeBlock]
  unfold factorTwoCenteredAlternatingCoupling
  rw [heArch, hoArch, hjArch]
  unfold factorTwoStaticPlusGrowingSquare
    factorTwoStaticPlusDecayingGram factorTwoStaticPlusPrimeRemainder
  rw [hsq]
  dsimp only [qe, qo, qj]
  ring

private theorem even_factorTwoEvenStructuralLowProfile_static
    (c0 c2 : ℝ) :
    Function.Even (factorTwoEvenStructuralLowProfile c0 c2) := by
  intro x
  unfold factorTwoEvenStructuralLowProfile centeredEvenP0 centeredEvenP2
  ring

private theorem odd_factorTwoOddStructuralLowProfile_static
    (c1 c3 : ℝ) :
    Function.Odd (factorTwoOddStructuralLowProfile c1 c3) := by
  intro x
  unfold factorTwoOddStructuralLowProfile centeredP1 centeredP3
  ring

/-- On the intrinsic planes, the thin static split is exactly one
full-series domination problem. -/
theorem factorTwoIntrinsicStaticPlus_eq_fullSeries
    (c0 c2 c1 c3 : ℝ) :
    factorTwoIntrinsicStaticSplit 1 c0 c2 c1 c3 =
      yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c0 c2) +
        yoshidaEndpointOddCleanQuadratic
          (factorTwoOddStructuralLowProfile c1 c3) +
        factorTwoStaticPlusGrowingSquare
          (factorTwoEvenStructuralLowProfile c0 c2)
          (factorTwoOddStructuralLowProfile c1 c3) -
        factorTwoStaticPlusDecayingGram
          (factorTwoEvenStructuralLowProfile c0 c2)
          (factorTwoOddStructuralLowProfile c1 c3) +
        factorTwoStaticPlusPrimeRemainder
          (factorTwoEvenStructuralLowProfile c0 c2)
          (factorTwoOddStructuralLowProfile c1 c3) := by
  rw [factorTwoIntrinsicStaticSplit_eq_profile]
  exact factorTwoStaticPlus_eq_clean_add_growing_sub_decaying_add_prime
    _ _ (continuous_factorTwoEvenStructuralLowProfile c0 c2)
    (continuous_factorTwoOddStructuralLowProfile c1 c3)
    (even_factorTwoEvenStructuralLowProfile_static c0 c2)
    (odd_factorTwoOddStructuralLowProfile_static c1 c3)

/-- The sole analytic inequality left by the complete rank decomposition of
the thin split. -/
def FactorTwoIntrinsicStaticPlusFullSeriesDomination : Prop :=
  ∀ c0 c2 c1 c3 : ℝ,
    factorTwoStaticPlusDecayingGram
        (factorTwoEvenStructuralLowProfile c0 c2)
        (factorTwoOddStructuralLowProfile c1 c3) ≤
      yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c0 c2) +
        yoshidaEndpointOddCleanQuadratic
          (factorTwoOddStructuralLowProfile c1 c3) +
        factorTwoStaticPlusGrowingSquare
          (factorTwoEvenStructuralLowProfile c0 c2)
          (factorTwoOddStructuralLowProfile c1 c3) +
        factorTwoStaticPlusPrimeRemainder
          (factorTwoEvenStructuralLowProfile c0 c2)
          (factorTwoOddStructuralLowProfile c1 c3)

/-! ## Endpoint signs already discharged structurally -/

theorem factorTwoIntrinsicStaticEven_plus_nonneg (c0 c2 : ℝ) :
    0 ≤ factorTwoIntrinsicStaticEvenQuadratic 1 c0 c2 := by
  by_cases hne : c0 ≠ 0 ∨ c2 ≠ 0
  · rw [factorTwoIntrinsicStaticEvenQuadratic_eq_profile]
    unfold factorTwoEndpointPhaseDiagonal
    simpa only [one_mul] using
      (factorTwoIntrinsicEven_plus_endpoint_structural_pos c0 c2 hne).le
  · simp only [not_or, not_not] at hne
    rcases hne with ⟨rfl, rfl⟩
    simp [factorTwoIntrinsicStaticEvenQuadratic]

theorem factorTwoIntrinsicStaticEven_minus_nonneg (c0 c2 : ℝ) :
    0 ≤ factorTwoIntrinsicStaticEvenQuadratic (-1) c0 c2 := by
  by_cases hne : c0 ≠ 0 ∨ c2 ≠ 0
  · rw [factorTwoIntrinsicStaticEvenQuadratic_eq_profile]
    unfold factorTwoEndpointPhaseDiagonal
    simpa only [neg_one_mul, sub_eq_add_neg] using
      (factorTwoIntrinsicEven_minus_endpoint_kernel_pos c0 c2 hne).le
  · simp only [not_or, not_not] at hne
    rcases hne with ⟨rfl, rfl⟩
    simp [factorTwoIntrinsicStaticEvenQuadratic]

theorem factorTwoIntrinsicStaticOdd_plus_nonneg (c1 c3 : ℝ) :
    0 ≤ factorTwoIntrinsicStaticOddQuadratic 1 c1 c3 := by
  by_cases hne : c1 ≠ 0 ∨ c3 ≠ 0
  · rw [factorTwoIntrinsicStaticOddQuadratic_eq_profile]
    unfold factorTwoEndpointPhaseDiagonal
    simpa only [neg_one_mul, sub_eq_add_neg] using
      (signed_oddStructuralLow_forms_positive.2 c1 c3 hne).le
  · simp only [not_or, not_not] at hne
    rcases hne with ⟨rfl, rfl⟩
    simp [factorTwoIntrinsicStaticOddQuadratic,
      factorTwoIntrinsicOddPhaseQuadratic]

theorem factorTwoIntrinsicStaticOdd_minus_nonneg (c1 c3 : ℝ) :
    0 ≤ factorTwoIntrinsicStaticOddQuadratic (-1) c1 c3 := by
  by_cases hne : c1 ≠ 0 ∨ c3 ≠ 0
  · rw [factorTwoIntrinsicStaticOddQuadratic_eq_profile]
    unfold factorTwoEndpointPhaseDiagonal
    simpa only [neg_neg, one_mul] using
      (signed_oddStructuralLow_forms_positive.1 c1 c3 hne).le
  · simp only [not_or, not_not] at hne
    rcases hne with ⟨rfl, rfl⟩
    simp [factorTwoIntrinsicStaticOddQuadratic,
      factorTwoIntrinsicOddPhaseQuadratic]

/-! ## Exact coupled Cauchy boundary -/

/-- The sharp static-split condition at sign `sigma`.  It keeps the whole
alternating bilinear coordinate squared before comparison with the two
complete signed endpoint forms. -/
def FactorTwoIntrinsicStaticCauchy (sigma : ℝ) : Prop :=
  ∀ c0 c2 c1 c3 : ℝ,
    factorTwoIntrinsicStaticAlternating c0 c2 c1 c3 ^ 2 ≤
      4 * factorTwoIntrinsicStaticEvenQuadratic sigma c0 c2 *
        factorTwoIntrinsicStaticOddQuadratic sigma c1 c3

/-- With nonnegative endpoint diagonals, positivity of the complete static
split is exactly the unsplit four-variable Cauchy inequality. -/
theorem factorTwoIntrinsicStaticSplit_nonneg_iff_cauchy
    (sigma : ℝ)
    (hEven : ∀ c0 c2 : ℝ,
      0 ≤ factorTwoIntrinsicStaticEvenQuadratic sigma c0 c2)
    (hOdd : ∀ c1 c3 : ℝ,
      0 ≤ factorTwoIntrinsicStaticOddQuadratic sigma c1 c3) :
    (∀ c0 c2 c1 c3 : ℝ,
        0 ≤ factorTwoIntrinsicStaticSplit sigma c0 c2 c1 c3) ↔
      FactorTwoIntrinsicStaticCauchy sigma := by
  constructor
  · intro hsplit c0 c2 c1 c3
    let E := factorTwoIntrinsicStaticEvenQuadratic sigma c0 c2
    let O := factorTwoIntrinsicStaticOddQuadratic sigma c1 c3
    let J := factorTwoIntrinsicStaticAlternating c0 c2 c1 c3
    have hpencil : ∀ r s : ℝ,
        0 ≤ E * r ^ 2 + 2 * (J / 2) * r * s + O * s ^ 2 := by
      intro r s
      have h := hsplit (r * c0) (r * c2) (s * c1) (s * c3)
      dsimp only [E, O, J]
      unfold factorTwoIntrinsicStaticSplit at h
      unfold
        factorTwoIntrinsicStaticEvenQuadratic
        factorTwoIntrinsicStaticOddQuadratic
        factorTwoIntrinsicStaticAlternating
        factorTwoIntrinsicOddPhaseQuadratic
        factorTwoIntrinsicAlternatingRow0
        factorTwoIntrinsicAlternatingRow2 at h ⊢
      nlinarith
    have hcoeff :=
      (real_quadratic_pencil_nonneg_iff E O (J / 2)).mp hpencil
    dsimp only [E, O, J] at hcoeff ⊢
    nlinarith [hcoeff.2.2]
  · intro hCauchy c0 c2 c1 c3
    let E := factorTwoIntrinsicStaticEvenQuadratic sigma c0 c2
    let O := factorTwoIntrinsicStaticOddQuadratic sigma c1 c3
    let J := factorTwoIntrinsicStaticAlternating c0 c2 c1 c3
    have hE : 0 ≤ E := by simpa only [E] using hEven c0 c2
    have hO : 0 ≤ O := by simpa only [O] using hOdd c1 c3
    have hJ : (J / 2) ^ 2 ≤ E * O := by
      have h := hCauchy c0 c2 c1 c3
      dsimp only [E, O, J] at h ⊢
      nlinarith
    have hpencil :=
      (real_quadratic_pencil_nonneg_iff E O (J / 2)).mpr
        ⟨hE, hO, hJ⟩
    have h := hpencil 1 1
    dsimp only [E, O, J] at h
    unfold factorTwoIntrinsicStaticSplit
    nlinarith

/-- The thin even-plus/odd-minus static split has one exact remaining
coupled Cauchy gate. -/
theorem factorTwoIntrinsicStaticPlus_nonneg_iff_cauchy :
    (∀ c0 c2 c1 c3 : ℝ,
        0 ≤ factorTwoIntrinsicStaticSplit 1 c0 c2 c1 c3) ↔
      FactorTwoIntrinsicStaticCauchy 1 :=
  factorTwoIntrinsicStaticSplit_nonneg_iff_cauchy 1
    factorTwoIntrinsicStaticEven_plus_nonneg
    factorTwoIntrinsicStaticOdd_plus_nonneg

/-- The full-series domination is equivalent to the sharp static Cauchy
gate, not merely a sufficient estimate. -/
theorem factorTwoIntrinsicStaticPlusCauchy_iff_fullSeriesDomination :
    FactorTwoIntrinsicStaticCauchy 1 ↔
      FactorTwoIntrinsicStaticPlusFullSeriesDomination := by
  rw [← factorTwoIntrinsicStaticPlus_nonneg_iff_cauchy]
  constructor
  · intro h c0 c2 c1 c3
    have hs := h c0 c2 c1 c3
    rw [factorTwoIntrinsicStaticPlus_eq_fullSeries] at hs
    linarith
  · intro h c0 c2 c1 c3
    rw [factorTwoIntrinsicStaticPlus_eq_fullSeries]
    have hs := h c0 c2 c1 c3
    linarith

/-- The even-minus/odd-plus static split has one exact remaining coupled
Cauchy gate. -/
theorem factorTwoIntrinsicStaticMinus_nonneg_iff_cauchy :
    (∀ c0 c2 c1 c3 : ℝ,
        0 ≤ factorTwoIntrinsicStaticSplit (-1) c0 c2 c1 c3) ↔
      FactorTwoIntrinsicStaticCauchy (-1) :=
  factorTwoIntrinsicStaticSplit_nonneg_iff_cauchy (-1)
    factorTwoIntrinsicStaticEven_minus_nonneg
    factorTwoIntrinsicStaticOdd_minus_nonneg

/-! ## Immediate phase-disk consequence -/

/-- The two exact static Cauchy inequalities close the entire intrinsic
four-mode phase disk. -/
theorem factorTwoEndpointChannelPhase_intrinsicLow_nonneg_of_staticCauchy
    (hPlus : FactorTwoIntrinsicStaticCauchy 1)
    (hMinus : FactorTwoIntrinsicStaticCauchy (-1))
    (c0 c2 c1 c3 a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c0 c2)
      (factorTwoOddStructuralLowProfile c1 c3) a b := by
  apply factorTwoEndpointChannelPhase_nonneg_of_profile_static_splits
    _ _ a b hab
  · intro r s
    have hsplit :=
      factorTwoIntrinsicStaticPlus_nonneg_iff_cauchy.mpr hPlus
        (r * c0) (r * c2) (s * c1) (s * c3)
    rw [← factorTwoIntrinsicStaticEvenQuadratic_eq_profile 1 c0 c2,
      ← factorTwoIntrinsicStaticOddQuadratic_eq_profile 1 c1 c3,
      ← factorTwoIntrinsicStaticAlternating_eq_profile]
    unfold factorTwoIntrinsicStaticSplit at hsplit
    unfold factorTwoIntrinsicStaticEvenQuadratic
      factorTwoIntrinsicStaticOddQuadratic
      factorTwoIntrinsicStaticAlternating
      factorTwoIntrinsicOddPhaseQuadratic
      factorTwoIntrinsicAlternatingRow0
      factorTwoIntrinsicAlternatingRow2 at hsplit ⊢
    nlinarith
  · intro r s
    have hsplit :=
      factorTwoIntrinsicStaticMinus_nonneg_iff_cauchy.mpr hMinus
        (r * c0) (r * c2) (s * c1) (s * c3)
    have hOddEq :=
      factorTwoIntrinsicStaticOddQuadratic_eq_profile (-1) c1 c3
    norm_num at hOddEq
    rw [← factorTwoIntrinsicStaticEvenQuadratic_eq_profile (-1) c0 c2,
      ← hOddEq,
      ← factorTwoIntrinsicStaticAlternating_eq_profile]
    unfold factorTwoIntrinsicStaticSplit at hsplit
    unfold factorTwoIntrinsicStaticEvenQuadratic
      factorTwoIntrinsicStaticOddQuadratic
      factorTwoIntrinsicStaticAlternating
      factorTwoIntrinsicOddPhaseQuadratic
      factorTwoIntrinsicAlternatingRow0
      factorTwoIntrinsicAlternatingRow2 at hsplit ⊢
    nlinarith

/-! ## Two-dimensional Schur residuals -/

/-- The odd Schur residual after eliminating the complete signed even
endpoint block.  Its nonnegativity is a binary quadratic condition in the
odd coefficients, not a `4 x 4` certificate. -/
def factorTwoIntrinsicStaticSchurResidual
    (sigma c1 c3 : ℝ) : ℝ :=
  4 * factorTwoIntrinsicEvenPhaseDet sigma *
      factorTwoIntrinsicStaticOddQuadratic sigma c1 c3 -
    factorTwoIntrinsicEvenAdjugateCoupling sigma c1 c3

/-- Exact Schur reduction of the unsplit static Cauchy inequality. -/
theorem factorTwoIntrinsicStaticCauchy_iff_schurResidual
    (sigma : ℝ)
    (h00 : 0 < factorTwoStructuralPhaseLow00 sigma)
    (hdet : 0 < factorTwoIntrinsicEvenPhaseDet sigma) :
    FactorTwoIntrinsicStaticCauchy sigma ↔
      ∀ c1 c3 : ℝ,
        0 ≤ factorTwoIntrinsicStaticSchurResidual sigma c1 c3 := by
  let q00 := factorTwoStructuralPhaseLow00 sigma
  let q02 := factorTwoStructuralPhaseLow02 sigma
  let q22 := factorTwoStructuralPhaseLow22 sigma
  let D := q00 * q22 - q02 ^ 2
  have hq00 : 0 < q00 := by simpa only [q00] using h00
  have hD : 0 < D := by
    simpa only [D, q00, q02, q22, factorTwoIntrinsicEvenPhaseDet] using hdet
  constructor
  · intro hCauchy c1 c3
    let j0 := factorTwoIntrinsicAlternatingRow0 c1 c3
    let j2 := factorTwoIntrinsicAlternatingRow2 c1 c3
    let O := factorTwoIntrinsicStaticOddQuadratic sigma c1 c3
    let A := q22 * j0 ^ 2 - 2 * q02 * j0 * j2 + q00 * j2 ^ 2
    let u := q22 * j0 - q02 * j2
    let v := q00 * j2 - q02 * j0
    have hO : 0 ≤ O := by
      have h := hCauchy 1 0 c1 c3
      dsimp only [factorTwoIntrinsicStaticAlternating,
        factorTwoIntrinsicStaticEvenQuadratic,
        q00, q02, q22, O] at h
      nlinarith [sq_nonneg
        (factorTwoIntrinsicAlternatingRow0 c1 c3)]
    have hA : 0 ≤ A := by
      dsimp only [A]
      exact twoByTwo_adjugateQuadratic_nonneg
        q00 q02 q22 j0 j2 hq00 hD
    have hlinear : u * j0 + v * j2 = A := by
      dsimp only [u, v, A]
      ring
    have henergy :
        q00 * u ^ 2 + 2 * q02 * u * v + q22 * v ^ 2 = D * A := by
      dsimp only [u, v, D, A]
      ring
    have hchosen := hCauchy u v c1 c3
    have hchosen' : A ^ 2 ≤ 4 * (D * A) * O := by
      dsimp only [factorTwoIntrinsicStaticAlternating,
        factorTwoIntrinsicStaticEvenQuadratic] at hchosen
      dsimp only [q00, q02, q22, j0, j2, O] at hlinear henergy hchosen ⊢
      rw [hlinear, henergy] at hchosen
      exact hchosen
    have hresidual : 0 ≤ 4 * D * O - A := by
      rcases hA.eq_or_lt with hAzero | hApos
      · have hAzero' : A = 0 := hAzero.symm
        rw [hAzero', sub_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) hD.le) hO
      · nlinarith
    simpa only [factorTwoIntrinsicStaticSchurResidual,
      factorTwoIntrinsicEvenPhaseDet,
      factorTwoIntrinsicEvenAdjugateCoupling,
      D, A, O, q00, q02, q22, j0, j2] using hresidual
  · intro hResidual c0 c2 c1 c3
    let j0 := factorTwoIntrinsicAlternatingRow0 c1 c3
    let j2 := factorTwoIntrinsicAlternatingRow2 c1 c3
    let E := factorTwoIntrinsicStaticEvenQuadratic sigma c0 c2
    let O := factorTwoIntrinsicStaticOddQuadratic sigma c1 c3
    let L := c0 * j0 + c2 * j2
    let A := q22 * j0 ^ 2 - 2 * q02 * j0 * j2 + q00 * j2 ^ 2
    have hE : 0 ≤ E := by
      have hscaled : 0 ≤ q00 * E := by
        rw [show q00 * E =
            (q00 * c0 + q02 * c2) ^ 2 + D * c2 ^ 2 by
          dsimp only [E, D, q00, q02, q22,
            factorTwoIntrinsicStaticEvenQuadratic]
          ring]
        exact add_nonneg (sq_nonneg _)
          (mul_nonneg hD.le (sq_nonneg _))
      nlinarith
    have hA : 0 ≤ A := by
      dsimp only [A]
      exact twoByTwo_adjugateQuadratic_nonneg
        q00 q02 q22 j0 j2 hq00 hD
    have hSchur : A ≤ 4 * D * O := by
      have h := hResidual c1 c3
      dsimp only [factorTwoIntrinsicStaticSchurResidual,
        factorTwoIntrinsicEvenPhaseDet,
        factorTwoIntrinsicEvenAdjugateCoupling,
        D, A, O, q00, q02, q22, j0, j2] at h
      linarith
    have hLagrange :
        E * A - D * L ^ 2 =
          (c0 * (q00 * j2 - q02 * j0) +
            c2 * (q02 * j2 - q22 * j0)) ^ 2 := by
      dsimp only [E, A, D, L, q00, q02, q22,
        factorTwoIntrinsicStaticEvenQuadratic]
      ring
    have hDA : D * L ^ 2 ≤ E * A := by
      nlinarith [sq_nonneg
        (c0 * (q00 * j2 - q02 * j0) +
          c2 * (q02 * j2 - q22 * j0))]
    have hEA : E * A ≤ E * (4 * D * O) :=
      mul_le_mul_of_nonneg_left hSchur hE
    have hfinal : L ^ 2 ≤ 4 * E * O := by
      have : D * L ^ 2 ≤ D * (4 * E * O) := by
        calc
          D * L ^ 2 ≤ E * A := hDA
          _ ≤ E * (4 * D * O) := hEA
          _ = D * (4 * E * O) := by ring
      nlinarith
    simpa only [factorTwoIntrinsicStaticAlternating,
      factorTwoIntrinsicAlternatingRow0,
      factorTwoIntrinsicAlternatingRow2, E, O, L] using hfinal

/-- Sharp binary Schur gate for the thin even-plus/odd-minus split. -/
theorem factorTwoIntrinsicStaticPlusCauchy_iff_schurResidual :
    FactorTwoIntrinsicStaticCauchy 1 ↔
      ∀ c1 c3 : ℝ,
        0 ≤ factorTwoIntrinsicStaticSchurResidual 1 c1 c3 :=
  factorTwoIntrinsicStaticCauchy_iff_schurResidual 1
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.1
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.2

/-- Sharp binary Schur gate for the even-minus/odd-plus split. -/
theorem factorTwoIntrinsicStaticMinusCauchy_iff_schurResidual :
    FactorTwoIntrinsicStaticCauchy (-1) ↔
      ∀ c1 c3 : ℝ,
        0 ≤ factorTwoIntrinsicStaticSchurResidual (-1) c1 c3 :=
  factorTwoIntrinsicStaticCauchy_iff_schurResidual (-1)
    factorTwoIntrinsicEven_minus_endpoint_kernel_gates.1
    factorTwoIntrinsicEven_minus_endpoint_kernel_gates.2

/-! ## Three exact scalar gates -/

def factorTwoIntrinsicStaticSchur00 (sigma : ℝ) : ℝ :=
  factorTwoIntrinsicStaticSchurResidual sigma 1 0

def factorTwoIntrinsicStaticSchur02 (sigma : ℝ) : ℝ :=
  (factorTwoIntrinsicStaticSchurResidual sigma 1 1 -
      factorTwoIntrinsicStaticSchurResidual sigma 1 0 -
      factorTwoIntrinsicStaticSchurResidual sigma 0 1) / 2

def factorTwoIntrinsicStaticSchur22 (sigma : ℝ) : ℝ :=
  factorTwoIntrinsicStaticSchurResidual sigma 0 1

/-- The Schur residual is exactly one binary quadratic; the three
coefficients are extracted by polarization, without evaluating any kernel. -/
theorem factorTwoIntrinsicStaticSchurResidual_expansion
    (sigma c1 c3 : ℝ) :
    factorTwoIntrinsicStaticSchurResidual sigma c1 c3 =
      factorTwoIntrinsicStaticSchur00 sigma * c1 ^ 2 +
        2 * factorTwoIntrinsicStaticSchur02 sigma * c1 * c3 +
        factorTwoIntrinsicStaticSchur22 sigma * c3 ^ 2 := by
  unfold factorTwoIntrinsicStaticSchur00
    factorTwoIntrinsicStaticSchur02 factorTwoIntrinsicStaticSchur22
    factorTwoIntrinsicStaticSchurResidual
    factorTwoIntrinsicStaticOddQuadratic
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicEvenAdjugateCoupling
    factorTwoIntrinsicAlternatingRow0
    factorTwoIntrinsicAlternatingRow2
  ring

/-- Exact Sylvester gate for either static Schur residual. -/
theorem factorTwoIntrinsicStaticSchurResidual_nonneg_iff
    (sigma : ℝ) :
    (∀ c1 c3 : ℝ,
        0 ≤ factorTwoIntrinsicStaticSchurResidual sigma c1 c3) ↔
      0 ≤ factorTwoIntrinsicStaticSchur00 sigma ∧
        0 ≤ factorTwoIntrinsicStaticSchur22 sigma ∧
        factorTwoIntrinsicStaticSchur02 sigma ^ 2 ≤
          factorTwoIntrinsicStaticSchur00 sigma *
            factorTwoIntrinsicStaticSchur22 sigma := by
  let A := factorTwoIntrinsicStaticSchur00 sigma
  let B := factorTwoIntrinsicStaticSchur22 sigma
  let C := factorTwoIntrinsicStaticSchur02 sigma
  have hpencil := real_quadratic_pencil_nonneg_iff A B C
  constructor
  · intro h
    apply hpencil.mp
    intro r s
    rw [← factorTwoIntrinsicStaticSchurResidual_expansion]
    exact h r s
  · intro h c1 c3
    have hp := hpencil.mpr h c1 c3
    rw [factorTwoIntrinsicStaticSchurResidual_expansion]
    simpa only [A, B, C] using hp

/-- The thin static split is now exactly three scalar inequalities.  Their
coupled determinant is retained intact. -/
theorem factorTwoIntrinsicStaticPlusCauchy_iff_three_gates :
    FactorTwoIntrinsicStaticCauchy 1 ↔
      0 ≤ factorTwoIntrinsicStaticSchur00 1 ∧
        0 ≤ factorTwoIntrinsicStaticSchur22 1 ∧
        factorTwoIntrinsicStaticSchur02 1 ^ 2 ≤
          factorTwoIntrinsicStaticSchur00 1 *
            factorTwoIntrinsicStaticSchur22 1 :=
  factorTwoIntrinsicStaticPlusCauchy_iff_schurResidual.trans
    (factorTwoIntrinsicStaticSchurResidual_nonneg_iff 1)

/-- The opposite static split has the same exact three-gate description. -/
theorem factorTwoIntrinsicStaticMinusCauchy_iff_three_gates :
    FactorTwoIntrinsicStaticCauchy (-1) ↔
      0 ≤ factorTwoIntrinsicStaticSchur00 (-1) ∧
        0 ≤ factorTwoIntrinsicStaticSchur22 (-1) ∧
        factorTwoIntrinsicStaticSchur02 (-1) ^ 2 ≤
          factorTwoIntrinsicStaticSchur00 (-1) *
            factorTwoIntrinsicStaticSchur22 (-1) :=
  factorTwoIntrinsicStaticMinusCauchy_iff_schurResidual.trans
    (factorTwoIntrinsicStaticSchurResidual_nonneg_iff (-1))

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
