import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedWeightedLp
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeMoments
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PerturbationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PrimeCorrelationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur

noncomputable section

open ThreeByThreeConvexPencil
open ThreeByThreeRankOneSchur
open YoshidaEndpointEvenProjectedWeightedLp
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenProjectedRemainderEnvelopeMoments
open YoshidaEndpointEvenProjectedRemainderEnvelopePolynomials
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenProjectedRemainderMoments
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointRegularCorrelation
open YoshidaEndpointScalarStructuralUpper
open YoshidaConstantBounds
open YoshidaRegularKernelBound
open YoshidaRegularKernelSchur
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicSixP4PrimeCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PerturbationStructural
open YoshidaFactorTwoPhaseSymmetricCarleman

/-!
# Exact-column Schur reduction at the positive endpoint

The coarse lower kernel is too small for the `P₄` column.  This reduction
keeps both genuine positive-endpoint cross entries and the genuine `P₄`
diagonal.  Only the `P₀/P₂` block is lowered, using the existing
UltraSharp Loewner theorem.

The remaining hypothesis is a weighted representer estimate.  It is the
ordinary two-dimensional Cauchy--Schwarz inequality in the retained endpoint
tail weight, together with a strict reserve for `P₄`; no determinant entry is
evaluated or enclosed.
-/

/-- The UltraSharp lower form with the *exact* positive-endpoint `P₄`
column and diagonal. -/
def factorTwoIntrinsicP024PlusUltraQuadratic
    (c0 c2 c4 : ℝ) : ℝ :=
  symmetricQuadratic
    evenPositiveEndpointUltraSharp00
    evenPositiveEndpointUltraSharp02
    (factorTwoIntrinsicFourP45Cross04 1)
    evenPositiveEndpointUltraSharp22
    (factorTwoIntrinsicFourP45Cross24 1)
    (factorTwoIntrinsicP4PhaseDiagonal 1)
    c0 c2 c4

/-- Replacing only the low `P₀/P₂` block by UltraSharp is a genuine
Loewner lowering of the exact endpoint form. -/
theorem factorTwoIntrinsicP024PlusUltraQuadratic_le_exact
    (c0 c2 c4 : ℝ) :
    factorTwoIntrinsicP024PlusUltraQuadratic c0 c2 c4 ≤
      symmetricQuadratic
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicP4PhaseDiagonal 1)
        c0 c2 c4 := by
  have hlow := evenPositiveEndpointUltraSharp_quadratic_le c0 c2
  unfold factorTwoIntrinsicStaticEvenQuadratic at hlow
  unfold factorTwoIntrinsicP024PlusUltraQuadratic symmetricQuadratic
  nlinarith

/-- A sharp weighted representer estimate for the two *exact* positive
endpoint `P₄` cross coordinates forces positivity of the exact-column
UltraSharp Schur determinant.

The functions `g0,g2` are deliberately left visible: a subsequent analytic
module may construct them from the clean tail representers and the symmetric
perturbation kernel. -/
theorem factorTwoIntrinsicP024PlusUltraDeterminant_pos_of_weighted_representers
    (g0 g2 : ℝ → ℝ) (kappa : ℝ) (hkappa : 0 < kappa)
    (hdualLp : ∀ c b : ℝ,
      MemLp (fun x : ℝ ↦
        (c * g0 x + b * g2 x) /
            Real.sqrt (yoshidaEndpointEvenTailWeight x)) 2
        (volume.restrict (Ioc (-1) 1)))
    (hcross0 : IntervalIntegrable
      (fun x ↦ g0 x * factorTwoCenteredP4 x)
      volume (-1) 1)
    (hcross2 : IntervalIntegrable
      (fun x ↦ g2 x * factorTwoCenteredP4 x)
      volume (-1) 1)
    (hcross0_eq :
      (∫ x : ℝ in -1..1, g0 x * factorTwoCenteredP4 x) =
        factorTwoIntrinsicFourP45Cross04 1)
    (hcross2_eq :
      (∫ x : ℝ in -1..1, g2 x * factorTwoCenteredP4 x) =
        factorTwoIntrinsicFourP45Cross24 1)
    (hdualGram : ∀ c b : ℝ,
      (∫ x : ℝ in -1..1,
        (c * g0 x + b * g2 x) ^ 2 /
            yoshidaEndpointEvenTailWeight x) ≤
        kappa * (evenPositiveEndpointUltraSharp00 * c ^ 2 +
          2 * evenPositiveEndpointUltraSharp02 * c * b +
          evenPositiveEndpointUltraSharp22 * b ^ 2))
    (hWeightedReserve :
      kappa * (∫ x : ℝ in -1..1,
        yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x ^ 2) <
        factorTwoIntrinsicP4PhaseDiagonal 1) :
    0 < symmetricDeterminant
      evenPositiveEndpointUltraSharp00
      evenPositiveEndpointUltraSharp02
      (factorTwoIntrinsicFourP45Cross04 1)
      evenPositiveEndpointUltraSharp22
      (factorTwoIntrinsicFourP45Cross24 1)
      (factorTwoIntrinsicP4PhaseDiagonal 1) := by
  have hminor : 0 <
      evenPositiveEndpointUltraSharp00 *
          evenPositiveEndpointUltraSharp22 -
        evenPositiveEndpointUltraSharp02 ^ 2 := by
    linarith [evenPositiveEndpointUltraSharp_principal_minors_pos.2.2]
  have hadj := weighted_low_tail_adjugate_le
    factorTwoCenteredP4 g0 g2
    (kappa * evenPositiveEndpointUltraSharp00)
    (kappa * evenPositiveEndpointUltraSharp02)
    (kappa * evenPositiveEndpointUltraSharp22)
    (mul_pos hkappa evenPositiveEndpointUltraSharp_principal_minors_pos.1)
    (by nlinarith [sq_pos_of_pos hkappa, hminor]) hdualLp
    (sqrt_tailWeight_mul_memLp_two factorTwoCenteredP4
      continuous_factorTwoCenteredP4)
    hcross0 hcross2 (fun c b ↦ by
      have h := hdualGram c b
      convert h using 1
      ring)
  rw [hcross0_eq, hcross2_eq] at hadj
  have hadj' :
      evenPositiveEndpointUltraSharp22 *
            factorTwoIntrinsicFourP45Cross04 1 ^ 2 -
          2 * evenPositiveEndpointUltraSharp02 *
            factorTwoIntrinsicFourP45Cross04 1 *
            factorTwoIntrinsicFourP45Cross24 1 +
          evenPositiveEndpointUltraSharp00 *
            factorTwoIntrinsicFourP45Cross24 1 ^ 2 ≤
        kappa *
          (evenPositiveEndpointUltraSharp00 *
              evenPositiveEndpointUltraSharp22 -
            evenPositiveEndpointUltraSharp02 ^ 2) *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x ^ 2) := by
    have hscaled :
        kappa *
            (evenPositiveEndpointUltraSharp22 *
                factorTwoIntrinsicFourP45Cross04 1 ^ 2 -
              2 * evenPositiveEndpointUltraSharp02 *
                factorTwoIntrinsicFourP45Cross04 1 *
                factorTwoIntrinsicFourP45Cross24 1 +
              evenPositiveEndpointUltraSharp00 *
                factorTwoIntrinsicFourP45Cross24 1 ^ 2) ≤
          kappa *
            (kappa *
              (evenPositiveEndpointUltraSharp00 *
                  evenPositiveEndpointUltraSharp22 -
                evenPositiveEndpointUltraSharp02 ^ 2) *
              (∫ x : ℝ in -1..1,
                yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x ^ 2)) := by
      convert hadj using 1 <;> ring
    exact le_of_mul_le_mul_left hscaled hkappa
  have hstrict := mul_lt_mul_of_pos_left hWeightedReserve hminor
  unfold symmetricDeterminant
  nlinarith [hadj']

/-- Final structural reduction of the genuine positive endpoint.  The low
Loewner step and the weighted Schur step together imply the exact endpoint
profile is positive, hence its exact determinant (and sequential Schur
leading scalar) is positive. -/
theorem factorTwoIntrinsicSixP4SchurLeading_plus_pos_of_weighted_representers
    (g0 g2 : ℝ → ℝ) (kappa : ℝ) (hkappa : 0 < kappa)
    (hdualLp : ∀ c b : ℝ,
      MemLp (fun x : ℝ ↦
        (c * g0 x + b * g2 x) /
            Real.sqrt (yoshidaEndpointEvenTailWeight x)) 2
        (volume.restrict (Ioc (-1) 1)))
    (hcross0 : IntervalIntegrable
      (fun x ↦ g0 x * factorTwoCenteredP4 x)
      volume (-1) 1)
    (hcross2 : IntervalIntegrable
      (fun x ↦ g2 x * factorTwoCenteredP4 x)
      volume (-1) 1)
    (hcross0_eq :
      (∫ x : ℝ in -1..1, g0 x * factorTwoCenteredP4 x) =
        factorTwoIntrinsicFourP45Cross04 1)
    (hcross2_eq :
      (∫ x : ℝ in -1..1, g2 x * factorTwoCenteredP4 x) =
        factorTwoIntrinsicFourP45Cross24 1)
    (hdualGram : ∀ c b : ℝ,
      (∫ x : ℝ in -1..1,
        (c * g0 x + b * g2 x) ^ 2 /
            yoshidaEndpointEvenTailWeight x) ≤
        kappa * (evenPositiveEndpointUltraSharp00 * c ^ 2 +
          2 * evenPositiveEndpointUltraSharp02 * c * b +
          evenPositiveEndpointUltraSharp22 * b ^ 2))
    (hWeightedReserve :
      kappa * (∫ x : ℝ in -1..1,
        yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x ^ 2) <
        factorTwoIntrinsicP4PhaseDiagonal 1) :
    0 < factorTwoIntrinsicSixP4SchurLeading 1 := by
  have hminor : 0 < leadingMinorTwo
      evenPositiveEndpointUltraSharp00
      evenPositiveEndpointUltraSharp02
      evenPositiveEndpointUltraSharp22 := by
    unfold leadingMinorTwo
    linarith [evenPositiveEndpointUltraSharp_principal_minors_pos.2.2]
  have hdet :=
    factorTwoIntrinsicP024PlusUltraDeterminant_pos_of_weighted_representers
      g0 g2 kappa hkappa hdualLp hcross0 hcross2 hcross0_eq hcross2_eq
      hdualGram hWeightedReserve
  apply factorTwoIntrinsicSixP4SchurLeading_pos_of_profile_pos 1
  intro c0 c2 c4 hne
  rw [factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic]
  have hultra : 0 < factorTwoIntrinsicP024PlusUltraQuadratic c0 c2 c4 :=
    symmetricQuadratic_pos
      evenPositiveEndpointUltraSharp00
      evenPositiveEndpointUltraSharp02
      (factorTwoIntrinsicFourP45Cross04 1)
      evenPositiveEndpointUltraSharp22
      (factorTwoIntrinsicFourP45Cross24 1)
      (factorTwoIntrinsicP4PhaseDiagonal 1)
      evenPositiveEndpointUltraSharp_principal_minors_pos.1
      hminor hdet c0 c2 c4 hne
  exact hultra.trans_le
    (factorTwoIntrinsicP024PlusUltraQuadratic_le_exact c0 c2 c4)

/-! ## Optimal witnesses for the single `P₄` row -/

/-- Exact retained weighted mass of `P₄`. -/
def factorTwoIntrinsicP4WeightedMass : ℝ :=
  ∫ x : ℝ in -1..1,
    yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x ^ 2

/-- The retained mass is strictly positive. -/
theorem factorTwoIntrinsicP4WeightedMass_pos :
    0 < factorTwoIntrinsicP4WeightedMass := by
  unfold factorTwoIntrinsicP4WeightedMass
  exact integral_tailWeight_mul_factorTwoCenteredP4_sq_pos

/-- Exact elementary value of the retained mass. -/
theorem factorTwoIntrinsicP4WeightedMass_eq :
    factorTwoIntrinsicP4WeightedMass =
      260 / 567 - (2 / 9 : ℝ) * Real.log 2 := by
  unfold factorTwoIntrinsicP4WeightedMass
  exact integral_tailWeight_mul_factorTwoCenteredP4_sq

/-- The optimal weighted representer aligned with `P₄` for the first
exact endpoint cross coordinate. -/
def factorTwoIntrinsicP4PlusAlignedRepresenter0 (x : ℝ) : ℝ :=
  (factorTwoIntrinsicFourP45Cross04 1 / factorTwoIntrinsicP4WeightedMass) *
    yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x

/-- The optimal weighted representer aligned with `P₄` for the second
exact endpoint cross coordinate. -/
def factorTwoIntrinsicP4PlusAlignedRepresenter2 (x : ℝ) : ℝ :=
  (factorTwoIntrinsicFourP45Cross24 1 / factorTwoIntrinsicP4WeightedMass) *
    yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x

private theorem alignedRepresenter_mul_P4_intervalIntegrable
    (u : ℝ) :
    IntervalIntegrable
      (fun x : ℝ ↦
        (u / factorTwoIntrinsicP4WeightedMass *
          yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x) *
          factorTwoCenteredP4 x)
      volume (-1) 1 := by
  have h := intervalIntegrable_tailWeight_mul_sq
    factorTwoCenteredP4 continuous_factorTwoCenteredP4
  apply h.const_mul (u / factorTwoIntrinsicP4WeightedMass) |>.congr
  intro x _hx
  ring

private theorem alignedRepresenter_pairing (u : ℝ) :
    (∫ x : ℝ in -1..1,
      (u / factorTwoIntrinsicP4WeightedMass *
        yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x) *
        factorTwoCenteredP4 x) = u := by
  have hne := factorTwoIntrinsicP4WeightedMass_pos.ne'
  rw [show (fun x : ℝ ↦
      (u / factorTwoIntrinsicP4WeightedMass *
        yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x) *
        factorTwoCenteredP4 x) =
      fun x ↦ (u / factorTwoIntrinsicP4WeightedMass) *
        (yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x ^ 2) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  unfold factorTwoIntrinsicP4WeightedMass
  exact div_mul_cancel₀ u hne

theorem factorTwoIntrinsicP4PlusAlignedRepresenter0_pairing :
    (∫ x : ℝ in -1..1,
      factorTwoIntrinsicP4PlusAlignedRepresenter0 x *
        factorTwoCenteredP4 x) = factorTwoIntrinsicFourP45Cross04 1 := by
  simpa only [factorTwoIntrinsicP4PlusAlignedRepresenter0] using
    alignedRepresenter_pairing (factorTwoIntrinsicFourP45Cross04 1)

theorem factorTwoIntrinsicP4PlusAlignedRepresenter2_pairing :
    (∫ x : ℝ in -1..1,
      factorTwoIntrinsicP4PlusAlignedRepresenter2 x *
        factorTwoCenteredP4 x) = factorTwoIntrinsicFourP45Cross24 1 := by
  simpa only [factorTwoIntrinsicP4PlusAlignedRepresenter2] using
    alignedRepresenter_pairing (factorTwoIntrinsicFourP45Cross24 1)

private theorem factorTwoIntrinsicP4PlusAlignedRepresenter_div_sqrt_memLp_two
    (c b : ℝ) :
    MemLp (fun x : ℝ ↦
      (c * factorTwoIntrinsicP4PlusAlignedRepresenter0 x +
        b * factorTwoIntrinsicP4PlusAlignedRepresenter2 x) /
          Real.sqrt (yoshidaEndpointEvenTailWeight x)) 2
      (volume.restrict (Ioc (-1) 1)) := by
  let ell : ℝ :=
    (c * factorTwoIntrinsicFourP45Cross04 1 +
      b * factorTwoIntrinsicFourP45Cross24 1) /
        factorTwoIntrinsicP4WeightedMass
  have hp4 := sqrt_tailWeight_mul_memLp_two
    factorTwoCenteredP4 continuous_factorTwoCenteredP4
  have hscaled := hp4.const_mul ell
  apply MeasureTheory.MemLp.ae_eq ?_ hscaled
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  have hW := yoshidaEndpointEvenTailWeight_pos_on_Icc hxIcc
  have hsqrt := Real.sq_sqrt hW.le
  have hsqrtPos := Real.sqrt_pos.2 hW
  dsimp only [ell]
  unfold factorTwoIntrinsicP4PlusAlignedRepresenter0
    factorTwoIntrinsicP4PlusAlignedRepresenter2
  field_simp [factorTwoIntrinsicP4WeightedMass_pos.ne', hsqrtPos.ne']
  rw [hsqrt]
  ring

private theorem factorTwoIntrinsicP4PlusAlignedDual_integral
    (c b : ℝ) :
    (∫ x : ℝ in -1..1,
      (c * factorTwoIntrinsicP4PlusAlignedRepresenter0 x +
        b * factorTwoIntrinsicP4PlusAlignedRepresenter2 x) ^ 2 /
          yoshidaEndpointEvenTailWeight x) =
      (c * factorTwoIntrinsicFourP45Cross04 1 +
        b * factorTwoIntrinsicFourP45Cross24 1) ^ 2 /
          factorTwoIntrinsicP4WeightedMass := by
  let ell : ℝ := c * factorTwoIntrinsicFourP45Cross04 1 +
    b * factorTwoIntrinsicFourP45Cross24 1
  have hmassInt := intervalIntegrable_tailWeight_mul_sq
    factorTwoCenteredP4 continuous_factorTwoCenteredP4
  have hae : (fun x : ℝ ↦
      (c * factorTwoIntrinsicP4PlusAlignedRepresenter0 x +
        b * factorTwoIntrinsicP4PlusAlignedRepresenter2 x) ^ 2 /
          yoshidaEndpointEvenTailWeight x) =ᵐ[volume.restrict (Ioc (-1) 1)]
      fun x ↦ (ell ^ 2 / factorTwoIntrinsicP4WeightedMass ^ 2) *
        (yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    have hW := yoshidaEndpointEvenTailWeight_pos_on_Icc hxIcc
    dsimp only [ell]
    unfold factorTwoIntrinsicP4PlusAlignedRepresenter0
      factorTwoIntrinsicP4PlusAlignedRepresenter2
    field_simp [factorTwoIntrinsicP4WeightedMass_pos.ne', hW.ne']
  have hae' : (fun x : ℝ ↦
      (c * factorTwoIntrinsicP4PlusAlignedRepresenter0 x +
        b * factorTwoIntrinsicP4PlusAlignedRepresenter2 x) ^ 2 /
          yoshidaEndpointEvenTailWeight x) =ᵐ[volume.restrict (uIoc (-1) 1)]
      fun x ↦ (ell ^ 2 / factorTwoIntrinsicP4WeightedMass ^ 2) *
        (yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x ^ 2) := by
    simpa only [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hae
  rw [intervalIntegral.integral_congr_ae_restrict hae',
    intervalIntegral.integral_const_mul]
  unfold factorTwoIntrinsicP4WeightedMass
  dsimp only [ell]
  field_simp [factorTwoIntrinsicP4WeightedMass_pos.ne']

/-- The sole sharp scalar needed by the aligned representers. -/
def factorTwoIntrinsicP4PlusUltraAdjugate : ℝ :=
  evenPositiveEndpointUltraSharp22 *
      factorTwoIntrinsicFourP45Cross04 1 ^ 2 -
    2 * evenPositiveEndpointUltraSharp02 *
      factorTwoIntrinsicFourP45Cross04 1 *
      factorTwoIntrinsicFourP45Cross24 1 +
    evenPositiveEndpointUltraSharp00 *
      factorTwoIntrinsicFourP45Cross24 1 ^ 2

/-- Sum of the two exact positive-endpoint `P₄` cross coordinates. -/
def factorTwoIntrinsicP4PlusCrossSum : ℝ :=
  factorTwoIntrinsicFourP45Cross04 1 +
    factorTwoIntrinsicFourP45Cross24 1

/-- Weak-direction difference of the two exact positive-endpoint `P₄`
cross coordinates. -/
def factorTwoIntrinsicP4PlusCrossDifference : ℝ :=
  factorTwoIntrinsicFourP45Cross24 1 -
    factorTwoIntrinsicFourP45Cross04 1

/-- The exact positive-endpoint `P₄` cross functional, evaluated on one
intrinsic low profile.  Keeping the two low coordinates combined here is what
preserves the weak-direction cancellation in the Schur adjugate. -/
def factorTwoIntrinsicP4PlusCrossFunctional (c b : ℝ) : ℝ :=
  yoshidaEndpointEvenCleanBilinear
      (factorTwoEvenStructuralLowProfile c b) factorTwoCenteredP4 +
    factorTwoCenteredSymmetricPerturbationBilinear
      (factorTwoEvenStructuralLowProfile c b) factorTwoCenteredP4

private theorem factorTwoIntrinsicP4_clean_cross_structuralLow
    (c b : ℝ) :
    yoshidaEndpointEvenCleanBilinear
        (factorTwoEvenStructuralLowProfile c b) factorTwoCenteredP4 =
      c * yoshidaEndpointEvenCleanBilinear
          centeredEvenP0 factorTwoCenteredP4 +
        b * yoshidaEndpointEvenCleanBilinear
          centeredEvenP2 factorTwoCenteredP4 := by
  have hprofile : factorTwoEvenStructuralLowProfile c b =
      yoshidaEndpointEvenLowProfile c b := by
    funext x
    unfold factorTwoEvenStructuralLowProfile yoshidaEndpointEvenLowProfile
      centeredEvenP0
    ring
  have h0 :
      yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 =
        ∫ x : ℝ in -1..1,
          yoshidaEndpointEvenTailRepresenter0 x * factorTwoCenteredP4 x := by
    have h := yoshidaEndpointEvenCleanBilinear_low_tail_eq_representers
      factorTwoCenteredP4 continuous_factorTwoCenteredP4
      even_factorTwoCenteredP4
      factorTwoCenteredP4_intrinsic_coefficients_zero.1
      factorTwoCenteredP4_intrinsic_coefficients_zero.2 1 0
    have hp0 : yoshidaEndpointEvenLowProfile 1 0 = centeredEvenP0 := by
      funext x
      unfold yoshidaEndpointEvenLowProfile centeredEvenP0
      ring
    rw [hp0] at h
    simpa using h
  have h2 :
      yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 =
        ∫ x : ℝ in -1..1,
          yoshidaEndpointEvenTailRepresenter2 x * factorTwoCenteredP4 x := by
    have h := yoshidaEndpointEvenCleanBilinear_low_tail_eq_representers
      factorTwoCenteredP4 continuous_factorTwoCenteredP4
      even_factorTwoCenteredP4
      factorTwoCenteredP4_intrinsic_coefficients_zero.1
      factorTwoCenteredP4_intrinsic_coefficients_zero.2 0 1
    have hp2 : yoshidaEndpointEvenLowProfile 0 1 = centeredEvenP2 := by
      funext x
      unfold yoshidaEndpointEvenLowProfile
      ring
    rw [hp2] at h
    simpa using h
  rw [hprofile,
    yoshidaEndpointEvenCleanBilinear_low_tail_eq_representers
      factorTwoCenteredP4 continuous_factorTwoCenteredP4
      even_factorTwoCenteredP4
      factorTwoCenteredP4_intrinsic_coefficients_zero.1
      factorTwoCenteredP4_intrinsic_coefficients_zero.2,
    ← h0, ← h2]

/-- Functional-level linearity of the exact positive-endpoint `P₄` cross
coordinate. -/
theorem factorTwoIntrinsicP4PlusCrossFunctional_eq
    (c b : ℝ) :
    factorTwoIntrinsicP4PlusCrossFunctional c b =
      c * factorTwoIntrinsicFourP45Cross04 1 +
        b * factorTwoIntrinsicFourP45Cross24 1 := by
  unfold factorTwoIntrinsicP4PlusCrossFunctional
    factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
  rw [factorTwoIntrinsicP4_clean_cross_structuralLow,
    factorTwoCenteredSymmetricPerturbationBilinear_structuralLow
      c b factorTwoCenteredP4 continuous_factorTwoCenteredP4]
  ring

/-- The sum coordinate is the whole functional on `P₀ + P₂`. -/
theorem factorTwoIntrinsicP4PlusCrossSum_eq_functional :
    factorTwoIntrinsicP4PlusCrossSum =
      factorTwoIntrinsicP4PlusCrossFunctional 1 1 := by
  rw [factorTwoIntrinsicP4PlusCrossFunctional_eq]
  unfold factorTwoIntrinsicP4PlusCrossSum
  ring

/-- The weak-direction coordinate is the whole functional on `P₂ - P₀`.
This rewrite occurs before any estimate is applied. -/
theorem factorTwoIntrinsicP4PlusCrossDifference_eq_functional :
    factorTwoIntrinsicP4PlusCrossDifference =
      factorTwoIntrinsicP4PlusCrossFunctional (-1) 1 := by
  rw [factorTwoIntrinsicP4PlusCrossFunctional_eq]
  unfold factorTwoIntrinsicP4PlusCrossDifference
  ring

/-- The strong low profile is an elementary nonnegative quadratic. -/
theorem factorTwoIntrinsicP4PlusCrossSum_profile (x : ℝ) :
    factorTwoEvenStructuralLowProfile 1 1 x = (3 * x ^ 2 + 1) / 2 := by
  unfold factorTwoEvenStructuralLowProfile centeredEvenP0 centeredEvenP2
  ring

/-- The weak low profile has an endpoint factor.  This is the cancellation
that is lost by estimating the two cross entries separately. -/
theorem factorTwoIntrinsicP4PlusCrossDifference_profile (x : ℝ) :
    factorTwoEvenStructuralLowProfile (-1) 1 x =
      (3 / 2 : ℝ) * (x - 1) * (x + 1) := by
  unfold factorTwoEvenStructuralLowProfile centeredEvenP0 centeredEvenP2
  ring

private theorem factorTwoCenteredCorrelationBilinear_structuralLow_p4
    (c b t : ℝ) :
    factorTwoCenteredCorrelationBilinear
        (factorTwoEvenStructuralLowProfile c b) factorTwoCenteredP4 t =
      c * factorTwoIntrinsicP4Correlation04 t +
        b * factorTwoIntrinsicP4Correlation24 t := by
  have h0 : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have h2 : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  rw [factorTwoEvenStructuralLowProfile_eq_smul_add]
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_add_left
      (c • centeredEvenP0) (b • centeredEvenP2) factorTwoCenteredP4
      (h0.const_smul c) (h2.const_smul b) continuous_factorTwoCenteredP4,
    factorTwoCenteredCrossCorrelation_add_right
      factorTwoCenteredP4 (c • centeredEvenP0) (b • centeredEvenP2)
      continuous_factorTwoCenteredP4 (h0.const_smul c) (h2.const_smul b),
    factorTwoCenteredCrossCorrelation_smul_left,
    factorTwoCenteredCrossCorrelation_smul_left,
    factorTwoCenteredCrossCorrelation_smul_right,
    factorTwoCenteredCrossCorrelation_smul_right]
  rw [← factorTwoCenteredCorrelationBilinear_p0_p4,
    ← factorTwoCenteredCorrelationBilinear_p2_p4]
  unfold factorTwoCenteredCorrelationBilinear
  ring

/-- Exact overlap polynomial seen by the strong `P₀ + P₂` profile. -/
theorem factorTwoIntrinsicP4PlusCrossSum_correlation (t : ℝ) :
    factorTwoCenteredCorrelationBilinear
        (factorTwoEvenStructuralLowProfile 1 1) factorTwoCenteredP4 t =
      factorTwoIntrinsicP4Correlation04 t +
        factorTwoIntrinsicP4Correlation24 t := by
  simpa using factorTwoCenteredCorrelationBilinear_structuralLow_p4 1 1 t

/-- Exact overlap polynomial seen by the endpoint-vanishing weak profile. -/
theorem factorTwoIntrinsicP4PlusCrossDifference_correlation (t : ℝ) :
    factorTwoCenteredCorrelationBilinear
        (factorTwoEvenStructuralLowProfile (-1) 1) factorTwoCenteredP4 t =
      factorTwoIntrinsicP4Correlation24 t -
        factorTwoIntrinsicP4Correlation04 t := by
  simpa [sub_eq_add_neg, add_comm] using
    factorTwoCenteredCorrelationBilinear_structuralLow_p4 (-1) 1 t

/-- The weak overlap has a double zero at both ends of the correlation
interval.  These factors must be retained through the pole estimates. -/
theorem factorTwoIntrinsicP4Correlation_difference_factorization (t : ℝ) :
    factorTwoIntrinsicP4Correlation24 t -
        factorTwoIntrinsicP4Correlation04 t =
      -(t ^ 2 * (t - 2) ^ 2 *
        (t ^ 3 + 4 * t ^ 2 - 12 * t + 6)) / 16 := by
  unfold factorTwoIntrinsicP4Correlation04
    factorTwoIntrinsicP4Correlation24
  ring

private theorem integral_inv_two_add_p4 :
    (∫ t : ℝ in 0..2, 1 / (2 + t)) = Real.log 2 := by
  let F : ℝ → ℝ := fun t ↦ Real.log (2 + t)
  have hderiv (t : ℝ) (ht : 2 + t ≠ 0) :
      HasDerivAt F (1 / (2 + t)) t := by
    have hadd : HasDerivAt (fun x : ℝ ↦ 2 + x) 1 t := by
      simpa using (hasDerivAt_const t 2).add (hasDerivAt_id t)
    simpa only [F, Function.comp_apply, one_div, mul_one] using
      (Real.hasDerivAt_log ht).comp t hadd
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / (2 + t))
      (uIcc (0 : ℝ) 2) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 2 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have hne : 2 + t ≠ 0 := by linarith [ht'.1]
    exact (continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hderiv t (by
      have ht' : t ∈ Icc (0 : ℝ) 2 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
      linarith [ht'.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num
  rw [show Real.log 4 = 2 * Real.log 2 by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
    ring]
  ring

private theorem intervalIntegrable_inv_two_add_p4 :
    IntervalIntegrable (fun t : ℝ ↦ 1 / (2 + t)) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have hne : 2 + t ≠ 0 := by linarith [ht'.1]
  exact (continuousAt_const.div
    (continuousAt_const.add continuousAt_id) hne).continuousWithinAt

/-- Exact pole contribution on the strong combined correlation. -/
theorem integral_poleWeight_mul_factorTwoIntrinsicP4Correlation_sum :
    (∫ t : ℝ in 0..2, evenStructuralPoleWeight t *
      (factorTwoIntrinsicP4Correlation04 t +
        factorTwoIntrinsicP4Correlation24 t)) =
      72 - 104 * Real.log 2 := by
  have heq : (∫ t : ℝ in 0..2, evenStructuralPoleWeight t *
      (factorTwoIntrinsicP4Correlation04 t +
        factorTwoIntrinsicP4Correlation24 t)) =
      ∫ t : ℝ in 0..2,
        (52 - 25 * t + (35 / 4 : ℝ) * t ^ 2 - t ^ 3 -
          (1 / 8 : ℝ) * t ^ 5) - 104 * (1 / (2 + t)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
    have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
    unfold evenStructuralPoleWeight factorTwoIntrinsicP4Correlation04
      factorTwoIntrinsicP4Correlation24
    field_simp [hp, hm]
    ring
  rw [heq]
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦ 52 - 25 * t + (35 / 4 : ℝ) * t ^ 2 - t ^ 3 -
        (1 / 8 : ℝ) * t ^ 5) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      52 - 25 * t + (35 / 4 : ℝ) * t ^ 2 - t ^ 3 -
        (1 / 8 : ℝ) * t ^ 5)).intervalIntegrable 0 2
  rw [intervalIntegral.integral_sub hpoly
      (intervalIntegrable_inv_two_add_p4.const_mul 104),
    intervalIntegral.integral_const_mul, integral_inv_two_add_p4]
  ring_nf
  repeat' first
    | rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
    | rw [intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

/-- Exact pole contribution on the endpoint-vanishing weak correlation. -/
theorem integral_poleWeight_mul_factorTwoIntrinsicP4Correlation_difference :
    (∫ t : ℝ in 0..2, evenStructuralPoleWeight t *
      (factorTwoIntrinsicP4Correlation24 t -
        factorTwoIntrinsicP4Correlation04 t)) =
      -(158 / 3 : ℝ) + 76 * Real.log 2 := by
  have heq : (∫ t : ℝ in 0..2, evenStructuralPoleWeight t *
      (factorTwoIntrinsicP4Correlation24 t -
        factorTwoIntrinsicP4Correlation04 t)) =
      ∫ t : ℝ in 0..2,
        (-38 + 19 * t - (35 / 4 : ℝ) * t ^ 2 +
          (5 / 2 : ℝ) * t ^ 3 - (1 / 8 : ℝ) * t ^ 5) +
          76 * (1 / (2 + t)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
    have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
    unfold evenStructuralPoleWeight factorTwoIntrinsicP4Correlation04
      factorTwoIntrinsicP4Correlation24
    field_simp [hp, hm]
    ring
  rw [heq]
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦ -38 + 19 * t - (35 / 4 : ℝ) * t ^ 2 +
        (5 / 2 : ℝ) * t ^ 3 - (1 / 8 : ℝ) * t ^ 5) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      -38 + 19 * t - (35 / 4 : ℝ) * t ^ 2 +
        (5 / 2 : ℝ) * t ^ 3 - (1 / 8 : ℝ) * t ^ 5))
      |>.intervalIntegrable 0 2
  rw [intervalIntegral.integral_add hpoly
      (intervalIntegrable_inv_two_add_p4.const_mul 76),
    intervalIntegral.integral_const_mul, integral_inv_two_add_p4]
  ring_nf
  repeat' rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

/-- Exact strong/weak-direction decomposition of the UltraSharp adjugate.
This identity isolates the genuinely delicate input: the difference
coordinate, rather than three unrelated matrix entries. -/
theorem factorTwoIntrinsicP4PlusUltraAdjugate_eq_sum_difference :
    factorTwoIntrinsicP4PlusUltraAdjugate =
      (141 / 100000 : ℝ) * factorTwoIntrinsicP4PlusCrossSum ^ 2 +
        (1 / 10000 : ℝ) * factorTwoIntrinsicP4PlusCrossSum *
          factorTwoIntrinsicP4PlusCrossDifference +
        (13679 / 100000 : ℝ) *
          factorTwoIntrinsicP4PlusCrossDifference ^ 2 := by
  unfold factorTwoIntrinsicP4PlusUltraAdjugate
    factorTwoIntrinsicP4PlusCrossSum
    factorTwoIntrinsicP4PlusCrossDifference
    evenPositiveEndpointUltraSharp00 evenPositiveEndpointUltraSharp02
    evenPositiveEndpointUltraSharp22
  ring

/-- Exact UltraSharp determinant. -/
theorem evenPositiveEndpointUltraSharp_det_eq :
    evenPositiveEndpointUltraSharp00 *
          evenPositiveEndpointUltraSharp22 -
        evenPositiveEndpointUltraSharp02 ^ 2 =
      (964357 / 1250000000 : ℝ) := by
  norm_num [evenPositiveEndpointUltraSharp00,
    evenPositiveEndpointUltraSharp02, evenPositiveEndpointUltraSharp22]

private theorem aligned_rankOne_dual_le
    (kappa : ℝ)
    (hAdj : factorTwoIntrinsicP4PlusUltraAdjugate ≤
      kappa *
        (evenPositiveEndpointUltraSharp00 *
            evenPositiveEndpointUltraSharp22 -
          evenPositiveEndpointUltraSharp02 ^ 2) *
        factorTwoIntrinsicP4WeightedMass)
    (c b : ℝ) :
      (c * factorTwoIntrinsicFourP45Cross04 1 +
        b * factorTwoIntrinsicFourP45Cross24 1) ^ 2 /
          factorTwoIntrinsicP4WeightedMass ≤
      kappa *
        (evenPositiveEndpointUltraSharp00 * c ^ 2 +
          2 * evenPositiveEndpointUltraSharp02 * c * b +
          evenPositiveEndpointUltraSharp22 * b ^ 2) := by
  let a := evenPositiveEndpointUltraSharp00
  let m := evenPositiveEndpointUltraSharp02
  let d := evenPositiveEndpointUltraSharp22
  let u := factorTwoIntrinsicFourP45Cross04 1
  let v := factorTwoIntrinsicFourP45Cross24 1
  let T := factorTwoIntrinsicP4WeightedMass
  let D := a * d - m ^ 2
  let A := d * u ^ 2 - 2 * m * u * v + a * v ^ 2
  let Q := a * c ^ 2 + 2 * m * c * b + d * b ^ 2
  let L := c * u + b * v
  have hD : 0 < D := by
    dsimp only [D, a, m, d]
    linarith [evenPositiveEndpointUltraSharp_principal_minors_pos.2.2]
  have hT : 0 < T := by
    simpa only [T] using factorTwoIntrinsicP4WeightedMass_pos
  have hQ : 0 ≤ Q := by
    by_cases hne : c ≠ 0 ∨ b ≠ 0
    · exact (real_twoByTwo_quadratic_pos a m d c b
        (by simpa only [a] using
          evenPositiveEndpointUltraSharp_principal_minors_pos.1)
        hD hne).le
    · push_neg at hne
      rcases hne with ⟨rfl, rfl⟩
      norm_num [Q]
  have hCauchy : D * L ^ 2 ≤ Q * A := by
    have hid : Q * A - D * L ^ 2 =
        ((m * u - a * v) * c + (d * u - m * v) * b) ^ 2 := by
      dsimp only [Q, A, D, L]
      ring
    nlinarith [sq_nonneg ((m * u - a * v) * c + (d * u - m * v) * b)]
  have hscaledAdj : Q * A ≤
      Q * (kappa * D * T) := by
    apply mul_le_mul_of_nonneg_left _ hQ
    simpa only [A, D, T, a, m, d, u, v,
      factorTwoIntrinsicP4PlusUltraAdjugate] using hAdj
  have hscaled : D * L ^ 2 ≤
      D * (T * (kappa * Q)) := by
    calc
      D * L ^ 2 ≤ Q * A := hCauchy
      _ ≤ Q * (kappa * D * T) := hscaledAdj
      _ = D * (T * (kappa * Q)) := by ring
  have hmain : L ^ 2 ≤ T * (kappa * Q) :=
    le_of_mul_le_mul_left hscaled hD
  rw [div_le_iff₀ hT]
  simpa only [L, T, Q, a, m, d, u, v, mul_assoc, mul_left_comm,
    mul_comm] using hmain

/-- Aligned-witness closure at any positive contraction scale.  All
functional-analytic hypotheses are discharged. -/
theorem factorTwoIntrinsicSixP4SchurLeading_plus_pos_of_aligned_bounds_at
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hAdj : factorTwoIntrinsicP4PlusUltraAdjugate ≤
      kappa *
        (evenPositiveEndpointUltraSharp00 *
            evenPositiveEndpointUltraSharp22 -
          evenPositiveEndpointUltraSharp02 ^ 2) *
        factorTwoIntrinsicP4WeightedMass)
    (hReserve :
      kappa * factorTwoIntrinsicP4WeightedMass <
        factorTwoIntrinsicP4PhaseDiagonal 1) :
    0 < factorTwoIntrinsicSixP4SchurLeading 1 := by
  apply factorTwoIntrinsicSixP4SchurLeading_plus_pos_of_weighted_representers
    factorTwoIntrinsicP4PlusAlignedRepresenter0
    factorTwoIntrinsicP4PlusAlignedRepresenter2 kappa hkappa
  · exact factorTwoIntrinsicP4PlusAlignedRepresenter_div_sqrt_memLp_two
  · simpa only [factorTwoIntrinsicP4PlusAlignedRepresenter0] using
      alignedRepresenter_mul_P4_intervalIntegrable
        (factorTwoIntrinsicFourP45Cross04 1)
  · simpa only [factorTwoIntrinsicP4PlusAlignedRepresenter2] using
      alignedRepresenter_mul_P4_intervalIntegrable
        (factorTwoIntrinsicFourP45Cross24 1)
  · exact factorTwoIntrinsicP4PlusAlignedRepresenter0_pairing
  · exact factorTwoIntrinsicP4PlusAlignedRepresenter2_pairing
  · intro c b
    rw [factorTwoIntrinsicP4PlusAlignedDual_integral]
    exact aligned_rankOne_dual_le kappa hAdj c b
  · simpa only [factorTwoIntrinsicP4WeightedMass] using hReserve

/-- Concrete `9/20` specialization of the aligned-witness closure. -/
theorem factorTwoIntrinsicSixP4SchurLeading_plus_pos_of_aligned_bounds
    (hAdj : factorTwoIntrinsicP4PlusUltraAdjugate ≤
      (9 / 20 : ℝ) *
        (evenPositiveEndpointUltraSharp00 *
            evenPositiveEndpointUltraSharp22 -
          evenPositiveEndpointUltraSharp02 ^ 2) *
        factorTwoIntrinsicP4WeightedMass)
    (hReserve :
      (9 / 20 : ℝ) * factorTwoIntrinsicP4WeightedMass <
        factorTwoIntrinsicP4PhaseDiagonal 1) :
    0 < factorTwoIntrinsicSixP4SchurLeading 1 := by
  exact factorTwoIntrinsicSixP4SchurLeading_plus_pos_of_aligned_bounds_at
    (9 / 20 : ℝ) (by norm_num) hAdj hReserve

/-! ## Structural `P₄` diagonal reserve -/

private def factorTwoIntrinsicP4Correlation44Shift (y : ℝ) : ℝ :=
  53 / 1152 + 37 / 128 * y - 25 / 32 * y ^ 2 -
    115 / 96 * y ^ 3 + 95 / 64 * y ^ 4 + 103 / 64 * y ^ 5 -
    35 / 96 * y ^ 6 - 25 / 32 * y ^ 7 - 35 / 128 * y ^ 8 -
    35 / 1152 * y ^ 9

private theorem factorTwoIntrinsicP4Correlation44_eq_shift (t : ℝ) :
    factorTwoIntrinsicP4Correlation44 t =
      factorTwoIntrinsicP4Correlation44Shift (t - 1) := by
  unfold factorTwoIntrinsicP4Correlation44
    factorTwoIntrinsicP4Correlation44Shift
  ring

private theorem hasDerivAt_factorTwoIntrinsicP4Correlation44Shift (y : ℝ) :
    HasDerivAt factorTwoIntrinsicP4Correlation44Shift
      (37 / 128 - 25 / 16 * y - 115 / 32 * y ^ 2 +
        95 / 16 * y ^ 3 + 515 / 64 * y ^ 4 - 35 / 16 * y ^ 5 -
        175 / 32 * y ^ 6 - 35 / 16 * y ^ 7 - 35 / 128 * y ^ 8) y := by
  unfold factorTwoIntrinsicP4Correlation44Shift
  convert ((((((((((hasDerivAt_const y (53 / 1152 : ℝ)).add
      ((hasDerivAt_id y).const_mul (37 / 128 : ℝ))).sub
      (((hasDerivAt_id y).pow 2).const_mul (25 / 32 : ℝ))).sub
      (((hasDerivAt_id y).pow 3).const_mul (115 / 96 : ℝ))).add
      (((hasDerivAt_id y).pow 4).const_mul (95 / 64 : ℝ))).add
      (((hasDerivAt_id y).pow 5).const_mul (103 / 64 : ℝ))).sub
      (((hasDerivAt_id y).pow 6).const_mul (35 / 96 : ℝ))).sub
      (((hasDerivAt_id y).pow 7).const_mul (25 / 32 : ℝ))).sub
      (((hasDerivAt_id y).pow 8).const_mul (35 / 128 : ℝ))).sub
      (((hasDerivAt_id y).pow 9).const_mul (35 / 1152 : ℝ))) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem factorTwoIntrinsicP4Correlation44Shift_strictAntiOn :
    StrictAntiOn factorTwoIntrinsicP4Correlation44Shift
      (Icc (1699 / 10000 : ℝ) (17 / 100)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (by unfold factorTwoIntrinsicP4Correlation44Shift; fun_prop)
  intro y hy
  rw [interior_Icc] at hy
  rw [(hasDerivAt_factorTwoIntrinsicP4Correlation44Shift y).deriv]
  have hy0 : 0 ≤ y := by linarith [hy.1]
  have hy2Lower := pow_lt_pow_left₀ hy.1
    (by norm_num : (0 : ℝ) ≤ 1699 / 10000)
    (by norm_num : (2 : ℕ) ≠ 0)
  have hy3Upper := pow_lt_pow_left₀ hy.2 hy0
    (by norm_num : (3 : ℕ) ≠ 0)
  have hy4Upper := pow_lt_pow_left₀ hy.2 hy0
    (by norm_num : (4 : ℕ) ≠ 0)
  have hy5 : 0 ≤ y ^ 5 := by positivity
  have hy6 : 0 ≤ y ^ 6 := by positivity
  have hy7 : 0 ≤ y ^ 7 := by positivity
  have hy8 : 0 ≤ y ^ 8 := by positivity
  norm_num at hy2Lower hy3Upper hy4Upper ⊢
  nlinarith

/-- A sharp rational box for the retained `p = 3` `P₄` autocorrelation.
The proof is monotonicity of its exact overlap polynomial on the already
proved logarithmic lag interval. -/
theorem factorTwoIntrinsicP4PrimeCorrelation44_bounds :
    (68143 / 1000000 : ℝ) < factorTwoIntrinsicP4Correlation44
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      factorTwoIntrinsicP4Correlation44
          (factorTwoPrimeShift / yoshidaEndpointA) <
        (68144 / 1000000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 1
  let a : ℝ := 16992 / 100000
  let b : ℝ := 16993 / 100000
  have htau := factorTwoPrimeRatio_sharp_bounds
  have hya : a < y := by
    dsimp only [a, y, tau]
    linarith [htau.1]
  have hyb : y < b := by
    dsimp only [b, y, tau]
    linarith [htau.2]
  have ha : a ∈ Icc (1699 / 10000 : ℝ) (17 / 100) := by
    norm_num [a]
  have hb : b ∈ Icc (1699 / 10000 : ℝ) (17 / 100) := by
    norm_num [b]
  have hy : y ∈ Icc (1699 / 10000 : ℝ) (17 / 100) := by
    constructor <;> dsimp only [y, tau] <;> linarith [htau.1, htau.2]
  have hlower :=
    factorTwoIntrinsicP4Correlation44Shift_strictAntiOn hy hb hyb
  have hupper :=
    factorTwoIntrinsicP4Correlation44Shift_strictAntiOn ha hy hya
  constructor
  · calc
      (68143 / 1000000 : ℝ) <
          factorTwoIntrinsicP4Correlation44Shift b := by
        norm_num [factorTwoIntrinsicP4Correlation44Shift, b]
      _ < factorTwoIntrinsicP4Correlation44Shift y := hlower
      _ = factorTwoIntrinsicP4Correlation44 tau := by
        rw [factorTwoIntrinsicP4Correlation44_eq_shift]
      _ = _ := by rfl
  · calc
      factorTwoIntrinsicP4Correlation44
          (factorTwoPrimeShift / yoshidaEndpointA) =
          factorTwoIntrinsicP4Correlation44Shift y := by
        rw [factorTwoIntrinsicP4Correlation44_eq_shift]
      _ < factorTwoIntrinsicP4Correlation44Shift a := hupper
      _ < (68144 / 1000000 : ℝ) := by
        norm_num [factorTwoIntrinsicP4Correlation44Shift, a]

private theorem abs_poleFreeAnalyticError_p4_le :
    |poleFreeAnalyticError factorTwoIntrinsicP4Correlation44| ≤
      (1 / 12000 : ℝ) := by
  have herr := abs_poleFreeAnalyticError_le
    factorTwoIntrinsicP4Correlation44
      continuous_factorTwoIntrinsicP4Correlation44
  have hL1 := integral_abs_centeredEndpointCorrelation_le_energy
    factorTwoCenteredP4 continuous_factorTwoCenteredP4
  simp_rw [centeredEndpointCorrelation_p4] at hL1
  rw [integral_factorTwoCenteredP4_sq] at hL1
  nlinarith

private theorem log_two_div_sqrt_two_p4_upper :
    Real.log 2 / Real.sqrt 2 < (49014 / 100000 : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hsqrtPos]
  nlinarith [strict_log_two_fine_bounds.2, sqrt_two_kernel_bounds.1]

/-- Structural lower bound for the complete positive-endpoint `P4`
perturbation.  Both retained prime atoms and the pole-free analytic remainder
remain in the exact decomposition until their final rational bounds. -/
theorem factorTwoCenteredSymmetricPerturbation_p4_lower :
    (-4416 / 25000 : ℝ) <
      factorTwoCenteredSymmetricPerturbation factorTwoCenteredP4 := by
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  let C : ℝ := factorTwoIntrinsicP4Correlation44
    (factorTwoPrimeShift / yoshidaEndpointA)
  have heq := factorTwoIntrinsicP4_perturbation_structural_eq.2.2
  have herr := abs_poleFreeAnalyticError_p4_le
  have herrLower : -(1 / 12000 : ℝ) ≤
      poleFreeAnalyticError factorTwoIntrinsicP4Correlation44 :=
    neg_le_of_abs_le herr
  have hlog := strict_log_two_fine_bounds.2
  have halpha := log_two_div_sqrt_two_p4_upper
  have hbeta := log_three_div_sqrt_three_kernel_bounds.2
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    positivity
  have hC := factorTwoIntrinsicP4PrimeCorrelation44_bounds
  have hC0 : 0 < C := by
    dsimp only [C]
    linarith [hC.1]
  have hprime : beta * C <
      (6343 / 10000 : ℝ) * (68144 / 1000000 : ℝ) := by
    calc
      beta * C < (6343 / 10000 : ℝ) * C :=
        mul_lt_mul_of_pos_right hbeta hC0
      _ < (6343 / 10000 : ℝ) * (68144 / 1000000 : ℝ) :=
        mul_lt_mul_of_pos_left hC.2 (by norm_num)
  rw [heq]
  unfold factorTwoIntrinsicP4PerturbationBase44
  dsimp only [beta, C] at hprime
  nlinarith

/-- The sharpened clean diagonal and exact perturbation decomposition leave
a strict `9/20` weighted `P4` reserve. -/
theorem factorTwoIntrinsicP4PlusWeightedReserve :
    (9 / 20 : ℝ) * factorTwoIntrinsicP4WeightedMass <
      factorTwoIntrinsicP4PhaseDiagonal 1 := by
  have hclean :=
    one_thousand_five_hundred_seventy_one_five_thousandths_lt_clean_p4
  have hpert := factorTwoCenteredSymmetricPerturbation_p4_lower
  have hlog := strict_log_two_bounds.1
  rw [factorTwoIntrinsicP4WeightedMass_eq]
  unfold factorTwoIntrinsicP4PhaseDiagonal
  norm_num only [one_mul]
  nlinarith

private def factorTwoIntrinsicP4CorrelationSumFactor (t : ℝ) : ℝ :=
  let y := t - 1
  y ^ 5 + 7 * y ^ 4 + 26 * y ^ 3 - 8 * y ^ 2 - 11 * y + 1

private def factorTwoIntrinsicP4CorrelationDifferenceFactor (t : ℝ) : ℝ :=
  let y := t - 1
  y ^ 3 + 7 * y ^ 2 - y - 1

private theorem factorTwoIntrinsicP4CorrelationSum_factorization (t : ℝ) :
    factorTwoIntrinsicP4CorrelationSum t =
      (1 - (t - 1) ^ 2) * factorTwoIntrinsicP4CorrelationSumFactor t / 16 := by
  unfold factorTwoIntrinsicP4CorrelationSum
    factorTwoIntrinsicP4CorrelationSumFactor
    factorTwoIntrinsicP4Correlation04 factorTwoIntrinsicP4Correlation24
  ring

private theorem factorTwoIntrinsicP4CorrelationDifference_factorization'
    (t : ℝ) :
    factorTwoIntrinsicP4CorrelationDifference t =
      -((1 - (t - 1) ^ 2) ^ 2 *
        factorTwoIntrinsicP4CorrelationDifferenceFactor t) / 16 := by
  unfold factorTwoIntrinsicP4CorrelationDifference
    factorTwoIntrinsicP4CorrelationDifferenceFactor
    factorTwoIntrinsicP4Correlation04 factorTwoIntrinsicP4Correlation24
  ring

private theorem continuous_factorTwoIntrinsicP4CorrelationSum :
    Continuous factorTwoIntrinsicP4CorrelationSum := by
  unfold factorTwoIntrinsicP4CorrelationSum
  exact continuous_factorTwoIntrinsicP4Correlation04.add
    continuous_factorTwoIntrinsicP4Correlation24

private theorem continuous_factorTwoIntrinsicP4CorrelationDifference :
    Continuous factorTwoIntrinsicP4CorrelationDifference := by
  unfold factorTwoIntrinsicP4CorrelationDifference
  exact continuous_factorTwoIntrinsicP4Correlation24.sub
    continuous_factorTwoIntrinsicP4Correlation04

private theorem integral_p4CorrelationSum_youngMajorant :
    (∫ t : ℝ in 0..2,
      (1 - (t - 1) ^ 2) *
        (factorTwoIntrinsicP4CorrelationSumFactor t ^ 2 / 6 + 3 / 2) / 16) =
      (12547 / 51480 : ℝ) := by
  unfold factorTwoIntrinsicP4CorrelationSumFactor
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_p4CorrelationDifference_youngMajorant :
    (∫ t : ℝ in 0..2,
      (1 - (t - 1) ^ 2) ^ 2 *
        (5 / 12 * factorTwoIntrinsicP4CorrelationDifferenceFactor t ^ 2 +
          3 / 5) / 16) = (152 / 1925 : ℝ) := by
  unfold factorTwoIntrinsicP4CorrelationDifferenceFactor
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

/-- The combined strong correlation has `L1` mass below `1/4`, proved from
its exact endpoint factor and one pointwise Young inequality. -/
theorem integral_abs_factorTwoIntrinsicP4CorrelationSum_lt :
    (∫ t : ℝ in 0..2, |factorTwoIntrinsicP4CorrelationSum t|) <
      (1 / 4 : ℝ) := by
  let M : ℝ → ℝ := fun t ↦
    (1 - (t - 1) ^ 2) *
      (factorTwoIntrinsicP4CorrelationSumFactor t ^ 2 / 6 + 3 / 2) / 16
  have hleft : IntervalIntegrable
      (fun t : ℝ ↦ |factorTwoIntrinsicP4CorrelationSum t|) volume 0 2 :=
    continuous_factorTwoIntrinsicP4CorrelationSum.abs.intervalIntegrable 0 2
  have hright : IntervalIntegrable M volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [M]
    unfold factorTwoIntrinsicP4CorrelationSumFactor
    fun_prop
  have hmono : (∫ t : ℝ in 0..2,
      |factorTwoIntrinsicP4CorrelationSum t|) ≤ ∫ t : ℝ in 0..2, M t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hleft hright
    intro t ht
    let w : ℝ := 1 - (t - 1) ^ 2
    let p : ℝ := factorTwoIntrinsicP4CorrelationSumFactor t
    have hw : 0 ≤ w := by
      have hprod : 0 ≤ t * (2 - t) :=
        mul_nonneg ht.1 (by linarith [ht.2])
      dsimp only [w]
      nlinarith
    have hyoung : |p| ≤ p ^ 2 / 6 + 3 / 2 := by
      nlinarith [sq_nonneg (|p| - 3), sq_abs p]
    rw [factorTwoIntrinsicP4CorrelationSum_factorization]
    dsimp only [M, w, p]
    rw [abs_div, abs_mul, abs_of_nonneg hw]
    norm_num
    have hmul := mul_le_mul_of_nonneg_left hyoung hw
    dsimp only [w, p] at hmul ⊢
    nlinarith
  rw [integral_p4CorrelationSum_youngMajorant] at hmono
  exact hmono.trans_lt (by norm_num)

/-- The endpoint-vanishing weak correlation has `L1` mass below `2/25`. -/
theorem integral_abs_factorTwoIntrinsicP4CorrelationDifference_lt :
    (∫ t : ℝ in 0..2,
      |factorTwoIntrinsicP4CorrelationDifference t|) < (2 / 25 : ℝ) := by
  let M : ℝ → ℝ := fun t ↦
    (1 - (t - 1) ^ 2) ^ 2 *
      (5 / 12 * factorTwoIntrinsicP4CorrelationDifferenceFactor t ^ 2 +
        3 / 5) / 16
  have hleft : IntervalIntegrable
      (fun t : ℝ ↦ |factorTwoIntrinsicP4CorrelationDifference t|)
      volume 0 2 :=
    continuous_factorTwoIntrinsicP4CorrelationDifference.abs.intervalIntegrable
      0 2
  have hright : IntervalIntegrable M volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [M]
    unfold factorTwoIntrinsicP4CorrelationDifferenceFactor
    fun_prop
  have hmono : (∫ t : ℝ in 0..2,
      |factorTwoIntrinsicP4CorrelationDifference t|) ≤
        ∫ t : ℝ in 0..2, M t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hleft hright
    intro t _ht
    let w : ℝ := (1 - (t - 1) ^ 2) ^ 2
    let q : ℝ := factorTwoIntrinsicP4CorrelationDifferenceFactor t
    have hw : 0 ≤ w := by positivity
    have hyoung : |q| ≤ 5 / 12 * q ^ 2 + 3 / 5 := by
      nlinarith [sq_nonneg (|q| - 6 / 5), sq_abs q]
    rw [factorTwoIntrinsicP4CorrelationDifference_factorization']
    dsimp only [M, w, q]
    rw [abs_div, abs_neg, abs_mul, abs_of_nonneg hw]
    norm_num
    have hmul := mul_le_mul_of_nonneg_left hyoung hw
    dsimp only [w, q] at hmul ⊢
    nlinarith
  rw [integral_p4CorrelationDifference_youngMajorant] at hmono
  exact hmono.trans_lt (by norm_num)

private theorem poleFreeAnalyticError_add
    (C D : ℝ → ℝ) (hC : Continuous C) (hD : Continuous D) :
    poleFreeAnalyticError C + poleFreeAnalyticError D =
      poleFreeAnalyticError (C + D) := by
  have hCI := intervalIntegrable_poleFreeAnalyticError C hC
  have hDI := intervalIntegrable_poleFreeAnalyticError D hD
  unfold poleFreeAnalyticError
  rw [← intervalIntegral.integral_add hCI hDI]
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only [Pi.add_apply]
  ring

private theorem poleFreeAnalyticError_sub
    (C D : ℝ → ℝ) (hC : Continuous C) (hD : Continuous D) :
    poleFreeAnalyticError C - poleFreeAnalyticError D =
      poleFreeAnalyticError (C - D) := by
  have hCI := intervalIntegrable_poleFreeAnalyticError C hC
  have hDI := intervalIntegrable_poleFreeAnalyticError D hD
  unfold poleFreeAnalyticError
  rw [← intervalIntegral.integral_sub hCI hDI]
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only [Pi.sub_apply]
  ring

private theorem abs_poleFreeAnalyticError_p4Sum_lt :
    |poleFreeAnalyticError factorTwoIntrinsicP4CorrelationSum| <
      (3 / 32000 : ℝ) := by
  have herr := abs_poleFreeAnalyticError_le
    factorTwoIntrinsicP4CorrelationSum
      continuous_factorTwoIntrinsicP4CorrelationSum
  have hL1 := integral_abs_factorTwoIntrinsicP4CorrelationSum_lt
  nlinarith

private theorem abs_poleFreeAnalyticError_p4Difference_lt :
    |poleFreeAnalyticError factorTwoIntrinsicP4CorrelationDifference| <
      (3 / 100000 : ℝ) := by
  have herr := abs_poleFreeAnalyticError_le
    factorTwoIntrinsicP4CorrelationDifference
      continuous_factorTwoIntrinsicP4CorrelationDifference
  have hL1 := integral_abs_factorTwoIntrinsicP4CorrelationDifference_lt
  nlinarith

private def factorTwoIntrinsicP4P6Sum : ℝ :=
  poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
    poleFreeCoeff6 yoshidaEndpointA * (32 / 99 + 32 / 315)

private def factorTwoIntrinsicP4P6Difference : ℝ :=
  -poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
    poleFreeCoeff6 yoshidaEndpointA * (32 / 315 - 32 / 99)

private theorem factorTwoIntrinsicP4P6Sum_bounds :
    0 ≤ factorTwoIntrinsicP4P6Sum ∧
      factorTwoIntrinsicP4P6Sum < (3 / 1000000 : ℝ) := by
  rcases poleFree_coefficient_bounds with
    ⟨_h0l, _h0u, _h2l, _h2u, h4l, h4u, h6l, h6u⟩
  unfold factorTwoIntrinsicP4P6Sum
  constructor <;> norm_num at h4l h4u h6l h6u ⊢ <;> nlinarith

private theorem factorTwoIntrinsicP4P6Difference_bounds :
    (-3 / 1000000 : ℝ) < factorTwoIntrinsicP4P6Difference ∧
      factorTwoIntrinsicP4P6Difference ≤ 0 := by
  rcases poleFree_coefficient_bounds with
    ⟨_h0l, _h0u, _h2l, _h2u, h4l, h4u, h6l, h6u⟩
  unfold factorTwoIntrinsicP4P6Difference
  constructor <;> norm_num at h4l h4u h6l h6u ⊢ <;> nlinarith

/-- Exact strong-coordinate decomposition: clean potential, degree-six
smooth term, one analytic error, both pole atoms, and the retained prime. -/
theorem factorTwoIntrinsicP4PlusCrossSum_structural_eq :
    factorTwoIntrinsicP4PlusCrossSum =
      (yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 +
        yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4) +
      poleFreeAnalyticError factorTwoIntrinsicP4CorrelationSum +
      factorTwoIntrinsicP4P6Sum + 72 - 104 * Real.log 2 -
      (Real.log 3 / Real.sqrt 3) * factorTwoIntrinsicP4CorrelationSum
        (factorTwoPrimeShift / yoshidaEndpointA) := by
  have herr :
      poleFreeAnalyticError factorTwoIntrinsicP4Correlation04 +
          poleFreeAnalyticError factorTwoIntrinsicP4Correlation24 =
        poleFreeAnalyticError factorTwoIntrinsicP4CorrelationSum := by
    simpa only [factorTwoIntrinsicP4CorrelationSum] using
      poleFreeAnalyticError_add factorTwoIntrinsicP4Correlation04
        factorTwoIntrinsicP4Correlation24
        continuous_factorTwoIntrinsicP4Correlation04
        continuous_factorTwoIntrinsicP4Correlation24
  rcases factorTwoIntrinsicP4_perturbation_structural_eq with
    ⟨h04, h24, _h44⟩
  unfold factorTwoIntrinsicP4PlusCrossSum
    factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
  rw [h04, h24]
  unfold factorTwoIntrinsicP4PerturbationBase04
    factorTwoIntrinsicP4PerturbationBase24 factorTwoIntrinsicP4P6Sum
    factorTwoIntrinsicP4CorrelationSum
  unfold factorTwoIntrinsicP4CorrelationSum at herr
  linear_combination herr

/-- Exact endpoint-vanishing weak-coordinate decomposition. -/
theorem factorTwoIntrinsicP4PlusCrossDifference_structural_eq :
    factorTwoIntrinsicP4PlusCrossDifference =
      (yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 -
        yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4) +
      poleFreeAnalyticError factorTwoIntrinsicP4CorrelationDifference +
      factorTwoIntrinsicP4P6Difference - (158 / 3 : ℝ) +
      76 * Real.log 2 -
      (Real.log 3 / Real.sqrt 3) *
        factorTwoIntrinsicP4CorrelationDifference
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  have herr :
      poleFreeAnalyticError factorTwoIntrinsicP4Correlation24 -
          poleFreeAnalyticError factorTwoIntrinsicP4Correlation04 =
        poleFreeAnalyticError factorTwoIntrinsicP4CorrelationDifference := by
    simpa only [factorTwoIntrinsicP4CorrelationDifference] using
      poleFreeAnalyticError_sub factorTwoIntrinsicP4Correlation24
        factorTwoIntrinsicP4Correlation04
        continuous_factorTwoIntrinsicP4Correlation24
        continuous_factorTwoIntrinsicP4Correlation04
  rcases factorTwoIntrinsicP4_perturbation_structural_eq with
    ⟨h04, h24, _h44⟩
  unfold factorTwoIntrinsicP4PlusCrossDifference
    factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
  rw [h04, h24]
  unfold factorTwoIntrinsicP4PerturbationBase04
    factorTwoIntrinsicP4PerturbationBase24
    factorTwoIntrinsicP4P6Difference
    factorTwoIntrinsicP4CorrelationDifference
  unfold factorTwoIntrinsicP4CorrelationDifference at herr
  linear_combination herr

/-- Structural rational box for the complete strong cross coordinate. -/
theorem factorTwoIntrinsicP4PlusCrossSum_bounds :
    0 < factorTwoIntrinsicP4PlusCrossSum ∧
      factorTwoIntrinsicP4PlusCrossSum < (193 / 1000 : ℝ) := by
  let clean : ℝ :=
    yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 +
      yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4
  let err : ℝ := poleFreeAnalyticError factorTwoIntrinsicP4CorrelationSum
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  let P : ℝ := -factorTwoIntrinsicP4CorrelationSum
    (factorTwoPrimeShift / yoshidaEndpointA)
  have heq := factorTwoIntrinsicP4PlusCrossSum_structural_eq
  have hclean :=
    factorTwoIntrinsicP4CleanCross_sum_sub_seventeen_seventieths_abs_lt
  have herr := abs_poleFreeAnalyticError_p4Sum_lt
  have hp6 := factorTwoIntrinsicP4P6Sum_bounds
  have hlog := strict_log_two_fine_bounds
  have hbeta := log_three_div_sqrt_three_kernel_bounds
  have hcorr := factorTwoIntrinsicP4PrimeCorrelation_sum_difference_bounds
  have hP : (29333 / 500000 : ℝ) < P ∧
      P < (29337 / 500000 : ℝ) := by
    dsimp only [P]
    constructor <;> linarith [hcorr.1, hcorr.2.1]
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    positivity
  have hP0 : 0 < P :=
    (by norm_num : (0 : ℝ) < 29333 / 500000).trans hP.1
  have hprimeLower :
      (63427 / 100000 : ℝ) * (29333 / 500000 : ℝ) < beta * P := by
    calc
      (63427 / 100000 : ℝ) * (29333 / 500000 : ℝ) <
          beta * (29333 / 500000 : ℝ) :=
        mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
      _ < beta * P := mul_lt_mul_of_pos_left hP.1 hbeta0
  have hprimeUpper : beta * P <
      (6343 / 10000 : ℝ) * (29337 / 500000 : ℝ) := by
    calc
      beta * P < (6343 / 10000 : ℝ) * P :=
        mul_lt_mul_of_pos_right hbeta.2 hP0
      _ < (6343 / 10000 : ℝ) * (29337 / 500000 : ℝ) :=
        mul_lt_mul_of_pos_left hP.2 (by norm_num)
  rw [abs_lt] at hclean herr
  dsimp only [clean, err, beta, P] at heq hprimeLower hprimeUpper ⊢
  constructor <;> nlinarith

/-- Structural rational box for the endpoint-vanishing weak coordinate. -/
theorem factorTwoIntrinsicP4PlusCrossDifference_bounds :
    0 < factorTwoIntrinsicP4PlusCrossDifference ∧
      factorTwoIntrinsicP4PlusCrossDifference < (39 / 2000 : ℝ) := by
  let clean : ℝ :=
    yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 -
      yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4
  let err : ℝ :=
    poleFreeAnalyticError factorTwoIntrinsicP4CorrelationDifference
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  let Q : ℝ := factorTwoIntrinsicP4CorrelationDifference
    (factorTwoPrimeShift / yoshidaEndpointA)
  have heq := factorTwoIntrinsicP4PlusCrossDifference_structural_eq
  have hclean :=
    factorTwoIntrinsicP4CleanCross_difference_sub_three_seventieths_abs_lt
  have herr := abs_poleFreeAnalyticError_p4Difference_lt
  have hp6 := factorTwoIntrinsicP4P6Difference_bounds
  have hlog := strict_log_two_fine_bounds
  have hbeta := log_three_div_sqrt_three_kernel_bounds
  have hcorr := factorTwoIntrinsicP4PrimeCorrelation_sum_difference_bounds
  have hQ : (56755 / 1000000 : ℝ) < Q ∧
      Q < (56757 / 1000000 : ℝ) := by
    dsimp only [Q]
    exact hcorr.2.2
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    positivity
  have hQ0 : 0 < Q :=
    (by norm_num : (0 : ℝ) < 56755 / 1000000).trans hQ.1
  have hprimeLower :
      (63427 / 100000 : ℝ) * (56755 / 1000000 : ℝ) < beta * Q := by
    calc
      (63427 / 100000 : ℝ) * (56755 / 1000000 : ℝ) <
          beta * (56755 / 1000000 : ℝ) :=
        mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
      _ < beta * Q := mul_lt_mul_of_pos_left hQ.1 hbeta0
  have hprimeUpper : beta * Q <
      (6343 / 10000 : ℝ) * (56757 / 1000000 : ℝ) := by
    calc
      beta * Q < (6343 / 10000 : ℝ) * Q :=
        mul_lt_mul_of_pos_right hbeta.2 hQ0
      _ < (6343 / 10000 : ℝ) * (56757 / 1000000 : ℝ) :=
        mul_lt_mul_of_pos_left hQ.2 (by norm_num)
  rw [abs_lt] at hclean herr
  dsimp only [clean, err, beta, Q] at heq hprimeLower hprimeUpper ⊢
  constructor <;> nlinarith

/-- The two structural coordinate boxes fit inside the UltraSharp adjugate
budget with a strict rational margin. -/
theorem factorTwoIntrinsicP4PlusUltraAdjugate_le_nine_twentieths :
    factorTwoIntrinsicP4PlusUltraAdjugate ≤
      (9 / 20 : ℝ) *
        (evenPositiveEndpointUltraSharp00 *
            evenPositiveEndpointUltraSharp22 -
          evenPositiveEndpointUltraSharp02 ^ 2) *
        factorTwoIntrinsicP4WeightedMass := by
  let S : ℝ := factorTwoIntrinsicP4PlusCrossSum
  let D : ℝ := factorTwoIntrinsicP4PlusCrossDifference
  have hS := factorTwoIntrinsicP4PlusCrossSum_bounds
  have hD := factorTwoIntrinsicP4PlusCrossDifference_bounds
  have hSsq : S ^ 2 < (193 / 1000 : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ hS.2 hS.1.le (by norm_num)
  have hDsq : D ^ 2 < (39 / 2000 : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ hD.2 hD.1.le (by norm_num)
  have hSD : S * D < (193 / 1000 : ℝ) * (39 / 2000 : ℝ) := by
    calc
      S * D < (193 / 1000 : ℝ) * D :=
        mul_lt_mul_of_pos_right hS.2 hD.1
      _ < (193 / 1000 : ℝ) * (39 / 2000 : ℝ) :=
        mul_lt_mul_of_pos_left hD.2 (by norm_num)
  have hT : (260 / 567 - 7 / 45 : ℝ) <
      factorTwoIntrinsicP4WeightedMass := by
    rw [factorTwoIntrinsicP4WeightedMass_eq]
    nlinarith [strict_log_two_bounds.2]
  rw [factorTwoIntrinsicP4PlusUltraAdjugate_eq_sum_difference,
    evenPositiveEndpointUltraSharp_det_eq]
  dsimp only [S, D] at hSsq hDsq hSD ⊢
  nlinarith

/-- Unconditional structural positivity of the positive-endpoint intrinsic
`P0/P2/P4` Schur leading coefficient. -/
theorem factorTwoIntrinsicSixP4SchurLeading_plus_pos :
    0 < factorTwoIntrinsicSixP4SchurLeading 1 := by
  exact factorTwoIntrinsicSixP4SchurLeading_plus_pos_of_aligned_bounds
    factorTwoIntrinsicP4PlusUltraAdjugate_le_nine_twentieths
    factorTwoIntrinsicP4PlusWeightedReserve


end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
