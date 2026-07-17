import ArithmeticHodge.Analysis.YoshidaEndpointOddLowGramExpansion
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLowSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticPoleWeightedCauchyStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticSquareClosureStructural

noncomputable section

open UnitIntervalLogEnergyAffine
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointTriangleFoldLipschitz
open YoshidaEndpointSingularCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddStructuralPerturbation
open YoshidaFactorTwoPhaseProfileStaticPoleWeightedCauchyStructural
open YoshidaFactorTwoPhaseProfileStaticPoleSquareStructural
open YoshidaFactorTwoPhaseProfileStaticSplit
open YoshidaFactorTwoPhaseProfileStaticSquareAssemblyStructural
open YoshidaRegularKernelSchur

/-!
# Static-square closure of the whole phase disk

The exact profile-static assembly leaves one sharp obligation for each of the
two Hadamard signs: the retained half of the logarithmically weighted pole
square must dominate the signed smooth remainder, uniformly under independent
even and odd rescaling.  This module proves that those two structural reserve
inequalities imply the complete same-seed phase inequality on the closed
disk.  It then proves, on an exact endpoint-zero cubic, that both reserve
hypotheses fail: the fatal step is discarding the positive-distance/raw
energy before controlling the signed remainder.  Thus the identities isolate
both the sufficient closure and the precise structural obstruction to it.
-/

/-- The exact scale-uniform reserve left by one profile-static square. -/
def FactorTwoProfileStaticSquareReserveNonnegative
    (e o : ℝ → ℝ) (sigma : ℝ) : Prop :=
  ∀ r s : ℝ,
    0 ≤ (1 / 2 : ℝ) *
          factorTwoProfileStaticPoleWeightedEnergy (r • e) (s • o) sigma +
        factorTwoProfileStaticSignedRemainder (r • e) (s • o) sigma

/-- Exact accounting for the proposed pole-only reserve.  It is the complete
static branch after *all* positive-distance/raw energy has been discarded.
This identity is useful both for applying the reserve and for detecting when
that discard is too strong. -/
theorem staticSquareReserveValue_eq_branch_sub_raw
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (hlocale : LocallyLipschitzOn (Icc (-1) 1) e)
    (hlocalo : LocallyLipschitzOn (Icc (-1) 1) o)
    (sigma : ℝ) (hsigma : sigma ^ 2 = 1) :
    (1 / 2 : ℝ) * factorTwoProfileStaticPoleWeightedEnergy e o sigma +
        factorTwoProfileStaticSignedRemainder e o sigma =
      factorTwoProfileStaticBranchForm e o sigma -
        centeredRawLogEnergy e / 4 - centeredRawLogEnergy o / 4 := by
  have heEnergy :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      e hlocale
  have hoEnergy :=
    intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
      o hlocalo
  have hpole :=
    intervalIntegrable_factorTwoProfileStaticPoleSquareNumerator_div
      e o he ho sigma hsigma
  have heRaw :=
    half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
      e hlocale
  have hoRaw :=
    half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
      o hlocalo
  have hbranch :=
    factorTwoProfileStaticBranchForm_eq_singularSquare_add_signedRemainder
      e o he ho hlocale hlocalo sigma
  have hsplit :
      (∫ r : ℝ in 0..2,
          factorTwoProfileStaticSingularSquareNumerator e o sigma r / r) =
        (∫ r : ℝ in 0..2, centeredPositiveDistanceEnergy e r / r) +
          (∫ r : ℝ in 0..2, centeredPositiveDistanceEnergy o r / r) +
          ∫ r : ℝ in 0..2,
            factorTwoProfileStaticPoleSquareNumerator e o sigma r / r := by
    rw [show (fun r : ℝ ↦
        factorTwoProfileStaticSingularSquareNumerator e o sigma r / r) =
      fun r ↦ centeredPositiveDistanceEnergy e r / r +
        centeredPositiveDistanceEnergy o r / r +
        factorTwoProfileStaticPoleSquareNumerator e o sigma r / r by
      funext r
      unfold factorTwoProfileStaticSingularSquareNumerator
      rw [factorTwoProfileStaticPoleDefectNumerator_eq_square
        e o sigma hsigma r]
      ring,
      intervalIntegral.integral_add (heEnergy.add hoEnergy) hpole,
      intervalIntegral.integral_add heEnergy hoEnergy]
  rw [hbranch, hsplit]
  unfold factorTwoProfileStaticPoleWeightedEnergy
  rw [← heRaw, ← hoRaw]
  ring

/-! ## Structural obstruction to discarding the raw energy -/

/-- The endpoint-zero odd cubic `x * (1 - x^2)`, expressed in the existing
`P₁/P₃` basis so that its raw and endpoint phase energies are exact. -/
def staticSquareOddCubic : ℝ → ℝ :=
  factorTwoOddStructuralLowProfile (2 / 5) (-2 / 5)

private theorem staticSquareOddCubic_continuous :
    Continuous staticSquareOddCubic := by
  exact continuous_factorTwoOddStructuralLowProfile (2 / 5) (-2 / 5)

private theorem staticSquareOddCubic_locallyLipschitzOn :
    LocallyLipschitzOn (Icc (-1) 1) staticSquareOddCubic := by
  have hdiff : ContDiffOn ℝ 1 staticSquareOddCubic (Icc (-1) 1) := by
    unfold staticSquareOddCubic factorTwoOddStructuralLowProfile
      centeredP1 centeredP3
    fun_prop
  exact hdiff.locallyLipschitzOn (convex_Icc (-1) 1)

/-- Exact raw logarithmic energy of the endpoint-zero cubic. -/
theorem centeredRawLogEnergy_staticSquareOddCubic :
    centeredRawLogEnergy staticSquareOddCubic = (16 / 21 : ℝ) := by
  unfold staticSquareOddCubic
  rw [centeredRawLogEnergy_factorTwoOddStructuralLowProfile]
  norm_num

private theorem factorTwoEndpointPhaseDiagonal_oddStructuralLow
    (a c d : ℝ) :
    factorTwoEndpointPhaseDiagonal
        (factorTwoOddStructuralLowProfile c d) a =
      factorTwoIntrinsicOddPhaseQuadratic a c d := by
  unfold factorTwoEndpointPhaseDiagonal factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33
  rw [yoshidaEndpointOddLowGram_quadratic,
    factorTwoCenteredSymmetricPerturbation_oddStructuralLow]
  ring

/-- The positive symmetric endpoint energy of the cubic is already much
smaller than one quarter of its raw logarithmic energy. -/
theorem staticSquareOddCubic_phaseDiagonal_plus_lt :
    factorTwoEndpointPhaseDiagonal staticSquareOddCubic 1 <
      (37 / 6250 : ℝ) := by
  rw [show staticSquareOddCubic =
      factorTwoOddStructuralLowProfile (2 / 5) (-2 / 5) by rfl,
    factorTwoEndpointPhaseDiagonal_oddStructuralLow]
  unfold factorTwoIntrinsicOddPhaseQuadratic
  rcases factorTwoIntrinsicOddPhaseLow_plus_entry_bounds with
    ⟨_h11Lower, h11Upper, h13Lower, _h13Upper,
      _h33Lower, h33Upper⟩
  norm_num at h11Upper h13Lower h33Upper ⊢
  nlinarith

/-- The negative symmetric endpoint energy of the same cubic is likewise
smaller than one quarter of its raw logarithmic energy. -/
theorem staticSquareOddCubic_phaseDiagonal_minus_lt :
    factorTwoEndpointPhaseDiagonal staticSquareOddCubic (-1) <
      (4 / 125 : ℝ) := by
  rw [show staticSquareOddCubic =
      factorTwoOddStructuralLowProfile (2 / 5) (-2 / 5) by rfl,
    factorTwoEndpointPhaseDiagonal_oddStructuralLow]
  unfold factorTwoIntrinsicOddPhaseQuadratic
  rcases factorTwoIntrinsicOddPhaseLow_minus_entry_bounds with
    ⟨_h11Lower, h11Upper, h13Lower, _h13Upper,
      _h33Lower, h33Upper⟩
  norm_num at h11Upper h13Lower h33Upper ⊢
  nlinarith

private theorem factorTwoProfileStaticBranchForm_zero_left
    (o : ℝ → ℝ) (sigma : ℝ) :
    factorTwoProfileStaticBranchForm 0 o sigma =
      factorTwoEndpointPhaseDiagonal o (-sigma) := by
  have hcleanZero :
      yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
    unfold yoshidaEndpointOddCleanQuadratic centeredRawLogEnergy
      yoshidaEndpointRegularQuadratic yoshidaEndpointHyperbolicQuadratic
    simp
  unfold factorTwoProfileStaticBranchForm factorTwoEndpointPhaseDiagonal
  simp [hcleanZero, factorTwoCenteredSymmetricPerturbation,
    factorTwoCenteredAlternatingCoupling]

private theorem centeredRawLogEnergy_zero :
    centeredRawLogEnergy (0 : ℝ → ℝ) = 0 := by
  simp [centeredRawLogEnergy]

/-- The pole-only square reserve fails for the positive static sign, already
on one smooth endpoint-zero odd cubic. -/
theorem not_staticSquareReserveNonnegative_plus :
    ¬ FactorTwoProfileStaticSquareReserveNonnegative
      0 staticSquareOddCubic 1 := by
  intro hreserve
  have hnonneg := hreserve 0 1
  simp only [zero_smul, one_smul] at hnonneg
  have hvalue := staticSquareReserveValue_eq_branch_sub_raw
    0 staticSquareOddCubic continuous_zero staticSquareOddCubic_continuous
    (by simpa using
      (LocallyLipschitz.const (0 : ℝ)).locallyLipschitzOn)
    staticSquareOddCubic_locallyLipschitzOn 1 (by norm_num)
  rw [hvalue, factorTwoProfileStaticBranchForm_zero_left,
    centeredRawLogEnergy_zero,
    centeredRawLogEnergy_staticSquareOddCubic] at hnonneg
  have hphase := staticSquareOddCubic_phaseDiagonal_minus_lt
  norm_num at hnonneg
  nlinarith

/-- The same pole-only square reserve also fails for the negative static
sign.  Therefore a viable square proof must retain positive-distance/raw
energy rather than spending it before the signed remainder is controlled. -/
theorem not_staticSquareReserveNonnegative_minus :
    ¬ FactorTwoProfileStaticSquareReserveNonnegative
      0 staticSquareOddCubic (-1) := by
  intro hreserve
  have hnonneg := hreserve 0 1
  simp only [zero_smul, one_smul] at hnonneg
  have hvalue := staticSquareReserveValue_eq_branch_sub_raw
    0 staticSquareOddCubic continuous_zero staticSquareOddCubic_continuous
    (by simpa using
      (LocallyLipschitz.const (0 : ℝ)).locallyLipschitzOn)
    staticSquareOddCubic_locallyLipschitzOn (-1) (by norm_num)
  rw [hvalue, factorTwoProfileStaticBranchForm_zero_left,
    centeredRawLogEnergy_zero,
    centeredRawLogEnergy_staticSquareOddCubic] at hnonneg
  have hphase := staticSquareOddCubic_phaseDiagonal_plus_lt
  norm_num at hnonneg
  nlinarith

private theorem factorTwoEndpointPhaseDiagonal_smul
    (w : ℝ → ℝ) (c a : ℝ) :
    factorTwoEndpointPhaseDiagonal (c • w) a =
      c ^ 2 * factorTwoEndpointPhaseDiagonal w a := by
  have hclean : yoshidaEndpointOddCleanQuadratic (c • w) =
      c ^ 2 * yoshidaEndpointOddCleanQuadratic w := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      yoshidaEndpointOddCleanQuadratic_const_mul w c
  unfold factorTwoEndpointPhaseDiagonal
  rw [hclean, factorTwoCenteredSymmetricPerturbation_smul]
  ring_nf

private theorem factorTwoProfileStaticBranchForm_smul_smul
    (e o : ℝ → ℝ) (r s sigma : ℝ) :
    factorTwoProfileStaticBranchForm (r • e) (s • o) sigma =
      r ^ 2 * factorTwoEndpointPhaseDiagonal e sigma +
        s ^ 2 * factorTwoEndpointPhaseDiagonal o (-sigma) +
        r * s * factorTwoCenteredAlternatingCoupling e o := by
  unfold factorTwoProfileStaticBranchForm
  rw [factorTwoEndpointPhaseDiagonal_smul,
    factorTwoEndpointPhaseDiagonal_smul,
    factorTwoCenteredAlternatingCoupling_smul_left,
    factorTwoCenteredAlternatingCoupling_smul_right]
  ring_nf

private theorem locallyLipschitzOn_smul
    (f : ℝ → ℝ) (hf : LocallyLipschitzOn (Icc (-1) 1) f) (c : ℝ) :
    LocallyLipschitzOn (Icc (-1) 1) (c • f) := by
  rw [locallyLipschitzOn_iff_restrict]
  have hscale : LocallyLipschitz (c • · : ℝ → ℝ) :=
    (lipschitzWith_smul c).locallyLipschitz
  have hcomp := hscale.comp hf.restrict
  simpa only [Function.comp_apply, Set.restrict_apply, Pi.smul_apply,
    smul_eq_mul] using hcomp

/-- One scale-uniform static-square reserve makes the corresponding static
branch nonnegative under every independent even/odd rescaling. -/
theorem factorTwoProfileStaticBranchForm_nonneg_of_squareReserve
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (hlocale : LocallyLipschitzOn (Icc (-1) 1) e)
    (hlocalo : LocallyLipschitzOn (Icc (-1) 1) o)
    (sigma : ℝ) (hsigma : sigma ^ 2 = 1)
    (hreserve : FactorTwoProfileStaticSquareReserveNonnegative e o sigma)
    (r s : ℝ) :
    0 ≤ factorTwoProfileStaticBranchForm (r • e) (s • o) sigma := by
  have hlower := half_integral_staticPoleSquare_add_signedRemainder_le_staticBranch
    (r • e) (s • o) (he.const_smul r) (ho.const_smul s)
    (locallyLipschitzOn_smul e hlocale r)
    (locallyLipschitzOn_smul o hlocalo s) sigma hsigma
  change (1 / 2 : ℝ) *
        factorTwoProfileStaticPoleWeightedEnergy (r • e) (s • o) sigma +
      factorTwoProfileStaticSignedRemainder (r • e) (s • o) sigma ≤
    factorTwoProfileStaticBranchForm (r • e) (s • o) sigma at hlower
  exact (hreserve r s).trans hlower

/-- The two exact static-square reserve inequalities close the complete
same-seed factor-two phase inequality for every point of the closed disk. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_staticSquareReserves
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (hlocale : LocallyLipschitzOn (Icc (-1) 1) e)
    (hlocalo : LocallyLipschitzOn (Icc (-1) 1) o)
    (hPlus : FactorTwoProfileStaticSquareReserveNonnegative e o 1)
    (hMinus : FactorTwoProfileStaticSquareReserveNonnegative e o (-1))
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  apply factorTwoEndpointChannelPhase_nonneg_of_profile_static_splits
    e o a b hab
  · intro r s
    have hbranch := factorTwoProfileStaticBranchForm_nonneg_of_squareReserve
      e o he ho hlocale hlocalo 1 (by norm_num) hPlus r s
    rw [factorTwoProfileStaticBranchForm_smul_smul] at hbranch
    simpa only [neg_one_mul] using hbranch
  · intro r s
    have hbranch := factorTwoProfileStaticBranchForm_nonneg_of_squareReserve
      e o he ho hlocale hlocalo (-1) (by norm_num) hMinus r s
    rw [factorTwoProfileStaticBranchForm_smul_smul] at hbranch
    norm_num at hbranch ⊢
    exact hbranch

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticSquareClosureStructural
