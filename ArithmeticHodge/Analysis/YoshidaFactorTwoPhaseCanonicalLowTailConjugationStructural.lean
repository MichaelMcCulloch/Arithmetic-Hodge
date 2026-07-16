import ArithmeticHodge.Analysis.YoshidaEvenCorrectionReality
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnStructural
import ArithmeticHodge.Analysis.YoshidaOddCompletionConjugationStructural

set_option autoImplicit false

open Complex Real
open scoped ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailConjugationStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaEndpointScaledCorrelation
open YoshidaEvenCorrectionReality
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseCanonicalTailDiagonalStructural
open YoshidaFactorTwoPhaseEndpointTailMixedCauchyStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseTailRealImagStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaOddCompletionConjugationStructural
open YoshidaOddHomogeneousCoercivity
open YoshidaWeightedTailBounds

/-!
# Conjugation symmetry of the algebraic canonical phase tail

The canonical complex tail is the `L²` product of the actual even and odd
critical-form spaces.  Pairing their pointwise conjugations gives an
involutive conjugate-linear isometry.  Its real tail profiles are fixed and
its imaginary tail profiles change sign, so the complete real phase form is
invariant under simultaneous conjugation.
-/

private theorem star_I_eq_neg_I : star (Complex.I : ℂ) = -Complex.I :=
  Complex.conj_I

/-- Componentwise pointwise conjugation on the algebraic canonical phase
tail. -/
def canonicalPhaseTailCoreConj
    (x : CanonicalPhaseTailCore) : CanonicalPhaseTailCore :=
  WithLp.toLp 2 (formSpaceConj x.fst, oddFormSpaceConj x.snd)

@[simp] theorem canonicalPhaseTailCoreConj_fst
    (x : CanonicalPhaseTailCore) :
    (canonicalPhaseTailCoreConj x).fst = formSpaceConj x.fst :=
  rfl

@[simp] theorem canonicalPhaseTailCoreConj_snd
    (x : CanonicalPhaseTailCore) :
    (canonicalPhaseTailCoreConj x).snd = oddFormSpaceConj x.snd :=
  rfl

@[simp] theorem canonicalPhaseTailCoreConj_fst_toV
    (x : CanonicalPhaseTailCore) :
    (canonicalPhaseTailCoreConj x).fst.toV = evenTailConj x.fst.toV :=
  rfl

@[simp] theorem canonicalPhaseTailCoreConj_snd_toV
    (x : CanonicalPhaseTailCore) :
    (canonicalPhaseTailCoreConj x).snd.toV = oddTailConj x.snd.toV :=
  rfl

@[simp] theorem canonicalPhaseTailCoreConj_zero :
    canonicalPhaseTailCoreConj (0 : CanonicalPhaseTailCore) = 0 := by
  apply WithLp.ofLp_injective 2
  ext <;> simp [canonicalPhaseTailCoreConj]

@[simp] theorem canonicalPhaseTailCoreConj_add
    (x y : CanonicalPhaseTailCore) :
    canonicalPhaseTailCoreConj (x + y) =
      canonicalPhaseTailCoreConj x + canonicalPhaseTailCoreConj y := by
  apply WithLp.ofLp_injective 2
  ext <;> simp [canonicalPhaseTailCoreConj]

@[simp] theorem canonicalPhaseTailCoreConj_smul
    (c : ℂ) (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailCoreConj (c • x) =
      star c • canonicalPhaseTailCoreConj x := by
  apply WithLp.ofLp_injective 2
  ext <;> simp [canonicalPhaseTailCoreConj]

@[simp] theorem canonicalPhaseTailCoreConj_involutive
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailCoreConj (canonicalPhaseTailCoreConj x) = x := by
  apply WithLp.ofLp_injective 2
  ext <;> simp [canonicalPhaseTailCoreConj]

@[simp] theorem norm_canonicalPhaseTailCoreConj
    (x : CanonicalPhaseTailCore) :
    ‖canonicalPhaseTailCoreConj x‖ = ‖x‖ := by
  rw [WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
  simp [canonicalPhaseTailCoreConj]

/-- Conjugation anticommutes with the canonical quarter turn. -/
@[simp] theorem canonicalPhaseTailCoreConj_I_smul
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailCoreConj (Complex.I • x) =
      (-Complex.I) • canonicalPhaseTailCoreConj x := by
  calc
    canonicalPhaseTailCoreConj (Complex.I • x) =
        star Complex.I • canonicalPhaseTailCoreConj x :=
      canonicalPhaseTailCoreConj_smul Complex.I x
    _ = (-Complex.I) • canonicalPhaseTailCoreConj x := by
      rw [star_I_eq_neg_I]

@[simp] private theorem evenTailRealPart_conj
    (f : YoshidaEvenOneNinetyNineTail) :
    evenTailRealPart (evenTailConj f) = evenTailRealPart f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change (((((star (evenOneNinetyNineTailToClippedSmooth f t)).re :
      ℝ) : ℂ))) =
    ((((evenOneNinetyNineTailToClippedSmooth f t).re : ℝ) : ℂ))
  apply Complex.ext <;> simp

@[simp] private theorem evenTailImagPart_conj
    (f : YoshidaEvenOneNinetyNineTail) :
    evenTailImagPart (evenTailConj f) = -evenTailImagPart f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change (((((star (evenOneNinetyNineTailToClippedSmooth f t)).im :
      ℝ) : ℂ))) =
    -((((evenOneNinetyNineTailToClippedSmooth f t).im : ℝ) : ℂ))
  apply Complex.ext <;> simp

@[simp] private theorem oddTailRealPart_conj
    (f : YoshidaOddTenTail) :
    oddTailRealPart (oddTailConj f) = oddTailRealPart f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change (((((star (oddTenTailToClippedSmooth f t)).re : ℝ) : ℂ))) =
    ((((oddTenTailToClippedSmooth f t).re : ℝ) : ℂ))
  apply Complex.ext <;> simp

@[simp] private theorem oddTailImagPart_conj
    (f : YoshidaOddTenTail) :
    oddTailImagPart (oddTailConj f) = -oddTailImagPart f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change (((((star (oddTenTailToClippedSmooth f t)).im : ℝ) : ℂ))) =
    -((((oddTenTailToClippedSmooth f t).im : ℝ) : ℂ))
  apply Complex.ext <;> simp

private theorem canonicalEvenTailPointwise_neg
    (f : YoshidaEvenOneNinetyNineTail) :
    canonicalEvenTailPointwise (-f) =
      (((-1 : ℝ) : ℂ) • canonicalEvenTailPointwise f) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change -evenOneNinetyNineTailToClippedSmooth f t =
    (((-1 : ℝ) : ℂ) * evenOneNinetyNineTailToClippedSmooth f t)
  simp

/-- Pointwise conjugation fixes the even real tail profile. -/
@[simp] theorem canonicalPhaseTailEvenRealProfile_conj
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenRealProfile (canonicalPhaseTailCoreConj x) =
      canonicalPhaseTailEvenRealProfile x := by
  unfold canonicalPhaseTailEvenRealProfile
  rw [canonicalPhaseTailCoreConj_fst_toV, evenTailRealPart_conj]

/-- Pointwise conjugation negates the even imaginary tail profile. -/
@[simp] theorem canonicalPhaseTailEvenImagProfile_conj
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenImagProfile (canonicalPhaseTailCoreConj x) =
      -canonicalPhaseTailEvenImagProfile x := by
  unfold canonicalPhaseTailEvenImagProfile boundaryCanonicalEvenTailProfile
  rw [canonicalPhaseTailCoreConj_fst_toV, evenTailImagPart_conj,
    canonicalEvenTailPointwise_neg]
  simpa only [neg_one_smul] using
    boundaryContinuousEvenProfile_smul_real (-1)
      (canonicalEvenTailPointwise (evenTailImagPart x.fst.toV))

/-- Pointwise conjugation fixes the odd real tail profile. -/
@[simp] theorem canonicalPhaseTailOddRealProfile_conj
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailOddRealProfile (canonicalPhaseTailCoreConj x) =
      canonicalPhaseTailOddRealProfile x := by
  unfold canonicalPhaseTailOddRealProfile
  rw [canonicalPhaseTailCoreConj_snd_toV, oddTailRealPart_conj]

/-- Pointwise conjugation negates the odd imaginary tail profile. -/
@[simp] theorem canonicalPhaseTailOddImagProfile_conj
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailOddImagProfile (canonicalPhaseTailCoreConj x) =
      -canonicalPhaseTailOddImagProfile x := by
  funext t
  unfold canonicalPhaseTailOddImagProfile canonicalOddTailProfile
    centeredRescale
  rw [canonicalPhaseTailCoreConj_snd_toV, oddTailImagPart_conj]
  change (-oddTenTailToClippedSmooth (oddTailImagPart x.snd.toV)
      (yoshidaA * t)).re =
    -(oddTenTailToClippedSmooth (oddTailImagPart x.snd.toV)
      (yoshidaA * t)).re
  simp

/-- The algebraic canonical tail diagonal is invariant under pointwise
conjugation. -/
theorem canonicalPhaseTailCoreDiagonal_conj
    (x : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseTailCoreDiagonal (canonicalPhaseTailCoreConj x) a b =
      canonicalPhaseTailCoreDiagonal x a b := by
  rw [canonicalPhaseTailCoreDiagonal,
    canonicalPhaseTailEvenRealProfile_conj,
    canonicalPhaseTailOddRealProfile_conj,
    canonicalPhaseTailEvenImagProfile_conj,
    canonicalPhaseTailOddImagProfile_conj,
    canonicalPhaseTailCoreDiagonal]
  have hneg := factorTwoEndpointChannelPhase_smul
    (canonicalPhaseTailEvenImagProfile x)
    (canonicalPhaseTailOddImagProfile x) (-1) a b
  have hneg' : factorTwoEndpointChannelPhase
      (-canonicalPhaseTailEvenImagProfile x)
      (-canonicalPhaseTailOddImagProfile x) a b =
      factorTwoEndpointChannelPhase
        (canonicalPhaseTailEvenImagProfile x)
        (canonicalPhaseTailOddImagProfile x) a b := by
    norm_num at hneg ⊢
    exact hneg
  rw [hneg']

/-- The algebraic canonical tail bilinear form is invariant under
simultaneous pointwise conjugation. -/
theorem canonicalPhaseTailCoreBilinearValue_conj_conj
    (x y : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseTailCoreBilinearValue
        (canonicalPhaseTailCoreConj x)
        (canonicalPhaseTailCoreConj y) a b =
      canonicalPhaseTailCoreBilinearValue x y a b := by
  rw [canonicalPhaseTailCoreBilinearValue_eq_polarization,
    ← canonicalPhaseTailCoreConj_add,
    canonicalPhaseTailCoreDiagonal_conj,
    canonicalPhaseTailCoreDiagonal_conj,
    canonicalPhaseTailCoreDiagonal_conj,
    ← canonicalPhaseTailCoreBilinearValue_eq_polarization]

/-- The algebraic real-coordinate low--tail functional is fixed by tail
conjugation. -/
theorem canonicalPhaseLowBasisTailRealMixedValue_conj
    (k : FactorTwoPhaseLowIndex) (x : CanonicalPhaseTailCore)
    (a b : ℝ) :
    canonicalPhaseLowBasisTailRealMixedValue k
        (canonicalPhaseTailCoreConj x) a b =
      canonicalPhaseLowBasisTailRealMixedValue k x a b := by
  unfold canonicalPhaseLowBasisTailRealMixedValue
  rw [canonicalPhaseTailEvenRealProfile_conj,
    canonicalPhaseTailOddRealProfile_conj]

/-- The algebraic imaginary-coordinate low--tail functional changes sign
under tail conjugation. -/
theorem canonicalPhaseLowBasisTailImagMixedValue_conj
    (k : FactorTwoPhaseLowIndex) (x : CanonicalPhaseTailCore)
    (a b : ℝ) :
    canonicalPhaseLowBasisTailImagMixedValue k
        (canonicalPhaseTailCoreConj x) a b =
      -canonicalPhaseLowBasisTailImagMixedValue k x a b := by
  unfold canonicalPhaseLowBasisTailImagMixedValue
  rw [canonicalPhaseTailEvenImagProfile_conj,
    canonicalPhaseTailOddImagProfile_conj]
  have h := canonicalPhaseLowBasisMixed_smul_right k
    (evenTailImagPart x.fst.toV) (oddTailImagPart x.snd.toV)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).im :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth x.snd.toV t).im :
        ℝ) : ℂ)).im) = 0
      simp)
    (-1) a b
  simpa only [neg_one_smul, neg_one_mul,
    canonicalPhaseTailEvenImagProfile,
    boundaryCanonicalEvenTailProfile,
    canonicalPhaseTailOddImagProfile, canonicalOddTailProfile] using h

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailConjugationStructural
