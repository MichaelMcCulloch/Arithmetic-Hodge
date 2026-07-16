import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailAssemblyClosureStructural

set_option autoImplicit false

open Complex Real
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaEndpointScaledCorrelation
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailRieszStructural
open YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseCanonicalTailDiagonalStructural
open YoshidaFactorTwoPhaseEndpointTailMixedCauchyStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseTailRealImagLinearStructural
open YoshidaFactorTwoPhaseTailRealImagStructural
open YoshidaOddHomogeneousCoercivity
open YoshidaWeightedTailBounds

/-!
# Quarter-turn symmetry of the canonical low--tail correction

Multiplication by `i` rotates the real and imaginary tail coordinates.  The
canonical phase-tail form is invariant under this quarter turn, while the
real and imaginary low-tail functionals rotate into one another.  Coercive
uniqueness therefore identifies the two diagonal Riesz-correction blocks.
The complementary conjugation symmetry is needed to make the mixed block
vanish.
-/

@[simp] theorem evenTailRealPart_I_smul
    (f : YoshidaEvenOneNinetyNineTail) :
    evenTailRealPart (Complex.I • f) = -evenTailImagPart f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change (((((Complex.I *
      evenOneNinetyNineTailToClippedSmooth f t).re : ℝ) : ℂ))) =
    -((((evenOneNinetyNineTailToClippedSmooth f t).im : ℝ) : ℂ))
  apply Complex.ext <;> simp

@[simp] theorem evenTailImagPart_I_smul
    (f : YoshidaEvenOneNinetyNineTail) :
    evenTailImagPart (Complex.I • f) = evenTailRealPart f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change (((((Complex.I *
      evenOneNinetyNineTailToClippedSmooth f t).im : ℝ) : ℂ))) =
    ((((evenOneNinetyNineTailToClippedSmooth f t).re : ℝ) : ℂ))
  apply Complex.ext <;> simp

@[simp] theorem oddTailRealPart_I_smul (f : YoshidaOddTenTail) :
    oddTailRealPart (Complex.I • f) = -oddTailImagPart f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change (((((Complex.I * oddTenTailToClippedSmooth f t).re : ℝ) : ℂ))) =
    -((((oddTenTailToClippedSmooth f t).im : ℝ) : ℂ))
  apply Complex.ext <;> simp

@[simp] theorem oddTailImagPart_I_smul (f : YoshidaOddTenTail) :
    oddTailImagPart (Complex.I • f) = oddTailRealPart f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change (((((Complex.I * oddTenTailToClippedSmooth f t).im : ℝ) : ℂ))) =
    ((((oddTenTailToClippedSmooth f t).re : ℝ) : ℂ))
  apply Complex.ext <;> simp

private theorem canonicalEvenTailPointwise_neg
    (f : YoshidaEvenOneNinetyNineTail) :
    canonicalEvenTailPointwise (-f) =
      ((-1 : ℝ) : ℂ) • canonicalEvenTailPointwise f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext t
  change -evenOneNinetyNineTailToClippedSmooth f t =
    (((-1 : ℝ) : ℂ) * evenOneNinetyNineTailToClippedSmooth f t)
  simp

theorem canonicalPhaseTailEvenRealProfile_I_smul
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenRealProfile (Complex.I • x) =
      -canonicalPhaseTailEvenImagProfile x := by
  unfold canonicalPhaseTailEvenRealProfile
    canonicalPhaseTailEvenImagProfile boundaryCanonicalEvenTailProfile
  rw [show (Complex.I • x).fst.toV = Complex.I • x.fst.toV by rfl,
    evenTailRealPart_I_smul, canonicalEvenTailPointwise_neg]
  simpa only [neg_one_smul] using
    boundaryContinuousEvenProfile_smul_real (-1)
      (canonicalEvenTailPointwise (evenTailImagPart x.fst.toV))

theorem canonicalPhaseTailEvenImagProfile_I_smul
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenImagProfile (Complex.I • x) =
      canonicalPhaseTailEvenRealProfile x := by
  unfold canonicalPhaseTailEvenRealProfile
    canonicalPhaseTailEvenImagProfile boundaryCanonicalEvenTailProfile
  rw [show (Complex.I • x).fst.toV = Complex.I • x.fst.toV by rfl,
    evenTailImagPart_I_smul]

theorem canonicalPhaseTailOddRealProfile_I_smul
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailOddRealProfile (Complex.I • x) =
      -canonicalPhaseTailOddImagProfile x := by
  funext t
  unfold canonicalPhaseTailOddRealProfile canonicalPhaseTailOddImagProfile
    canonicalOddTailProfile centeredRescale
  rw [show (Complex.I • x).snd.toV = Complex.I • x.snd.toV by rfl,
    oddTailRealPart_I_smul]
  change (-oddTenTailToClippedSmooth (oddTailImagPart x.snd.toV)
    (yoshidaA * t)).re =
      -(oddTenTailToClippedSmooth (oddTailImagPart x.snd.toV)
        (yoshidaA * t)).re
  simp

theorem canonicalPhaseTailOddImagProfile_I_smul
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailOddImagProfile (Complex.I • x) =
      canonicalPhaseTailOddRealProfile x := by
  funext t
  unfold canonicalPhaseTailOddRealProfile canonicalPhaseTailOddImagProfile
    canonicalOddTailProfile centeredRescale
  rw [show (Complex.I • x).snd.toV = Complex.I • x.snd.toV by rfl,
    oddTailImagPart_I_smul]

theorem canonicalPhaseTailCoreDiagonal_I_smul
    (x : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseTailCoreDiagonal (Complex.I • x) a b =
      canonicalPhaseTailCoreDiagonal x a b := by
  rw [canonicalPhaseTailCoreDiagonal,
    canonicalPhaseTailEvenRealProfile_I_smul,
    canonicalPhaseTailOddRealProfile_I_smul,
    canonicalPhaseTailEvenImagProfile_I_smul,
    canonicalPhaseTailOddImagProfile_I_smul,
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
  ring

theorem canonicalPhaseTailCoreBilinearValue_eq_polarization
    (x y : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseTailCoreBilinearValue x y a b =
      (canonicalPhaseTailCoreDiagonal (x + y) a b -
        canonicalPhaseTailCoreDiagonal x a b -
        canonicalPhaseTailCoreDiagonal y a b) / 2 := by
  rw [← canonicalPhaseTailCoreBilinearValue_self,
    ← canonicalPhaseTailCoreBilinearValue_self,
    ← canonicalPhaseTailCoreBilinearValue_self,
    canonicalPhaseTailCoreBilinearValue_add_left,
    canonicalPhaseTailCoreBilinearValue_add_right,
    canonicalPhaseTailCoreBilinearValue_add_right,
    canonicalPhaseTailCoreBilinearValue_comm y x]
  ring

/-- The algebraic canonical tail form is invariant under simultaneous
quarter turn. -/
theorem canonicalPhaseTailCoreBilinearValue_I_smul_I_smul
    (x y : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseTailCoreBilinearValue (Complex.I • x)
        (Complex.I • y) a b =
      canonicalPhaseTailCoreBilinearValue x y a b := by
  rw [canonicalPhaseTailCoreBilinearValue_eq_polarization,
    ← smul_add, canonicalPhaseTailCoreDiagonal_I_smul,
    canonicalPhaseTailCoreDiagonal_I_smul,
    canonicalPhaseTailCoreDiagonal_I_smul,
    ← canonicalPhaseTailCoreBilinearValue_eq_polarization]

/-- Multiplication by `i` is skew-adjoint for the real canonical tail
bilinear form. -/
theorem canonicalPhaseTailCoreBilinearValue_I_smul_left
    (x y : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseTailCoreBilinearValue (Complex.I • x) y a b =
      -canonicalPhaseTailCoreBilinearValue x (Complex.I • y) a b := by
  have h := canonicalPhaseTailCoreBilinearValue_I_smul_I_smul
    x (Complex.I • y) a b
  have hII : Complex.I • (Complex.I • y) = -y := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [hII] at h
  have hneg :
      canonicalPhaseTailCoreBilinearValue (Complex.I • x) (-y) a b =
        -canonicalPhaseTailCoreBilinearValue (Complex.I • x) y a b := by
    simpa only [neg_one_smul, neg_one_mul] using
      canonicalPhaseTailCoreBilinearValue_smul_right
        (-1) (Complex.I • x) y a b
  linarith

theorem canonicalPhaseLowBasisTailRealMixedValue_I_smul
    (k : FactorTwoPhaseLowIndex) (x : CanonicalPhaseTailCore)
    (a b : ℝ) :
    canonicalPhaseLowBasisTailRealMixedValue k (Complex.I • x) a b =
      -canonicalPhaseLowBasisTailImagMixedValue k x a b := by
  unfold canonicalPhaseLowBasisTailRealMixedValue
    canonicalPhaseLowBasisTailImagMixedValue
  rw [canonicalPhaseTailEvenRealProfile_I_smul,
    canonicalPhaseTailOddRealProfile_I_smul]
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

theorem canonicalPhaseLowBasisTailImagMixedValue_I_smul
    (k : FactorTwoPhaseLowIndex) (x : CanonicalPhaseTailCore)
    (a b : ℝ) :
    canonicalPhaseLowBasisTailImagMixedValue k (Complex.I • x) a b =
      canonicalPhaseLowBasisTailRealMixedValue k x a b := by
  unfold canonicalPhaseLowBasisTailRealMixedValue
    canonicalPhaseLowBasisTailImagMixedValue
  rw [canonicalPhaseTailEvenImagProfile_I_smul,
    canonicalPhaseTailOddImagProfile_I_smul]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnStructural
