import ArithmeticHodge.Analysis.BilinearFormCompletionCoercive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousTailMixedCauchyStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalTailDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailRealImagLinearStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalTailBilinearStructural

noncomputable section

open ArithmeticHodge.Analysis
open FormSpace
open UniformSpace
open YoshidaCoercivityNumerics
open YoshidaEndpointScaledCorrelation
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailMixedCauchyStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseCanonicalTailDiagonalStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseOddRealDecomposition
open YoshidaFactorTwoPhaseTailRealImagLinearStructural
open YoshidaFactorTwoPhaseTailRealImagStructural
open YoshidaOddHomogeneousCoercivity
open YoshidaWeightedTailBounds

/-!
# The completed canonical phase-tail bilinear form

The standard complex tail carrier is two real phase channels: its pointwise
real and imaginary coordinates.  Polarizing each channel gives a symmetric
real bilinear form whose diagonal is the already-proved coercive canonical
tail phase.  A uniform diagonal upper bound makes this form continuous, so it
extends without loss to the Hilbert completion and remains coercive there.
-/

abbrev CanonicalPhaseTailCompletion := Completion CanonicalPhaseTailCore

private theorem canonicalEvenTailPointwise_add
    (f g : YoshidaEvenOneNinetyNineTail) :
    canonicalEvenTailPointwise (f + g) =
      canonicalEvenTailPointwise f + canonicalEvenTailPointwise g := by
  apply Subtype.ext
  rfl

private theorem canonicalEvenTailPointwise_smul_real
    (r : ℝ) (f : YoshidaEvenOneNinetyNineTail) :
    canonicalEvenTailPointwise ((r : ℂ) • f) =
      (r : ℂ) • canonicalEvenTailPointwise f := by
  apply Subtype.ext
  rfl

@[simp] theorem canonicalPhaseTailEvenRealProfile_add
    (x y : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenRealProfile (x + y) =
      canonicalPhaseTailEvenRealProfile x +
        canonicalPhaseTailEvenRealProfile y := by
  unfold canonicalPhaseTailEvenRealProfile boundaryCanonicalEvenTailProfile
  rw [show (x + y).fst.toV = x.fst.toV + y.fst.toV by rfl,
    evenTailRealPart_add, canonicalEvenTailPointwise_add,
    boundaryContinuousEvenProfile_add]

@[simp] theorem canonicalPhaseTailEvenImagProfile_add
    (x y : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenImagProfile (x + y) =
      canonicalPhaseTailEvenImagProfile x +
        canonicalPhaseTailEvenImagProfile y := by
  unfold canonicalPhaseTailEvenImagProfile boundaryCanonicalEvenTailProfile
  rw [show (x + y).fst.toV = x.fst.toV + y.fst.toV by rfl,
    evenTailImagPart_add, canonicalEvenTailPointwise_add,
    boundaryContinuousEvenProfile_add]

@[simp] theorem canonicalPhaseTailOddRealProfile_add
    (x y : CanonicalPhaseTailCore) :
    canonicalPhaseTailOddRealProfile (x + y) =
      canonicalPhaseTailOddRealProfile x +
        canonicalPhaseTailOddRealProfile y := by
  funext t
  unfold canonicalPhaseTailOddRealProfile canonicalOddTailProfile
    centeredRescale
  rw [show (x + y).snd.toV = x.snd.toV + y.snd.toV by rfl,
    oddTailRealPart_add]
  simp

@[simp] theorem canonicalPhaseTailOddImagProfile_add
    (x y : CanonicalPhaseTailCore) :
    canonicalPhaseTailOddImagProfile (x + y) =
      canonicalPhaseTailOddImagProfile x +
        canonicalPhaseTailOddImagProfile y := by
  funext t
  unfold canonicalPhaseTailOddImagProfile canonicalOddTailProfile
    centeredRescale
  rw [show (x + y).snd.toV = x.snd.toV + y.snd.toV by rfl,
    oddTailImagPart_add]
  simp

@[simp] theorem canonicalPhaseTailEvenRealProfile_smul
    (r : ℝ) (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenRealProfile (r • x) =
      r • canonicalPhaseTailEvenRealProfile x := by
  unfold canonicalPhaseTailEvenRealProfile boundaryCanonicalEvenTailProfile
  rw [show (r • x).fst.toV = (r : ℂ) • x.fst.toV by rfl,
    evenTailRealPart_smul_real, canonicalEvenTailPointwise_smul_real,
    boundaryContinuousEvenProfile_smul_real]

@[simp] theorem canonicalPhaseTailEvenImagProfile_smul
    (r : ℝ) (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenImagProfile (r • x) =
      r • canonicalPhaseTailEvenImagProfile x := by
  unfold canonicalPhaseTailEvenImagProfile boundaryCanonicalEvenTailProfile
  rw [show (r • x).fst.toV = (r : ℂ) • x.fst.toV by rfl,
    evenTailImagPart_smul_real, canonicalEvenTailPointwise_smul_real,
    boundaryContinuousEvenProfile_smul_real]

@[simp] theorem canonicalPhaseTailOddRealProfile_smul
    (r : ℝ) (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailOddRealProfile (r • x) =
      r • canonicalPhaseTailOddRealProfile x := by
  funext t
  unfold canonicalPhaseTailOddRealProfile canonicalOddTailProfile
    centeredRescale
  rw [show (r • x).snd.toV = (r : ℂ) • x.snd.toV by rfl,
    oddTailRealPart_smul_real]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]

@[simp] theorem canonicalPhaseTailOddImagProfile_smul
    (r : ℝ) (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailOddImagProfile (r • x) =
      r • canonicalPhaseTailOddImagProfile x := by
  funext t
  unfold canonicalPhaseTailOddImagProfile canonicalOddTailProfile
    centeredRescale
  rw [show (r • x).snd.toV = (r : ℂ) • x.snd.toV by rfl,
    oddTailImagPart_smul_real]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]

/-- Polarization of the complete fixed-phase tail energy on the full complex
carrier, viewed as the sum of its real and imaginary phase channels. -/
def canonicalPhaseTailCoreBilinearValue
    (x y : CanonicalPhaseTailCore) (a b : ℝ) : ℝ :=
  factorTwoEndpointLowTailMixed
      (canonicalPhaseTailEvenRealProfile x)
      (canonicalPhaseTailEvenRealProfile y)
      (canonicalPhaseTailOddRealProfile x)
      (canonicalPhaseTailOddRealProfile y) a b +
    factorTwoEndpointLowTailMixed
      (canonicalPhaseTailEvenImagProfile x)
      (canonicalPhaseTailEvenImagProfile y)
      (canonicalPhaseTailOddImagProfile x)
      (canonicalPhaseTailOddImagProfile y) a b

private theorem factorTwoCenteredCleanPolarization_comm
    (u v : ℝ → ℝ) :
    factorTwoCenteredCleanPolarization u v =
      factorTwoCenteredCleanPolarization v u := by
  unfold factorTwoCenteredCleanPolarization
  rw [add_comm]
  ring

private theorem factorTwoCenteredSymmetricPerturbationBilinear_comm
    (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear u v =
      factorTwoCenteredSymmetricPerturbationBilinear v u := by
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_comm u v]

/-- The canonical full-complex polarization is symmetric. -/
theorem canonicalPhaseTailCoreBilinearValue_comm
    (x y : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseTailCoreBilinearValue x y a b =
      canonicalPhaseTailCoreBilinearValue y x a b := by
  unfold canonicalPhaseTailCoreBilinearValue
    factorTwoEndpointLowTailMixed
  rw [factorTwoCenteredCleanPolarization_comm
        (canonicalPhaseTailEvenRealProfile x)
        (canonicalPhaseTailEvenRealProfile y),
    factorTwoCenteredCleanPolarization_comm
        (canonicalPhaseTailOddRealProfile x)
        (canonicalPhaseTailOddRealProfile y),
    factorTwoCenteredCleanPolarization_comm
        (canonicalPhaseTailEvenImagProfile x)
        (canonicalPhaseTailEvenImagProfile y),
    factorTwoCenteredCleanPolarization_comm
        (canonicalPhaseTailOddImagProfile x)
        (canonicalPhaseTailOddImagProfile y),
    factorTwoCenteredSymmetricPerturbationBilinear_comm
        (canonicalPhaseTailEvenRealProfile x)
        (canonicalPhaseTailEvenRealProfile y),
    factorTwoCenteredSymmetricPerturbationBilinear_comm
        (canonicalPhaseTailOddRealProfile x)
        (canonicalPhaseTailOddRealProfile y),
    factorTwoCenteredSymmetricPerturbationBilinear_comm
        (canonicalPhaseTailEvenImagProfile x)
        (canonicalPhaseTailEvenImagProfile y),
    factorTwoCenteredSymmetricPerturbationBilinear_comm
        (canonicalPhaseTailOddImagProfile x)
        (canonicalPhaseTailOddImagProfile y)]
  ring

/-- Additivity in the first canonical complex tail argument. -/
theorem canonicalPhaseTailCoreBilinearValue_add_left
    (x y z : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseTailCoreBilinearValue (x + y) z a b =
      canonicalPhaseTailCoreBilinearValue x z a b +
        canonicalPhaseTailCoreBilinearValue y z a b := by
  obtain ⟨hxrNeg, hxrPos⟩ :=
    oddTenTail_endpoints_zero (oddTailRealPart x.snd.toV)
  obtain ⟨hyrNeg, hyrPos⟩ :=
    oddTenTail_endpoints_zero (oddTailRealPart y.snd.toV)
  obtain ⟨hzrNeg, hzrPos⟩ :=
    oddTenTail_endpoints_zero (oddTailRealPart z.snd.toV)
  obtain ⟨hxiNeg, hxiPos⟩ :=
    oddTenTail_endpoints_zero (oddTailImagPart x.snd.toV)
  obtain ⟨hyiNeg, hyiPos⟩ :=
    oddTenTail_endpoints_zero (oddTailImagPart y.snd.toV)
  obtain ⟨hziNeg, hziPos⟩ :=
    oddTenTail_endpoints_zero (oddTailImagPart z.snd.toV)
  have hr := factorTwoEndpointLowTailMixed_boundaryContinuous_add_left
    (canonicalEvenTailPointwise (evenTailRealPart x.fst.toV))
    (canonicalEvenTailPointwise (evenTailRealPart y.fst.toV))
    (canonicalEvenTailPointwise (evenTailRealPart z.fst.toV))
    (oddTailRealPart x.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
    (oddTailRealPart y.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
    (oddTailRealPart z.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).re :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth y.fst.toV t).re :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth z.fst.toV t).re :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth x.snd.toV t).re : ℝ) :
        ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth y.snd.toV t).re : ℝ) :
        ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth z.snd.toV t).re : ℝ) :
        ℂ)).im) = 0
      simp)
    hxrNeg hxrPos hyrNeg hyrPos hzrNeg hzrPos a b
  have hi := factorTwoEndpointLowTailMixed_boundaryContinuous_add_left
    (canonicalEvenTailPointwise (evenTailImagPart x.fst.toV))
    (canonicalEvenTailPointwise (evenTailImagPart y.fst.toV))
    (canonicalEvenTailPointwise (evenTailImagPart z.fst.toV))
    (oddTailImagPart x.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
    (oddTailImagPart y.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
    (oddTailImagPart z.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).im :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth y.fst.toV t).im :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth z.fst.toV t).im :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth x.snd.toV t).im : ℝ) :
        ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth y.snd.toV t).im : ℝ) :
        ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth z.snd.toV t).im : ℝ) :
        ℂ)).im) = 0
      simp)
    hxiNeg hxiPos hyiNeg hyiPos hziNeg hziPos a b
  unfold canonicalPhaseTailCoreBilinearValue
  rw [canonicalPhaseTailEvenRealProfile_add,
    canonicalPhaseTailOddRealProfile_add,
    canonicalPhaseTailEvenImagProfile_add,
    canonicalPhaseTailOddImagProfile_add]
  change factorTwoEndpointLowTailMixed
      (canonicalPhaseTailEvenRealProfile x +
        canonicalPhaseTailEvenRealProfile y)
      (canonicalPhaseTailEvenRealProfile z)
      (canonicalPhaseTailOddRealProfile x +
        canonicalPhaseTailOddRealProfile y)
      (canonicalPhaseTailOddRealProfile z) a b =
    factorTwoEndpointLowTailMixed
        (canonicalPhaseTailEvenRealProfile x)
        (canonicalPhaseTailEvenRealProfile z)
        (canonicalPhaseTailOddRealProfile x)
        (canonicalPhaseTailOddRealProfile z) a b +
      factorTwoEndpointLowTailMixed
        (canonicalPhaseTailEvenRealProfile y)
        (canonicalPhaseTailEvenRealProfile z)
        (canonicalPhaseTailOddRealProfile y)
        (canonicalPhaseTailOddRealProfile z) a b at hr
  change factorTwoEndpointLowTailMixed
      (canonicalPhaseTailEvenImagProfile x +
        canonicalPhaseTailEvenImagProfile y)
      (canonicalPhaseTailEvenImagProfile z)
      (canonicalPhaseTailOddImagProfile x +
        canonicalPhaseTailOddImagProfile y)
      (canonicalPhaseTailOddImagProfile z) a b =
    factorTwoEndpointLowTailMixed
        (canonicalPhaseTailEvenImagProfile x)
        (canonicalPhaseTailEvenImagProfile z)
        (canonicalPhaseTailOddImagProfile x)
        (canonicalPhaseTailOddImagProfile z) a b +
      factorTwoEndpointLowTailMixed
        (canonicalPhaseTailEvenImagProfile y)
        (canonicalPhaseTailEvenImagProfile z)
        (canonicalPhaseTailOddImagProfile y)
        (canonicalPhaseTailOddImagProfile z) a b at hi
  rw [hr, hi]
  ring

/-- Real homogeneity in the first canonical complex tail argument. -/
theorem canonicalPhaseTailCoreBilinearValue_smul_left
    (r : ℝ) (x y : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseTailCoreBilinearValue (r • x) y a b =
      r * canonicalPhaseTailCoreBilinearValue x y a b := by
  obtain ⟨hxrNeg, hxrPos⟩ :=
    oddTenTail_endpoints_zero (oddTailRealPart x.snd.toV)
  obtain ⟨hyrNeg, hyrPos⟩ :=
    oddTenTail_endpoints_zero (oddTailRealPart y.snd.toV)
  obtain ⟨hxiNeg, hxiPos⟩ :=
    oddTenTail_endpoints_zero (oddTailImagPart x.snd.toV)
  obtain ⟨hyiNeg, hyiPos⟩ :=
    oddTenTail_endpoints_zero (oddTailImagPart y.snd.toV)
  have hr := factorTwoEndpointLowTailMixed_boundaryContinuous_smul_smul
    (canonicalEvenTailPointwise (evenTailRealPart x.fst.toV))
    (canonicalEvenTailPointwise (evenTailRealPart y.fst.toV))
    (oddTailRealPart x.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
    (oddTailRealPart y.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).re :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth y.fst.toV t).re :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth x.snd.toV t).re : ℝ) :
        ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth y.snd.toV t).re : ℝ) :
        ℂ)).im) = 0
      simp)
    hxrNeg hxrPos hyrNeg hyrPos r 1 a b
  have hi := factorTwoEndpointLowTailMixed_boundaryContinuous_smul_smul
    (canonicalEvenTailPointwise (evenTailImagPart x.fst.toV))
    (canonicalEvenTailPointwise (evenTailImagPart y.fst.toV))
    (oddTailImagPart x.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
    (oddTailImagPart y.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).im :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth y.fst.toV t).im :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth x.snd.toV t).im : ℝ) :
        ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth y.snd.toV t).im : ℝ) :
        ℂ)).im) = 0
      simp)
    hxiNeg hxiPos hyiNeg hyiPos r 1 a b
  simp only [one_smul, mul_one] at hr hi
  unfold canonicalPhaseTailCoreBilinearValue
  rw [canonicalPhaseTailEvenRealProfile_smul,
    canonicalPhaseTailOddRealProfile_smul,
    canonicalPhaseTailEvenImagProfile_smul,
    canonicalPhaseTailOddImagProfile_smul]
  change factorTwoEndpointLowTailMixed
      (r • canonicalPhaseTailEvenRealProfile x)
      (canonicalPhaseTailEvenRealProfile y)
      (r • canonicalPhaseTailOddRealProfile x)
      (canonicalPhaseTailOddRealProfile y) a b =
    r * factorTwoEndpointLowTailMixed
      (canonicalPhaseTailEvenRealProfile x)
      (canonicalPhaseTailEvenRealProfile y)
      (canonicalPhaseTailOddRealProfile x)
      (canonicalPhaseTailOddRealProfile y) a b at hr
  change factorTwoEndpointLowTailMixed
      (r • canonicalPhaseTailEvenImagProfile x)
      (canonicalPhaseTailEvenImagProfile y)
      (r • canonicalPhaseTailOddImagProfile x)
      (canonicalPhaseTailOddImagProfile y) a b =
    r * factorTwoEndpointLowTailMixed
      (canonicalPhaseTailEvenImagProfile x)
      (canonicalPhaseTailEvenImagProfile y)
      (canonicalPhaseTailOddImagProfile x)
      (canonicalPhaseTailOddImagProfile y) a b at hi
  rw [hr, hi]
  ring

/-- Additivity in the second canonical complex tail argument. -/
theorem canonicalPhaseTailCoreBilinearValue_add_right
    (x y z : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseTailCoreBilinearValue x (y + z) a b =
      canonicalPhaseTailCoreBilinearValue x y a b +
        canonicalPhaseTailCoreBilinearValue x z a b := by
  rw [canonicalPhaseTailCoreBilinearValue_comm x (y + z),
    canonicalPhaseTailCoreBilinearValue_add_left,
    canonicalPhaseTailCoreBilinearValue_comm y x,
    canonicalPhaseTailCoreBilinearValue_comm z x]

/-- Real homogeneity in the second canonical complex tail argument. -/
theorem canonicalPhaseTailCoreBilinearValue_smul_right
    (r : ℝ) (x y : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseTailCoreBilinearValue x (r • y) a b =
      r * canonicalPhaseTailCoreBilinearValue x y a b := by
  rw [canonicalPhaseTailCoreBilinearValue_comm x (r • y),
    canonicalPhaseTailCoreBilinearValue_smul_left,
    canonicalPhaseTailCoreBilinearValue_comm y x]

private theorem factorTwoCenteredCleanPolarization_self
    (u : ℝ → ℝ) :
    factorTwoCenteredCleanPolarization u u =
      yoshidaEndpointOddCleanQuadratic u := by
  unfold factorTwoCenteredCleanPolarization
  rw [show u + u = fun x ↦ (2 : ℝ) * u x by
    funext x
    simp [two_mul],
    yoshidaEndpointOddCleanQuadratic_const_mul]
  ring

/-- The mixed polarization recovers the complete phase on the diagonal. -/
theorem factorTwoEndpointLowTailMixed_self_eq_phase
    (u v : ℝ → ℝ) (a b : ℝ) :
    factorTwoEndpointLowTailMixed u u v v a b =
      factorTwoEndpointChannelPhase u v a b := by
  unfold factorTwoEndpointLowTailMixed factorTwoEndpointChannelPhase
    factorTwoEndpointChannelCleanSum factorTwoEndpointChannelSymmetricSum
  rw [factorTwoCenteredCleanPolarization_self,
    factorTwoCenteredCleanPolarization_self,
    factorTwoCenteredSymmetricPerturbationBilinear_self,
    factorTwoCenteredSymmetricPerturbationBilinear_self]
  ring

/-- The algebraic polarization has exactly the previously established
canonical phase diagonal. -/
@[simp] theorem canonicalPhaseTailCoreBilinearValue_self
    (x : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseTailCoreBilinearValue x x a b =
      canonicalPhaseTailCoreDiagonal x a b := by
  unfold canonicalPhaseTailCoreBilinearValue
    canonicalPhaseTailCoreDiagonal
  rw [factorTwoEndpointLowTailMixed_self_eq_phase,
    factorTwoEndpointLowTailMixed_self_eq_phase]

/-- The fixed-phase canonical tail polarization as an algebraic real
bilinear form. -/
def canonicalPhaseTailCoreBilinear (a b : ℝ) :
    LinearMap.BilinForm ℝ CanonicalPhaseTailCore :=
  LinearMap.mk₂ ℝ
    (fun x y ↦ canonicalPhaseTailCoreBilinearValue x y a b)
    (fun x y z ↦
      canonicalPhaseTailCoreBilinearValue_add_left x y z a b)
    (fun r x y ↦ by
      simpa only [smul_eq_mul] using
        canonicalPhaseTailCoreBilinearValue_smul_left r x y a b)
    (fun x y z ↦
      canonicalPhaseTailCoreBilinearValue_add_right x y z a b)
    (fun r x y ↦ by
      simpa only [smul_eq_mul] using
        canonicalPhaseTailCoreBilinearValue_smul_right r x y a b)

@[simp] theorem canonicalPhaseTailCoreBilinear_apply
    (a b : ℝ) (x y : CanonicalPhaseTailCore) :
    canonicalPhaseTailCoreBilinear a b x y =
      canonicalPhaseTailCoreBilinearValue x y a b :=
  rfl

theorem canonicalPhaseTailCoreBilinear_isSymm (a b : ℝ) :
    (canonicalPhaseTailCoreBilinear a b).IsSymm :=
  ⟨fun x y ↦ canonicalPhaseTailCoreBilinearValue_comm x y a b⟩

/-- Positive-semidefinite bilinear Cauchy--Schwarz on the full complex tail
carrier. -/
theorem canonicalPhaseTailCoreBilinear_sq_le
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (x y : CanonicalPhaseTailCore) :
    canonicalPhaseTailCoreBilinear a b x y ^ 2 ≤
      canonicalPhaseTailCoreBilinear a b x x *
        canonicalPhaseTailCoreBilinear a b y y := by
  exact (canonicalPhaseTailCoreBilinear a b).apply_sq_le_of_symm
    (fun z ↦ by
      rw [canonicalPhaseTailCoreBilinear_apply,
        canonicalPhaseTailCoreBilinearValue_self]
      exact canonicalPhaseTailCoreDiagonal_nonneg z a b hphase)
    (by
      rw [← LinearMap.BilinForm.isSymm_iff]
      exact canonicalPhaseTailCoreBilinear_isSymm a b) x y

/-- Uniform operator bound obtained from bilinear Cauchy--Schwarz and the
flipped-phase diagonal estimate. -/
theorem norm_canonicalPhaseTailCoreBilinear_apply_le
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (x y : CanonicalPhaseTailCore) :
    ‖canonicalPhaseTailCoreBilinear a b x y‖ ≤
      (399 / (200 * yoshidaA) : ℝ) * ‖x‖ * ‖y‖ := by
  let M : ℝ := 399 / (200 * yoshidaA)
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact div_nonneg (by norm_num)
      (mul_nonneg (by norm_num) yoshidaA_pos.le)
  have hcs := canonicalPhaseTailCoreBilinear_sq_le a b hphase x y
  have hx0 : 0 ≤ canonicalPhaseTailCoreBilinear a b x x := by
    rw [canonicalPhaseTailCoreBilinear_apply,
      canonicalPhaseTailCoreBilinearValue_self]
    exact canonicalPhaseTailCoreDiagonal_nonneg x a b hphase
  have hy0 : 0 ≤ canonicalPhaseTailCoreBilinear a b y y := by
    rw [canonicalPhaseTailCoreBilinear_apply,
      canonicalPhaseTailCoreBilinearValue_self]
    exact canonicalPhaseTailCoreDiagonal_nonneg y a b hphase
  have hxU : canonicalPhaseTailCoreBilinear a b x x ≤ M * ‖x‖ ^ 2 := by
    rw [canonicalPhaseTailCoreBilinear_apply,
      canonicalPhaseTailCoreBilinearValue_self]
    simpa only [M] using canonicalPhaseTailCoreDiagonal_upper x a b hphase
  have hyU : canonicalPhaseTailCoreBilinear a b y y ≤ M * ‖y‖ ^ 2 := by
    rw [canonicalPhaseTailCoreBilinear_apply,
      canonicalPhaseTailCoreBilinearValue_self]
    simpa only [M] using canonicalPhaseTailCoreDiagonal_upper y a b hphase
  have hprod :
      canonicalPhaseTailCoreBilinear a b x x *
          canonicalPhaseTailCoreBilinear a b y y ≤
        (M * ‖x‖ ^ 2) * (M * ‖y‖ ^ 2) :=
    mul_le_mul hxU hyU hy0 (mul_nonneg hM (sq_nonneg ‖x‖))
  have hsq : canonicalPhaseTailCoreBilinear a b x y ^ 2 ≤
      (M * ‖x‖ * ‖y‖) ^ 2 := by
    calc
      _ ≤ _ := hcs
      _ ≤ _ := hprod
      _ = _ := by ring
  have habs := abs_le_of_sq_le_sq hsq
    (mul_nonneg (mul_nonneg hM (norm_nonneg x)) (norm_nonneg y))
  simpa only [Real.norm_eq_abs, M] using habs

/-- Bounded bilinear form on the algebraic canonical tail carrier. -/
def canonicalPhaseTailCoreContinuousBilinear
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    CanonicalPhaseTailCore →L[ℝ] CanonicalPhaseTailCore →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (canonicalPhaseTailCoreBilinear a b)
    (399 / (200 * yoshidaA))
    (norm_canonicalPhaseTailCoreBilinear_apply_le a b hphase)

@[simp] theorem canonicalPhaseTailCoreContinuousBilinear_apply
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (x y : CanonicalPhaseTailCore) :
    canonicalPhaseTailCoreContinuousBilinear a b hphase x y =
      canonicalPhaseTailCoreBilinearValue x y a b :=
  rfl

/-- Exact coercivity of the bounded algebraic tail form. -/
theorem canonicalPhaseTailCoreContinuousBilinear_isCoercive
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    IsCoercive (canonicalPhaseTailCoreContinuousBilinear a b hphase) := by
  refine ⟨1 / (200 * yoshidaA),
    one_div_pos.mpr (mul_pos (by norm_num) yoshidaA_pos), ?_⟩
  intro x
  rw [canonicalPhaseTailCoreContinuousBilinear_apply,
    canonicalPhaseTailCoreBilinearValue_self]
  have h := canonicalPhaseTailCoreDiagonal_coercive x a b hphase
  nlinarith [sq_nonneg ‖x‖]

/-- The complete fixed-phase form on the Hilbert completion of the canonical
complex tail carrier. -/
def completedCanonicalPhaseTailBilinear
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    CanonicalPhaseTailCompletion →L[ℝ]
      CanonicalPhaseTailCompletion →L[ℝ] ℝ :=
  completionBilinearExtension
    (canonicalPhaseTailCoreContinuousBilinear a b hphase)

@[simp] theorem completedCanonicalPhaseTailBilinear_coe_coe
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (x y : CanonicalPhaseTailCore) :
    completedCanonicalPhaseTailBilinear a b hphase
        (x : CanonicalPhaseTailCompletion)
        (y : CanonicalPhaseTailCompletion) =
      canonicalPhaseTailCoreBilinearValue x y a b := by
  exact completionBilinearExtension_coe_coe
    (canonicalPhaseTailCoreContinuousBilinear a b hphase) x y

/-- Symmetry survives passage to the completed tail space. -/
theorem completedCanonicalPhaseTailBilinear_symm
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (x y : CanonicalPhaseTailCompletion) :
    completedCanonicalPhaseTailBilinear a b hphase x y =
      completedCanonicalPhaseTailBilinear a b hphase y x := by
  exact completionBilinearExtension_symm
    (canonicalPhaseTailCoreContinuousBilinear a b hphase)
    (fun u v ↦ canonicalPhaseTailCoreBilinearValue_comm u v a b) x y

/-- The complete canonical phase-tail form remains uniformly coercive on its
Hilbert completion. -/
theorem completedCanonicalPhaseTailBilinear_isCoercive
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    IsCoercive (completedCanonicalPhaseTailBilinear a b hphase) := by
  exact isCoercive_completionBilinearExtension
    (canonicalPhaseTailCoreContinuousBilinear a b hphase)
    (canonicalPhaseTailCoreContinuousBilinear_isCoercive a b hphase)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
