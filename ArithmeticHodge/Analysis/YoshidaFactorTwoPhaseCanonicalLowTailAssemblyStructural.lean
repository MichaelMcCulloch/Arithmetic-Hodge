import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural

set_option autoImplicit false

open Complex Matrix Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailAssemblyStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEndpointScaledCorrelation
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailMixedCauchyStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddRealDecomposition
open YoshidaFactorTwoPhaseTailRealImagStructural
open YoshidaOddModeRegularity
open YoshidaOddHomogeneousCoercivity
open YoshidaPointwiseParityCore
open YoshidaWeightedTailBounds

/-!
# Physical assembly of the canonical low--tail Schur quadratic

The completed Schur square is useful for the same-seed problem only after
its finite coordinates and completed functionals are identified with the
literal low profiles and low--tail mixed block.  This module supplies that
exact synthesis bridge for both pointwise real coordinates of a complex
canonical seed.
-/

/-- Extract the even coordinates from one packed canonical low vector. -/
def canonicalPhaseLowEvenCoefficients
    (c : FactorTwoPhaseLowIndex → ℝ) : YoshidaEvenIndex → ℝ :=
  fun i ↦ c (Sum.inl i)

/-- Extract the odd coordinates from one packed canonical low vector. -/
def canonicalPhaseLowOddCoefficients
    (c : FactorTwoPhaseLowIndex → ℝ) : YoshidaOddIndex → ℝ :=
  fun j ↦ c (Sum.inr j)

/-- The real canonical odd low synthesis inside the clipped periodic core. -/
def canonicalOddRealLowPeriodicCore
    (o : YoshidaOddIndex → ℝ) : YoshidaClippedPeriodicCore yoshidaA :=
  ∑ j, (o j : ℂ) • canonicalOddLowModePeriodicCore j

@[simp] theorem canonicalOddRealLowPeriodicCore_toSmooth
    (o : YoshidaOddIndex → ℝ) :
    ((canonicalOddRealLowPeriodicCore o :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) =
        ∑ j, (o j : ℂ) • yoshidaClippedOddLowMode yoshidaA j := by
  classical
  simp [canonicalOddRealLowPeriodicCore]

private theorem canonicalEvenRealLowPointwise_im_zero
    (e : YoshidaEvenIndex → ℝ) (x : ℝ) :
    ((((canonicalEvenRealLowPointwise e).1 :
        YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) x).im = 0 := by
  classical
  simp only [canonicalEvenRealLowPointwise,
    canonicalEvenRealLowPeriodicCore_toSmooth, Submodule.coe_sum,
    Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [evenLowMode_im_zero]
    ring

private theorem canonicalOddRealLowPeriodicCore_im_zero
    (o : YoshidaOddIndex → ℝ) (x : ℝ) :
    ((canonicalOddRealLowPeriodicCore o : YoshidaClippedSmooth yoshidaA) x).im = 0 := by
  classical
  simp only [canonicalOddRealLowPeriodicCore_toSmooth, Submodule.coe_sum,
    Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  exact Finset.sum_eq_zero fun j _ ↦ by
    rw [oddLowMode_im_zero]
    ring

private theorem canonicalOddRealLowPeriodicCore_left_endpoint
    (o : YoshidaOddIndex → ℝ) :
    (canonicalOddRealLowPeriodicCore o : YoshidaClippedSmooth yoshidaA)
        (-yoshidaA) = 0 := by
  classical
  simp only [canonicalOddRealLowPeriodicCore_toSmooth, Submodule.coe_sum,
    Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
  exact Finset.sum_eq_zero fun j _ ↦ by
    change (o j : ℂ) •
      yoshidaClippedOddMode yoshidaA (j.1 + 1) (-yoshidaA) = 0
    rw [yoshidaClippedOddMode_left_endpoint yoshidaA_pos (j.1 + 1)]
    simp

private theorem canonicalOddRealLowPeriodicCore_right_endpoint
    (o : YoshidaOddIndex → ℝ) :
    (canonicalOddRealLowPeriodicCore o : YoshidaClippedSmooth yoshidaA)
        yoshidaA = 0 := by
  classical
  simp only [canonicalOddRealLowPeriodicCore_toSmooth, Submodule.coe_sum,
    Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
  exact Finset.sum_eq_zero fun j _ ↦ by
    change (o j : ℂ) •
      yoshidaClippedOddMode yoshidaA (j.1 + 1) yoshidaA = 0
    rw [yoshidaClippedOddMode_right_endpoint yoshidaA_pos (j.1 + 1)]
    simp

/-- The raw real profile of the odd periodic-core synthesis is exactly the
existing centered odd low synthesis. -/
theorem canonicalOddRealLowPeriodicCore_profile
    (o : YoshidaOddIndex → ℝ) :
    centeredRescale yoshidaA (fun x ↦
      ((canonicalOddRealLowPeriodicCore o :
        YoshidaClippedSmooth yoshidaA) x).re) =
      factorTwoOddLowSynthesis o := by
  classical
  funext x
  unfold canonicalOddRealLowPeriodicCore factorTwoOddLowSynthesis
    factorTwoCenteredOddLowProfile centeredRescale
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [canonicalOddLowModePeriodicCore_toSmooth]

private theorem factorTwoBoundaryCanonicalEvenLowProfile_add
    (e₁ e₂ : YoshidaEvenIndex → ℝ) :
    factorTwoBoundaryCanonicalEvenLowProfile (e₁ + e₂) =
      factorTwoBoundaryCanonicalEvenLowProfile e₁ +
        factorTwoBoundaryCanonicalEvenLowProfile e₂ := by
  unfold factorTwoBoundaryCanonicalEvenLowProfile
  rw [show canonicalEvenRealLowPointwise (e₁ + e₂) =
      canonicalEvenRealLowPointwise e₁ +
        canonicalEvenRealLowPointwise e₂ by
    apply Subtype.ext
    change canonicalEvenRealLowPeriodicCore (e₁ + e₂) =
      canonicalEvenRealLowPeriodicCore e₁ +
        canonicalEvenRealLowPeriodicCore e₂
    classical
    simp [canonicalEvenRealLowPeriodicCore, add_smul,
      Finset.sum_add_distrib],
    boundaryContinuousEvenProfile_add]

private theorem factorTwoBoundaryCanonicalEvenLowProfile_smul
    (r : ℝ) (e : YoshidaEvenIndex → ℝ) :
    factorTwoBoundaryCanonicalEvenLowProfile (r • e) =
      r • factorTwoBoundaryCanonicalEvenLowProfile e := by
  unfold factorTwoBoundaryCanonicalEvenLowProfile
  rw [show canonicalEvenRealLowPointwise (r • e) =
      (r : ℂ) • canonicalEvenRealLowPointwise e by
    apply Subtype.ext
    change canonicalEvenRealLowPeriodicCore (r • e) =
      (r : ℂ) • canonicalEvenRealLowPeriodicCore e
    classical
    simp [canonicalEvenRealLowPeriodicCore, smul_smul,
      Finset.smul_sum],
    boundaryContinuousEvenProfile_smul_real]

private theorem factorTwoOddLowSynthesis_add
    (o₁ o₂ : YoshidaOddIndex → ℝ) :
    factorTwoOddLowSynthesis (o₁ + o₂) =
      factorTwoOddLowSynthesis o₁ + factorTwoOddLowSynthesis o₂ := by
  classical
  unfold factorTwoOddLowSynthesis
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

private theorem factorTwoOddLowSynthesis_smul
    (r : ℝ) (o : YoshidaOddIndex → ℝ) :
    factorTwoOddLowSynthesis (r • o) = r • factorTwoOddLowSynthesis o := by
  classical
  unfold factorTwoOddLowSynthesis
  simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [smul_smul]

private theorem canonicalPhaseLowTailMixed_add_profiles
    (c₁ c₂ : FactorTwoPhaseLowIndex → ℝ)
    (feTail : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
    (roTail : YoshidaClippedPeriodicCore yoshidaA)
    (heTailReal : ∀ x : ℝ,
      ((feTail.1 : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoTailReal : ∀ x : ℝ,
      ((roTail : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoTailNeg : (roTail : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoTailPos : (roTail : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (a b : ℝ) :
    factorTwoEndpointLowTailMixed
        (factorTwoBoundaryCanonicalEvenLowProfile
          (canonicalPhaseLowEvenCoefficients c₁) +
         factorTwoBoundaryCanonicalEvenLowProfile
          (canonicalPhaseLowEvenCoefficients c₂))
        (boundaryContinuousEvenProfile feTail)
        (factorTwoOddLowSynthesis (canonicalPhaseLowOddCoefficients c₁) +
         factorTwoOddLowSynthesis (canonicalPhaseLowOddCoefficients c₂))
        (centeredRescale yoshidaA fun x ↦
          ((roTail : YoshidaClippedSmooth yoshidaA) x).re) a b =
      factorTwoEndpointLowTailMixed
          (factorTwoBoundaryCanonicalEvenLowProfile
            (canonicalPhaseLowEvenCoefficients c₁))
          (boundaryContinuousEvenProfile feTail)
          (factorTwoOddLowSynthesis
            (canonicalPhaseLowOddCoefficients c₁))
          (centeredRescale yoshidaA fun x ↦
            ((roTail : YoshidaClippedSmooth yoshidaA) x).re) a b +
        factorTwoEndpointLowTailMixed
          (factorTwoBoundaryCanonicalEvenLowProfile
            (canonicalPhaseLowEvenCoefficients c₂))
          (boundaryContinuousEvenProfile feTail)
          (factorTwoOddLowSynthesis
            (canonicalPhaseLowOddCoefficients c₂))
          (centeredRescale yoshidaA fun x ↦
            ((roTail : YoshidaClippedSmooth yoshidaA) x).re) a b := by
  let e₁ := canonicalPhaseLowEvenCoefficients c₁
  let e₂ := canonicalPhaseLowEvenCoefficients c₂
  let o₁ := canonicalPhaseLowOddCoefficients c₁
  let o₂ := canonicalPhaseLowOddCoefficients c₂
  have h := factorTwoEndpointLowTailMixed_boundaryContinuous_add_left
    (canonicalEvenRealLowPointwise e₁)
    (canonicalEvenRealLowPointwise e₂) feTail
    (canonicalOddRealLowPeriodicCore o₁)
    (canonicalOddRealLowPeriodicCore o₂) roTail
    (canonicalEvenRealLowPointwise_im_zero e₁)
    (canonicalEvenRealLowPointwise_im_zero e₂) heTailReal
    (canonicalOddRealLowPeriodicCore_im_zero o₁)
    (canonicalOddRealLowPeriodicCore_im_zero o₂) hoTailReal
    (canonicalOddRealLowPeriodicCore_left_endpoint o₁)
    (canonicalOddRealLowPeriodicCore_right_endpoint o₁)
    (canonicalOddRealLowPeriodicCore_left_endpoint o₂)
    (canonicalOddRealLowPeriodicCore_right_endpoint o₂)
    hoTailNeg hoTailPos a b
  simpa only [e₁, e₂, o₁, o₂,
    factorTwoBoundaryCanonicalEvenLowProfile,
    canonicalOddRealLowPeriodicCore_profile] using h

private theorem canonicalPhaseLowTailMixed_smul_profiles
    (c : FactorTwoPhaseLowIndex → ℝ) (r : ℝ)
    (feTail : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
    (roTail : YoshidaClippedPeriodicCore yoshidaA)
    (heTailReal : ∀ x : ℝ,
      ((feTail.1 : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoTailReal : ∀ x : ℝ,
      ((roTail : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hoTailNeg : (roTail : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hoTailPos : (roTail : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (a b : ℝ) :
    factorTwoEndpointLowTailMixed
        (r • factorTwoBoundaryCanonicalEvenLowProfile
          (canonicalPhaseLowEvenCoefficients c))
        (boundaryContinuousEvenProfile feTail)
        (r • factorTwoOddLowSynthesis
          (canonicalPhaseLowOddCoefficients c))
        (centeredRescale yoshidaA fun x ↦
          ((roTail : YoshidaClippedSmooth yoshidaA) x).re) a b =
      r * factorTwoEndpointLowTailMixed
        (factorTwoBoundaryCanonicalEvenLowProfile
          (canonicalPhaseLowEvenCoefficients c))
        (boundaryContinuousEvenProfile feTail)
        (factorTwoOddLowSynthesis
          (canonicalPhaseLowOddCoefficients c))
        (centeredRescale yoshidaA fun x ↦
          ((roTail : YoshidaClippedSmooth yoshidaA) x).re) a b := by
  let e := canonicalPhaseLowEvenCoefficients c
  let o := canonicalPhaseLowOddCoefficients c
  have h := factorTwoEndpointLowTailMixed_boundaryContinuous_smul_smul
    (canonicalEvenRealLowPointwise e) feTail
    (canonicalOddRealLowPeriodicCore o) roTail
    (canonicalEvenRealLowPointwise_im_zero e) heTailReal
    (canonicalOddRealLowPeriodicCore_im_zero o) hoTailReal
    (canonicalOddRealLowPeriodicCore_left_endpoint o)
    (canonicalOddRealLowPeriodicCore_right_endpoint o)
    hoTailNeg hoTailPos r 1 a b
  simpa only [e, o, one_smul, mul_one,
    factorTwoBoundaryCanonicalEvenLowProfile,
    canonicalOddRealLowPeriodicCore_profile] using h

/-- Physical low--tail mixed value on the real coordinate of a canonical
complex tail. -/
def canonicalPhaseLowTailRealMixed
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) : ℝ :=
  factorTwoEndpointLowTailMixed
    (factorTwoBoundaryCanonicalEvenLowProfile
      (canonicalPhaseLowEvenCoefficients c))
    (canonicalPhaseTailEvenRealProfile x)
    (factorTwoOddLowSynthesis (canonicalPhaseLowOddCoefficients c))
    (canonicalPhaseTailOddRealProfile x) a b

/-- Physical low--tail mixed value on the imaginary coordinate of a
canonical complex tail. -/
def canonicalPhaseLowTailImagMixed
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) : ℝ :=
  factorTwoEndpointLowTailMixed
    (factorTwoBoundaryCanonicalEvenLowProfile
      (canonicalPhaseLowEvenCoefficients c))
    (canonicalPhaseTailEvenImagProfile x)
    (factorTwoOddLowSynthesis (canonicalPhaseLowOddCoefficients c))
    (canonicalPhaseTailOddImagProfile x) a b

theorem canonicalPhaseLowTailRealMixed_add
    (c₁ c₂ : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseLowTailRealMixed (c₁ + c₂) x a b =
      canonicalPhaseLowTailRealMixed c₁ x a b +
        canonicalPhaseLowTailRealMixed c₂ x a b := by
  have he : canonicalPhaseLowEvenCoefficients (c₁ + c₂) =
      canonicalPhaseLowEvenCoefficients c₁ +
        canonicalPhaseLowEvenCoefficients c₂ := by
    ext i
    rfl
  have ho : canonicalPhaseLowOddCoefficients (c₁ + c₂) =
      canonicalPhaseLowOddCoefficients c₁ +
        canonicalPhaseLowOddCoefficients c₂ := by
    ext j
    rfl
  obtain ⟨hoNeg, hoPos⟩ := oddTenTail_endpoints_zero
    (oddTailRealPart x.snd.toV)
  have h := canonicalPhaseLowTailMixed_add_profiles c₁ c₂
    (canonicalEvenTailPointwise (evenTailRealPart x.fst.toV))
    (oddTailRealPart x.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).re :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth x.snd.toV t).re :
        ℝ) : ℂ)).im) = 0
      simp)
    hoNeg hoPos a b
  unfold canonicalPhaseLowTailRealMixed
  rw [he, ho, factorTwoBoundaryCanonicalEvenLowProfile_add,
    factorTwoOddLowSynthesis_add]
  simpa only [canonicalPhaseTailEvenRealProfile,
    boundaryCanonicalEvenTailProfile,
    canonicalPhaseTailOddRealProfile, canonicalOddTailProfile] using h

theorem canonicalPhaseLowTailImagMixed_add
    (c₁ c₂ : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseLowTailImagMixed (c₁ + c₂) x a b =
      canonicalPhaseLowTailImagMixed c₁ x a b +
        canonicalPhaseLowTailImagMixed c₂ x a b := by
  have he : canonicalPhaseLowEvenCoefficients (c₁ + c₂) =
      canonicalPhaseLowEvenCoefficients c₁ +
        canonicalPhaseLowEvenCoefficients c₂ := by
    ext i
    rfl
  have ho : canonicalPhaseLowOddCoefficients (c₁ + c₂) =
      canonicalPhaseLowOddCoefficients c₁ +
        canonicalPhaseLowOddCoefficients c₂ := by
    ext j
    rfl
  obtain ⟨hoNeg, hoPos⟩ := oddTenTail_endpoints_zero
    (oddTailImagPart x.snd.toV)
  have h := canonicalPhaseLowTailMixed_add_profiles c₁ c₂
    (canonicalEvenTailPointwise (evenTailImagPart x.fst.toV))
    (oddTailImagPart x.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
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
    hoNeg hoPos a b
  unfold canonicalPhaseLowTailImagMixed
  rw [he, ho, factorTwoBoundaryCanonicalEvenLowProfile_add,
    factorTwoOddLowSynthesis_add]
  simpa only [canonicalPhaseTailEvenImagProfile,
    boundaryCanonicalEvenTailProfile,
    canonicalPhaseTailOddImagProfile, canonicalOddTailProfile] using h

theorem canonicalPhaseLowTailRealMixed_smul
    (r : ℝ) (c : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseLowTailRealMixed (r • c) x a b =
      r * canonicalPhaseLowTailRealMixed c x a b := by
  have he : canonicalPhaseLowEvenCoefficients (r • c) =
      r • canonicalPhaseLowEvenCoefficients c := by
    ext i
    rfl
  have ho : canonicalPhaseLowOddCoefficients (r • c) =
      r • canonicalPhaseLowOddCoefficients c := by
    ext j
    rfl
  obtain ⟨hoNeg, hoPos⟩ := oddTenTail_endpoints_zero
    (oddTailRealPart x.snd.toV)
  have h := canonicalPhaseLowTailMixed_smul_profiles c r
    (canonicalEvenTailPointwise (evenTailRealPart x.fst.toV))
    (oddTailRealPart x.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
    (by
      intro t
      change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).re :
        ℝ) : ℂ)).im) = 0
      simp)
    (by
      intro t
      change (((((oddTenTailToClippedSmooth x.snd.toV t).re :
        ℝ) : ℂ)).im) = 0
      simp)
    hoNeg hoPos a b
  unfold canonicalPhaseLowTailRealMixed
  rw [he, ho, factorTwoBoundaryCanonicalEvenLowProfile_smul,
    factorTwoOddLowSynthesis_smul]
  simpa only [canonicalPhaseTailEvenRealProfile,
    boundaryCanonicalEvenTailProfile,
    canonicalPhaseTailOddRealProfile, canonicalOddTailProfile] using h

theorem canonicalPhaseLowTailImagMixed_smul
    (r : ℝ) (c : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseLowTailImagMixed (r • c) x a b =
      r * canonicalPhaseLowTailImagMixed c x a b := by
  have he : canonicalPhaseLowEvenCoefficients (r • c) =
      r • canonicalPhaseLowEvenCoefficients c := by
    ext i
    rfl
  have ho : canonicalPhaseLowOddCoefficients (r • c) =
      r • canonicalPhaseLowOddCoefficients c := by
    ext j
    rfl
  obtain ⟨hoNeg, hoPos⟩ := oddTenTail_endpoints_zero
    (oddTailImagPart x.snd.toV)
  have h := canonicalPhaseLowTailMixed_smul_profiles c r
    (canonicalEvenTailPointwise (evenTailImagPart x.fst.toV))
    (oddTailImagPart x.snd.toV : YoshidaClippedPeriodicCore yoshidaA)
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
    hoNeg hoPos a b
  unfold canonicalPhaseLowTailImagMixed
  rw [he, ho, factorTwoBoundaryCanonicalEvenLowProfile_smul,
    factorTwoOddLowSynthesis_smul]
  simpa only [canonicalPhaseTailEvenImagProfile,
    boundaryCanonicalEvenTailProfile,
    canonicalPhaseTailOddImagProfile, canonicalOddTailProfile] using h

/-- The physical real-coordinate low--tail mixed value as a linear map of
all `210` packed low coefficients. -/
def canonicalPhaseLowTailRealLinear
    (x : CanonicalPhaseTailCore) (a b : ℝ) :
    (FactorTwoPhaseLowIndex → ℝ) →ₗ[ℝ] ℝ where
  toFun c := canonicalPhaseLowTailRealMixed c x a b
  map_add' c₁ c₂ := canonicalPhaseLowTailRealMixed_add c₁ c₂ x a b
  map_smul' r c := by
    simpa only [smul_eq_mul] using
      canonicalPhaseLowTailRealMixed_smul r c x a b

/-- The physical imaginary-coordinate low--tail mixed value as a linear map
of all `210` packed low coefficients. -/
def canonicalPhaseLowTailImagLinear
    (x : CanonicalPhaseTailCore) (a b : ℝ) :
    (FactorTwoPhaseLowIndex → ℝ) →ₗ[ℝ] ℝ where
  toFun c := canonicalPhaseLowTailImagMixed c x a b
  map_add' c₁ c₂ := canonicalPhaseLowTailImagMixed_add c₁ c₂ x a b
  map_smul' r c := by
    simpa only [smul_eq_mul] using
      canonicalPhaseLowTailImagMixed_smul r c x a b

@[simp] theorem canonicalPhaseLowEvenCoefficients_single
    (k : FactorTwoPhaseLowIndex) :
    canonicalPhaseLowEvenCoefficients (Pi.single k 1) =
      canonicalLowEvenSelector k := by
  ext i
  cases k with
  | inl j =>
      by_cases h : j = i <;>
        simp [canonicalPhaseLowEvenCoefficients, canonicalLowEvenSelector,
          Pi.single_apply, h]
  | inr j =>
      simp [canonicalPhaseLowEvenCoefficients, canonicalLowEvenSelector]

@[simp] theorem canonicalPhaseLowOddCoefficients_single
    (k : FactorTwoPhaseLowIndex) :
    canonicalPhaseLowOddCoefficients (Pi.single k 1) =
      canonicalLowOddSelector k := by
  ext j
  cases k with
  | inl i =>
      simp [canonicalPhaseLowOddCoefficients, canonicalLowOddSelector]
  | inr i =>
      by_cases h : i = j <;>
        simp [canonicalPhaseLowOddCoefficients, canonicalLowOddSelector,
          Pi.single_apply, h]

private theorem canonicalEvenRealLowPointwise_single
    (i : YoshidaEvenIndex) :
    canonicalEvenRealLowPointwise (Pi.single i 1) =
      canonicalEvenLowModePointwise i := by
  apply Subtype.ext
  change canonicalEvenRealLowPeriodicCore (Pi.single i 1) =
    canonicalEvenLowModePeriodicCore i
  classical
  unfold canonicalEvenRealLowPeriodicCore
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

@[simp] theorem factorTwoBoundaryCanonicalEvenLowProfile_selector
    (k : FactorTwoPhaseLowIndex) :
    factorTwoBoundaryCanonicalEvenLowProfile (canonicalLowEvenSelector k) =
      canonicalPhaseLowBasisEvenProfile k := by
  cases k with
  | inl i =>
      unfold canonicalLowEvenSelector factorTwoBoundaryCanonicalEvenLowProfile
        canonicalPhaseLowBasisEvenProfile
      rw [canonicalEvenRealLowPointwise_single]
  | inr j =>
      unfold canonicalLowEvenSelector factorTwoBoundaryCanonicalEvenLowProfile
        canonicalPhaseLowBasisEvenProfile
      have hzero : canonicalEvenRealLowPointwise
          (0 : YoshidaEvenIndex → ℝ) = 0 := by
        apply Subtype.ext
        change canonicalEvenRealLowPeriodicCore
          (0 : YoshidaEvenIndex → ℝ) = 0
        classical
        simp [canonicalEvenRealLowPeriodicCore]
      rw [hzero, boundaryContinuousEvenProfile_zero]

@[simp] theorem factorTwoOddLowSynthesis_selector
    (k : FactorTwoPhaseLowIndex) :
    factorTwoOddLowSynthesis (canonicalLowOddSelector k) =
      canonicalPhaseLowBasisOddProfile k := by
  classical
  cases k with
  | inl i =>
      simp [canonicalLowOddSelector, canonicalPhaseLowBasisOddProfile,
        factorTwoOddLowSynthesis]
  | inr j =>
      simp [canonicalLowOddSelector, canonicalPhaseLowBasisOddProfile,
        factorTwoOddLowSynthesis, Pi.single_apply]

@[simp] theorem canonicalPhaseLowTailRealLinear_single
    (k : FactorTwoPhaseLowIndex) (x : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseLowTailRealLinear x a b (Pi.single k 1) =
      canonicalPhaseLowBasisTailRealMixedValue k x a b := by
  change canonicalPhaseLowTailRealMixed (Pi.single k 1) x a b = _
  unfold canonicalPhaseLowTailRealMixed
    canonicalPhaseLowBasisTailRealMixedValue
  rw [canonicalPhaseLowEvenCoefficients_single,
    canonicalPhaseLowOddCoefficients_single,
    factorTwoBoundaryCanonicalEvenLowProfile_selector,
    factorTwoOddLowSynthesis_selector]

@[simp] theorem canonicalPhaseLowTailImagLinear_single
    (k : FactorTwoPhaseLowIndex) (x : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseLowTailImagLinear x a b (Pi.single k 1) =
      canonicalPhaseLowBasisTailImagMixedValue k x a b := by
  change canonicalPhaseLowTailImagMixed (Pi.single k 1) x a b = _
  unfold canonicalPhaseLowTailImagMixed
    canonicalPhaseLowBasisTailImagMixedValue
  rw [canonicalPhaseLowEvenCoefficients_single,
    canonicalPhaseLowOddCoefficients_single,
    factorTwoBoundaryCanonicalEvenLowProfile_selector,
    factorTwoOddLowSynthesis_selector]

/-- Arbitrary real-coordinate physical low--tail mixing is the exact basis
sum of the canonical mixed values. -/
theorem canonicalPhaseLowTailRealMixed_eq_sum
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) :
    canonicalPhaseLowTailRealMixed c x a b =
      ∑ k, c k * canonicalPhaseLowBasisTailRealMixedValue k x a b := by
  classical
  have hc : c = ∑ k, c k •
      (Pi.single k 1 : FactorTwoPhaseLowIndex → ℝ) :=
    pi_eq_sum_univ' c
  change canonicalPhaseLowTailRealLinear x a b c = _
  calc
    canonicalPhaseLowTailRealLinear x a b c =
        canonicalPhaseLowTailRealLinear x a b
          (∑ k, c k •
            (Pi.single k 1 : FactorTwoPhaseLowIndex → ℝ)) :=
      congrArg (canonicalPhaseLowTailRealLinear x a b) hc
    _ = ∑ k, canonicalPhaseLowTailRealLinear x a b
        (c k • (Pi.single k 1 : FactorTwoPhaseLowIndex → ℝ)) := by
      rw [map_sum]
    _ = ∑ k, c k * canonicalPhaseLowBasisTailRealMixedValue k x a b := by
      apply Finset.sum_congr rfl
      intro k _
      rw [map_smul, canonicalPhaseLowTailRealLinear_single]
      rfl

/-- Arbitrary imaginary-coordinate physical low--tail mixing is the exact
basis sum of the canonical mixed values. -/
theorem canonicalPhaseLowTailImagMixed_eq_sum
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) :
    canonicalPhaseLowTailImagMixed c x a b =
      ∑ k, c k * canonicalPhaseLowBasisTailImagMixedValue k x a b := by
  classical
  have hc : c = ∑ k, c k •
      (Pi.single k 1 : FactorTwoPhaseLowIndex → ℝ) :=
    pi_eq_sum_univ' c
  change canonicalPhaseLowTailImagLinear x a b c = _
  calc
    canonicalPhaseLowTailImagLinear x a b c =
        canonicalPhaseLowTailImagLinear x a b
          (∑ k, c k •
            (Pi.single k 1 : FactorTwoPhaseLowIndex → ℝ)) :=
      congrArg (canonicalPhaseLowTailImagLinear x a b) hc
    _ = ∑ k, canonicalPhaseLowTailImagLinear x a b
        (c k • (Pi.single k 1 : FactorTwoPhaseLowIndex → ℝ)) := by
      rw [map_sum]
    _ = ∑ k, c k * canonicalPhaseLowBasisTailImagMixedValue k x a b := by
      apply Finset.sum_congr rfl
      intro k _
      rw [map_smul, canonicalPhaseLowTailImagLinear_single]
      rfl

/-- On the dense canonical tail core, the physical real-coordinate mixed
block is exactly the sum of the completed basis functionals. -/
theorem canonicalPhaseLowTailRealMixed_eq_completed_sum
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    canonicalPhaseLowTailRealMixed c x a b =
      ∑ k, c k * completedCanonicalPhaseLowBasisTailRealFunctional
        k a b hphase (x : CanonicalPhaseTailCompletion) := by
  rw [canonicalPhaseLowTailRealMixed_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [completedCanonicalPhaseLowBasisTailRealFunctional_coe]

/-- On the dense canonical tail core, the physical imaginary-coordinate
mixed block is exactly the sum of the completed basis functionals. -/
theorem canonicalPhaseLowTailImagMixed_eq_completed_sum
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    canonicalPhaseLowTailImagMixed c x a b =
      ∑ k, c k * completedCanonicalPhaseLowBasisTailImagFunctional
        k a b hphase (x : CanonicalPhaseTailCompletion) := by
  rw [canonicalPhaseLowTailImagMixed_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [completedCanonicalPhaseLowBasisTailImagFunctional_coe]

@[simp] theorem factorTwoPhaseLowCoefficients_unpacked
    (c : FactorTwoPhaseLowIndex → ℝ) :
    factorTwoPhaseLowCoefficients
        (canonicalPhaseLowEvenCoefficients c)
        (canonicalPhaseLowOddCoefficients c) = c := by
  ext k
  cases k <;> rfl

/-- The duplicated canonical low matrix is exactly the sum of the real and
imaginary low quadratics. -/
theorem canonicalPhaseLowRealImagMatrix_quadratic
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ) (a b : ℝ) :
    let d := canonicalPhaseLowRealImagCoefficients cReal cImag
    d ⬝ᵥ (canonicalPhaseLowRealImagMatrix a b *ᵥ d) =
      cReal ⬝ᵥ (canonicalPhaseLowMatrix a b *ᵥ cReal) +
        cImag ⬝ᵥ (canonicalPhaseLowMatrix a b *ᵥ cImag) := by
  classical
  dsimp only
  simp only [dotProduct, mulVec, canonicalPhaseLowRealImagCoefficients,
    canonicalPhaseLowRealImagMatrix, duplicatePhaseLowMatrix]
  simp_rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add]

/-- The doubled mixed-functional sum splits into the literal real and
imaginary basis sums. -/
theorem completedCanonicalPhaseLowRealImagFunctional_sum
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    let d := canonicalPhaseLowRealImagCoefficients cReal cImag
    ∑ p, d p * completedCanonicalPhaseLowRealImagFunctional
        a b hphase p (x : CanonicalPhaseTailCompletion) =
      (∑ k, cReal k *
        completedCanonicalPhaseLowBasisTailRealFunctional
          k a b hphase (x : CanonicalPhaseTailCompletion)) +
      ∑ k, cImag k *
        completedCanonicalPhaseLowBasisTailImagFunctional
          k a b hphase (x : CanonicalPhaseTailCompletion) := by
  classical
  dsimp only
  rw [Fintype.sum_sum_type]
  rfl

/-- The literal sum of the real- and imaginary-coordinate full phases for
one canonical low block plus one canonical complex tail. -/
def canonicalPhasePhysicalLowTailValue
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ) : ℝ :=
  factorTwoEndpointChannelPhase
      (factorTwoBoundaryCanonicalEvenLowProfile
          (canonicalPhaseLowEvenCoefficients cReal) +
        canonicalPhaseTailEvenRealProfile x)
      (factorTwoOddLowSynthesis
          (canonicalPhaseLowOddCoefficients cReal) +
        canonicalPhaseTailOddRealProfile x) a b +
    factorTwoEndpointChannelPhase
      (factorTwoBoundaryCanonicalEvenLowProfile
          (canonicalPhaseLowEvenCoefficients cImag) +
        canonicalPhaseTailEvenImagProfile x)
      (factorTwoOddLowSynthesis
          (canonicalPhaseLowOddCoefficients cImag) +
        canonicalPhaseTailOddImagProfile x) a b

/-- The assembled finite-low, mixed, and completed-tail quadratic before
completion of the square. -/
def canonicalPhaseLowTailSchurQuadratic
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) : ℝ :=
  let d := canonicalPhaseLowRealImagCoefficients cReal cImag
  d ⬝ᵥ (canonicalPhaseLowRealImagMatrix a b *ᵥ d) +
    2 * ∑ p, d p *
      completedCanonicalPhaseLowRealImagFunctional a b hphase p
        (x : CanonicalPhaseTailCompletion) +
    completedCanonicalPhaseTailBilinear a b hphase
      (x : CanonicalPhaseTailCompletion)
      (x : CanonicalPhaseTailCompletion)

/-- The exact physical-to-Schur assembly proposition, packaged opaquely so
downstream elaboration need not unfold the large analytic expressions. -/
def CanonicalPhasePhysicalLowTailAssembly
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) : Prop :=
  canonicalPhasePhysicalLowTailValue cReal cImag x a b =
    canonicalPhaseLowTailSchurQuadratic cReal cImag x a b hphase

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailAssemblyStructural
