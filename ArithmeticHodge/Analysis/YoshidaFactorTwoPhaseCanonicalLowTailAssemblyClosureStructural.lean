import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailAssemblyStructural

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailAssemblyClosureStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseTailRealImagStructural

/-- The literal full phase of the real low/tail coordinate. -/
def canonicalPhasePhysicalRealLowTailValue
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) : ℝ :=
  factorTwoEndpointChannelPhase
    (factorTwoBoundaryCanonicalEvenLowProfile
        (canonicalPhaseLowEvenCoefficients c) +
      canonicalPhaseTailEvenRealProfile x)
    (factorTwoOddLowSynthesis (canonicalPhaseLowOddCoefficients c) +
      canonicalPhaseTailOddRealProfile x) a b

/-- Its exact finite-low, completed-mixed, and pure-tail expansion. -/
def canonicalPhaseRealLowTailExpandedValue
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) : ℝ :=
  c ⬝ᵥ (canonicalPhaseLowMatrix a b *ᵥ c) +
    2 * ∑ k, c k * completedCanonicalPhaseLowBasisTailRealFunctional
      k a b hphase (x : CanonicalPhaseTailCompletion) +
    factorTwoEndpointChannelPhase
      (canonicalPhaseTailEvenRealProfile x)
      (canonicalPhaseTailOddRealProfile x) a b

def CanonicalPhasePhysicalRealLowTailAssembly
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) : Prop :=
  canonicalPhasePhysicalRealLowTailValue c x a b =
    canonicalPhaseRealLowTailExpandedValue c x a b hphase

/-- The real coordinate of the physical low-plus-tail phase has exactly the
completed functional expansion. -/
theorem canonicalPhasePhysicalRealLowTailValue_eq_expanded
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    CanonicalPhasePhysicalRealLowTailAssembly c x a b hphase := by
  unfold CanonicalPhasePhysicalRealLowTailAssembly
    canonicalPhasePhysicalRealLowTailValue
    canonicalPhaseRealLowTailExpandedValue
  rw [factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
    (factorTwoBoundaryCanonicalEvenLowProfile
      (canonicalPhaseLowEvenCoefficients c))
    (canonicalPhaseTailEvenRealProfile x)
    (factorTwoOddLowSynthesis (canonicalPhaseLowOddCoefficients c))
    (canonicalPhaseTailOddRealProfile x)
    (continuous_factorTwoBoundaryCanonicalEvenLowProfile
      (canonicalPhaseLowEvenCoefficients c))
    (continuous_boundaryCanonicalEvenTailProfile
      (evenTailRealPart x.fst.toV))
    (continuous_factorTwoOddLowSynthesis
      (canonicalPhaseLowOddCoefficients c))
    (continuous_canonicalOddTailProfile (oddTailRealPart x.snd.toV)) a b,
    factorTwoBoundaryCanonicalFiniteLowPhaseMatrix_represents,
    factorTwoPhaseLowCoefficients_unpacked]
  change c ⬝ᵥ (canonicalPhaseLowMatrix a b *ᵥ c) +
      2 * canonicalPhaseLowTailRealMixed c x a b +
      factorTwoEndpointChannelPhase
        (canonicalPhaseTailEvenRealProfile x)
        (canonicalPhaseTailOddRealProfile x) a b = _
  rw [canonicalPhaseLowTailRealMixed_eq_completed_sum]

/-- The literal full phase of the imaginary low/tail coordinate. -/
def canonicalPhasePhysicalImagLowTailValue
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) : ℝ :=
  factorTwoEndpointChannelPhase
    (factorTwoBoundaryCanonicalEvenLowProfile
        (canonicalPhaseLowEvenCoefficients c) +
      canonicalPhaseTailEvenImagProfile x)
    (factorTwoOddLowSynthesis (canonicalPhaseLowOddCoefficients c) +
      canonicalPhaseTailOddImagProfile x) a b

/-- Its exact finite-low, completed-mixed, and pure-tail expansion. -/
def canonicalPhaseImagLowTailExpandedValue
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) : ℝ :=
  c ⬝ᵥ (canonicalPhaseLowMatrix a b *ᵥ c) +
    2 * ∑ k, c k * completedCanonicalPhaseLowBasisTailImagFunctional
      k a b hphase (x : CanonicalPhaseTailCompletion) +
    factorTwoEndpointChannelPhase
      (canonicalPhaseTailEvenImagProfile x)
      (canonicalPhaseTailOddImagProfile x) a b

def CanonicalPhasePhysicalImagLowTailAssembly
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) : Prop :=
  canonicalPhasePhysicalImagLowTailValue c x a b =
    canonicalPhaseImagLowTailExpandedValue c x a b hphase

/-- The imaginary coordinate of the physical low-plus-tail phase has exactly
the completed functional expansion. -/
theorem canonicalPhasePhysicalImagLowTailValue_eq_expanded
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    CanonicalPhasePhysicalImagLowTailAssembly c x a b hphase := by
  unfold CanonicalPhasePhysicalImagLowTailAssembly
    canonicalPhasePhysicalImagLowTailValue
    canonicalPhaseImagLowTailExpandedValue
  rw [factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
    (factorTwoBoundaryCanonicalEvenLowProfile
      (canonicalPhaseLowEvenCoefficients c))
    (canonicalPhaseTailEvenImagProfile x)
    (factorTwoOddLowSynthesis (canonicalPhaseLowOddCoefficients c))
    (canonicalPhaseTailOddImagProfile x)
    (continuous_factorTwoBoundaryCanonicalEvenLowProfile
      (canonicalPhaseLowEvenCoefficients c))
    (continuous_boundaryCanonicalEvenTailProfile
      (evenTailImagPart x.fst.toV))
    (continuous_factorTwoOddLowSynthesis
      (canonicalPhaseLowOddCoefficients c))
    (continuous_canonicalOddTailProfile (oddTailImagPart x.snd.toV)) a b,
    factorTwoBoundaryCanonicalFiniteLowPhaseMatrix_represents,
    factorTwoPhaseLowCoefficients_unpacked]
  change c ⬝ᵥ (canonicalPhaseLowMatrix a b *ᵥ c) +
      2 * canonicalPhaseLowTailImagMixed c x a b +
      factorTwoEndpointChannelPhase
        (canonicalPhaseTailEvenImagProfile x)
        (canonicalPhaseTailOddImagProfile x) a b = _
  rw [canonicalPhaseLowTailImagMixed_eq_completed_sum]

/-- The completed tail diagonal is exactly the sum of its physical real and
imaginary channel phases on the dense core. -/
theorem completedCanonicalPhaseTailBilinear_coe_self_eq_physical
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    completedCanonicalPhaseTailBilinear a b hphase
        (x : CanonicalPhaseTailCompletion)
        (x : CanonicalPhaseTailCompletion) =
      factorTwoEndpointChannelPhase
          (canonicalPhaseTailEvenRealProfile x)
          (canonicalPhaseTailOddRealProfile x) a b +
        factorTwoEndpointChannelPhase
          (canonicalPhaseTailEvenImagProfile x)
          (canonicalPhaseTailOddImagProfile x) a b := by
  rw [completedCanonicalPhaseTailBilinear_coe_coe,
    canonicalPhaseTailCoreBilinearValue_self]
  rfl

def CanonicalPhasePhysicalCoordinateSplit
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ) : Prop :=
  canonicalPhasePhysicalLowTailValue cReal cImag x a b =
    canonicalPhasePhysicalRealLowTailValue cReal x a b +
      canonicalPhasePhysicalImagLowTailValue cImag x a b

theorem canonicalPhasePhysicalLowTailValue_eq_coordinate_sum
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ) :
    CanonicalPhasePhysicalCoordinateSplit cReal cImag x a b := by
  unfold CanonicalPhasePhysicalCoordinateSplit
    canonicalPhasePhysicalLowTailValue
    canonicalPhasePhysicalRealLowTailValue
    canonicalPhasePhysicalImagLowTailValue
  rfl

def CanonicalPhaseExpandedCoordinateAssembly
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) : Prop :=
  canonicalPhasePhysicalRealLowTailValue cReal x a b +
      canonicalPhasePhysicalImagLowTailValue cImag x a b =
    canonicalPhaseRealLowTailExpandedValue cReal x a b hphase +
      canonicalPhaseImagLowTailExpandedValue cImag x a b hphase

theorem canonicalPhasePhysicalCoordinateSum_eq_expanded
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    CanonicalPhaseExpandedCoordinateAssembly
      cReal cImag x a b hphase := by
  have hr := canonicalPhasePhysicalRealLowTailValue_eq_expanded
    cReal x a b hphase
  have hi := canonicalPhasePhysicalImagLowTailValue_eq_expanded
    cImag x a b hphase
  unfold CanonicalPhasePhysicalRealLowTailAssembly at hr
  unfold CanonicalPhasePhysicalImagLowTailAssembly at hi
  unfold CanonicalPhaseExpandedCoordinateAssembly
  rw [hr, hi]

def CanonicalPhaseSchurCoordinateSplit
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) : Prop :=
  canonicalPhaseLowTailSchurQuadratic cReal cImag x a b hphase =
    canonicalPhaseRealLowTailExpandedValue cReal x a b hphase +
      canonicalPhaseImagLowTailExpandedValue cImag x a b hphase

theorem canonicalPhaseLowTailSchurQuadratic_eq_coordinate_sum
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    CanonicalPhaseSchurCoordinateSplit cReal cImag x a b hphase := by
  unfold CanonicalPhaseSchurCoordinateSplit
    canonicalPhaseLowTailSchurQuadratic
    canonicalPhaseRealLowTailExpandedValue
    canonicalPhaseImagLowTailExpandedValue
  dsimp only
  rw [canonicalPhaseLowRealImagMatrix_quadratic,
    completedCanonicalPhaseLowRealImagFunctional_sum,
    completedCanonicalPhaseTailBilinear_coe_self_eq_physical]
  ring

/-- Exact physical assembly: the two real coordinate phases of the actual
low-plus-tail profiles equal the `420`-coordinate low quadratic, twice its
completed mixed functional, and the completed coercive tail diagonal. -/
theorem canonicalPhasePhysicalLowTailValue_eq_schurQuadratic
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    CanonicalPhasePhysicalLowTailAssembly cReal cImag x a b hphase := by
  have hPhysical := canonicalPhasePhysicalLowTailValue_eq_coordinate_sum
    cReal cImag x a b
  have hExpanded := canonicalPhasePhysicalCoordinateSum_eq_expanded
    cReal cImag x a b hphase
  have hSchur := canonicalPhaseLowTailSchurQuadratic_eq_coordinate_sum
    cReal cImag x a b hphase
  unfold CanonicalPhasePhysicalCoordinateSplit at hPhysical
  unfold CanonicalPhaseExpandedCoordinateAssembly at hExpanded
  unfold CanonicalPhaseSchurCoordinateSplit at hSchur
  unfold CanonicalPhasePhysicalLowTailAssembly
  exact hPhysical.trans (hExpanded.trans hSchur.symm)

/-- The physical full phase after completing the shared real/imaginary tail
square. -/
def CanonicalPhasePhysicalLowTailCompletedSquare
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) : Prop :=
  let d := canonicalPhaseLowRealImagCoefficients cReal cImag
  canonicalPhasePhysicalLowTailValue cReal cImag x a b =
    d ⬝ᵥ (completedCanonicalPhaseLowTailCorrectedGram a b hphase *ᵥ d) +
      completedCanonicalPhaseTailBilinear a b hphase
        ((x : CanonicalPhaseTailCompletion) +
          ∑ p, d p • canonicalPhaseLowRealImagRieszCorrection a b hphase p)
        ((x : CanonicalPhaseTailCompletion) +
          ∑ p, d p • canonicalPhaseLowRealImagRieszCorrection a b hphase p)

/-- Exact completion of the square for the literal physical low-plus-tail
profiles.  No mixed term or real--imaginary correction block is discarded. -/
theorem canonicalPhasePhysicalLowTailValue_eq_completedSquare
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    CanonicalPhasePhysicalLowTailCompletedSquare
      cReal cImag x a b hphase := by
  have hPhysical := canonicalPhasePhysicalLowTailValue_eq_schurQuadratic
    cReal cImag x a b hphase
  unfold CanonicalPhasePhysicalLowTailAssembly at hPhysical
  have hSquare := completedCanonicalPhaseLowTail_complete_square
    a b hphase (canonicalPhaseLowRealImagCoefficients cReal cImag)
      (x : CanonicalPhaseTailCompletion)
  change canonicalPhaseLowTailSchurQuadratic cReal cImag x a b hphase = _
    at hSquare
  unfold CanonicalPhasePhysicalLowTailCompletedSquare
  dsimp only
  exact hPhysical.trans hSquare

def CanonicalPhasePhysicalLowTailNonnegative
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ) : Prop :=
  0 ≤ canonicalPhasePhysicalLowTailValue cReal cImag x a b

/-- The exact remaining finite Schur obligation: PSD of the corrected
`420 × 420` Gram implies nonnegativity of every assembled physical
canonical low-plus-tail profile at the fixed disk phase. -/
theorem canonicalPhasePhysicalLowTailValue_nonneg_of_correctedGram_posSemidef
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hG : Matrix.PosSemidef
      (completedCanonicalPhaseLowTailCorrectedGram a b hphase)) :
    CanonicalPhasePhysicalLowTailNonnegative cReal cImag x a b := by
  have hPhysical := canonicalPhasePhysicalLowTailValue_eq_schurQuadratic
    cReal cImag x a b hphase
  unfold CanonicalPhasePhysicalLowTailAssembly at hPhysical
  have hnonneg :=
    completedCanonicalPhaseLowTail_nonneg_of_correctedGram_posSemidef
      a b hphase hG
        (canonicalPhaseLowRealImagCoefficients cReal cImag)
        (x : CanonicalPhaseTailCompletion)
  change 0 ≤ canonicalPhaseLowTailSchurQuadratic
    cReal cImag x a b hphase at hnonneg
  unfold CanonicalPhasePhysicalLowTailNonnegative
  rw [hPhysical]
  exact hnonneg

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailAssemblyClosureStructural
