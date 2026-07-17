import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailCleanRowsStructural

noncomputable section

open ArithmeticHodge.Analysis
open FormSpace
open UnitIntervalLogEnergyAffine
open YoshidaCoercivityNumerics
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaRegularKernelSchur
open YoshidaEvenTailLowFunctional
open YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
open YoshidaFactorTwoPhaseBoundaryContinuousCleanPolarizationStructural
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseCleanPolarizationCritical
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddRealDecomposition
open YoshidaFactorTwoPhaseTailRealImagStructural
open YoshidaEvenHomogeneousCoercivity
open YoshidaOddHomogeneousCoercivity
open YoshidaOddModeRegularity
open YoshidaOddTailLowFunctional
open YoshidaWeightedTailBounds

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

@[simp] private theorem yoshidaEndpointOddCleanQuadratic_zero :
    yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
  unfold yoshidaEndpointOddCleanQuadratic centeredRawLogEnergy
    yoshidaEndpointRegularQuadratic yoshidaEndpointHyperbolicQuadratic
  simp

@[simp] private theorem factorTwoCenteredCleanPolarization_zero_left
    (u : ℝ → ℝ) : factorTwoCenteredCleanPolarization 0 u = 0 := by
  unfold factorTwoCenteredCleanPolarization
  rw [zero_add, yoshidaEndpointOddCleanQuadratic_zero]
  ring

/-- Clean part of one canonical real low-to-tail row. -/
def canonicalPhaseLowBasisTailRealCleanValue
    (k : FactorTwoPhaseLowIndex) (x : CanonicalPhaseTailCore) : ℝ :=
  factorTwoCenteredCleanPolarization
    (canonicalPhaseLowBasisEvenProfile k)
    (canonicalPhaseTailEvenRealProfile x) +
  factorTwoCenteredCleanPolarization
    (canonicalPhaseLowBasisOddProfile k)
    (canonicalPhaseTailOddRealProfile x)

private theorem norm_evenTailRealPart_le_core
    (x : CanonicalPhaseTailCore) :
    ‖(FormSpace.of (evenTailRealPart x.fst.toV) :
      EvenPhaseTailFormSpace)‖ ≤ ‖x‖ := by
  have hsplit := evenFormSpace_norm_sq_eq_real_add_imag x.fst
  have hsq :
      ‖(FormSpace.of (evenTailRealPart x.fst.toV) :
        EvenPhaseTailFormSpace)‖ ^ 2 ≤ ‖x.fst‖ ^ 2 := by
    nlinarith [sq_nonneg
      ‖(FormSpace.of (evenTailImagPart x.fst.toV) :
        EvenPhaseTailFormSpace)‖]
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq).trans
    (WithLp.norm_fst_le EvenPhaseTailFormSpace x)

private theorem norm_oddTailRealPart_le_core
    (x : CanonicalPhaseTailCore) :
    ‖(FormSpace.of (oddTailRealPart x.snd.toV) :
      OddPhaseTailFormSpace)‖ ≤ ‖x‖ := by
  have hsplit := oddFormSpace_norm_sq_eq_real_add_imag x.snd
  have hsq :
      ‖(FormSpace.of (oddTailRealPart x.snd.toV) :
        OddPhaseTailFormSpace)‖ ^ 2 ≤ ‖x.snd‖ ^ 2 := by
    nlinarith [sq_nonneg
      ‖(FormSpace.of (oddTailImagPart x.snd.toV) :
        OddPhaseTailFormSpace)‖]
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq).trans
    (WithLp.norm_snd_le EvenPhaseTailFormSpace x)

/-- The exact cutoff-`199` Parseval estimate gives a sharp clean-row bound
for every retained even mode. -/
theorem canonicalPhaseEvenLowBasisTailRealCleanValue_sq_le
    (i : YoshidaEvenIndex) (x : CanonicalPhaseTailCore) :
    canonicalPhaseLowBasisTailRealCleanValue (Sum.inl i) x ^ 2 ≤
      (1 / (2000 * yoshidaA ^ 2) : ℝ) * ‖x‖ ^ 2 := by
  let e := evenTailRealPart x.fst.toV
  let z : ℂ := yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
    (yoshidaClippedEvenLowMode yoshidaA i)
    (evenOneNinetyNineTailToClippedSmooth e)
  have hreal : ∀ t : ℝ,
      (evenOneNinetyNineTailToClippedSmooth e t).im = 0 := by
    intro t
    simp only [e, evenTailRealPart_apply, Complex.ofReal_im]
  have hlowReal : ∀ t : ℝ,
      ((((canonicalEvenLowModePointwise i).1 :
        YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) t).im = 0 := by
    intro t
    simpa only [canonicalEvenLowModePointwise,
      canonicalEvenLowModePeriodicCore_toSmooth] using
        evenLowMode_im_zero i t
  have hbridge :=
    factorTwoCenteredCleanPolarization_boundaryContinuous_eq_clippedCriticalForm_re_div
      (canonicalEvenLowModePointwise i)
      (canonicalEvenTailPointwise e) hlowReal hreal
  have htail := evenTailLowFunctional_sq_le_formNorm
    (FormSpace.of e : EvenPhaseTailFormSpace) i
  have hconj := yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos
    (evenOneNinetyNineTailToClippedSmooth e)
    (yoshidaClippedEvenLowMode yoshidaA i)
  have hz : Complex.normSq z ≤
      (1 / 2000 : ℝ) *
        ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    have htail' := htail
    rw [← hconj] at htail'
    simpa only [z, norm_star] using htail'
  have hrealSq : z.re ^ 2 ≤ Complex.normSq z := by
    simpa only [pow_two] using Complex.re_sq_le_normSq z
  have heNorm := norm_evenTailRealPart_le_core x
  change factorTwoCenteredCleanPolarization
      (boundaryContinuousEvenProfile (canonicalEvenLowModePointwise i))
      (boundaryCanonicalEvenTailProfile e) = z.re / yoshidaA at hbridge
  unfold canonicalPhaseLowBasisTailRealCleanValue
    canonicalPhaseLowBasisEvenProfile canonicalPhaseLowBasisOddProfile
    canonicalPhaseTailEvenRealProfile
  simp only [factorTwoCenteredCleanPolarization_zero_left]
  rw [hbridge]
  simp only [add_zero]
  have hA2 : 0 < yoshidaA ^ 2 := sq_pos_of_pos yoshidaA_pos
  rw [div_pow]
  calc
    z.re ^ 2 / yoshidaA ^ 2 ≤ Complex.normSq z / yoshidaA ^ 2 :=
      div_le_div_of_nonneg_right hrealSq hA2.le
    _ ≤ ((1 / 2000 : ℝ) *
          ‖(FormSpace.of e : EvenPhaseTailFormSpace)‖ ^ 2) /
        yoshidaA ^ 2 := div_le_div_of_nonneg_right hz hA2.le
    _ ≤ ((1 / 2000 : ℝ) * ‖x‖ ^ 2) / yoshidaA ^ 2 := by
      gcongr
    _ = (1 / (2000 * yoshidaA ^ 2) : ℝ) * ‖x‖ ^ 2 := by ring

/-- The exact cutoff-`10` Parseval estimate gives the corresponding clean-row
bound for every retained odd mode. -/
theorem canonicalPhaseOddLowBasisTailRealCleanValue_sq_le
    (j : YoshidaOddIndex) (x : CanonicalPhaseTailCore) :
    canonicalPhaseLowBasisTailRealCleanValue (Sum.inr j) x ^ 2 ≤
      (1 / (40 * yoshidaA ^ 2) : ℝ) * ‖x‖ ^ 2 := by
  let o := oddTailRealPart x.snd.toV
  let r : YoshidaClippedPeriodicCore yoshidaA :=
    canonicalOddLowModePeriodicCore j
  let z : ℂ := yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
    (r : YoshidaClippedSmooth yoshidaA)
    (oddTenTailToClippedSmooth o)
  have hreal : ∀ t : ℝ, (oddTenTailToClippedSmooth o t).im = 0 := by
    intro t
    simp only [o, oddTailRealPart_apply, Complex.ofReal_im]
  have hrReal : ∀ t : ℝ, ((r : YoshidaClippedSmooth yoshidaA) t).im = 0 := by
    intro t
    simpa only [r, canonicalOddLowModePeriodicCore_toSmooth] using
      oddLowMode_im_zero j t
  have hrNeg : (r : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0 := by
    change yoshidaClippedOddMode yoshidaA (j.1 + 1) (-yoshidaA) = 0
    exact yoshidaClippedOddMode_left_endpoint yoshidaA_pos (j.1 + 1)
  have hrPos : (r : YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
    change yoshidaClippedOddMode yoshidaA (j.1 + 1) yoshidaA = 0
    exact yoshidaClippedOddMode_right_endpoint yoshidaA_pos (j.1 + 1)
  obtain ⟨hoNeg, hoPos⟩ := oddTenTail_endpoints_zero o
  have hbridge := factorTwoCenteredCleanPolarization_eq_clippedCriticalForm_re_div
    r (o : YoshidaClippedPeriodicCore yoshidaA) hrReal hreal
      hrNeg hrPos hoNeg hoPos
  have htail := oddTailLowFunctional_sq_le_formNorm
    (FormSpace.of o : OddPhaseTailFormSpace) j
  have hconj := yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos
    (oddTenTailToClippedSmooth o)
    (yoshidaClippedOddLowMode yoshidaA j)
  have hz : Complex.normSq z ≤
      (1 / 40 : ℝ) * ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    have htail' := htail
    rw [← hconj] at htail'
    simpa only [z, r, canonicalOddLowModePeriodicCore, norm_star] using htail'
  have hrealSq : z.re ^ 2 ≤ Complex.normSq z := by
    simpa only [pow_two] using Complex.re_sq_le_normSq z
  have hoNorm := norm_oddTailRealPart_le_core x
  change factorTwoCenteredCleanPolarization
      (factorTwoCenteredOddLowProfile j) (canonicalOddTailProfile o) =
    z.re / yoshidaA at hbridge
  unfold canonicalPhaseLowBasisTailRealCleanValue
    canonicalPhaseLowBasisEvenProfile canonicalPhaseLowBasisOddProfile
    canonicalPhaseTailOddRealProfile
  simp only [factorTwoCenteredCleanPolarization_zero_left, zero_add]
  rw [hbridge]
  have hA2 : 0 < yoshidaA ^ 2 := sq_pos_of_pos yoshidaA_pos
  rw [div_pow]
  calc
    z.re ^ 2 / yoshidaA ^ 2 ≤ Complex.normSq z / yoshidaA ^ 2 :=
      div_le_div_of_nonneg_right hrealSq hA2.le
    _ ≤ ((1 / 40 : ℝ) *
          ‖(FormSpace.of o : OddPhaseTailFormSpace)‖ ^ 2) /
        yoshidaA ^ 2 := div_le_div_of_nonneg_right hz hA2.le
    _ ≤ ((1 / 40 : ℝ) * ‖x‖ ^ 2) / yoshidaA ^ 2 := by
      gcongr
    _ = (1 / (40 * yoshidaA ^ 2) : ℝ) * ‖x‖ ^ 2 := by ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailCleanRowsStructural
