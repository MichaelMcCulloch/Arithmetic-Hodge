import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailPhysicalCharacterizationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailProductionClosureStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailRadiusStructural

noncomputable section

open ArithmeticHodge.Analysis
open FormSpace
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailPhysicalCharacterizationStructural
open YoshidaFactorTwoPhaseCanonicalLowTailProductionClosureStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseTailRealImagStructural
open YoshidaOddHomogeneousCoercivity
open YoshidaWeightedTailBounds

/-!
# Real-coordinate reduction of the canonical physical radius

The shared complex tail carrier contributes two real endpoint channels.  The
imaginary channel contains no retained low vector, hence its sharp radius is
already supplied by the proved tail theorem.  The triangle inequality then
shows that the full complex physical-radius target is equivalent to the same
target for the single real low-plus-tail channel.  Thus no separate mixed
estimate involving the imaginary tail remains.
-/

/-- Center of the only channel which contains retained low coordinates. -/
def canonicalPhasePhysicalRealLowTailCleanSum
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore) : ℝ :=
  factorTwoEndpointChannelCleanSum
    (factorTwoBoundaryCanonicalEvenLowProfile
        (canonicalPhaseLowEvenCoefficients c) +
      canonicalPhaseTailEvenRealProfile x)
    (factorTwoOddLowSynthesis (canonicalPhaseLowOddCoefficients c) +
      canonicalPhaseTailOddRealProfile x)

/-- Complex coordinate of the only channel which contains retained low
coordinates. -/
def canonicalPhasePhysicalRealLowTailCoordinate
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore) : ℂ :=
  factorTwoEndpointChannelCoordinate
    (factorTwoBoundaryCanonicalEvenLowProfile
        (canonicalPhaseLowEvenCoefficients c) +
      canonicalPhaseTailEvenRealProfile x)
    (factorTwoOddLowSynthesis (canonicalPhaseLowOddCoefficients c) +
      canonicalPhaseTailOddRealProfile x)

/-- Center of the pure imaginary tail channel. -/
def canonicalPhasePhysicalImagTailCleanSum
    (x : CanonicalPhaseTailCore) : ℝ :=
  factorTwoEndpointChannelCleanSum
    (canonicalPhaseTailEvenImagProfile x)
    (canonicalPhaseTailOddImagProfile x)

/-- Complex coordinate of the pure imaginary tail channel. -/
def canonicalPhasePhysicalImagTailCoordinate
    (x : CanonicalPhaseTailCore) : ℂ :=
  factorTwoEndpointChannelCoordinate
    (canonicalPhaseTailEvenImagProfile x)
    (canonicalPhaseTailOddImagProfile x)

theorem normSq_add_le_add_sq
    (z w : ℂ) (q r : ℝ)
    (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hz : Complex.normSq z ≤ q ^ 2)
    (hw : Complex.normSq w ≤ r ^ 2) :
    Complex.normSq (z + w) ≤ (q + r) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq] at hz hw ⊢
  have hz' : ‖z‖ ≤ q :=
    (sq_le_sq₀ (norm_nonneg z) hq).1 hz
  have hw' : ‖w‖ ≤ r :=
    (sq_le_sq₀ (norm_nonneg w) hr).1 hw
  have hadd : ‖z + w‖ ≤ q + r :=
    (norm_add_le z w).trans (add_le_add hz' hw')
  exact (sq_le_sq₀ (norm_nonneg (z + w)) (add_nonneg hq hr)).2 hadd

private theorem yoshidaEndpointOddCleanQuadratic_zero :
    yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
  have h := yoshidaEndpointOddCleanQuadratic_const_mul (fun _ : ℝ ↦ 1) 0
  norm_num at h
  change yoshidaEndpointOddCleanQuadratic (fun _ : ℝ ↦ 0) = 0
  exact h

private theorem factorTwoCenteredSymmetricPerturbation_zero :
    factorTwoCenteredSymmetricPerturbation (0 : ℝ → ℝ) = 0 := by
  have h := factorTwoCenteredSymmetricPerturbation_smul
    0 (fun _ : ℝ ↦ 1)
  norm_num at h
  exact h

private theorem factorTwoEndpointChannelCleanSum_zero_zero :
    factorTwoEndpointChannelCleanSum (0 : ℝ → ℝ) (0 : ℝ → ℝ) = 0 := by
  unfold factorTwoEndpointChannelCleanSum
  rw [yoshidaEndpointOddCleanQuadratic_zero]
  ring

private theorem factorTwoEndpointChannelCoordinate_zero_zero :
    factorTwoEndpointChannelCoordinate (0 : ℝ → ℝ) (0 : ℝ → ℝ) = 0 := by
  apply Complex.ext
  · unfold factorTwoEndpointChannelCoordinate
      factorTwoEndpointChannelSymmetricSum
    simp only [zero_re]
    rw [factorTwoCenteredSymmetricPerturbation_zero]
    ring
  · unfold factorTwoEndpointChannelCoordinate
    simp only [zero_im]
    rw [factorTwoCenteredAlternatingCoupling_self]


@[simp] private theorem factorTwoBoundaryCanonicalEvenLowProfile_zero :
    factorTwoBoundaryCanonicalEvenLowProfile
      (0 : YoshidaEvenIndex → ℝ) = 0 := by
  unfold factorTwoBoundaryCanonicalEvenLowProfile
  have hzero : canonicalEvenRealLowPointwise
      (0 : YoshidaEvenIndex → ℝ) = 0 := by
    apply Subtype.ext
    change canonicalEvenRealLowPeriodicCore
      (0 : YoshidaEvenIndex → ℝ) = 0
    classical
    simp [canonicalEvenRealLowPeriodicCore]
  rw [hzero, boundaryContinuousEvenProfile_zero]

@[simp] private theorem factorTwoOddLowSynthesis_zero :
    factorTwoOddLowSynthesis (0 : YoshidaOddIndex → ℝ) = 0 := by
  funext t
  unfold factorTwoOddLowSynthesis factorTwoCenteredOddLowProfile
  simp

private theorem evenTailImagPart_real
    (x : CanonicalPhaseTailCore) (t : ℝ) :
    (evenOneNinetyNineTailToClippedSmooth
      (evenTailImagPart x.fst.toV) t).im = 0 := by
  change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).im : ℝ) :
    ℂ)).im) = 0
  simp

private theorem evenTailRealPart_real
    (x : CanonicalPhaseTailCore) (t : ℝ) :
    (evenOneNinetyNineTailToClippedSmooth
      (evenTailRealPart x.fst.toV) t).im = 0 := by
  change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).re : ℝ) :
    ℂ)).im) = 0
  simp

private theorem oddTailImagPart_real
    (x : CanonicalPhaseTailCore) (t : ℝ) :
    (oddTenTailToClippedSmooth (oddTailImagPart x.snd.toV) t).im = 0 := by
  change (((((oddTenTailToClippedSmooth x.snd.toV t).im : ℝ) : ℂ)).im) = 0
  simp

private theorem oddTailRealPart_real
    (x : CanonicalPhaseTailCore) (t : ℝ) :
    (oddTenTailToClippedSmooth (oddTailRealPart x.snd.toV) t).im = 0 := by
  change (((((oddTenTailToClippedSmooth x.snd.toV t).re : ℝ) : ℂ)).im) = 0
  simp

/-- The proved tail coercivity has a quantitative numerical-radius form: a
standard real tail channel has radius at most `199 / 200` of its clean
center.  This is the exact residual margin left by the uniform `1 / 200`
phase reserve. -/
theorem canonicalRealTail_radius_le_199_div_200
    (e : YoshidaEvenOneNinetyNineTail) (o : YoshidaOddTenTail)
    (he : ∀ t : ℝ, (evenOneNinetyNineTailToClippedSmooth e t).im = 0)
    (ho : ∀ t : ℝ, (oddTenTailToClippedSmooth o t).im = 0) :
    0 ≤ factorTwoEndpointChannelCleanSum
        (boundaryCanonicalEvenTailProfile e) (canonicalOddTailProfile o) ∧
      Complex.normSq (factorTwoEndpointChannelCoordinate
          (boundaryCanonicalEvenTailProfile e) (canonicalOddTailProfile o)) ≤
        ((199 / 200 : ℝ) * factorTwoEndpointChannelCleanSum
          (boundaryCanonicalEvenTailProfile e) (canonicalOddTailProfile o)) ^ 2 := by
  let E := boundaryCanonicalEvenTailProfile e
  let O := canonicalOddTailProfile o
  let Q := factorTwoEndpointChannelCleanSum E O
  let P := factorTwoEndpointChannelSymmetricSum E O
  let J := factorTwoCenteredAlternatingCoupling E O
  have hnonneg : ∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ 1 →
      0 ≤ (199 / 200 : ℝ) * Q + a * P + b * J := by
    intro a b hphase
    have hreserve := boundaryContinuous_tail_phase_uniform_clean_reserve
      (e : YoshidaClippedPeriodicCore yoshidaA)
      (o : YoshidaClippedPeriodicCore yoshidaA)
      e.property o.property he ho a b hphase
    change (1 / 200 : ℝ) * Q ≤
      factorTwoEndpointChannelPhase E O a b at hreserve
    unfold factorTwoEndpointChannelPhase at hreserve
    dsimp only [Q, P, J] at hreserve ⊢
    linarith
  have hradius := (real_closedDisk_phase_nonneg_iff_radius
    ((199 / 200 : ℝ) * Q) P J).1 hnonneg
  have hQ : 0 ≤ Q := by
    have hcoef : 0 < (199 / 200 : ℝ) := by norm_num
    nlinarith [hradius.1]
  refine ⟨?_, ?_⟩
  · simpa only [Q, E, O] using hQ
  · rw [factorTwoEndpointChannelCoordinate_normSq]
    simpa only [Q, P, J, E, O] using hradius.2

/-- Quantitative form of the already-closed imaginary-tail radius. -/
theorem canonicalPhasePhysicalImagTail_radius_le_199_div_200
    (x : CanonicalPhaseTailCore) :
    0 ≤ canonicalPhasePhysicalImagTailCleanSum x ∧
      Complex.normSq (canonicalPhasePhysicalImagTailCoordinate x) ≤
        ((199 / 200 : ℝ) * canonicalPhasePhysicalImagTailCleanSum x) ^ 2 := by
  simpa only [canonicalPhasePhysicalImagTailCleanSum,
    canonicalPhasePhysicalImagTailCoordinate,
    canonicalPhaseTailEvenImagProfile, canonicalPhaseTailOddImagProfile]
    using canonicalRealTail_radius_le_199_div_200
      (evenTailImagPart x.fst.toV) (oddTailImagPart x.snd.toV)
      (evenTailImagPart_real x) (oddTailImagPart_real x)

/-- Projection of the complex canonical tail onto its pointwise-real
coordinate, still represented inside the same canonical carrier. -/
def canonicalPhaseTailCoreRealPart
    (x : CanonicalPhaseTailCore) : CanonicalPhaseTailCore :=
  canonicalPhaseTailCoreOfRealTails
    (evenTailRealPart x.fst.toV) (oddTailRealPart x.snd.toV)

/-- Realification preserves the real profiles and kills the imaginary
profiles exactly. -/
theorem canonicalPhaseTailCoreRealPart_profiles
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenRealProfile (canonicalPhaseTailCoreRealPart x) =
        canonicalPhaseTailEvenRealProfile x ∧
      canonicalPhaseTailOddRealProfile (canonicalPhaseTailCoreRealPart x) =
        canonicalPhaseTailOddRealProfile x ∧
      canonicalPhaseTailEvenImagProfile (canonicalPhaseTailCoreRealPart x) = 0 ∧
      canonicalPhaseTailOddImagProfile (canonicalPhaseTailCoreRealPart x) = 0 := by
  have hp := canonicalPhaseTailCoreOfRealTails_profiles
    (evenTailRealPart x.fst.toV) (oddTailRealPart x.snd.toV)
    (evenTailRealPart_real x) (oddTailRealPart_real x)
  simpa only [canonicalPhaseTailCoreRealPart,
    canonicalPhaseTailEvenRealProfile, canonicalPhaseTailOddRealProfile]
    using hp

/-- The pure imaginary tail channel already obeys the sharp radius bound; it
does not consume any retained-low Schur budget. -/
theorem canonicalPhasePhysicalImagTail_radius
    (x : CanonicalPhaseTailCore) :
    0 ≤ canonicalPhasePhysicalImagTailCleanSum x ∧
      Complex.normSq (canonicalPhasePhysicalImagTailCoordinate x) ≤
        canonicalPhasePhysicalImagTailCleanSum x ^ 2 := by
  obtain ⟨hQ, hZ⟩ :=
    canonicalPhasePhysicalImagTail_radius_le_199_div_200 x
  refine ⟨hQ, hZ.trans ?_⟩
  nlinarith [sq_nonneg (canonicalPhasePhysicalImagTailCleanSum x)]

theorem canonicalPhasePhysicalLowTailCleanSum_eq_real_add_imag
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore) :
    canonicalPhasePhysicalLowTailCleanSum c 0 x =
      canonicalPhasePhysicalRealLowTailCleanSum c x +
        canonicalPhasePhysicalImagTailCleanSum x := by
  unfold canonicalPhasePhysicalLowTailCleanSum
    canonicalPhasePhysicalRealLowTailCleanSum
    canonicalPhasePhysicalImagTailCleanSum
  have he : canonicalPhaseLowEvenCoefficients
      (0 : FactorTwoPhaseLowIndex → ℝ) = 0 := rfl
  have ho : canonicalPhaseLowOddCoefficients
      (0 : FactorTwoPhaseLowIndex → ℝ) = 0 := rfl
  rw [he, ho, factorTwoBoundaryCanonicalEvenLowProfile_zero,
    factorTwoOddLowSynthesis_zero, zero_add, zero_add]

theorem canonicalPhasePhysicalLowTailCoordinate_eq_real_add_imag
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore) :
    canonicalPhasePhysicalLowTailCoordinate c 0 x =
      canonicalPhasePhysicalRealLowTailCoordinate c x +
        canonicalPhasePhysicalImagTailCoordinate x := by
  unfold canonicalPhasePhysicalLowTailCoordinate
    canonicalPhasePhysicalRealLowTailCoordinate
    canonicalPhasePhysicalImagTailCoordinate
  have he : canonicalPhaseLowEvenCoefficients
      (0 : FactorTwoPhaseLowIndex → ℝ) = 0 := rfl
  have ho : canonicalPhaseLowOddCoefficients
      (0 : FactorTwoPhaseLowIndex → ℝ) = 0 := rfl
  rw [he, ho, factorTwoBoundaryCanonicalEvenLowProfile_zero,
    factorTwoOddLowSynthesis_zero, zero_add, zero_add]

/-- It is sufficient to prove the radius inequality only for the real
low-plus-tail channel.  The imaginary channel is a pure tail and combines
with it at constant one by the complex triangle inequality. -/
theorem canonicalPhasePhysicalLowTail_radius_of_real_radius
    (hreal : ∀ (c : FactorTwoPhaseLowIndex → ℝ)
        (x : CanonicalPhaseTailCore),
      0 ≤ canonicalPhasePhysicalRealLowTailCleanSum c x ∧
        Complex.normSq (canonicalPhasePhysicalRealLowTailCoordinate c x) ≤
          canonicalPhasePhysicalRealLowTailCleanSum c x ^ 2) :
    ∀ (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore),
      0 ≤ canonicalPhasePhysicalLowTailCleanSum c 0 x ∧
        Complex.normSq (canonicalPhasePhysicalLowTailCoordinate c 0 x) ≤
          canonicalPhasePhysicalLowTailCleanSum c 0 x ^ 2 := by
  intro c x
  obtain ⟨hQr, hZr⟩ := hreal c x
  obtain ⟨hQi, hZi⟩ := canonicalPhasePhysicalImagTail_radius x
  rw [canonicalPhasePhysicalLowTailCleanSum_eq_real_add_imag,
    canonicalPhasePhysicalLowTailCoordinate_eq_real_add_imag]
  exact ⟨add_nonneg hQr hQi,
    normSq_add_le_add_sq _ _ _ _ hQr hQi hZr hZi⟩

/-- Exact reduction of the phase-free canonical target to the single real
low-plus-tail channel.  The reverse implication uses realification, so the
imaginary pure-tail channel cannot hide failure of the real channel. -/
theorem canonicalPhasePhysicalLowTail_radius_iff_real_radius :
    (∀ (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore),
      0 ≤ canonicalPhasePhysicalLowTailCleanSum c 0 x ∧
        Complex.normSq (canonicalPhasePhysicalLowTailCoordinate c 0 x) ≤
          canonicalPhasePhysicalLowTailCleanSum c 0 x ^ 2) ↔
    (∀ (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore),
      0 ≤ canonicalPhasePhysicalRealLowTailCleanSum c x ∧
        Complex.normSq (canonicalPhasePhysicalRealLowTailCoordinate c x) ≤
          canonicalPhasePhysicalRealLowTailCleanSum c x ^ 2) := by
  constructor
  · intro hfull c x
    let y := canonicalPhaseTailCoreRealPart x
    obtain ⟨hER, hOR, hEI, hOI⟩ :=
      canonicalPhaseTailCoreRealPart_profiles x
    have h := hfull c y
    rw [canonicalPhasePhysicalLowTailCleanSum_eq_real_add_imag,
      canonicalPhasePhysicalLowTailCoordinate_eq_real_add_imag] at h
    unfold canonicalPhasePhysicalRealLowTailCleanSum
      canonicalPhasePhysicalRealLowTailCoordinate
      canonicalPhasePhysicalImagTailCleanSum
      canonicalPhasePhysicalImagTailCoordinate at h
    unfold canonicalPhasePhysicalRealLowTailCleanSum
      canonicalPhasePhysicalRealLowTailCoordinate
    rw [hER, hOR, hEI, hOI,
      factorTwoEndpointChannelCleanSum_zero_zero,
      factorTwoEndpointChannelCoordinate_zero_zero,
      add_zero, add_zero] at h
    exact h
  · exact canonicalPhasePhysicalLowTail_radius_of_real_radius

/-- The entire uniform-disk corrected-Gram problem therefore has one exact
phase-free remaining estimate: the radius of the real low-plus-tail channel. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_disk_posSemidef_iff_real_radius :
    (∀ (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1),
      Matrix.PosSemidef
        (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase)) ↔
    (∀ (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore),
      0 ≤ canonicalPhasePhysicalRealLowTailCleanSum c x ∧
        Complex.normSq (canonicalPhasePhysicalRealLowTailCoordinate c x) ≤
          canonicalPhasePhysicalRealLowTailCleanSum c x ^ 2) := by
  exact
    completedCanonicalPhaseLowTailRealCorrectedGram_disk_posSemidef_iff_physical_radius.trans
      canonicalPhasePhysicalLowTail_radius_iff_real_radius

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailRadiusStructural
