import ArithmeticHodge.Analysis.CoerciveBilinearSchurShear
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailCorrectionEnergyStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailAssemblyClosureStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedDecomposition
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowPhaseMatrix

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open Complex Matrix Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailEndpointShearStructural

noncomputable section

open ArithmeticHodge.Analysis
open FormSpace
open YoshidaClippedEvenMomentBridge
open YoshidaCoercivityNumerics
open YoshidaEndpointScaledCorrelation
open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaEvenHomogeneousCoercivity
open YoshidaEvenTailLowFunctional
open YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousPhaseCongruenceStructural
open YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyClosureStructural
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionEnergyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailRieszStructural
open YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
open YoshidaFactorTwoPhaseEndpointAdaptedDecomposition
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseEndpointAdaptedTail
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseTailRealImagStructural
open YoshidaWeightedTailBounds

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

/-- Frequency `200`, bundled as the first vector in the canonical even tail. -/
def canonicalPhaseMode200Tail : YoshidaEvenOneNinetyNineTail :=
  ⟨evenHighModePeriodicCore 0, endpointEvenCorrectionMode_mem_tail⟩

/-- Frequency `200` in the real coordinate of the canonical phase-tail core. -/
def canonicalPhaseMode200Core : CanonicalPhaseTailCore :=
  WithLp.toLp 2
    (FormSpace.of canonicalPhaseMode200Tail,
      (0 : OddPhaseTailFormSpace))

/-- The endpoint trace carried by a packed finite-low coefficient vector,
realized inside the actual cutoff-`199` tail. -/
def canonicalPhaseLowMode200ShiftCore
    (c : FactorTwoPhaseLowIndex → ℝ) : CanonicalPhaseTailCore :=
  evenLowEndpointCorrectionCoefficient
      (canonicalPhaseLowEvenCoefficients c) • canonicalPhaseMode200Core

/-- The same endpoint shift in the completed coercive tail space. -/
def canonicalPhaseLowMode200Shift
    (c : FactorTwoPhaseLowIndex → ℝ) : CanonicalPhaseTailCompletion :=
  (canonicalPhaseLowMode200ShiftCore c : CanonicalPhaseTailCompletion)

private theorem mode200_argument (x : ℝ) :
    Real.pi * (200 : ℝ) * (yoshidaA * x) / yoshidaA =
      Real.pi * (200 : ℝ) * x := by
  field_simp [yoshidaA_pos.ne']

/-- On the physical endpoint interval, the embedded tail direction is the
normalized centered cosine of frequency `200`. -/
theorem canonicalPhaseMode200EvenRealProfile_eq_top_Icc
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    canonicalPhaseTailEvenRealProfile canonicalPhaseMode200Core x =
      factorTwoCenteredCanonicalEvenProfile
        factorTwoCanonicalEvenTopIndex x := by
  have hAx : yoshidaA * x ∈ Icc (-yoshidaA) yoshidaA := by
    constructor
    · nlinarith [yoshidaA_pos, hx.1]
    · nlinarith [yoshidaA_pos, hx.2]
  rw [show canonicalPhaseTailEvenRealProfile canonicalPhaseMode200Core =
      boundaryContinuousEvenProfile
        (canonicalEvenTailPointwise
          (evenTailRealPart canonicalPhaseMode200Tail)) by rfl,
    boundaryContinuousEvenProfile_eq_centeredRescale _
      (by
        intro t
        rw [show ((((canonicalEvenTailPointwise
            (evenTailRealPart canonicalPhaseMode200Tail)).1 :
              YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) t) =
          evenOneNinetyNineTailToClippedSmooth
            (evenTailRealPart canonicalPhaseMode200Tail) t by rfl,
          evenTailRealPart_apply]
        simp) hx]
  unfold centeredRescale
  change (evenOneNinetyNineTailToClippedSmooth
      (evenTailRealPart canonicalPhaseMode200Tail) (yoshidaA * x)).re = _
  rw [evenTailRealPart_apply]
  unfold canonicalPhaseMode200Tail
  change (yoshidaClippedEvenMode yoshidaA 200 (yoshidaA * x)).re = _
  rw [yoshidaClippedEvenMode_apply_of_mem yoshidaA_pos 200 hAx]
  change (Real.sqrt yoshidaA)⁻¹ *
      Real.cos (Real.pi * (200 : ℝ) * (yoshidaA * x) / yoshidaA) = _
  rw [show factorTwoCenteredCanonicalEvenProfile
      factorTwoCanonicalEvenTopIndex x =
        (Real.sqrt yoshidaA)⁻¹ *
          Real.cos (Real.pi * (200 : ℝ) * x) by
    unfold factorTwoCenteredCanonicalEvenProfile
    change (if (200 : ℕ) = 0 then
        fun _ ↦ (Real.sqrt (2 * yoshidaA))⁻¹
      else fun y ↦ (Real.sqrt yoshidaA)⁻¹ *
        Real.cos (Real.pi * (200 : ℝ) * y)) x = _
    rw [if_neg (by norm_num)]]
  rw [mode200_argument]

/-- The frequency-`200` core is pointwise real. -/
theorem canonicalPhaseMode200EvenImagProfile_eq_zero :
    canonicalPhaseTailEvenImagProfile canonicalPhaseMode200Core = 0 := by
  funext x
  change boundaryCanonicalEvenTailProfile
      (evenTailImagPart canonicalPhaseMode200Tail) x = 0
  have himag : evenTailImagPart canonicalPhaseMode200Tail = 0 := by
    unfold evenTailImagPart
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext t
    change (((((evenHighModePeriodicCore 0 :
      YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) t).im : ℝ) : ℂ) = 0
    rw [evenHighModePeriodicCore_zero_im]
    simp
  rw [himag]
  exact congrFun boundaryContinuousEvenProfile_zero x

@[simp] theorem canonicalPhaseMode200OddRealProfile_eq_zero :
    canonicalPhaseTailOddRealProfile canonicalPhaseMode200Core = 0 := by
  rfl

@[simp] theorem canonicalPhaseMode200OddImagProfile_eq_zero :
    canonicalPhaseTailOddImagProfile canonicalPhaseMode200Core = 0 := by
  rfl

/-- The aggregate shift profile is exactly its endpoint coefficient times
the normalized frequency-`200` cosine. -/
theorem canonicalPhaseLowMode200ShiftEvenRealProfile_eq_top_Icc
    (c : FactorTwoPhaseLowIndex → ℝ) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    canonicalPhaseTailEvenRealProfile
        (canonicalPhaseLowMode200ShiftCore c) x =
      evenLowEndpointCorrectionCoefficient
          (canonicalPhaseLowEvenCoefficients c) *
        factorTwoCenteredCanonicalEvenProfile
          factorTwoCanonicalEvenTopIndex x := by
  rw [canonicalPhaseLowMode200ShiftCore,
    canonicalPhaseTailEvenRealProfile_smul,
    Pi.smul_apply, smul_eq_mul,
    canonicalPhaseMode200EvenRealProfile_eq_top_Icc hx]

@[simp] theorem canonicalPhaseLowMode200ShiftEvenImagProfile_eq_zero
    (c : FactorTwoPhaseLowIndex → ℝ) :
    canonicalPhaseTailEvenImagProfile
        (canonicalPhaseLowMode200ShiftCore c) = 0 := by
  rw [canonicalPhaseLowMode200ShiftCore,
    canonicalPhaseTailEvenImagProfile_smul,
    canonicalPhaseMode200EvenImagProfile_eq_zero, smul_zero]

@[simp] theorem canonicalPhaseLowMode200ShiftOddRealProfile_eq_zero
    (c : FactorTwoPhaseLowIndex → ℝ) :
    canonicalPhaseTailOddRealProfile
        (canonicalPhaseLowMode200ShiftCore c) = 0 := by
  rw [canonicalPhaseLowMode200ShiftCore,
    canonicalPhaseTailOddRealProfile_smul,
    canonicalPhaseMode200OddRealProfile_eq_zero, smul_zero]

@[simp] theorem canonicalPhaseLowMode200ShiftOddImagProfile_eq_zero
    (c : FactorTwoPhaseLowIndex → ℝ) :
    canonicalPhaseTailOddImagProfile
        (canonicalPhaseLowMode200ShiftCore c) = 0 := by
  rw [canonicalPhaseLowMode200ShiftCore,
    canonicalPhaseTailOddImagProfile_smul,
    canonicalPhaseMode200OddImagProfile_eq_zero, smul_zero]

/-- Subtracting the endpoint shift from the canonical boundary-continuous
low profile produces the endpoint-adapted finite synthesis on the entire
physical interval. -/
theorem canonicalBoundaryLow_sub_mode200Shift_eq_adapted_Icc
    (c : FactorTwoPhaseLowIndex → ℝ) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoBoundaryCanonicalEvenLowProfile
        (canonicalPhaseLowEvenCoefficients c) x -
      canonicalPhaseTailEvenRealProfile
        (canonicalPhaseLowMode200ShiftCore c) x =
      factorTwoAdaptedEvenLowSynthesis
        (canonicalPhaseLowEvenCoefficients c) x := by
  rw [factorTwoBoundaryCanonicalEvenLowProfile_eq_canonical_Icc _ hx,
    canonicalPhaseLowMode200ShiftEvenRealProfile_eq_top_Icc c hx]
  classical
  unfold factorTwoCanonicalEvenLowSynthesis
    factorTwoAdaptedEvenLowSynthesis
    evenLowEndpointCorrectionCoefficient
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [factorTwoCenteredAdaptedEvenLowProfile_eq_canonical_sub _ hx]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem canonicalPhaseTailEvenRealProfile_neg
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenRealProfile (-x) =
      -canonicalPhaseTailEvenRealProfile x := by
  simpa only [neg_one_smul] using
    (canonicalPhaseTailEvenRealProfile_smul (-1) x)

private theorem canonicalPhaseTailEvenImagProfile_neg
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenImagProfile (-x) =
      -canonicalPhaseTailEvenImagProfile x := by
  simpa only [neg_one_smul] using
    (canonicalPhaseTailEvenImagProfile_smul (-1) x)

private theorem canonicalPhaseTailOddRealProfile_neg
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailOddRealProfile (-x) =
      -canonicalPhaseTailOddRealProfile x := by
  simpa only [neg_one_smul] using
    (canonicalPhaseTailOddRealProfile_smul (-1) x)

private theorem canonicalPhaseTailOddImagProfile_neg
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailOddImagProfile (-x) =
      -canonicalPhaseTailOddImagProfile x := by
  simpa only [neg_one_smul] using
    (canonicalPhaseTailOddImagProfile_smul (-1) x)

private theorem yoshidaEndpointOddCleanQuadratic_zero :
    yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
  have h :=
    yoshidaEndpointOddCleanQuadratic_const_mul (fun _ : ℝ ↦ 1) 0
  norm_num at h
  change yoshidaEndpointOddCleanQuadratic (fun _ : ℝ ↦ 0) = 0
  exact h

private theorem factorTwoCenteredSymmetricPerturbation_zero :
    factorTwoCenteredSymmetricPerturbation (0 : ℝ → ℝ) = 0 := by
  have h := factorTwoCenteredSymmetricPerturbation_smul
    0 (fun _ : ℝ ↦ 1)
  norm_num at h
  exact h

private theorem factorTwoEndpointChannelPhase_zero_zero (a b : ℝ) :
    factorTwoEndpointChannelPhase (0 : ℝ → ℝ) (0 : ℝ → ℝ) a b = 0 := by
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
  rw [yoshidaEndpointOddCleanQuadratic_zero,
    factorTwoCenteredSymmetricPerturbation_zero,
    factorTwoCenteredAlternatingCoupling_self]
  ring

/-- Giving the canonical finite-low block the negative of its endpoint shift
leaves exactly the endpoint-adapted finite-low physical phase. -/
theorem canonicalPhasePhysicalLowTailValue_neg_mode200Shift_eq_concrete
    (c : FactorTwoPhaseLowIndex → ℝ) (a b : ℝ) :
    canonicalPhasePhysicalLowTailValue c 0
        (-canonicalPhaseLowMode200ShiftCore c) a b =
      c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c) := by
  have hreal :
      factorTwoEndpointChannelPhase
          (factorTwoBoundaryCanonicalEvenLowProfile
              (canonicalPhaseLowEvenCoefficients c) +
            canonicalPhaseTailEvenRealProfile
              (-canonicalPhaseLowMode200ShiftCore c))
          (factorTwoOddLowSynthesis
              (canonicalPhaseLowOddCoefficients c) +
            canonicalPhaseTailOddRealProfile
              (-canonicalPhaseLowMode200ShiftCore c)) a b =
        factorTwoEndpointChannelPhase
          (factorTwoAdaptedEvenLowSynthesis
            (canonicalPhaseLowEvenCoefficients c))
          (factorTwoOddLowSynthesis
            (canonicalPhaseLowOddCoefficients c)) a b := by
    apply factorTwoEndpointChannelPhase_congr_Icc
    · intro x hx
      rw [Pi.add_apply, canonicalPhaseTailEvenRealProfile_neg,
        Pi.neg_apply]
      change factorTwoBoundaryCanonicalEvenLowProfile
          (canonicalPhaseLowEvenCoefficients c) x -
        canonicalPhaseTailEvenRealProfile
          (canonicalPhaseLowMode200ShiftCore c) x = _
      exact canonicalBoundaryLow_sub_mode200Shift_eq_adapted_Icc c hx
    · intro x _hx
      rw [Pi.add_apply, canonicalPhaseTailOddRealProfile_neg,
        canonicalPhaseLowMode200ShiftOddRealProfile_eq_zero,
        Pi.neg_apply, Pi.zero_apply]
      ring
  have himag :
      factorTwoEndpointChannelPhase
          (factorTwoBoundaryCanonicalEvenLowProfile
              (canonicalPhaseLowEvenCoefficients 0) +
            canonicalPhaseTailEvenImagProfile
              (-canonicalPhaseLowMode200ShiftCore c))
          (factorTwoOddLowSynthesis
              (canonicalPhaseLowOddCoefficients 0) +
            canonicalPhaseTailOddImagProfile
              (-canonicalPhaseLowMode200ShiftCore c)) a b = 0 := by
    calc
      _ = factorTwoEndpointChannelPhase
          (0 : ℝ → ℝ) (0 : ℝ → ℝ) a b := by
        apply factorTwoEndpointChannelPhase_congr_Icc
        · intro x hx
          rw [Pi.add_apply,
            factorTwoBoundaryCanonicalEvenLowProfile_eq_canonical_Icc _ hx,
            canonicalPhaseTailEvenImagProfile_neg,
            canonicalPhaseLowMode200ShiftEvenImagProfile_eq_zero,
            Pi.neg_apply, Pi.zero_apply]
          classical
          simp [factorTwoCanonicalEvenLowSynthesis,
            canonicalPhaseLowEvenCoefficients]
        · intro x _hx
          rw [Pi.add_apply, canonicalPhaseTailOddImagProfile_neg,
            canonicalPhaseLowMode200ShiftOddImagProfile_eq_zero,
            Pi.neg_apply, Pi.zero_apply]
          classical
          simp [factorTwoOddLowSynthesis, canonicalPhaseLowOddCoefficients]
      _ = 0 := factorTwoEndpointChannelPhase_zero_zero a b
  unfold canonicalPhasePhysicalLowTailValue
  rw [hreal, himag, add_zero]
  simpa only [factorTwoPhaseLowCoefficients_unpacked] using
    (factorTwoConcreteLowPhaseMatrix_represents
      (canonicalPhaseLowEvenCoefficients c)
      (canonicalPhaseLowOddCoefficients c) a b)

/-- Exact quadratic effect of moving the aggregate endpoint trace from the
canonical low block into frequency `200` and then cancelling it in the tail. -/
theorem factorTwoConcreteLowPhaseMatrix_quadratic_eq_canonical_shear
    (c : FactorTwoPhaseLowIndex → ℝ) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c) =
      c ⬝ᵥ (canonicalPhaseLowMatrix a b *ᵥ c) -
        2 * ∑ k, c k *
          completedCanonicalPhaseLowBasisTailRealFunctional
            k a b hphase (canonicalPhaseLowMode200Shift c) +
        completedCanonicalPhaseTailBilinear a b hphase
          (canonicalPhaseLowMode200Shift c)
          (canonicalPhaseLowMode200Shift c) := by
  have hPhysical :=
    canonicalPhasePhysicalLowTailValue_eq_schurQuadratic
      c 0 (-canonicalPhaseLowMode200ShiftCore c) a b hphase
  unfold CanonicalPhasePhysicalLowTailAssembly at hPhysical
  rw [canonicalPhasePhysicalLowTailValue_neg_mode200Shift_eq_concrete]
    at hPhysical
  unfold canonicalPhaseLowTailSchurQuadratic at hPhysical
  dsimp only at hPhysical
  rw [canonicalPhaseLowRealImagMatrix_quadratic,
    completedCanonicalPhaseLowRealImagFunctional_sum] at hPhysical
  simp only [zero_dotProduct, UniformSpace.Completion.coe_neg, map_neg,
    ContinuousLinearMap.neg_apply, mul_neg,
    Finset.sum_neg_distrib, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, neg_neg] at hPhysical
  unfold canonicalPhaseLowMode200Shift
  convert hPhysical using 1
  ring

/-- The aggregate canonical Riesz correction represents the aggregate
finite-low mixed functional, without expanding any correction entry. -/
theorem completedCanonicalPhaseTailBilinear_realRieszCombination_apply
    (c : FactorTwoPhaseLowIndex → ℝ) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (z : CanonicalPhaseTailCompletion) :
    completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseLowTailRealRieszCombination c a b hphase) z =
      ∑ k, c k *
        completedCanonicalPhaseLowBasisTailRealFunctional
          k a b hphase z := by
  classical
  unfold canonicalPhaseLowTailRealRieszCombination
  simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [completedCanonicalPhaseTailBilinear_realRieszCorrection_apply]

/-- Endpoint-cancelled aggregate Riesz correction.  This is the canonical
aggregate representer after the exact frequency-`200` tail shear. -/
def canonicalPhaseAdaptedLowTailRealRieszCombination
    (c : FactorTwoPhaseLowIndex → ℝ) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) : CanonicalPhaseTailCompletion :=
  canonicalPhaseLowTailRealRieszCombination c a b hphase -
    canonicalPhaseLowMode200Shift c

private theorem completedCanonicalPhaseTailBilinear_sub_self
    (r s : CanonicalPhaseTailCompletion) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    completedCanonicalPhaseTailBilinear a b hphase (r - s) (r - s) =
      completedCanonicalPhaseTailBilinear a b hphase r r -
        2 * completedCanonicalPhaseTailBilinear a b hphase r s +
        completedCanonicalPhaseTailBilinear a b hphase s s := by
  have hSymm := completedCanonicalPhaseTailBilinear_symm
    a b hphase s r
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [hSymm]
  ring

/-- The canonical and endpoint-adapted Schur quadratics agree exactly after
the mode-`200` tail shear. -/
theorem canonical_correctedQuadratic_eq_endpointAdapted
    (c : FactorTwoPhaseLowIndex → ℝ) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    c ⬝ᵥ (canonicalPhaseLowMatrix a b *ᵥ c) -
        completedCanonicalPhaseTailBilinear a b hphase
          (canonicalPhaseLowTailRealRieszCombination c a b hphase)
          (canonicalPhaseLowTailRealRieszCombination c a b hphase) =
      c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c) -
        completedCanonicalPhaseTailBilinear a b hphase
          (canonicalPhaseAdaptedLowTailRealRieszCombination
            c a b hphase)
          (canonicalPhaseAdaptedLowTailRealRieszCombination
            c a b hphase) := by
  let r := canonicalPhaseLowTailRealRieszCombination c a b hphase
  let s := canonicalPhaseLowMode200Shift c
  let ellSum := ∑ k, c k *
    completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase s
  have hLow := factorTwoConcreteLowPhaseMatrix_quadratic_eq_canonical_shear
    c a b hphase
  have hCross :
      completedCanonicalPhaseTailBilinear a b hphase r s = ellSum := by
    exact completedCanonicalPhaseTailBilinear_realRieszCombination_apply
      c a b hphase s
  change c ⬝ᵥ (canonicalPhaseLowMatrix a b *ᵥ c) -
      completedCanonicalPhaseTailBilinear a b hphase r r =
    c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c) -
      completedCanonicalPhaseTailBilinear a b hphase (r - s) (r - s)
  rw [completedCanonicalPhaseTailBilinear_sub_self, hCross]
  linarith [hLow]

/-- Exact structural normalization of the remaining reduced certificate.
The canonical corrected Gram is PSD iff the endpoint-adapted low quadratic
dominates the energy of the endpoint-cancelled aggregate representer. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_endpointAdapted_energy
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    Matrix.PosSemidef
        (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) ↔
      ∀ c : FactorTwoPhaseLowIndex → ℝ,
        completedCanonicalPhaseTailBilinear a b hphase
            (canonicalPhaseAdaptedLowTailRealRieszCombination
              c a b hphase)
            (canonicalPhaseAdaptedLowTailRealRieszCombination
              c a b hphase) ≤
          c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c) := by
  rw [completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_energy]
  constructor
  · intro hEnergy c
    have hCanonical := hEnergy c
    have hShear := canonical_correctedQuadratic_eq_endpointAdapted
      c a b hphase
    linarith
  · intro hEnergy c
    have hAdapted := hEnergy c
    have hShear := canonical_correctedQuadratic_eq_endpointAdapted
      c a b hphase
    linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailEndpointShearStructural
