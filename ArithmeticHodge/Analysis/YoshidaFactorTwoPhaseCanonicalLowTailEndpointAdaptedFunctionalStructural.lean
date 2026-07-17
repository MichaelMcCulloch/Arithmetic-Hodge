import ArithmeticHodge.Analysis.CoerciveBilinearSchurCharacterization
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailEndpointAdaptedRieszStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousPhaseCongruenceStructural

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Matrix Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailEndpointAdaptedFunctionalStructural

noncomputable section

open ArithmeticHodge.Analysis
open FormSpace
open YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
open YoshidaFactorTwoPhaseBoundaryContinuousPhaseCongruenceStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyClosureStructural
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailEndpointAdaptedRieszStructural
open YoshidaFactorTwoPhaseCanonicalLowTailEndpointShearStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailRieszStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseTailRealImagStructural

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

/-!
# Aggregate endpoint-adapted low--tail functional

The mode-`200` endpoint shear is useful only if it is kept at the aggregate
functional level.  This module records that exact aggregate functional and
uses coercive Riesz duality to replace the corrected-Gram certificate by one
functional-square inequality against the complete tail energy.
-/

/-- The sum of the endpoint-adapted basis functionals is exactly the
canonical aggregate functional minus evaluation against the aggregate
mode-`200` shift. -/
theorem sum_completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
    (c : FactorTwoPhaseLowIndex → ℝ) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (z : CanonicalPhaseTailCompletion) :
    ∑ k, c k *
        completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
          k a b hphase z =
      (∑ k, c k *
        completedCanonicalPhaseLowBasisTailRealFunctional
          k a b hphase z) -
        completedCanonicalPhaseTailBilinear a b hphase
          (canonicalPhaseLowMode200Shift c) z := by
  rw [← sum_canonicalPhaseMode200BasisShift c]
  unfold completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
    coerciveBilinearShearedFunctional
  simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [ContinuousLinearMap.sub_apply, mul_sub]

/-- On the dense canonical tail core, the aggregate adapted functional is
the canonical physical mixed block minus the exact mode-`200` tail pairing. -/
theorem sum_completedCanonicalPhaseAdaptedLowBasisTailRealFunctional_coe_eq_sub
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    ∑ k, c k *
        completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
          k a b hphase (x : CanonicalPhaseTailCompletion) =
      canonicalPhaseLowTailRealMixed c x a b -
        canonicalPhaseTailCoreBilinearValue
          (canonicalPhaseLowMode200ShiftCore c) x a b := by
  rw [sum_completedCanonicalPhaseAdaptedLowBasisTailRealFunctional,
    ← canonicalPhaseLowTailRealMixed_eq_completed_sum]
  change canonicalPhaseLowTailRealMixed c x a b -
      completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseLowMode200ShiftCore c :
          CanonicalPhaseTailCompletion)
        (x : CanonicalPhaseTailCompletion) = _
  rw [completedCanonicalPhaseTailBilinear_coe_coe]

private theorem canonicalPhaseTailEvenRealProfile_sub
    (x y : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenRealProfile (x - y) =
    canonicalPhaseTailEvenRealProfile x -
        canonicalPhaseTailEvenRealProfile y := by
  rw [sub_eq_add_neg]
  rw [show -y = (-1 : ℝ) • y by simp]
  rw [canonicalPhaseTailEvenRealProfile_add,
    canonicalPhaseTailEvenRealProfile_smul]
  rw [neg_one_smul, sub_eq_add_neg]

private theorem canonicalPhaseTailEvenImagProfile_sub
    (x y : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenImagProfile (x - y) =
    canonicalPhaseTailEvenImagProfile x -
        canonicalPhaseTailEvenImagProfile y := by
  rw [sub_eq_add_neg]
  rw [show -y = (-1 : ℝ) • y by simp]
  rw [canonicalPhaseTailEvenImagProfile_add,
    canonicalPhaseTailEvenImagProfile_smul]
  rw [neg_one_smul, sub_eq_add_neg]

private theorem canonicalPhaseTailOddRealProfile_sub
    (x y : CanonicalPhaseTailCore) :
    canonicalPhaseTailOddRealProfile (x - y) =
    canonicalPhaseTailOddRealProfile x -
        canonicalPhaseTailOddRealProfile y := by
  rw [sub_eq_add_neg]
  rw [show -y = (-1 : ℝ) • y by simp]
  rw [canonicalPhaseTailOddRealProfile_add,
    canonicalPhaseTailOddRealProfile_smul]
  rw [neg_one_smul, sub_eq_add_neg]

private theorem canonicalPhaseTailOddImagProfile_sub
    (x y : CanonicalPhaseTailCore) :
    canonicalPhaseTailOddImagProfile (x - y) =
    canonicalPhaseTailOddImagProfile x -
        canonicalPhaseTailOddImagProfile y := by
  rw [sub_eq_add_neg]
  rw [show -y = (-1 : ℝ) • y by simp]
  rw [canonicalPhaseTailOddImagProfile_add,
    canonicalPhaseTailOddImagProfile_smul]
  rw [neg_one_smul, sub_eq_add_neg]

/-- Moving the aggregate endpoint trace into the real tail leaves exactly an
endpoint-adapted real low profile plus the original tail. -/
theorem canonicalPhasePhysicalLowTailValue_sub_mode200Shift_eq_adapted
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) :
    canonicalPhasePhysicalLowTailValue c 0
        (x - canonicalPhaseLowMode200ShiftCore c) a b =
      factorTwoEndpointChannelPhase
          (factorTwoAdaptedEvenLowSynthesis
              (canonicalPhaseLowEvenCoefficients c) +
            canonicalPhaseTailEvenRealProfile x)
          (factorTwoOddLowSynthesis
              (canonicalPhaseLowOddCoefficients c) +
            canonicalPhaseTailOddRealProfile x) a b +
        factorTwoEndpointChannelPhase
          (canonicalPhaseTailEvenImagProfile x)
          (canonicalPhaseTailOddImagProfile x) a b := by
  have hreal := factorTwoEndpointChannelPhase_congr_Icc
    (u := factorTwoBoundaryCanonicalEvenLowProfile
        (canonicalPhaseLowEvenCoefficients c) +
      canonicalPhaseTailEvenRealProfile
        (x - canonicalPhaseLowMode200ShiftCore c))
    (u' := factorTwoAdaptedEvenLowSynthesis
        (canonicalPhaseLowEvenCoefficients c) +
      canonicalPhaseTailEvenRealProfile x)
    (v := factorTwoOddLowSynthesis
        (canonicalPhaseLowOddCoefficients c) +
      canonicalPhaseTailOddRealProfile
        (x - canonicalPhaseLowMode200ShiftCore c))
    (v' := factorTwoOddLowSynthesis
        (canonicalPhaseLowOddCoefficients c) +
      canonicalPhaseTailOddRealProfile x)
    (by
      intro t ht
      rw [Pi.add_apply, canonicalPhaseTailEvenRealProfile_sub,
        Pi.sub_apply, Pi.add_apply]
      have hadapt := canonicalBoundaryLow_sub_mode200Shift_eq_adapted_Icc
        c ht
      linarith)
    (by
      intro t _ht
      rw [Pi.add_apply, canonicalPhaseTailOddRealProfile_sub,
        canonicalPhaseLowMode200ShiftOddRealProfile_eq_zero,
        Pi.sub_apply, Pi.zero_apply, sub_zero]
      rfl) a b
  have himag := factorTwoEndpointChannelPhase_congr_Icc
    (u := factorTwoBoundaryCanonicalEvenLowProfile
        (canonicalPhaseLowEvenCoefficients 0) +
      canonicalPhaseTailEvenImagProfile
        (x - canonicalPhaseLowMode200ShiftCore c))
    (u' := canonicalPhaseTailEvenImagProfile x)
    (v := factorTwoOddLowSynthesis
        (canonicalPhaseLowOddCoefficients 0) +
      canonicalPhaseTailOddImagProfile
        (x - canonicalPhaseLowMode200ShiftCore c))
    (v' := canonicalPhaseTailOddImagProfile x)
    (by
      intro t ht
      rw [Pi.add_apply,
        factorTwoBoundaryCanonicalEvenLowProfile_eq_canonical_Icc _ ht,
        canonicalPhaseTailEvenImagProfile_sub,
        canonicalPhaseLowMode200ShiftEvenImagProfile_eq_zero,
        Pi.sub_apply, Pi.zero_apply, sub_zero]
      classical
      simp [factorTwoCanonicalEvenLowSynthesis,
        canonicalPhaseLowEvenCoefficients])
    (by
      intro t _ht
      rw [Pi.add_apply, canonicalPhaseTailOddImagProfile_sub,
        canonicalPhaseLowMode200ShiftOddImagProfile_eq_zero,
        Pi.sub_apply, Pi.zero_apply, sub_zero]
      classical
      simp [factorTwoOddLowSynthesis, canonicalPhaseLowOddCoefficients]) a b
  unfold canonicalPhasePhysicalLowTailValue
  rw [hreal, himag]

private theorem completedCanonicalPhaseTailBilinear_sub_self
    (r s : CanonicalPhaseTailCompletion) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    completedCanonicalPhaseTailBilinear a b hphase (r - s) (r - s) =
      completedCanonicalPhaseTailBilinear a b hphase r r -
        2 * completedCanonicalPhaseTailBilinear a b hphase s r +
        completedCanonicalPhaseTailBilinear a b hphase s s := by
  have hsymm := completedCanonicalPhaseTailBilinear_symm
    a b hphase r s
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [hsymm]
  ring

/-- Exact full Schur quadratic after the endpoint shear, before making any
estimate: concrete low energy plus twice the adapted aggregate functional
plus the unchanged complete tail energy. -/
theorem canonicalPhaseLowTailSchurQuadratic_sub_mode200Shift
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    canonicalPhaseLowTailSchurQuadratic c 0
        (x - canonicalPhaseLowMode200ShiftCore c) a b hphase =
      c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c) +
        2 * (∑ k, c k *
          completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
            k a b hphase (x : CanonicalPhaseTailCompletion)) +
        completedCanonicalPhaseTailBilinear a b hphase
          (x : CanonicalPhaseTailCompletion)
          (x : CanonicalPhaseTailCompletion) := by
  have hlow := factorTwoConcreteLowPhaseMatrix_quadratic_eq_canonical_shear
    c a b hphase
  have hadapt := sum_completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
    c a b hphase (x : CanonicalPhaseTailCompletion)
  have hfunctionalSub :
      (∑ k, c k *
        completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase
          ((x - canonicalPhaseLowMode200ShiftCore c :
            CanonicalPhaseTailCore) : CanonicalPhaseTailCompletion)) =
        (∑ k, c k *
          completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase
            (x : CanonicalPhaseTailCompletion)) -
          ∑ k, c k *
            completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase
              (canonicalPhaseLowMode200Shift c) := by
    rw [UniformSpace.Completion.coe_sub]
    unfold canonicalPhaseLowMode200Shift
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_sub, mul_sub]
  have htailSub :
      completedCanonicalPhaseTailBilinear a b hphase
          ((x - canonicalPhaseLowMode200ShiftCore c :
            CanonicalPhaseTailCore) : CanonicalPhaseTailCompletion)
          ((x - canonicalPhaseLowMode200ShiftCore c :
            CanonicalPhaseTailCore) : CanonicalPhaseTailCompletion) =
        completedCanonicalPhaseTailBilinear a b hphase
            (x : CanonicalPhaseTailCompletion)
            (x : CanonicalPhaseTailCompletion) -
          2 * completedCanonicalPhaseTailBilinear a b hphase
            (canonicalPhaseLowMode200Shift c)
            (x : CanonicalPhaseTailCompletion) +
          completedCanonicalPhaseTailBilinear a b hphase
            (canonicalPhaseLowMode200Shift c)
            (canonicalPhaseLowMode200Shift c) := by
    rw [UniformSpace.Completion.coe_sub]
    exact completedCanonicalPhaseTailBilinear_sub_self
      (x : CanonicalPhaseTailCompletion)
      (canonicalPhaseLowMode200Shift c) a b hphase
  unfold canonicalPhaseLowTailSchurQuadratic
  dsimp only
  rw [canonicalPhaseLowRealImagMatrix_quadratic]
  rw [completedCanonicalPhaseLowRealImagFunctional_sum]
  simp only [zero_dotProduct, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero]
  linear_combination -hlow + 2 * hfunctionalSub - 2 * hadapt + htailSub

/-- On the dense canonical tail core, the aggregate adapted functional is
literally the physical low--tail mixed block of the endpoint-adapted finite
profile.  This is the exact bridge from the abstract Schur certificate back
to the factor-two channel. -/
theorem completedCanonicalPhaseAdaptedLowTailRealFunctional_sum_coe
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    ∑ k, c k *
        completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
          k a b hphase (x : CanonicalPhaseTailCompletion) =
      factorTwoEndpointLowTailMixed
        (factorTwoAdaptedEvenLowSynthesis
          (canonicalPhaseLowEvenCoefficients c))
        (canonicalPhaseTailEvenRealProfile x)
        (factorTwoOddLowSynthesis
          (canonicalPhaseLowOddCoefficients c))
        (canonicalPhaseTailOddRealProfile x) a b := by
  have hassembly := canonicalPhasePhysicalLowTailValue_eq_schurQuadratic
    c 0 (x - canonicalPhaseLowMode200ShiftCore c) a b hphase
  unfold CanonicalPhasePhysicalLowTailAssembly at hassembly
  have hphysical :=
    canonicalPhasePhysicalLowTailValue_sub_mode200Shift_eq_adapted
      c x a b
  have hschur := canonicalPhaseLowTailSchurQuadratic_sub_mode200Shift
    c x a b hphase
  have hfull :
      factorTwoEndpointChannelPhase
          (factorTwoAdaptedEvenLowSynthesis
              (canonicalPhaseLowEvenCoefficients c) +
            canonicalPhaseTailEvenRealProfile x)
          (factorTwoOddLowSynthesis
              (canonicalPhaseLowOddCoefficients c) +
            canonicalPhaseTailOddRealProfile x) a b +
        factorTwoEndpointChannelPhase
          (canonicalPhaseTailEvenImagProfile x)
          (canonicalPhaseTailOddImagProfile x) a b =
      c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c) +
        2 * (∑ k, c k *
          completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
            k a b hphase (x : CanonicalPhaseTailCompletion)) +
        completedCanonicalPhaseTailBilinear a b hphase
          (x : CanonicalPhaseTailCompletion)
          (x : CanonicalPhaseTailCompletion) := by
    calc
      _ = canonicalPhasePhysicalLowTailValue c 0
          (x - canonicalPhaseLowMode200ShiftCore c) a b := hphysical.symm
      _ = canonicalPhaseLowTailSchurQuadratic c 0
          (x - canonicalPhaseLowMode200ShiftCore c) a b hphase := hassembly
      _ = _ := hschur
  have hdecomp := factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
    (factorTwoAdaptedEvenLowSynthesis
      (canonicalPhaseLowEvenCoefficients c))
    (canonicalPhaseTailEvenRealProfile x)
    (factorTwoOddLowSynthesis (canonicalPhaseLowOddCoefficients c))
    (canonicalPhaseTailOddRealProfile x)
    (continuous_factorTwoAdaptedEvenLowSynthesis
      (canonicalPhaseLowEvenCoefficients c))
    (continuous_boundaryCanonicalEvenTailProfile
      (evenTailRealPart x.fst.toV))
    (continuous_factorTwoOddLowSynthesis
      (canonicalPhaseLowOddCoefficients c))
    (continuous_canonicalOddTailProfile (oddTailRealPart x.snd.toV)) a b
  have hlow := factorTwoConcreteLowPhaseMatrix_represents
    (canonicalPhaseLowEvenCoefficients c)
    (canonicalPhaseLowOddCoefficients c) a b
  simp only [factorTwoPhaseLowCoefficients_unpacked] at hlow
  rw [hdecomp, hlow,
    completedCanonicalPhaseTailBilinear_coe_self_eq_physical] at hfull
  linarith

/-- Exact remaining certificate after the endpoint shear: the concrete low
quadratic must dominate the square of the *aggregate* adapted functional in
the full completed tail metric.  No rowwise norm or diagonal budget appears. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_adapted_functional_sq
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    Matrix.PosSemidef
        (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) ↔
      ∀ c : FactorTwoPhaseLowIndex → ℝ,
        0 ≤ c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c) ∧
          ∀ z : CanonicalPhaseTailCompletion,
            (∑ k, c k *
              completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
                k a b hphase z) ^ 2 ≤
              (c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c)) *
                completedCanonicalPhaseTailBilinear a b hphase z z := by
  rw [completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_sum_endpointAdapted_energy]
  constructor
  · intro henergy c
    apply (coerciveBilinear_aggregateRiesz_energy_le_iff_functional_sq
      (completedCanonicalPhaseTailBilinear a b hphase)
      (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
      (completedCanonicalPhaseTailBilinear_symm a b hphase)
      (fun k ↦ completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
        k a b hphase) c
      (c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c))).mp
    simpa only [coerciveRieszCorrection_adaptedLowBasisTailRealFunctional]
      using henergy c
  · intro hfunctional c
    have henergy :=
      (coerciveBilinear_aggregateRiesz_energy_le_iff_functional_sq
        (completedCanonicalPhaseTailBilinear a b hphase)
        (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
        (completedCanonicalPhaseTailBilinear_symm a b hphase)
        (fun k ↦ completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
          k a b hphase) c
        (c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c))).mpr
        (hfunctional c)
    simpa only [coerciveRieszCorrection_adaptedLowBasisTailRealFunctional]
      using henergy

/-- Fully physical form of the remaining corrected-Gram certificate.  The
abstract completion can be eliminated: on the dense canonical core the
aggregate functional is the literal adapted low--tail mixed block and the
bilinear diagonal is the sum of the two physical tail-channel phases. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_physical_mixed_sq
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    Matrix.PosSemidef
        (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) ↔
      ∀ c : FactorTwoPhaseLowIndex → ℝ,
        0 ≤ c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c) ∧
          ∀ x : CanonicalPhaseTailCore,
            factorTwoEndpointLowTailMixed
                (factorTwoAdaptedEvenLowSynthesis
                  (canonicalPhaseLowEvenCoefficients c))
                (canonicalPhaseTailEvenRealProfile x)
                (factorTwoOddLowSynthesis
                  (canonicalPhaseLowOddCoefficients c))
                (canonicalPhaseTailOddRealProfile x) a b ^ 2 ≤
              (c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c)) *
                (factorTwoEndpointChannelPhase
                    (canonicalPhaseTailEvenRealProfile x)
                    (canonicalPhaseTailOddRealProfile x) a b +
                  factorTwoEndpointChannelPhase
                    (canonicalPhaseTailEvenImagProfile x)
                    (canonicalPhaseTailOddImagProfile x) a b) := by
  rw [completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_adapted_functional_sq]
  constructor
  · intro hfunctional c
    refine ⟨(hfunctional c).1, ?_⟩
    intro x
    have hx := (hfunctional c).2 (x : CanonicalPhaseTailCompletion)
    rw [completedCanonicalPhaseAdaptedLowTailRealFunctional_sum_coe,
      completedCanonicalPhaseTailBilinear_coe_self_eq_physical] at hx
    exact hx
  · intro hphysical c
    refine ⟨(hphysical c).1, ?_⟩
    intro z
    refine UniformSpace.Completion.induction_on z
      (isClosed_le (by fun_prop) (by fun_prop)) ?_
    intro x
    have hx := (hphysical c).2 x
    rw [completedCanonicalPhaseAdaptedLowTailRealFunctional_sum_coe,
      completedCanonicalPhaseTailBilinear_coe_self_eq_physical]
    exact hx

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailEndpointAdaptedFunctionalStructural
