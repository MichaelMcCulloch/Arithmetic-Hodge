import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailBoundaryReductionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailAssemblyStructural

set_option autoImplicit false
set_option maxHeartbeats 800000

open Complex Matrix Real
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailCircleSymmetryStructural

noncomputable section

open ArithmeticHodge.Analysis
open FormSpace
open YoshidaEndpointScaledCorrelation
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailBoundaryReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionEnergyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailQuarterTurnStructural
open YoshidaFactorTwoPhaseCanonicalLowTailRieszStructural
open YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseCanonicalTailDiagonalStructural
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddRealDecomposition
open YoshidaFactorTwoPhaseTailRealImagLinearStructural
open YoshidaFactorTwoPhaseTailRealImagStructural

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

/-!
# Reflection symmetry of the canonical phase-circle Schur block

Changing `b` to `-b` is implemented by negating every odd low coordinate and
the odd completed-tail component.  The finite matrix, completed tail form,
mixed functionals, Riesz corrections, and corrected Gram all respect this
involution.  Consequently the circle PSD obligation reduces exactly to one
closed semicircle.
-/

/-- Sign of a canonical finite-low coordinate under the even--odd parity
involution. -/
def canonicalPhaseLowParitySign : FactorTwoPhaseLowIndex → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

@[simp] theorem canonicalPhaseLowParitySign_sq
    (k : FactorTwoPhaseLowIndex) :
    canonicalPhaseLowParitySign k ^ 2 = 1 := by
  cases k <;> norm_num [canonicalPhaseLowParitySign]

/-- Negate precisely the odd finite-low coordinates. -/
def canonicalPhaseLowParityFlip
    (c : FactorTwoPhaseLowIndex → ℝ) : FactorTwoPhaseLowIndex → ℝ :=
  fun k ↦ canonicalPhaseLowParitySign k * c k

/-- The same parity sign acting on the completed tail, written explicitly to
avoid any ambiguity between its real and complex scalar structures. -/
def canonicalPhaseTailParityAction
    (k : FactorTwoPhaseLowIndex) (z : CanonicalPhaseTailCompletion) :
    CanonicalPhaseTailCompletion :=
  match k with
  | Sum.inl _ => z
  | Sum.inr _ => -z

@[simp] theorem canonicalPhaseLowParityFlip_apply
    (c : FactorTwoPhaseLowIndex → ℝ) (k : FactorTwoPhaseLowIndex) :
    canonicalPhaseLowParityFlip c k =
      canonicalPhaseLowParitySign k * c k :=
  rfl

@[simp] theorem canonicalPhaseLowParityFlip_involutive
    (c : FactorTwoPhaseLowIndex → ℝ) :
    canonicalPhaseLowParityFlip (canonicalPhaseLowParityFlip c) = c := by
  funext k
  cases k <;> simp [canonicalPhaseLowParityFlip,
    canonicalPhaseLowParitySign]

/-- Negate precisely the odd algebraic tail component. -/
def canonicalPhaseTailCoreOddFlip
    (x : CanonicalPhaseTailCore) : CanonicalPhaseTailCore :=
  WithLp.toLp 2 (x.fst, -x.snd)

@[simp] theorem canonicalPhaseTailCoreOddFlip_fst
    (x : CanonicalPhaseTailCore) :
    (canonicalPhaseTailCoreOddFlip x).fst = x.fst :=
  rfl

@[simp] theorem canonicalPhaseTailCoreOddFlip_snd
    (x : CanonicalPhaseTailCore) :
    (canonicalPhaseTailCoreOddFlip x).snd = -x.snd :=
  rfl

@[simp] theorem canonicalPhaseTailCoreOddFlip_zero :
    canonicalPhaseTailCoreOddFlip (0 : CanonicalPhaseTailCore) = 0 := by
  apply WithLp.ofLp_injective 2
  ext <;> simp [canonicalPhaseTailCoreOddFlip]

@[simp] theorem canonicalPhaseTailCoreOddFlip_add
    (x y : CanonicalPhaseTailCore) :
    canonicalPhaseTailCoreOddFlip (x + y) =
      canonicalPhaseTailCoreOddFlip x + canonicalPhaseTailCoreOddFlip y := by
  apply WithLp.ofLp_injective 2
  ext
  · simp [canonicalPhaseTailCoreOddFlip]
  · change -(x.snd + y.snd) = -x.snd + -y.snd
    abel

@[simp] theorem canonicalPhaseTailCoreOddFlip_involutive
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailCoreOddFlip (canonicalPhaseTailCoreOddFlip x) = x := by
  apply WithLp.ofLp_injective 2
  ext <;> simp [canonicalPhaseTailCoreOddFlip]

@[simp] theorem norm_canonicalPhaseTailCoreOddFlip
    (x : CanonicalPhaseTailCore) :
    ‖canonicalPhaseTailCoreOddFlip x‖ = ‖x‖ := by
  rw [WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
  simp [canonicalPhaseTailCoreOddFlip]

@[simp] theorem canonicalPhaseTailEvenRealProfile_oddFlip
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenRealProfile (canonicalPhaseTailCoreOddFlip x) =
      canonicalPhaseTailEvenRealProfile x :=
  rfl

@[simp] theorem canonicalPhaseTailEvenImagProfile_oddFlip
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailEvenImagProfile (canonicalPhaseTailCoreOddFlip x) =
      canonicalPhaseTailEvenImagProfile x :=
  rfl

@[simp] theorem canonicalPhaseTailOddRealProfile_oddFlip
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailOddRealProfile (canonicalPhaseTailCoreOddFlip x) =
      -canonicalPhaseTailOddRealProfile x := by
  let y : CanonicalPhaseTailCore := WithLp.toLp 2 (0, x.snd)
  have h := canonicalPhaseTailOddRealProfile_smul (-1) y
  simpa only [y, canonicalPhaseTailCoreOddFlip, neg_one_smul] using h

@[simp] theorem canonicalPhaseTailOddImagProfile_oddFlip
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailOddImagProfile (canonicalPhaseTailCoreOddFlip x) =
      -canonicalPhaseTailOddImagProfile x := by
  let y : CanonicalPhaseTailCore := WithLp.toLp 2 (0, x.snd)
  have h := canonicalPhaseTailOddImagProfile_smul (-1) y
  simpa only [y, canonicalPhaseTailCoreOddFlip, neg_one_smul] using h

private theorem factorTwoCenteredCleanPolarization_neg_neg
    (u v : ℝ → ℝ) :
    factorTwoCenteredCleanPolarization (-u) (-v) =
      factorTwoCenteredCleanPolarization u v := by
  have hadd : (-u) + (-v) = -(u + v) := by
    funext x
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  have hneg (w : ℝ → ℝ) :
      yoshidaEndpointOddCleanQuadratic (-w) =
        yoshidaEndpointOddCleanQuadratic w := by
    have h := yoshidaEndpointOddCleanQuadratic_const_mul w (-1)
    change yoshidaEndpointOddCleanQuadratic (fun x ↦ -w x) = _
    norm_num at h
    exact h
  unfold factorTwoCenteredCleanPolarization
  rw [hadd, hneg, hneg, hneg]

private theorem factorTwoCenteredSymmetricPerturbationBilinear_neg_neg
    (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear (-u) (-v) =
      factorTwoCenteredSymmetricPerturbationBilinear u v := by
  have h := factorTwoCenteredSymmetricPerturbationBilinear_smul_smul
    (-1) (-1) u v
  norm_num at h
  simpa only [neg_one_smul] using h

private theorem factorTwoCenteredAlternatingCoupling_neg_right
    (u v : ℝ → ℝ) :
    factorTwoCenteredAlternatingCoupling u (-v) =
      -factorTwoCenteredAlternatingCoupling u v := by
  simpa only [neg_one_smul, neg_one_mul] using
    (factorTwoCenteredAlternatingCoupling_smul_right (-1) u v)

/-- Exact covariance of the mixed phase block when both odd inputs and the
alternating phase coordinate change sign. -/
theorem factorTwoEndpointLowTailMixed_odd_neg_phase_neg
    (uLow uTail vLow vTail : ℝ → ℝ) (a b : ℝ) :
    factorTwoEndpointLowTailMixed
        uLow uTail (-vLow) (-vTail) a (-b) =
      factorTwoEndpointLowTailMixed uLow uTail vLow vTail a b := by
  unfold factorTwoEndpointLowTailMixed
  rw [factorTwoCenteredCleanPolarization_neg_neg,
    factorTwoCenteredSymmetricPerturbationBilinear_neg_neg,
    factorTwoCenteredAlternatingCoupling_neg_right,
    factorTwoCenteredAlternatingCoupling_neg_right]
  ring

/-- The algebraic canonical tail bilinear is equivariant under odd-tail and
`b` reflection. -/
theorem canonicalPhaseTailCoreBilinearValue_oddFlip_neg_b
    (x y : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhaseTailCoreBilinearValue
        (canonicalPhaseTailCoreOddFlip x)
        (canonicalPhaseTailCoreOddFlip y) a (-b) =
      canonicalPhaseTailCoreBilinearValue x y a b := by
  unfold canonicalPhaseTailCoreBilinearValue
  rw [canonicalPhaseTailEvenRealProfile_oddFlip,
    canonicalPhaseTailEvenRealProfile_oddFlip,
    canonicalPhaseTailOddRealProfile_oddFlip,
    canonicalPhaseTailOddRealProfile_oddFlip,
    canonicalPhaseTailEvenImagProfile_oddFlip,
    canonicalPhaseTailEvenImagProfile_oddFlip,
    canonicalPhaseTailOddImagProfile_oddFlip,
    canonicalPhaseTailOddImagProfile_oddFlip,
    factorTwoEndpointLowTailMixed_odd_neg_phase_neg,
    factorTwoEndpointLowTailMixed_odd_neg_phase_neg]

/-- Algebraic odd-tail reflection as a bounded additive map into the
canonical completion. -/
def canonicalPhaseTailCoreOddFlipNormedAddGroupHom :
    NormedAddGroupHom CanonicalPhaseTailCore CanonicalPhaseTailCompletion where
  toFun := fun x ↦
    (canonicalPhaseTailCoreOddFlip x : CanonicalPhaseTailCompletion)
  map_add' := fun x y ↦ by
    rw [canonicalPhaseTailCoreOddFlip_add,
      UniformSpace.Completion.coe_add]
  bound' := ⟨1, fun x ↦ by
    simpa only [UniformSpace.Completion.norm_coe,
      norm_canonicalPhaseTailCoreOddFlip, one_mul] using (le_refl ‖x‖)⟩

/-- Continuous odd-tail reflection on the canonical completion. -/
noncomputable def canonicalPhaseTailCompletionOddFlip :
    CanonicalPhaseTailCompletion → CanonicalPhaseTailCompletion :=
  canonicalPhaseTailCoreOddFlipNormedAddGroupHom.extension

@[simp] theorem canonicalPhaseTailCompletionOddFlip_coe
    (x : CanonicalPhaseTailCore) :
    canonicalPhaseTailCompletionOddFlip
        (x : CanonicalPhaseTailCompletion) =
      (canonicalPhaseTailCoreOddFlip x : CanonicalPhaseTailCompletion) := by
  exact NormedAddGroupHom.extension_coe
    canonicalPhaseTailCoreOddFlipNormedAddGroupHom x

theorem continuous_canonicalPhaseTailCompletionOddFlip :
    Continuous canonicalPhaseTailCompletionOddFlip :=
  canonicalPhaseTailCoreOddFlipNormedAddGroupHom.extension.continuous

@[simp] theorem canonicalPhaseTailCompletionOddFlip_add
    (z w : CanonicalPhaseTailCompletion) :
    canonicalPhaseTailCompletionOddFlip (z + w) =
      canonicalPhaseTailCompletionOddFlip z +
        canonicalPhaseTailCompletionOddFlip w :=
  canonicalPhaseTailCoreOddFlipNormedAddGroupHom.extension.map_add' z w

@[simp] theorem canonicalPhaseTailCompletionOddFlip_neg
    (z : CanonicalPhaseTailCompletion) :
    canonicalPhaseTailCompletionOddFlip (-z) =
      -canonicalPhaseTailCompletionOddFlip z := by
  exact map_neg canonicalPhaseTailCoreOddFlipNormedAddGroupHom.extension z

@[simp] theorem canonicalPhaseTailCompletionOddFlip_involutive
    (z : CanonicalPhaseTailCompletion) :
    canonicalPhaseTailCompletionOddFlip
        (canonicalPhaseTailCompletionOddFlip z) = z := by
  have heq :
      (fun w : CanonicalPhaseTailCompletion ↦
        canonicalPhaseTailCompletionOddFlip
          (canonicalPhaseTailCompletionOddFlip w)) = id := by
    apply UniformSpace.Completion.denseRange_coe.equalizer
    · exact continuous_canonicalPhaseTailCompletionOddFlip.comp
        continuous_canonicalPhaseTailCompletionOddFlip
    · exact continuous_id
    · funext x
      calc
        canonicalPhaseTailCompletionOddFlip
            (canonicalPhaseTailCompletionOddFlip
              (x : CanonicalPhaseTailCompletion)) =
          canonicalPhaseTailCompletionOddFlip
            (canonicalPhaseTailCoreOddFlip x :
              CanonicalPhaseTailCompletion) := by
            rw [canonicalPhaseTailCompletionOddFlip_coe]
        _ = (canonicalPhaseTailCoreOddFlip
              (canonicalPhaseTailCoreOddFlip x) :
              CanonicalPhaseTailCompletion) :=
          canonicalPhaseTailCompletionOddFlip_coe
            (canonicalPhaseTailCoreOddFlip x)
        _ = (x : CanonicalPhaseTailCompletion) := by
          rw [canonicalPhaseTailCoreOddFlip_involutive]
        _ = id (x : CanonicalPhaseTailCompletion) := rfl
  exact congrFun heq z

/-- Completed tail covariance under odd-tail and `b` reflection. -/
theorem completedCanonicalPhaseTailBilinear_oddFlip_neg_b
    (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hneg : a ^ 2 + (-b) ^ 2 ≤ 1)
    (z w : CanonicalPhaseTailCompletion) :
    completedCanonicalPhaseTailBilinear a (-b) hneg
        (canonicalPhaseTailCompletionOddFlip z)
        (canonicalPhaseTailCompletionOddFlip w) =
      completedCanonicalPhaseTailBilinear a b hphase z w := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq
      (((completedCanonicalPhaseTailBilinear a (-b) hneg).continuous.comp
        continuous_canonicalPhaseTailCompletionOddFlip).clm_apply
          (continuous_canonicalPhaseTailCompletionOddFlip.comp
            continuous_const))
      ((completedCanonicalPhaseTailBilinear a b hphase).continuous.clm_apply
        continuous_const)) ?_
  intro x
  refine UniformSpace.Completion.induction_on w
    (isClosed_eq
      ((completedCanonicalPhaseTailBilinear a (-b) hneg
        (canonicalPhaseTailCompletionOddFlip
          (x : CanonicalPhaseTailCompletion))).continuous.comp
            continuous_canonicalPhaseTailCompletionOddFlip)
      (completedCanonicalPhaseTailBilinear a b hphase
        (x : CanonicalPhaseTailCompletion)).continuous) ?_
  intro y
  simp only [canonicalPhaseTailCompletionOddFlip_coe,
    completedCanonicalPhaseTailBilinear_coe_coe]
  exact canonicalPhaseTailCoreBilinearValue_oddFlip_neg_b x y a b

@[simp] theorem canonicalPhaseLowEvenCoefficients_parityFlip
    (c : FactorTwoPhaseLowIndex → ℝ) :
    canonicalPhaseLowEvenCoefficients (canonicalPhaseLowParityFlip c) =
      canonicalPhaseLowEvenCoefficients c := by
  ext i
  simp [canonicalPhaseLowEvenCoefficients, canonicalPhaseLowParityFlip,
    canonicalPhaseLowParitySign]

@[simp] theorem canonicalPhaseLowOddCoefficients_parityFlip
    (c : FactorTwoPhaseLowIndex → ℝ) :
    canonicalPhaseLowOddCoefficients (canonicalPhaseLowParityFlip c) =
      -canonicalPhaseLowOddCoefficients c := by
  ext i
  simp [canonicalPhaseLowOddCoefficients, canonicalPhaseLowParityFlip,
    canonicalPhaseLowParitySign]

private theorem factorTwoOddLowSynthesis_neg
    (o : YoshidaOddIndex → ℝ) :
    factorTwoOddLowSynthesis (-o) = -factorTwoOddLowSynthesis o := by
  classical
  unfold factorTwoOddLowSynthesis
  simp

/-- The physical real low--tail mixed block is invariant when the odd low
coordinates, odd tail, and `b` all change sign. -/
theorem canonicalPhaseLowTailRealMixed_parityFlip_oddFlip_neg_b
    (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore)
    (a b : ℝ) :
    canonicalPhaseLowTailRealMixed
        (canonicalPhaseLowParityFlip c)
        (canonicalPhaseTailCoreOddFlip x) a (-b) =
      canonicalPhaseLowTailRealMixed c x a b := by
  unfold canonicalPhaseLowTailRealMixed
  rw [canonicalPhaseLowEvenCoefficients_parityFlip,
    canonicalPhaseLowOddCoefficients_parityFlip,
    factorTwoOddLowSynthesis_neg,
    canonicalPhaseTailEvenRealProfile_oddFlip,
    canonicalPhaseTailOddRealProfile_oddFlip]
  exact factorTwoEndpointLowTailMixed_odd_neg_phase_neg _ _ _ _ a b

@[simp] theorem canonicalPhaseLowParityFlip_single
    (k : FactorTwoPhaseLowIndex) :
    canonicalPhaseLowParityFlip
        (Pi.single k 1 : FactorTwoPhaseLowIndex → ℝ) =
      canonicalPhaseLowParitySign k •
        (Pi.single k 1 : FactorTwoPhaseLowIndex → ℝ) := by
  classical
  ext q
  rcases k with k | k <;> rcases q with q | q <;>
    simp [canonicalPhaseLowParityFlip, canonicalPhaseLowParitySign,
      Pi.single_apply]

@[simp] theorem canonicalPhaseLowTailRealMixed_single
    (k : FactorTwoPhaseLowIndex) (x : CanonicalPhaseTailCore)
    (a b : ℝ) :
    canonicalPhaseLowTailRealMixed
        (Pi.single k 1 : FactorTwoPhaseLowIndex → ℝ) x a b =
      canonicalPhaseLowBasisTailRealMixedValue k x a b := by
  classical
  rw [canonicalPhaseLowTailRealMixed_eq_sum]
  cases k <;> simp [Pi.single_apply]

/-- Algebraic real-coordinate basis functionals transform by the matching
finite-low parity sign. -/
theorem canonicalPhaseLowBasisTailRealMixedValue_oddFlip_neg_b
    (k : FactorTwoPhaseLowIndex) (x : CanonicalPhaseTailCore)
    (a b : ℝ) :
    canonicalPhaseLowBasisTailRealMixedValue k
        (canonicalPhaseTailCoreOddFlip x) a (-b) =
      canonicalPhaseLowParitySign k *
        canonicalPhaseLowBasisTailRealMixedValue k x a b := by
  have h := canonicalPhaseLowTailRealMixed_parityFlip_oddFlip_neg_b
    (Pi.single k 1 : FactorTwoPhaseLowIndex → ℝ) x a b
  rw [canonicalPhaseLowParityFlip_single,
    canonicalPhaseLowTailRealMixed_smul,
    canonicalPhaseLowTailRealMixed_single,
    canonicalPhaseLowTailRealMixed_single] at h
  cases k with
  | inl k =>
      simpa [canonicalPhaseLowParitySign] using h
  | inr k =>
      simp only [canonicalPhaseLowParitySign] at h ⊢
      linarith

/-- Completed real-coordinate functionals obey the same parity covariance. -/
theorem completedCanonicalPhaseLowBasisTailRealFunctional_oddFlip_neg_b
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hneg : a ^ 2 + (-b) ^ 2 ≤ 1)
    (z : CanonicalPhaseTailCompletion) :
    completedCanonicalPhaseLowBasisTailRealFunctional
        k a (-b) hneg (canonicalPhaseTailCompletionOddFlip z) =
      canonicalPhaseLowParitySign k *
        completedCanonicalPhaseLowBasisTailRealFunctional
          k a b hphase z := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq
      ((completedCanonicalPhaseLowBasisTailRealFunctional
        k a (-b) hneg).continuous.comp
          continuous_canonicalPhaseTailCompletionOddFlip)
      (continuous_const.mul
        (completedCanonicalPhaseLowBasisTailRealFunctional
          k a b hphase).continuous)) ?_
  intro x
  simp only [canonicalPhaseTailCompletionOddFlip_coe,
    completedCanonicalPhaseLowBasisTailRealFunctional_coe]
  exact canonicalPhaseLowBasisTailRealMixedValue_oddFlip_neg_b k x a b

private theorem eq_of_completedCanonicalPhaseTailBilinear_apply_eq
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    {x y : CanonicalPhaseTailCompletion}
    (h : ∀ z, completedCanonicalPhaseTailBilinear a b hphase x z =
      completedCanonicalPhaseTailBilinear a b hphase y z) :
    x = y := by
  let hB := completedCanonicalPhaseTailBilinear_isCoercive a b hphase
  apply hB.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro z
  rw [hB.continuousLinearEquivOfBilin_apply,
    hB.continuousLinearEquivOfBilin_apply]
  exact h z

/-- Odd-tail reflection sends each phase-`b` Riesz representative to the
parity-signed phase-`-b` representative. -/
theorem canonicalPhaseTailCompletionOddFlip_realRieszCorrection_neg_b
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hneg : a ^ 2 + (-b) ^ 2 ≤ 1) :
    canonicalPhaseTailCompletionOddFlip
        (canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase) =
      canonicalPhaseTailParityAction k
        (canonicalPhaseLowBasisTailRealRieszCorrection k a (-b) hneg) := by
  apply eq_of_completedCanonicalPhaseTailBilinear_apply_eq a (-b) hneg
  intro z
  let r := canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase
  let rneg := canonicalPhaseLowBasisTailRealRieszCorrection
    k a (-b) hneg
  have hfun :=
    completedCanonicalPhaseLowBasisTailRealFunctional_oddFlip_neg_b
      k a b hphase hneg (canonicalPhaseTailCompletionOddFlip z)
  rw [canonicalPhaseTailCompletionOddFlip_involutive] at hfun
  have hfun' :
      completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase
          (canonicalPhaseTailCompletionOddFlip z) =
        canonicalPhaseLowParitySign k *
          completedCanonicalPhaseLowBasisTailRealFunctional
            k a (-b) hneg z := by
    cases k with
    | inl k =>
        simpa [canonicalPhaseLowParitySign] using hfun.symm
    | inr k =>
        simp only [canonicalPhaseLowParitySign] at hfun ⊢
        linarith
  change completedCanonicalPhaseTailBilinear a (-b) hneg
      (canonicalPhaseTailCompletionOddFlip r) z =
    completedCanonicalPhaseTailBilinear a (-b) hneg
      (canonicalPhaseTailParityAction k rneg) z
  calc
    completedCanonicalPhaseTailBilinear a (-b) hneg
        (canonicalPhaseTailCompletionOddFlip r) z =
      completedCanonicalPhaseTailBilinear a (-b) hneg
        (canonicalPhaseTailCompletionOddFlip r)
        (canonicalPhaseTailCompletionOddFlip
          (canonicalPhaseTailCompletionOddFlip z)) := by
      rw [canonicalPhaseTailCompletionOddFlip_involutive]
    _ = completedCanonicalPhaseTailBilinear a b hphase r
        (canonicalPhaseTailCompletionOddFlip z) :=
      completedCanonicalPhaseTailBilinear_oddFlip_neg_b
        a b hphase hneg r (canonicalPhaseTailCompletionOddFlip z)
    _ = completedCanonicalPhaseLowBasisTailRealFunctional
        k a b hphase (canonicalPhaseTailCompletionOddFlip z) :=
      completedCanonicalPhaseTailBilinear_realRieszCorrection_apply
        k a b hphase (canonicalPhaseTailCompletionOddFlip z)
    _ = canonicalPhaseLowParitySign k *
        completedCanonicalPhaseLowBasisTailRealFunctional
          k a (-b) hneg z := hfun'
    _ = canonicalPhaseLowParitySign k *
        completedCanonicalPhaseTailBilinear a (-b) hneg rneg z := by
      rw [completedCanonicalPhaseTailBilinear_realRieszCorrection_apply]
    _ = completedCanonicalPhaseTailBilinear a (-b) hneg
        (canonicalPhaseTailParityAction k rneg) z := by
      cases k <;>
        simp [canonicalPhaseLowParitySign, canonicalPhaseTailParityAction]

/-- Inverse form of the Riesz covariance. -/
theorem canonicalPhaseLowBasisTailRealRieszCorrection_neg_b_eq
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hneg : a ^ 2 + (-b) ^ 2 ≤ 1) :
    canonicalPhaseLowBasisTailRealRieszCorrection k a (-b) hneg =
      canonicalPhaseTailParityAction k
        (canonicalPhaseTailCompletionOddFlip
          (canonicalPhaseLowBasisTailRealRieszCorrection
            k a b hphase)) := by
  have h :=
    canonicalPhaseTailCompletionOddFlip_realRieszCorrection_neg_b
      k a b hphase hneg
  cases k with
  | inl k =>
      change canonicalPhaseLowBasisTailRealRieszCorrection
          (Sum.inl k) a (-b) hneg =
        canonicalPhaseTailCompletionOddFlip
          (canonicalPhaseLowBasisTailRealRieszCorrection
            (Sum.inl k) a b hphase)
      change canonicalPhaseTailCompletionOddFlip
          (canonicalPhaseLowBasisTailRealRieszCorrection
            (Sum.inl k) a b hphase) =
        canonicalPhaseLowBasisTailRealRieszCorrection
          (Sum.inl k) a (-b) hneg at h
      exact h.symm
  | inr k =>
      change canonicalPhaseLowBasisTailRealRieszCorrection
          (Sum.inr k) a (-b) hneg =
        -canonicalPhaseTailCompletionOddFlip
          (canonicalPhaseLowBasisTailRealRieszCorrection
            (Sum.inr k) a b hphase)
      change canonicalPhaseTailCompletionOddFlip
          (canonicalPhaseLowBasisTailRealRieszCorrection
            (Sum.inr k) a b hphase) =
        -canonicalPhaseLowBasisTailRealRieszCorrection
          (Sum.inr k) a (-b) hneg at h
      simpa only [neg_neg] using (congrArg Neg.neg h).symm

/-- The finite canonical low matrix is congruent under the low parity sign
when `b` is reflected. -/
theorem canonicalPhaseLowMatrix_neg_b
    (a b : ℝ) (k l : FactorTwoPhaseLowIndex) :
    canonicalPhaseLowMatrix a (-b) k l =
      canonicalPhaseLowParitySign k * canonicalPhaseLowParitySign l *
        canonicalPhaseLowMatrix a b k l := by
  rcases k with k | k <;> rcases l with l | l <;>
    simp [canonicalPhaseLowMatrix, factorTwoFiniteLowPhaseMatrix,
      factorTwoPhaseBlockMatrix, canonicalPhaseLowParitySign] <;> ring

/-- The eliminated tail correction has the same signed congruence. -/
theorem completedCanonicalPhaseTailBilinear_realRieszCorrection_neg_b
    (k l : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hneg : a ^ 2 + (-b) ^ 2 ≤ 1) :
    completedCanonicalPhaseTailBilinear a (-b) hneg
        (canonicalPhaseLowBasisTailRealRieszCorrection k a (-b) hneg)
        (canonicalPhaseLowBasisTailRealRieszCorrection l a (-b) hneg) =
      canonicalPhaseLowParitySign k * canonicalPhaseLowParitySign l *
        completedCanonicalPhaseTailBilinear a b hphase
          (canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase)
          (canonicalPhaseLowBasisTailRealRieszCorrection l a b hphase) := by
  rw [canonicalPhaseLowBasisTailRealRieszCorrection_neg_b_eq
      k a b hphase hneg,
    canonicalPhaseLowBasisTailRealRieszCorrection_neg_b_eq
      l a b hphase hneg]
  have hcov := completedCanonicalPhaseTailBilinear_oddFlip_neg_b
    a b hphase hneg
    (canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase)
    (canonicalPhaseLowBasisTailRealRieszCorrection l a b hphase)
  rcases k with k | k <;> rcases l with l | l <;>
    simp [canonicalPhaseTailParityAction, canonicalPhaseLowParitySign,
      hcov]

/-- Exact entrywise congruence of the reduced corrected Gram under
`b ↦ -b`. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_neg_b
    (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hneg : a ^ 2 + (-b) ^ 2 ≤ 1)
    (k l : FactorTwoPhaseLowIndex) :
    completedCanonicalPhaseLowTailRealCorrectedGram a (-b) hneg k l =
      canonicalPhaseLowParitySign k * canonicalPhaseLowParitySign l *
        completedCanonicalPhaseLowTailRealCorrectedGram
          a b hphase k l := by
  unfold completedCanonicalPhaseLowTailRealCorrectedGram
  rw [canonicalPhaseLowMatrix_neg_b a b k l,
    completedCanonicalPhaseTailBilinear_realRieszCorrection_neg_b
      k l a b hphase hneg]
  ring

/-- Quadratic-form version of the signed corrected-Gram congruence. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_quadratic_neg_b
    (c : FactorTwoPhaseLowIndex → ℝ) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hneg : a ^ 2 + (-b) ^ 2 ≤ 1) :
    c ⬝ᵥ (completedCanonicalPhaseLowTailRealCorrectedGram
        a (-b) hneg *ᵥ c) =
      canonicalPhaseLowParityFlip c ⬝ᵥ
        (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase *ᵥ
          canonicalPhaseLowParityFlip c) := by
  classical
  simp only [dotProduct, mulVec]
  apply Finset.sum_congr rfl
  intro k _hk
  simp_rw [completedCanonicalPhaseLowTailRealCorrectedGram_neg_b
    a b hphase hneg]
  have hinner :
      (∑ l, canonicalPhaseLowParitySign k *
          canonicalPhaseLowParitySign l *
          completedCanonicalPhaseLowTailRealCorrectedGram a b hphase k l *
          c l) =
        canonicalPhaseLowParitySign k *
          ∑ l, completedCanonicalPhaseLowTailRealCorrectedGram
            a b hphase k l * canonicalPhaseLowParityFlip c l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _hl
    simp only [canonicalPhaseLowParityFlip_apply]
    ring
  rw [hinner]
  simp only [canonicalPhaseLowParityFlip_apply]
  ring

/-- PSD is exactly invariant under reflection across the `a`-axis. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_neg_b_posSemidef_iff
    (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hneg : a ^ 2 + (-b) ^ 2 ≤ 1) :
    Matrix.PosSemidef
        (completedCanonicalPhaseLowTailRealCorrectedGram a (-b) hneg) ↔
      Matrix.PosSemidef
        (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) := by
  constructor
  · intro hnegPSD
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (completedCanonicalPhaseLowTailRealCorrectedGram_isHermitian
        a b hphase)
    intro c
    simp only [star_trivial]
    have hq := hnegPSD.dotProduct_mulVec_nonneg
      (canonicalPhaseLowParityFlip c)
    simp only [star_trivial] at hq
    rw [completedCanonicalPhaseLowTailRealCorrectedGram_quadratic_neg_b,
      canonicalPhaseLowParityFlip_involutive] at hq
    exact hq
  · intro hposPSD
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (completedCanonicalPhaseLowTailRealCorrectedGram_isHermitian
        a (-b) hneg)
    intro c
    simp only [star_trivial]
    rw [completedCanonicalPhaseLowTailRealCorrectedGram_quadratic_neg_b
      c a b hphase hneg]
    exact hposPSD.dotProduct_mulVec_nonneg
      (canonicalPhaseLowParityFlip c)

/-- It is enough to prove the circle certificate on the closed upper
semicircle. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_circle_posSemidef_of_upper
    (hupper : ∀ (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1),
      a ^ 2 + b ^ 2 = 1 → 0 ≤ b →
        Matrix.PosSemidef
          (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase))
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hcircle : a ^ 2 + b ^ 2 = 1) :
    Matrix.PosSemidef
      (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) := by
  by_cases hb : 0 ≤ b
  · exact hupper a b hphase hcircle hb
  · have hneg : a ^ 2 + (-b) ^ 2 ≤ 1 := by nlinarith
    have hnegCircle : a ^ 2 + (-b) ^ 2 = 1 := by nlinarith
    have hnegPSD := hupper a (-b) hneg hnegCircle (by linarith)
    exact (completedCanonicalPhaseLowTailRealCorrectedGram_neg_b_posSemidef_iff
      a b hphase hneg).mp hnegPSD

/-- Combining circle reflection with Schur concavity, an upper-semicircle
certificate implies the canonical corrected-Gram certificate on the entire
closed phase disk. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_disk_posSemidef_of_upperSemicircle
    (hupper : ∀ (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1),
      a ^ 2 + b ^ 2 = 1 → 0 ≤ b →
        Matrix.PosSemidef
          (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase))
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    Matrix.PosSemidef
      (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) := by
  apply completedCanonicalPhaseLowTailRealCorrectedGram_disk_posSemidef_of_circle
    (fun a' b' hphase' hcircle ↦
      completedCanonicalPhaseLowTailRealCorrectedGram_circle_posSemidef_of_upper
        hupper a' b' hphase' hcircle)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailCircleSymmetryStructural
