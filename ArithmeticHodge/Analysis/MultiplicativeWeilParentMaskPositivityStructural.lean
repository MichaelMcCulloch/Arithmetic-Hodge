import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCutPencilStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilLiCriterionClosure

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ArithmeticFunction BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilParentMaskPositivityStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCoherentCutPencilStructural
open MultiplicativeWeilCoherentFejerResidualParentMaskStructural

/-!
# What positivity of a coherent parent mask does and does not give

The coefficient kernel of a coherent cut pencil is pointwise rank one.  At
the identity ratio it is literally a norm square, so all of the naive
pointwise Gram positivity is present.

Bombieri's functional is not integration against that pointwise Gram kernel:
it is the local critical form minus the finite von-Mangoldt correlation sum.
This file rewrites the latter exactly through the coherent phase mask.  The
cut-pencil inequality is therefore equivalent to one explicit arithmetic
domination inequality.  A universal Markov/complete-positivity assertion for
arbitrary coherent masks is shown to be exactly RH, not an unconditional
functional-analytic consequence of rank-one coherence.
-/

/-- The parent correlation carrying the complete coherent cut phase mask. -/
def coherentCutParentCorrelation
    (parent : BombieriTest) (eta : ℤ → ℝ → ℝ)
    (cut hi : ℤ) (c : ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ in Set.Ioi 0,
    coherentCutPhaseMask eta cut hi c x y *
      (parent (x * y) * starRingEnd ℂ (parent y))

/-- The exact finite von-Mangoldt cost of the coherent cut phase mask. -/
def coherentCutParentPrimeCost
    (parent : BombieriTest) (eta : ℤ → ℝ → ℝ)
    (cut hi : ℤ) (c : ℂ) : ℂ :=
  ∑' k : ℕ,
    (ArithmeticFunction.vonMangoldt (k + 1) : ℂ) *
      ((2 *
        (coherentCutParentCorrelation parent eta cut hi c
          ((k + 1 : ℕ) : ℝ)).re : ℝ) : ℂ)

/-- At ratio one the coherent phase mask is exactly a rank-one norm square. -/
theorem coherentCutPhaseMask_one_eq_normSq
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (c : ℂ) (y : ℝ) :
    coherentCutPhaseMask eta cut hi c 1 y =
      ((Complex.normSq
        ((eta cut y : ℂ) +
          c * (coherentCutSuffixMask eta cut hi y : ℂ)) : ℝ) : ℂ) := by
  rw [← coherentCut_coefficient_mul_conj_eq_phaseMask]
  rw [one_mul]
  let z : ℂ :=
    (eta cut y : ℂ) + c * (coherentCutSuffixMask eta cut hi y : ℂ)
  change z * starRingEnd ℂ z = (Complex.normSq z : ℂ)
  rw [starRingEnd_apply, Complex.star_def, mul_comm,
    ← Complex.normSq_eq_conj_mul_self]

/-- In particular, the full phase mask has the strongest available
pointwise diagonal positivity. -/
theorem coherentCutPhaseMask_one_re_nonneg
    (eta : ℤ → ℝ → ℝ) (cut hi : ℤ) (c : ℂ) (y : ℝ) :
    0 ≤ (coherentCutPhaseMask eta cut hi c 1 y).re := by
  rw [coherentCutPhaseMask_one_eq_normSq]
  simp only [Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- The prime contribution of the cut pencil is precisely the
von-Mangoldt-weighted real part of its parent-mask correlations. -/
theorem primeSum_bombieriQuadraticTest_coherentCutPencil_eq_parentPrimeCost
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ)
    (hcommon : ∀ k : ℤ, ∀ x : ℝ,
      A k x = (eta k x : ℂ) * parent x)
    (cut hi : ℤ) (c : ℂ) :
    primeSum
        (bombieriQuadraticTest
          (A cut + c • coherentCutSuffix A cut hi)) =
      coherentCutParentPrimeCost parent eta cut hi c := by
  unfold primeSum coherentCutParentPrimeCost
  apply tsum_congr
  intro k
  unfold vonMangoldtPrimeSummand
  rw [primeKernel_bombieriQuadraticTest_eq_two_re]
  rw [bombieriQuadraticTest_coherentCutPencil_apply_eq_parentMask
    parent A eta hcommon]
  rfl

/-- Exact global balance for one coherent cut pencil: local critical energy
minus the explicit parent-mask prime cost. -/
theorem bombieriFunctional_coherentCutPencil_re_eq_local_sub_parentPrimeCost
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ)
    (hcommon : ∀ k : ℤ, ∀ x : ℝ,
      A k x = (eta k x : ℂ) * parent x)
    (cut hi : ℤ) (c : ℂ) :
    (bombieriFunctional
        (bombieriQuadraticTest
          (A cut + c • coherentCutSuffix A cut hi))).re =
      (bombieriLocalCriticalForm
        (A cut + c • coherentCutSuffix A cut hi)
        (A cut + c • coherentCutSuffix A cut hi)).re -
        (coherentCutParentPrimeCost parent eta cut hi c).re := by
  rw [bombieriFunctional_quadratic_eq_localCritical_sub_prime,
    primeSum_bombieriQuadraticTest_coherentCutPencil_eq_parentPrimeCost
      parent A eta hcommon]
  rfl

/-- The weakest exact arithmetic lemma needed at a selected coherent cut.
Pointwise rank-one positivity has already been discharged above; what remains
is domination of every von-Mangoldt mask correlation by the complete local
critical energy. -/
theorem bombieriFunctional_coherentCutPencil_nonneg_iff_parentPrimeDomination
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ)
    (hcommon : ∀ k : ℤ, ∀ x : ℝ,
      A k x = (eta k x : ℂ) * parent x)
    (cut hi : ℤ) (c : ℂ) :
    0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (A cut + c • coherentCutSuffix A cut hi))).re ↔
      (coherentCutParentPrimeCost parent eta cut hi c).re ≤
        (bombieriLocalCriticalForm
          (A cut + c • coherentCutSuffix A cut hi)
          (A cut + c • coherentCutSuffix A cut hi)).re := by
  rw [bombieriFunctional_coherentCutPencil_re_eq_local_sub_parentPrimeCost
    parent A eta hcommon]
  exact sub_nonneg

/-- The tempting generic complete-positivity assertion, even restricted to
real masks taking values in the Markov interval `[0,1]`.  No partition support
geometry is imposed here. -/
def UniversalSubMarkovParentMaskPositivity : Prop :=
  ∀ (parent f : BombieriTest) (eta : ℝ → ℝ),
    CoherentWith parent f eta →
      (∀ x : ℝ, 0 ≤ eta x ∧ eta x ≤ 1) →
        0 ≤ (bombieriFunctional (bombieriQuadraticTest f)).re

/-- Adversarial diagnostic: generic Markov positivity of common-parent masks
is exactly global Bombieri positivity, hence exactly RH.  The constant mask
one already contains every Bombieri test, so rank-one coherence alone cannot
be the missing unconditional mechanism. -/
theorem universalSubMarkovParentMaskPositivity_iff_riemannHypothesis
    (zeros : ZetaZeroEnumeration) :
    UniversalSubMarkovParentMaskPositivity ↔ RiemannHypothesis := by
  constructor
  · intro hmask
    apply (riemannHypothesis_iff_bombieriQuadratic_re_nonnegative zeros).2
    intro g
    apply hmask g g (fun _x ↦ 1)
    · intro x
      simp
    · intro x
      exact ⟨zero_le_one, le_rfl⟩
  · intro hRH parent f eta _hcoherent _heta
    exact
      (riemannHypothesis_iff_bombieriQuadratic_re_nonnegative zeros).1
        hRH f

end

end ArithmeticHodge.Analysis.MultiplicativeWeilParentMaskPositivityStructural
