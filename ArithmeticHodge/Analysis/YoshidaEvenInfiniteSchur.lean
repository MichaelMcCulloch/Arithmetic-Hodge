import ArithmeticHodge.Analysis.HilbertTailSchur
import ArithmeticHodge.Analysis.YoshidaEvenFiniteSchur
import ArithmeticHodge.Analysis.YoshidaParityRecombination

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace

namespace ArithmeticHodge.Analysis.YoshidaEvenInfiniteSchur

open ArithmeticHodge.Analysis
open FormSpace
open YoshidaClippedCircleBridge
open YoshidaCoercivityNumerics
open YoshidaEvenFiniteSchur
open YoshidaEvenHomogeneousCoercivity
open YoshidaEvenIntervalCertificate
open YoshidaEvenMomentTargets
open YoshidaEvenTailLowFunctional
open YoshidaOddGramPrefix
open YoshidaParityRecombination
open YoshidaWeightedTailBounds

/-!
# Infinite Schur closure for Yoshida's even component

The actual two-hundred-mode low block is corrected by the Gram matrix of the
actual low/even-tail Riesz vectors.  The finite certificate proves this Schur
complement positive; completion of the square then yields positivity on the
entire genuinely infinite periodic even carrier.
-/

abbrev EvenTailCompletion :=
  FormSpace.Completion evenOneNinetyNineTailPositiveHermitianForm

/-- The completed low/tail functional represented by the production Riesz
vector. -/
noncomputable def actualEvenTailLowFunctional
    (i : YoshidaEvenIndex) : StrongDual ℂ EvenTailCompletion :=
  (InnerProductSpace.toDual ℂ EvenTailCompletion)
    (actualEvenTailLowRieszCorrection i)

@[simp] theorem actualEvenTailLowFunctional_apply
    (i : YoshidaEvenIndex) (x : EvenTailCompletion) :
    actualEvenTailLowFunctional i x =
      ⟪actualEvenTailLowRieszCorrection i, x⟫_ℂ := by
  exact InnerProductSpace.toDual_apply_apply

@[simp] theorem actualEvenTailLowFunctional_apply_coe
    (i : YoshidaEvenIndex)
    (x : FormSpace evenOneNinetyNineTailPositiveHermitianForm) :
    actualEvenTailLowFunctional i (x : EvenTailCompletion) =
      yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (yoshidaClippedEvenLowMode yoshidaA i)
        (evenOneNinetyNineTailToClippedSmooth x.toV) := by
  rw [actualEvenTailLowFunctional_apply, ← inner_conj_symm,
    formSpace_inner_actualEvenTailLowRieszCorrection]
  exact yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos
    (yoshidaClippedEvenLowMode yoshidaA i)
    (evenOneNinetyNineTailToClippedSmooth x.toV)

@[simp] theorem hilbertTailRieszCorrection_actualEvenTailLowFunctional
    (i : YoshidaEvenIndex) :
    hilbertTailRieszCorrection (actualEvenTailLowFunctional i) =
      actualEvenTailLowRieszCorrection i := by
  simp [hilbertTailRieszCorrection, actualEvenTailLowFunctional]

theorem hilbertTailCorrectedGram_eq_actual :
    hilbertTailCorrectedGram clippedEvenFullGram
        actualEvenTailLowFunctional =
      clippedEvenFullGram - actualEvenTailCorrectionGram := by
  ext i j
  simp [hilbertTailCorrectedGram, actualEvenTailCorrectionGram]

/-- The completed quadratic expression for an arbitrary even low vector and
an arbitrary point of the completed actual mode-`200` even tail. -/
def completedEvenLowTailQuadratic
    (c : YoshidaEvenIndex → ℂ) (x : EvenTailCompletion) : ℂ :=
  star c ⬝ᵥ (clippedEvenFullGram *ᵥ c) +
    ∑ i, star (c i) * actualEvenTailLowFunctional i x +
    ∑ i, c i * star (actualEvenTailLowFunctional i x) +
    ⟪x, x⟫_ℂ

/-- The exact sine, diagonal, and pivot certificates imply strict positivity
on the completed low-plus-infinite-tail coordinate space. -/
theorem completedEvenLowTailQuadratic_re_pos_of_certificates
    (hS : YoshidaEvenSineTargetEnclosures)
    (hD : YoshidaEvenDiagonalTargetEnclosures)
    (hP : YoshidaEvenFullTargetPivots)
    (c : YoshidaEvenIndex → ℂ) (x : EvenTailCompletion)
    (hne : c ≠ 0 ∨ x ≠ 0) :
    0 < (completedEvenLowTailQuadratic c x).re := by
  unfold completedEvenLowTailQuadratic
  apply hilbertTail_quadratic_re_pos
  rw [hilbertTailCorrectedGram_eq_actual]
  exact actualEvenTailCorrectedGram_posDef_of_certificates hS hD hP
  exact hne

/-- Embed an algebraic production even-tail vector into its form
completion. -/
noncomputable def evenTailCompletionCoe
    (f : YoshidaEvenOneNinetyNineTail) : EvenTailCompletion :=
  ((FormSpace.of f :
      FormSpace evenOneNinetyNineTailPositiveHermitianForm) :
    EvenTailCompletion)

@[simp] theorem actualEvenTailLowFunctional_apply_evenTailCompletionCoe
    (i : YoshidaEvenIndex) (f : YoshidaEvenOneNinetyNineTail) :
    actualEvenTailLowFunctional i (evenTailCompletionCoe f) =
      yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (yoshidaClippedEvenLowMode yoshidaA i)
        (evenOneNinetyNineTailToClippedSmooth f) := by
  exact actualEvenTailLowFunctional_apply_coe i (FormSpace.of f)

@[simp] theorem evenTailCompletionCoe_inner_self
    (f : YoshidaEvenOneNinetyNineTail) :
    ⟪evenTailCompletionCoe f, evenTailCompletionCoe f⟫_ℂ =
      yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (evenOneNinetyNineTailToClippedSmooth f)
        (evenOneNinetyNineTailToClippedSmooth f) := by
  unfold evenTailCompletionCoe
  rw [FormSpace.completion_inner_coe]
  rfl

/-- The completed quadratic is exactly the production clipped form of the
corresponding finite-low plus algebraic-tail function. -/
theorem clippedCriticalForm_evenLow_add_tail_eq_completedQuadratic
    (c : YoshidaEvenIndex → ℂ) (f : YoshidaEvenOneNinetyNineTail) :
    yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (∑ i, c i • yoshidaClippedEvenLowMode yoshidaA i +
          evenOneNinetyNineTailToClippedSmooth f)
        (∑ i, c i • yoshidaClippedEvenLowMode yoshidaA i +
          evenOneNinetyNineTailToClippedSmooth f) =
      completedEvenLowTailQuadratic c (evenTailCompletionCoe f) := by
  classical
  let B := yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
  let L := ∑ i, c i • yoshidaClippedEvenLowMode yoshidaA i
  let t := evenOneNinetyNineTailToClippedSmooth f
  have hexpand :
      B (L + t) (L + t) =
        B L L + B L t + B t L + B t t := by
    rw [map_add]
    simp only [map_add]
    change (B L L + B t L) + (B L t + B t t) = _
    ring
  have hLL : B L L = star c ⬝ᵥ (clippedEvenFullGram *ᵥ c) := by
    dsimp only [B, L]
    simp [clippedEvenFullGram, yoshidaClippedEvenGram, dotProduct, mulVec,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change c j * ((starRingEnd ℂ) (c i) *
        yoshidaClippedLocalCriticalPairing yoshidaHalfLength
          yoshidaHalfLength_pos
          (yoshidaClippedEvenLowMode yoshidaHalfLength i)
          (yoshidaClippedEvenLowMode yoshidaHalfLength j)) = _
    ring
  have hLt : B L t =
      ∑ i, star (c i) *
        B (yoshidaClippedEvenLowMode yoshidaA i) t := by
    dsimp only [L]
    simp
  have htL : B t L =
      ∑ i, c i * star
        (B (yoshidaClippedEvenLowMode yoshidaA i) t) := by
    dsimp only [L]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [B]
    rw [← yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos
      (evenOneNinetyNineTailToClippedSmooth f)
      (yoshidaClippedEvenLowMode yoshidaA i)]
  change B (L + t) (L + t) = _
  rw [hexpand, hLL, hLt, htL]
  simp only [completedEvenLowTailQuadratic,
    actualEvenTailLowFunctional_apply_evenTailCompletionCoe,
    evenTailCompletionCoe_inner_self]
  dsimp only [B, t]

private theorem evenTailCompletionCoe_ne_zero
    {f : YoshidaEvenOneNinetyNineTail} (hf : f ≠ 0) :
    evenTailCompletionCoe f ≠ 0 := by
  intro hzero
  have hform : (FormSpace.of f :
      FormSpace evenOneNinetyNineTailPositiveHermitianForm) = 0 := by
    apply UniformSpace.Completion.coe_injective
      (FormSpace evenOneNinetyNineTailPositiveHermitianForm)
    simpa [evenTailCompletionCoe] using hzero
  apply hf
  exact congrArg FormSpace.toV hform

/-- Strict positivity on every nonzero low-plus-actual-even-tail coordinate
pair, conditional only on the three finite certificates. -/
theorem clippedCriticalForm_evenLow_add_tail_re_pos_of_certificates
    (hS : YoshidaEvenSineTargetEnclosures)
    (hD : YoshidaEvenDiagonalTargetEnclosures)
    (hP : YoshidaEvenFullTargetPivots)
    (c : YoshidaEvenIndex → ℂ) (f : YoshidaEvenOneNinetyNineTail)
    (hne : c ≠ 0 ∨ f ≠ 0) :
    0 < (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      (∑ i, c i • yoshidaClippedEvenLowMode yoshidaA i +
        evenOneNinetyNineTailToClippedSmooth f)
      (∑ i, c i • yoshidaClippedEvenLowMode yoshidaA i +
        evenOneNinetyNineTailToClippedSmooth f)).re := by
  rw [clippedCriticalForm_evenLow_add_tail_eq_completedQuadratic]
  apply completedEvenLowTailQuadratic_re_pos_of_certificates hS hD hP
  rcases hne with hc | hf
  · exact Or.inl hc
  · exact Or.inr (evenTailCompletionCoe_ne_zero hf)

/-! ## The entire periodic even source space -/

private def evenLowPeriodicCore (i : YoshidaEvenIndex) :
    YoshidaClippedPeriodicCore yoshidaA :=
  ⟨yoshidaClippedEvenLowMode yoshidaA i,
    yoshidaClippedEvenLowMode_mem_periodicCore yoshidaA_pos i⟩

@[simp] private theorem evenLowPeriodicCore_toSmooth
    (i : YoshidaEvenIndex) :
    ((evenLowPeriodicCore i : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) =
      yoshidaClippedEvenLowMode yoshidaA i :=
  rfl

@[simp] private theorem evenLowPeriodicCore_circle
    (i : YoshidaEvenIndex) :
    letI : Fact (0 < 2 * yoshidaA) :=
      ⟨mul_pos (by norm_num) yoshidaA_pos⟩
    yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos
        (evenLowPeriodicCore i) =
      yoshidaEvenLowMode (T := 2 * yoshidaA) i := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  exact yoshidaClippedCircleL2_evenLowMode yoshidaA_pos i

set_option maxRecDepth 100000 in
/-- Every actual periodic even vector is exactly a two-hundred-mode low
combination plus a vector of the actual periodic mode-`200` even tail. -/
theorem exists_periodicEvenCore_low_add_actualTail
    (g : YoshidaPeriodicEvenCore) :
    ∃ c : YoshidaEvenIndex → ℂ, ∃ f : YoshidaEvenOneNinetyNineTail,
      (((g : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)) =
        (∑ i, c i • yoshidaClippedEvenLowMode yoshidaA i) +
          evenOneNinetyNineTailToClippedSmooth f := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  let F : CircleL2 (T := 2 * yoshidaA) :=
    yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos g.1
  have heven : F ∈ evenL2Submodule (T := 2 * yoshidaA) := g.2
  obtain ⟨c, hc⟩ :=
    exists_yoshida_even_twoHundred_coefficients_add_tail heven
  let low : YoshidaClippedPeriodicCore yoshidaA :=
    ∑ i, c i • evenLowPeriodicCore i
  let residual : YoshidaClippedPeriodicCore yoshidaA := g.1 - low
  have hlowCircle :
      yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos low =
        ∑ i, c i • yoshidaEvenLowMode (T := 2 * yoshidaA) i := by
    dsimp only [low]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, evenLowPeriodicCore_circle]
  have hresidualCircle :
      yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos residual =
        (evenTailRemainder (T := 2 * yoshidaA) 199 heven :
          CircleL2 (T := 2 * yoshidaA)) := by
    dsimp only [residual]
    have hmap :
        yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos (g.1 - low) =
          yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos g.1 -
            yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos low :=
      map_sub (yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos) g.1 low
    rw [hmap, hlowCircle]
    change F - (∑ i, c i • yoshidaEvenLowMode
      (T := 2 * yoshidaA) i) = _
    calc
      F - (∑ i, c i • yoshidaEvenLowMode (T := 2 * yoshidaA) i) =
          ((∑ i, c i • yoshidaEvenLowMode (T := 2 * yoshidaA) i) +
            (evenTailRemainder (T := 2 * yoshidaA) 199 heven :
              CircleL2 (T := 2 * yoshidaA))) -
            ∑ i, c i • yoshidaEvenLowMode (T := 2 * yoshidaA) i :=
        congrArg
          (fun z : CircleL2 (T := 2 * yoshidaA) ↦
            z - ∑ i, c i • yoshidaEvenLowMode (T := 2 * yoshidaA) i)
          hc
      _ = _ := by abel
  have hresidualTail :
      residual ∈ yoshidaPeriodicCoreEvenTailSubmodule
        yoshidaA_pos 199 := by
    change yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos residual ∈
      evenFourierTailSubmodule (T := 2 * yoshidaA) 199
    rw [hresidualCircle]
    exact (evenTailRemainder (T := 2 * yoshidaA) 199 heven).property
  let f : YoshidaEvenOneNinetyNineTail := ⟨residual, hresidualTail⟩
  refine ⟨c, f, ?_⟩
  change ((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) =
    (∑ i, c i • yoshidaClippedEvenLowMode yoshidaA i) +
      ((residual : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA)
  dsimp only [residual, low]
  change ((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) =
    (∑ i, c i • yoshidaClippedEvenLowMode yoshidaA i) +
      (((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) -
        ∑ i, c i • yoshidaClippedEvenLowMode yoshidaA i)
  abel

/-- Strict positivity of the actual production clipped form on the entire
periodic even carrier, conditional only on the three finite certificates. -/
theorem periodicEvenCore_clippedCriticalForm_re_pos_of_certificates
    (hS : YoshidaEvenSineTargetEnclosures)
    (hD : YoshidaEvenDiagonalTargetEnclosures)
    (hP : YoshidaEvenFullTargetPivots)
    (g : YoshidaPeriodicEvenCore) (hg : g ≠ 0) :
    0 < (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      ((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA)
      ((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA)).re := by
  obtain ⟨c, f, hdecomp⟩ := exists_periodicEvenCore_low_add_actualTail g
  rw [hdecomp]
  apply clippedCriticalForm_evenLow_add_tail_re_pos_of_certificates hS hD hP
  by_contra hboth
  push_neg at hboth
  obtain ⟨hc, hf⟩ := hboth
  apply hg
  apply Subtype.ext
  apply Subtype.ext
  simpa [hc, hf] using hdecomp

/-- The three finite certificates close Gate 1: strict production-form
positivity holds on every nonzero vector of the full restricted periodic
source core. -/
theorem periodicCore_clippedCriticalForm_re_pos_of_certificates
    (hS : YoshidaEvenSineTargetEnclosures)
    (hD : YoshidaEvenDiagonalTargetEnclosures)
    (hP : YoshidaEvenFullTargetPivots)
    (f : YoshidaClippedPeriodicCore yoshidaA) (hf : f ≠ 0) :
    0 < (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      (f : YoshidaClippedSmooth yoshidaA)
      (f : YoshidaClippedSmooth yoshidaA)).re := by
  apply periodicCore_clippedCriticalForm_re_pos_of_even
  · exact periodicEvenCore_clippedCriticalForm_re_pos_of_certificates
      hS hD hP
  · exact hf

end ArithmeticHodge.Analysis.YoshidaEvenInfiniteSchur
