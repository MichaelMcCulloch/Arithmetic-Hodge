import ArithmeticHodge.Analysis.HilbertTailSchur
import ArithmeticHodge.Analysis.YoshidaDiagonalMomentEnclosures
import ArithmeticHodge.Analysis.YoshidaOddComparisonReserve
import ArithmeticHodge.Analysis.YoshidaOddRealSpaceAssembly
import ArithmeticHodge.Analysis.YoshidaOddTailLowFunctional
import ArithmeticHodge.Analysis.YoshidaRestrictedCoreBridge
import ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace

namespace ArithmeticHodge.Analysis.YoshidaOddInfiniteSchur

open ArithmeticHodge.Analysis
open FormSpace
open YoshidaClippedCircleBridge
open YoshidaDiagonalMomentEnclosures
open YoshidaCoercivityNumerics
open YoshidaOddComparisonReserve
open YoshidaOddGramPrefix
open YoshidaOddHomogeneousCoercivity
open YoshidaOddIntervalCertificate
open YoshidaOddRealSpaceAssembly
open YoshidaOddTailLowFunctional
open YoshidaSineMomentEnclosures
open YoshidaWeightedTailBounds

/-!
# Infinite Schur closure for Yoshida's odd component

The actual low/tail Riesz vectors define the Schur correction of the certified
ten-mode clipped Gram.  Their `1/40` squared-norm bound fits exactly inside the
entrywise comparison reserve, so the corrected finite Gram remains positive
definite.  Completing the square then proves strict positivity for every
finite low vector plus every vector in the completed infinite tenth odd tail.
-/

abbrev OddTailCompletion :=
  FormSpace.Completion oddTenTailPositiveHermitianForm

/-- The completed low/tail functional represented by the actual production
Riesz vector. -/
noncomputable def actualOddTailLowFunctional
    (i : YoshidaOddIndex) : StrongDual ℂ OddTailCompletion :=
  (InnerProductSpace.toDual ℂ OddTailCompletion)
    (actualOddTailLowRieszCorrection i)

@[simp] theorem actualOddTailLowFunctional_apply
    (i : YoshidaOddIndex) (x : OddTailCompletion) :
    actualOddTailLowFunctional i x =
      ⟪actualOddTailLowRieszCorrection i, x⟫_ℂ := by
  exact InnerProductSpace.toDual_apply_apply

@[simp] theorem actualOddTailLowFunctional_apply_coe
    (i : YoshidaOddIndex)
    (x : FormSpace oddTenTailPositiveHermitianForm) :
    actualOddTailLowFunctional i
        (x : OddTailCompletion) =
      yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (yoshidaClippedOddLowMode yoshidaA i)
        (oddTenTailToClippedSmooth x.toV) := by
  rw [actualOddTailLowFunctional_apply, ← inner_conj_symm,
    formSpace_inner_actualOddTailLowRieszCorrection]
  exact yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos
    (yoshidaClippedOddLowMode yoshidaA i)
    (oddTenTailToClippedSmooth x.toV)

/-- Gram matrix of the ten actual low/tail Riesz corrections. -/
noncomputable def actualOddTailCorrectionGram :
    Matrix YoshidaOddIndex YoshidaOddIndex ℂ :=
  fun i j ↦
    ⟪actualOddTailLowRieszCorrection i,
      actualOddTailLowRieszCorrection j⟫_ℂ

theorem actualOddTailCorrectionGram_isHermitian :
    actualOddTailCorrectionGram.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  exact inner_conj_symm _ _

private theorem correction_norm_product_le
    (i j : YoshidaOddIndex) :
    ‖actualOddTailLowRieszCorrection i‖ *
        ‖actualOddTailLowRieszCorrection j‖ ≤ (1 / 40 : ℝ) := by
  rw [← sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 1 / 40)]
  calc
    (‖actualOddTailLowRieszCorrection i‖ *
        ‖actualOddTailLowRieszCorrection j‖) ^ 2 =
        ‖actualOddTailLowRieszCorrection i‖ ^ 2 *
          ‖actualOddTailLowRieszCorrection j‖ ^ 2 := by ring
    _ ≤ (1 / 40 : ℝ) * (1 / 40 : ℝ) :=
      mul_le_mul
        (norm_sq_actualOddTailLowRieszCorrection_le i)
        (norm_sq_actualOddTailLowRieszCorrection_le j)
        (sq_nonneg _) (by norm_num)
    _ = (1 / 40 : ℝ) ^ 2 := by ring

theorem actualOddTailCorrectionGram_norm_le
    (i j : YoshidaOddIndex) :
    ‖actualOddTailCorrectionGram i j‖ ≤ (1 / 40 : ℝ) := by
  exact (norm_inner_le_norm _ _).trans (correction_norm_product_le i j)

/-- The actual ten-mode Gram remains positive definite after subtracting the
complete infinite-tail Schur correction. -/
theorem actualOddTailCorrectedGram_posDef :
    (clippedOddFullGram - actualOddTailCorrectionGram).PosDef := by
  exact clippedOddFullGram_sub_posDef_of_bridge_and_target_enclosures
    clippedOddFullMomentBridge
    sineTargetEnclosures_from_series192
    diagonalTargetEnclosures_from_certificate
    actualOddTailCorrectionGram
    actualOddTailCorrectionGram_isHermitian
    actualOddTailCorrectionGram_norm_le

@[simp] theorem hilbertTailRieszCorrection_actualOddTailLowFunctional
    (i : YoshidaOddIndex) :
    hilbertTailRieszCorrection (actualOddTailLowFunctional i) =
      actualOddTailLowRieszCorrection i := by
  simp [hilbertTailRieszCorrection, actualOddTailLowFunctional]

theorem hilbertTailCorrectedGram_eq_actual :
    hilbertTailCorrectedGram clippedOddFullGram
        actualOddTailLowFunctional =
      clippedOddFullGram - actualOddTailCorrectionGram := by
  ext i j
  simp [hilbertTailCorrectedGram, actualOddTailCorrectionGram]

/-- The completed quadratic expression for an arbitrary odd low coefficient
vector and an arbitrary point of the completed actual odd tail. -/
def completedOddLowTailQuadratic
    (c : YoshidaOddIndex → ℂ) (x : OddTailCompletion) : ℂ :=
  star c ⬝ᵥ (clippedOddFullGram *ᵥ c) +
    ∑ i, star (c i) * actualOddTailLowFunctional i x +
    ∑ i, c i * star (actualOddTailLowFunctional i x) +
    ⟪x, x⟫_ℂ

/-- Strict positivity on the direct low-plus-completed-tail coordinate space.
This is genuinely infinite-dimensional: `x` ranges over the Hilbert
completion of the actual tenth periodic odd tail. -/
theorem completedOddLowTailQuadratic_re_pos
    (c : YoshidaOddIndex → ℂ) (x : OddTailCompletion)
    (hne : c ≠ 0 ∨ x ≠ 0) :
    0 < (completedOddLowTailQuadratic c x).re := by
  unfold completedOddLowTailQuadratic
  apply hilbertTail_quadratic_re_pos
  rw [hilbertTailCorrectedGram_eq_actual]
  exact actualOddTailCorrectedGram_posDef
  exact hne

/-- Embed an algebraic actual odd-tail vector into its form completion. -/
noncomputable def oddTailCompletionCoe
    (f : YoshidaOddTenTail) : OddTailCompletion :=
  ((FormSpace.of f : FormSpace oddTenTailPositiveHermitianForm) :
    OddTailCompletion)

@[simp] theorem actualOddTailLowFunctional_apply_oddTailCompletionCoe
    (i : YoshidaOddIndex) (f : YoshidaOddTenTail) :
    actualOddTailLowFunctional i (oddTailCompletionCoe f) =
      yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (yoshidaClippedOddLowMode yoshidaA i)
        (oddTenTailToClippedSmooth f) := by
  exact actualOddTailLowFunctional_apply_coe i (FormSpace.of f)

@[simp] theorem oddTailCompletionCoe_inner_self
    (f : YoshidaOddTenTail) :
    ⟪oddTailCompletionCoe f, oddTailCompletionCoe f⟫_ℂ =
      yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (oddTenTailToClippedSmooth f)
        (oddTenTailToClippedSmooth f) := by
  unfold oddTailCompletionCoe
  rw [FormSpace.completion_inner_coe]
  rfl

/-- The completed quadratic is exactly the production clipped critical form
of the corresponding finite-low plus algebraic-tail function. -/
theorem clippedCriticalForm_oddLow_add_tail_eq_completedQuadratic
    (c : YoshidaOddIndex → ℂ) (f : YoshidaOddTenTail) :
    yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (∑ i, c i • yoshidaClippedOddLowMode yoshidaA i +
          oddTenTailToClippedSmooth f)
        (∑ i, c i • yoshidaClippedOddLowMode yoshidaA i +
          oddTenTailToClippedSmooth f) =
      completedOddLowTailQuadratic c (oddTailCompletionCoe f) := by
  classical
  let B := yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
  let L := ∑ i, c i • yoshidaClippedOddLowMode yoshidaA i
  let t := oddTenTailToClippedSmooth f
  have hexpand :
      B (L + t) (L + t) =
        B L L + B L t + B t L + B t t := by
    rw [map_add]
    simp only [map_add]
    change (B L L + B t L) + (B L t + B t t) = _
    ring
  have hLL : B L L = star c ⬝ᵥ (clippedOddFullGram *ᵥ c) := by
    dsimp only [B, L]
    simp [clippedOddFullGram, yoshidaClippedOddGram, dotProduct, mulVec,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change c j * ((starRingEnd ℂ) (c i) *
        yoshidaClippedLocalCriticalPairing yoshidaHalfLength
          yoshidaHalfLength_pos
          (yoshidaClippedOddLowMode yoshidaHalfLength i)
          (yoshidaClippedOddLowMode yoshidaHalfLength j)) = _
    ring
  have hLt : B L t =
      ∑ i, star (c i) * B (yoshidaClippedOddLowMode yoshidaA i) t := by
    dsimp only [L]
    simp
  have htL : B t L =
      ∑ i, c i * star (B (yoshidaClippedOddLowMode yoshidaA i) t) := by
    dsimp only [L]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [B]
    rw [← yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos
      (oddTenTailToClippedSmooth f)
      (yoshidaClippedOddLowMode yoshidaA i)]
  change B (L + t) (L + t) = _
  rw [hexpand, hLL, hLt, htL]
  simp only [completedOddLowTailQuadratic,
    actualOddTailLowFunctional_apply_oddTailCompletionCoe,
    oddTailCompletionCoe_inner_self]
  dsimp only [B, t]

private theorem oddTailCompletionCoe_ne_zero
    {f : YoshidaOddTenTail} (hf : f ≠ 0) :
    oddTailCompletionCoe f ≠ 0 := by
  intro hzero
  have hform : (FormSpace.of f :
      FormSpace oddTenTailPositiveHermitianForm) = 0 := by
    apply UniformSpace.Completion.coe_injective
      (FormSpace oddTenTailPositiveHermitianForm)
    simpa [oddTailCompletionCoe] using hzero
  apply hf
  exact congrArg FormSpace.toV hform

/-- Strict positivity of the actual production clipped form on every nonzero
low-plus-tenth-odd-tail coordinate pair. -/
theorem clippedCriticalForm_oddLow_add_tail_re_pos
    (c : YoshidaOddIndex → ℂ) (f : YoshidaOddTenTail)
    (hne : c ≠ 0 ∨ f ≠ 0) :
    0 < (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      (∑ i, c i • yoshidaClippedOddLowMode yoshidaA i +
        oddTenTailToClippedSmooth f)
      (∑ i, c i • yoshidaClippedOddLowMode yoshidaA i +
        oddTenTailToClippedSmooth f)).re := by
  rw [clippedCriticalForm_oddLow_add_tail_eq_completedQuadratic]
  apply completedOddLowTailQuadratic_re_pos
  rcases hne with hc | hf
  · exact Or.inl hc
  · exact Or.inr (oddTailCompletionCoe_ne_zero hf)

/-! ## The entire periodic odd source space -/

/-- Periodic-core functions whose faithful circle coordinate is odd. -/
def yoshidaPeriodicCoreOddSubmodule :
    Submodule ℂ (YoshidaClippedPeriodicCore yoshidaA) := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  exact (oddL2Submodule (T := 2 * yoshidaA)).comap
    (yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos)

/-- The actual canonical periodic odd carrier before the low/tail split. -/
abbrev YoshidaPeriodicOddCore := yoshidaPeriodicCoreOddSubmodule

private def oddLowPeriodicCore (i : YoshidaOddIndex) :
    YoshidaClippedPeriodicCore yoshidaA :=
  ⟨yoshidaClippedOddLowMode yoshidaA i,
    yoshidaClippedOddLowMode_mem_periodicCore yoshidaA_pos i⟩

@[simp] private theorem oddLowPeriodicCore_toSmooth
    (i : YoshidaOddIndex) :
    ((oddLowPeriodicCore i : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) =
      yoshidaClippedOddLowMode yoshidaA i :=
  rfl

@[simp] private theorem oddLowPeriodicCore_circle
    (i : YoshidaOddIndex) :
    letI : Fact (0 < 2 * yoshidaA) :=
      ⟨mul_pos (by norm_num) yoshidaA_pos⟩
    yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos
        (oddLowPeriodicCore i) =
      yoshidaOddLowMode (T := 2 * yoshidaA) i := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  exact yoshidaClippedCircleL2_oddLowMode yoshidaA_pos i

/-- Every actual periodic odd vector is exactly a ten-mode low combination
plus a vector of the actual periodic tenth odd tail. -/
theorem exists_periodicOddCore_low_add_actualTail
    (g : YoshidaPeriodicOddCore) :
    ∃ c : YoshidaOddIndex → ℂ, ∃ f : YoshidaOddTenTail,
      (((g : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)) =
        (∑ i, c i • yoshidaClippedOddLowMode yoshidaA i) +
          oddTenTailToClippedSmooth f := by
  letI : Fact (0 < 2 * yoshidaA) :=
    ⟨mul_pos (by norm_num) yoshidaA_pos⟩
  let F : CircleL2 (T := 2 * yoshidaA) :=
    yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos g.1
  have hodd : F ∈ oddL2Submodule (T := 2 * yoshidaA) := g.2
  obtain ⟨c, hc⟩ :=
    exists_yoshida_odd_ten_coefficients_add_tail hodd
  let low : YoshidaClippedPeriodicCore yoshidaA :=
    ∑ i, c i • oddLowPeriodicCore i
  let residual : YoshidaClippedPeriodicCore yoshidaA := g.1 - low
  have hlowCircle :
      yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos low =
        ∑ i, c i • yoshidaOddLowMode (T := 2 * yoshidaA) i := by
    dsimp only [low]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, oddLowPeriodicCore_circle]
  have hresidualCircle :
      yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos residual =
        (oddTailRemainder (T := 2 * yoshidaA) 10 hodd :
          CircleL2 (T := 2 * yoshidaA)) := by
    dsimp only [residual]
    have hmap :
        yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos (g.1 - low) =
          yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos g.1 -
            yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos low :=
      map_sub (yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos) g.1 low
    rw [hmap, hlowCircle]
    change F - (∑ i, c i • yoshidaOddLowMode (T := 2 * yoshidaA) i) = _
    calc
      F - (∑ i, c i • yoshidaOddLowMode (T := 2 * yoshidaA) i) =
          ((∑ i, c i • yoshidaOddLowMode (T := 2 * yoshidaA) i) +
            (oddTailRemainder (T := 2 * yoshidaA) 10 hodd :
              CircleL2 (T := 2 * yoshidaA))) -
            ∑ i, c i • yoshidaOddLowMode (T := 2 * yoshidaA) i :=
        congrArg
          (fun z : CircleL2 (T := 2 * yoshidaA) ↦
            z - ∑ i, c i • yoshidaOddLowMode (T := 2 * yoshidaA) i)
          hc
      _ = _ := by abel
  have hresidualTail :
      residual ∈ yoshidaPeriodicCoreOddTailSubmodule yoshidaA_pos 10 := by
    change yoshidaPeriodicCoreCircleL2Linear yoshidaA_pos residual ∈
      oddFourierTailSubmodule (T := 2 * yoshidaA) 10
    rw [hresidualCircle]
    exact (oddTailRemainder (T := 2 * yoshidaA) 10 hodd).property
  let f : YoshidaOddTenTail := ⟨residual, hresidualTail⟩
  refine ⟨c, f, ?_⟩
  change ((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) =
    (∑ i, c i • yoshidaClippedOddLowMode yoshidaA i) +
      ((residual : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA)
  dsimp only [residual, low]
  change ((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA) =
    (∑ i, c i • yoshidaClippedOddLowMode yoshidaA i) +
      (((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) -
        ∑ i, c i • yoshidaClippedOddLowMode yoshidaA i)
  abel

/-- Unconditional strict positivity of the production clipped critical form
on every nonzero vector of the full periodic odd source carrier. -/
theorem periodicOddCore_clippedCriticalForm_re_pos
    (g : YoshidaPeriodicOddCore) (hg : g ≠ 0) :
    0 < (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      ((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA)
      ((g : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA)).re := by
  obtain ⟨c, f, hdecomp⟩ := exists_periodicOddCore_low_add_actualTail g
  rw [hdecomp]
  apply clippedCriticalForm_oddLow_add_tail_re_pos
  by_contra hboth
  push_neg at hboth
  obtain ⟨hc, hf⟩ := hboth
  apply hg
  apply Subtype.ext
  apply Subtype.ext
  simpa [hc, hf] using hdecomp

end ArithmeticHodge.Analysis.YoshidaOddInfiniteSchur
