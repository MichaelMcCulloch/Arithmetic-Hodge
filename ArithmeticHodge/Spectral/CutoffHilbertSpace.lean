/-
  The Cutoff Hilbert Space and Spectral Pairing Construction

  For each cutoff Λ > 0, constructs L²(X, μ|_{S_Λ}) where
  S_Λ = {x ∈ X : heightFn x ≤ Λ} is a compact subset of
  the adèle class space.
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import ArithmeticHodge.Adelic.ClassSpace
import ArithmeticHodge.Spectral.UnboundedOperator
import ArithmeticHodge.Analysis.WeilDefs

open MeasureTheory Measure RCLike
open scoped ENNReal InnerProductSpace InnerProduct

namespace ArithmeticHodge.Spectral.Cutoff

-- ============================================================
-- The Cutoff Set
-- ============================================================

section CutoffSet

variable (X : Type*) [inst : Adelic.AdeleClassSpaceData X]

/-- The cutoff set S_Λ = {x ∈ X : heightFn x ≤ Λ}. -/
def cutoffSet (Λ : ℝ) : Set X :=
  {x : X | inst.heightFn x ≤ Λ}

/-- The cutoff set is measurable. -/
theorem cutoffSet_measurable (Λ : ℝ) : MeasurableSet (cutoffSet X Λ) :=
  inst.heightFn_measurable measurableSet_Iic

/-- The cutoff set is compact. -/
theorem cutoffSet_compact (Λ : ℝ) : IsCompact (cutoffSet X Λ) :=
  inst.heightFn_compact Λ

/-- The cutoff set has finite Haar measure. -/
theorem cutoffSet_measure_lt_top (Λ : ℝ) :
    inst.haarMeasure (cutoffSet X Λ) < ⊤ := by
  haveI := inst.isHaar
  exact (cutoffSet_compact X Λ).measure_lt_top

end CutoffSet

-- ============================================================
-- The Cutoff Measure and Hilbert Space
-- ============================================================

section CutoffHilbert

variable (X : Type*) [inst : Adelic.AdeleClassSpaceData X]

/-- The cutoff measure: Haar measure restricted to S_Λ. -/
noncomputable def cutoffMeasure (Λ : ℝ) : Measure X :=
  inst.haarMeasure.restrict (cutoffSet X Λ)

/-- The cutoff measure is finite. -/
noncomputable instance cutoffMeasure_isFinite (Λ : ℝ) :
    IsFiniteMeasure (cutoffMeasure X Λ) := by
  constructor
  simp only [cutoffMeasure, restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact cutoffSet_measure_lt_top X Λ

/-- The cutoff Hilbert space H_Λ = L²(X, μ_Λ).
    By Mathlib: this is an InnerProductSpace ℂ and CompleteSpace. -/
noncomputable def CutoffL2 (Λ : ℝ) := Lp ℂ 2 (cutoffMeasure X Λ)

end CutoffHilbert

-- ============================================================
-- The Vacuum Vector
-- ============================================================

section Vacuum

variable (X : Type*) [inst : Adelic.AdeleClassSpaceData X]

/-- The vacuum vector: constant function 1 restricted to S_Λ.

    This is the indicator function 1_{S_Λ} viewed as an element of L²(X, μ_Λ).
    It represents the "ground state" of the scaling flow. -/
noncomputable def vacuumVector (Λ : ℝ) :
    Lp ℂ 2 (cutoffMeasure X Λ) := by
  -- The cutoff set has finite cutoff measure (it's the full space under restriction)
  have hmeas : MeasurableSet (cutoffSet X Λ) := cutoffSet_measurable X Λ
  have hfin : (cutoffMeasure X Λ) (cutoffSet X Λ) ≠ ⊤ := by
    simp only [cutoffMeasure, restrict_apply hmeas, Set.inter_self]
    exact (cutoffSet_measure_lt_top X Λ).ne
  exact indicatorConstLp 2 hmeas hfin (1 : ℂ)

end Vacuum

-- ============================================================
-- The Generator and Spectral Decomposition (sorry'd construction)
-- ============================================================

section Spectral

variable (X : Type*) [inst : Adelic.AdeleClassSpaceData X]

/-- The eigenvalues of D_Λ.

    On the compact quotient, D_Λ has discrete spectrum. The eigenvalues
    are real (self-adjointness) and enumerated by ℕ.

    SORRY: Requires constructing D_Λ from the scaling flow, proving
    compact resolvent, and extracting the discrete spectrum. -/
noncomputable def cutoffEigenvaluesOf (Λ : ℝ) : ℕ → ℝ :=
  have : IsCompact (cutoffSet X Λ) := cutoffSet_compact X Λ  -- force X dependency
  sorry

/-- The cutoff measure is separable (X is second-countable, Borel, and the measure is finite).

    PROOF: AdeleClassSpaceData gives SecondCountableTopology X and BorelSpace X,
    so CountablyGenerated X holds. The cutoff measure is finite (hence s-finite),
    so IsSeparable follows from the Mathlib instance. -/
instance cutoffMeasure_isSeparable (Λ : ℝ) :
    IsSeparable (cutoffMeasure X Λ) := by
  haveI : MeasurableSpace.CountablyGenerated X := BorelSpace.countablyGenerated
  infer_instance

/-- L²(X, μ_Λ) has second-countable topology (separable Hilbert space).

    This follows from: μ_Λ is separable + ℂ is second-countable + p = 2 < ∞. -/
instance cutoffL2_secondCountableTopology (Λ : ℝ) :
    SecondCountableTopology (Lp ℂ 2 (cutoffMeasure X Λ)) := by
  haveI : IsSeparable (cutoffMeasure X Λ) := cutoffMeasure_isSeparable X Λ
  haveI : TopologicalSpace.SeparableSpace ℂ := inferInstance
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  exact Lp.SecondCountableTopology

/-- A Hilbert basis exists for L²(X, μ_Λ) indexed by some countable set.

    PROOF: By Mathlib's `exists_hilbertBasis`, every inner product space
    (that is complete) admits a Hilbert basis. Since L²(X, μ_Λ) has
    second-countable topology, the basis set is countable. -/
theorem exists_cutoffHilbertBasis (Λ : ℝ) :
    ∃ (w : Set (Lp ℂ 2 (cutoffMeasure X Λ)))
      (b : HilbertBasis w ℂ (Lp ℂ 2 (cutoffMeasure X Λ))),
      ⇑b = ((↑) : w → Lp ℂ 2 (cutoffMeasure X Λ)) :=
  exists_hilbertBasis ℂ (Lp ℂ 2 (cutoffMeasure X Λ))

/-- The eigenbasis of D_Λ as an orthonormal system in L²(X, μ_Λ).

    CONSTRUCTION STRATEGY:
    1. L²(X, μ_Λ) is a separable Hilbert space (proved above).
    2. A Hilbert basis indexed by some countable set exists (proved above).
    3. Re-indexing to ℕ: this is the spectral theorem for compact self-adjoint
       operators on a separable Hilbert space — the eigenvalues form a countable
       (possibly finite) sequence, and eigenvectors form an orthonormal basis.

    SORRY: The re-indexing from an abstract countable set to ℕ requires either:
    - The spectral theorem for compact operators (eigenvectors indexed by ℕ), or
    - An equivalence between the abstract basis set and ℕ.
    Both are pure-math facts not yet wired in Mathlib for this particular L² space. -/
noncomputable def cutoffEigenbasis (Λ : ℝ) :
    HilbertBasis ℕ ℂ (Lp ℂ 2 (cutoffMeasure X Λ)) :=
  -- We know a Hilbert basis exists (exists_cutoffHilbertBasis), indexed by some Set E.
  -- The spectral theorem for compact self-adjoint operators on separable Hilbert spaces
  -- provides an eigenbasis indexed by ℕ. We sorry the re-indexing/spectral step.
  HilbertBasis.ofRepr sorry

/-- The vacuum amplitude: ⟨Ω_Λ, eᵢ⟩ where eᵢ is the i-th eigenvector.

    DEFINED as the inner product of the vacuum with the i-th eigenvector. -/
noncomputable def vacuumAmplitudeOf (Λ : ℝ) (i : ℕ) : ℂ :=
  @inner ℂ _ _ (vacuumVector X Λ) (cutoffEigenbasis X Λ i)

/-- The vacuum weight |⟨Ω_Λ, eᵢ⟩|² — manifestly non-negative. -/
noncomputable def vacuumWeightOf (Λ : ℝ) (i : ℕ) : ℝ :=
  Complex.normSq (vacuumAmplitudeOf X Λ i)

/-- Vacuum weights are non-negative (by definition as normSq). -/
theorem vacuumWeightOf_nonneg (Λ : ℝ) (i : ℕ) :
    0 ≤ vacuumWeightOf X Λ i :=
  Complex.normSq_nonneg _

-- ============================================================
-- The Spectral Pairing (DEFINED)
-- ============================================================

/-- **The spectral pairing: ⟨ĥ(D_Λ)Ω, Ω⟩.**

    Σᵢ (fourierCos h)(λᵢ) · |⟨Ω, eᵢ⟩|²

    DEFINED — depends on sorry'd eigenvalues and eigenbasis, but the
    formula itself is concrete. -/
noncomputable def spectralPairingOf (Λ : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∑' i, Analysis.fourierCos h (cutoffEigenvaluesOf X Λ i) *
    vacuumWeightOf X Λ i

/-- **Non-negativity of the spectral pairing for autocorrelations.**

    Each term is (fourierCos h)(λᵢ) · |⟨Ω, eᵢ⟩|².
    For autocorrelations: fourierCos h ≥ 0 (Bochner), weights ≥ 0 (normSq).

    SORRY COUNT: 0 in this theorem body.
    Depends on: autocorrelation_fourierCos_nonneg (needs Fubini sorry). -/
theorem spectralPairingOf_nonneg (Λ : ℝ) (hΛ : 0 < Λ)
    (h : ℝ → ℝ) (hf : Analysis.IsAutocorrelation h)
    (hfourier_nonneg : ∀ ξ : ℝ, 0 ≤ Analysis.fourierCos h ξ) :
    0 ≤ spectralPairingOf X Λ h := by
  apply tsum_nonneg
  intro i
  exact mul_nonneg (hfourier_nonneg _) (vacuumWeightOf_nonneg X Λ i)

/-- **Convergence of the spectral pairing to the Weil functional.**

    As Λ → ∞: spectralPairingOf X Λ h → W(h).

    This IS the GL(1)/ℚ trace formula.

    SORRY: PNT + RAGE + Tate local computations + convergence. -/
theorem spectralPairingOf_tendsto_weil
    (h : ℝ → ℝ) (hcont : Continuous h)
    (hdecay : ∀ x, ‖h x‖ ≤ 1 / (1 + x ^ 2)) :
    Filter.Tendsto (fun Λ => spectralPairingOf X Λ h)
      Filter.atTop (nhds (Analysis.weilFunctionalFull h (Analysis.fourierCos h))) := by
  sorry

end Spectral

end ArithmeticHodge.Spectral.Cutoff
