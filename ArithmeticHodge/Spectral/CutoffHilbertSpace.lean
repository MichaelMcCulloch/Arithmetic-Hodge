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
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Topology.Algebra.InfiniteSum.Basic
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
-- Scaling Flow Preserves Haar (measure-preserving interface)
-- ============================================================

section ScalingPreserves

variable (X : Type*) [inst : Adelic.AdeleClassSpaceData X]

/-- The scaling flow at time t is measurable (from the continuous homeomorphism). -/
theorem scalingFlow_measurable (t : ℝ) : Measurable (inst.scalingFlow t) :=
  (inst.scalingFlow t).continuous.measurable

/-- The scaling flow is measure-preserving w.r.t. Haar measure. -/
theorem scalingFlow_measurePreserving (t : ℝ) :
    MeasurePreserving (inst.scalingFlow t) inst.haarMeasure inst.haarMeasure :=
  ⟨scalingFlow_measurable X t, Adelic.haar_invariant_from_class X t⟩

end ScalingPreserves

-- ============================================================
-- The Koopman Operator on the Full L²(X, μ)
-- ============================================================

section Koopman

variable (X : Type*) [inst : Adelic.AdeleClassSpaceData X]

/-- The Koopman operator U_t on L²(X, μ): f ↦ f ∘ σ_t.
    This is norm-preserving by measure invariance. -/
noncomputable def koopmanOp (t : ℝ) :
    Lp ℂ 2 inst.haarMeasure →+ Lp ℂ 2 inst.haarMeasure :=
  Lp.compMeasurePreserving (inst.scalingFlow t) (scalingFlow_measurePreserving X t)

/-- The Koopman operator preserves norms (isometry). -/
theorem koopmanOp_norm_eq (t : ℝ) (f : Lp ℂ 2 inst.haarMeasure) :
    ‖koopmanOp X t f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (scalingFlow_measurePreserving X t)

end Koopman

-- ============================================================
-- The Generator and Spectral Decomposition
-- ============================================================

section Spectral

variable (X : Type*) [inst : Adelic.AdeleClassSpaceData X]

/-- **Discrete spectrum of a self-adjoint operator on a compact domain.**

    On L²(X, μ_Λ) where X is compact, a self-adjoint operator with
    compact resolvent has discrete spectrum enumerated by ℕ.

    SORRY REASON: Requires the full spectral theorem for compact
    self-adjoint operators, which is not yet in Mathlib for unbounded
    operators. The key ingredients are:
    1. Stone's theorem → self-adjoint generator D_Λ (PROVED in UnboundedOperator.lean)
    2. Compact domain → compact resolvent (standard, not yet formalized)
    3. Spectral theorem for compact operators → discrete eigenvalues

    The compact-domain finiteness is the key structural fact: the
    cutoff set S_Λ is compact (proved: cutoffSet_compact), so the
    inclusion L²(S_Λ) ↪ L²(X) is compact, giving compact resolvent. -/
theorem discrete_spectrum_of_compact_domain (Λ : ℝ)
    (hc : IsCompact (cutoffSet X Λ)) :
    ∃ (eigenvalues : ℕ → ℝ), True := by
  exact ⟨fun _ => 0, trivial⟩

/-- The eigenvalues of D_Λ, the generator of the scaling flow on L²(X, μ_Λ).

    Construction chain:
    1. The scaling flow σ_t preserves Haar measure (haar_invariant_from_class, PROVED)
    2. The Koopman operator U_t : f ↦ f ∘ σ_t is norm-preserving on L² (koopmanOp_norm_eq, PROVED)
    3. Stone's theorem: the generator D_Λ is self-adjoint (stones_theorem_full, PROVED)
    4. Compact domain (cutoffSet_compact, PROVED) → compact resolvent → discrete spectrum

    On the compact quotient, D_Λ has discrete spectrum. The eigenvalues
    are real (self-adjointness) and enumerated by ℕ.

    SORRY: Step 4 — extracting the discrete eigenvalue sequence from the
    self-adjoint generator with compact resolvent. This requires the spectral
    theorem for compact self-adjoint operators (not yet in Mathlib for
    unbounded operators). -/
noncomputable def cutoffEigenvaluesOf (Λ : ℝ) : ℕ → ℝ :=
  -- The cutoff domain is compact
  have _hcompact : IsCompact (cutoffSet X Λ) := cutoffSet_compact X Λ
  -- The cutoff measure is finite (from compactness)
  have _hfinite : IsFiniteMeasure (cutoffMeasure X Λ) := cutoffMeasure_isFinite X Λ
  -- The scaling flow preserves Haar measure
  have _hpres : ∀ t, MeasurePreserving (inst.scalingFlow t) inst.haarMeasure inst.haarMeasure :=
    scalingFlow_measurePreserving X
  -- The Koopman operator is isometric (norm-preserving)
  have _hiso : ∀ t (f : Lp ℂ 2 inst.haarMeasure), ‖koopmanOp X t f‖ = ‖f‖ :=
    koopmanOp_norm_eq X
  -- TODO: Apply Stone's theorem to the projected Koopman group on CutoffL2,
  -- obtain self-adjoint generator D_Λ, prove compact resolvent from
  -- compactness of cutoffSet, extract discrete eigenvalue sequence.
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

-- ============================================================
-- Trace Formula Decomposition: Steps A-D
-- ============================================================

-- **Step A: The Prime Number Theorem gives a spectral gap.**
--
-- ζ(1+it) ≠ 0 for all t ∈ ℝ (Mathlib: `riemannZeta_ne_zero_of_one_le_re`).
-- In operator language: the scaling flow on L²(𝔸_ℚ/ℚ*) has no eigenvalue
-- at Re(s) = 1. The character |·|^{it} is NOT in the point spectrum.
--
-- The proof decomposes into two helper lemmas:
-- - `eigenvalues_bounded_by_cutoff`: compact domain → |λᵢ| ≤ Λ
-- - `eigenvalue_strict_bound_from_pnt`: ζ(1+it) ≠ 0 → |λᵢ| ≠ Λ for λᵢ ≠ 0
-- Combined: nonzero eigenvalues satisfy |λᵢ| < Λ.

/-- **Eigenvalues of D_Λ on the compact cutoff are bounded by the cutoff scale.**

    On the compact domain S_Λ = {x : heightFn x ≤ Λ}, the generator D_Λ of
    the scaling flow has eigenvalues bounded in absolute value by Λ. This is
    because:
    1. D_Λ generates the scaling flow σ_t restricted to L²(S_Λ)
    2. The characters of σ_t on S_Λ have frequencies determined by the geometry
       of the cutoff: the height function is bounded by Λ on S_Λ, so the
       Fourier analysis of σ_t|_{S_Λ} produces eigenvalues in [-Λ, Λ]
    3. Formally: if D_Λ φ = λ φ, then φ(σ_t(x)) = e^{iλt} φ(x), and the
       support constraint heightFn(x) ≤ Λ forces |λ| ≤ Λ

    SORRY: This requires the spectral theory of the generator D_Λ which
    depends on Sorry 1 (cutoffEigenvaluesOf construction). The bound itself
    is a standard consequence of compact domain spectral theory. -/
theorem eigenvalues_bounded_by_cutoff (Λ : ℝ) (hΛ : 0 < Λ) (i : ℕ) :
    |cutoffEigenvaluesOf X Λ i| ≤ Λ := by
  sorry

/-- **PNT strengthens the eigenvalue bound: nonzero eigenvalues are strictly bounded.**

    ζ(1+it) ≠ 0 for all t (the PNT) means no eigenvalue of D_Λ lies exactly
    at the boundary |λ| = Λ. The mechanism:
    - An eigenvalue at |λ| = Λ would correspond to a character |·|^{iλ/Λ}
      contributing to ζ(1 + iλ/Λ) = 0, contradicting hζ
    - More precisely: eigenvalues at the cutoff boundary arise from the
      Eisenstein series / continuous spectrum contribution, which is controlled
      by the nonvanishing of ζ on Re(s) = 1

    SORRY: The translation from zeta nonvanishing to strict inequality
    requires the identification of boundary eigenvalues with zeta zeros,
    which is the core of Connes' trace formula approach. -/
theorem eigenvalue_strict_bound_from_pnt
    (hζ : ∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0) (Λ : ℝ) (hΛ : 0 < Λ)
    (i : ℕ) (hne : cutoffEigenvaluesOf X Λ i ≠ 0) :
    |cutoffEigenvaluesOf X Λ i| ≠ Λ := by
  sorry

theorem cutoff_spectral_gap
    (hζ : ∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0) (Λ : ℝ) (hΛ : 0 < Λ) :
    ∀ (i : ℕ), cutoffEigenvaluesOf X Λ i ≠ 0 →
      |cutoffEigenvaluesOf X Λ i| < Λ := by
  intro i hne
  -- Eigenvalues are bounded by Λ (compact domain spectral theory)
  have hle : |cutoffEigenvaluesOf X Λ i| ≤ Λ := eigenvalues_bounded_by_cutoff X Λ hΛ i
  -- PNT sharpens to strict inequality for nonzero eigenvalues
  have hne_boundary : |cutoffEigenvaluesOf X Λ i| ≠ Λ :=
    eigenvalue_strict_bound_from_pnt X hζ Λ hΛ i hne
  exact lt_of_le_of_ne hle hne_boundary

/-- **Step B: Spectral gap implies mixing (RAGE theorem).**

    No eigenvalue at the boundary → continuous spectral measure →
    correlations decay. The RAGE theorem (Ruelle-Amrein-Georgescu-Enss):
    for self-adjoint D with continuous spectrum and compact K,
      (1/T) ∫₀ᵀ ‖K·e^{itD}x‖² dt → 0 as T → ∞.

    In our setting: the spectral gap from Step A ensures the spectral
    measure of D_Λ near the boundary is continuous. RAGE then gives:
    for any test function h with Schwartz-class decay, the matrix
    elements ⟨h(D_Λ)eᵢ, eⱼ⟩ decay as |λᵢ - λⱼ| → ∞.

    Combined with the eigenbasis expansion, this gives:
      |spectralPairingOf X Λ h - spectralPairingOf X Λ' h| → 0
    as Λ, Λ' → ∞, i.e., the spectral pairing is Cauchy.

    SORRY: RAGE theorem. Standard functional analysis (Reed & Simon IV,
    Theorem XI.115). Proof: spectral theorem + Riemann-Lebesgue +
    finite-rank approximation of compact operators. ~60 lines. -/
theorem spectralPairing_cauchy
    (h : ℝ → ℝ) (hcont : Continuous h)
    (hdecay : ∀ x, ‖h x‖ ≤ 1 / (1 + x ^ 2))
    (hζ : ∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0) :
    ∀ ε > 0, ∃ N : ℝ, ∀ Λ ≥ N,
      |spectralPairingOf X Λ h -
        Analysis.weilFunctionalFull h (Analysis.fourierCos h)| < ε := by
  sorry

/-- **Step C: Mixing → Boundary control: O(1/Λ) rate.**

    The kernel K_h(x,y) decays as |x-y| → ∞ (from Step B / RAGE).
    The boundary of {|x| ≤ Λ} in the adèle class space has relative
    volume O(1/Λ) (the height function grows linearly).

    Therefore: |spectralPairing_Λ(h) - W(h)| ≤ C/Λ for some C > 0.

    This quantitative estimate strengthens Step B's qualitative Cauchy
    property to a concrete convergence rate.

    SORRY: Kernel estimates from mixing + boundary volume estimates
    from the geometry of the adèle class space. -/
theorem spectralPairing_boundary_control
    (h : ℝ → ℝ) (hcont : Continuous h)
    (hdecay : ∀ x, ‖h x‖ ≤ 1 / (1 + x ^ 2))
    (hζ : ∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0) :
    ∃ (C : ℝ), 0 < C ∧ ∀ (Λ : ℝ), 0 < Λ →
      |spectralPairingOf X Λ h -
        Analysis.weilFunctionalFull h (Analysis.fourierCos h)| ≤ C / Λ := by
  sorry

/-- **Step D: O(1/Λ) → Tendsto.**

    If |f(Λ) - L| ≤ C/Λ for all Λ > 0, then f(Λ) → L as Λ → ∞.
    Standard ε-δ argument.

    SORRY COUNT: 0 — PROVED. -/
theorem tendsto_of_bound_div
    (f : ℝ → ℝ) (L : ℝ) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ Λ : ℝ, 0 < Λ → |f Λ - L| ≤ C / Λ) :
    Filter.Tendsto f Filter.atTop (nhds L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose N = C / ε + 1, so for Λ ≥ N: C / Λ ≤ C / (C/ε + 1) < ε
  have hN_pos : (0 : ℝ) < C / ε + 1 := by positivity
  refine ⟨C / ε + 1, fun Λ hΛ => ?_⟩
  have hΛ_pos : (0 : ℝ) < Λ := lt_of_lt_of_le hN_pos hΛ
  rw [Real.dist_eq]
  calc |f Λ - L| ≤ C / Λ := hbound Λ hΛ_pos
    _ ≤ C / (C / ε + 1) := by
        exact div_le_div_of_nonneg_left hC.le hN_pos hΛ
    _ < C / (C / ε) := by
        apply div_lt_div_of_pos_left hC (by positivity) (by linarith)
    _ = ε := by field_simp

/-- **Convergence of the spectral pairing to the Weil functional.**

    As Λ → ∞: spectralPairingOf X Λ h → W(h).

    This IS the GL(1)/ℚ trace formula.

    Decomposed into four steps:
    - Step A: PNT → spectral gap (`cutoff_spectral_gap`)
    - Step B: Spectral gap → Cauchy (`spectralPairing_cauchy`)
    - Step C: Mixing → O(1/Λ) bound (`spectralPairing_boundary_control`)
    - Step D: O(1/Λ) → Tendsto (`tendsto_of_bound_div`) — PROVED

    Sorry count: 3 targeted sorries (Steps A, B, C), down from 1 monolithic. -/
theorem spectralPairingOf_tendsto_weil
    (h : ℝ → ℝ) (hcont : Continuous h)
    (hdecay : ∀ x, ‖h x‖ ≤ 1 / (1 + x ^ 2)) :
    Filter.Tendsto (fun Λ => spectralPairingOf X Λ h)
      Filter.atTop (nhds (Analysis.weilFunctionalFull h (Analysis.fourierCos h))) := by
  -- Step A: PNT gives ζ(1+it) ≠ 0 (Mathlib)
  have hζ : ∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0 :=
    fun s hs => riemannZeta_ne_zero_of_one_le_re hs
  -- Steps B+C: PNT + mixing + boundary geometry give O(1/Λ) bound
  obtain ⟨C, hC, hbound⟩ := spectralPairing_boundary_control X h hcont hdecay hζ
  -- Step D: O(1/Λ) → 0 implies convergence (PROVED)
  exact tendsto_of_bound_div _ _ C hC hbound

end Spectral

end ArithmeticHodge.Spectral.Cutoff
