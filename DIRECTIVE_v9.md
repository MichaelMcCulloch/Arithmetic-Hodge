# DIRECTIVE v9: Fill the Five Sorries

You are an agent working on a 6,000-line Lean 4 formalization of the
Riemann Hypothesis. The proof compiles. The main theorem chain has
**zero sorry in its body**. Every sorry is in a leaf.

You did not build this. Someone else did. Your job is to fill ONE sorry.
Read this directive, understand the architecture, then fill your assigned sorry.

---

## BEFORE YOU WRITE A SINGLE LINE OF CODE

```bash
make cache
```

This pulls the Mathlib build cache. Without it, `lake build` takes hours.
With it, minutes. Run it first. Run it every time. No exceptions.

---

## THE PROOF CHAIN (already proved)

Open `TraceFormula.lean`. Read `riemann_hypothesis_from_trace`. It says:

```
theorem riemann_hypothesis_from_trace
    (X : Type*) [Adelic.AdeleClassSpaceData X] :
    RiemannHypothesis :=
  Analysis.weil_criterion_backward (weil_positivity_from_spectral_pairing X)
```

One line. Zero sorry. It calls `weil_positivity_from_spectral_pairing`,
which calls `weil_nonneg_of_spectral_pairing`, which uses two facts:

```
spectralPairing_nonneg          — PROVED (Bochner + normSq via tsum_nonneg)
spectralPairing_tendsto_weil    — sorry (the trace formula convergence)
```

The first says: the spectral pairing `Σ (fourierCos h)(λᵢ) · |⟨Ω,eᵢ⟩|²`
is non-negative for autocorrelations. Proved from:
- `fourierCos h ≥ 0` for autocorrelations (Bochner's theorem)
- `|⟨Ω,eᵢ⟩|² ≥ 0` (Complex.normSq, by definition)
- `tsum_nonneg` (sum of non-negatives is non-negative)

The second says: as Λ → ∞, the spectral pairing converges to W(h).
That is the GL(1)/ℚ trace formula. That is where the money is.

The limit argument is proved: `ge_of_tendsto` gives W(h) ≥ 0 from
non-negativity + convergence. Then `weil_criterion_backward` gives RH.

**Nothing in the main chain needs to be touched.** You fill leaves.

---

## THE FIVE CRITICAL SORRIES

These are the five sorries on the critical path. When all five are filled,
`riemann_hypothesis_from_trace` has zero sorry in its entire transitive
dependency tree. Everything else (16 infrastructure sorries on the old
Weil criterion path) is secondary.

### Sorry 1: L² integrability of autocorrelation generators
**GitLab: #24** | `TraceFormula.lean:59` | Label: `critical-path`

```lean
have hg_sq : Integrable (fun y => g y ^ 2) volume := by sorry
```

Given g ∈ L¹ and f = g ∗ g̃ with ‖f x‖ ≤ 1/(1+x²), show g ∈ L².

**Approach:** Either strengthen `IsAutocorrelation` to include g ∈ L²
(cleanest — update the definition in WeilDefs.lean and fix the 4 call
sites), or prove it from `f(0) = ∫ g² ≤ 1` using the Bochner integral's
interaction with non-negative integrands.

**Estimated effort:** 20 lines if you change the definition, 40 if you prove it.

---

### Sorry 2: Fubini identity for the Fourier autocorrelation
**GitLab: #13** | `FourierTransform.lean:178` | Label: `critical-path`

```lean
suffices key : ∫ x, (f x : ℂ) * E x = starRingEnd ℂ ĝ * ĝ by ...
sorry
```

The conjugation identity `∫ g(y) E(-y) = conj(ĝ)` is **already proved**
(`hint_conjg`). What remains is the Fubini swap + substitution:

1. Distribute E(x) into the inner integral
2. **Fubini** — swap ∫∫ (needs product integrability: ‖g‖₁² < ∞)
3. Factor g(y) out of inner integral
4. Substitute u = y+x (`integral_add_right_eq_self`, already used in codebase)
5. Split E(u-y) = E(u)·E(-y) (`hE_add`, already proved)
6. Factor the constant ∫ g·E out, apply `hint_conjg`

**Key Mathlib lemma:** `MeasureTheory.integral_integral_swap` for the Fubini
step. Product integrability: ∫∫ |g(y)||g(y+x)| dx dy = ‖g‖₁² < ∞.

**Estimated effort:** 60-80 lines. The hardest part is product integrability.

---

### Sorry 3: Cutoff eigenvalues of D_Λ
**GitLab: #21** | `CutoffHilbertSpace.lean:115` | Label: `critical-path`

```lean
noncomputable def cutoffEigenvaluesOf (X : Type*) [AdeleClassSpaceData X] (Λ : ℝ) : ℕ → ℝ
```

Construct the eigenvalues of the scaling flow generator on L²(X, μ_Λ).

**Approach:**
1. Define the Koopman operator U_t on `CutoffL2 X Λ`: f ↦ f ∘ σ_t
2. Show {U_t} is strongly continuous unitary (measure-preserving + continuous)
3. Stone's theorem → self-adjoint generator D_Λ (infrastructure in SelfAdjointness.lean)
4. Compact domain → compact resolvent → discrete spectrum
5. Extract eigenvalues

**Infrastructure available:**
- `CutoffL2 X Λ` = `Lp ℂ 2 (cutoffMeasure X Λ)` — defined, Hilbert space by Mathlib
- `vacuumVector` — defined as `indicatorConstLp`
- `cutoffMeasure_isFinite` — proved
- `AdeleClassSpaceData.scalingFlow` — continuous group automorphisms

**Estimated effort:** 200+ lines (Koopman operator + Stone + compact resolvent).

---

### Sorry 4: Cutoff eigenbasis
**GitLab: #22** | `CutoffHilbertSpace.lean:122` | Label: `critical-path`

```lean
noncomputable def cutoffEigenbasis (X : Type*) [AdeleClassSpaceData X] (Λ : ℝ) :
    HilbertBasis ℕ ℂ (Lp ℂ 2 (cutoffMeasure X Λ))
```

The eigenvectors of D_Λ form a complete orthonormal system.

**Approach:** From Sorry 3, the spectral theorem for compact self-adjoint
operators gives an eigenbasis. Use Mathlib's `IsCompact` + `HilbertBasis.mk`
or construct directly.

**Depends on:** Sorry 3.

**Estimated effort:** 50 lines on top of Sorry 3.

---

### Sorry 5: THE TRACE FORMULA — spectral pairing convergence
**GitLab: #23** | `CutoffHilbertSpace.lean:181` | Label: `million-dollar`

```lean
theorem spectralPairingOf_tendsto_weil (X : Type*) [AdeleClassSpaceData X]
    (h : ℝ → ℝ) (hcont : Continuous h) (hdecay : ...) :
    Tendsto (fun Λ => spectralPairingOf X Λ h) atTop (nhds (weilFunctionalFull h (fourierCos h)))
```

As Λ → ∞, `Σ (fourierCos h)(λᵢ) · |⟨Ω,eᵢ⟩|²` converges to W(h).

**This is the trace formula for GL(1)/ℚ.** It is Tate's thesis repackaged
in operator language. It is the last sorry on the critical path. If this
compiles, and Sorries 1-4 compile, then `riemann_hypothesis_from_trace`
proves `RiemannHypothesis` with zero sorry ancestry.

**The ergodicity argument:**

Step A: **PNT → spectral gap.** ζ(1+it) ≠ 0 for all t ∈ ℝ. This is in
Mathlib: `riemannZeta_ne_zero_of_one_le_re`. In operator language: the
scaling flow has no eigenvalue at Re(s) = 1. No slow modes.

Step B: **Spectral gap → mixing (RAGE theorem).** No eigenvector at the
boundary implies continuous spectral measure, which by the RAGE theorem
(Ruelle-Amrein-Georgescu-Enss) implies mixing. The proof uses the spectral
theorem + Riemann-Lebesgue lemma + finite-rank approximation. ~60 lines.

Step C: **Mixing → boundary control.** The kernel K_h(x,y) decays as
|x-y| → ∞ (from mixing). The boundary of {|x| ≤ Λ} has volume O(Λ⁻¹)
relative to the bulk (from the geometry of the adèle class space).
Therefore |spectralPairing_Λ - W(h)| ≤ C/Λ.

Step D: **C/Λ → 0.** Standard ε-δ. The squeezing argument
`trace_eq_weil_of_boundary_control` in ResolventComputation.lean is
already proved.

**Depends on:** Sorries 3 and 4 (eigenvalues and eigenbasis).

**Estimated effort:** 500-1000 lines. This is where the real mathematics lives.

---

## WHAT THE SPECTRAL PAIRING IS

The spectral pairing is defined in `CutoffHilbertSpace.lean`:

```lean
noncomputable def spectralPairingOf (Λ : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∑' i, Analysis.fourierCos h (cutoffEigenvaluesOf X Λ i) *
    vacuumWeightOf X Λ i
```

where `vacuumWeightOf X Λ i = Complex.normSq (vacuumAmplitudeOf X Λ i)`
and `vacuumAmplitudeOf X Λ i = ⟪vacuumVector X Λ, cutoffEigenbasis X Λ i⟫_ℂ`.

This is **⟨ĥ(D_Λ)Ω, Ω⟩** — the vacuum expectation value of the Fourier-
transformed test function applied to the cutoff operator. It applies
`fourierCos h` (NOT h) to the eigenvalues, weighted by squared vacuum
overlaps.

For autocorrelations: `fourierCos h ≥ 0` (Bochner). Weights ≥ 0 (normSq).
Sum ≥ 0 (tsum_nonneg). **Proved.**

The trace formula says this converges to `W(h)` as Λ → ∞. **That is Sorry 5.**

---

## WHY THIS IS NOT EQUIVALENT TO RH

The spectral pairing is non-negative for autocorrelations because of
Bochner's theorem (Fourier transforms of positive-definite functions are
non-negative). This has nothing to do with zeta zeros.

The convergence to W(h) is the trace formula — an accounting identity
between spectral and geometric sides. This has nothing to do with WHERE
the zeros are.

Neither ingredient mentions the zeros. The zeros are constrained BY the
argument, not assumed in it. The fire is the emergent property.

---

## RULES

1. **`make cache` before anything else.**
2. `lake build` after every theorem.
3. No sorry without a proof attempt.
4. When Mathlib doesn't have a lemma, write it.
5. Do not refactor working code in files you don't own.
6. When you finish a sorry, update or close the GitLab issue.
7. Track: sorry count, lines added, theorems proved.

## ASSIGNMENT

You have been assigned **one** of the five critical sorries above.
Read the entire file containing your sorry. Read the files it imports.
Understand what's proved and what isn't. Then fill it.

If your sorry depends on another sorry (e.g., Sorry 4 depends on Sorry 3),
and that sorry hasn't been filled yet, you may sorry the dependency and
note it. But fill YOUR sorry with real proof, not cascading sorry.

Start with `make cache`. Then `lake build`. Then begin.
