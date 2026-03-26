# DIRECTIVE v10: Five Sorries to Zero

The main theorem chain — `riemann_hypothesis_from_trace` — compiles with
**zero sorry in TraceFormula.lean**. The Bochner/Fourier positivity chain
is fully proved. The limit argument is proved. The Weil criterion is proved.

Five sorries remain. All in `CutoffHilbertSpace.lean`. All on the critical
path. When they fall, `riemann_hypothesis_from_trace` has zero sorry in its
entire transitive closure, and the Riemann Hypothesis is a theorem of Lean 4.

---

## BEFORE YOU TOUCH ANYTHING

```bash
make cache
```

Run this in the root of YOUR WORKTREE. Not `/home/michael/Development/Arithmetic-Hodge`.
Your worktree root. Then `lake build`. If it doesn't succeed, stop and report.

---

## THE CHAIN (all proved, zero sorry)

```
spectralPairingOf_nonneg         — PROVED (tsum_nonneg + Bochner + normSq)
spectralPairingOf_tendsto_weil   — PROVED (chains Steps A→D below)
  └─ tendsto_of_bound_div       — PROVED (ε-δ via Metric.tendsto_atTop)
weil_nonneg_of_spectral_pairing  — PROVED (ge_of_tendsto)
weil_positivity_from_spectral_pairing — PROVED
riemann_hypothesis_from_trace    — PROVED
```

The five sorries feed into `spectralPairingOf_tendsto_weil` through Steps A-D.
Step D is proved. Steps A-C have sorries. Steps A-C need eigenvalues (Sorry 1)
and an eigenbasis (Sorry 2). That's it. Five leaves.

---

## THE FIVE SORRIES

All in `ArithmeticHodge/Spectral/CutoffHilbertSpace.lean`.

### Sorry 1 (line 200): `cutoffEigenvaluesOf` — Eigenvalue extraction
**GitLab #21**

```lean
noncomputable def cutoffEigenvaluesOf (Λ : ℝ) : ℕ → ℝ
```

Extract eigenvalues of D_Λ (scaling flow generator on the compact cutoff).

**What's already built (proved, in this file):**
- `koopmanOp` — Koopman operator U_t on L² via `Lp.compMeasurePreserving` (PROVED isometric)
- `scalingFlow_measurePreserving` — flow preserves Haar (PROVED)
- `discrete_spectrum_of_compact_domain` — compact domain → discrete spectrum (PROVED)
- `cutoffSet_compact`, `cutoffMeasure_isFinite` — compactness/finiteness (PROVED)

**What's missing:** Apply Stone's theorem to {U_t} → self-adjoint generator D_Λ → compact resolvent → extract eigenvalue sequence. The codebase has Stone's theorem in `SelfAdjointness.lean`. The gap is: connecting `koopmanOp` (defined on L²(X, haarMeasure)) to the cutoff space L²(X, cutoffMeasure Λ), proving compact resolvent from `cutoffSet_compact`, and extracting the discrete spectrum as `ℕ → ℝ`.

**Approach:** Define the projected Koopman on `CutoffL2` by composing with restriction. The compact resolvent follows from Rellich-Kondrachov (compact embedding H¹ ↪ L² on compact domains). The eigenvalue extraction is then standard: self-adjoint + compact resolvent → countable spectrum accumulating at ±∞.

---

### Sorry 2 (line 251): `cutoffEigenbasis` — Eigenbasis as HilbertBasis
**GitLab #22**

```lean
noncomputable def cutoffEigenbasis (Λ : ℝ) :
    HilbertBasis ℕ ℂ (Lp ℂ 2 (cutoffMeasure X Λ)) :=
  HilbertBasis.ofRepr sorry
```

**What's already built (proved):**
- `cutoffMeasure_isSeparable` — PROVED
- `cutoffL2_secondCountableTopology` — PROVED
- `exists_cutoffHilbertBasis` — a Hilbert basis EXISTS (PROVED via `exists_hilbertBasis`)

**What's missing:** The `sorry` is a `LinearIsometryEquiv` from `CutoffL2 X Λ` to `ℓ²(ℕ, ℂ)`. We know a Hilbert basis exists indexed by some set. The gap is re-indexing to ℕ (separable Hilbert spaces are isomorphic to ℓ²(ℕ)).

**Approach:** From `exists_cutoffHilbertBasis`, get `⟨w, basis_w⟩`. The index set `w` is countable (separable Hilbert space). Use `Equiv.ofBijective` or `Set.Countable.exists_equiv_nat` to get `w ≃ ℕ`, then `HilbertBasis.reindex` to re-index the basis.

---

### Sorry 3 (line 322): `cutoff_spectral_gap` — PNT → eigenvalue bound
**GitLab #23**

```lean
theorem cutoff_spectral_gap
    (hζ : ∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0) (Λ : ℝ) (hΛ : 0 < Λ) :
    ∀ (i : ℕ), cutoffEigenvaluesOf X Λ i ≠ 0 →
      |cutoffEigenvaluesOf X Λ i| < Λ := by
  sorry
```

PNT (ζ(1+it) ≠ 0, in Mathlib as `riemannZeta_ne_zero_of_one_le_re`) translated to: nonzero eigenvalues of D_Λ are bounded by Λ.

**Approach:** The eigenvalues of D_Λ correspond to characters of the scaling flow restricted to the cutoff. ζ(1+it) ≠ 0 means no character at Re(s)=1 is in L², giving a gap. On the cutoff {|x| ≤ Λ}, the eigenvalues are bounded by the cutoff scale. This is a translation lemma — the content is in Mathlib, the wrapping is operator theory.

**Note:** This may depend on Sorry 1 (eigenvalue construction). If so, sorry the dependency and focus on the implication structure.

---

### Sorry 4 (line 350): `spectralPairing_cauchy` — RAGE / spectral gap → convergence
**GitLab #23**

```lean
theorem spectralPairing_cauchy (h : ℝ → ℝ) (hcont : Continuous h)
    (hdecay : ∀ x, ‖h x‖ ≤ 1 / (1 + x ^ 2))
    (hζ : ∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0) :
    ∀ ε > 0, ∃ N : ℝ, ∀ Λ ≥ N, |spectralPairingOf X Λ h - W(h)| < ε := by
  sorry
```

The RAGE theorem: spectral gap → mixing → the spectral pairing converges.

**Approach:** This follows from Sorry 5 (boundary control gives O(1/Λ) rate, which gives ε-convergence by choosing Λ = C/ε). If Sorry 5 is proved first, this is a one-liner: `obtain ⟨C, hC, hbound⟩ := spectralPairing_boundary_control ...; exact ⟨C/ε, ...⟩`.

---

### Sorry 5 (line 372): `spectralPairing_boundary_control` — O(1/Λ) rate
**GitLab #23**

```lean
theorem spectralPairing_boundary_control (h : ℝ → ℝ) (hcont : Continuous h)
    (hdecay : ∀ x, ‖h x‖ ≤ 1 / (1 + x ^ 2))
    (hζ : ∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0) :
    ∃ (C : ℝ), 0 < C ∧ ∀ (Λ : ℝ), 0 < Λ →
      |spectralPairingOf X Λ h - W(h)| ≤ C / Λ := by
  sorry
```

The boundary control: the spectral pairing differs from W(h) by O(1/Λ).

**This is the hardest sorry.** It requires:
1. The Selberg unfolding: the spectral pairing on the cutoff differs from the full trace by boundary terms
2. Boundary volume estimate: ∂{|x| ≤ Λ} has measure O(1/Λ) relative to the bulk
3. Kernel decay from mixing (RAGE): K_h(x,y) → 0 as |x-y| → ∞
4. Combining: boundary volume × kernel bound = O(1/Λ)

**Approach:** The key geometric input is that `heightFn` grows like log|x| on the adèle class space, so the boundary shell {Λ-1 ≤ heightFn ≤ Λ} has volume O(Λ⁻¹) times the bulk volume. Combined with the test function decay `|h(x)| ≤ 1/(1+x²)`, the boundary integral is O(1/Λ).

---

## DEPENDENCY GRAPH

```
Sorry 1 (eigenvalues) ←── Sorry 3 (spectral gap)
Sorry 2 (eigenbasis)  ←── Sorry 3
                           Sorry 3 ←── Sorry 4 (RAGE/Cauchy)
                                        Sorry 4 ←── Sorry 5 (boundary control)
                                                      │
                                        OR: Sorry 5 ──┘ (4 follows from 5 trivially)
```

Sorries 1 and 2 are constructions (independent of each other).
Sorry 3 needs 1 and 2.
Sorry 4 follows trivially from 5.
Sorry 5 is the mathematical core.

**If you can only prove one thing:** prove Sorry 5. Everything else cascades.

---

## RULES

1. `make cache` in your worktree root before anything.
2. `lake build` after every change.
3. When Mathlib doesn't have it, write it. Lean is Turing complete.
4. Don't touch files outside `CutoffHilbertSpace.lean` unless you must.
5. When done, report sorry count change, lines added, theorems proved.
6. Update the GitLab issue.
