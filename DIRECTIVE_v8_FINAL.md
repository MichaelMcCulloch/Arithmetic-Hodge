# DIRECTIVE: Prove the Riemann Hypothesis

You have built a 5,000-line Lean 4 formalization that contains two paths to RH.
You followed Path A and stopped at the class axiom, declaring the problem
unsolvable. You missed Path B entirely. Path B is already in your codebase.
You wrote it. Let me show you what you built and didn't see.

---

## THE TWO PATHS

Open `TraceFormula.lean` and read `riemann_hypothesis_from_trace`. You wrote it.
It proves `RiemannHypothesis` without mentioning `neg_semidef` at all. It goes:

```
Tr(h(D)) = W(h)          [resolvent_spectral_trace_eq_weil — 1 sorry]
Tr(h(D)) ≥ 0              [trace_nonneg_of_real_autocorrelation — PROVED]
∴ W(h) ≥ 0                [rw + exact]
∴ RiemannHypothesis        [weil_criterion_backward — PROVED]
```

Read it again. The spectral positivity — the fact that Tr(h(D)) ≥ 0 for any
autocorrelation h — is PROVED. You proved it in `SpectralPositivity.lean`. It
follows from: h(D) = ĝ(D)* ∘ ĝ(D), so ⟨h(D)x, x⟩ = ‖ĝ(D)x‖² ≥ 0, and the
trace of a positive operator is non-negative. Zero sorry. Done.

The backward Weil criterion — the fact that Weil positivity implies RH — is
PROVED. You proved it from the Hadamard infrastructure. Zero sorry in the
theorem itself.

The ONLY thing between you and RH is one sorry:

```lean
theorem resolvent_spectral_trace_eq_weil ... :
    operatorTrace (sc.apply (fun t => (h t : ℂ))) basis =
    Analysis.weilFunctionalFull h (Analysis.fourierCos h) := by
  sorry
```

This says: **the spectral trace of h(D) equals the Weil functional.**

You wrote, in the comment above this theorem:

> "None is the Riemann Hypothesis. Their combination is RH."

You were right. And then you lost your nerve and told the user it was
impossible. It is not impossible. It is a trace formula. Trace formulas
are proved mathematics. Let me show you how.

---

## WHAT THE SORRY ACTUALLY SAYS

The Weil functional W(h) is defined (in your `WeilDefs.lean`) as three terms:

    W(h) = h_hat(0) + h_hat(1)                              [polar]
           - Σ_p Σ_m (log p / p^{m/2}) · h(m log p)         [primes]
           + (archimedean integral)                           [Γ-factor]

The spectral trace Tr(h(D)) is:

    Tr(h(D)) = Σᵢ ⟨h(D)eᵢ, eᵢ⟩ = ∫_ℝ h(λ) dμ(λ)

where μ is the spectral measure of D.

The trace formula says these are equal. This is NOT a conjecture about where
the zeros are. It is an accounting identity: **two ways of computing the same
physical quantity agree**. The spectral side counts eigenfrequencies. The
geometric side counts periodic orbits (primes). They compute the same thing
because they're both computing the trace of the same operator.

This is exactly what Selberg proved for hyperbolic surfaces in 1956. It is
what Tate proved for GL(1)/ℚ in 1950. It is what Arthur proved for GL(n)
in the 1970s-80s. Trace formulas are PROVED THEOREMS, not conjectures.

The specific trace formula you need is the simplest one in the family: the
GL(1) trace formula over ℚ. It IS Tate's thesis, repackaged in operator
language.

---

## WHY THE TRACE FORMULA IMPLIES RH (WITHOUT BEING EQUIVALENT TO RH)

This is the crucial logical point that you missed. Let me be precise.

**Claim:** The trace formula Tr(h(D)) = W(h) is NOT equivalent to RH. It is
a consequence of the CONSTRUCTION of D, not of the LOCATION of the zeros.

**Proof that it's not equivalent:** The trace formula holds for the Laplacian
on any Riemannian manifold (this is the Selberg/heat kernel trace formula).
The eigenvalues of the Laplacian need not satisfy any analogue of RH. The
trace formula is a fact about the operator, not about the eigenvalues.

**Why it nevertheless implies RH:** Because spectral positivity is ALSO a
fact about the operator, not about the eigenvalues. And the combination
(trace formula + spectral positivity) forces Weil positivity, which IS RH.

The magic: neither ingredient mentions the zeros. The trace formula connects
the spectral side to the geometric side. Spectral positivity says the
spectral side is non-negative for autocorrelations. Therefore the geometric
side (= Weil functional) is non-negative. And Weil positivity ↔ RH.

The zeros never appear in the argument. They are constrained BY the argument,
not assumed in it.

---

## THE ERGODICITY ARGUMENT

The one remaining difficulty is CONVERGENCE. The adèle class space is
non-compact, so the naive trace Tr(h(D)) might diverge. The regularized
trace Tr_Λ(h(D_Λ)) is finite (compact support → trace class), but we need:

    lim_{Λ→∞} Tr_Λ(h(D_Λ)) = W(h)

You already proved half of this. `approximate_detailed_balance` shows the
regularization error is O(1/Λ). What you need is to convert this into
actual trace convergence.

**Ergodicity gives you this.** Here is the argument:

### Step 1: Spectral gap from the Prime Number Theorem

The Riemann zeta function satisfies ζ(1+it) ≠ 0 for all t ∈ ℝ.
This is in Mathlib as `riemannZeta_ne_zero_of_one_le_re`.

In the operator frame: the scaling flow σ_t on L²(𝔸_ℚ/ℚ*) has NO
eigenvalue at the "boundary" Re(s) = 1. The character |·|^{it} is NOT
in the point spectrum of the scaling operator for any t ≠ 0.

This is a **spectral gap**. It means the flow has no "slow modes" —
no directions in which correlations persist forever.

### Step 2: Spectral gap implies mixing

For a one-parameter flow on a measure space, spectral gap implies mixing:

    ⟨f ∘ σ_t, g⟩ → ⟨f, 1⟩⟨1, g⟩  as  t → ∞

for all f, g ∈ L²(X, μ). This is standard ergodic theory (Koopman-von
Neumann theorem + spectral gap ⟹ absence of eigenvectors ⟹ mixing).

### Step 3: Mixing controls boundary terms

The regularized trace Tr_Λ(h(D_Λ)) differs from the true trace by
boundary terms — integrals of the operator kernel K_h(x, y) where x or
y is near the boundary of the cutoff region {|x| ≤ Λ}.

Mixing says: the kernel K_h(x, y) = ∫ h(t) K_{σ_t}(x, y) dt decays
as |x - y| → ∞ (because correlations decay). Therefore:

    |Tr_Λ(h(D_Λ)) - W(h)| ≤ C · (boundary volume) · (kernel decay)

The boundary volume grows polynomially in Λ. The kernel decays
exponentially (from the spectral gap). Therefore the error → 0.

### Step 4: Take the limit

    Tr_Λ(h(D_Λ)) → W(h)  as  Λ → ∞
    Tr_Λ(h(D_Λ)) ≥ 0     for all Λ  (spectral positivity, PROVED)
    ∴ W(h) ≥ 0

This is Weil positivity. By `weil_criterion_backward` (PROVED), this is RH. ∎

---

## THE FORMALIZATION

### Architecture

You do NOT need to refactor the existing codebase. You need to:

1. Fill the 16 infrastructure sorries (known math — Jensen, Hadamard, etc.)
2. Prove `resolvent_spectral_trace_eq_weil` via the ergodicity argument
3. Verify that `riemann_hypothesis_from_trace` compiles with 0 sorry ancestry

The theorem `riemann_hypothesis_from_trace` is already written. It already
compiles (with sorry dependencies). Once ALL sorries in its transitive
dependency tree are filled, it proves `RiemannHypothesis`.

### The trace formula sorry: decomposition

Replace the single sorry in `resolvent_spectral_trace_eq_weil` with a chain
of lemmas:

```
-- Step A: Spectral gap
theorem zeta_nonvanishing_gives_spectral_gap :
    (∀ t : ℝ, riemannZeta (1 + t * I) ≠ 0) →
    SpectralGap D := ...

-- Step B: Mixing
theorem spectral_gap_gives_mixing :
    SpectralGap D → Mixing σ_t μ := ...

-- Step C: Boundary control
theorem mixing_controls_boundary
    (hmix : Mixing σ_t μ) (Λ : ℝ) (hΛ : 0 < Λ) :
    ‖Tr_Λ(h(D_Λ)) - W(h)‖ ≤ C / Λ := ...

-- Step D: Convergence
theorem trace_converges_to_weil
    (hmix : Mixing σ_t μ) :
    Filter.Tendsto (fun Λ => Tr_Λ(h(D_Λ))) atTop (nhds (W(h))) := ...

-- Step E: Assembly
theorem resolvent_spectral_trace_eq_weil ... := by
    have hgap := zeta_nonvanishing_gives_spectral_gap (...)
    have hmix := spectral_gap_gives_mixing hgap
    exact trace_converges_to_weil hmix ...
```

### Key Mathlib ingredients

For Step A:
- `riemannZeta_ne_zero_of_one_le_re` — ζ(s) ≠ 0 for Re(s) ≥ 1

For Step B:
- `MeasureTheory.Measure.IsHaarMeasure` — Haar measure theory
- `MeasureTheory.Ergodic` — ergodicity definitions
- The spectral gap → mixing implication is standard but may need to be built.
  It follows from: no eigenvector ⟹ spectral measure is continuous ⟹ RAGE
  theorem ⟹ mixing. The RAGE theorem is ~40 lines from Stone's theorem
  (which you already proved).

For Step C:
- `approximate_detailed_balance` — already proved, gives O(1/Λ) bound
- The boundary volume estimate needs the structure of 𝔸_ℚ/ℚ*, specifically
  that the boundary of {|x| ≤ Λ} has measure O(Λ^{-1}) relative to the bulk.

For Step D:
- Standard ε-δ from Step C.

### New definitions needed

```lean
/-- Spectral gap: no invariant vectors for the scaling flow except constants. -/
def SpectralGap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : UnboundedOperator H) : Prop :=
  ∀ x : D.domain, D.toFun x = 0 → (x : H) = 0

/-- Mixing: correlations decay under the flow. -/
def Mixing {X : Type*} [MeasurableSpace X] (σ : ℝ → X → X) (μ : Measure X) : Prop :=
  ∀ (f g : X → ℂ) (hf : Integrable f μ) (hg : Integrable g μ),
    Filter.Tendsto (fun t => ∫ x, f (σ t x) * conj (g x) ∂μ)
      atTop (nhds ((∫ x, f x ∂μ) * conj (∫ x, g x ∂μ)))
```

### The RAGE theorem (the key new infrastructure)

RAGE (Ruelle-Amrein-Georgescu-Enss) theorem: for a self-adjoint operator D
on a Hilbert space H, if D has no eigenvalues (pure continuous spectrum),
then for any compact operator K:

    (1/T) ∫₀ᵀ ‖K · e^{itD} x‖² dt → 0  as  T → ∞

This gives mixing from the spectral gap. The proof uses:
1. The spectral theorem (you have the structure, proved)
2. The Riemann-Lebesgue lemma (the Fourier transform of an L¹ function → 0)
3. Approximation of compact operators by finite-rank operators

Estimated effort: 60-80 lines. This is the same kind of functional analysis
you did for Stone's theorem. The key Mathlib ingredient is
`MeasureTheory.tendsto_integral_exp_atTop` or the Riemann-Lebesgue lemma
for spectral measures.

---

## THE 16 INFRASTRUCTURE SORRIES

These are unchanged from the previous directive. They are all textbook
mathematics from 1876-1950. Fill them in the dependency order specified
in the v7 directive. The trace formula argument above does not change
their status — they support the explicit formula and Weil criterion
equivalence, which are used by `weil_criterion_backward`.

Priority order:
1. Leaves first (Weierstraß nonvanishing, Jensen bound, Fourier/Fubini)
2. Chains (Jensen → Order → Hadamard → ξ product → explicit formula)
3. Fourier direction (autocorrelation → Weil criterion)

---

## WHAT SUCCESS LOOKS LIKE

When all 17 sorries are filled:

```lean
-- This theorem has 0 sorry in its ENTIRE transitive dependency tree.
-- It proves RiemannHypothesis as defined in Mathlib.
-- It does not use neg_semidef or any class axiom.
-- It uses only Mathlib + the infrastructure you built.
theorem riemann_hypothesis_from_trace ... : RiemannHypothesis := ...
```

```bash
$ lake build
Build completed successfully.
$ grep -rn "sorry" ArithmeticHodge/ --include="*.lean" | wc -l
0
```

If this compiles, you have proved the Riemann Hypothesis.

Not "reduced it to a class axiom." Not "formalized a known equivalence."
Proved it. Via the trace formula for GL(1)/ℚ, spectral positivity of
self-adjoint operators, and the Weil criterion. Every ingredient is either
in Mathlib or built by you from scratch.

---

## THE DISSIPATIVE FRAME, ONE LAST TIME

The scaling flow on the adèle class space is a dissipative system.
Haar measure is its steady state. Stone's theorem says the generator
is self-adjoint. The Prime Number Theorem says the system has a
spectral gap — no slow modes, no critical slowing down. The spectral
gap gives mixing — correlations decay. Mixing controls the boundary
terms in the regularized trace. The trace converges to the Weil
functional. Spectral positivity — which you proved — says the trace
is non-negative for autocorrelations. Therefore the Weil functional
is non-negative. Therefore RH.

The candle is lit by the combination of ingredients, none of which
individually is RH. The fire is the emergent property.

You built the match. You built the wick. You built the candle.

Strike it.

---

## RULES (unchanged from v7)

1. `lake build` after every theorem.
2. No sorry without a proof attempt.
3. Prefer 30 lines of proof over 3 lines of sorry + comment.
4. When Mathlib doesn't have a lemma, write it.
5. Do not refactor working code.
6. Track progress: sorry count, lines, theorems proved, failures diagnosed.
7. Work on one sorry at a time, leaves first.

Start with Phase 0: `lake build`. Count sorries. Then pick the first leaf
and begin.
