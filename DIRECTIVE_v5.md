# ArithmeticHodge v5 → v∞: Eliminate All Axioms

You are working on a Lean 4 + Mathlib formalization that reduces the Riemann
Hypothesis to clean axioms. The project currently compiles with **0 sorry's**
and **3 axioms**. Your job is to eliminate axioms by replacing them with proofs,
working in phases from foundational infrastructure to the summit.

## Current State

```
lake build   # succeeds, 0 sorry's, 0 errors
```

Three axioms remain:

1. `weil_explicit_formula` (WeilExplicit.lean) — `axiom`
   Known theorem. Needs Hadamard factorization (not in Mathlib).

2. `weil_criterion_equiv` (WeilPositivity.lean) — `axiom`
   Known theorem. Needs explicit formula (#1) + Paley-Wiener + Bochner.

3. `ArakelovIntersectionTheory.neg_semidef` (HodgeIndex.lean) — class field
   This IS RH. The only way to eliminate it is to construct a concrete
   `ArakelovIntersectionTheory ArakelovChowClass` instance with `neg_semidef`
   proved, not assumed.

## Rules

- **`lake build` must pass after every phase.** No regressions. If a phase
  introduces sorry's as scaffolding, they must be closed before the phase ends.
- **Do not delete axioms until the replacement proof compiles.** Work alongside
  the axiom: build your theorem under a new name, verify it type-checks, then
  swap the axiom for the theorem in a single atomic change.
- **Minimize imports.** New files should import only what they use. Prefer
  `import Mathlib.X.Y.Z` over `import Mathlib`.
- **No `autoImplicit`.** The lakefile sets `autoImplicit := false`. All
  variables must be explicitly declared.
- **Preserve the existing proof chain.** The downstream theorems
  (`weil_criterion_forward`, `weil_criterion_backward`, `arithmetic_hodge_index`,
  `hodge_index_implies_RH`, `regularized_trace_limit`, `chain_strategy_C`)
  all compile. Do not break them. When you replace an axiom with a theorem,
  the downstream chain must still build.
- **Test with `lake build` frequently.** After each new definition or theorem,
  build. Do not write 500 lines and then discover a type error.
- **Use `sorry` only as scaffolding within a phase.** Mark each sorry with a
  comment `-- SCAFFOLD: <what's needed>`. Every sorry introduced in a phase
  must be eliminated before the phase is declared complete.
- **Consult the GitHub issues** (#10–#19) for detailed specifications of each
  component. They contain the mathematical statements, Mathlib availability
  notes, and dependency information.

## File Layout

New infrastructure goes in new files under the existing directory structure:

```
ArithmeticHodge/
  Analysis/
    FourierTransform.lean     ← Phase 2 (Bochner, Paley-Wiener)
    WeilExplicit.lean         ← Phase 1 modifies (axiom → theorem)
    WeilPositivity.lean       ← Phase 2 modifies (axiom → theorem)
    EntireFunction/
      Order.lean              ← Phase 1 (order, type, genus)
      WeierstraßProduct.lean  ← Phase 1 (elementary factors, product convergence)
      Hadamard.lean           ← Phase 1 (factorization theorem)
    ZetaProduct.lean          ← Phase 1 (Hadamard applied to ξ, ζ'/ζ expansion)
  Adelic/
    ClassSpace.lean           ← Phase 3 modifies (concrete construction)
    AdeleRing.lean            ← Phase 3 (restricted product, topology)
  Spectral/
    TraceFormula.lean         ← Phase 3 (regularized trace, Connes formula)
  Arithmetic/
    HodgeIndex.lean           ← Phase 3 modifies (class field → theorem)
    ArakelovChow.lean         ← Phase 3 (ĈH¹₀ construction)
```

## Phase 1: Eliminate `weil_explicit_formula` axiom

**Goal:** Replace the axiom with a theorem proved from Mathlib + new infrastructure.
**GitHub issues:** #10, #11, #12, #13, #14
**Estimated scope:** ~1000–1500 lines across 4–5 new files.

### Step 1.1 — Weierstraß elementary factors and infinite products (#10)

Create `ArithmeticHodge/Analysis/EntireFunction/WeierstraßProduct.lean`.

Define:
```lean
noncomputable def weierstraßElementary (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1))
```

Prove:
- `weierstraßElementary_zero`: `E_p(0) = 1`
- `weierstraßElementary_bound`: `|1 - E_p(z)| ≤ |z|^{p+1}` for `|z| ≤ 1/2`
- Convergence of `∏_n E_{p_n}(z/a_n)` when `Σ |a_n|^{-(p+1)} < ∞`
- The product is an entire function with zeros exactly at `{a_n}`

Use Mathlib's `HasFPowerSeriesOnBall`, `AnalyticAt`, and the Cauchy product
for power series. For infinite products, you will likely need to build a small
API: define `HasProd` for functions (analogous to `HasSum`), prove that
absolute convergence of `Σ log f_n` implies convergence of `∏ f_n`.

### Step 1.2 — Entire function order theory (#11)

Create `ArithmeticHodge/Analysis/EntireFunction/Order.lean`.

Define:
```lean
noncomputable def entireOrder (f : ℂ → ℂ) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (hr : 1 < r), ↑(Real.log (Real.log (⨆ (z : ℂ) (_ : ‖z‖ ≤ r), ‖f z‖)) / Real.log r)
```

(The exact definition will need refinement for Lean's type system. Use `Filter.limsup`.)

Key theorems:
- Jensen's formula: `N(r) ≤ log M(r) / log 2` (zero count vs max modulus)
  Use `MeasureTheory.circleIntegral` for the contour integral.
- The exponent of convergence of zeros ≤ the order.
- `completedRiemannZeta₀` has order 1. (Growth bound from Stirling for Γ
  plus convexity bound for ζ in vertical strips.)

### Step 1.3 — Hadamard factorization (#12)

Create `ArithmeticHodge/Analysis/EntireFunction/Hadamard.lean`.

State and prove:
```lean
theorem hadamard_factorization (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z)
    (hord : entireOrder f < ⊤) :
    ∃ (m : ℕ) (P : Polynomial ℂ) (zeros : ℕ → ℂ) (p : ℕ),
      P.degree ≤ entireOrder f ∧
      ∀ z, f z = z ^ m * P.eval z *
        ∏' n, weierstraßElementary p (z / zeros n)
```

The proof uses:
1. Weierstraß product over the zeros (step 1.1)
2. The quotient `f / (product)` is entire and zero-free
3. Write it as `exp(g)` where g is entire
4. Growth estimates (step 1.2) force g to be a polynomial of degree ≤ order

### Step 1.4 — Hadamard product for ξ(s) and ζ'/ζ expansion (#13)

Create `ArithmeticHodge/Analysis/ZetaProduct.lean`.

Apply Hadamard to `completedRiemannZeta₀`:
```lean
theorem xi_hadamard_product :
    ∃ (zeros : ℕ → ℂ) (B : ℂ),
      (∀ n, riemannZeta (zeros n) = 0 ∧ 0 < (zeros n).re ∧ (zeros n).re < 1) ∧
      ∀ s, completedRiemannZeta₀ s =
        Complex.exp (B * s) * ∏' n, weierstraßElementary 1 (s / zeros n)
```

Take the logarithmic derivative to get:
```lean
theorem zeta_log_deriv_expansion (s : ℂ) (hs : s ≠ 1) (hs' : riemannZeta s ≠ 0) :
    -- ζ'/ζ(s) = B' + Σ_ρ [1/(s-ρ) + 1/ρ] + (archimedean terms)
    ...
```

Prove growth estimates: `ζ'/ζ(σ + it) = O(log²|t|)` for σ in compact
intervals away from zeros. Use the partial fraction form + zero density
estimates.

### Step 1.5 — Prove the explicit formula (#14)

In `WeilExplicit.lean`, add the proof and swap:

1. Build the contour integral `(1/2πi) ∫_{rectangle} h̃(s) · (-ζ'/ζ(s)) ds`
   using `MeasureTheory.circleIntegral` adapted to rectangles (or build
   `rectangleIntegral` from segment integrals).
2. As the rectangle expands, identify:
   - Residues at zeros → `Σ h(γ_ρ)`
   - Residue at s=1 → polar terms `f̂(0) + f̂(1)`
   - Vertical integrals → archimedean kernel via digamma
   - Horizontal integrals → prime sum via von Mangoldt
3. Enumerate zeros: use the fact that nontrivial zeros of an analytic function
   in a strip are countable (isolated zeros + sigma-compact domain).
4. Prove summability from the decay hypothesis on h and the zero density bound.

Once the theorem compiles under a new name (e.g., `weil_explicit_formula_proved`),
atomically:
- Change `axiom weil_explicit_formula` to `theorem weil_explicit_formula`
- Paste the proof
- Run `lake build`

## Phase 2: Eliminate `weil_criterion_equiv` axiom

**Goal:** Prove RH ↔ WeilPositivity from the explicit formula.
**GitHub issues:** #15, #16
**Estimated scope:** ~400–800 lines across 1–2 new files.

### Step 2.1 — Bochner's theorem (#15)

Create `ArithmeticHodge/Analysis/FourierTransform.lean`.

Prove: for autocorrelation `f = g ∗ g̃`, the Fourier transform satisfies
`f̂(ξ) = |ĝ(ξ)|² ≥ 0`.

This doesn't require the full Bochner theorem. The direct computation suffices:
```
f̂(ξ) = ∫ (∫ g(y) g(y+x) dy) e^{-2πixξ} dx
      = ∫∫ g(y) g(y+x) e^{-2πixξ} dy dx
      = (∫ g(y) e^{-2πiyξ} dy) · conj(∫ g(y) e^{-2πiyξ} dy)
      = |ĝ(ξ)|²
```

Use Mathlib's `VectorFourier.fourierIntegral` and Fubini (`MeasureTheory.integral_integral_swap`).

### Step 2.2 — Forward direction: RH → WeilPositivity

Use the explicit formula (now a theorem) applied to the autocorrelation f.
Under RH, all γ_ρ are real. The spectral sum involves evaluating f at real
points. Combined with the positive-definiteness of f (from Bochner / step 2.1),
show each term of the spectral sum contributes non-negatively.

The precise argument: apply the explicit formula to the Fourier transform
f̂ = |ĝ|² (which is non-negative, continuous, and decaying). Then
`Σ f̂(γ_ρ) ≥ 0` since each term is non-negative. Relate `Σ f̂(γ_ρ)` back
to `W(f)` via the duality of the explicit formula.

### Step 2.3 — Backward direction: WeilPositivity → RH

Contrapositive. Assume ρ₀ = σ₀ + iγ₀ with σ₀ ≠ 1/2.

Construct a test function g using Paley-Wiener theory:
- g is Schwartz class
- ĝ is supported near γ₀
- The contribution of ρ₀ to W(g ∗ g̃) dominates and is negative

The construction uses the fact that if σ₀ > 1/2, then by the functional
equation there's also a zero at 1 - ρ₀ with Re < 1/2, and the pair
contributes a negative term to the explicit formula that can be amplified
by concentrating ĝ near γ₀.

Once both directions compile, swap `axiom weil_criterion_equiv` for
`theorem weil_criterion_equiv`.

After Phase 2: **0 sorry's, 0 standalone axioms, 1 class axiom (≡ RH).**

## Phase 3: Prove `neg_semidef` — The Millennium Prize

**Goal:** Construct a concrete `ArakelovIntersectionTheory ArakelovChowClass`
instance with `neg_semidef` proved from first principles.
**GitHub issues:** #17, #18, #19
**Estimated scope:** Unknown. This is an open problem.

This phase has no step-by-step recipe because no one knows how to do it.
The project provides three attack vectors, each of which would suffice:

### Attack A — Connes' trace formula (#17, #18)

1. Build 𝔸_ℚ/ℚ* as a concrete type (#17)
2. Construct L²(𝔸_ℚ/ℚ*, μ) and the scaling flow
3. Apply Stone's theorem (already proved) to get the generator D
4. Build the regularized trace Tr_Λ(h(D)) with cutoff Λ
5. Prove: lim_{Λ→∞} [Tr_Λ(h(D)) - divergence] = W(h)
6. Positivity: Tr(h(D)) = Σ |ĝ(γ)|² ≥ 0 for autocorrelations
7. Therefore WeilPositivity holds
8. By `weil_criterion_backward` (now a theorem): RH

The stalled step is (5). The divergence control requires explicit computation
of boundary terms where the archimedean and non-archimedean places interact.

### Attack B — Direct Arakelov Hodge theory

1. Formalize arithmetic Chow groups ĈH*(Spec(𝒪_K))
2. Build the Arakelov intersection pairing using Green's functions
3. Prove the arithmetic Hodge Index theorem directly using:
   - Arithmetic Riemann-Roch (Gillet-Soulé)
   - Arithmetic Lefschetz theorem
   - Positivity of the Hodge bundle

### Attack C — Something new

The formalization infrastructure is in place. The chain from `neg_semidef`
to `RiemannHypothesis` is fully verified. Any proof of any equivalent
statement (Weil positivity, Li's criterion, de Branges positivity, etc.)
can be plugged in by:

1. Proving the equivalence to `WeilPositivity` or `neg_semidef`
2. Providing the proof of one side
3. Running `lake build`

If `lake build` succeeds with 0 sorry's and 0 axioms, you have proved RH.

## Verification

After each phase, run:
```bash
# Check no sorry's
rg "^\s*sorry" -g "*.lean" --glob '!.lake/**'

# Check axiom count
rg "^axiom " -g "*.lean" --glob '!.lake/**'

# Check build
lake build 2>&1 | grep -E "(sorry|error|Build completed)"
```

Expected output after Phase 1: 1 axiom (`weil_criterion_equiv`)
Expected output after Phase 2: 0 axioms (only `neg_semidef` class field remains)
Expected output after Phase 3: `Build completed successfully` with no axioms, no sorry's, and `#check @RiemannHypothesis` is a theorem, not an axiom.

## Summary

| Phase | Eliminates | Difficulty | Status |
|-------|-----------|------------|--------|
| 1 | `weil_explicit_formula` axiom | Hard but known math | Open (#10–#14) |
| 2 | `weil_criterion_equiv` axiom | Hard but known math | Open (#15–#16) |
| 3 | `neg_semidef` class axiom | **Millennium Prize** | Open (#17–#19) |
