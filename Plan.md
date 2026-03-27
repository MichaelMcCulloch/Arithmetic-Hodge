# Claude Code Instructions: ArithmeticHodge Project

## Project Identity

This is a Lean 4 formalization reducing the Riemann Hypothesis to a minimal sorry surface, using the chain:

```
ZFC → ℤ with perfect distribution → additive self-duality → functional equation
→ Weil explicit formula → Weil positivity criterion ⟺ RH
```

The approach is informed by a physical intuition: mathematical structures are dissipative systems minimizing surprisal, the distributive law is a Markov blanket between additive and multiplicative structure, and the Riemann Hypothesis is a detailed balance condition — the statement that the additive-multiplicative tension resolves symmetrically at every frequency.

## Current State (Read Before Touching Anything)

### What's genuinely proved (0 sorry)
- Stone's theorem for unbounded operators (UnboundedOperator.lean — ~800 lines, fully proved including deficiency indices)
- Weierstraß elementary factor bounds, convergence, differentiability, zero characterization
- Hadamard product logarithmic derivative (hadamard_logDeriv)
- Borel-Carathéodory theorem
- Jensen's formula connection to Mathlib's logCounting
- **Jensen zero count bound** (`zeroCount_le_logMax` — n(f,r) ≤ (1/log2)·log(M(f,2r)/|f(0)|), full finsum infrastructure)
- Poisson summation, theta functional equation, zeta functional equation (from Mathlib)
- Fourier positivity of autocorrelations (fourierCos_autocorrelation_eq_sq — full Fubini proof)
- Weil criterion backward direction (positivity → RH, via Bombieri test functions)
- Spectral pairing non-negativity → convergence → Weil positivity → RH chain
- Cutoff Hilbert space infrastructure (separability, infinite-dimensionality, eigenbasis)
- **Atomless splitting lemma** (Sierpinski 1922 — `noAtoms_exists_measurableSet_pos_lt`, full proof via measure support)
- **Infinite-dimensional L²** (`noAtoms_hilbertBasis_infinite` — no sorry, uses splitting lemma)
- Haar invariance from trivial Haar character

### What's scaffolded (sorry present, known mathematics)
- `hadamard_factorization` / `hadamard_factorization_order_one` — the factorization theorem itself
- `xi_hadamard_product` — applying Hadamard to ξ(s)
- `completedZeta_order` — order of ξ is 1
- `sum_over_zeros_eq_contour` — contour integration for explicit formula
- `zeta_logDeriv_growth` — growth of ζ'/ζ in strips
- `zeta_zero_density` — N(T) ~ (T/2π)log(T/2πe)
- `bombieriAutocorrelation_weil_neg` — Bombieri's Theorem 2
- `rh_implies_weil_positivity_from_explicit` — forward Weil criterion
- ~~`zeroCount_le_logMax`~~ — **PROVED** (zero count from Jensen, full finsum infrastructure)
- `vacuumVector_norm_sq_le_one` — vacuum normalization

### What's axiomatized (the real mathematical content)
1. **`selberg_unfolding_bound`** (CutoffHilbertSpace.lean) — The Selberg trace formula boundary estimate: the spectral pairing differs from the Weil functional by O(K·M/(c·Λ)). This is THE gap in Connes' program — the absorption spectrum problem.
2. **`boundary_eigenvalue_implies_zeta_zero`** (CutoffHilbertSpace.lean) — Spectral-zeta correspondence: boundary eigenvalues of the cutoff generator correspond to zeta zeros on Re(s)≥1.

### Architecture
```
ArithmeticHodge/
├── Algebra/DistributiveCoupling.lean    # Layer 0: Ring axioms, PID, UFD
├── Analysis/
│   ├── PoissonSummation.lean            # Layer 1a: Poisson (Mathlib wrapper)
│   ├── ThetaFunction.lean              # Layer 1b: Theta (Mathlib wrapper)
│   ├── ZetaFunctionalEquation.lean     # Layer 1c: ζ functional eq (Mathlib)
│   ├── WeilDefs.lean                   # Shared defs: zeros, Fourier, Weil functional
│   ├── EntireFunction/
│   │   ├── WeierstraßProduct.lean      # Weierstraß factors (PROVED)
│   │   ├── Order.lean                  # Entire function order theory
│   │   └── Hadamard.lean              # Hadamard factorization + log derivative
│   ├── ZetaProduct.lean               # Hadamard for ξ, ζ'/ζ expansion
│   ├── WeilExplicit.lean              # Weil explicit formula
│   ├── FourierTransform.lean          # Bochner positivity (PROVED) + Weil criterion
│   └── WeilPositivity.lean            # Weil criterion equivalence
├── Adelic/
│   ├── ClassSpace.lean                # Adèle class space axioms, scaling flow
│   ├── SelbergUnfolding.lean          # Orbital decomposition
│   ├── TateLocalComputation.lean      # Tate's local computations
│   └── OrbitalIntegrals.lean          # Trace formula assembly
├── Spectral/
│   ├── UnboundedOperator.lean         # Unbounded ops + Stone's theorem (PROVED)
│   ├── SelfAdjointness.lean           # Spectral consequences
│   ├── SpectralPositivity.lean        # Trace positivity for autocorrelations
│   ├── CutoffHilbertSpace.lean        # L² cutoff, eigenbasis, convergence
│   ├── ResolventComputation.lean      # Resolvent → orbital integrals
│   └── TraceFormula.lean              # Assembly: spectral pairing → RH
├── Arithmetic/HodgeIndex.lean         # Arakelov geometry, Hodge index → RH
└── Strategy/DetailedBalance.lean      # Workpacket decomposition
```

## What To Work On

### Priority 1: Close the Hadamard scaffolding

The Hadamard factorization is *known mathematics* with a clear proof strategy already documented in the sorry'd theorems. This is pure Lean engineering, not research.

**Files**: `EntireFunction/Hadamard.lean`, `EntireFunction/Order.lean`, `ZetaProduct.lean`

**Specific targets**:
1. `hadamard_factorization` — Fill the 4-step proof using existing infrastructure (WeierstraßProduct convergence + entire_logarithm + Borel-Carathéodory)
2. `completedZeta_order` — Upper bound via Stirling, lower bound via zero density
3. `xi_hadamard_product` — Needs `completedRiemannZeta₀ 0 ≠ 0` (compute: ξ(0) = ζ(0)·Γ(0)·... needs careful analysis of the completed zeta at 0). Check Mathlib for `completedRiemannZeta₀_zero` or similar.

### Priority 2: Contour integration for the explicit formula

**File**: `ZetaProduct.lean` → `sum_over_zeros_eq_contour`

The proof sketch is clear: residue theorem on a rectangle, send horizontal contours to infinity using test function decay. Needs:
- Mathlib's `Complex.cauchyIntegral` / residue theorem
- `zeta_logDeriv_growth` for controlling horizontal integrals
- `zeta_zero_density` for justifying the residue sum

These are classical analytic number theory. The zero density estimate N(T) ~ (T/2π)log(T/2πe) follows from the argument principle applied to ξ on a rectangle. Stirling's approximation for Γ(s/2) gives the main term.

### Priority 3: The FEP formalization (NEW WORK)

This is where the novel contribution lives. Create a new file:

**`ArithmeticHodge/FEP/MarkovBlanket.lean`**

The thesis: the distributive law a(b+c) = ab + ac is a *formal Markov blanket* between additive and multiplicative structure. The conditional independence is precise:

```
-- Knowing only additive facts (successor, order) tells you nothing about
-- prime factorization without invoking distribution.
-- Knowing only multiplicative facts (divisibility) tells you nothing about
-- additive position without invoking distribution.
```

Formalize this as:

1. **Additive-multiplicative conditional independence**: Define what it means for two algebraic operations on a monoid to be "coupled only through distribution." Near-rings (where distribution holds on one side only) provide the counterexample: the coupling is asymmetric, and spectral theory degenerates.

2. **The free energy functional on test functions**: The Weil functional W(h) = polar + archimedean + prime_sum IS a free energy:
   - "Energy" = Σ_ρ h(γ_ρ) (spectral contribution)  
   - "Entropy" = prime sum (geometric contribution)
   - "Equilibrium" = W(h) = 0 for the optimal test function
   - "Weil positivity" for autocorrelations = "free energy doesn't decrease" = second law
   
   Make this formal by defining `freeEnergy (h : ℝ → ℝ) := weilFunctionalFull h (fourierCos h)` and showing that Weil positivity on autocorrelations IS the statement that free energy is minimized at the symmetric configuration.

3. **Detailed balance = functional equation**: The functional equation ξ(s) = ξ(1-s) IS the time-reversal symmetry. In FEP language, the transition kernel (from additive to multiplicative description, via the Euler product ↔ Dirichlet series duality) satisfies detailed balance when the functional equation holds. Formalize: `detailed_balance_of_functional_equation`.

4. **The positivity gap as an ergodicity question**: The remaining axiom `selberg_unfolding_bound` asks whether the scaling flow on 𝔸_ℚ/ℚ* is *mixing*. In FEP terms: does the system reach its free energy minimum? The PNT (ζ(1+it) ≠ 0) gives *ergodicity* (no invariant modes at the boundary). The gap is ergodicity → mixing. In dissipative systems, this follows from the existence of dissipation. The cutoff at Λ IS the dissipation — it breaks Hamiltonian symmetry and introduces energy loss at the boundary.

### Priority 4: Attack `selberg_unfolding_bound`

This is the axiom that currently carries all the mathematical weight. The FEP perspective suggests a specific attack:

The axiom states: for Λ > 1,
```
|spectralPairingOf X Λ h - weilFunctionalFull h (fourierCos h)| ≤ K·M/(c·Λ)
```

The existing decomposition into sub-lemmas 5a-5d is correct:
- 5a (boundary_volume_estimate): PROVED from AdeleClassSpaceData axioms
- 5b (bulk_volume_lower_bound): PROVED from AdeleClassSpaceData axioms  
- 5c (kernel_uniform_bound): PROVED
- 5d: The actual Selberg unfolding identity

The attack on 5d: The spectral pairing Σ fourierCos(h)(λᵢ)·|⟨Ω,eᵢ⟩|² differs from W(h) because the cutoff truncates the integral. The boundary contribution is:

∫_{boundary shell} K_h(x,x) dμ(x)

where K_h is the automorphic kernel. This is bounded by (sup of kernel) × (boundary volume). The sup of the kernel is bounded by K (sub-lemma 5c). The boundary volume is bounded by M (sub-lemma 5a). The bulk volume is at least c·Λ (sub-lemma 5b). So the relative error is K·M/(c·Λ).

The rigorous proof requires: the Selberg unfolding identity for GL(1)/ℚ, which follows from Poisson summation (already proved!) applied to the automorphic kernel on the adèle class space.

**Strategy**: Replace the axiom with a theorem that uses `poisson_summation` (Mathlib) on the adèle class space. The key insight: for GL(1) (abelian!), the Selberg unfolding is just Poisson summation on ℚ\𝔸_ℚ. No cuspidal spectral theory needed. This is Tate's thesis.

### Priority 5: Eliminate `boundary_eigenvalue_implies_zeta_zero`

This axiom says: if a nonzero eigenvalue of D_Λ sits at the boundary |λ|=Λ, then ζ has a zero with Re(s)≥1.

The current implementation has cutoffKoopmanOp as the identity (placeholder), making the generator zero and all eigenvalues zero. To make this axiom a theorem, you need to:

1. Implement the actual projected Koopman operator P_Λ U_t P_Λ on L²(μ_Λ)
2. Show its eigenvalues correspond to characters |·|^{it} restricted to the cutoff
3. Connect boundary eigenvalues to zeta values via the Mellin transform

This is substantial but follows from Tate's thesis infrastructure.

## Build & Test

```bash
cd /home/claude/rh-project
# Get Mathlib cache first (saves hours)
lake exe cache get
# Build
lake build
```

The build will fail on the current codebase because Mathlib API may have changed (the project pins `master` which moves). If build fails:
1. Check `lean-toolchain` matches available Lean version
2. Run `lake update` to refresh dependencies  
3. Fix any API breakage (Mathlib renames happen frequently)

## Principles

1. **Every sorry must have a documented proof strategy**. No sorry without a comment explaining what mathematics fills it and why it's known to be true.

2. **Axioms are for genuinely open problems**. Known mathematics should be sorry'd, not axiomatized. The only legitimate axiom is one equivalent to RH itself.

3. **The FEP framing is not metaphorical**. When we say "detailed balance" we mean the literal mathematical condition π(i)T(i→j) = π(j)T(j→i). When we say "Markov blanket" we mean conditional independence in the formal probabilistic sense. When we say "free energy" we mean F = E - TS with specific mathematical objects playing each role.

4. **Failures are data, not evidence of impossibility**. If a Lean proof attempt fails, record WHY it failed with surgical precision. Which sub-goal couldn't be closed? What Mathlib lemma was missing? What type didn't unify? The failure mode IS the research.

5. **Don't paint the frame. Fill the hole.** The project has enough framing. What it needs is: closed sorries, eliminated axioms, and new mathematical content connecting the FEP perspective to the actual proof obligations.
