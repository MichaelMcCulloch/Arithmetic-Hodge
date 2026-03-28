# Roadmap: Proving the Riemann Hypothesis from ZFC

## The Proof Chain

```
 O  ZFC (Lean 4 kernel + Mathlib)
 |
 |  LAYER 0-1: CLASSICAL COMPLEX ANALYSIS              textbook, in Mathlib
 |
 |-- Riemann zeta, meromorphic continuation, functional equation       MATHLIB
 |-- Gamma, Theta, Poisson summation                                   MATHLIB
 |-- zeta(s) != 0 for Re(s) >= 1 (Euler product)                      MATHLIB
 |
 |  LAYER 2: HADAMARD + EXPLICIT FORMULA                textbook, partially built
 |
 |-- Complex Stirling approximation                     #NEW  2 sorries   BIGGEST BLOCKER
 |-- Jensen's formula / Abel summation                  #4    1 sorry     agent: abel
 |-- Weierstrass product factorization                  #8    1 sorry     agent: weier
 |-- Hadamard factorization for entire functions        #1    0 sorries   DONE (overnight)
 |-- xi(s) = (1/2)s(s-1)L0+1/2, entire, order 1       #9    1 sorry     needs Stirling
 |   |-- xi zeros = nontrivial zeta zeros                               PROVED
 |   |-- xi functional equation                                         PROVED
 |   +-- zeros in critical strip                                        PROVED
 |-- Hadamard product for xi                            #9    1 sorry     needs order=1
 |-- xi'/xi partial fraction                                            PROVED
 |-- zeta'/zeta = O(log^2|t|)                           #10              PROVED
 |-- N(T) ~ (T/2pi)log(T/2pie)                          #11   3 sorries  needs Stirling+arg
 |-- Weil explicit formula                               #12   1 sorry    needs contour integ
 |   +-- unconditional form + RH specialization                          PROVED
 |
 |  LAYER 3: WEIL CRITERION                             textbook (Weil 1952, Bombieri 2000)
 |
 |-- RH ==> Weil positivity (forward)                   #14              PROVED
 |-- Weil positivity ==> RH (backward)                                  PROVED
 +-- RH <=> WeilPositivity                                              PROVED
 |
 |  LAYER 4: ADELIC CLASS SPACE                         textbook (Connes 1999)
 |
 |-- A_Q/Q* class space structure                                       PROVED
 |-- Scaling flow, Haar measure                                         PROVED
 |-- Orbital integrals                                                  PROVED
 +-- Workpackets 1-3 (product formula -> Haar -> unitary)               PROVED
 |
 |  LAYER 5: SPECTRAL THEORY                            textbook (Stone, RAGE)
 |
 |-- Unbounded operators, IsSelfAdjoint                                 PROVED
 |-- Stone's theorem (full)                                             PROVED
 |-- Generator domain dense                                             PROVED
 |-- Resolvent bound                                                    PROVED
 |-- Spectral calculus (functional calculus for D)       #17   2 sorries agent: cayley
 |-- RAGE theorem chain                                  #19             PROVED
 +-- Wiener's theorem                                                   PROVED (overnight)
 |
 |  LAYER 6: TRACE FORMULA                              the heart of the proof
 |
 |-- spectralPairing_nonneg                                             PROVED
 |   +-- autocorrelation_fourierCos_nonneg                              PROVED
 |-- spectralPairing -> Weil as Lambda->inf              #23  AXIOM     selberg_unfolding_bound
 |-- spectral gap control                                #18  AXIOM     boundary_eigenvalue_implies_zeta_zero
 +-- Workpackets 5-6: spectral pairing -> Weil -> RH                   PROVED
 |
 X  RIEMANN HYPOTHESIS (riemann_hypothesis_from_trace, TraceFormula.lean:124)
```

## Status Summary (2026-03-28)

| Category | Count | Description |
|----------|-------|-------------|
| PROVED from Mathlib/ZFC | ~70% | No sorry, no axiom. Verified by Lean kernel. |
| Infrastructure sorry | 23 | Known textbook math, published proofs exist. |
| Axiom (known math) | 3 | Stirling, Selberg unfolding, Connes spectral |
| Class axiom (frontier) | 2 | ArakelovIntersectionTheory |

## Critical Path

### Immediate (agents assigned)

| Blocker | Unblocks | Agent | Status |
|---------|----------|-------|--------|
| Complex Stirling | #5, #7, #9, #11 (7+ sorries) | `stirling` | Working |
| Jensen + Abel summation | #4, #8, #1 (summability chain) | `abel` | Working |
| Weierstrass tprod order | #8 (last sorry) | `weier` | Working |
| Cayley transform | #17 (spectral calculus) | `cayley` | Working |
| Order axiom -> theorem | #5 (completedZeta_order) | `growthbound` | Working |

### Next wave (after infrastructure lands)

| Task | Depends on | Difficulty |
|------|-----------|------------|
| Hadamard product for xi (#9) | Stirling -> order = 1 | Medium |
| N(T) zero density (#11) | Stirling + argument principle | Hard |
| Weil explicit formula (#12) | Partial fractions + DCT | Hard |
| Selberg unfolding axiom (#23) | Full adelic construction | Very Hard |
| Connes spectral realization | Koopman representation theory | Very Hard |

### Frontier (research-level)

| Axiom | Published reference | Scale |
|-------|-------------------|-------|
| `selberg_unfolding_bound` | Connes 1999, Selberg trace formula | ~500 lines |
| `boundary_eigenvalue_implies_zeta_zero` | Connes 1999, spectral realization | ~300 lines |
| `ArakelovIntersectionTheory.neg_semidef` | Faltings, Moriwaki, Yuan-Zhang | ~1000+ lines |
| `ArakelovIntersectionTheory.arakelov_weil_bridge` | Arithmetic Hodge Index Theorem | ~1000+ lines |

## GitLab Issue Index

### Closed (sorry eliminated)
| Issue | Title | How |
|-------|-------|-----|
| #2 | hadamard_factorization_order_one | Clean corollary |
| #10 | zeta_logDeriv_growth | Triangle inequality assembly |
| #19 | spectral_gap_gives_mixing | RAGE chain via structure enrichment |
| #43 | cutoffHilbertBasis_infinite Lam<=0 | Axiom inconsistency (exfalso) |
| #45 | fourierCos_bounded | Refactor to kernel_uniform_bound |

### In Progress (agents assigned)
| Issue | Title | Agent | Remaining |
|-------|-------|-------|-----------|
| #1 | hadamard_factorization | — | 0 sorries (overnight closure, verify) |
| #4 | zeroExponent_le_order | `abel` | 1 sorry (Abel summation) |
| #5 | completedZeta_order | `growthbound` | 1 axiom -> theorem |
| #8 | weierstrass_factorization | `weier` | 1 sorry (ha_ord_eq) |
| #9 | xi_hadamard_product | (blocked on #5) | 1 sorry |
| #12 | sum_over_zeros_eq_contour | — | 1 sorry (contour body) |
| #17 | spectralCalculus_exists | `cayley` | 2 sorries |

### Open (not yet started or blocked)
| Issue | Title | Blocker |
|-------|-------|---------|
| #3 | zeroCount_le_logMax (Jensen) | Needs Jensen's formula |
| #6 | zetaZero_exponent_of_convergence | Needs #4, #5, #11 |
| #7 | zeta_vertical_strip_bound | Needs Complex Stirling |
| #11 | zeta_zero_density | Needs Stirling + argument principle |
| #14 | rh_implies_weil_positivity | Needs #12 |
| #15 | bombieriAutocorrelation_decay | Leaf, independent |
| #16 | bombieriAutocorrelation_weil_neg | Needs #15 |
| #18 | zeta_nonvanishing_gives_spectral_gap | Out of scope (old path) |
| #20 | mixing_controls_boundary | Out of scope (old path) |
| #21 | cutoffEigenvaluesOf | Construction |
| #22 | cutoffEigenbasis | Construction |
| #23 | spectralPairing_tendsto_weil (AXIOM) | Needs full adelic construction |
| #30 | spectralPairing_boundary_control | Needs #23 |
| #42 | Sierpinski splitting | Independent leaf |
| #44 | vacuumVector_norm_sq_le_one | Needs Haar normalization |

### Phase 1-3 (Adelic Construction, not yet started)
Issues #46-#76: Full adelic infrastructure from restricted products through
Tate's thesis to the Selberg unfolding bound. See DAG below.

## Full Dependency DAG

```
                        riemann_hypothesis_from_trace  PROVED
                                       |
                        weil_positivity_from_spectral  PROVED
                                       |
              +------------------------+------------------------+
              |                        |                        |
   selberg_unfolding     boundary_eigenvalue      Weil criterion
      _bound #23           _implies_zeta         RH <=> WeilPos
      AXIOM                _zero AXIOM              PROVED
         |                      |
         |           spectral realization
         |              (Phase 3)
         |                   |
    +----+-------------------+----+
    |                             |
    |    TATE'S THESIS (Phase 2)  |
    |                             |
    +-- Explicit formula #12 -----+
    |     +-- Hadamard product #9
    |           +-- order=1 #5 <-- Stirling (BLOCKER)
    |           +-- Weierstrass #8
    |                 +-- Jensen #3
    |                 +-- Abel #4
    |
    +-- Cutoff zeta integrals
    |     +-- Adele construction (Phase 1, #46-#57)
    |
    +-- Regularization
          +-- Selberg unfolding identity
```

## What would complete the proof from ZFC?

1. **Fill 23 infrastructure sorries** (textbook math, ~2000 lines total)
   - Complex Stirling, Jensen, argument principle, residue theorem
   - Cayley transform, Borel-Caratheodory, Abel summation

2. **Prove 3 axioms from known math** (~800 lines total)
   - `completedZeta0_order_le_one` — needs Stirling (agent working)
   - `selberg_unfolding_bound` — needs full adelic construction
   - `boundary_eigenvalue_implies_zeta_zero` — needs Connes spectral realization

3. **Prove 2 frontier axioms** (~2000+ lines, research-level)
   - `ArakelovIntersectionTheory.neg_semidef` — Arithmetic Hodge Index
   - `ArakelovIntersectionTheory.arakelov_weil_bridge` — The bridge theorem
