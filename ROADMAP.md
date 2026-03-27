# Roadmap: Proving the Riemann Hypothesis

## The DAG

Every node is a GitLab issue. Arrows are dependencies (→ means "requires").

```
                        ┌─────────────────────────────────┐
                        │  riemann_hypothesis_from_trace   │
                        │        (PROVED)                  │
                        └──────────────┬──────────────────┘
                                       │
                        ┌──────────────┴──────────────────┐
                        │    AdeleClassSpaceData instance   │
                        │           #31 (META)             │
                        └──────────────┬──────────────────┘
                                       │
              ┌────────────────────────┼────────────────────────┐
              │                        │                        │
   ┌──────────┴────────┐  ┌───────────┴──────────┐  ┌─────────┴──────────┐
   │ selberg_unfolding  │  │ boundary_eigenvalue   │  │  Geometry axioms   │
   │   _bound #41      │  │ _implies_zeta_zero #40│  │  #36,#37,#39       │
   └────────┬──────────┘  └───────────┬──────────┘  └─────────┬──────────┘
            │                         │                        │
            │              ┌──────────┴──────────┐             │
            │              │  Spectral-zeta      │             │
            │              │  correspondence     │             │
            │              │  Phase 3            │             │
            │              └──────────┬──────────┘             │
            │                         │                        │
   ┌────────┴─────────────────────────┴────────────────────────┘
   │
   │         TATE'S THESIS (Phase 2)
   │
   ├── Explicit formula (#12, 2.7)
   │     └── Contour integration of ζ'/ζ
   │           └── Hadamard product (existing, partially proved)
   │
   ├── Functional equation (2.6)
   │     └── Zeta integrals (2.5)
   │           └── Poisson summation on 𝔸_ℚ/ℚ (2.4) ← THE DOMINO
   │                 ├── Fourier transform on 𝔸_ℚ (2.3)
   │                 │     ├── Fourier on ℝ (Mathlib ✓)
   │                 │     ├── Fourier on ℚ_p (2.3.2)
   │                 │     └── Product Fourier (2.3.3)
   │                 ├── ℚ ⊂ 𝔸_ℚ cocompact discrete (2.4.1)
   │                 │     └── Product formula (1.5.2)
   │                 └── Additive characters (2.1)
   │
   └── Regularization (2.8)
         └── Cutoff zeta integrals
               └── Adèle construction (Phase 1)
                     ├── 𝔸_ℚ as topological ring (1.3)
                     │     ├── Restricted product ∏'_p ℚ_p (1.2)
                     │     │     ├── ℚ_p (Mathlib ✓)
                     │     │     └── ℤ_p (Mathlib ✓)
                     │     └── ℝ (Mathlib ✓)
                     ├── 𝔸_ℚ* idèle group (1.4)
                     │     └── Idèle norm (1.4.2)
                     ├── ℚ* discrete in 𝔸_ℚ* (1.5)
                     │     └── Product formula (1.5.2)
                     ├── C_ℚ = 𝔸_ℚ*/ℚ* (1.6)
                     ├── Height function (1.7)
                     │     └── Compactness of C_ℚ¹ (1.8.1)
                     └── Scaling flow (1.7.3)
```

## Issue Index

### Phase 1: Adèle Construction
| Issue | Title | Depends on | Independent? |
|-------|-------|------------|--------------|
| #46 | Restricted product ∏'_p ℚ_p | — | ✓ YES |
| #47 | 𝔸_ℚ as locally compact topological ring | #46 | |
| #48 | Haar measure on ℚ_p and ℚ_p* | — | ✓ YES |
| #49 | Idèle group 𝔸_ℚ* and idèle norm | #47 | |
| #50 | Product formula ∏_v |α|_v = 1 | #49 | |
| #51 | ℚ* discrete in 𝔸_ℚ* | #49, #50 | |
| #52 | Idèle class group C_ℚ = 𝔸_ℚ*/ℚ* | #51 | |
| #53 | Haar measure on C_ℚ | #52 | |
| #54 | Height function and scaling flow on C_ℚ | #52 | |
| #55 | Compactness of sublevel sets (C_ℚ¹ compact) | #52, #54 | |
| #56 | Geometry: shell bound + volume growth + nondiscrete | #53, #55 | |
| #57 | Instantiate AdeleClassSpaceData | #53-#56 | |

### Phase 2: Tate's Thesis
| Issue | Title | Depends on | Independent? |
|-------|-------|------------|--------------|
| #58 | Additive characters ψ_p on ℚ_p | #48 | |
| #59 | Global additive character ψ on 𝔸_ℚ | #47, #58 | |
| #60 | Schwartz-Bruhat functions on ℚ_p | — | ✓ YES |
| #61 | Schwartz-Bruhat functions on 𝔸_ℚ | #47, #60 | |
| #62 | Fourier transform on ℚ_p | #48, #58, #60 | |
| #63 | Fourier transform on 𝔸_ℚ + inversion | #59, #61, #62 | |
| #64 | ℚ cocompact discrete in 𝔸_ℚ | #47, #51 | |
| #65 | **Poisson summation on 𝔸_ℚ/ℚ** | #63, #64 | |
| #66 | Zeta integrals Z(Φ, s) | #49, #61 | |
| #67 | Meromorphic continuation of Z | #65, #66 | |
| #68 | Functional equation Z(Φ,s) = Z(Φ̂,1-s) | #65, #66 | |
| #69 | Z(Φ₀, s) = completedRiemannZeta₀(s) | #61, #66 | |
| #70 | Explicit formula via contour integration | #67, #68, existing Hadamard | |
| #71 | Cutoff zeta integrals Z_Λ | #54, #66 | |
| #72 | **Z_Λ → Z convergence (O(1/Λ))** | #56, #71 | |
| #73 | **Prove selberg_unfolding_bound** | #70, #72 | |

### Phase 3: Spectral Realization
| Issue | Title | Depends on | Independent? |
|-------|-------|------------|--------------|
| #74 | Characters χ_s as Koopman eigenvectors | #54, existing Koopman | |
| #75 | Eigenvalue-character correspondence on cutoff | #74, #71 | |
| #76 | **Prove boundary_eigenvalue_implies_zeta_zero** | #69, #75 | |

### Phase 4: Technicalities
| Issue | Title | Depends on | Independent? |
|-------|-------|------------|--------------|
| #42 | Sierpinski splitting | — | ✓ YES |
| #43 | Λ ≤ 0 edge case | — | ✓ YES |
| #44 | Vacuum normalization | #53 | |
| #45 | Fourier integrability | — | ✓ YES |

## Independent starting points (can begin NOW, in parallel)
1. **#46** Restricted product topology
2. **#48** Haar measure on ℚ_p
3. **#60** Schwartz-Bruhat functions on ℚ_p
4. **#42** Sierpinski splitting lemma
5. **#43** Λ ≤ 0 edge case
6. **#45** Fourier integrability edge case
