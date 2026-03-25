# ArithmeticHodge: Sorry Roadmap

The project compiles cleanly (`lake build` succeeds with only sorry warnings).
Every `sorry` traces to one of the distinct mathematical gaps below.

## Status Summary

| Metric | Count |
|--------|-------|
| Total .lean files | 13 |
| Total lines | ~1,700 |
| `True := by trivial` placeholders | **0** (was 10) |
| sorry declarations | 10 |
| Distinct mathematical gaps | 8 |
| Fully proved theorems | 30+ |
| New infrastructure | UnboundedOperator API (170 lines) |

## Proved Theorems (highlights)

| Theorem | File | Method |
|---------|------|--------|
| `product_formula_rat` | ClassSpace.lean | `Nat.prod_factorization_pow_eq_self` |
| `haar_invariant_of_trivial_haarChar` | ClassSpace.lean | `mulEquivHaarChar_smul_map` from Mathlib |
| `scaling_flow_unitary_from_invariance` | SelfAdjointness.lean | `MeasurePreserving.integral_comp'` |
| `symmetric_eigenvalue_real` | UnboundedOperator.lean | Inner product manipulation |
| `symmetric_eigenvectors_orthogonal` | UnboundedOperator.lean | Symmetry + eigenvalue reality |
| `approximate_detailed_balance` | DetailedBalance.lean | Archimedean property of ℝ |
| `approximate_positivity_on_autocorrelations` | DetailedBalance.lean | Direct construction |
| `workpacket_2` (Haar from unimodularity) | DetailedBalance.lean | `MeasurePreserving` constructor |
| Delegations: WP4→stones, WP5→trace_limit, WP6→weil_criterion, chain→WP6 | | |

## Sorry Classification

### [INFRASTRUCTURE] — Known mathematics, needs Lean formalization

#### 1. `stones_theorem` (SelfAdjointness.lean:64)
**Statement:** Strongly continuous unitary group has self-adjoint generator.
**Infrastructure built:**
- ✓ `UnboundedOperator` structure with dense domain (UnboundedOperator.lean)
- ✓ `IsSymmetric`, `IsSelfAdjoint` predicates
- ✓ `symmetric_eigenvalue_real` — PROVED
- ✓ `symmetric_eigenvectors_orthogonal` — PROVED
- ✓ `generatorDomain` submodule (zero_mem proved)
- ✓ `stones_theorem_full` stated with proper unbounded types

**Proved:**
- ✓ `generatorDomain` submodule closure (add_mem, smul_mem) — PROVED
- ✓ `unitary_adjoint_eq` — U(-t) is adjoint of U(t) — PROVED
- ✓ `raw_generator_skew_symmetric` — limit substitution t↦-t — PROVED
- ✓ `generator_is_symmetric` — via -i factor + skew-symmetry — PROVED
**Remaining sorry's within the infrastructure:**
- `generator_domain_dense` — Bochner interval integral + FTC mollification
- Deficiency indices Dom(A*) ⊆ Dom(A) — Cayley transform
**Delegated to by:** `workpacket_4`, `scaling_generator_self_adjoint`, `stones_theorem_unbounded`

#### 2. `haar_invariant_under_scaling` (ClassSpace.lean:151)
**Statement:** Scaling flow preserves Haar measure on the adèle class space.
**Proved:** `haar_invariant_of_trivial_haarChar` — if `mulEquivHaarChar φ = 1` then `map φ μ = μ`
**Remaining sorry:** Connecting the ScalingFlowData to ContinuousMulEquiv with trivial Haar character.
**What eliminates it:** Construction of 𝔸_ℚ/ℚ* as a locally compact group.

#### 3. `workpacket_1` (DetailedBalance.lean:43)
**Statement:** Product formula ∏|x|_v = 1 implies trivial modular function.
**What eliminates it:** Adelic norm API + connection to mulEquivHaarChar.

### [DEEP] — Known mathematics, substantial effort

#### 4. `weil_explicit_formula` (WeilExplicit.lean:135)
**Statement:** Sum over zeta zeros = Weil functional (with proper NontrivialZetaZero types).
**What eliminates it:** Hadamard factorization, contour integration, ζ'/ζ estimates.

#### 5. `weil_criterion` (WeilPositivity.lean:151)
**Statement:** RH ⟺ Weil functional ≥ 0 on autocorrelations.
**Delegated to by:** `workpacket_6`, `chain_strategy_C`

#### 6. `hodge_index_implies_RH` (HodgeIndex.lean:180)
**Statement:** Arithmetic Hodge Index implies Riemann Hypothesis.
**What eliminates it:** Arakelov-to-Weil dictionary formalization.

### [RESEARCH] — New mathematics or Millennium Prize

#### 7. `regularized_trace_limit` (DetailedBalance.lean:202) — **THE ATOMIC GAP**
**Statement:** Regularized trace converges to Weil functional; limit ≥ 0 on autocorrelations.
**Proved surrounding steps:**
- ✓ `approximate_detailed_balance` — O(1/Λ) vanishing (PROVED)
- ✓ `approximate_positivity_on_autocorrelations` — non-negativity exists (PROVED)
**Delegated to by:** `workpacket_5`

#### 8. `arithmetic_hodge_index` (HodgeIndex.lean:168) — **THE SUMMIT**
**Statement:** ⟨α, α⟩ ≤ 0 for all α ∈ ĈH¹₀(Spec(ℤ̄)). **Equivalent to RH.**

## Dependency Graph

```
product_formula_rat ✓ PROVED
    │
    ▼
workpacket_1 [#3] ───► haar_invariant [#2] ◄── haar_invariant_of_trivial_haarChar ✓ PROVED
    │                         │
    ▼                         ▼
WP2 ✓ PROVED ──► WP3 ✓ ──► stones_theorem [#1]
                                   │
                            ┌──────┴──────┐
                            │ Infrastructure│
                            │   ✓ UnboundedOperator
                            │   ✓ eigenvalue_real
                            │   ✓ eigenvectors_orthogonal
                            └──────┬──────┘
                                   ▼
                   approximate_detailed_balance ✓ PROVED
                                   │
                                   ▼
                   regularized_trace_limit [#7] ◄── THE ATOMIC GAP
                                   │
                                   ▼
                   WP5 ✓ DELEGATES ──► weil_criterion [#5]
                                             │
                                             ▼
                   WP6 ✓ DELEGATES ──► chain ✓ DELEGATES
                                             │
                                             ▼
                                     RiemannHypothesis
                                             ▲
                                             │
                   arithmetic_hodge_index [#8] ◄── THE SUMMIT
                                             │
                   hodge_index_implies_RH [#6]
```
