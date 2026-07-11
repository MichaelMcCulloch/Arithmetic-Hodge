# Bombieri Local Critical Hermitian Form Implementation Plan

> **For agentic workers:** Use `superpowers:subagent-driven-development` for
> this task and obtain a fresh independent review after the production commit.

**Goal:** Polarize the ratio-two Bombieri diagonal formula into a genuine
conjugate-linear/linear Hermitian form on smooth `BombieriTest`, prove all
cross integrals converge, and identify its diagonal with the existing
prime-free quadratic functional.

**Architecture:** Reuse the existing `mellinLinearMap`. Define the real
critical kernel and cross integrand, prove cross-integrability by multiplying
the existing integrable `K(v) M_g(v)` by the uniformly bounded `conj M_f(v)`,
bundle the pairing as a sesquilinear map, prove Hermitian symmetry by conjugating
the integral, then recover the existing endpoint diagonal exactly.

**Verified discovery artifact:** The production-shaped strict probe
`/tmp/BombieriLocalHermitianFormProbe.lean`, SHA-256
`949fccc81dc8f34e073bdab6a05f07a9a2150a0bcbb8c4409f92ed1f936aae1d`,
is described in
`docs/research/bombieri-local-critical-hermitian-form-2026-07-11.md`.

## Global constraints

- No `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, or
  RH/positivity assumption.
- Preserve all 159 inventoried legacy root Lean files byte-for-byte.
- Work directly on `main` as authorized; stage only the assigned production
  module and umbrella import.
- Record a strict missing-module RED before implementation.
- Strict-compile the module and API scratch, run a targeted build and
  `lake build ArithmeticHodge`, forbidden-proof/naming/dependency scans,
  exhaustive theorem axiom audit, and exact inventory comparison.
- Every theorem must depend only on `propext`, `Classical.choice`, and
  `Quot.sound`, or a subset.
- Reuse `MultiplicativeWeil.mellinLinearMap`; do not land the probe's earlier
  duplicate Mellin-linear definition or redundant add/smul lemmas.
- Do not construct `PositiveHermitianForm` here. Global or tail positivity has
  not been proved.
- Do not claim this form already contains clipped Yoshida sine/cosine `L²`
  modes. Its domain is smooth `BombieriTest` only.

---

### Task 1: Cross-integrable smooth Bombieri Hermitian form

**Files:**

- Create:
  `ArithmeticHodge/Analysis/MultiplicativeWeilLocalCriticalForm.lean`
- Modify: `ArithmeticHodge.lean`
- Temporary test: `MultiplicativeWeilLocalCriticalFormScratch.lean`

**Import:**

```lean
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticEndpoint
```

**Required public definitions in
`ArithmeticHodge.Analysis.MultiplicativeWeil`:**

```lean
def bombieriLocalCriticalKernel (v : ℝ) : ℂ

def bombieriLocalCriticalCrossIntegrand
    (f g : BombieriTest) (v : ℝ) : ℂ

def bombieriLocalCriticalPairing (f g : BombieriTest) : ℂ

def bombieriLocalCriticalForm :
    BombieriTest →ₗ⋆[ℂ] BombieriTest →ₗ[ℂ] ℂ

def bombieriLocalCriticalQuadraticIntegrand
    (f : BombieriTest) (v : ℝ) : ℂ

def bombieriLocalCriticalQuadratic (f : BombieriTest) : ℂ
```

The pairing must be exactly

```text
conj(Mf(1)) Mg(0) + conj(Mf(0)) Mg(1)
  + (1/(2*pi)) integral K(v) conj(Mf(1/2+iv)) Mg(1/2+iv) dv.
```

**Required public theorems:**

```lean
theorem bombieriLocalCriticalCrossIntegrand_integrable
    (f g : BombieriTest) :
    Integrable (bombieriLocalCriticalCrossIntegrand f g)

@[simp] theorem bombieriLocalCriticalForm_apply
    (f g : BombieriTest) :
    bombieriLocalCriticalForm f g =
      bombieriLocalCriticalPairing f g

theorem bombieriLocalCriticalPairing_conj (f g : BombieriTest) :
    star (bombieriLocalCriticalPairing g f) =
      bombieriLocalCriticalPairing f g

theorem bombieriLocalCriticalForm_conj_apply (f g : BombieriTest) :
    star (bombieriLocalCriticalForm g f) =
      bombieriLocalCriticalForm f g

theorem bombieriLocalCriticalPairing_self (f : BombieriTest) :
    bombieriLocalCriticalPairing f f =
      bombieriLocalCriticalQuadratic f

theorem bombieriLocalCriticalForm_self (f : BombieriTest) :
    bombieriLocalCriticalForm f f =
      bombieriLocalCriticalQuadratic f

theorem bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    bombieriFunctional (bombieriQuadraticTest g) =
      bombieriLocalCriticalForm g g
```

- [ ] Create a strict scratch importing the absent module and checking every
  public definition/theorem plus explicit right-linear and left-conjugate-
  linear scalar examples. Record the missing-module RED.
- [ ] Port the current production-shaped probe. The bound on the first Mellin
  factor must come from the bounded continuous Fourier transform of the
  critical logarithmic Schwartz pullback; use
  `bombieriCriticalArchKernel_integrable` for the second factor.
- [ ] Keep the four integral slot-algebra lemmas, the conjugated-integral
  helper, the Mellin sup bound, kernel-star helper, and generic two-real-part
  algebra theorem private.
- [ ] Prove the form fields from the separately verified integral add/smul
  identities. Respect Mathlib's conjugate-linear-first convention.
- [ ] Prove Hermitian symmetry with `integral_conj` and the real kernel.
- [ ] Prove the diagonal identities and compose exactly with
  `bombieriFunctional_quadratic_eq_local_critical_form_le_two`.
- [ ] Add one umbrella import immediately after
  `MultiplicativeWeilQuadraticEndpoint`, run all gates, delete scratch/audit,
  and commit `polarize the Bombieri local critical form`.

## Terminal boundary after this plan

This task closes polarization on smooth tests only. The next Yoshida-domain
task must extend/evaluate the pairing on clipped interval Fourier modes or
define equivalent external low-tail functionals. It may not infer such an
extension from ordinary `L²` boundedness, because the local critical form is
unbounded on all circle `L²`.
