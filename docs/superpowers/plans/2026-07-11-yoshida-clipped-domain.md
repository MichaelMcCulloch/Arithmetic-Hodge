# Yoshida Clipped Domain Implementation Plan

> **For agentic workers:** Use `superpowers:subagent-driven-development` and
> obtain a fresh independent review after each production commit.

**Goal:** Add the direct log-interval ambient domain that contains Yoshida's
endpoint-jumping clipped Fourier modes, together with exact centered Laplace
evaluation and a total removable-value transform formula.

**Architecture:** Functions are `C∞` only on `Icc (-a) a` and zero outside.
This is an algebraic ambient domain, not a form on all circle `L²`. Bundle
centered bilateral Laplace evaluation as a complex linear map, define the
clipped exponentials with Yoshida's Lebesgue normalization, totalize the
single removable quotient before simplifying it, and add a linear crop of
smooth Bombieri critical pullbacks with an explicit support predicate.

**Verified discovery artifact:**
`/tmp/ClippedModeDomainProbe.lean`, SHA-256
`8034818815d07ec3769ca510e9e9a23df58206f2f41a122a9096ae475f299feb`,
strict-compiles and is documented in
`docs/research/yoshida-clipped-domain-2026-07-11.md`.

## Global constraints

- No `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, positivity
  assumption, or RH-equivalent dependency.
- Preserve all 159 inventoried legacy root Lean files byte-for-byte.
- Work directly on `main` as authorized; stage only task-owned paths.
- Record a strict missing-module RED, then strict source/facade/API GREEN.
- Run a targeted build, `lake build ArithmeticHodge`, forbidden-proof and
  naming scans, dependency scan, exhaustive public axiom audit, exact archive
  comparison, and independent review.
- Every exported theorem must use only `propext`, `Classical.choice`, and
  `Quot.sound`, or a subset.
- Do not define the local critical form, assume cross-integrability, add a
  `PositiveHermitianForm`, or claim (5.16-Q) in this task.
- Do not claim the critical form is bounded on ordinary circle `L²`.
- Endpoint jumps are intentional; use `ContDiffOn`/`derivWithin`, never global
  differentiability of a clipped function.
- Every apparent mode-transform pole must be handled by a removable-value
  definition before algebraic splitting.

---

### Task 1: Direct carrier, clipped modes, and total transform

**Files:**

- Create: `ArithmeticHodge/Analysis/YoshidaClippedDomain.lean`
- Modify: `ArithmeticHodge.lean`
- Temporary test: `YoshidaClippedDomainScratch.lean`

**Imports:**

```lean
import ArithmeticHodge.Analysis.MultiplicativeWeilLocalCriticalForm
import ArithmeticHodge.Analysis.YoshidaFourierModes
```

Add only the interval-integral dependency actually required for the exact
exponential integral.

**Carrier:**

```lean
def yoshidaClippedSmoothSubmodule (a : ℝ) : Submodule ℂ (ℝ → ℂ)

abbrev YoshidaClippedSmooth (a : ℝ) :=
  yoshidaClippedSmoothSubmodule a

instance : CoeFun (YoshidaClippedSmooth a) (fun _ => ℝ → ℂ)
```

The carrier predicate must be exactly

```text
ContDiffOn R infinity f (Icc (-a) a)
and f(x)=0 outside Icc (-a) a.
```

Export the outside-zero theorem and keep the submodule operations
definitionally/algebraically transparent.

**Lebesgue-normalized modes:**

```lean
def yoshidaClippedExponential
    (a : ℝ) (n : ℤ) : YoshidaClippedSmooth a
```

On the interval it is exactly

```text
(sqrt(2*a))^-1 * exp(pi*i*n*x/a).
```

Export pointwise `of_mem` and `of_not_mem` theorems. Do not yet map it into
circle `L²`; injectivity and the exact Haar/Lebesgue norm theorem belong to
the later tail-coordinate module.

**Centered Laplace maps:**

```lean
def yoshidaCenteredLaplaceLinear
    (a : ℝ) (ha : 0 < a) (z : ℂ) :
    YoshidaClippedSmooth a →ₗ[ℂ] ℂ

def yoshidaCriticalSampleLinear
    (a : ℝ) (ha : 0 < a) (v : ℝ) :
    YoshidaClippedSmooth a →ₗ[ℂ] ℂ

def yoshidaPositivePolarLinear ...
def yoshidaNegativePolarLinear ...
```

Prove the application theorem and explicit add/scalar orientation examples.

**Mode exponent and removable quotient:**

```lean
def yoshidaModeLaplaceExponent
    (a : ℝ) (n : ℤ) (z : ℂ) : ℂ :=
  -z + ((Real.pi * n / a : ℝ) : ℂ) * Complex.I

def yoshidaIntervalExpQuotient (a : ℝ) (c : ℂ) : ℂ :=
  if c = 0 then (2 * a : ℝ)
  else (Complex.exp (c * a) - Complex.exp (c * (-a))) / c
```

Required theorems:

```lean
@[simp] theorem yoshidaIntervalExpQuotient_zero :
  yoshidaIntervalExpQuotient a 0 = (2*a : ℝ)

theorem yoshidaIntervalExpQuotient_of_ne
    (hc : c ≠ 0) : ...

theorem yoshidaCenteredLaplace_clippedExponential
    (ha : 0 < a) (z : ℂ) (n : ℤ) :
  yoshidaCenteredLaplaceLinear a ha z
      (yoshidaClippedExponential a n) =
    ((Real.sqrt (2*a))⁻¹ : ℂ) *
      yoshidaIntervalExpQuotient a
        (yoshidaModeLaplaceExponent a n z)
```

Prove the zero branch by reducing the interval integrand to a constant and
integrating the interval length. Prove the nonzero branch with the existing
`integral_exp_mul_complex`. Also export the simpler nonzero-denominator
corollary matching the discovery probe.

At `z = 1/2` and `z = -1/2`, prove the exponent is nonzero and export the two
polar-value corollaries if their forms are stable and useful downstream.

**Smooth critical-pullback crop:**

```lean
def yoshidaCriticalPullbackCropLinear (a : ℝ) :
  MultiplicativeWeil.BombieriTest →ₗ[ℂ]
    YoshidaClippedSmooth a

def YoshidaCriticalPullbackSupported
    (a : ℝ) (f : MultiplicativeWeil.BombieriTest) : Prop :=
  ∀ x ∉ Icc (-a) a,
    f.logarithmicPullbackSchwartz (1/2) x = 0
```

Export:

- crop value on the interval;
- crop value outside the interval;
- equality of the crop with the full critical pullback under the support
  predicate;
- add/scalar linearity through the bundled map.

Do not state form agreement yet; that theorem needs the actual clipped form
and cross-integrability from Task 2.

**TDD and verification:**

- [ ] Create a strict scratch importing the absent module and checking every
  public definition/theorem, total transform at `c = 0`, a representative
  nonzero mode transform, linearity, and crop/support equality. Record the
  expected missing-module RED.
- [ ] Port the carrier, modes, and linear maps from the strict probe, renaming
  them into `ArithmeticHodge.Analysis` and keeping helper integrability
  theorems private.
- [ ] Add and prove the removable-value quotient before landing the transform
  theorem. Do not keep only an `hc : c ≠ 0` API.
- [ ] Add the crop and support predicate; test an explicitly supported smooth
  pullback equality.
- [ ] Add one umbrella import after the local critical form/Yoshida analysis
  imports in dependency order.
- [ ] Run strict source, umbrella, and API compiles; targeted and full builds;
  global proof/naming/dependency scans; exhaustive axiom audit; exact legacy
  inventory comparison.
- [ ] Delete scratch/audit files and commit exactly
  `add Yoshida clipped log-interval domain`.
- [ ] Obtain a fresh independent review before starting the critical-form
  module.

## Terminal boundary after Task 1

This task proves a sound ambient carrier and exact transform calculus. It
does not yet prove cross-integrability, define the actual clipped Hermitian
form, prove smooth agreement, establish (5.16-Q)/(5.15), construct the
periodic positive tail, or prove ratio-two positivity.

The next plan increment is
`YoshidaClippedCriticalForm.lean`: prove the `O(1/|v|)` transform bound by
interval integration by parts, combine it with the logarithmic kernel bound,
bundle the actual Hermitian form, and prove support-conditional agreement
with `bombieriLocalCriticalForm`.
