# Yoshida Fourier Modes and Decomposition Implementation Plan

> **For agentic workers:** Use `superpowers:subagent-driven-development` and
> implement one task at a time with a fresh independent review after each
> commit.

**Goal:** Reconcile Mathlib's probability-Haar Fourier basis with Yoshida's
Lebesgue-normalized sine/cosine modes, then prove exact `Fin 10` odd and
`Fin 200` even coefficient-plus-tail decompositions.

**Architecture:** Put normalization and mode identities in a reusable mode
module. Put reverse span inclusions, parity-filtered low projections, typed
tail remainders, and the matrix-ready decompositions in a second module. Use
the reviewed projection and parity APIs; do not duplicate reflection or
generic Fourier-tail definitions.

**Verified discovery artifact:**
`/tmp/YoshidaFourierParityTailProbe.lean`, SHA-256
`7823338c6144f7e6c9cb9b9c7623b41af41ca3bebb60666889f0a30ef836bd33`,
strict-compiles and audits to the standard Mathlib axioms. The exact theorem
shapes and normalization rationale are recorded in
`docs/research/yoshida-fourier-parity-tail-2026-07-11.md`.

## Global constraints

- No `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, or circular
  positivity/RH assumptions.
- Preserve all 159 inventoried legacy root Lean files byte-for-byte.
- Work directly on `main` as authorized; stage only task-owned paths.
- Strict missing-module RED before implementation; strict production,
  facade, and API checks; full `lake build ArithmeticHodge`; forbidden-proof
  and naming scans; theorem axiom audits; exact inventory comparison.
- Every exported theorem must depend only on `propext`, `Classical.choice`,
  and `Quot.sound`, or a subset.
- Keep the modules generic over a positive circle length `T`. Do not hard-code
  `T = log 2`; that specialization belongs at the Bombieri/Yoshida boundary.
- Distinguish probability-Haar norm from volume/Lebesgue norm explicitly.

---

### Task 1: Lebesgue-normalized Yoshida modes and finite low spans

**Files:**

- Create: `ArithmeticHodge/Analysis/YoshidaFourierModes.lean`
- Modify: `ArithmeticHodge/Analysis/CenteredAddCircleFourier.lean`
- Temporary test: `YoshidaFourierModesScratch.lean`

**Import:**

```lean
import ArithmeticHodge.Analysis.CenteredAddCircleFourierParity
```

**Required public definitions:**

```lean
def lebesgueNormalizedExponential (n : ℤ) : CircleL2 (T := T) :=
  ((Real.sqrt T)⁻¹ : ℂ) • fourierLp 2 n

def lebesgueNormSq (f : CircleL2 (T := T)) : ℝ :=
  T * ‖f‖ ^ 2

def yoshidaOddMode (n : ℕ) : CircleL2 (T := T)
def yoshidaEvenMode (n : ℕ) : CircleL2 (T := T)
def yoshidaEvenZeroMode : CircleL2 (T := T)

abbrev YoshidaOddIndex := Fin 10
abbrev YoshidaEvenIndex := Fin 200

def yoshidaOddLowMode (i : YoshidaOddIndex) : CircleL2 (T := T)
def yoshidaEvenLowMode (i : YoshidaEvenIndex) : CircleL2 (T := T)

def yoshidaOddLowSubmodule : Submodule ℂ (CircleL2 (T := T))
def yoshidaEvenLowSubmodule : Submodule ℂ (CircleL2 (T := T))
```

Use exactly the mode scalars verified in the probe:

```lean
yoshidaOddMode n =
  (-Complex.I / (Real.sqrt 2 : ℂ)) • (chi n - chi (-n))

yoshidaEvenMode n =
  ((Real.sqrt 2 : ℂ)⁻¹) • (chi n + chi (-n))

yoshidaEvenZeroMode = chi 0
```

where `chi = lebesgueNormalizedExponential`.

**Required theorem groups:**

- `reflectionL2_lebesgueNormalizedExponential`;
- `integral_norm_sq_volume_eq_lebesgueNormSq` and volume norm one for `chi`;
- parity membership for all three mode families;
- exponential orthogonality;
- `lebesgueNormSq = 1` for nonzero sine/cosine modes and the zero mode;
- exact Fourier coefficient formulas for `chi`, odd modes, even modes, and
  the zero mode;
- exact low indexing: odd `i.val + 1`, even `i.val` with a separate zero case;
- parity, finite-Fourier-span, and Lebesgue-norm-one theorems for every low
  mode;
- forward inclusions

```lean
yoshidaOddLowSubmodule ≤ oddL2Submodule ⊓ finiteFourierSubmodule 10
yoshidaEvenLowSubmodule ≤ evenL2Submodule ⊓ finiteFourierSubmodule 199.
```

- [ ] Record a strict missing-module RED checking all public definitions and
  representative norm/coefficient/index theorems.
- [ ] Port the verified normalization proof using
  `AddCircle.volume_eq_smul_haarAddCircle` and the actual `L2.inner_def`;
  do not infer the factor from informal measure notation.
- [ ] Prove norm identities from Fourier orthonormality and exact square-root
  algebra. Require `n ≠ 0` where positive and negative frequencies must differ.
- [ ] Add one facade import, run all gates, delete scratch, and commit
  `add Lebesgue-normalized Yoshida Fourier modes`.

---

### Task 2: Parity low-span equalities and coefficient-plus-tail decomposition

**Files:**

- Create: `ArithmeticHodge/Analysis/YoshidaFourierDecomposition.lean`
- Modify: `ArithmeticHodge/Analysis/CenteredAddCircleFourier.lean`
- Temporary test: `YoshidaFourierDecompositionScratch.lean`

**Import:**

```lean
import ArithmeticHodge.Analysis.YoshidaFourierModes
```

**Required public definitions:**

```lean
def evenLowFourierProjection (N : ℕ) (f : CircleL2 (T := T)) :=
  evenPart (T := T) (lowFourierProjection (T := T) N f)

def oddLowFourierProjection (N : ℕ) (f : CircleL2 (T := T)) :=
  oddPart (T := T) (lowFourierProjection (T := T) N f)

def evenTailRemainder (N : ℕ)
    {f : CircleL2 (T := T)} (hf : f ∈ evenL2Submodule (T := T)) :
    evenFourierTailSubmodule (T := T) N

def oddTailRemainder (N : ℕ)
    {f : CircleL2 (T := T)} (hf : f ∈ oddL2Submodule (T := T)) :
    oddFourierTailSubmodule (T := T) N

def yoshidaOddLowComponent (f : CircleL2 (T := T)) :
    yoshidaOddLowSubmodule (T := T)

def yoshidaEvenLowComponent (f : CircleL2 (T := T)) :
    yoshidaEvenLowSubmodule (T := T)
```

**Required reverse span and equality results:**

```lean
theorem yoshidaOddLowSubmodule_eq_parity_finite :
  yoshidaOddLowSubmodule (T := T) =
    oddL2Submodule (T := T) ⊓ finiteFourierSubmodule (T := T) 10

theorem yoshidaEvenLowSubmodule_eq_parity_finite :
  yoshidaEvenLowSubmodule (T := T) =
    evenL2Submodule (T := T) ⊓ finiteFourierSubmodule (T := T) 199
```

Prove these constructively, as in the strict probe: express
`fourierLp n - fourierLp (-n)` and
`fourierLp n + fourierLp (-n)` as nonzero scalar multiples of the matching
Yoshida modes, and treat `n = 0` separately. Do not replace the proof with an
unproved dimension claim.

**Required projection/tail results:**

- parity membership and exact Fourier coefficients of both parity-filtered
  projections;
- low projection membership in the corresponding Yoshida span at cutoffs 10
  and 199;
- remainders in the exact complete odd/even tail submodules;
- exact low-plus-tail equalities.

**Final matrix-ready APIs:**

```lean
theorem exists_yoshida_odd_ten_coefficients_add_tail
    {f : CircleL2 (T := T)} (hf : f ∈ oddL2Submodule (T := T)) :
  ∃ c : Fin 10 → ℂ,
    f = (∑ i, c i • yoshidaOddLowMode (T := T) i) +
      (oddTailRemainder (T := T) 10 hf : CircleL2 (T := T))

theorem exists_yoshida_even_twoHundred_coefficients_add_tail
    {f : CircleL2 (T := T)} (hf : f ∈ evenL2Submodule (T := T)) :
  ∃ c : Fin 200 → ℂ,
    f = (∑ i, c i • yoshidaEvenLowMode (T := T) i) +
      (evenTailRemainder (T := T) 199 hf : CircleL2 (T := T))
```

- [ ] Record strict missing-module RED with both final decompositions.
- [ ] Reuse production `evenPartCLM`/`oddPartCLM`; do not duplicate the parity
  continuous maps from the discovery probe.
- [ ] Port the reverse-span proof and all tail membership/equality results.
- [ ] Obtain coefficient functions from submodule span membership using
  finite span induction or the strict probe's constructive route; retain exact
  `Fin 10`/`Fin 200` types.
- [ ] Strict-check, full-build, audit all exported theorems, scan, compare the
  159 artifacts, delete scratch, and commit
  `decompose parity functions into Yoshida modes and tails`.

## Terminal boundary after this plan

The output is an exact Hilbert-space coordinate decomposition. It does not
claim that Yoshida's Hermitian form is bounded on circle `L²`, does not provide
tail coercivity, and does not prove any finite corrected Gram matrix positive.
Those are separate form-completion, analytic-certificate, and matrix tasks.
