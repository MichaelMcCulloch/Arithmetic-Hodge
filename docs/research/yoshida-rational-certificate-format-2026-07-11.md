# Lean-Replayable Rational Certificates for Yoshida's Finite Blocks

Date: 2026-07-11

This note records the certificate format chosen for the finite-dimensional
part of Yoshida's support-ratio-two positivity argument.  It is a design and
trust-boundary result, not a positivity theorem and not a claim about RH.

## Source boundary

Yoshida's section 6 gives the architecture and the final correction budgets,
but does not print the numerical matrices or the elimination trace:

- odd block: dimension 10 and entrywise correction budget `1 / 40`;
- even block: dimension 200 and entrywise correction budget `1 / 2000`.

The ancillary program from the recent finite Guinand--Weil work,
`arb_ldlt_certify.py`, is useful as a generator pattern but certifies a
different 401-by-401 matrix.  Its JSON and log contain only parameters,
timings, and inertia counts; they contain no replayable entries, factors, or
pivots.  It therefore cannot be reused as Yoshida's missing certificate.

Primary references:

- Yoshida, *On Weil's criterion for the Riemann hypothesis*, section 6:
  <https://projecteuclid.org/download/pdf_1/euclid.aspm/1534359132>
- Finite Guinand--Weil ancillary source:
  <https://arxiv.org/abs/2607.02828>

The inspected ancillary script has SHA-256
`02462e7f75a601ed8a5cc4d5c22064ece8088140ff45b9a21fd0295162c72039`.

## Two proof layers

The certificate must keep numerical discovery outside the trusted base.

1. The analytic comparison layer proves in Lean that the true corrected Gram
   matrix satisfies the exact rational inequalities used by the certificate.
2. The algebraic layer checks an exact rational factorization in Lean and
   transports its positivity to a complex matrix.

Arb or Python may search for rational endpoints and factors.  Their output is
only witness data: Lean must prove the enclosures, exact recurrences, positive
pivots, and comparison theorem.

## Default packed format

For dimension `n`, store:

- the lower triangle of a symmetric rational matrix `A`;
- the strict lower triangle of a unit-lower rational matrix `L`;
- a positive rational diagonal `d`.

Conceptually:

```lean
structure PackedRationalLDL (n : ℕ) where
  aLower : Vector ℚ (n * (n + 1) / 2)
  lStrict : Vector ℚ (n * (n - 1) / 2)
  d : Vector ℚ n
```

Accessors reflect `A` across the diagonal and supply zero/one entries of `L`
structurally.  Hence symmetry of `A`, triangularity of `L`, and the unit
diagonal are generic theorems rather than generated evidence.  In particular,
`det L = 1`, so no inverse matrix belongs in the payload.

At `n = 200`, this contains:

- 20,100 entries of `A`;
- 19,900 strict-lower entries of `L`;
- 200 diagonal entries;
- 40,200 rationals total.

Every rational must be serialized as a reduced numerator/positive-denominator
pair without passing through binary floating point.  A provenance manifest
should record the dimension, counts, bit-size statistics, smallest pivot,
formula version, generator revision, and payload SHA-256, but the manifest is
not a proof premise.

## Kernel-checked recurrence

For structural unit-lower `L`, check only the lower recurrences:

```lean
def LDLRecurrence (A L : Matrix (Fin n) (Fin n) ℚ)
    (d : Fin n → ℚ) : Prop :=
  (∀ i, 0 < d i) ∧
  (∀ i,
    A i i = d i + ∑ k ∈ Finset.Iio i, L i k * L i k * d k) ∧
  (∀ i j, j < i →
    A i j = L i j * d j +
      ∑ k ∈ Finset.Iio j, L i k * L j k * d k)
```

Together with structural symmetry, this proves
`A = L * Matrix.diagonal d * L.transpose`.  The production bridge
`rationalLDL_posDef_complex` then maps this equality through `Rat.castHom ℂ`
and applies positive-definite congruence.

At dimension 200 the recurrence has 1,353,400 scalar summands, versus
8,000,000 for checking all dense factor entries.  Reduction of a nested dense
matrix expression can duplicate work toward `n^4`; it must not be the
production checking path.

Generate row-level or small row-chunk lemmas using `decide +kernel`, ordinary
`decide`, or `norm_num`.  This permits kernel caching and resumable builds.
Do not use `native_decide`: in the pinned Lean version it introduces a named
`native_decide` axiom and violates the repository's proof invariant.

## Analytic front ends

### Odd block

Yoshida's comparison matrix has diagonal entries bounded below by the true
diagonal minus `1 / 40`, and off-diagonal entries formed from negative
absolute-value bounds minus `1 / 40`.  The appropriate generic bridge is an
absolute-entry comparison theorem: apply the positive real comparison matrix
to the vector of coefficient norms and bound every complex off-diagonal term
by its norm.

A fixed rational lower comparison matrix followed by exact rational LDL is
the preferred artifact for the 10-by-10 block.

### Even block

Yoshida propagates intervals through elimination after the `1 / 2000`
correction bound.  This does not automatically produce a single entrywise or
Loewner lower matrix.  Try, in order:

1. find a fixed rational lower form;
2. apply a rational congruence preconditioner and prove a fixed lower form or
   strict diagonal dominance;
3. formalize a sound rational interval-Schur checker and replay the interval
   elimination in Lean.

The soundness theorem for the fallback must induct through Schur complements;
externally asserted pivot signs are not acceptable.

## Factor-growth fallback

Exact rational LDL factors may acquire determinant-sized numerators and
denominators.  The generator must report actual bit-size histograms before a
large payload is committed.  If growth is excessive, clear a positive common
denominator and use fraction-free symmetric Bareiss elimination over `Int`.
Lean must then prove exact divisibility, positive pivots, and the link from the
fraction-free recurrence to positive definiteness.

## Required generator contract

The Yoshida-specific generator must:

1. implement the exact odd/even Gram formulas;
2. use rigorous balls only to discover outward rational bounds;
3. convert bounds by explicit rational floor/ceiling operations;
4. incorporate the formal `1 / 40` and `1 / 2000` correction budgets in the
   direction required by the comparison theorem;
5. generate and self-check the exact rational certificate;
6. emit deterministic Lean data and row proof modules;
7. fail on any non-strict pivot, invalid enclosure, or recurrence mismatch;
8. switch to the fraction-free format when the configured size threshold is
   exceeded.

## Current verified prototypes

The investigation produced strict-compiling temporary probes for:

- rational LDL-to-complex positive definiteness;
- structural unit-lower invertibility;
- a lower-recurrence soundness checker;
- a concrete 2-by-2 regression;
- the trust difference between `decide +kernel` and `native_decide`.

The next production certificate task is to formalize the packed recurrence
checker.  The unresolved mathematical boundary is regenerating rigorous
analytic entries for Yoshida's two finite blocks, especially the even
interval-elimination argument.
