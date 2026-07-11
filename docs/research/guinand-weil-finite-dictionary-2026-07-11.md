# Finite Guinand--Weil Dictionary: Formalization Relevance

## Primary source

- Akiva Groskin, *A finite Guinand--Weil dictionary and archimedean tail order
  for the truncated Weil quadratic form*, arXiv:2607.02828v1, 2 July 2026:
  <https://arxiv.org/abs/2607.02828>
- Archival package: <https://doi.org/10.5281/zenodo.21124802>
- Downloaded source/ancillary tarball SHA-256:
  `8ae1a52f365f5302b89b1cbfa53336457e6f0285b35daf5d69fcf2e9ba6cec66`.

## Exact scope

The paper gives two finite-level results relevant to the repository's Weil
positivity program:

1. A real even Galerkin vector of dimension `N + 1` is transported explicitly
   to a band-limited Guinand--Weil test function whose zero sum is exactly the
   corresponding cutoff-free quadratic matrix value.
2. The omitted archimedean tail past a finite cutoff is a positive
   Cauchy--Stieltjes matrix increment, with an explicit two-sided error budget.

The released package constructs rigorous Arb interval entries and performs an
interval `LDL^T` inertia computation. Its recorded `c = 100`, `N = 200`,
dimension-401 run at 9000 bits reports 401 positive pivots, zero negative
pivots, and no undetermined pivot. The generator is
`anc/arb_ldlt_certify.py`; its SHA-256 is
`02462e7f75a601ed8a5cc4d5c22064ece8088140ff45b9a21fd0295162c72039`.

## What this does not prove

The paper explicitly makes no RH or global Weil-positivity claim. In
particular:

- it parametrizes a finite family at each `(c, N)`, not every admissible test;
- it provides no inverse map from an arbitrary Guinand--Weil test to a finite
  Galerkin vector;
- positivity of one or many finite matrices does not supply the missing
  density, uniform lower-bound, or limiting argument needed for all tests;
- the reported positive dimension-401 block therefore is not evidence of a
  formal RH proof and supplies no negative witness.

Consequently this route does not replace the current Yoshida program, which
targets every test with support ratio at most two.

## Use in Arithmetic-Hodge

The package is valuable in two narrower roles.

### Certificate engineering

Its cutoff-free entry formulas and interval `LDL^T` implementation are a model
for generating the finite certificates missing from Yoshida's paper. For Lean,
the Python/Arb result is only a generator: production theorems must prove entry
enclosures, import exact rational centers/error radii or factors, and check the
resulting matrix inequalities or pivots with the kernel.

The shipped provenance JSON records only the inertia summary, not a replayable
list of exact entries, factors, or pivot intervals. It cannot itself be used as
a Lean certificate.

### Falsification search

Every rigorously negative finite matrix vector produced by the dictionary
would give an explicit Guinand--Weil test with a negative zero-side quadratic
value. After formalizing the transport and explicit formula, such a witness
would be a finite route to `not RH`. The paper's certified block is positive,
but the architecture gives a principled search-and-certify loop for other
parameters without confusing numerical cutoff artifacts with genuine
negativity.

## Decision

Continue the Yoshida ratio-two formalization as the proof-side critical path.
Reuse the new package's interval-entry and `LDL^T` ideas when designing the
10-by-10 and 200-by-200 Yoshida certificates. Keep the finite dictionary as a
parallel, bounded falsification track once the current dilation and
Fourier/Schur foundations are in production.
