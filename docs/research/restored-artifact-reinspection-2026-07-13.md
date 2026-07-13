# Restored artifact reinspection (2026-07-13)

This note records a content-level reinspection of the 183 untracked Lean files
that had accumulated around the production tree.  The files were restored
byte-for-byte after a premature cleanup, inspected before disposition, and
then placed under durable remote archive tags.

## Durable archives

- `archive/legacy-lean-2026-07-11` points to the existing 159-file legacy
  archive commit.  The restored root files matched it exactly.
- `archive/yoshida-finite-fallbacks-2026-07-12` points to commit
  `fede61f0c4593be2b8afd86a8e18691242c6a066`, whose only changes from its
  parent are the 24 Yoshida fallback files.  Their aggregate path-and-content
  SHA-256 is
  `4ebc8b644fc92bb459cd7f05c7add77f26993c14e29ca27a3b592ed979f84fd3`.

Both tags are present on `origin`; recovery no longer depends on untracked
working copies or an opaque Codex checkpoint ref.

## The 159 legacy files

The existing detailed inventory remains accurate: 98 scratch files and 61
audit files, 19,307 lines, no source `sorry`, `admit`, custom `axiom`,
`unsafe`, or `native_decide`, and a large majority consisting of promoted
drafts or print-only promotion audits.  There is no hidden RH proof or
falsifying witness in the set.

Fresh compilation against the current tree identified several kinds of
residual value:

1. `SpectralCalculusAuditScratch.lean`, `ResolventSorryAuditScratch.lean`, and
   `WeilContourSorryAuditScratch.lean` still pass strict checking.  They contain
   explicit countermodels to underspecified spectral calculi, unrelated
   mixing/boundary claims, and the old contour polar-sign/kernel conventions.
   They are useful regression evidence, not production premises.
2. `OrderSorryClosureScratch.lean` and `GrowthCounterexampleScratch.lean` pass
   strict checking and preserve structural obstructions that killed earlier
   completed-zeta and arbitrary-factorization growth routes.
3. `BombieriTestConvergenceScratch.lean`, `FourierForwardRepairScratch.lean`,
   `PaddedLogDerivScratch.lean`, and `WeilConventionScratch.lean` also pass
   strict checking.  Their content is reusable but does not address the active
   factor-two endpoint inequality.
4. The dependency chain through `XiHadamardClosureScratch.lean` and
   `ZeroExponentScratch.lean` checks when built in dependency order.
   `OrderExponentRepair2Scratch.lean` then passes strict checking.
   `XiZeroExponentScratch.lean` checks with one linter warning; its strongest
   theorem gives inverse-square summability and divergence below exponent one,
   not the stronger all-exponents-above-one statement suggested by its name.
   This is the best unpromoted structural salvage candidate, but it requires a
   corrected statement and does not close the current Gate 3 obligation.
5. `HodgeStrategyAuditScratch.lean`, `WeilPublicChainAuditScratch.lean`, and
   `BombieriNegativityAuditScratch.lean` no longer compile unchanged because
   production declarations were renamed or promoted.  Their remaining value
   is historical route/provenance evidence.

The correct disposition is selective recovery from the archive if a named
future obligation needs one of these proofs.  Importing the restored root
files wholesale would cause declaration collisions and revive stale APIs.

## The 24 Yoshida fallbacks

The fallback bundle has 24,430 lines and 6,853,439 bytes.  Its source contains
no `sorry`, `admit`, explicit `axiom`, `unsafe`, or `native_decide`, but it is
an intentionally computational certificate route.

### Ten diagonal enclosures

The files for modes `189` and `191` through `199` each prove the genuine,
currently untracked endpoint

```text
(yoshidaEvenDiagonalTargets n).Contains (yoshidaDiagonalMoment n).
```

Their infinite analytic tail is bounded rather than truncated, but the bulk
of each file is a literal outward-rounded chunk table checked by
`decide +kernel`.  Together with tracked modes `0` through `3` and `190`, they
cover only 15 of 200 old diagonal targets; 185 remain.  They therefore do not
close even the superseded finite route.

### Full-pivot bundle

`YoshidaEvenFullPivotCore.lean` contains a sound, strict-compiling generic
interval-refinement and rounded-Schur checkpoint argument.  Its key theorem
shows that positive pivots of wider rounded intervals imply exact interval
pivots.  This generic core could be extracted into a neutral interval-Schur
module if a future non-enumerative obligation needs it.

The other thirteen files are one indivisible payload certificate: six packed
payloads with 513,500 entries, six chunk replays, and a terminal assembly
proving

```text
evenTarget_full_intervalPivots : YoshidaEvenFullTargetPivots.
```

They use 40 high-heartbeat chunk decisions plus ancillary kernel decisions.
The result discharges the old target-box pivot premise only; it does not prove
that the actual 200 moments lie in those boxes.

## Decision for the active RH path

Promote none of the archived files into the current umbrella.  The finite
mode tables and pivot payloads violate the structural-proof policy and remain
incomplete.  The legacy countermodels and xi exponent argument have research
value and are now durably recoverable, but none proves or falsifies the active
factor-two inequalities `0 <= Q(w) + P(w)` and `0 <= Q(w) - P(w)`.
