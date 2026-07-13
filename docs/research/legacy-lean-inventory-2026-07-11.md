# Legacy Lean Research Inventory (2026-07-11)

This inventory records the 159 untracked root-level Lean research artifacts
that predated the active compact-support positivity task.  The corresponding
machine-readable table is
[`legacy-lean-inventory-2026-07-11.tsv`](legacy-lean-inventory-2026-07-11.tsv).
A current compile-and-content follow-up, including the later 24-file Yoshida
fallback bundle, is recorded in
[`restored-artifact-reinspection-2026-07-13.md`](restored-artifact-reinspection-2026-07-13.md).

## Summary

- 159 files: 98 scratch files and 61 audit files.
- 19,307 source lines.
- 772 top-level declarations: 613 theorems, 26 lemmas, 130 definitions, and
  3 abbreviations.
- No source-level `sorry`, `admit`, or custom `axiom` declaration was found.
- 555 `#print axioms` commands occur in the audit artifacts.
- 66 files have complete normalized declaration overlap with tracked
  production code; 29 have partial overlap; 10 have no matched production
  declaration; 54 contain no top-level theorem or definition.
- TSV SHA-256:
  `f21de348033190d753349c12427a26ea09b5e472b7117ee605b8ace01ea0df0d`.

This was a structural inventory only.  It did not compile the 159 files and
does not by itself certify that unmatched declarations still typecheck.

## Disposition policy

1. Preserve the original files until an archival Git ref contains them.
2. Treat complete-overlap promotion audits and print-only audit markers as
   superseded, but do not delete them before archival.
3. Compile and inspect partial- or no-overlap files before promoting any
   declaration.
4. Promote useful declarations through focused production modules with the
   same proof, naming, build, and review gates as current work.
5. Keep countermodels and dependency audits as research evidence even when
   they are intentionally unsuitable for the trusted production import tree.

## Highest-value salvage queue

1. `SpectralCalculusAuditScratch.lean`
2. `ResolventSorryAuditScratch.lean`
3. `WeilContourSorryAuditScratch.lean`
4. `HodgeStrategyAuditScratch.lean`
5. `WeilPublicChainAuditScratch.lean`
6. `BombieriNegativityAuditScratch.lean`
7. `OrderSorryClosureScratch.lean`
8. `GrowthCounterexampleScratch.lean`
9. `OrderExponentRepair2Scratch.lean`
10. `XiZeroExponentScratch.lean`

The first six primarily preserve countermodels, provenance checks, or an
explicit statement of the remaining positivity gap.  The last four contain
unmatched or partially matched mathematical declarations that should be
compiled before any production promotion.

## Clearly superseded families

- All 49 `PromotionAudit` artifacts.
- The 66 files whose normalized declarations now all occur under
  `ArithmeticHodge`.
- Five non-promotion print-only audit markers.
- `XiProductReindexScratch.lean`.

The largest promoted clusters concern Bombieri/Multiplicative Weil formulas,
rectangle and xi contours, zeta zero counting and logarithmic derivatives,
Hadamard/entire-function infrastructure, and adèle-class consistency.
