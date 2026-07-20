# Module coverage ledger

`lake build` verifies only the import closure of the root `ArithmeticHodge.lean`.
A module on disk but outside that closure is silently unverified by the default
target. Audit with:

```sh
python3 scripts/module_reachability.py          # summary
python3 scripts/module_reachability.py --list   # plus orphan list
```

## Rule

Every committed module must be reachable from the root, normally by adding its
`import` to `ArithmeticHodge.lean` in the same commit. When a route is
abandoned, keep its compiled obstruction/probe modules imported — they document
why the route died — but stop extending them.

## Snapshot (2026-07-20, after integration)

| | count |
|---|---|
| modules on disk | 1,278 |
| reachable from root | 1,126 |
| unreachable (coverage debt) | 152 |

Debt breakdown: 73 `YoshidaEvenSparse*` (generated sparse-congruence family,
see `scripts/generate_yoshida_even_sparse_congruence.py`), 46 `YoshidaFourCell*`
(mid-chain modules of the odd `P51` route whose tips do not re-import them),
15 `YoshidaFactorTwo*` strata, plus a handful of endpoint modules.

## Guidance for the next agent

- Integrate or archive the 152 in bounded batches: add a batch of imports to
  the root, run `just build`, commit on green. Any batch member that no longer
  compiles is dead work — record what it claimed, then delete it.
- The `YoshidaEvenSparse*` family belongs to the demoted static-split
  certificate (see the certificate decision in `GOAL.md`). Integrate it only
  if the static fallback is ever reactivated; otherwise it is the first
  candidate for archival.
- Two files were deleted on 2026-07-20 as unfinished drafts that failed proof
  elaboration after import repair
  (`YoshidaFactorTwoPhaseRetunedObstruction{OddP5Cap,AlternatingCap}Structural`).
  Their intended obstruction caps for the retuned static gates are still open
  claims; the compiled `IntrinsicNine*` siblings document that route's status.
- The resource guard in the `Justfile` now measures PSS, so full-parallel
  `lake build` of the whole library is safe (~9,300 jobs). Do not fall back to
  one-file-per-build workflows.
