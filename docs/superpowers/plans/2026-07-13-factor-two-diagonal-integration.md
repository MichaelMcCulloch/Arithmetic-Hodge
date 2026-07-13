# Factor-Two Diagonal Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Integrate the exact factor-two physical diagonal into the project umbrella, restore `GOAL.md` to the live Gate 3 route, and record the resulting terminal-distance checkpoint.

**Architecture:** Reuse the already structural theorem `bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical`; do not introduce a second diagonal API. The umbrella import makes its dependency closure part of the canonical build, while the goal and audit name the exact parity-channel determinant that remains open.

**Tech Stack:** Lean 4, Mathlib, Lake, the root `Justfile`, Markdown, Git.

## Global Constraints

- Every Lean- or Lake-related command must run through a root `Justfile` recipe.
- Never edit, rename, move, stage, or delete the 159 protected legacy Lean artifacts or the 24 documented fallback modules.
- No finite mode table, numeric enclosure, certificate, `sorry`, custom axiom, `unsafe`, `native_decide`, or circular restricted-positivity premise may enter the terminal path.
- Run no concurrent high-memory Lean workloads.
- Stage and commit only the files in this increment after fresh verification.

---

### Task 1: Integrate and audit the exact physical diagonal

**Files:**
- Modify: `ArithmeticHodge.lean`
- Modify: `GOAL.md`
- Modify: `docs/research/rh-terminal-distance-audit-2026-07-11.md`
- Create: `docs/superpowers/plans/2026-07-13-factor-two-diagonal-integration.md`

**Interfaces:**
- Consumes: `YoshidaFactorTwoDiagonalPhysical.bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical` and `YoshidaFactorTwoCenteredPhysical.factorTwoGlobalCrossSymbol_re_eq_parity` / `factorTwoGlobalCrossSymbol_im_eq_parity`.
- Produces: a canonical umbrella import and a live directive whose next obligation is the exact same-seed parity-channel determinant.

- [x] **Step 1: Confirm the stale and missing-integration preconditions**

Run:

```console
rg -n 'Gate 0 is reopened|YoshidaFactorTwoDiagonalPhysical' GOAL.md ArithmeticHodge.lean
git status --short --untracked-files=no
```

Expected: the stale Gate 0 text is present, the diagonal module is absent from `ArithmeticHodge.lean`, and no tracked worktree changes predate this increment.

- [x] **Step 2: Add the umbrella import and replace only stale goal routing**

Add:

```lean
import ArithmeticHodge.Analysis.YoshidaFactorTwoDiagonalPhysical
```

beside the existing factor-two physical/centered imports. In `GOAL.md`, change the checkout path to `/workspaces/Arithmetic-Hodge` and replace only `Current directive`: record structural closure of Gates 0--2, the failed isolated-core bound, the exact diagonal and cross parity formulas now available, and the same-seed determinant as the current proof-or-obstruction target.

- [x] **Step 3: Record the terminal-distance checkpoint**

Append one audit entry covering commits `cdfde51` through `79df9f0`: exact theorem added, Gate 3 obligation eliminated, remaining determinant/Toeplitz obligations, next parity-channel lemma, and integrity evidence actually observed in Step 4.

- [x] **Step 4: Run fresh focused and umbrella verification**

Run sequentially:

```console
just strict ArithmeticHodge/Analysis/YoshidaFactorTwoDiagonalPhysical.lean
just strict ArithmeticHodge.lean
just build
rg -n 'sorry|native_decide|unsafe|axiom ' ArithmeticHodge/Analysis/YoshidaFactorTwoSelfCorrelationSupport.lean ArithmeticHodge/Analysis/YoshidaFactorTwoDiagonalGeometric.lean ArithmeticHodge/Analysis/YoshidaFactorTwoDiagonalPhysical.lean
```

Expected: both strict compiles and the full build pass; the forbidden-proof scan has no matches. Check the protected inventory against `refs/archive/legacy-lean-2026-07-11` and confirm all 159 inventoried files plus 24 fallbacks remain byte-identical.

- [x] **Step 5: Review the patch and commit the coherent increment**

Run:

```console
git diff --check
git diff -- ArithmeticHodge.lean GOAL.md docs/research/rh-terminal-distance-audit-2026-07-11.md docs/superpowers/plans/2026-07-13-factor-two-diagonal-integration.md
git diff --no-index /dev/null docs/superpowers/plans/2026-07-13-factor-two-diagonal-integration.md || true
git add ArithmeticHodge.lean GOAL.md docs/research/rh-terminal-distance-audit-2026-07-11.md docs/superpowers/plans/2026-07-13-factor-two-diagonal-integration.md
git diff --cached --check
git commit -m "integrate the factor-two physical diagonal"
```

Expected: only the four named files are staged and the commit succeeds.
