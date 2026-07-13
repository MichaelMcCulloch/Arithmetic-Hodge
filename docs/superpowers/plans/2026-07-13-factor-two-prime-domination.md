# Factor-Two Local-Form/Prime-Domination Plan

**Status:** Complete and verified.  The two local-prime endpoint inequalities
and the mixed phase-pencil inequality remain open.

**Goal:** Recombine the signed factor-two real channels into the actual local
critical self-form of `g ± normalizedDilation 2 g` and the exact coupled
two-prime cross symbol.  This should remove the artificial core/residual split
from the open endpoint inequalities without asserting their positivity.

## Decisive obligation

For every ratio-at-most-two seed `g`, prove exact identities

```text
D(g) - R(g) = (1/2) B_local(g - D₂g, g - D₂g) + Re P₂,₃(g)
D(g) + R(g) = (1/2) B_local(g + D₂g, g + D₂g) - Re P₂,₃(g).
```

The corresponding signed channel is nonnegative exactly when its full local
critical self-form dominates the correctly signed prime term.  A strict reverse
must remain an explicit `c = -1` or `c = 1` negative Bombieri witness.

## Constraints

- Do not assume local critical positivity: the two-cell tests have support
  ratio at most four, and the prime terms for `2` and `3` survive.
- Keep the local gamma and prime pieces coupled.  Do not return to the false
  core-only norm route or truncate the complete residual series.
- Do not claim the mixed alternating phase-pencil inequality from the two
  signed endpoints; it remains a separate sharp obligation.
- Every production dependency must be structural.  Finite mode tables,
  enclosures, generated certificates, evaluators, `native_decide`, `unsafe`,
  custom axioms, `sorry`, and protected fallback imports are inadmissible.
- Run all Lean/Lake workloads sequentially through the root `Justfile` and
  preserve all 159 archived artifacts and 24 fallbacks byte-for-byte.

## Implementation

1. Prove normalized-dilation invariance of the real local diagonal by
   transporting through the exact production functional on each ratio-two
   cell.
2. Polarize the Hermitian local form to identify the local self-forms of
   `g - D₂g` and `g + D₂g` with twice `D - Re localCross` and
   `D + Re localCross`, respectively.
3. Substitute the exact global-cross identity
   `globalCross = localCross - primeCross` to obtain both signed channel
   identities.
4. Export the two nonnegativity iff statements and the two strict explicit
   `c = ±1` failure iff statements.

## Validation and publication

- Strict-check the focused module and umbrella, then run one sequential full
  build.
- Audit every public endpoint with `#print axioms`, requiring only the
  standard Mathlib axioms.
- Recursively inspect the tracked/current source closure for missing,
  untracked, cyclic, protected, quarantined-name, or forbidden-proof
  dependencies.
- Recheck both protected inventories and obtain independent sign, factor,
  support, circularity, and no-overclaim review.
- Append the five-part terminal-distance audit, stage only the intended
  production module, umbrella import, plan, and audit entry, then commit and
  push `main`.

## Next analytic target

Prove or strictly reverse either exact local-prime domination inequality by a
two-cell real-space square that retains both prime atoms.  If both endpoint
channels survive, prove the sharp mixed phase-pencil inequality at form level;
do not replace it with the strictly stronger row-contraction condition.
