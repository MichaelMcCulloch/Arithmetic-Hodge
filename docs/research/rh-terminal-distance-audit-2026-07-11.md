# RH Terminal-Distance Audit — 2026-07-11

This log records how each coherent increment changes the distance to the
terminal proof-or-falsification objective in `GOAL.md`.  It is deliberately
separate from build logs: a green build is evidence, not a stage transition.

## `519bb2e` — Yoshida odd comparison reserve

1. **Theorem added.**  The exact target interval Gram has an entrywise
   `1 / 40` reserve over the kernel-certified rational comparison matrix.  The
   reserve transports to the actual clipped odd Gram under the explicit moment
   bridge and sine/diagonal enclosure hypotheses, and every Hermitian
   entrywise perturbation bounded by `1 / 40` preserves positive definiteness.
2. **Gate hypothesis eliminated.**  No Gate 0 analytic hypothesis was
   eliminated: the diagonal enclosure is still open.  The increment does
   eliminate a later finite/tail closure subproblem: once an omitted Hermitian
   contribution is bounded entrywise by `1 / 40`, positivity of the corrected
   ten-mode block follows without recomputing or enlarging the finite matrix.
3. **Assumptions remaining.**  Gate 0 still requires the unconditional
   diagonal target enclosure package and its composition with the already
   unconditional clipped/moment bridge and sine enclosure package.  Gates 1–4
   remain untouched.
4. **Next make-or-break lemma.**  Prove
   `diagonalTargetEnclosures_from_certificate :
   YoshidaOddDiagonalTargetEnclosures` by kernel-checking the rational finite
   heads and applying the sharp infinite correction-tail estimate.
5. **Viability evidence.**  The `1 / 40` inequalities reduce in the kernel;
   strict compilation and the targeted module build pass; all five public
   theorems use only `propext`, `Classical.choice`, and `Quot.sound`; an
   independent review found the diagonal and off-diagonal signs correct and no
   circular dependency or proof bypass.
