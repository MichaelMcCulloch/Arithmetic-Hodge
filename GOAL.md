# Arithmetic-Hodge Terminal Goal

## Active objective

Continue autonomously in `/home/michael/Development/Arithmetic-Hodge` toward a
fully formal, axiom-free proof or falsification of the Riemann Hypothesis in
Lean 4/mathlib. Preserve the production invariant of zero
`sorry`/`admit`/custom `axiom`/unsafe proof bypasses, preserve the 159
inventoried legacy Lean research artifacts, and never claim RH is settled
until an all-test theorem or an explicit verified counterexample witness
compiles under the repository's full gates.

Keep the root agent continuously advancing the mathematical critical path;
use subagents only for bounded, independent research, implementation, or
review; avoid idle waiting while useful local work exists. Commit each
coherent verified increment on `main` as work proceeds, with strict module
compilation, full `lake build`, forbidden-proof/naming scans, dependency and
axiom audits, and independent review in proportion to risk. Maintain
reboot-resumable plans, ledgers, source notes, and exact commit references.

The immediate program is:

1. Formalize normalized multiplicative dilation and logarithmic centering.
2. Formalize Yoshida's support-ratio-at-most-two positivity through
   Fourier-circle normalization, parity decomposition, coercive tails, an
   abstract Schur-complement theorem, sharp analytic estimates, and
   Lean-checked rational finite-matrix certificates.
3. Transport this positivity theorem to the Bombieri quadratic functional.
4. Attack the remaining all-support gap through source-backed positivity
   mechanisms, or pursue a fully explicit negative Bombieri witness that
   would falsify RH.

Use primary web sources whenever they can sharpen obligations or certify
constants, and continue through non-obvious proof obligations rather than
stopping at a research summary.

## Completion standard

This goal is complete only when one of these artifacts passes every repository
gate without proof bypasses:

- a theorem proving RH for all required Bombieri/Weil test functions and then
  the repository's canonical `RiemannHypothesis` statement; or
- an explicit, formally verified counterexample witness implying `¬ RH`.

Finite-support or restricted-support positivity theorems are progress toward
the goal, not completion of it.

## Working discipline

- Commit each coherent, freshly verified increment as work proceeds.
- Keep production Lean free of `sorry`, `admit`, custom axioms, unsafe proof
  shortcuts, and circular RH-equivalent dependencies.
- Keep the root agent on the critical path while agents perform distinct,
  bounded work; do not idle merely because agents are running.
- Preserve all inventoried legacy Lean artifacts and keep their archive ref
  and inventory usable across reboot.
- Record exact sources, theorem obligations, certificates, build commands,
  scans, reviews, and commit hashes so another session can resume precisely.
- Treat a full successful build and axiom/dependency audit as evidence, and do
  not describe RH as proved or falsified before the terminal artifact exists.
