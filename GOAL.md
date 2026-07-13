# Arithmetic-Hodge RH Objective

## Objective

Work toward a closed Lean theorem establishing exactly one of:

```lean
theorem arithmeticHodge_riemannHypothesis : RiemannHypothesis := by
  ...
```

or

```lean
theorem arithmeticHodge_not_riemannHypothesis : ¬ RiemannHypothesis := by
  ...
```

The theorem must have no mathematical hypotheses. It must compile in the
current repository without `sorry`, `admit`, a project-added axiom, or a
circular assumption equivalent to the desired conclusion.

This is the only terminal success condition. Intermediate results matter to
the extent that they shorten a credible path to one of these two declarations.
Do not claim that RH has been proved or falsified before the corresponding
closed theorem exists and passes final validation.

## Mathematical fidelity

Lean is the primary proof checker. Any method is permitted when its logical
content is represented faithfully in Lean and it advances the terminal
objective. In particular, the work may use:

- direct analytic, algebraic, spectral, operator-theoretic, or number-theoretic
  arguments;
- exact reductions, finite-dimensional lemmas, verified certificates, and
  kernel-checked computation;
- numerical experiments, symbolic computation, and external literature for
  conjecture selection or counterexample discovery;
- new definitions, alternate coordinates, refactors, or a completely new RH
  route when the present route is unproductive; and
- parallel proof attempts or adversarial searches on genuinely independent
  subproblems.

Finite or numerical evidence is not by itself a proof of an infinite claim.
It becomes relevant proof material only through a sound Lean theorem that
connects it to the required quantified statement. External floating-point
output must not be presented as a rigorous inequality without a verified error
bound or exact replacement.

Do not weaken the intended theorem merely to obtain a compiling declaration.
In particular, a theorem conditional on RH, positivity, an unproved operator
bound, or an encoded equivalent of the missing result is not terminal progress.

## Adaptive proof methodology

Use a theorem-driven loop rather than a fixed stage-gate process:

1. Choose the sharpest unresolved statement whose proof or disproof would
   materially change the route to RH.
2. Inspect the existing definitions and theorems that touch that statement.
3. Write a Lean proof attempt quickly. Let elaboration and compiler errors
   expose the actual missing lemmas.
4. Prove only the supporting facts needed by that attempt, preferring the
   shortest reusable formulation.
5. If the statement resists proof, test it adversarially. A counterexample,
   failed constant, sign obstruction, or non-coercive direction is useful when
   it rules out the proposed mechanism.
6. Change coordinates, refactor, or abandon the route when evidence warrants
   it. No historical plan has authority over the mathematics.

Keep one principal mathematical claim in focus. Avoid producing chains of
nearby interface lemmas unless the active proof attempt actually calls for
them. Notes and design documents are optional memory aids, not deliverables.

Subagents are most useful for distinct proof attempts, source/API discovery,
or counterexample searches. Repeated independent audits of already compiled
routine algebra are usually lower value than another proof attempt.

## Validation policy

Validation should be proportional to the claim:

- During proof development, a focused `just strict <file>` is normally enough.
- Run the relevant target build when a module is integrated or its imports
  change.
- Run the full build at meaningful repository checkpoints and before a
  terminal claim, not after every small lemma.
- Inspect assumptions or dependency provenance when there is a concrete risk
  of `sorry`, a new axiom, a circular theorem, an unintended certificate, or a
  misleading statement. Do not repeat such audits mechanically when nothing
  relevant changed.
- Before claiming RH or `¬ RH`, run the full repository build, inspect the
  terminal theorem's assumptions and dependency path, and verify that the
  theorem is the canonical proposition intended here.

Use the root `Justfile` for Lean/Lake workloads so the repository's resource
guard remains in effect. Ordinary source inspection and Git commands may run
directly.

Commit and push coherent checkpoints when doing so preserves useful progress.
There is no required theorem count, audit template, documentation quota, or
commit cadence.

## Current mathematical frontier

The current production route has established restricted positivity for
Bombieri tests whose positive support ratio is at most two. The immediate
adjacent-window problem is the same-seed factor-two family

```text
Re F(g + c D₂g) = (1 + |c|²) D(g) + 2 Re(c Z(g)),
```

where

```text
D(g) = Re F(g),
Z(g) = factorTwoGlobalCrossSymbol(g).
```

For a centered ratio-two seed, the exact endpoint coordinates now have the
form

```text
D(g) = A Q,
Z(g) = A (P + i J),
A = log 2 / 2 > 0.
```

Thus universal positivity of this two-bump family is exactly

```text
normSq (P + i J) ≤ Q²,
```

and strict reversal is exactly a negative member of the family. In the current
Lean API these quantities are represented by
`factorTwoEndpointChannelCleanSum` and
`factorTwoEndpointChannelCoordinate`.

Reflection parity splits the scalar pencil into even--odd and odd--even
blocks. The sharp total criterion adds the two complex block coordinates
before taking `normSq`. Proving the two block-radius bounds separately is a
valid sufficient route, but it is stronger than necessary; failure of one
block alone is not a production counterexample because the other block may
compensate.

A promising positive mechanism is a phase-uniform coercivity or Schur estimate
for the complete coupled form

```text
Q + a P + b J,    a² + b² ≤ 1,
```

retaining the endpoint, smooth-kernel, residual, and prime terms together. A
promising falsification mechanism is an admissible centered seed for which the
total radius inequality is strictly reversed. These are current opportunities,
not mandatory routes.

Even if the same-seed factor-two inequality is proved, arbitrary support still
requires a valid local-to-global argument, such as a controlled chain of
logarithmic windows or another all-support mechanism. Conversely, a strict
negative production witness becomes a falsification only after its
admissibility and the transport to `¬ RiemannHypothesis` are proved in Lean.

The agent may bypass this frontier entirely if a more direct proof or
falsification route becomes credible.

## Research conduct

- State uncertainty plainly and distinguish a compiled theorem from a
  numerical observation or plausible route.
- Preserve unrelated worktree changes.
- Prefer proving or refuting a substantive statement over polishing process
  artifacts.
- When a route repeatedly reproduces the same missing lemma, change the
  mathematical mechanism rather than renaming the obstruction.
- Keep the objective precise and the methodology flexible.
