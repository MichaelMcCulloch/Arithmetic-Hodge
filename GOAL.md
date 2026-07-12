# Arithmetic-Hodge Decisive RH Program

This is the active goal for the autonomous run. It is intentionally stable at
the program and stage-gate level; rapidly changing theorem-by-theorem status
lives in the terminal-distance audit linked under **Current directive**.

## Terminal objective

Continue autonomously in `/home/michael/Development/Arithmetic-Hodge` until the
repository contains one of the following fully verified Lean artifacts:

1. an axiom-free theorem proving the repository's canonical
   `RiemannHypothesis` statement for every required Bombieri/Weil test
   function; or
2. an explicit admissible test-function or zero witness whose verified
   properties imply `¬ RiemannHypothesis`.

Do not claim that RH is proved or falsified before one of those terminal
artifacts passes every repository gate.

Time, edit count, theorem count, and repository size are not progress metrics.
The program must continually reduce the mathematical distance to a terminal
artifact.

## What counts as decisive progress

An increment is decisive only if it does at least one of the following:

- discharges a named hypothesis of a theorem on the active terminal dependency
  path;
- upgrades a finite, conditional, or restricted statement to the next
  quantified statement required by that path;
- proves that a proposed RH route cannot work by exhibiting a verified
  obstruction or counterexample;
- produces and verifies a candidate negative Bombieri/Weil witness; or
- removes a proof-integrity risk from a theorem already on the terminal path.

Refactoring, stronger constants, larger finite matrices, duplicated APIs,
additional exploratory files, and broader literature notes are supporting
work, not decisive progress, unless a current gate explicitly requires them.

Every task must be expressible in this form before work begins:

> If this succeeds, it discharges **[specific obligation]** in **[current
> gate]**; if it fails, the failure decides **[specific route or bound]**.

## Firm-ground and loose-end policy

Advance from firm, checked ground without allowing loose ends to control the
research program.

- Close every proof obligation that blocks the active gate.
- Finish a nearly complete coherent theorem before changing routes when its
  completion has clear downstream value.
- Inventory and quarantine non-blocking experiments, superseded approaches,
  and research artifacts. Preserve them, but do not polish them on the
  critical path.
- Do not advance a theorem by replacing `sorry` with an axiom, typeclass
  bridge, circular RH-equivalent assumption, `unsafe`, `native_decide`, or any
  other proof bypass.
- The terminal theorem's complete transitive dependency closure must consist
  of structural proofs: analytic identities and estimates, algebraic or
  operator-theoretic arguments, and uniform quantified reductions that explain
  why the result holds.
- Exhaustive finite computation is not a proof ingredient for this program.
  Generated numeric tables, mode-by-mode target boxes, matrix-cell or row/block
  enumeration, pivot/Cholesky replay, and `decide +kernel` evaluation of a
  discovered certificate may be used to find conjectures or counterexamples,
  but no terminal-path theorem may import or depend on them.
- This restriction is retroactive.  Audit every theorem previously called
  firm ground through all of its imports; if its weakest lemma is computational
  rather than structural, reclassify the theorem as exploratory evidence and
  reopen the obligation.  Closed scalar arithmetic after a structural
  reduction is acceptable only when it does not encode an enumerated family
  of cases or a discovered numeric certificate.
- Preserve the 159 inventoried legacy Lean artifacts, their archive ref, and
  the separately identified untracked fallback modules byte-for-byte: do not
  edit, rename, move, stage, or delete them unless the user explicitly changes
  this directive.

Firm ground means a structural-proof dependency audit first, followed by strict
compilation, a full `lake build`, forbidden-proof and naming scans, axiom
audits, and independent review proportional to mathematical risk.

## Active stage gates

Work on the earliest unclosed gate. Later gates may receive bounded exploratory
probes only when they clarify whether the active route is viable.

### Gate 0 — Structuralize the restricted Yoshida foundation

Reopen every claimed odd/even restricted-support result whose dependency graph
passes through finite numeric certificates.  Replace the weakest such lemma by
one structural theorem that works uniformly in the Fourier dimension, for
example through the real-space correlation form, a coercive operator
decomposition, a positive integral/rank-one representation, or an exact
structural obstruction.

The deliverable is a dependency-audited theorem or falsification result with no
mode table, target enclosure family, finite Gram certificate, or enumerated
matrix inequality in its transitive imports.

### Gate 1 — Prove or refute infinite-mode restricted-support positivity

This is the first decisive mathematical gate. Prove a theorem for the complete
restricted-support space, not another truncation. The proof must assemble:

- the required parity components and Fourier-circle normalization;
- a genuinely infinite coercive-tail estimate;
- a structural treatment of the low modes that is uniform in dimension;
- a sound operator Schur-complement or equivalent infinite-space argument; and
- all cross terms, convergence statements, and closure/density steps.

The deliverable is either:

- an unconditional theorem establishing Yoshida positivity for every
  admissible test in the support-ratio-at-most-two class; or
- a formally or exactly verified obstruction showing why the proposed
  finite-plus-tail mechanism cannot establish that theorem.

If the constants or hypotheses do not close, record the precise failing
inequality or construct a counterexample to the intermediate claim. Do not
respond by merely enlarging the finite block indefinitely.

### Gate 2 — Transport restricted positivity to the Bombieri functional

Prove an exact theorem connecting the restricted Yoshida statement to the
repository's production Bombieri/Weil quadratic functional. Discharge, rather
than assume:

- normalized multiplicative dilation and logarithmic centering;
- Fourier/Mellin convention compatibility;
- admissibility and support transport;
- equality of the relevant quadratic forms; and
- every continuity, density, and limiting step used by the transport.

The result must be a quantified Bombieri positivity theorem on a precisely
stated nontrivial class, with no hidden convention or integrability boundary.

### Gate 3 — Cross or decisively characterize the all-support gap

Restricted-support positivity is not RH. Attack the all-support gap directly.
Candidate mechanisms may include support decomposition, normalized dilation,
localization, density, monotone exhaustion, or another source-backed
local-to-global principle, but each candidate must control cross terms and
preserve the exact Bombieri functional.

For each candidate mechanism:

1. state the complete theorem that would imply all-test positivity;
2. isolate its strongest genuinely new lemma;
3. try to prove that lemma before building auxiliary infrastructure; and
4. in parallel, search for a counterexample to the lemma and its quantitative
   bounds.

The gate closes only with either an all-support Bombieri positivity theorem or
a verified obstruction that eliminates the route and identifies the next
specific mechanism to test.

### Gate 4 — Terminal RH theorem or falsifying witness

Connect the all-test Bombieri/Weil result to the canonical
`RiemannHypothesis` theorem, or connect a verified negative witness to
`¬ RiemannHypothesis`. Audit the entire dependency closure and run all project
gates before making a terminal claim.

## Parallel falsification lane

Maintain a bounded adversarial lane at every gate. Its purpose is not generic
numerical experimentation; it is to kill false intermediate claims early or
produce a terminal witness.

A candidate negative witness is relevant only if it includes:

- an explicit representation accepted by Lean;
- proofs of every Bombieri/Weil admissibility condition;
- a rigorous error bound or exact evaluation of the quadratic functional;
- a strict negative inequality; and
- the theorem transporting that inequality to `¬ RiemannHypothesis`.

Numerical searches may select candidates, but they do not discharge any of
these obligations.

## Anti-drift operating rules

### Resource-safety invariant

Lean- and Lake-related workloads must use the root `Justfile`; do not spell out
or bypass its systemd wrapper:

```console
just cache
just build [target]
just lean <file> [lean-args...]
just strict <file> [lean-args...]
just guarded <other-lean-related-command> [args...]
```

These recipes run the workload in a transient user systemd scope capped at
exactly 48 GiB. The guarded runner also terminates the workload's complete
process group if either the scope's cgroup `memory.current` or the summed RSS
of the workload's descendant tree reaches 40 GiB.

- Ordinary non-Lean commands such as `git`, `rg`, and `git diff` run directly;
  they do not need or benefit from a systemd scope.
- Never launch a Lean- or Lake-related workload outside the `Justfile`
  recipes. Do not weaken, abbreviate, or silently omit the scope or guard for
  work believed to be trivial.
- Do not run multiple high-memory scopes concurrently merely because each has
  its own 48 GiB cap; protect the machine from aggregate memory pressure too.
- Propagate the `Justfile` requirement explicitly in every subagent task that
  runs Lean- or Lake-related workloads.
- If a required proof or computation reaches the cap, treat that as a design
  failure: checkpoint, reduce, or reformulate it. Do not raise or bypass the
  cap without the user's explicit permission.
- A resource-intensive validation that remains at full CPU is not evidence
  that it is safe to leave running. Monitor memory and terminate it before it
  threatens desktop responsiveness.
- The guarded recipes monitor both counters because shared or file-backed
  mappings can make process RSS materially exceed memory charged to a newly
  created cgroup; never trust the smaller counter when the two disagree.

- Keep the root agent on the strongest unresolved lemma of the active gate.
- Use subagents only for distinct bounded proofs, independent audits,
  counterexample searches, source verification, or certificate generation.
- Never idle solely because agents are running while useful critical-path work
  remains.
- Prefer a proof or disproof of the gate's hardest lemma over improvements to
  already adequate constants or infrastructure.
- Do not expand a finite certificate after its downstream inequalities close.
- Do not undertake broad refactors unless a current proof is blocked by the
  existing interface and characterization tests protect the change.
- Use primary sources when they sharpen a named obligation; do not substitute
  literature collection for proving the obligation.
- As soon as a coherent increment passes its verification gates, commit it
  before beginning the next mutable increment, staging only its intended
  files by explicit path.

After every coherent increment, record a terminal-distance audit:

1. theorem or obstruction added;
2. active-gate hypothesis eliminated;
3. assumptions still remaining;
4. exact next make-or-break lemma; and
5. evidence that the current route remains viable.

If repeated attempts merely restate the same unresolved lemma, stop generating
nearby lemmas. Produce a route audit, test the lemma adversarially, and either
change the mathematical mechanism or formalize the obstruction.

## Current directive

Gate 0 is reopened by the structural-proof requirement.  The results formerly
treated as closed at `1ea80bc` and `a038238`, together with all full-pivot,
sparse-dominance, target-enclosure, and generated block modules, are
quarantined evidence until a transitive dependency audit proves that no
computational certificate supports them.  They are not admissible premises for
the terminal theorem.

The current critical path is:

Primary-source audit fixes the endpoint obligation sharply.  The structural
``sufficiently small support'' theorems stop strictly before
`a = log 2 / 2`; published results at the endpoint return to finite spectral
or matrix computations and are therefore evidence, not admissible premises.
Suzuki's scaled real-space identity reduces the endpoint to a continuous
operator inequality on `[-1, 1]`: the fractional logarithmic energy

```text
L(w) = (1/4) integral integral |w(x)-w(y)|^2 / |x-y|
       - (1/2) integral |w(x)|^2 log(1-x^2)
```

minus the smooth kernel perturbation
`a * Re integral integral r''(a*(x-y))*w(y)*conj(w(x))` must dominate
`(log(2*pi) + EulerGamma - log(2/log 2)) * ||w||_2^2`, with
`a = log 2 / 2`, on the exact production domain.  The prime-translation term
has zero-length overlap at this endpoint.  A proof of this inequality, or a
structural counterexample to it, is the current make-or-break lemma; replacing
it by a discretized spectral calculation is not progress under this program.

1. express the production clipped quadratic form on arbitrary finite Fourier
   combinations directly through its real-space correlation or spectral
   operator, without expanding a finite matrix;
2. prove a dimension-free coercive/positive decomposition, or isolate a
   concrete structural obstruction to such a decomposition;
3. derive odd, even, tail, coupling, and parity results as restrictions or
   Schur complements of that one operator theorem rather than from certified
   low blocks; and
4. audit the resulting theorem's complete import closure before it is restored
   to firm ground and advanced toward the Bombieri/Weil all-support gate.

The live theorem-by-theorem position and next make-or-break lemma are recorded
in `docs/research/rh-terminal-distance-audit-2026-07-11.md`; that audit, rather
than this stable program, carries rapidly changing commit-level status.

No restricted-support or finite-dimensional result is terminal. The program
exists to force each such result into the next quantified theorem—or to expose
precisely why that transition fails—until RH is proved or falsified.
