# Arithmetic-Hodge Decisive RH Program

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
- Preserve the 159 inventoried legacy Lean artifacts and their archive ref.

Firm ground means strict compilation, a full `lake build`, forbidden-proof and
naming scans, dependency and axiom audits, and independent review proportional
to mathematical risk.

## Active stage gates

Work on the earliest unclosed gate. Later gates may receive bounded exploratory
probes only when they clarify whether the active route is viable.

### Gate 0 — Close the current finite Yoshida certificate

Complete the current ten-mode odd-block work as one checked artifact:

- exact accelerated diagonal moment identity;
- sound rational finite-head evaluation and certified analytic tail;
- all ten diagonal and sine target enclosures;
- unconditional positive definiteness of the actual ten-mode odd Gram block;
- full build, scan, dependency, axiom, and independent-review evidence.

Once this gate closes, stop increasing the matrix dimension, tightening its
constants, or reorganizing its certificate unless Gate 1 proves that a
specific refinement is necessary.

### Gate 1 — Prove or refute infinite-mode restricted-support positivity

This is the first decisive mathematical gate. Prove a theorem for the complete
restricted-support space, not another truncation. The proof must assemble:

- the required parity components and Fourier-circle normalization;
- a genuinely infinite coercive-tail estimate;
- the certified finite low-mode block;
- a sound Schur-complement or equivalent finite-to-infinite argument; and
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
- Commit each coherent verified increment, staging only its intended files.

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

Gate 0 closed at `1ea80bc`; treat it as immutable firm ground and do not reopen
or enlarge its ten-mode certificate without a specific Gate 1 dependency.
Gate 1 is active.  The next major success criterion is not a larger finite
matrix: it is a Lean theorem that converts the certified low blocks, genuinely
infinite coercive tails, and controlled couplings into positivity for the
entire restricted-support space.

The current Gate 1 critical path is:

1. use the now-proved homogeneous `38/25` coercivity and bundled positive
   Hermitian form on the actual infinite tenth odd tail to prove that every
   production low/tail pairing is form-norm bounded; then combine its Riesz
   corrections with the closed coupling budget and ten-mode Gram reserve;
2. use the now-unconditional even clipped-form-to-moment bridge, the certified
   `D_0`, `D_1`, and `S_1` boxes, and reusable accelerated/checkpointed
   enclosures to finish the remaining canonical `Fin 200` scalar boxes and
   Schur pivots; in parallel close the exceptional coupling estimate and
   `102/25` infinite even-tail coercivity; and
3. assemble both parities and every closure/density step into one quantified
   restricted-support positivity theorem, or formalize the exact obstruction
   if any required inequality or extension fails.

The live theorem-by-theorem position and next make-or-break lemma are recorded
in `docs/research/rh-terminal-distance-audit-2026-07-11.md`; that audit, rather
than this stable program, carries rapidly changing commit-level status.

No restricted-support or finite-dimensional result is terminal. The program
exists to force each such result into the next quantified theorem—or to expose
precisely why that transition fails—until RH is proved or falsified.
