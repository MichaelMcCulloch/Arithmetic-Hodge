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

The high-frequency instance of that positive mechanism and its decomposition
hypotheses are now compiled. `endpoint_tail_phase_uniform` proves the complete
phase-disk inequality when the even component lies in the tail above the first
200 even modes and the odd component lies in the tail above the first 10 odd
modes, provided both tails are pointwise real and have zero endpoint traces.
Its even lower bound comes from a genuine infinite Schur estimate, not a
retained numerical cutoff.

The standard 200-mode even split did not itself preserve the required
endpoint trace. The endpoint-adapted basis now replaces each retained even
mode by that mode minus its endpoint-trace multiple of frequency `200`.
Frequency `200` remains in the cutoff-`199` tail, so this change preserves the
`Fin 200` low dimension while forcing every adapted low mode and the resulting
tail to vanish at both endpoints. Pointwise realification is proved to
preserve both even and odd Fourier-tail submodules. The compiled decomposition
theorems therefore return real `Fin 200` and `Fin 10` coefficients, exact
low-plus-tail equalities, and real endpoint-zero tails to which the tail phase
theorem applies. This still does not establish the canonical same-seed pencil.

The smallest explicit gap on this route is now the concrete finite-low and
low-tail Schur certificate. After the exact decompositions `e = eL + eT` and
`o = oL + oT`, write the phase form as a low block `L`, a tail block `T`, and
twice a mixed block `C`. The tail theorem gives `0 ≤ T`; it remains to prove
`0 ≤ L` and `C ^ 2 ≤ L * T` for each opposite-parity reflection channel
(with the appropriate alternating-coordinate sign change). The existing
`210 x 210` matrix API is now fully instantiated on the endpoint-adapted
production basis. The clean blocks are obtained without a new singular-form
bilinearity assumption: the public clipped critical sesquilinear form expands
the finite syntheses, and the endpoint-clean bridge identifies its real
diagonal with the clean quadratic. Together with the two symmetric
perturbation blocks and the alternating block, this gives an assumption-free
exact representation of the complete finite-low phase by one concrete
matrix for every disk phase. An inverse-free scalar Schur reduction further
eliminates the second disk coordinate: it is enough, for every `a² ≤ 1`, to
prove nonnegativity of the even and odd diagonal pencils and

```text
(1 - a²) X(e,o)² ≤ 4 Eₐ(e) Oₐ(o).
```

This criterion remains sound when a diagonal pencil is only semidefinite.
There is also a parameter-free sufficient certificate.  The concrete
`420 x 420` real Toeplitz matrix has now been defined and proved to control
every phase in the disk.  An exact unnormalized Hadamard/parity congruence
reduces its positive semidefiniteness to the following two real `210 x 210`
split matrices:

```text
[[Q_E + P_E, J/2], [Jᵀ/2, Q_O - P_O]],
[[Q_E - P_E, J/2], [Jᵀ/2, Q_O + P_O]].
```

All entries needed by either finite certificate now have exact
enclosure-ready formulas.  The adapted even clean block is a four-term
pullback of the canonical Section-6 moment Gram through frequency `200`; the
odd clean block is already unconditionally positive definite by its existing
interval certificate; the canonical symmetric perturbation blocks have
explicit zero, diagonal, and off-diagonal trigonometric correlation formulas;
and the alternating block has an explicit three-branch formula followed by
the endpoint-adaptation subtraction.  No floating-point bound is asserted by
these identities.

A deterministic external reconstruction currently finds no finite-low
counterexample.  It reports a worst scalar-Schur normalized ratio about
`0.959645` (roughly four percent below one) and a minimum full phase-matrix
eigenvalue about `3.53e-4`.  The stronger static split certificate is also
numerically positive, but only by about `2.51e-7` in its thinner split, so it
is substantially more delicate to certify.  These are discovery results,
not Lean inequalities.  The perturbation entry compression is now exact:
all three blocks reduce to four one-dimensional frequency families (a
symmetric sine moment, a symmetric affine-cosine moment, an antisymmetric
one-minus-cosine moment, and an antisymmetric affine-sine moment).  The
four families now have exact dyadic Cauchy-series representations proved by
dominated convergence from the genuine singular integrals, including their
retained prime atoms.  The affine-cosine identity also covers the zero mode;
the other three vanish there and are stated on positive canonical modes.
The clean sine moments at frequencies `191` through `200` now have
kernel-checked rational boxes of width at most `10^-9`, including the extra
`S_200` introduced by endpoint adaptation.  The retained `p = 3` sine and
cosine phases at every frequency `0` through `200` also have exact rational
Taylor enclosures of width at most `10^-10`, after a kernel-checked
quarter-turn reduction.  The remaining finite obligation is to prove
sufficiently sharp rational enclosures for the dyadic parts of all four
perturbation families and the still-unboxed clean moments through frequency
`200`, then replay an exact certificate.  A generic robust-congruence theorem
is now compiled: a
rational invertible change of basis, a uniform entrywise error bound around a
rational center, and kernel-checked weighted diagonal dominance imply
positive definiteness of the true matrix.  This avoids the width growth of a
raw 210-stage interval elimination and makes the two fixed static splits the
shortest current formal route.  Numerical conditioning still calls for
scalar moment boxes around `1e-9` or tighter.  The healthier scalar-Schur
margin remains a fallback if the static certificate cannot retain its thin
reserve under rigorous enclosure inflation.

For the full-profile assembly, the clean part of the low-tail mixed term is
now exactly the real clipped critical pairing divided by `yoshidaA`, obtained
from the diagonal endpoint-clean bridge and Hermitian sesquilinearity. The
remaining assembly obligation is still the phase-dependent low-tail Schur
bound, including the symmetric-perturbation and alternating mixed terms.

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
