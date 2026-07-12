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

## `af4e69a` — Yoshida diagonal moment enclosures

1. **Theorem added.**  The zero-hypothesis theorem
   `diagonalTargetEnclosures_from_certificate` encloses each actual diagonal
   moment `D₁, …, D₁₀` in the rational target box consumed by the interval
   Schur certificate.
2. **Gate hypothesis eliminated.**  Gate 0's diagonal target-enclosure
   proposition is discharged.  The proof connects the exact accelerated
   diagonal identity to a rational finite head, a sharp certified infinite
   tail, and proof-producing kernel checkpoints; it is not a numerical
   assumption.
3. **Assumptions remaining.**  No analytic hypothesis remains in the ten-mode
   diagonal package.  Gate 0 still requires the final composition theorem to
   be imported by the project umbrella and a fresh full build and dependency
   audit.  Gates 1–4 remain open.
4. **Next make-or-break lemma.**  Compose the exact clipped/moment bridge,
   `sineTargetEnclosures_from_series192`, and the new diagonal package through
   `clippedOddFullGram_posDef_of_bridge_and_target_enclosures` to prove the
   actual `clippedOddFullGram.PosDef` with no parameters.
5. **Viability evidence.**  Strict compilation produced a 2.1 MiB proof
   artifact.  All 92 exact chunk claims covering 23,542 terms and all ten
   coarse target claims reduce in the kernel.  Independent exact rational
   arithmetic reproduced every checkpoint, direct integration of the original
   diagonal integrand agreed with the accelerated route, and the public axiom
   audit found only `propext`, `Classical.choice`, and `Quot.sound`.

## `1ea80bc` — Gate 0 closed

1. **Theorem added.**  The zero-hypothesis theorem
   `YoshidaOddGramPosDef.clippedOddFullGram_posDef` proves
   `clippedOddFullGram.PosDef`, where `clippedOddFullGram` is the actual clipped
   critical-form Gram on `Fin 10` and odd frequencies `1, …, 10`.
2. **Gate hypothesis eliminated.**  Every Gate 0 hypothesis is discharged:
   the exact clipped/moment bridge, all sine and diagonal target enclosures,
   and all ten interval Schur pivots are unconditional proof terms.  Gate 0 is
   passed; a larger finite matrix is not an allowed substitute for Gate 1.
3. **Assumptions remaining.**  Gate 1 still requires positivity on the complete
   infinite-dimensional restricted-support space.  In particular, the current
   theorem does not yet control the full odd/even Fourier tail or the finite-to-
   tail cross terms for arbitrary admissible restricted-support data.  Gates
   2–4 remain blocked by Gate 1.
4. **Next make-or-break lemma.**  Establish an exact representation bridge
   from arbitrary restricted-support clipped test functions to the parity-
   split circle/Fourier Hilbert space on which a finite low block, a coercive
   infinite tail, and their cross terms can be combined by a Schur or operator
   argument.  If that bridge or the needed tail coercivity is false, produce a
   verified obstruction rather than increasing the truncation.
5. **Viability evidence.**  The canonical full project build succeeds with
   3,784 jobs; the final module and umbrella build cleanly; the top theorem has
   no explicit or implicit hypotheses and uses only `propext`,
   `Classical.choice`, and `Quot.sound`.  A 117-module recursive dependency
   audit found no import cycle, proof bypass, or logical dependence of the
   analytic enclosures on positivity.  The preserved root legacy inventory is
   still exactly 159 untracked Lean files.

## `8672247` — Clipped-to-circle Fourier coordinate bridge

1. **Theorem added.**  Every `YoshidaClippedSmooth a` function now has a
   linear coordinate in `CircleL2 (T := 2*a)` with exact centered Fourier
   coefficients and Fourier-series convergence.  Clipped exponentials and all
   normalized odd/even low modes map to the matching circle modes with no sign
   or scale change.  Every clipped function receives the canonical even
   200-mode-plus-tail and odd 10-mode-plus-tail `L²` decomposition.
2. **Gate hypothesis eliminated.**  Gate 1 no longer lacks a rigorous map from
   the clipped carrier to the existing parity/Fourier decomposition.  This is
   a coordinate theorem only: it deliberately does not assume or claim that
   the critical form is bounded on ordinary `L²`.
3. **Assumptions remaining.**  Bare `YoshidaClippedSmooth` is larger than
   Yoshida's source space because endpoint jets may fail to match.  A source-
   faithful periodic clipped core, explicit clipped residuals, genuine odd
   and even tail coercivity, low/high coupling bounds, form-norm completion,
   and the even finite block remain open.
4. **Next make-or-break lemma.**  Define the clipped periodic-core submodule
   and its odd/even tail comaps, prove supported critical pullbacks and finite-
   low residuals lie in it, then prove `odd_K10_coercive` with the exact source
   constant `38/25`.
5. **Viability evidence.**  All thirteen public bridge theorems strict-compile
   and use only `propext`, `Classical.choice`, and `Quot.sound`; the full build
   succeeds with 3,785 jobs.  The production module explicitly excludes
   injectivity, form continuity, periodic-core membership, and surjectivity
   onto arbitrary closed `L²` tails, preventing those facts from being smuggled
   through the coordinate construction.

## Gate 1 bounded falsification lane

1. **Result.**  No negative direction or violation of Yoshida's printed tail
   and coupling constants was found within the fixed search caps.  A rigorous
   one-dimensional saturation model does falsify one tempting weakening:
   `(19/500)/(3/2) = 1/40 + 1/3000`, while
   `(19/500)/(38/25) = 1/40` exactly.
2. **False route eliminated.**  Odd coercivity cannot be weakened from
   `38/25` to `3/2` before the Schur/Riesz correction.  In addition, the
   unit-`L²` diagonal values grow like `log n`; hence the critical form cannot
   be extended as a bounded sesquilinear form on ordinary circle `L²`.  Gate 1
   must retain `38/25` through correction and use the form-norm completion.
3. **Assumptions remaining.**  The diagnostic eigenvalue and coupling scans
   are not certified enclosures and do not prove positivity.  The analytic
   coercivity and decay statements, especially their infinite interchanges,
   remain formal obligations.
4. **Next make-or-break lemma.**  Prove the source-faithful periodic-tail
   coercivity and the uniform odd low/high pairing decay; do not pursue an
   ordinary-`L²` bounded-form abstraction or the weakened `3/2` budget.
5. **Viability evidence.**  Reproducible scratch script
   `/tmp/gate1_falsification_lane.py` has SHA-256
   `9d0d7d52edf986ea2334d0eb9f09cc579234bd78be65959cca781b8b11728fa8`.
   It found positive truncated odd/even tail minima, Schur corrections below
   the source budgets, and coupling decay below the printed constants through
   mode `10^6`; these figures are recorded only as adversarial diagnostics.

## `0cc0913` — Faithful clipped carrier and parity splitting

1. **Theorems added.**  Yoshida's source-faithful carrier is now the submodule
   of clipped functions admitting a globally smooth, `2*a`-periodic extension;
   every clipped Fourier mode belongs to it and its odd/even tails are literal
   comaps of the circle tails.  The clipped-to-circle coordinate is injective,
   preserves the Lebesgue norm square exactly, and gives an explicit clipped
   low-mode residual.  Finally, the local critical form's odd/even and
   even/odd cross terms vanish exactly.
2. **Gate hypothesis eliminated.**  Gate 1 no longer conflates arbitrary
   interval-smooth clipped functions with Yoshida's periodic source space, no
   longer needs faithfulness of the circle coordinate as an assumption, and
   no longer needs an unproved parity-decoupling assertion when the odd and
   even coercivity estimates are recombined.
3. **Assumptions remaining.**  Neither parity tail is yet coercive in Lean.
   The odd `K(10)` estimate with constant `38/25`, the even tail estimate, both
   finite-to-tail coupling bounds, the even finite low block, the form-norm
   completion step, and the link from the final restricted-support test class
   into the periodic core all remain open.  The residual theorem constructs
   only the tail of a given clipped function and does not assert surjectivity
   onto arbitrary circle tails.
4. **Next make-or-break lemma.**  Prove the source-faithful infinite odd-tail
   coercivity at `38/25` and its uniform ten-low-mode coupling decay; in
   parallel, expose and certify the corresponding even all-mode pairing and
   tail interfaces starting at the actual post-low cutoff.
5. **Viability evidence.**  Direct warning-as-error compiles, targeted builds,
   and the canonical 3,788-job build pass.  The nine audited public endpoints
   use only `propext`, `Classical.choice`, and `Quot.sound`; forbidden-proof
   scans are clean.  The root legacy inventory remains exactly 159 untracked
   Lean files.

## `00803f0` — Exact all-mode even pairing bridge

1. **Theorem added.**  Every clipped even/even critical-form entry now has an
   exact removable-safe formula through `yoshidaIntervalExpQuotient`.  Public
   consequences cover all modes, the normalized zero mode, the canonical
   `Fin 200` low block against every tail mode, and the Hermitian reverse
   orientation.
2. **Gate hypothesis eliminated.**  Gate 1 no longer lacks an exact analytic
   target for the even finite-to-infinite coupling calculation.  The bridge
   also resolves an indexing ambiguity: the repository's `YoshidaEvenIndex`
   is zero plus modes `1, ..., 199`, so its canonical first tail mode is `200`,
   not `201`.
3. **Assumptions remaining.**  The formula is an identity, not a decay or
   positivity estimate.  No even analogue of the odd admissible-distribution,
   correlation-fold, or real-space assembly stack yet proves the source tail
   coercivity, the low/high square-sum bound, or the even finite block's
   positivity.  Infinite interchange and form-completion obligations remain.
4. **Next make-or-break lemma.**  Derive a uniform summable bound for the exact
   canonical even low/tail entries and construct the corresponding even
   real-space tail coercivity theorem; abandon the route if their certified
   constants exceed the available Schur budget.
5. **Viability evidence.**  The 288-line module strict-compiles, its targeted
   build and the canonical 3,789-job build pass, and five audited public
   endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.
   Forbidden-proof scans are clean and the root legacy inventory remains 159.
