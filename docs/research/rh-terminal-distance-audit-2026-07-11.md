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

## `dad1983` — Canonical even-tail reductions

1. **Theorems added.**  Pointwise evenness now proves the polar energy is
   nonnegative and discharges the Section 6 polar lower bound outright.  A
   homogeneous equation-(6.7) inequality implies the exact even coercivity
   bound `(102/25) * ‖f‖²_L2 ≤ B(f,f)`, and the concrete canonical `200+k`
   low/tail pairings satisfy the full `51/25000` source budget whenever the
   source pointwise (6.26) decay holds.
2. **Gate hypothesis eliminated.**  The even lane no longer carries a polar
   estimate as an analytic premise, and its infinite coupling sum, cutoff,
   and correction arithmetic have been reduced to the single concrete
   pointwise decay statement without enlarging the low block.
3. **Assumptions remaining.**  The homogeneous analytic equation (6.7) and
   pointwise (6.26) estimate are still premises; the module does not infer
   either from its exact Laplace formula.  Even finite-block positivity and
   the final form-completion/Schur assembly also remain open.
4. **Next make-or-break lemma.**  Prove or refute (6.26) for the committed
   removable-safe even pairing formula, while the parallel coercivity lane
   derives homogeneous (6.7) on the actual periodic even tail.
5. **Viability evidence.**  Direct strict compilation, the targeted build,
   and the canonical 3,790-job build pass.  Five audited public endpoints use
   only `propext`, `Classical.choice`, and `Quot.sound`; the forbidden-proof
   scan is clean and the root legacy count remains 159.

## `2cc297f` — Odd coupling reduced to a scalar high-moment window

1. **Theorems added.**  Every actual clipped odd high/low entry is identified
   with its exact off-diagonal moment formula.  The certified first-ten sine
   boxes, together with the single uniform scalar window
   `-79/50 ≤ S_n ≤ -31/20` for `n ≥ 11`, imply Yoshida's concrete (6.18)
   bound `(19/50)/n²` and the full infinite coupling budget `19/500` for each
   of the ten low modes.
2. **Gate hypothesis eliminated.**  The odd finite-to-tail correction no
   longer depends on a mode-pairing identity, an abstract summability premise,
   or ten separate decay arguments.  Its entire remaining analytic content is
   the stated two-sided high sine-moment bound.
3. **Assumptions remaining.**  `YoshidaOddHighSineBounds` is not yet proved.
   Odd-tail coercivity at `38/25`, homogeneous equation (6.7), form-completion
   assembly, and the even finite block remain open.  The scalar reduction does
   not by itself establish any form boundedness.
4. **Next make-or-break lemma.**  Prove the uniform high sine-moment window
   from the exact Cauchy series by a monotone sum/integral enclosure, or produce
   a certified counterexample.  In parallel, finish the homogeneous odd-tail
   coercivity estimate.
5. **Viability evidence.**  Direct warning-as-error compilation, the targeted
   3,619-job build, and the canonical 3,791-job build pass.  Four audited public
   endpoints use only `propext`, `Classical.choice`, and `Quot.sound`; the
   forbidden-proof scan is clean and the root legacy count remains 159.

## `208f6c6` — Restricted support bridged to the periodic core

1. **Theorems added.**  A locally finite integer-translate periodization of a
   globally smooth critical crop is constructed in Lean and shown to lie in
   the clipped Yoshida periodic core.  After Bombieri normalization, every
   test function supported in `[l,r]` with `r / l ≤ 2` maps into that fixed
   carrier.  Subtracting either canonical finite low projection leaves a
   residual in the same core.
2. **Gate hypothesis eliminated.**  Gate 1 no longer assumes that the final
   restricted-support Bombieri class belongs to the periodic source space on
   which the odd/even spectral decomposition is carried out.  The low/tail
   split is now closed inside that source space rather than merely asserted
   for an unrelated circle function.
3. **Assumptions remaining.**  Core membership alone proves neither
   coercivity nor positivity.  Odd-tail coercivity at `38/25`, the high
   sine-moment window needed for odd coupling, homogeneous even coercivity,
   even pointwise coupling decay, even finite-block positivity, and the final
   completed-form Schur assembly remain open.
4. **Next make-or-break lemma.**  Promote the exact infinite critical-sampling
   theorem and connect its paired positive-frequency estimate to the committed
   odd weighted-tail functional; this is the shortest current route to the
   actual infinite `K(10)` coercivity bound.
5. **Viability evidence.**  The 282-line bridge warning-as-error compiles, all
   seven audited public endpoints use only `propext`, `Classical.choice`, and
   `Quot.sound`, and the canonical 3,792-job build passes.  The forbidden-proof
   scan is clean and the root legacy count remains exactly 159.

## `67bae28` — Exact infinite critical-sample expansion

1. **Theorems added.**  Every clipped smooth function's critical sample is an
   exact unordered sum over all centered Fourier modes, with each coefficient
   multiplied by the removable-safe Section 6 interval-exponential quotient.
   The proof realizes one fixed sample as a bounded circle-`L²` Riesz
   functional and applies it to the genuine Fourier `HasSum`.
2. **Gate hypothesis eliminated.**  The odd-tail analytic lane no longer needs
   to assume an infinite mode expansion or interchange a conditionally
   presented formal series with critical evaluation.  Resonant modes are also
   covered by the same theorem rather than excluded by division.
3. **Assumptions remaining.**  This is pointwise continuity of one critical
   sample, not boundedness of the full Yoshida form.  The paired odd estimate
   must still be connected to the committed weighted-tail energy and
   integrated against the Section 6 measure.  Both parity coercivity bounds,
   both coupling estimates, even finite-block positivity, and completed-form
   assembly remain open.
4. **Next make-or-break lemma.**  Pair the positive and negative frequencies
   for an odd periodic-core tail, bound the resulting sample by the existing
   `weightedTail 10` quantity, and integrate that exact bound to obtain—or
   refute—the source constant `38/25`.
5. **Viability evidence.**  The 203-line module warning-as-error compiles, its
   target build passes, all four audited public endpoints use only `propext`,
   `Classical.choice`, and `Quot.sound`, and the canonical 3,793-job build
   passes.  The forbidden-proof scan is clean and the root legacy count
   remains exactly 159.

## `6089f45` — Corrected full even interval-certificate interface

1. **Theorems added.**  All `200 × 200` even moment-model entries, including
   the separately normalized zero mode, now have exact rational-coefficient
   formulas using only `1 / π`, `1 / sqrt 2`, and the shared sine and diagonal
   moments.  Sound rational interval evaluation feeds the complete `Fin 200`
   pivot order into the existing Schur checker.  A symmetric outward inflation
   incorporates an arbitrary entrywise perturbation, with the source
   correction radius fixed as `1/2000`.
2. **Gate hypothesis eliminated.**  The even finite-block lane no longer lacks
   a formal target connecting scalar moment enclosures and an entrywise
   low/high correction budget to positive definiteness of the actual-sized
   matrix.  No finite truncation larger or smaller than Yoshida's canonical
   zero-plus-`1..199` block is substituted.
3. **Assumptions remaining.**  The production file intentionally contains no
   invented 200-mode numerical payload.  It still needs certified boxes for
   `S_1,...,S_199` and `D_0,...,D_199`, a kernel-positive elimination trace
   after `1/2000` inflation, and the analytic clipped-form/moment bridge.
   Tail coercivity and the remaining analytic coupling bridges are separate
   open obligations.
4. **Next make-or-break lemma.**  Generate deterministic rational moment
   targets from the committed series enclosures, evaluate all 200 inflated
   pivots, and stop immediately if any interval crosses zero; a successful
   trace must then be replayed with `decide +kernel`.
5. **Viability evidence.**  The 400-line module warning-as-error compiles, its
   targeted build and the canonical 3,794-job build pass, and seven audited
   public endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.
   The forbidden-proof scan is clean and the root legacy count remains 159.

## `3b96277` — Even moment targets and checkpoint scaling

1. **Theorems added.**  Exact rational target boxes now cover the canonical
   sine moments `S_1,...,S_199` and diagonal moments `D_0,...,D_199`.  With
   the source `1/2000` entrywise inflation, the first ten and first twenty-five
   Schur pivots are kernel-positive.  The full pivot order is reducible and
   generic pivot certificates can be split and recombined at named
   checkpoints (`6496b75`, `dfa1e60`).
2. **Gate uncertainty eliminated.**  The actual-sized target matrix is no
   longer merely a floating-point sketch: its leading 25 elimination stages
   replay exactly in Lean.  The experiment also falsified a monolithic replay
   as the production format, without changing the canonical 200-mode block.
3. **Assumptions remaining.**  The rational boxes are candidate witnesses,
   not analytic enclosure theorems.  The remaining 175 pivots, checkpoint
   matrices, `D_0` and all other moment containments, and the clipped-form to
   moment-model bridge remain open.
4. **Next make-or-break lemma.**  Prove the zero-mode diagonal enclosure and
   emit a normalized 25-pivot checkpoint, then continue the exact elimination
   in independently cached stages rather than recomputing the prefix.
5. **Viability evidence.**  The 461-line target module strict-compiles; its
   3,589-job target build completes and both pivot theorems use only `propext`,
   `Classical.choice`, and `Quot.sound`.  The 25-pivot replay takes about
   36--44 seconds.  A 50-pivot monolith was stopped after 7.5 minutes at
   roughly 37 GB RSS; the root legacy count remains 159.

## `22d283e` — Even coupling reduced to two source bridges

1. **Theorems added.**  The rational, infinite-geometric, and digamma pieces
   of the printed even formula (6.25) now satisfy the full `C₂/m` estimate for
   every canonical low/high pair.  The zero row carries the required
   `1/sqrt 2` normalization, the first row keeps a sharp `1/12` remainder,
   and rows `n ≥ 2` close with the source's `1/10` consequence.  An exact
   certificate proves `C₂² ≤ 10149/25000`, yielding the squared premise
   consumed verbatim by `YoshidaEvenTailReduction`.
2. **Gate hypothesis eliminated.**  Once actual pairings are identified with
   (6.25) and the exceptional digamma remainder is supplied, no further
   infinite summation, constant arithmetic, exceptional-index case, or
   coupling-budget premise remains.
3. **Assumptions remaining.**  `ActualEvenPairingEquation6_25` and
   `SharpDigammaImagRemainder5_11` are explicit unproved interfaces.  The
   latter is stronger than the literal simplified source consequence: source
   (5.11) gives `1/12` relative to `log s - 1/(2s)`, but only `1/10` after the
   asymptotic imaginary main term used here.  A sharper direct `n=1`
   certificate or cancellation is therefore still required.
4. **Next make-or-break lemma.**  Derive the actual (6.25) equality from the
   removable-safe Laplace formula and prove the `n=1` digamma estimate
   directly; the already sufficient `1/10` theorem should be used for every
   other positive mode.
5. **Viability evidence.**  The 1,208-line module strict-compiles and its
   3,554-job target build passes.  Twenty-two public endpoints were audited
   with only `propext`, `Classical.choice`, and `Quot.sound`; independent
   formula, indexing, normalization, and downstream-composition review found
   no hidden premise or semantic defect.  Forbidden-proof scans are clean.

## `2327ad3` — Odd low/high coupling closed unconditionally

1. **Theorems added.**  For every `n ≥ 11`, the exact Yoshida sine moment now
   satisfies `-79/50 ≤ S_n ≤ -31/20`.  The proof bounds the complete
   quarter-shifted Cauchy sum by a trapezoidal integral with split `M=2n`,
   proves the total remainder is at most `7/5000`, and controls the polar and
   dyadic corrections.  Consequently every actual clipped odd low/high entry
   has the source square decay and each of the ten full infinite coupling
   energies is at most `19/500`, with no premise.
2. **Gate hypothesis eliminated.**  The scalar `YoshidaOddHighSineBounds`
   interface introduced in `2cc297f` is completely discharged, closing the
   odd finite-to-infinite coupling lane rather than merely reducing it.
3. **Assumptions remaining.**  Odd-tail coercivity still requires the weighted
   digamma high-frequency lower estimate and final critical-form assembly.
   The low digamma integral certificate and the completed-form Schur/Riesz
   recombination remain separate obligations.  This theorem alone does not
   assert full restricted-support positivity.
4. **Next make-or-break lemma.**  Finish the certified low digamma half-integral
   and the high-frequency digamma lower estimate, then combine those losses
   with the now-unconditional `19/500` coupling budget and the positive odd
   low block.
5. **Viability evidence.**  The 880-line analytic module and 35-line closure
   module strict-compile; targeted builds pass.  All audited endpoints use
   only `propext`, `Classical.choice`, and `Quot.sound`.  Independent review
   checked the trapezoidal direction, constants, terminal arithmetic, and
   direct inhabitation of the downstream premise; forbidden scans are clean.
   The canonical integration build at `2327ad3` subsequently passed all 3,800
   jobs; the expensive diagonal enclosure was compiled once, in 818 seconds.

## `b0fb4c3` — Odd digamma loss and global split closed

1. **Theorems added.**  A kernel-checked 1,024-cell rational upper Riemann
   certificate proves the source half-integral bound `2773/1000` for the
   negative quarter-line digamma kernel.  It discharges the actual `N = 10`
   low-digamma loss.  A separate global indicator split proves that unit
   spectral mass, the exact high central-energy estimate, and that low loss
   imply `ClippedSection6DigammaLowerEstimate`; the specialized wrapper
   `oddTenTail_clippedSection6DigammaLowerEstimate` contains no numerical or
   high-frequency premise.
2. **Gate hypothesis eliminated.**  The low digamma half-integral, its
   interpretation as a weighted loss, the monotonic high-frequency lower
   bound, and the complete measure-theoretic assembly of Yoshida (6.4)--(6.7)
   are all proof terms.  The odd coercivity lane no longer assumes an
   equation-(6.7) digamma inequality.
3. **Assumptions remaining.**  For arbitrary periodic odd-tail data, the
   wrapper still exposes integrability of the spectral norm square,
   integrability after the digamma weight, and the normalized Parseval
   identity.  The polar lower estimate and the final archimedean/form
   composition also remain before `38/25` coercivity is unconditional.
4. **Next make-or-break lemma.**  Use pointwise oddness and periodic endpoint
   cancellation to prove quadratic decay of the clipped Fourier transform;
   derive both weighted spectral integrability and exact Plancherel for every
   periodic odd tail.  If that regularity does not follow from the current
   carrier, isolate the missing trace condition instead of assuming it.
5. **Viability evidence.**  The exact rational replay, both analytic modules,
   the composed split, and the umbrella strict-compile.  The targeted build
   passes all 8,307 jobs.  Six audited endpoints use only `propext`,
   `Classical.choice`, and `Quot.sound`; forbidden scans are clean.  Independent
   review checked every cast, the series direction, all grid cells, evenness,
   interval orientation, the three indicator cases, and the `1/(2*pi)`
   normalization.  An independent numerical sanity check found certificate
   value about `2.772105475`, below `2.773` by about `0.000894525`.

## `2385f22` — Clipped even correlations bridged to the moment model

1. **Theorems added.**  The normalized positive cosine modes and separately
   normalized zero mode now have exact one-sided correlations in every
   zero/positive, positive/zero, diagonal, and off-diagonal case.  Their
   removable admissible-distribution integrands agree almost everywhere with
   the production sine and diagonal moment expressions.  Hence
   `clippedEvenAdmissibleRealSpaceGram_eq_evenMomentGram` holds for all natural
   frequency pairs, and one explicit distribution bridge implies the
   production `ClippedEvenFullMomentBridge` on `Fin 200`.
2. **Gate hypothesis eliminated.**  No cosine normalization, zero-mode
   factor, correlation integral, removable endpoint, or scalar moment algebra
   remains between an admissible real-space assembly and `evenMomentGram`.
   The even finite-block bridge is no longer a collection of unchecked
   formula cases.
3. **Assumptions remaining.**  The named proposition
   `ClippedEvenFullAdmissibleDistributionBridge` still packages the equality
   of each production clipped critical pairing with its exact real-space
   admissible-distribution value.  It is broad but explicit: the full
   spectral/digamma/polar distribution assembly for all 40,000 entries.
   Analytic moment containments, remaining Schur checkpoints, and even-tail
   coercivity are also open.
4. **Next make-or-break lemma.**  Prove the production distribution bridge by
   connecting `clippedEvenFullGram` to the already formalized Cauchy/digamma
   distribution and the unified correlations.  Keep this separate from the
   numerical moment certificate so a failure identifies an analytic, not
   matrix-arithmetic, obstruction.
5. **Viability evidence.**  The 868-line module strict-compiles, its 3,596-job
   target build and umbrella compile pass, and audited endpoints use only
   `propext`, `Classical.choice`, and `Quot.sound`.  Forbidden and diff scans
   are clean.  Independent review checked every normalization, sign, factor,
   branch, and null-endpoint argument; independent numerical evaluations of
   every correlation/moment branch agreed to floating-point precision.  The
   root legacy inventory remains exactly 159 files.

## `d87709c` — Odd polar loss and coercivity assembly closed

1. **Theorems added.**  Pointwise oddness identifies the negative clipped
   polar sample with the hyperbolic-sine functional.  Cauchy--Schwarz on the
   clipped interval then proves the exact lower bound
   `-(1 / sqrt 2 - log 2)` for unit interval energy.  Composing this with the
   certified digamma split and archimedean bridge gives the source threshold
   `38/25` for every normalized tenth odd-tail vector satisfying the explicit
   spectral regularity and Parseval inputs.
2. **Gate hypothesis eliminated.**  The polar term, its sign, the factor two
   from paired samples, the identity
   `2 * (sinh yoshidaA - yoshidaA) = 1 / sqrt 2 - log 2`, and the final
   Section 6 numerical substitution are now proof terms.  No separate polar
   estimate or final coercivity-arithmetic premise remains on the odd lane.
3. **Assumptions remaining.**  The normalized theorem still exposes
   pointwise oddness, integrability of the spectral norm square, integrability
   after the digamma weight, and exact unit spectral mass.  Homogeneity and
   completed-form recombination are still needed after those analytic facts
   are discharged.
4. **Next make-or-break lemma.**  Derive parity, both integrability statements,
   and exact Parseval mass directly from periodic-core odd-tail membership and
   unit interval energy, then instantiate the assembled `38/25` theorem with
   no auxiliary analytic premise.
5. **Viability evidence.**  Both new modules strict-compile, the targeted
   8,310-job build and umbrella compile pass, and the six audited endpoints
   use only `propext`, `Classical.choice`, and `Quot.sound`.  Forbidden and
   diff scans are clean.  Independent review verified the Laplace sign,
   odd-pair extraction, restricted-measure Cauchy normalization, exact
   hyperbolic identity, and final inequality direction; the root legacy count
   remains 159.

## `43ea136` — Even zero diagonal moment certified

1. **Theorems added.**  The production zero-mode diagonal moment now lies in
   its exact target box `[18338/100000, 18339/100000]`.  The proof derives the
   `n = 0` accelerated identity, bounds Euler's constant and `log pi` at the
   required precision, replays four exact 256-term rational chunks through
   index 1023, and bounds the analytic tail beginning at 1024.
2. **Gate hypothesis eliminated.**  `D_0` is no longer a candidate numerical
   target: its actual analytic moment inhabits the box consumed by the
   200-mode interval matrix.  The constant term, geometric correction, head,
   and tail are all checked in Lean.
3. **Assumptions remaining.**  The positive diagonal boxes `D_1,...,D_199`,
   all sine-moment boxes `S_1,...,S_199`, and the remaining exact Schur
   checkpoints are still open.  This certificate does not address the
   production distribution bridge or even-tail coercivity.
4. **Next make-or-break lemma.**  Reuse the accelerated enclosure architecture
   for `D_1`, then split the remaining positive diagonal indices into cached
   certificate batches while separately beginning the sine-moment boxes.
5. **Viability evidence.**  Independent review checked the integrand sign,
   `k = 0` cancellation, accelerated identity, constant-bound directions, and
   the gap-free `1..1023` plus `1024..` partition.  Direct warning-as-error,
   the 3,625-job target, and the umbrella compile pass; both public endpoints
   use only `propext`, `Classical.choice`, and `Quot.sound`.  Numerical sanity
   gives approximately `0.183382657594389`, strictly inside the target box.

## `7a12a2d` — Normalized odd-tail coercivity closed

1. **Theorems added.**  Every clipped smooth carrier has integrable critical
   norm square and digamma-weighted norm square.  Periodic tenth odd-tail
   membership gives genuine pointwise oddness, endpoint cancellation and
   continuity, while autocorrelation Fourier inversion proves exact spectral
   mass equals interval energy.  Consequently every unit-energy tenth odd-tail
   vector satisfies the production clipped-form lower bound `38/25` with no
   auxiliary analytic premise.
2. **Gate hypothesis eliminated.**  The four exposed assumptions of
   `d87709c`—pointwise parity, unweighted integrability, digamma-weighted
   integrability, and unit Parseval mass—are all discharged from the actual
   infinite periodic-tail carrier.  This closes normalized odd Section 6
   coercivity rather than a finite truncation.
3. **Assumptions remaining.**  Homogeneous coercivity for arbitrary energy,
   construction of the positive Hermitian tail form, its source-faithful form
   completion, and low/odd-tail Schur recombination remain.  The even lane is
   unaffected.
4. **Next make-or-break lemma.**  Normalize a nonzero arbitrary tail vector by
   the square root of its interval energy, handle the zero-energy case using
   clipped-circle faithfulness, and use sesquilinearity to derive the exact
   homogeneous lower bound.
5. **Viability evidence.**  Independent review checked the clipped reflection
   upgrade, endpoint representatives, Fourier inversion, and exact `v=2*pi*w`
   scaling.  Direct strict compiles, the 8,313-job target, and the umbrella
   pass.  All six relevant endpoints, including the composed unit-energy
   theorem, use only `propext`, `Classical.choice`, and `Quot.sound`; forbidden
   and diff scans are clean and the root legacy count remains 159.

## `bba8386` — Even distribution bridge reduced to one critical-cross identity

1. **Theorems added.**  Unified zero/cosine representatives now have exact
   support, reflection, and all correlation branches.  Their complete polar
   cross term is evaluated with the production normalization, the stable
   geometric kernel is rewritten pointwise as the admissible kernel minus the
   polar contribution, and every spectral product is proved integrable by an
   endpoint-aware `O(v^-2)` estimate.  A single critical-cross distribution
   identity now implies both the full admissible bridge and the moment bridge.
2. **Gate hypothesis eliminated.**  Mode support, correlation orientation,
   polar signs, factor two from whole-line folding, the `1/(2*pi)` scaling,
   and ordinary cross-product integrability no longer sit inside the broad
   40,000-entry interface.  The remaining statement concerns only the actual
   digamma/stable critical-cross transform.
3. **Assumptions remaining.**  `ClippedEvenCriticalCrossDistributionBridge`
   is still open.  Because the zero-extended cosine modes jump at the
   endpoints, the odd lane's global-continuity route and its stronger weighted
   spectral premise are unavailable; a tailored interchange for ordinary
   integrable `O(v^-2)` products is required.
4. **Next make-or-break lemma.**  Prove a Cauchy/digamma distribution identity
   under the already established product integrability, use the stable-minus-
   polar kernel and compactly supported correlations, and instantiate it for
   every unified even-mode pair.
5. **Viability evidence.**  Independent symbolic and numerical review checked
   every zero/positive/diagonal/off-diagonal branch, swap orientation, polar
   sign, fold, and normalization to about `1e-16`.  Warning-as-error, the
   3,600-job target, and umbrella compile pass; six public endpoints use only
   `propext`, `Classical.choice`, and `Quot.sound`.  The residual bridge is
   strictly narrower and does not reference either proposition it implies.

## `8ae5103` — Infinite odd tail bundled as a coercive positive form

1. **Theorems added.**  Exact scalar laws for clipped interval energy and the
   diagonal critical form promote unit-energy coercivity to
   `(38/25) * E(f) <= Q(f)` for every vector in the actual periodic tenth odd
   tail.  Zero energy is shown to force the clipped function to vanish through
   the exact circle norm identity and faithfulness.  Restricting the production
   sesquilinear form therefore yields a bundled `PositiveHermitianForm` with
   explicit source-`L²` coercivity.
2. **Gate hypothesis eliminated.**  Odd-tail positivity and definiteness are
   no longer assumptions or normalized-only statements.  The actual infinite
   tail now carries the source-faithful form norm required by the committed
   completion and Riesz-correction infrastructure.
3. **Assumptions remaining.**  Each low-mode pairing must be proved bounded in
   the form norm with the certified infinite coupling energy, and the resulting
   Riesz correction must be combined with the positive ten-mode Gram reserve.
   The final decomposition must then be transported back to every periodic
   odd source vector.
4. **Next make-or-break lemma.**  Expand a periodic odd-tail/low-mode pairing
   in the normalized high sine basis, justify the infinite interchange, and
   use the committed `19/500` squared coupling sum to construct the completed
   low-mode functionals.
5. **Viability evidence.**  Independent review checked both normalization
   cases, sesquilinear scaling, circle faithfulness, nested subtype instances,
   nonnegativity, and definiteness.  Direct strict and the 8,315-job focused
   build pass; seven endpoints use only `propext`, `Classical.choice`, and
   `Quot.sound`.  No form-positivity premise or theorem-shaped interface was
   introduced, and the root legacy count remains 159.

## `1f8e157` — First positive even diagonal moment certified

1. **Theorems added.**  The actual production moment `D_1` now lies in
   `[38331/100000, 38332/100000]`.  The accelerated series is enclosed by 32
   exact checkpoint blocks: blocks 0--30 contain 256 terms each and the final
   block contains 255, covering exactly `k = 1,...,8191`; the analytic tail
   begins at 8192.
2. **Gate hypothesis eliminated.**  The first nonconstant diagonal entry of
   the 200-mode interval Gram is now an analytic theorem rather than a
   discovery target.  Together with `D_0`, two of the 200 diagonal boxes are
   inhabited by their production moments.
3. **Assumptions remaining.**  `D_2,...,D_199`, all 199 sine boxes, and the
   remaining exact Schur checkpoints are still open.  The existing accelerated
   method is sound but its per-index replay cost motivates reusable batching.
4. **Next make-or-break lemma.**  Certify `D_2` with the same checkpointed
   architecture, then factor common head/tail lemmas so ranges of positive
   diagonal indices can share analytic and kernel work.
5. **Viability evidence.**  The exact enclosure is approximately
   `[0.383313987787, 0.383318714995]`; independent evaluation gives
   `0.3833159502715774`.  Independent review checked every block, subtraction
   direction, constant bound, and the 8191/8192 boundary.  Direct strict took
   about five minutes, the 3,625-job build passed, and the endpoint uses only
   `propext`, `Classical.choice`, and `Quot.sound`.

## `a2300bd` — First even sine moment certified

1. **Theorems added.**  The actual production sine moment `S_1` now lies in
   `[-145119/100000, -145118/100000]`.  The exact series enclosure uses the
   finite head `k = 0,...,1535` and an analytic infinite tail beginning at
   1536; `sum_add_tsum_nat_add` proves the split is exhaustive and disjoint.
2. **Gate hypothesis eliminated.**  One of the 199 sine target boxes consumed
   by the even interval Gram is now inhabited by its analytic moment.  The
   theorem is not a numerical truncation: every remaining series term is
   covered by a proved tail inequality.
3. **Assumptions remaining.**  `S_2,...,S_199`, `D_2,...,D_199`, and the full
   Schur replay remain.  The 1,536-term direct head shows the existing tail
   estimate is correct but too expensive to scale naively across all modes.
4. **Next make-or-break lemma.**  Retain additional terms of the Cauchy-tail
   asymptotic expansion and build checkpointed head accumulation so later
   sine boxes can use shorter analytic tails without deep recursive replay.
5. **Viability evidence.**  Direct strict and the 3,604-job focused build
   pass.  Independent review checked the subinterval direction and exact
   1535/1536 boundary; independent quadrature gives
   `-1.4511874810319608966`, inside the target.  Both endpoints use only
   `propext`, `Classical.choice`, and `Quot.sound`.

## `71503de` — Even critical-cross and full moment bridges closed

1. **Theorems added.**  Measurable Fourier convolution identifies every
   endpoint-jumping even spectral product with a continuous compactly
   supported correlation.  Ordinary-`L¹` Cauchy evaluation, finite monotone
   digamma partial sums, an index-independent dominator, and the renormalized
   real-space limit prove the critical-cross distribution identity for every
   pair of natural modes.  Premise-free wrappers then prove both the full
   40,000-entry admissible-distribution bridge and `ClippedEvenFullMomentBridge`.
2. **Gate hypothesis eliminated.**  The last analytic interface between the
   production clipped even Gram and `evenMomentFullGram` is gone.  Endpoint
   jumps do not require the false odd-style weighted integrability premise;
   the actual `O(v^-2)` product decay suffices.
3. **Assumptions remaining.**  Analytic containment of the remaining 396
   scalar moment targets, completion of the 200 exact Schur pivots, even-tail
   coercivity, and finite-to-tail coupling/recombination remain.  The moment
   bridge itself is unconditional.
4. **Next make-or-break lemma.**  Continue the diagonal and sine enclosure
   batches, then use those actual boxes to finish checkpointed pivot replay;
   in parallel, close the endpoint-compatible even-tail Section 6 estimate.
5. **Viability evidence.**  Deep independent review checked convolution
   orientation, angular `1/(2*pi)`, Cauchy signs, rate, fold, digamma
   monotonicity, domination, and every renormalized constant.  Strict direct,
   the 3,604-job target, and umbrella compile pass.  Final and downstream
   endpoints use only `propext`, `Classical.choice`, and `Quot.sound`;
   numerical spectral/real-space errors on representative branches range
   from about `2.1e-11` to `1.5e-9`.

## `a80978b` — Second positive even diagonal moment certified

1. **Theorems added.**  The actual production moment `D_2` now lies in
   `[106433/100000, 106434/100000]`.  Forty exact checkpoint blocks cover
   precisely `k = 1,...,10239`—39 blocks of 256 corrections and a final block
   of 255—while the proved analytic tail begins at 10240.
2. **Gate hypothesis eliminated.**  `D_2` is now an analytic theorem rather
   than a discovery target.  Together with `D_0` and `D_1`, three of the 200
   production diagonal boxes required by the full even Gram are certified.
3. **Assumptions remaining.**  `D_3,...,D_199`, `S_2,...,S_199`, the remaining
   exact Schur pivots, even-tail coercivity, and the exceptional finite/tail
   coupling estimate remain open.
4. **Next make-or-break lemma.**  Finish the in-progress `D_3` certificate and
   validate the accelerated, checkpointed sine architecture on `S_2`; then
   batch the remaining scalar boxes without changing their production target
   widths.
5. **Viability evidence.**  Independent exact replay gives the enclosure
   `[1.06433089932556, 1.06433981690207]`, while independent quadrature gives
   approximately `1.0643351971246413`.  Review checked every block, sign,
   constant, and the 10239/10240 boundary.  Fresh warning-as-error direct and
   umbrella elaboration pass; the endpoint uses only `propext`,
   `Classical.choice`, and `Quot.sound`, and all 159 legacy root artifacts
   remain untouched.

## `3842119` — Accelerated analytic sine tails certified

1. **Theorems added.**  Exact telescoping potentials enclose the shifted
   inverse-power tails for powers 2, 4, and 6.  Expanding
   `y / (t^2 + y^2)` through the cubic term with a proved positive fifth-order
   remainder yields two-sided bounds for the full Cauchy tail, including the
   correctly signed dyadic correction.  Rational interval wrappers compose
   those bounds with the exact finite head and production sine moment.
2. **Gate hypothesis eliminated.**  Sine-moment certification no longer
   depends on the coarse first-order `O(y/K)` tail.  The stronger analytic
   tail already reduces the `S_2` head requirement to 4096 and closes the
   `S_10` discovery target at 8192, making checkpointed scalar certificates
   practical without changing any target interval.
3. **Assumptions remaining.**  The accelerated layer does not itself inhabit
   `S_2,...,S_199`; each finite head still needs exact compact checkpoints and
   a final target subinterval theorem.  The diagonal, Schur, even-tail, and
   exceptional-coupling obligations are unchanged.
4. **Next make-or-break lemma.**  Prove a reusable theorem that a shallow sum
   of certified 256-term boxes contains the exact production head, then use it
   to certify `S_2` end to end and measure scaling at higher modes.
5. **Viability evidence.**  Independent review checked all telescoping limits,
   remainder signs, endpoint directions, the dyadic subtraction, and the
   exact finite-head/tail split.  Hurwitz-zeta sanity checks enclose multiple
   `(n,K)` pairs, including `n=10,K=256`.  Fresh strict direct, the 3,603-job
   target, and umbrella elaboration pass; all five public endpoints use only
   `propext`, `Classical.choice`, and `Quot.sound`.
