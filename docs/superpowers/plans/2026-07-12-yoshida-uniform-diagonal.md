# Yoshida Uniform Diagonal Certificate Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to implement this plan task by
> task with test-driven development and an independent review after each
> commit.

**Goal:** Replace the mode-by-mode high diagonal certificates with one exact
series identity and a uniform analytic error theorem that certifies every
canonical diagonal target through mode 199, using finite checkpoints only for
modes 4, 5, 6, 7, 8, 11, 14, and 15.

**Architecture:** First expose the algebraic profile identity and reorganize
the production accelerated series into digamma, derivative-tail, and dyadic
pieces. Prove the three error estimates independently, combine them into one
asymmetric high-mode enclosure, and finish with kernel-checked rational target
arithmetic plus a small checkpoint exception module. Each analytic component
is independently reviewable and no task requires generating one file per high
mode.

**Tech Stack:** Lean 4.29.0-rc8, Mathlib real analysis and `tsum`, the existing
Yoshida accelerated-series API, exact `RatInterval` arithmetic, and
kernel-checked `norm_num`/`decide` certificates.

## Global Constraints

- No `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, or proof
  bypass.
- Preserve the 159 inventoried legacy root Lean artifacts and their archive
  ref; stage only explicit intended paths.
- Every shell workload must run as
  `systemd-run --user --scope --quiet --expand-environment=no -p MemoryMax=48G -- <command>`.
- Run only one high-memory Lean/Lake scope at a time. Monitor both cgroup
  `memory.current` and summed descendant `VmRSS`, with a lower manual stop
  threshold selected before each build.
- Begin every Lean task with a temporary RED scratch theorem and remove the
  scratch file before committing production code.
- Strict-compile each production module, scan forbidden tokens, inspect
  `#print axioms` for public endpoints, and obtain an independent source review
  before each commit.
- The allowed public axiom footprint is exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- Do not compile the generated mode 189 or 191--199 fallback files while the
  uniform route remains viable.

---

### Task 1: Exact ramp/profile algebra

**Files:**

- Create: `ArithmeticHodge/Analysis/YoshidaDiagonalUniformIdentity.lean`
- Test: `YoshidaDiagonalUniformIdentityScratch.lean` (temporary; delete before
  commit)

**Imports:**

```lean
import ArithmeticHodge.Analysis.DigammaTrapezoid
import ArithmeticHodge.Analysis.YoshidaDiagonalAcceleratedSeries
```

**Produces in `ArithmeticHodge.Analysis.YoshidaDiagonalUniformIdentity`:**

```lean
def yoshidaY (n : ℕ) : ℝ := yoshidaKappa n / 2

def diagonalHighProfile (y t : ℝ) : ℝ :=
  reciprocalRealPart y (t + 1 / 4)

def diagonalHighProfileDeriv (y t : ℝ) : ℝ :=
  reciprocalRealPartDeriv y (t + 1 / 4)

theorem two_mul_diagonalRampClosed_eq_profile_add_deriv
    {L y k : ℝ} (hL : L ≠ 0) (hy : y ≠ 0) :
    2 * diagonalRampClosed L ((2 * y) ^ 2) (2 * k + 1 / 2) 0 =
      diagonalHighProfile y k + diagonalHighProfileDeriv y k / (2 * L)
```

- [ ] Write the scratch `example` with the exact theorem statement and record
  RED because the production module/theorem does not exist.
- [ ] Implement only the three definitions and algebra theorem by unfolding
  `diagonalRampClosed`, `reciprocalRealPart`, and
  `reciprocalRealPartDeriv`, then `field_simp [hL, hy]` and `ring`.
- [ ] Strict-compile scratch and production in the 48 GiB scope; delete the
  scratch; scan, axiom-audit, review, stage only the new production file, and
  commit as `start uniform diagonal identity`.

### Task 2: Production moment series decomposition

**Files:**

- Modify: `ArithmeticHodge/Analysis/YoshidaDiagonalUniformIdentity.lean`
- Test: `YoshidaDiagonalUniformSeriesScratch.lean` (temporary)

**Produces:**

```lean
def diagonalHighDerivativeTerm (n j : ℕ) : ℝ :=
  diagonalHighProfileDeriv (yoshidaY n) (j + 1)

def diagonalHighQTerm (n j : ℕ) : ℝ :=
  let k : ℝ := j + 1
  2 * ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ (j + 1)) *
    (((2 * k + 1 / 2) ^ 2 - yoshidaKappa n ^ 2) /
      (yoshidaLength *
        ((2 * k + 1 / 2) ^ 2 + yoshidaKappa n ^ 2) ^ 2))

def diagonalHighQ (n : ℕ) : ℝ :=
  ∑' j : ℕ, diagonalHighQTerm n j

theorem yoshidaDiagonalMoment_eq_uniformSeries
    {n : ℕ} (hn : n ≠ 0) :
    yoshidaDiagonalMoment n =
      (Complex.digamma ((1 / 4 : ℝ) + yoshidaY n * Complex.I)).re -
        Real.log Real.pi +
        2 * diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
          (-1 / 2) (Real.sqrt 2) +
        diagonalHighProfile (yoshidaY n) 0 -
        (∑' j : ℕ, diagonalHighDerivativeTerm n j) /
          (2 * yoshidaLength) -
        diagonalHighQ n
```

- [ ] Record RED on the exact identity in the scratch file.
- [ ] Prove summability of the derivative and dyadic terms by comparison with
  the existing summable accelerated correction and geometric series APIs.
- [ ] Rewrite `yoshidaDiagonalMoment_eq_acceleratedSeries`, use the Task 1
  pointwise identity at `k = j + 1`, and use
  `digamma_quarter_vertical_re_eq_trapezoid_series` to sum the profile-minus-
  harmonic part.
- [ ] Check explicitly that Euler gamma, `log (4/3)`, and `pi^2/6` cancel and
  that the outer raw-series `+1` cancels the shifted harmonic telescope.
- [ ] Strict-compile, delete scratch, scan, axiom-audit, independently review
  signs and `j=0`/`k=1` indexing, and commit as
  `decompose uniform diagonal series`.

### Task 3: Corrected trapezoid and real-digamma error

**Files:**

- Create: `ArithmeticHodge/Analysis/CorrectedTrapezoidRemainder.lean`
- Create: `ArithmeticHodge/Analysis/YoshidaDiagonalDigammaHighBound.lean`
- Test: `CorrectedTrapezoidRemainderScratch.lean` (temporary)
- Test: `YoshidaDiagonalDigammaHighBoundScratch.lean` (temporary)

**Produces:**

```lean
def diagonalHighProfileThirdDeriv (y t : ℝ) : ℝ :=
  -6 * ((t + 1 / 4) ^ 4 - 6 * (t + 1 / 4) ^ 2 * y ^ 2 + y ^ 4) /
    ((t + 1 / 4) ^ 2 + y ^ 2) ^ 4

def diagonalDigammaMain (y : ℝ) : ℝ :=
  Real.log ((1 / 16 : ℝ) + y ^ 2) / 2 -
    diagonalHighProfile y 0 / 2 +
    diagonalHighProfileDeriv y 0 / 12 -
    diagonalHighProfileThirdDeriv y 0 / 720

theorem digamma_quarter_vertical_re_sub_highMain_abs_le
    {y : ℝ} (hy : 0 < y) :
    |(Complex.digamma ((1 / 4 : ℝ) + y * Complex.I)).re -
        diagonalDigammaMain y| ≤ 4 / (3 * y ^ 5)
```

The generic helper in `CorrectedTrapezoidRemainder.lean` must state the
fourth-order corrected one-cell trapezoid remainder in terms of a fifth
derivative integral, with correction coefficients `1/12` and `1/720`; it must
not be Yoshida-specific.

- [ ] RED-test the generic corrected-trapezoid theorem on a polynomial whose
  fifth derivative vanishes.
- [ ] Prove the generic integral remainder from repeated integration by parts
  or the existing trapezoidal-error kernel identity.
- [ ] RED-test the public real-digamma bound with `y = yoshidaY 16`.
- [ ] Establish the exact first, third, and fifth derivative formulas for the
  shifted reciprocal profile.
- [ ] Prove
  `|f⁽⁵⁾(t)| ≤ 600 / (((t + 1/4)^2 + y^2)^3)` on `t ≥ 0`, integrate it,
  and close `4/(3*y^5)` using the repository's strict rational pi bound.
- [ ] Strict-compile each module separately, remove scratches, scan,
  axiom-audit, review the derivative algebra and improper-integral boundary,
  and commit as `bound uniform diagonal digamma error`.

### Task 4: Derivative-tail and dyadic error bounds

**Files:**

- Create: `ArithmeticHodge/Analysis/YoshidaDiagonalDerivativeTailBound.lean`
- Create: `ArithmeticHodge/Analysis/YoshidaDiagonalDyadicHighBound.lean`
- Test: `YoshidaDiagonalHighTailsScratch.lean` (temporary)

**Produces:**

```lean
def diagonalDerivativeMain (y : ℝ) : ℝ :=
  -diagonalHighProfile y 1 +
    diagonalHighProfileDeriv y 1 / 2 -
    reciprocalRealPartSecondDeriv y (1 + 1 / 4) / 12

theorem diagonalHighDerivative_tsum_sub_main_abs_le
    {n : ℕ} (hn : 1 ≤ n) :
    |(∑' j : ℕ, diagonalHighDerivativeTerm n j) -
        diagonalDerivativeMain (yoshidaY n)| ≤
      5 / (2 * yoshidaY n ^ 4)

def diagonalQMain (n : ℕ) : ℝ :=
  -2 / (3 * Real.sqrt 2 * yoshidaLength * yoshidaKappa n ^ 2)

theorem diagonalHighQ_bounds {n : ℕ} (hn : 1 ≤ n) :
    diagonalQMain n ≤ diagonalHighQ n ∧
      diagonalHighQ n ≤ diagonalQMain n +
        425 / (18 * Real.sqrt 2 * yoshidaLength *
          (yoshidaKappa n ^ 2) ^ 2)
```

- [ ] RED-test both exact public statements.
- [ ] Prove the derivative-tail Euler--Maclaurin estimate from
  `|f⁽⁴⁾(t)| ≤ 120*(t+1/4)/(((t+1/4)^2+y^2)^3)` and its exact integral
  bound `30/y^4`.
- [ ] Prove pointwise
  `-1/p ≤ (a^2-p)/(a^2+p)^2` and
  `(a^2-p)/(a^2+p)^2 ≤ -1/p + 3*a^2/p^2`.
- [ ] Kernel-check the two geometric sums
  `sum 4^-k/sqrt 2 = 1/(3*sqrt 2)` and
  `sum (4^-k/sqrt 2)*(2*k+1/2)^2 = 425/(108*sqrt 2)` with indexing
  starting at `k=1`.
- [ ] Combine pointwise and geometric bounds, strict-compile, remove scratch,
  scan, axiom-audit, independent-review the one-sided signs, and commit as
  `bound uniform diagonal tail terms`.

### Task 5: Combined asymmetric moment enclosure

**Files:**

- Create: `ArithmeticHodge/Analysis/YoshidaDiagonalUniformHighBound.lean`
- Test: `YoshidaDiagonalUniformHighBoundScratch.lean` (temporary)

**Produces:**

```lean
def diagonalHighMain (n : ℕ) : ℝ :=
  diagonalDigammaMain (yoshidaY n) - Real.log Real.pi +
    2 * diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
      (-1 / 2) (Real.sqrt 2) +
    diagonalHighProfile (yoshidaY n) 0 -
    diagonalDerivativeMain (yoshidaY n) / (2 * yoshidaLength) -
    diagonalQMain n

theorem yoshidaDiagonalMoment_highMain_error
    {n : ℕ} (hn : 1 ≤ n) :
    -(4 / (3 * yoshidaY n ^ 5) +
        5 / (4 * yoshidaLength * yoshidaY n ^ 4) +
        425 / (18 * Real.sqrt 2 * yoshidaLength *
          (yoshidaKappa n ^ 2) ^ 2)) ≤
      yoshidaDiagonalMoment n - diagonalHighMain n ∧
    yoshidaDiagonalMoment n - diagonalHighMain n ≤
      4 / (3 * yoshidaY n ^ 5) +
        5 / (4 * yoshidaLength * yoshidaY n ^ 4)
```

- [ ] RED-test the combined theorem at modes 9, 16, 162, and 199.
- [ ] Rewrite the Task 2 exact identity and substitute the three Task 3--4
  estimates without weakening the one-sided dyadic sign.
- [ ] Strict-compile, remove scratch, scan, axiom-audit, independently compare
  the theorem against exact high-precision values, and commit as
  `assemble uniform diagonal error bound`.

### Task 6: Rational targets and eight finite exceptions

**Files:**

- Create: `ArithmeticHodge/Analysis/YoshidaEvenDiagonalUniformEnclosures.lean`
- Create: `ArithmeticHodge/Analysis/YoshidaEvenDiagonalExceptionEnclosures.lean`
- Create: `ArithmeticHodge/Analysis/YoshidaEvenDiagonalAllEnclosures.lean`
- Test: `YoshidaEvenDiagonalAllEnclosuresScratch.lean` (temporary)

**Produces:**

```lean
theorem yoshidaEvenDiagonalTarget_uniform_contains
    {n : ℕ} (hlo : 9 ≤ n) (hhi : n ≤ 199)
    (h11 : n ≠ 11) (h14 : n ≠ 14) (h15 : n ≠ 15) :
    (yoshidaEvenDiagonalTargets n).Contains (yoshidaDiagonalMoment n)

theorem yoshidaEvenDiagonalTarget_all_contains
    {n : ℕ} (hn : n ≤ 199) :
    (yoshidaEvenDiagonalTargets n).Contains (yoshidaDiagonalMoment n)
```

- [ ] Generate exact rational intervals for the canceled logarithmic form
  `log n - log yoshidaLength +
  log (1 + yoshidaLength^2/(16*pi^2*n^2))/2`; use at least 12 atanh terms
  for `log n` and `log yoshidaLength` and an exact one-term `log1p`
  remainder.
- [ ] Re-run the exact `Fraction` oracle and require all 188 uniform cases to
  pass; explicitly record the mode-162 lower margin and hash the generated
  rational table.
- [ ] Kernel-check the uniform table in bounded chunks so no single theorem
  recreates the previous monolithic elaboration failure.
- [ ] Build a single checkpoint exception module for exactly modes
  `4,5,6,7,8,11,14,15`; reuse existing modes 0--3 and the uniform theorem
  for all remaining cases.
- [ ] RED-test and then prove `yoshidaEvenDiagonalTarget_all_contains` by
  finite case routing only; do not duplicate analytic calculations.
- [ ] Sequentially strict-compile each chunk/module under dual memory guards,
  remove scratch, full-build, forbidden-scan, axiom-audit the all-mode
  endpoint, independently replay all rational data, and commit as
  `certify all Yoshida even diagonal targets`.

## Final integration gate

- [ ] Replace the diagonal premise of the full 200-mode pivot/Schur
  specialization with `yoshidaEvenDiagonalTarget_all_contains`.
- [ ] Verify that only the sine certificate and pivot certificate remain as
  finite premises; do not retain generated high-mode diagonal imports.
- [ ] Run the full scoped `lake build`, source/olean forbidden scans, dependency
  closure, `#print axioms`, legacy-artifact count, and independent review.
- [ ] Record the exact Gate 1 hypothesis discharged and the next unresolved
  premise in the terminal-distance audit before committing the integration.
