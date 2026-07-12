# Yoshida Sparse Congruence Certificate Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to implement this plan task by
> task with test-driven development and independent mathematical review after
> every production commit.

**Goal:** Prove positive definiteness of every real matrix contained in the
inflated 200-mode Yoshida target intervals using a sparse rational congruence
and exact weighted diagonal-dominance certificate, eliminating the
resource-infeasible full interval-pivot premise.

**Architecture:** A generic theorem first proves that a symmetric matrix with
strict weighted entrywise diagonal dominance is positive definite. A second
generic layer bounds the error after congruence and evaluates a rational
congruence through sparse `Finsupp` rows. Generated data then supplies a
lower-triangular rational preconditioner with 762 nonzeros and 200 positive
weights; bounded kernel checks prove the target-width and dominance
inequalities. The final bridge applies the robust interval theorem directly to
the actual corrected real Gram and then coerces it to the production complex
matrix.

**Tech Stack:** Lean 4.29.0-rc8, Mathlib `Matrix.PosDef`, `Finsupp`, exact
rational arithmetic, `RatInterval`, generated `decide +kernel` checks, and a
deterministic Python `Fraction` oracle.

## Global Constraints

- No `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, or proof
  bypass.
- Every shell workload must run as
  `systemd-run --user --scope --quiet --expand-environment=no -p MemoryMax=48G -- <command>`.
- Only one high-memory Lean/Lake scope may run at once; monitor cgroup
  `memory.current` and summed descendant `VmRSS` under predeclared lower stop
  thresholds.
- Preserve all 159 inventoried root Lean artifacts and all untracked pivot
  fallback sources. Stage only explicit intended files.
- Begin every production theorem with a temporary scratch RED test and remove
  the scratch before commit.
- Public theorem axiom footprints may contain only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The generated certificate must be reproducible from the committed target
  definitions; record exact payload hash, 762-nonzero count, support ordering,
  positive diagonal, exact maximum radius, and exact minimum dominance margin.
- Do not resume the 513,500-cell checkpoint replay unless this sparse route is
  formally falsified.

---

### Task 1: Generic weighted diagonal dominance

**Files:**

- Create: `ArithmeticHodge/Analysis/WeightedDiagonalDominance.lean`
- Test: `WeightedDiagonalDominanceScratch.lean` (temporary)

**Imports:**

```lean
import Mathlib.Analysis.Matrix.PosDef
```

**Produces:**

```lean
namespace ArithmeticHodge.Analysis.WeightedDiagonalDominance

theorem posDef_of_weighted_entry_bounds
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (d w : n → ℝ) (r : n → n → ℝ)
    (hw : ∀ i, 0 < w i)
    (hr0 : ∀ i j, 0 ≤ r i j)
    (hrsymm : ∀ i j, r i j = r j i)
    (hdiag : ∀ i, d i ≤ A i i)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ r i j)
    (hdom : ∀ i, (∑ j ∈ Finset.univ.erase i, r i j * w j) < d i * w i) :
    A.PosDef

end ArithmeticHodge.Analysis.WeightedDiagonalDominance
```

**Required RED/GREEN regression:** the matrix
`!![(2:ℝ), 1; 1, 2]`, weights `(1,1)`, diagonal bound `2`, and off-diagonal
bound `1` must instantiate the theorem and compile.

- [ ] Write the exact `Fin 2` regression against the absent module and record
  the missing-import RED failure.
- [ ] Expand `star x ⬝ᵥ (A *ᵥ x)` into diagonal and ordered off-diagonal sums.
- [ ] Bound each off-diagonal term below by
  `-r i j * |x i * x j|`.
- [ ] Prove weighted Young's inequality
  `2*|u*v| ≤ (b/a)*u^2 + (a/b)*v^2` for positive `a,b`, and use symmetry of
  `r` to reindex the second ordered sum.
- [ ] Extract a positive slack coefficient from `hdom`; show a nonzero vector
  has one strictly positive diagonal contribution.
- [ ] Strict-compile RED/GREEN, remove scratch, scan, axiom-audit, independently
  review both weight ratios and strictness, and commit as
  `formalize weighted diagonal dominance`.

### Task 2: Congruence error and sparse rational evaluator

**Files:**

- Create: `ArithmeticHodge/Analysis/SparseCongruenceCertificate.lean`
- Test: `SparseCongruenceCertificateScratch.lean` (temporary)

**Imports:**

```lean
import ArithmeticHodge.Analysis.WeightedDiagonalDominance
import Mathlib.LinearAlgebra.Matrix.Block
```

**Produces:**

```lean
abbrev SparseRow (n : Type*) := n →₀ ℚ

def matrixOfSparseRows {n : Type*} [DecidableEq n]
    (rows : n → SparseRow n) : Matrix n n ℚ :=
  fun i j => rows i j

def SparseRowsLowerTriangular {n : Type*} [Preorder n]
    (rows : n → SparseRow n) : Prop :=
  ∀ i j, rows i j ≠ 0 → j ≤ i

def sparseCongruenceEntry {n : Type*} [DecidableEq n]
    (rows : n → SparseRow n) (C : Matrix n n ℚ) (i j : n) : ℚ :=
  (rows i).sum fun k pik =>
    (rows j).sum fun l pjl => pik * C k l * pjl

theorem sparseCongruenceEntry_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (rows : n → SparseRow n) (C : Matrix n n ℚ) (i j : n) :
    sparseCongruenceEntry rows C i j =
      (matrixOfSparseRows rows * C * (matrixOfSparseRows rows)ᵀ) i j

theorem congruence_sub_center_entry_abs_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (P A C : Matrix n n ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ k l, |A k l - C k l| ≤ ε) (i j : n) :
    |(P * A * Pᵀ) i j - (P * C * Pᵀ) i j| ≤
      ε * (∑ k, |P i k|) * (∑ l, |P j l|)
```

- [ ] RED-test sparse evaluation on a two-entry `Fin 2` row and the
  congruence error theorem at `P=1`.
- [ ] Prove sparse/dense equality with `Finsupp.sum_fintype`; do not enumerate
  zero dense entries in generated checks.
- [ ] Expand the congruence difference, apply `abs_sum_le_sum_abs`, the entry
  error bound, and factor the two nonnegative L1 sums.
- [ ] Add generic lemmas converting a checked lower-triangular sparse support
  predicate plus nonzero diagonal into `IsUnit (matrixOfSparseRows rows)` via
  `Matrix.det_of_lowerTriangular`.
- [ ] Strict-compile, remove scratch, scan, axiom-audit, review sum index
  orientation and transpose placement, and commit as
  `add sparse congruence certificate machinery`.

### Task 3: Generated Yoshida sparse certificate data and checks

**Files:**

- Create: `ArithmeticHodge/Analysis/YoshidaEvenSparseCongruenceData.lean`
- Create: `ArithmeticHodge/Analysis/YoshidaEvenSparseCongruenceChecks1.lean`
- Create through:
  `ArithmeticHodge/Analysis/YoshidaEvenSparseCongruenceChecks10.lean`
- Test: `YoshidaEvenSparseCongruenceDataScratch.lean` (temporary)

**Generated declarations:** the deterministic generator emits complete Lean
equation tables, with no runtime file parsing, for these exact names and
types:

- `evenSparseEpsilon : ℚ`, definitionally `51 / 100000`;
- `evenSparseRows : YoshidaEvenIndex → SparseRow YoshidaEvenIndex`;
- `evenSparseWeights : YoshidaEvenIndex → ℚ`.

**Derived definitions:**

```lean
def evenSparseEpsilon : ℚ := 51 / 100000
def evenTargetInterval :
    Matrix YoshidaEvenIndex YoshidaEvenIndex RatInterval :=
  inflatedEvenMomentIntervalGram evenCorrectionRadius
    yoshidaEvenSineTargets yoshidaEvenDiagonalTargets
def evenTargetCenter : Matrix YoshidaEvenIndex YoshidaEvenIndex ℚ :=
  fun i j =>
    ((evenTargetInterval i j).lower + (evenTargetInterval i j).upper) / 2
def evenSparseRowL1 (i : YoshidaEvenIndex) : ℚ :=
  (evenSparseRows i).sum fun _ x => |x|
def evenSparseCenterCongruence (i j : YoshidaEvenIndex) : ℚ :=
  sparseCongruenceEntry evenSparseRows evenTargetCenter i j
```

**Checked endpoints:**

```lean
theorem evenTarget_radius_le_epsilon (i j : YoshidaEvenIndex) :
  ((evenTargetInterval i j).upper - (evenTargetInterval i j).lower) / 2 ≤
    evenSparseEpsilon

theorem evenSparseWeights_pos (i : YoshidaEvenIndex) :
  0 < evenSparseWeights i

theorem evenSparseRows_lowerTriangular :
  SparseRowsLowerTriangular evenSparseRows
theorem evenSparseRows_diagonal_pos (i : YoshidaEvenIndex) :
  0 < evenSparseRows i i

theorem evenSparse_weightedDominance (i : YoshidaEvenIndex) :
  (∑ j ∈ Finset.univ.erase i,
      (|evenSparseCenterCongruence i j| +
        evenSparseEpsilon * evenSparseRowL1 i * evenSparseRowL1 j) *
        evenSparseWeights j) <
    (evenSparseCenterCongruence i i -
      evenSparseEpsilon * evenSparseRowL1 i ^ 2) *
      evenSparseWeights i
```

- [ ] Run the deterministic `Fraction` generator and require exact target
  reconstruction, maximum half-width
  `41214331/80896200000 < 51/100000`, exactly 762 nonzeros, 200 positive
  diagonal entries, and all 200 strict dominance rows.
- [ ] Record the canonical serialization hash and exact minimum rational
  dominance margin in the source header.
- [ ] Emit only sparse rows and weights; compute center-congruence entries
  through sparse supports, not dense 200-term matrix multiplication.
- [ ] Split width/dominance checks into ten fixed 20-row opaque modules so
  kernel reduction state is released between targets.
- [ ] Sequentially strict-build each checks module with dual memory guards;
  independently replay the generator and compare hashes.
- [ ] Remove scratch, scan, axiom-audit the aggregate endpoints, and commit as
  `certify sparse Yoshida congruence data`.

### Task 4: Robust interval positive definiteness endpoint

**Files:**

- Create: `ArithmeticHodge/Analysis/YoshidaEvenSparseCongruence.lean`
- Test: `YoshidaEvenSparseCongruenceScratch.lean` (temporary)

**Produces:**

```lean
theorem evenTarget_sparseCongruence_posDef
    (A : Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ)
    (hA : A.IsHermitian)
    (hcontains : ∀ i j,
      (inflatedEvenMomentIntervalGram evenCorrectionRadius
        yoshidaEvenSineTargets yoshidaEvenDiagonalTargets i j).Contains
          (A i j)) :
    A.PosDef
```

- [ ] RED-test the exact endpoint on the interval midpoint matrix.
- [ ] Derive `|A-C|≤ε` from containment, midpoint algebra, and the checked
  half-width theorem.
- [ ] Apply `congruence_sub_center_entry_abs_le` to obtain diagonal lower and
  off-diagonal absolute bounds for `P*A*Pᵀ`.
- [ ] Cast the exact rational weighted-dominance checks to real and invoke
  `posDef_of_weighted_entry_bounds`.
- [ ] Prove the sparse rational `P` is a unit after real coercion, then use
  `Matrix.IsUnit.posDef_star_right_conjugate_iff` to transport positivity from
  `P*A*Pᵀ` back to `A`.
- [ ] Strict-compile, remove scratch, source/olean scan, axiom-audit,
  independent mathematical review, and commit as
  `prove robust Yoshida target positivity`.

### Task 5: Actual corrected Gram and conditional-chain specialization

**Files:**

- Create: `ArithmeticHodge/Analysis/YoshidaEvenSparseFiniteSchur.lean`
- Test: `YoshidaEvenSparseFiniteSchurScratch.lean` (temporary)

**Produces:**

```lean
theorem actualEvenTailCorrectedGram_posDef_of_enclosures
    (hS : YoshidaEvenSineTargetEnclosures)
    (hD : YoshidaEvenDiagonalTargetEnclosures) :
    (clippedEvenFullGram - actualEvenTailCorrectionGram).PosDef
```

- [ ] RED-test the two-premise endpoint and verify the old three-premise
  theorem cannot discharge it without `YoshidaEvenFullTargetPivots`.
- [ ] Use `inflatedEvenMomentIntervalGram_contains`, the sine/diagonal
  enclosures, and `actualEvenTailCorrectedRealGram_close` to contain the actual
  corrected real Gram in the target matrix.
- [ ] Apply `evenTarget_sparseCongruence_posDef`, then
  `Matrix.PosDef.complexOfReal` and
  `complexOfRealMatrix_actualEvenTailCorrectedRealGram`.
- [ ] Instantiate the existing infinite even/parity and ratio-two Bombieri
  theorems with the committed sine inhabitant and, once available, the full
  diagonal inhabitant; the pivot proposition must disappear from the public
  specialization.
- [ ] Strict-build the focused chain and full project under guards, remove
  scratch, scan, axiom-audit, independent-review, record the terminal-distance
  reduction, and commit as `eliminate the Yoshida pivot premise`.

## Fallback disposition

- [ ] Keep the existing untracked Core/Payload/Chunks/Certificate sources
  unchanged until `evenTarget_sparseCongruence_posDef` is committed and
  independently reviewed.
- [ ] After the sparse endpoint lands, inventory those files as superseded
  fallback artifacts rather than deleting them; do not add them to production
  imports.
