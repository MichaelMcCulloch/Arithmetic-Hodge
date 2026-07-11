# Yoshida Matrix Comparison Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce the exact Lean bridge from a rational Yoshida comparison matrix, through real positive definiteness and entrywise Gram bounds, to positive definiteness of the corrected complex Gram.

**Architecture:** First extend the rational LDL certificate API to real matrices so its output matches the comparison theorem. Next prove a generic absolute-entry comparison by testing the real matrix on the vector of complex coordinate norms. Finally promote the fixed q9-minus-two odd 10-by-10 matrix and its exact unit-lower LDL payload into a tracked production module exposing both real and complex positive-definiteness theorems.

**Tech Stack:** Lean 4, Mathlib `Matrix.PosDef`, rational casts, exact `LDLᴴ`, finite sums, `decide +kernel`, and complex norm inequalities.

## Global Constraints

- No `sorry`, `admit`, custom `axiom`, unsafe declaration, `native_decide`, or RH-equivalent proof bypass.
- Preserve all 159 inventoried legacy untracked Lean research files exactly.
- Work directly on `main` as explicitly authorized by the user; commit each reviewed task separately.
- Use one implementation agent at a time and give every agent disjoint production and scratch files.
- Every production theorem must first have a strict RED that fails for the expected missing declaration or module.
- Every production module must pass `lake env lean -DwarningAsError=true <file>` and the repository must pass `lake build ArithmeticHodge`.
- Every public theorem must audit to `[propext, Classical.choice, Quot.sound]` or a subset.
- Generated decimal or mpmath output is discovery only; all stored matrix entries, factors, pivots, and identities are exact rationals checked by the Lean kernel.
- `decide +kernel` is allowed for exact finite rational propositions; `native_decide` is forbidden because it introduces a native-evaluation axiom.
- The exact matrix certificate does not assert the still-unproved analytic comparison between the rational matrix and Yoshida's true or corrected Gram.

---

### Task 1: Real rational-LDL positive-definiteness bridge

**Files:**

- Modify: `ArithmeticHodge/Analysis/RationalPosDefCertificate.lean`
- Test: `RationalPosDefRealScratch.lean` (temporary; delete before commit)

**Interfaces:**

- Consumes: the same rational `A`, unit `L`, positive `d`, and exact factorization as `rationalLDL_posDef_complex`.
- Produces:

```lean
theorem rationalLDL_posDef_real
    {n : Type*} [Fintype n] [DecidableEq n]
    (A L : Matrix n n ℚ) (d : n → ℚ)
    (hL : IsUnit L) (hd : ∀ i, 0 < d i)
    (hA : A = L * Matrix.diagonal d * Lᴴ) :
    Matrix.PosDef ((Rat.castHom ℝ).mapMatrix A)
```

- [ ] **Step 1: Write and run the strict RED**

Create `RationalPosDefRealScratch.lean`:

```lean
import ArithmeticHodge.Analysis.RationalPosDefCertificate

set_option autoImplicit false

namespace ArithmeticHodge.Analysis

#check rationalLDL_posDef_real

end ArithmeticHodge.Analysis
```

Run:

```bash
lake env lean -DwarningAsError=true RationalPosDefRealScratch.lean
```

Expected: unknown identifier `rationalLDL_posDef_real`.

- [ ] **Step 2: Add the real star-order dependency and theorem**

Add this direct import after the existing import:

```lean
import Mathlib.Data.Real.StarOrdered
```

Add the theorem in `ArithmeticHodge.Analysis`:

```lean
theorem rationalLDL_posDef_real
    {n : Type*} [Fintype n] [DecidableEq n]
    (A L : Matrix n n ℚ) (d : n → ℚ)
    (hL : IsUnit L) (hd : ∀ i, 0 < d i)
    (hA : A = L * Matrix.diagonal d * Lᴴ) :
    Matrix.PosDef ((Rat.castHom ℝ).mapMatrix A) := by
  rw [hA, map_mul, map_mul]
  have hL' : IsUnit ((Rat.castHom ℝ).mapMatrix L) :=
    hL.map (Rat.castHom ℝ).mapMatrix
  rw [show (Rat.castHom ℝ).mapMatrix Lᴴ =
      star ((Rat.castHom ℝ).mapMatrix L) by
    ext i j
    simp [RingHom.mapMatrix_apply]]
  apply hL'.posDef_star_right_conjugate_iff.mpr
  rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero (Rat.castHom ℝ))]
  apply Matrix.PosDef.diagonal
  intro i
  exact (Rat.cast_pos (K := ℝ)).2 (hd i)
```

- [ ] **Step 3: Verify GREEN, regression, and gates**

Extend the scratch with this exact 2-by-2 regression:

```lean
example : Matrix.PosDef
    ((Rat.castHom ℝ).mapMatrix
      (!![(2 : ℚ), 1;
          1, 2] : Matrix (Fin 2) (Fin 2) ℚ)) := by
  let A : Matrix (Fin 2) (Fin 2) ℚ :=
    !![(2 : ℚ), 1;
       1, 2]
  let L : Matrix (Fin 2) (Fin 2) ℚ :=
    !![(1 : ℚ), 0;
       1 / 2, 1]
  let d : Fin 2 → ℚ := ![(2 : ℚ), 3 / 2]
  apply rationalLDL_posDef_real A L d
  · rw [Matrix.isUnit_iff_isUnit_det]
    norm_num [L, Matrix.det_fin_two]
  · intro i
    fin_cases i <;> norm_num [d]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, L, d, Matrix.mul_apply, Matrix.vecMul, dotProduct]
```

Run:

```bash
lake env lean -DwarningAsError=true RationalPosDefRealScratch.lean
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/RationalPosDefCertificate.lean
lake build ArithmeticHodge
```

Expected: all exit zero. Delete the scratch, run proof/naming/dependency scans, audit both rational-LDL theorems, inspect the exact one-file diff, and verify all 159 legacy artifacts against the archive ref.

- [ ] **Step 4: Commit**

```bash
git add ArithmeticHodge/Analysis/RationalPosDefCertificate.lean
git commit -m "extend rational LDL certificates to real matrices"
```

---

### Task 2: Absolute-entry positive-definite comparison

**Files:**

- Create: `ArithmeticHodge/Analysis/MatrixAbsEntryComparison.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `MatrixAbsEntryComparisonScratch.lean` (temporary; delete before commit)

**Interfaces:**

- Consumes: a Hermitian complex Gram `G`, a positive-definite real comparison matrix `U`, diagonal lower bounds, and off-diagonal absolute upper bounds.
- Produces:

```lean
theorem Matrix.posDef_of_abs_entry_comparison
    {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℂ) (U : Matrix n n ℝ)
    (hG : G.IsHermitian) (hU : U.PosDef)
    (hdiag : ∀ i, U i i ≤ (G i i).re)
    (hoff : ∀ i j, i ≠ j → ‖G i j‖ ≤ -U i j) : G.PosDef
```

- [ ] **Step 1: Write and run the strict missing-module RED**

Create `MatrixAbsEntryComparisonScratch.lean`:

```lean
import ArithmeticHodge.Analysis.MatrixAbsEntryComparison

set_option autoImplicit false

#check Matrix.posDef_of_abs_entry_comparison
```

Run:

```bash
lake env lean -DwarningAsError=true MatrixAbsEntryComparisonScratch.lean
```

Expected: missing production module.

- [ ] **Step 2: Implement the exact comparison theorem**

Create `ArithmeticHodge/Analysis/MatrixAbsEntryComparison.lean`:

```lean
import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false

open scoped BigOperators ComplexOrder

namespace Matrix

private lemma diagonal_comparison (u : ℝ) (a b : ℂ) (h : u ≤ b.re) :
    u * ‖a‖ * ‖a‖ ≤ (star a * b * a).re := by
  calc
    u * ‖a‖ * ‖a‖ = u * ‖a‖ ^ 2 := by ring
    _ ≤ b.re * ‖a‖ ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg _)
    _ = (star a * b * a).re := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.star_def, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im]
      ring

private lemma offDiagonal_comparison (u : ℝ) (a b c : ℂ) (h : ‖b‖ ≤ -u) :
    u * ‖a‖ * ‖c‖ ≤ (star a * b * c).re := by
  calc
    u * ‖a‖ * ‖c‖ = u * (‖a‖ * ‖c‖) := by ring
    _ ≤ (-‖b‖) * (‖a‖ * ‖c‖) := by
      gcongr
      linarith
    _ = -‖star a * b * c‖ := by simp; ring
    _ ≤ (star a * b * c).re := neg_le_of_abs_le (Complex.abs_re_le_norm _)

theorem posDef_of_abs_entry_comparison
    {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℂ) (U : Matrix n n ℝ)
    (hG : G.IsHermitian) (hU : U.PosDef)
    (hdiag : ∀ i, U i i ≤ (G i i).re)
    (hoff : ∀ i j, i ≠ j → ‖G i j‖ ≤ -U i j) : G.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hG fun z hz ↦ ?_
  apply RCLike.pos_iff.mpr
  refine ⟨?_, hG.im_star_dotProduct_mulVec_self z⟩
  let r : n → ℝ := fun i ↦ ‖z i‖
  have hr : r ≠ 0 := by
    intro hr
    apply hz
    funext i
    exact norm_eq_zero.mp (congr_fun hr i)
  have hpositive : 0 < star r ⬝ᵥ (U *ᵥ r) := hU.dotProduct_mulVec_pos hr
  apply hpositive.trans_le
  simp only [dotProduct, mulVec, Finset.mul_sum, map_sum, star_trivial, r]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i = j
  · subst j
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      diagonal_comparison (U i i) (z i) (G i i) (hdiag i)
  · simpa only [mul_assoc, mul_left_comm, mul_comm] using
      offDiagonal_comparison (U i j) (z i) (G i j) (z j) (hoff i j hij)

end Matrix
```

- [ ] **Step 3: Verify GREEN and gates**

Run:

```bash
lake env lean -DwarningAsError=true MatrixAbsEntryComparisonScratch.lean
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/MatrixAbsEntryComparison.lean
lake build ArithmeticHodge
```

Expected: all exit zero. Delete the scratch, scan, audit `Matrix.posDef_of_abs_entry_comparison`, inspect the exact module plus umbrella-import diff, and verify the legacy inventory.

- [ ] **Step 4: Commit**

```bash
git add ArithmeticHodge/Analysis/MatrixAbsEntryComparison.lean ArithmeticHodge.lean
git commit -m "compare Hermitian Grams by absolute entries"
```

---

### Task 3: Exact q9-minus-two odd 10-by-10 certificate

**Files:**

- Create: `ArithmeticHodge/Analysis/YoshidaOddComparisonCertificate.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `YoshidaOddComparisonCertificateScratch.lean` (temporary; delete before commit)

**Interfaces:**

- Consumes: both rational-LDL bridge theorems from Task 1.
- Produces: the exact rational matrix, its unit-lower factor and positive diagonal, plus real and complex positive-definiteness theorems.

- [ ] **Step 1: Write and run the strict missing-module RED**

Create `YoshidaOddComparisonCertificateScratch.lean`:

```lean
import ArithmeticHodge.Analysis.YoshidaOddComparisonCertificate

set_option autoImplicit false

namespace ArithmeticHodge.Analysis

#check yoshidaOddComparison10
#check yoshidaOddComparison10L
#check yoshidaOddComparison10D
#check yoshidaOddComparison10_posDef_real
#check yoshidaOddComparison10_posDef_complex

end ArithmeticHodge.Analysis
```

Run:

```bash
lake env lean -DwarningAsError=true YoshidaOddComparisonCertificateScratch.lean
```

Expected: missing production module.

- [ ] **Step 2: Store the exact matrix and LDL payload**

Create the module header and exact data:

```lean
import ArithmeticHodge.Analysis.RationalPosDefCertificate

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace ArithmeticHodge.Analysis

def yoshidaOddComparison10 : Matrix (Fin 10) (Fin 10) ℚ := ![
  ![63 / 512, -(91 / 512), -(73 / 512), -(31 / 256), -(27 / 256),
    -(49 / 512), -(45 / 512), -(41 / 512), -(39 / 512), -(37 / 512)],
  ![-(91 / 512), 117 / 128, -(63 / 512), -(55 / 512), -(25 / 256),
    -(23 / 256), -(21 / 256), -(5 / 64), -(37 / 512), -(9 / 128)],
  ![-(73 / 512), -(63 / 512), 347 / 256, -(25 / 256), -(23 / 256),
    -(43 / 512), -(5 / 64), -(19 / 256), -(9 / 128), -(17 / 256)],
  ![-(31 / 256), -(55 / 512), -(25 / 256), 851 / 512, -(43 / 512),
    -(5 / 64), -(19 / 256), -(9 / 128), -(17 / 256), -(33 / 512)],
  ![-(27 / 256), -(25 / 256), -(23 / 256), -(43 / 512), 243 / 128,
    -(19 / 256), -(9 / 128), -(17 / 256), -(33 / 512), -(1 / 16)],
  ![-(49 / 512), -(23 / 256), -(43 / 512), -(5 / 64), -(19 / 256),
    1069 / 512, -(35 / 512), -(33 / 512), -(1 / 16), -(31 / 512)],
  ![-(45 / 512), -(21 / 256), -(5 / 64), -(19 / 256), -(9 / 128),
    -(35 / 512), 1151 / 512, -(1 / 16), -(31 / 512), -(15 / 256)],
  ![-(41 / 512), -(5 / 64), -(19 / 256), -(9 / 128), -(17 / 256),
    -(33 / 512), -(1 / 16), 1221 / 512, -(15 / 256), -(29 / 512)],
  ![-(39 / 512), -(37 / 512), -(9 / 128), -(17 / 256), -(33 / 512),
    -(1 / 16), -(31 / 512), -(15 / 256), 1283 / 512, -(29 / 512)],
  ![-(37 / 512), -(9 / 128), -(17 / 256), -(33 / 512), -(1 / 16),
    -(31 / 512), -(15 / 256), -(29 / 512), -(29 / 512), 1339 / 512]
]

def yoshidaOddComparison10L : Matrix (Fin 10) (Fin 10) ℚ := ![
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-(13 / 9), 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-(73 / 63), -(1516 / 3029), 1, 0, 0, 0, 0, 0, 0, 0],
  ![-(62 / 63), -(1301 / 3029), -(4117424 / 11133845), 1, 0, 0, 0, 0, 0, 0],
  ![-(6 / 7), -(1152 / 3029), -(3660376 / 11133845),
    -(2393365603 / 7304709298), 1, 0, 0, 0, 0, 0],
  ![-(7 / 9), -(1051 / 3029), -(3354834 / 11133845),
    -(2192178737 / 7304709298), -(1760017649575 / 5477401595643),
    1, 0, 0, 0, 0],
  ![-(5 / 7), -(963 / 3029), -(3089189 / 11133845),
    -(2027738007 / 7304709298), -(1627763048717 / 5477401595643),
    -(1518811051261949 / 4415794839266231), 1, 0, 0, 0],
  ![-(41 / 63), -(893 / 3029), -(2865971 / 11133845),
    -(1881100503 / 7304709298), -(1509697178105 / 5477401595643),
    -(1408561517935355 / 4415794839266231),
    -(1444423476414783536 / 3675102233535782813), 1, 0, 0],
  ![-(13 / 21), -(840 / 3029), -(542387 / 2226769),
    -(889422340 / 3652354649), -(1434082146950 / 5477401595643),
    -(1338065551138682 / 4415794839266231),
    -(1372141434824927612 / 3675102233535782813),
    -(503644873903627025147 / 1003557538322298450899), 1, 0],
  ![-(37 / 63), -(805 / 3029), -(2579123 / 11133845),
    -(850704252 / 3652354649), -(1371762612668 / 5477401595643),
    -(1279890564942179 / 4415794839266231),
    -(1312431114375892414 / 3675102233535782813),
    -(481710145333908751425 / 1003557538322298450899),
    -(286934058981571001518729 / 358843898432320643688653), 1]
]

def yoshidaOddComparison10D : Fin 10 → ℚ := ![
  63 / 512,
  3029 / 4608,
  11133845 / 10855936,
  3652354649 / 2850264320,
  5477401595643 / 3740011160576,
  4415794839266231 / 2804429616969216,
  3675102233535782813 / 2260886957704310272,
  3010672614966895352697 / 1881652343570320800256,
  358843898432320643688653 / 256910729810508403430144,
  32550872422740888070024259 / 45932018999337042392147584
]
```

- [ ] **Step 3: Prove the shared exact obligations and both cast certificates**

Continue the module:

```lean
private theorem yoshidaOddComparison10L_isUnit :
    IsUnit yoshidaOddComparison10L := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have htri : yoshidaOddComparison10L.BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> simp_all [yoshidaOddComparison10L]
  rw [Matrix.det_of_lowerTriangular yoshidaOddComparison10L htri]
  norm_num [yoshidaOddComparison10L, Fin.prod_univ_succ]

private theorem yoshidaOddComparison10D_pos :
    ∀ i, 0 < yoshidaOddComparison10D i := by
  decide +kernel

set_option maxHeartbeats 10000000 in
private theorem yoshidaOddComparison10_factorization :
    yoshidaOddComparison10 =
      yoshidaOddComparison10L * Matrix.diagonal yoshidaOddComparison10D *
        yoshidaOddComparison10Lᴴ := by
  decide +kernel

set_option maxHeartbeats 10000000 in
theorem yoshidaOddComparison10_posDef_real : Matrix.PosDef
    ((Rat.castHom ℝ).mapMatrix yoshidaOddComparison10) := by
  exact rationalLDL_posDef_real
    yoshidaOddComparison10 yoshidaOddComparison10L yoshidaOddComparison10D
    yoshidaOddComparison10L_isUnit yoshidaOddComparison10D_pos
    yoshidaOddComparison10_factorization

set_option maxHeartbeats 10000000 in
theorem yoshidaOddComparison10_posDef_complex : Matrix.PosDef
    ((Rat.castHom ℂ).mapMatrix yoshidaOddComparison10) := by
  exact rationalLDL_posDef_complex
    yoshidaOddComparison10 yoshidaOddComparison10L yoshidaOddComparison10D
    yoshidaOddComparison10L_isUnit yoshidaOddComparison10D_pos
    yoshidaOddComparison10_factorization

end ArithmeticHodge.Analysis
```

- [ ] **Step 4: Verify GREEN and gates**

Run:

```bash
lake env lean -DwarningAsError=true YoshidaOddComparisonCertificateScratch.lean
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/YoshidaOddComparisonCertificate.lean
lake build ArithmeticHodge
```

Expected: all exit zero. Delete the scratch, run scans, print axioms for both certificate theorems, compare the stored payload to the research probe, inspect the exact module plus umbrella-import diff, and verify the 159-file legacy archive byte-for-byte.

- [ ] **Step 5: Commit**

```bash
git add ArithmeticHodge/Analysis/YoshidaOddComparisonCertificate.lean ArithmeticHodge.lean
git commit -m "add exact Yoshida odd comparison certificate"
```

## Downstream boundary

For the corrected odd Gram `G`, define

```text
U = (Rat.castHom ℝ).mapMatrix yoshidaOddComparison10.
```

Task 3 supplies `U.PosDef`; Task 2 then reduces `G.PosDef` to the 55 analytic inequalities

```text
U_ii <= Re(G_ii),
norm(G_ij) <= -U_ij,  i != j.
```

Those bounds must come from certified moment enclosures and the `1/40` correction budget. None is assumed or encoded in this algebraic plan.
