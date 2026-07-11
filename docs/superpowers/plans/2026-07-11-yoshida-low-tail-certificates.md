# Yoshida Low-Tail and Rational Certificate Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to implement this plan task by
> task with test-driven development and an independent review after each
> commit.

**Goal:** Isolate the algebraic low-mode/tail positivity argument and an exact
rational `LDLᴴ` certificate bridge needed by Yoshida's finite blocks.

**Architecture:** The infinite-dimensional argument is split at its genuine
boundary. A generic sesquilinear lemma proves strict positivity once corrected
low modes are orthogonal to a positive tail and their finite Gram matrix is
positive definite. A separate certificate lemma maps a rational matrix
factorization into Mathlib's complex `Matrix.PosDef`, so generated 10-by-10
and 200-by-200 data can be checked by the Lean kernel rather than trusted as
external numerics.

**Tech Stack:** Lean 4, Mathlib sesquilinear maps, submodules,
`Matrix.PosDef`, `Rat.castHom`, and exact finite matrix arithmetic.

## Global Constraints

- No `sorry`, `admit`, custom `axiom`, unsafe declaration, or RH-equivalent
  proof bypass.
- Preserve all 159 inventoried legacy untracked Lean research files.
- Keep the lemmas generic under `ArithmeticHodge.Analysis`; do not couple
  them to Bombieri tests or Yoshida's analytic constants.
- Every production module must strict-compile with
  `lake env lean -DwarningAsError=true`.
- Run the full `lake build ArithmeticHodge`, proof/naming scans, and an axiom
  audit before each production commit.
- Commit each task separately and obtain an independent post-commit review.

---

### Task 1: Orthogonal finite-block plus positive-tail theorem

**Files:**

- Create: `ArithmeticHodge/Analysis/HermitianLowTail.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `YoshidaLowTailScratch.lean` (temporary; delete before commit)

**Imports:**

```lean
import Mathlib.Analysis.Matrix.PosDef
```

**Produces:**

```lean
namespace ArithmeticHodge.Analysis

theorem sesquilinear_orthogonal_sum_self
    {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℂ E]
    (B : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ)
    (w : ι → E) (c : ι → ℂ) (v : E)
    (hleft : ∀ i, B (w i) v = 0)
    (hright : ∀ i, B v (w i) = 0) :
    B (∑ i, c i • w i + v) (∑ i, c i • w i + v) =
      star c ⬝ᵥ ((fun i j ↦ B (w i) (w j)) *ᵥ c) + B v v

theorem posDef_add_tail_strictPos
    {ι T : Type*} [Fintype ι] [Zero T]
    {A : Matrix ι ι ℂ} (hA : A.PosDef)
    (qTail : T → ℝ)
    (hqTail_nonneg : ∀ v, 0 ≤ qTail v)
    (hqTail_pos : ∀ v, v ≠ 0 → 0 < qTail v)
    {c : ι → ℂ} {v : T} (hne : c ≠ 0 ∨ v ≠ 0) :
    0 < (star c ⬝ᵥ (A *ᵥ c)).re + qTail v

theorem sesquilinear_orthogonal_sum_re_pos
    {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℂ E]
    (B : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ)
    (K : Submodule ℂ E) (w : ι → E) (c : ι → ℂ) (v : K)
    (hleft : ∀ i, B (w i) (v : E) = 0)
    (hright : ∀ i, B (v : E) (w i) = 0)
    (hgram : Matrix.PosDef (fun i j ↦ B (w i) (w j)))
    (htail_nonneg : ∀ x : K, 0 ≤ (B (x : E) (x : E)).re)
    (htail_pos : ∀ x : K, x ≠ 0 → 0 < (B (x : E) (x : E)).re)
    (hne : c ≠ 0 ∨ v ≠ 0) :
    0 < (B (∑ i, c i • w i + (v : E))
      (∑ i, c i • w i + (v : E))).re

end ArithmeticHodge.Analysis
```

- [ ] Create the temporary scratch import and exact theorem-use examples;
  record a strict RED failure because `HermitianLowTail` is absent.
- [ ] Implement `sesquilinear_orthogonal_sum_self` by expanding the two sums
  and eliminating both cross terms from `hleft` and `hright`.
- [ ] Implement `posDef_add_tail_strictPos` by splitting
  `c ≠ 0 ∨ v ≠ 0` and using `re_dotProduct_pos` or
  `re_dotProduct_nonneg` on the finite block.
- [ ] Derive `sesquilinear_orthogonal_sum_re_pos` by rewriting the exact
  orthogonal decomposition and applying the numeric lemma only to the tail
  subtype `K`.
- [ ] Strict-compile scratch and production, delete scratch, full-build, scan,
  axiom-audit, inspect the exact two-file diff, and commit as
  `formalize Hermitian low-tail positivity`.

### Task 2: Rational `LDLᴴ` certificate bridge

**Files:**

- Create: `ArithmeticHodge/Analysis/RationalPosDefCertificate.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `RationalPosDefCertificateScratch.lean` (temporary; delete before
  commit)

**Imports:**

```lean
import ArithmeticHodge.Analysis.HermitianLowTail
```

**Produces:**

```lean
namespace ArithmeticHodge.Analysis

theorem rationalLDL_posDef_complex
    {n : Type*} [Fintype n] [DecidableEq n]
    (A L : Matrix n n ℚ) (d : n → ℚ)
    (hL : IsUnit L) (hd : ∀ i, 0 < d i)
    (hA : A = L * Matrix.diagonal d * Lᴴ) :
    Matrix.PosDef ((Rat.castHom ℂ).mapMatrix A)

end ArithmeticHodge.Analysis
```

**Required concrete regression:**

```lean
example : Matrix.PosDef
    ((Rat.castHom ℂ).mapMatrix
      (!![(2 : ℚ), 1;
          1, 2] : Matrix (Fin 2) (Fin 2) ℚ)) := by
  let A : Matrix (Fin 2) (Fin 2) ℚ :=
    !![(2 : ℚ), 1;
       1, 2]
  let L : Matrix (Fin 2) (Fin 2) ℚ :=
    !![(1 : ℚ), 0;
       1 / 2, 1]
  let d : Fin 2 → ℚ := ![(2 : ℚ), 3 / 2]
  apply rationalLDL_posDef_complex A L d
  · rw [Matrix.isUnit_iff_isUnit_det]
    norm_num [L, Matrix.det_fin_two]
  · intro i
    fin_cases i <;> norm_num [d]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, L, d, Matrix.mul_apply, Matrix.vecMul, dotProduct]
```

- [ ] Write the concrete regression in the temporary scratch and record RED
  because `RationalPosDefCertificate` is absent.
- [ ] Map `IsUnit L` through `(Rat.castHom ℂ).mapMatrix`.
- [ ] Prove positivity of the cast diagonal using `Complex.pos_iff`, then
  transport the rational diagonal and conjugate-transpose identities.
- [ ] Apply `Matrix.IsUnit.posDef_star_right_conjugate_iff` to conclude complex
  positive definiteness.
- [ ] Record GREEN on the concrete 2-by-2 regression, strict-compile
  production, delete scratch, full-build, scan, axiom-audit, inspect the exact
  two-file diff, and commit as `add rational positive-definite certificates`.

### Task 3: Coercive Riesz correction through Lax--Milgram

**Files:**

- Create: `ArithmeticHodge/Analysis/CoerciveRieszCorrection.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `CoerciveRieszCorrectionScratch.lean` (temporary; delete before
  commit)

**Imports:**

```lean
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
```

**Produces:**

```lean
namespace ArithmeticHodge.Analysis

noncomputable def coerciveRieszCorrection
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    (ell : StrongDual ℝ V) : V

theorem coerciveRieszCorrection_apply
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    (ell : StrongDual ℝ V) (w : V) :
    B (coerciveRieszCorrection hB ell) w = ell w

theorem norm_coerciveRieszCorrection_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    (ell : StrongDual ℝ V) {mu : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ v, mu * ‖v‖ * ‖v‖ ≤ B v v) :
    ‖coerciveRieszCorrection hB ell‖ ≤ ‖ell‖ / mu

theorem coerciveRieszCorrection_energy_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    (ell : StrongDual ℝ V) {mu : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ v, mu * ‖v‖ * ‖v‖ ≤ B v v) :
    B (coerciveRieszCorrection hB ell)
      (coerciveRieszCorrection hB ell) ≤ ‖ell‖ ^ 2 / mu

end ArithmeticHodge.Analysis
```

- [ ] Write a temporary scratch importing the absent production module and
  checking all four interfaces; record the strict missing-module RED result.
- [ ] Define the correction as the inverse Lax--Milgram image of the
  Frechet--Riesz representative `(InnerProductSpace.toDual ℝ V).symm ell`.
- [ ] Prove the evaluation identity from
  `IsCoercive.continuousLinearEquivOfBilin_apply` and
  `InnerProductSpace.toDual_symm_apply`.
- [ ] Derive the norm bound by combining explicit coercivity with
  `ContinuousLinearMap.le_opNorm` and cancelling the norm of a nonzero
  correction; handle the zero correction separately.
- [ ] Derive the energy bound from the evaluation identity, the dual norm
  estimate, and the norm bound.
- [ ] Strict-compile scratch and production, delete scratch, full-build, scan,
  axiom-audit, inspect the exact two-file diff, and commit as
  `formalize coercive Riesz corrections`.

## Downstream use

Yoshida's analytic stages must produce corrected low modes orthogonal to the
coercive tail and a rational lower Gram matrix. Generated finite data may
supply rational `A`, `L`, and `d`, but Lean must prove the exact factorization,
unit condition, positive pivots, and comparison from the true Gram matrix to
the rational lower matrix. External Arb output is a generator, never a trusted
proof artifact.
