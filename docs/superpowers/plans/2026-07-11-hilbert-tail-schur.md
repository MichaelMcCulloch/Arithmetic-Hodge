# Hilbert Tail Schur Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize the source-faithful finite-low-mode plus completed-Hilbert-tail Schur complement used in Yoshida's positivity argument.

**Architecture:** Work entirely in an abstract complex Hilbert space `K`, after Yoshida's form-norm completion has already been constructed. Represent each bounded low-tail pairing by ordinary Riesz duality, subtract the Gram matrix of the representatives, prove the exact completion-of-the-square identity, and derive strict positivity plus entrywise correction bounds.

**Tech Stack:** Lean 4, Mathlib complex inner-product duality, finite matrices, Hermitian positive definiteness, and finite sums.

## Global Constraints

- No `sorry`, `admit`, custom `axiom`, unsafe declaration, `native_decide`, or RH-equivalent proof bypass.
- Preserve all 159 inventoried legacy untracked Lean research files byte-for-byte.
- Work directly on `main` as explicitly authorized by the user, committing the coherent verified task.
- Only one implementation subagent may run; it owns only `ArithmeticHodge/Analysis/HilbertTailSchur.lean`, the one umbrella import line, and its temporary scratch.
- First run the strict RED scratch and confirm that it fails only because the production module is absent.
- The production module and interface scratch must pass `lake env lean -DwarningAsError=true`; the repository must pass `lake build ArithmeticHodge`.
- Run the global forbidden-proof and scratch-naming scans, audit every exported declaration, and require only `[propext, Classical.choice, Quot.sound]` or a subset.
- Keep this generic layer independent of circle `L²`, Fourier normalization, Yoshida constants, Bombieri tests, and RH statements.
- Use Mathlib's convention that `⟪v, x⟫_ℂ` is conjugate-linear in `v` and linear in `x`.
- Do not add a Lax--Milgram or ordinary-`L²` continuity hypothesis; `K` is already the completed form Hilbert space.

---

### Task 1: Generic completed-tail Schur complement

**Files:**

- Create: `ArithmeticHodge/Analysis/HilbertTailSchur.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `HilbertTailSchurScratch.lean` (temporary; delete before commit)

**Interfaces:**

- Consumes: `Matrix.PosDef`, `InnerProductSpace.toDual`, and the finite-matrix notation already imported by `ArithmeticHodge.Analysis.HermitianLowTail`.
- Produces: `hilbertTailRieszCorrection`, `hilbertTailRieszCorrection_inner`, `norm_hilbertTailRieszCorrection`, `hilbertTailCorrectedGram`, `hilbertTail_complete_square`, `hilbertTail_quadratic_re_pos`, and `norm_hilbertTail_correction_pairing_le`.

- [ ] **Step 1: Write the strict failing interface test**

Create `HilbertTailSchurScratch.lean`:

```lean
import ArithmeticHodge.Analysis.HilbertTailSchur

set_option autoImplicit false

namespace ArithmeticHodge.Analysis

#check hilbertTailRieszCorrection
#check hilbertTailRieszCorrection_inner
#check norm_hilbertTailRieszCorrection
#check hilbertTailCorrectedGram
#check hilbertTail_complete_square
#check hilbertTail_quadratic_re_pos
#check norm_hilbertTail_correction_pairing_le

end ArithmeticHodge.Analysis
```

- [ ] **Step 2: Run RED and record the expected failure**

Run:

```bash
lake env lean -DwarningAsError=true HilbertTailSchurScratch.lean
```

Expected: nonzero exit because `ArithmeticHodge.Analysis.HilbertTailSchur` does not exist. Any syntax or unrelated elaboration error is not an acceptable RED.

- [ ] **Step 3: Implement the minimal production module**

Create `ArithmeticHodge/Analysis/HilbertTailSchur.lean`:

```lean
import ArithmeticHodge.Analysis.HermitianLowTail
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace

namespace ArithmeticHodge.Analysis

noncomputable section

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

noncomputable def hilbertTailRieszCorrection
    (ell : StrongDual ℂ K) : K :=
  (InnerProductSpace.toDual ℂ K).symm ell

@[simp] theorem hilbertTailRieszCorrection_inner
    (ell : StrongDual ℂ K) (x : K) :
    ⟪hilbertTailRieszCorrection ell, x⟫_ℂ = ell x := by
  exact InnerProductSpace.toDual_symm_apply

@[simp] theorem norm_hilbertTailRieszCorrection
    (ell : StrongDual ℂ K) :
    ‖hilbertTailRieszCorrection ell‖ = ‖ell‖ := by
  exact (InnerProductSpace.toDual ℂ K).symm.norm_map ell

noncomputable def hilbertTailCorrectedGram
    {ι : Type*} (A : Matrix ι ι ℂ) (ell : ι → StrongDual ℂ K) :
    Matrix ι ι ℂ :=
  fun i j ↦ A i j -
    ⟪hilbertTailRieszCorrection (ell i), hilbertTailRieszCorrection (ell j)⟫_ℂ

theorem hilbertTail_complete_square
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (ell : ι → StrongDual ℂ K)
    (c : ι → ℂ) (x : K) :
    star c ⬝ᵥ (A *ᵥ c) +
          ∑ i, star (c i) * ell i x +
          ∑ i, c i * star (ell i x) + ⟪x, x⟫_ℂ =
      star c ⬝ᵥ (hilbertTailCorrectedGram A ell *ᵥ c) +
        ⟪x + ∑ i, c i • hilbertTailRieszCorrection (ell i),
          x + ∑ i, c i • hilbertTailRieszCorrection (ell i)⟫_ℂ := by
  classical
  let v : ι → K := fun i ↦ hilbertTailRieszCorrection (ell i)
  have hv (i : ι) (y : K) : ⟪v i, y⟫_ℂ = ell i y := by
    simp [v]
  have hxv (i : ι) : ⟪x, v i⟫_ℂ = star (ell i x) := by
    rw [← inner_conj_symm, hv]
    rfl
  have hswap :
      (∑ i, ∑ j, c i * (star (c j) * ell j (v i))) =
        ∑ i, ∑ j, star (c i) * (ell i (v j) * c j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring_nf
  let C : ℂ := ∑ i, ∑ j, star (c i) * ell i (v j) * c j
  have hmatrix :
      star c ⬝ᵥ ((fun i j ↦ A i j - ⟪v i, v j⟫_ℂ) *ᵥ c) =
        star c ⬝ᵥ (A *ᵥ c) - C := by
    simp only [dotProduct, mulVec, Finset.mul_sum, sub_mul, mul_sub, hv, C,
      Pi.star_apply]
    simp_rw [Finset.sum_sub_distrib]
    ring_nf
  have htail :
      ⟪x + ∑ i, c i • v i, x + ∑ i, c i • v i⟫_ℂ =
        ⟪x, x⟫_ℂ +
          ∑ i, star (c i) * ell i x +
          ∑ i, c i * star (ell i x) + C := by
    simp only [inner_add_add_self, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, hv, hxv, starRingEnd_apply, C]
    simp_rw [Finset.mul_sum]
    rw [hswap]
    ring_nf
  change star c ⬝ᵥ (A *ᵥ c) +
          ∑ i, star (c i) * ell i x +
          ∑ i, c i * star (ell i x) + ⟪x, x⟫_ℂ =
      star c ⬝ᵥ ((fun i j ↦ A i j - ⟪v i, v j⟫_ℂ) *ᵥ c) +
        ⟪x + ∑ i, c i • v i, x + ∑ i, c i • v i⟫_ℂ
  rw [hmatrix, htail]
  ring_nf

theorem hilbertTail_quadratic_re_pos
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (ell : ι → StrongDual ℂ K)
    (hG : Matrix.PosDef (hilbertTailCorrectedGram A ell))
    (c : ι → ℂ) (x : K) (hne : c ≠ 0 ∨ x ≠ 0) :
    0 < (star c ⬝ᵥ (A *ᵥ c) +
          ∑ i, star (c i) * ell i x +
          ∑ i, c i * star (ell i x) + ⟪x, x⟫_ℂ).re := by
  rw [hilbertTail_complete_square]
  rw [Complex.add_re]
  by_cases hc : c = 0
  · have hx : x ≠ 0 := by
      rcases hne with hcne | hx
      · exact (hcne hc).elim
      · exact hx
    subst c
    have hmatrix :
        star (0 : ι → ℂ) ⬝ᵥ
          (hilbertTailCorrectedGram A ell *ᵥ (0 : ι → ℂ)) = 0 := by
      simp
    have hsum :
        ∑ i, (0 : ι → ℂ) i • hilbertTailRieszCorrection (ell i) = 0 := by
      simp
    rw [hmatrix, hsum]
    simp only [Complex.zero_re, zero_add, add_zero]
    rw [inner_self_eq_norm_sq_to_K]
    change 0 < ((‖x‖ : ℂ) ^ 2).re
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_pos_of_pos (norm_pos_iff.mpr hx)
  · have htail : 0 ≤
        (⟪x + ∑ i, c i • hilbertTailRieszCorrection (ell i),
          x + ∑ i, c i • hilbertTailRieszCorrection (ell i)⟫_ℂ).re :=
      @inner_self_nonneg ℂ K _ _ _
        (x := x + ∑ i, c i • hilbertTailRieszCorrection (ell i))
    exact add_pos_of_pos_of_nonneg (hG.re_dotProduct_pos hc) htail

theorem norm_hilbertTail_correction_pairing_le
    (ell₁ ell₂ : StrongDual ℂ K) :
    ‖⟪hilbertTailRieszCorrection ell₁, hilbertTailRieszCorrection ell₂⟫_ℂ‖ ≤
      ‖ell₁‖ * ‖ell₂‖ := by
  simpa using (@norm_inner_le_norm ℂ K _ _ _
    (hilbertTailRieszCorrection ell₁) (hilbertTailRieszCorrection ell₂))

end

end ArithmeticHodge.Analysis
```

Add exactly one umbrella import immediately after `HermitianLowTail`:

```lean
import ArithmeticHodge.Analysis.HilbertTailSchur
```

- [ ] **Step 4: Verify GREEN, axioms, and repository invariants**

Run:

```bash
lake env lean -DwarningAsError=true HilbertTailSchurScratch.lean
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/HilbertTailSchur.lean
lake build ArithmeticHodge
```

Create a temporary audit importing the module and run `#print axioms` for all five theorem declarations. Require only `propext`, `Classical.choice`, and `Quot.sound` or a subset. Delete both temporary files.

Run:

```bash
if rg -n --glob '*.lean' '^\s*(private\s+)?axiom\b|^\s*sorry\b|\bby\s+sorry\b|^\s*admit\b|\bby\s+admit\b|^\s*unsafe\b' ArithmeticHodge; then exit 1; fi
if rg -n '_scratch|Scratch' ArithmeticHodge --glob '*.lean'; then exit 1; fi
git diff --check
```

Compare every filename in `docs/research/legacy-lean-inventory-2026-07-11.tsv` against `refs/archive/legacy-lean-2026-07-11` with `git hash-object` and require exactly 159 byte-identical files. Inspect `git diff -- ArithmeticHodge/Analysis/HilbertTailSchur.lean ArithmeticHodge.lean` and confirm no other repository file changed.

- [ ] **Step 5: Commit the verified increment**

```bash
git add ArithmeticHodge/Analysis/HilbertTailSchur.lean ArithmeticHodge.lean
git commit -m "add Hilbert-tail Schur complement"
```
