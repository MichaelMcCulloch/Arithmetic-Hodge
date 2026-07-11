# Hermitian Tail Correction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn complex Lax--Milgram coercivity into quantitative, Hermitian-orthogonal low-mode corrections and a reusable finite-low-mode plus positive-tail positivity theorem.

**Architecture:** Extend the existing complex Lax--Milgram bridge with norm and energy estimates. Put restriction, correction, orthogonality, exact Gram subtraction, and entrywise correction bounds in one focused module; put finite-family decomposition and the final call to `HermitianLowTail` in a separate module. The convention is fixed throughout: `B` is conjugate-linear in its first slot, `tailCorrection` solves `B v x = B u x`, and Hermitian symmetry supplies the reversed zero pairing.

**Tech Stack:** Lean 4, Mathlib continuous sesquilinear maps, Lax--Milgram, closed submodules, finite matrices, and exact real inequalities.

## Global Constraints

- No `sorry`, `admit`, custom `axiom`, unsafe declaration, `native_decide`, or RH-equivalent proof bypass.
- Preserve all 159 inventoried legacy untracked Lean research files.
- Work directly on `main` as explicitly authorized by the user, committing each coherent verified task.
- Run only one implementation subagent at a time; agents must own disjoint production and scratch files.
- Every new behavior must first have a strict-compiling scratch that fails for the expected missing declaration or missing module.
- Every production module must pass `lake env lean -DwarningAsError=true <file>` and `lake build ArithmeticHodge`.
- Before each commit, scan production Lean for forbidden proof bypasses and scratch naming, audit dependencies, and require every exported theorem to use only `[propext, Classical.choice, Quot.sound]` or a subset.
- Respect Mathlib's slot convention exactly: `B v x = ell x`; a Hermitian flip is `B x v = star (ell x)`, never `ell x` without conjugation.
- Keep the generic correction layer independent of Fourier normalization, Yoshida constants, Bombieri tests, and RH statements.
- Do not conflate a coupling norm `C`, its square `C ^ 2`, and a source coupling-square sum `S`; correction energy is bounded by `C ^ 2 / mu`.

---

### Task 1: Quantitative complex Lax--Milgram bounds

**Files:**

- Modify: `ArithmeticHodge/Analysis/ComplexCoerciveRieszCorrection.lean`
- Test: `ComplexCoerciveBoundsScratch.lean` (temporary; delete before commit)

**Interfaces:**

- Consumes: `complexLaxMilgramSolution`, `complexLaxMilgramSolution_apply`.
- Produces: `norm_complexLaxMilgramSolution_le`, `complexLaxMilgramSolution_energy_le`, and `complexLaxMilgramSolution_energy_le_of_norm_sq`.

- [ ] **Step 1: Write the strict failing interface test**

Create `ComplexCoerciveBoundsScratch.lean`:

```lean
import ArithmeticHodge.Analysis.ComplexCoerciveRieszCorrection

set_option autoImplicit false

open scoped ComplexOrder

namespace ArithmeticHodge.Analysis

#check norm_complexLaxMilgramSolution_le
#check complexLaxMilgramSolution_energy_le
#check complexLaxMilgramSolution_energy_le_of_norm_sq

end ArithmeticHodge.Analysis
```

- [ ] **Step 2: Run the RED and record the expected failure**

Run:

```bash
lake env lean -DwarningAsError=true ComplexCoerciveBoundsScratch.lean
```

Expected: failure because `norm_complexLaxMilgramSolution_le` and the two energy declarations are unknown; no syntax, import, or unrelated elaboration error is acceptable.

- [ ] **Step 3: Add the minimal quantitative theorems**

Append inside `ArithmeticHodge.Analysis` and its existing `noncomputable section`:

```lean
theorem norm_complexLaxMilgramSolution_le
    [CompleteSpace E] {B : E →L⋆[ℂ] E →L[ℂ] ℂ}
    (hB : IsCoercive (complexToRealForm B))
    (ell : StrongDual ℂ E) {mu : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ x, mu * ‖x‖ * ‖x‖ ≤ (B x x).re) :
    ‖complexLaxMilgramSolution hB ell‖ ≤ ‖ell‖ / mu := by
  let v := complexLaxMilgramSolution hB ell
  by_cases hv : v = 0
  · change ‖v‖ ≤ ‖ell‖ / mu
    rw [hv, norm_zero]
    exact div_nonneg (norm_nonneg ell) hmu.le
  · have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have henergy : mu * ‖v‖ * ‖v‖ ≤ (ell v).re := by
      simpa [v, complexLaxMilgramSolution_apply] using hcoercive v
    have hdual : (ell v).re ≤ ‖ell‖ * ‖v‖ :=
      (Complex.re_le_norm _).trans (ell.le_opNorm v)
    have hcancel : mu * ‖v‖ ≤ ‖ell‖ := by nlinarith
    change ‖v‖ ≤ ‖ell‖ / mu
    exact (le_div_iff₀ hmu).2 (by nlinarith)

theorem complexLaxMilgramSolution_energy_le
    [CompleteSpace E] {B : E →L⋆[ℂ] E →L[ℂ] ℂ}
    (hB : IsCoercive (complexToRealForm B))
    (ell : StrongDual ℂ E) {mu : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ x, mu * ‖x‖ * ‖x‖ ≤ (B x x).re) :
    (B (complexLaxMilgramSolution hB ell)
      (complexLaxMilgramSolution hB ell)).re ≤ ‖ell‖ ^ 2 / mu := by
  let v := complexLaxMilgramSolution hB ell
  rw [complexLaxMilgramSolution_apply]
  calc
    (ell v).re ≤ ‖ell‖ * ‖v‖ :=
      (Complex.re_le_norm _).trans (ell.le_opNorm v)
    _ ≤ ‖ell‖ * (‖ell‖ / mu) :=
      mul_le_mul_of_nonneg_left
        (norm_complexLaxMilgramSolution_le hB ell hmu hcoercive)
        (norm_nonneg ell)
    _ = ‖ell‖ ^ 2 / mu := by ring

theorem complexLaxMilgramSolution_energy_le_of_norm_sq
    [CompleteSpace E] {B : E →L⋆[ℂ] E →L[ℂ] ℂ}
    (hB : IsCoercive (complexToRealForm B))
    (ell : StrongDual ℂ E) {mu S : ℝ} (hmu : 0 < mu)
    (hcoercive : ∀ x, mu * ‖x‖ * ‖x‖ ≤ (B x x).re)
    (hellSq : ‖ell‖ ^ 2 ≤ S) :
    (B (complexLaxMilgramSolution hB ell)
      (complexLaxMilgramSolution hB ell)).re ≤ S / mu := by
  exact (complexLaxMilgramSolution_energy_le hB ell hmu hcoercive).trans
    (div_le_div_of_nonneg_right hellSq hmu.le)
```

- [ ] **Step 4: Verify GREEN and production gates**

Run:

```bash
lake env lean -DwarningAsError=true ComplexCoerciveBoundsScratch.lean
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/ComplexCoerciveRieszCorrection.lean
lake build ArithmeticHodge
```

Expected: all exit zero with no warnings. Delete the scratch, run the global proof/naming scans and `#print axioms` on all three theorems, and inspect that only the intended production file changed.

- [ ] **Step 5: Commit**

```bash
git add ArithmeticHodge/Analysis/ComplexCoerciveRieszCorrection.lean
git commit -m "bound complex Lax-Milgram corrections"
```

---

### Task 2: Hermitian tail correction and Gram control

**Files:**

- Create: `ArithmeticHodge/Analysis/HermitianTailCorrection.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `HermitianTailCorrectionScratch.lean` (temporary; delete before commit)

**Interfaces:**

- Consumes: the three quantitative Task 1 theorems and the existing complex correction bridge.
- Produces: restriction, Hermitian restriction, low-mode functional, tail correction, both orthogonality directions, exact Gram subtraction, operator-norm bounds, and explicit-coupling bounds.

- [ ] **Step 1: Write the strict missing-module RED**

Create `HermitianTailCorrectionScratch.lean`:

```lean
import ArithmeticHodge.Analysis.HermitianTailCorrection

set_option autoImplicit false

namespace ArithmeticHodge.Analysis

#check restrictedForm
#check restrictedForm_isSymm
#check lowModeFunctional
#check tailCorrection
#check tailCorrection_spec
#check correctedLowMode
#check correctedLowMode_orthogonal_right
#check correctedLowMode_orthogonal_left
#check correctedLowMode_gram
#check norm_tailCorrection_le
#check tailCorrection_energy_le
#check norm_tailCorrection_pairing_le
#check norm_correctedLowMode_gram_sub_le
#check norm_tailCorrection_le_of_bound
#check tailCorrection_energy_le_of_bound
#check norm_tailCorrection_pairing_le_of_bound

end ArithmeticHodge.Analysis
```

- [ ] **Step 2: Run the RED and record the expected failure**

Run:

```bash
lake env lean -DwarningAsError=true HermitianTailCorrectionScratch.lean
```

Expected: failure because the imported production module does not exist.

- [ ] **Step 3: Implement restriction, correction, orthogonality, and exact Gram subtraction**

Create the module with this boundary and proofs:

```lean
import ArithmeticHodge.Analysis.ComplexCoerciveRieszCorrection

set_option autoImplicit false

open scoped ComplexConjugate ComplexOrder

namespace ArithmeticHodge.Analysis

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def restrictedForm (B : H →L⋆[ℂ] H →L[ℂ] ℂ) (K : Submodule ℂ H) :
    K →L⋆[ℂ] K →L[ℂ] ℂ :=
  B.bilinearComp K.subtypeL K.subtypeL

@[simp] theorem restrictedForm_apply
    (B : H →L⋆[ℂ] H →L[ℂ] ℂ) (K : Submodule ℂ H) (x y : K) :
    restrictedForm B K x y = B (x : H) (y : H) := rfl

theorem restrictedForm_isSymm
    {B : H →L⋆[ℂ] H →L[ℂ] ℂ} (K : Submodule ℂ H)
    (hHerm : B.toLinearMap₁₂.IsSymm) :
    (restrictedForm B K).toLinearMap₁₂.IsSymm := by
  constructor
  intro x y
  exact hHerm.eq (x : H) (y : H)

def lowModeFunctional (B : H →L⋆[ℂ] H →L[ℂ] ℂ)
    (K : Submodule ℂ H) (u : H) : StrongDual ℂ K :=
  (B u).comp K.subtypeL

@[simp] theorem lowModeFunctional_apply
    (B : H →L⋆[ℂ] H →L[ℂ] ℂ) (K : Submodule ℂ H) (u : H) (x : K) :
    lowModeFunctional B K u x = B u (x : H) := rfl

def tailCorrection (B : H →L⋆[ℂ] H →L[ℂ] ℂ)
    (K : Submodule ℂ H) [completeK : CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K))) (u : H) : K :=
  @complexLaxMilgramSolution K inferInstance inferInstance completeK _ hcoercive
    (lowModeFunctional B K u)

@[simp] theorem tailCorrection_spec
    (B : H →L⋆[ℂ] H →L[ℂ] ℂ) (K : Submodule ℂ H)
    [completeK : CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K))) (u : H) (x : K) :
    B (tailCorrection B K hcoercive u : H) (x : H) = B u (x : H) := by
  exact @complexLaxMilgramSolution_apply K inferInstance inferInstance completeK _ hcoercive
    (lowModeFunctional B K u) x

def correctedLowMode (B : H →L⋆[ℂ] H →L[ℂ] ℂ)
    (K : Submodule ℂ H) [CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K))) (u : H) : H :=
  u - (tailCorrection B K hcoercive u : H)

theorem correctedLowMode_orthogonal_right
    (B : H →L⋆[ℂ] H →L[ℂ] ℂ) (K : Submodule ℂ H) [CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K))) (u : H) (x : K) :
    B (correctedLowMode B K hcoercive u) (x : H) = 0 := by
  simp [correctedLowMode, tailCorrection_spec]

theorem correctedLowMode_orthogonal_left
    {B : H →L⋆[ℂ] H →L[ℂ] ℂ} (K : Submodule ℂ H) [CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K)))
    (hHerm : B.toLinearMap₁₂.IsSymm) (u : H) (x : K) :
    B (x : H) (correctedLowMode B K hcoercive u) = 0 := by
  calc
    B (x : H) (correctedLowMode B K hcoercive u) =
        star (B (correctedLowMode B K hcoercive u) (x : H)) :=
      (hHerm.eq (correctedLowMode B K hcoercive u) (x : H)).symm
    _ = 0 := by rw [correctedLowMode_orthogonal_right]; simp

theorem correctedLowMode_gram
    {B : H →L⋆[ℂ] H →L[ℂ] ℂ} (K : Submodule ℂ H) [CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K)))
    (hHerm : B.toLinearMap₁₂.IsSymm) (u z : H) :
    B (correctedLowMode B K hcoercive u) (correctedLowMode B K hcoercive z) =
      B u z - B (tailCorrection B K hcoercive u : H)
        (tailCorrection B K hcoercive z : H) := by
  let vu := tailCorrection B K hcoercive u
  let vz := tailCorrection B K hcoercive z
  have hz : B (vu : H) (vz : H) = B (vu : H) z := by
    calc
      B (vu : H) (vz : H) = star (B (vz : H) (vu : H)) :=
        (hHerm.eq (vz : H) (vu : H)).symm
      _ = star (B z (vu : H)) := by rw [tailCorrection_spec B K hcoercive z vu]
      _ = B (vu : H) z := hHerm.eq z (vu : H)
  calc
    B (correctedLowMode B K hcoercive u) (correctedLowMode B K hcoercive z) =
        B (correctedLowMode B K hcoercive u) z := by
      rw [show correctedLowMode B K hcoercive z = z - (vz : H) by rfl, map_sub,
        correctedLowMode_orthogonal_right, sub_zero]
    _ = B u z - B (vu : H) z := by
      rw [show correctedLowMode B K hcoercive u = u - (vu : H) by rfl, map_sub]
      rfl
    _ = B u z - B (vu : H) (vz : H) := by rw [hz]
```

- [ ] **Step 4: Add operator-norm and explicit-coupling estimates**

Continue the same module with the following exact statements. The operator-norm variants apply Task 1 to the restricted form; the explicit variants use `tailCorrection_spec`, `Complex.re_le_norm`, `ContinuousLinearMap.le_opNorm`, and cancellation of the nonzero correction norm exactly as in Task 1.

```lean
theorem norm_tailCorrection_le
    (B : H →L⋆[ℂ] H →L[ℂ] ℂ) (K : Submodule ℂ H) [completeK : CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K)))
    (u : H) {mu : ℝ} (hmu : 0 < mu)
    (htail : ∀ x : K, mu * ‖x‖ * ‖x‖ ≤ (B (x : H) (x : H)).re) :
    ‖tailCorrection B K hcoercive u‖ ≤
      ContinuousLinearMap.opNorm (lowModeFunctional B K u) / mu := by
  exact @norm_complexLaxMilgramSolution_le K inferInstance inferInstance completeK
    (restrictedForm B K) hcoercive (lowModeFunctional B K u) mu hmu (by simpa using htail)

theorem tailCorrection_energy_le
    (B : H →L⋆[ℂ] H →L[ℂ] ℂ) (K : Submodule ℂ H) [completeK : CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K)))
    (u : H) {mu : ℝ} (hmu : 0 < mu)
    (htail : ∀ x : K, mu * ‖x‖ * ‖x‖ ≤ (B (x : H) (x : H)).re) :
    (B (tailCorrection B K hcoercive u : H)
      (tailCorrection B K hcoercive u : H)).re ≤
      ContinuousLinearMap.opNorm (lowModeFunctional B K u) ^ 2 / mu := by
  exact @complexLaxMilgramSolution_energy_le K inferInstance inferInstance completeK
    (restrictedForm B K) hcoercive (lowModeFunctional B K u) mu hmu (by simpa using htail)

theorem norm_tailCorrection_pairing_le
    (B : H →L⋆[ℂ] H →L[ℂ] ℂ) (K : Submodule ℂ H) [CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K)))
    (u z : H) {mu : ℝ} (hmu : 0 < mu)
    (htail : ∀ x : K, mu * ‖x‖ * ‖x‖ ≤ (B (x : H) (x : H)).re) :
    ‖B (tailCorrection B K hcoercive u : H)
        (tailCorrection B K hcoercive z : H)‖ ≤
      ContinuousLinearMap.opNorm (lowModeFunctional B K u) *
        ContinuousLinearMap.opNorm (lowModeFunctional B K z) / mu := by
  let vz := tailCorrection B K hcoercive z
  calc
    ‖B (tailCorrection B K hcoercive u : H) (vz : H)‖ = ‖lowModeFunctional B K u vz‖ := by
      rw [lowModeFunctional_apply, tailCorrection_spec B K hcoercive u vz]
    _ ≤ ContinuousLinearMap.opNorm (lowModeFunctional B K u) * ‖vz‖ :=
      (lowModeFunctional B K u).le_opNorm vz
    _ ≤ ContinuousLinearMap.opNorm (lowModeFunctional B K u) *
        (ContinuousLinearMap.opNorm (lowModeFunctional B K z) / mu) :=
      mul_le_mul_of_nonneg_left (norm_tailCorrection_le B K hcoercive z hmu htail)
        (ContinuousLinearMap.opNorm_nonneg _)
    _ = ContinuousLinearMap.opNorm (lowModeFunctional B K u) *
        ContinuousLinearMap.opNorm (lowModeFunctional B K z) / mu := by ring

theorem norm_correctedLowMode_gram_sub_le
    {B : H →L⋆[ℂ] H →L[ℂ] ℂ} (K : Submodule ℂ H) [CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K)))
    (hHerm : B.toLinearMap₁₂.IsSymm) (u z : H)
    {mu : ℝ} (hmu : 0 < mu)
    (htail : ∀ x : K, mu * ‖x‖ * ‖x‖ ≤ (B (x : H) (x : H)).re) :
    ‖B (correctedLowMode B K hcoercive u) (correctedLowMode B K hcoercive z) - B u z‖ ≤
      ContinuousLinearMap.opNorm (lowModeFunctional B K u) *
        ContinuousLinearMap.opNorm (lowModeFunctional B K z) / mu := by
  rw [correctedLowMode_gram K hcoercive hHerm]
  simpa using norm_tailCorrection_pairing_le B K hcoercive u z hmu htail
```

Add the explicit-coupling statements and proofs:

```lean
theorem norm_tailCorrection_le_of_bound
    (B : H →L⋆[ℂ] H →L[ℂ] ℂ) (K : Submodule ℂ H) [CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K)))
    (u : H) {mu C : ℝ} (hmu : 0 < mu) (hC : 0 ≤ C)
    (htail : ∀ x : K, mu * ‖x‖ * ‖x‖ ≤ (B (x : H) (x : H)).re)
    (hbound : ∀ x : K, ‖B u (x : H)‖ ≤ C * ‖x‖) :
    ‖tailCorrection B K hcoercive u‖ ≤ C / mu := by
  let v := tailCorrection B K hcoercive u
  by_cases hv : v = 0
  · change ‖v‖ ≤ C / mu
    rw [hv, norm_zero]
    exact div_nonneg hC hmu.le
  · have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have henergy : mu * ‖v‖ * ‖v‖ ≤ C * ‖v‖ := by
      calc
        mu * ‖v‖ * ‖v‖ ≤ (B (v : H) (v : H)).re := htail v
        _ = (B u (v : H)).re :=
          congrArg Complex.re (tailCorrection_spec B K hcoercive u v)
        _ ≤ ‖B u (v : H)‖ := Complex.re_le_norm _
        _ ≤ C * ‖v‖ := hbound v
    have hcancel : mu * ‖v‖ ≤ C := by nlinarith
    change ‖v‖ ≤ C / mu
    exact (le_div_iff₀ hmu).2 (by nlinarith)

theorem tailCorrection_energy_le_of_bound
    (B : H →L⋆[ℂ] H →L[ℂ] ℂ) (K : Submodule ℂ H) [CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K)))
    (u : H) {mu C : ℝ} (hmu : 0 < mu) (hC : 0 ≤ C)
    (htail : ∀ x : K, mu * ‖x‖ * ‖x‖ ≤ (B (x : H) (x : H)).re)
    (hbound : ∀ x : K, ‖B u (x : H)‖ ≤ C * ‖x‖) :
    (B (tailCorrection B K hcoercive u : H)
      (tailCorrection B K hcoercive u : H)).re ≤ C ^ 2 / mu := by
  let v := tailCorrection B K hcoercive u
  calc
    (B (v : H) (v : H)).re = (B u (v : H)).re :=
      congrArg Complex.re (tailCorrection_spec B K hcoercive u v)
    _ ≤ ‖B u (v : H)‖ := Complex.re_le_norm _
    _ ≤ C * ‖v‖ := hbound v
    _ ≤ C * (C / mu) :=
      mul_le_mul_of_nonneg_left
        (norm_tailCorrection_le_of_bound B K hcoercive u hmu hC htail hbound) hC
    _ = C ^ 2 / mu := by ring

theorem norm_tailCorrection_pairing_le_of_bound
    (B : H →L⋆[ℂ] H →L[ℂ] ℂ) (K : Submodule ℂ H) [CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K)))
    (u z : H) {mu Cu Cz : ℝ} (hmu : 0 < mu) (hCu : 0 ≤ Cu) (hCz : 0 ≤ Cz)
    (htail : ∀ x : K, mu * ‖x‖ * ‖x‖ ≤ (B (x : H) (x : H)).re)
    (hboundu : ∀ x : K, ‖B u (x : H)‖ ≤ Cu * ‖x‖)
    (hboundz : ∀ x : K, ‖B z (x : H)‖ ≤ Cz * ‖x‖) :
    ‖B (tailCorrection B K hcoercive u : H)
      (tailCorrection B K hcoercive z : H)‖ ≤ Cu * Cz / mu := by
  let vz := tailCorrection B K hcoercive z
  calc
    ‖B (tailCorrection B K hcoercive u : H) (vz : H)‖ = ‖B u (vz : H)‖ :=
      congrArg norm (tailCorrection_spec B K hcoercive u vz)
    _ ≤ Cu * ‖vz‖ := hboundu vz
    _ ≤ Cu * (Cz / mu) :=
      mul_le_mul_of_nonneg_left
        (norm_tailCorrection_le_of_bound B K hcoercive z hmu hCz htail hboundz) hCu
    _ = Cu * Cz / mu := by ring

end

end ArithmeticHodge.Analysis
```

Do not introduce Fourier-specific aliases or constants.

- [ ] **Step 5: Verify GREEN and production gates**

Run:

```bash
lake env lean -DwarningAsError=true HermitianTailCorrectionScratch.lean
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/HermitianTailCorrection.lean
lake build ArithmeticHodge
```

Expected: all exit zero. Delete the scratch, run global scans, audit every exported theorem, inspect the exact new-module plus umbrella-import diff, and verify the 159-file legacy inventory.

- [ ] **Step 6: Commit**

```bash
git add ArithmeticHodge/Analysis/HermitianTailCorrection.lean ArithmeticHodge.lean
git commit -m "formalize Hermitian tail corrections"
```

---

### Task 3: Finite corrected-mode decomposition and positivity

**Files:**

- Create: `ArithmeticHodge/Analysis/HermitianTailDecomposition.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `HermitianTailDecompositionScratch.lean` (temporary; delete before commit)

**Interfaces:**

- Consumes: `HermitianTailCorrection` and `sesquilinear_orthogonal_sum_re_pos` from `HermitianLowTail`.
- Produces: positivity for a corrected finite family plus tail, algebraic transport of any low-plus-tail decomposition to corrected modes, and strict positivity of any nonzero decomposed vector.

- [ ] **Step 1: Write the strict missing-module RED**

Create `HermitianTailDecompositionScratch.lean`:

```lean
import ArithmeticHodge.Analysis.HermitianTailDecomposition

set_option autoImplicit false

namespace ArithmeticHodge.Analysis

#check correctedLowModes_sum_re_pos
#check exists_correctedLowMode_decomposition
#check correctedLowModes_re_pos_of_decomposition

end ArithmeticHodge.Analysis
```

- [ ] **Step 2: Run the RED**

Run:

```bash
lake env lean -DwarningAsError=true HermitianTailDecompositionScratch.lean
```

Expected: failure because `HermitianTailDecomposition` does not exist.

- [ ] **Step 3: Implement the finite-family bridge**

Create the module with the following complete content:

```lean
import ArithmeticHodge.Analysis.HermitianLowTail
import ArithmeticHodge.Analysis.HermitianTailCorrection

set_option autoImplicit false

open scoped ComplexConjugate ComplexOrder

namespace ArithmeticHodge.Analysis

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem correctedLowModes_sum_re_pos
    {ι : Type*} [Fintype ι]
    {B : H →L⋆[ℂ] H →L[ℂ] ℂ} (K : Submodule ℂ H) [CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K)))
    (hHerm : B.toLinearMap₁₂.IsSymm) (u : ι → H) (c : ι → ℂ) (v : K)
    {mu : ℝ} (hmu : 0 < mu)
    (htail : ∀ x : K, mu * ‖x‖ * ‖x‖ ≤ (B (x : H) (x : H)).re)
    (hgram : Matrix.PosDef
      (fun i j ↦ B (correctedLowMode B K hcoercive (u i))
        (correctedLowMode B K hcoercive (u j))))
    (hne : c ≠ 0 ∨ v ≠ 0) :
    0 < (B
      (∑ i, c i • correctedLowMode B K hcoercive (u i) + (v : H))
      (∑ i, c i • correctedLowMode B K hcoercive (u i) + (v : H))).re := by
  apply sesquilinear_orthogonal_sum_re_pos B.toLinearMap₁₂ K
    (fun i ↦ correctedLowMode B K hcoercive (u i)) c v
  · exact fun i ↦ correctedLowMode_orthogonal_right B K hcoercive (u i) v
  · exact fun i ↦ correctedLowMode_orthogonal_left K hcoercive hHerm (u i) v
  · exact hgram
  · intro x
    exact (by positivity : 0 ≤ mu * ‖x‖ * ‖x‖).trans (htail x)
  · intro x hx
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    exact (mul_pos (mul_pos hmu hxnorm) hxnorm).trans_le (htail x)
  · exact hne

theorem exists_correctedLowMode_decomposition
    {ι : Type*} [Fintype ι]
    (B : H →L⋆[ℂ] H →L[ℂ] ℂ) (K : Submodule ℂ H) [CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K)))
    (u : ι → H) (x : H) (c : ι → ℂ) (v : K)
    (hx : x = ∑ i, c i • u i + (v : H)) :
    ∃ v' : K,
      x = ∑ i, c i • correctedLowMode B K hcoercive (u i) + (v' : H) := by
  let v' : K := v + ∑ i, c i • tailCorrection B K hcoercive (u i)
  refine ⟨v', ?_⟩
  rw [hx]
  simp only [correctedLowMode, smul_sub, Finset.sum_sub_distrib, v',
    Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul]
  abel

theorem correctedLowModes_re_pos_of_decomposition
    {ι : Type*} [Fintype ι]
    {B : H →L⋆[ℂ] H →L[ℂ] ℂ} (K : Submodule ℂ H) [CompleteSpace K]
    (hcoercive : IsCoercive (complexToRealForm (restrictedForm B K)))
    (hHerm : B.toLinearMap₁₂.IsSymm) (u : ι → H)
    {mu : ℝ} (hmu : 0 < mu)
    (htail : ∀ y : K, mu * ‖y‖ * ‖y‖ ≤ (B (y : H) (y : H)).re)
    (hgram : Matrix.PosDef
      (fun i j ↦ B (correctedLowMode B K hcoercive (u i))
        (correctedLowMode B K hcoercive (u j))))
    (x : H) (hx : x ≠ 0)
    (hdecomp : ∃ (c : ι → ℂ) (v : K), x = ∑ i, c i • u i + (v : H)) :
    0 < (B x x).re := by
  obtain ⟨c, v, hxbase⟩ := hdecomp
  obtain ⟨v', hxcorr⟩ :=
    exists_correctedLowMode_decomposition B K hcoercive u x c v hxbase
  rw [hxcorr]
  apply correctedLowModes_sum_re_pos K hcoercive hHerm u c v' hmu htail hgram
  by_contra hne
  push_neg at hne
  exact hx (by simpa [hne.1, hne.2] using hxcorr)

end

end ArithmeticHodge.Analysis
```

- [ ] **Step 4: Verify GREEN and production gates**

Run:

```bash
lake env lean -DwarningAsError=true HermitianTailDecompositionScratch.lean
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/HermitianTailDecomposition.lean
lake build ArithmeticHodge
```

Expected: all exit zero. Delete the scratch, run proof/naming and dependency scans, audit the three public theorems, inspect the exact two-file diff, and verify the legacy inventory.

- [ ] **Step 5: Commit**

```bash
git add ArithmeticHodge/Analysis/HermitianTailDecomposition.lean ArithmeticHodge.lean
git commit -m "assemble corrected low modes with positive tails"
```

## Downstream boundary

The Fourier/Yoshida layer must now provide only four mathematical inputs: a closed odd or even tail `K`; a Hermitian form `B`; exact coercivity on `K` with odd `mu = 3 / 2` or even `mu = 102 / 25`; and positive definiteness of the corrected finite Gram. Coupling estimates enter through the explicit `C` interfaces, with `C ^ 2` identified with Yoshida's coupling-square sum. Probability-Haar normalization and the rational comparison matrix remain outside this generic plan.
