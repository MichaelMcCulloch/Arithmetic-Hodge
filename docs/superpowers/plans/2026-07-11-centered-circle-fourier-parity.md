# Centered Circle Fourier Parity Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize measure-preserving reflection on circle `L²`, its closed even/odd subspaces, complete parity Fourier tails, and Fourier coefficient symmetry.

**Architecture:** Prove negation preserves normalized Haar measure by uniqueness, lift it to an involutive continuous linear isometry on `L²`, and define parity spaces as closed kernels of `R-id` and `R+id`. Intersect those kernels with the closed coefficient tail from the projection module, then expose algebraic/continuous parity projections and their exact Fourier coefficient formulas.

**Tech Stack:** Lean 4, Mathlib Haar uniqueness, `Lp.compMeasurePreservingₗᵢ`, closed submodules, continuous linear maps, and the circle Fourier basis.

## Global Constraints

- No `sorry`, `admit`, custom `axiom`, unsafe declaration, `native_decide`, or RH-equivalent proof bypass.
- Preserve all 159 inventoried legacy untracked Lean research files byte-for-byte.
- Work directly on `main` as explicitly authorized; commit and independently review the task.
- Execute only after the centered-circle Fourier projection task is reviewed and committed.
- Run only one implementation subagent; it owns the parity module, one facade import, and its temporary scratch/audit files.
- Run strict RED first, then strict production/facade/interface checks, the full build, global scans, theorem axiom audits, and exact legacy comparison.
- Every exported theorem must use only `[propext, Classical.choice, Quot.sound]` or a subset.
- Prove Haar negation invariance from Mathlib uniqueness; do not assume it or introduce a measure-preservation axiom.
- Keep the module generic over positive circle length `T`; do not introduce Lebesgue normalization, Yoshida mode cutoffs, finite corrected matrices, Bombieri tests, or RH.
- Keep existing pointwise centered-coefficient symmetry APIs intact; this module adds the `L²` reflection/submodule layer.

---

### Task 1: Reflection, parity kernels, and complete parity tails

**Files:**

- Create: `ArithmeticHodge/Analysis/CenteredAddCircleFourierParity.lean`
- Modify: `ArithmeticHodge/Analysis/CenteredAddCircleFourier.lean`
- Test: `CenteredAddCircleFourierParityScratch.lean` (temporary; delete before commit)

**Interfaces:**

- Consumes: `CircleL2`, `fourierCoeffCLM`, `LowIndex`, and `fourierTailSubmodule` from the projection module.
- Produces: Haar-preserving reflection; even/odd submodules; complete parity tails; algebraic and continuous parity projections; reflection of Fourier modes and coefficients; parity coefficient identities; and fixed-point identities.

- [ ] **Step 1: Write and run the strict missing-module RED**

Create `CenteredAddCircleFourierParityScratch.lean`:

```lean
import ArithmeticHodge.Analysis.CenteredAddCircleFourierParity

set_option autoImplicit false

namespace ArithmeticHodge.Analysis

#check circleNegMeasurePreserving
#check reflectionL2
#check reflectionL2_ae
#check reflectionL2_involutive
#check evenL2Submodule
#check oddL2Submodule
#check mem_evenL2Submodule_iff
#check mem_oddL2Submodule_iff
#check evenL2Submodule_isClosed
#check oddL2Submodule_isClosed
#check evenFourierTailSubmodule
#check oddFourierTailSubmodule
#check evenFourierTailSubmodule_isClosed
#check oddFourierTailSubmodule_isClosed
example {T : ℝ} [Fact (0 < T)] (N : ℕ) :
    CompleteSpace (evenFourierTailSubmodule (T := T) N) :=
  inferInstance
example {T : ℝ} [Fact (0 < T)] (N : ℕ) :
    CompleteSpace (oddFourierTailSubmodule (T := T) N) :=
  inferInstance
#check evenPart
#check oddPart
#check evenPartCLM
#check oddPartCLM
#check evenPart_mem
#check oddPart_mem
#check evenPart_add_oddPart
#check fourier_apply_neg
#check reflectionL2_fourierLp
#check fourierCoeff_reflectionL2
#check fourierCoeff_even_of_mem
#check fourierCoeff_odd_of_mem
#check fourierCoeff_evenPart
#check fourierCoeff_oddPart
#check evenPart_eq_self_of_mem
#check oddPart_eq_self_of_mem
#check neg_mem_lowIndex

end ArithmeticHodge.Analysis
```

Run:

```bash
lake env lean -DwarningAsError=true CenteredAddCircleFourierParityScratch.lean
```

Expected: nonzero exit because the production module does not exist.

- [ ] **Step 2: Implement reflection, parity kernels, and complete tails**

Create `ArithmeticHodge/Analysis/CenteredAddCircleFourierParity.lean`:

```lean
import ArithmeticHodge.Analysis.CenteredAddCircleFourierProjection
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false

noncomputable section

open AddCircle MeasureTheory Set
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace ArithmeticHodge.Analysis

variable {T : ℝ} [hT : Fact (0 < T)]

def circleNegMeasurePreserving :
    MeasurePreserving
      (Neg.neg : AddCircle T → AddCircle T)
      haarAddCircle haarAddCircle := by
  haveI : Measure.IsAddHaarMeasure
      (Measure.map
        (Neg.neg : AddCircle T → AddCircle T)
        haarAddCircle) :=
    (AddEquiv.neg
      (AddCircle T)).isAddHaarMeasure_map
        haarAddCircle continuous_neg continuous_neg
  haveI : IsProbabilityMeasure
      (Measure.map
        (Neg.neg : AddCircle T → AddCircle T)
        haarAddCircle) :=
    Measure.isProbabilityMeasure_map
      continuous_neg.aemeasurable
  exact ⟨measurable_neg,
    Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure
      (Measure.map
        (Neg.neg : AddCircle T → AddCircle T)
        haarAddCircle)
      haarAddCircle⟩

def reflectionL2 :
    CircleL2 (T := T) →L[ℂ] CircleL2 (T := T) :=
  (Lp.compMeasurePreservingₗᵢ ℂ Neg.neg
    (circleNegMeasurePreserving
      (T := T))).toContinuousLinearMap

theorem reflectionL2_ae
    (f : CircleL2 (T := T)) :
    reflectionL2 f =ᵐ[haarAddCircle]
      fun x ↦ f (-x) := by
  exact Lp.coeFn_compMeasurePreserving f
    (circleNegMeasurePreserving (T := T))

@[simp] theorem reflectionL2_involutive
    (f : CircleL2 (T := T)) :
    reflectionL2 (reflectionL2 f) = f := by
  change Lp.compMeasurePreserving Neg.neg
      (circleNegMeasurePreserving (T := T))
      (Lp.compMeasurePreserving Neg.neg
        (circleNegMeasurePreserving (T := T)) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f
    (circleNegMeasurePreserving (T := T))
    (circleNegMeasurePreserving (T := T))]
  have hfun :
      (Neg.neg ∘ Neg.neg :
        AddCircle T → AddCircle T) = id := by
    funext x
    simp
  simpa only [hfun] using
    Lp.compMeasurePreserving_id_apply f

def evenL2Submodule :
    Submodule ℂ (CircleL2 (T := T)) :=
  LinearMap.ker
    (reflectionL2 (T := T) -
      ContinuousLinearMap.id ℂ
        (CircleL2 (T := T))).toLinearMap

def oddL2Submodule :
    Submodule ℂ (CircleL2 (T := T)) :=
  LinearMap.ker
    (reflectionL2 (T := T) +
      ContinuousLinearMap.id ℂ
        (CircleL2 (T := T))).toLinearMap

theorem mem_evenL2Submodule_iff
    (f : CircleL2 (T := T)) :
    f ∈ evenL2Submodule (T := T) ↔
      reflectionL2 (T := T) f = f := by
  rw [evenL2Submodule, LinearMap.mem_ker]
  change reflectionL2 (T := T) f - f = 0 ↔ _
  exact sub_eq_zero

theorem mem_oddL2Submodule_iff
    (f : CircleL2 (T := T)) :
    f ∈ oddL2Submodule (T := T) ↔
      reflectionL2 (T := T) f = -f := by
  rw [oddL2Submodule, LinearMap.mem_ker]
  change reflectionL2 (T := T) f + f = 0 ↔ _
  exact add_eq_zero_iff_eq_neg

theorem evenL2Submodule_isClosed :
    IsClosed
      (evenL2Submodule (T := T) :
        Set (CircleL2 (T := T))) :=
  ContinuousLinearMap.isClosed_ker _

theorem oddL2Submodule_isClosed :
    IsClosed
      (oddL2Submodule (T := T) :
        Set (CircleL2 (T := T))) :=
  ContinuousLinearMap.isClosed_ker _

def evenFourierTailSubmodule (N : ℕ) :
    Submodule ℂ (CircleL2 (T := T)) :=
  evenL2Submodule (T := T) ⊓
    fourierTailSubmodule (T := T) N

def oddFourierTailSubmodule (N : ℕ) :
    Submodule ℂ (CircleL2 (T := T)) :=
  oddL2Submodule (T := T) ⊓
    fourierTailSubmodule (T := T) N

theorem evenFourierTailSubmodule_isClosed
    (N : ℕ) :
    IsClosed
      (evenFourierTailSubmodule (T := T) N :
        Set (CircleL2 (T := T))) := by
  simpa only [evenFourierTailSubmodule,
    Submodule.coe_inf] using
      (evenL2Submodule_isClosed
        (T := T)).inter
          (fourierTailSubmodule_isClosed
            (T := T) N)

theorem oddFourierTailSubmodule_isClosed
    (N : ℕ) :
    IsClosed
      (oddFourierTailSubmodule (T := T) N :
        Set (CircleL2 (T := T))) := by
  simpa only [oddFourierTailSubmodule,
    Submodule.coe_inf] using
      (oddL2Submodule_isClosed
        (T := T)).inter
          (fourierTailSubmodule_isClosed
            (T := T) N)

noncomputable instance instCompleteSpaceEvenFourierTail
    (N : ℕ) :
    CompleteSpace
      (evenFourierTailSubmodule (T := T) N) :=
  (evenFourierTailSubmodule_isClosed
    (T := T) N).completeSpace_coe

noncomputable instance instCompleteSpaceOddFourierTail
    (N : ℕ) :
    CompleteSpace
      (oddFourierTailSubmodule (T := T) N) :=
  (oddFourierTailSubmodule_isClosed
    (T := T) N).completeSpace_coe
```

- [ ] **Step 3: Add parity projections and Fourier interaction**

Continue the same module:

```lean
def evenPart (f : CircleL2 (T := T)) :
    CircleL2 (T := T) :=
  (2 : ℂ)⁻¹ •
    (f + reflectionL2 (T := T) f)

def oddPart (f : CircleL2 (T := T)) :
    CircleL2 (T := T) :=
  (2 : ℂ)⁻¹ •
    (f - reflectionL2 (T := T) f)

def evenPartCLM :
    CircleL2 (T := T) →L[ℂ] CircleL2 (T := T) :=
  (2 : ℂ)⁻¹ •
    (ContinuousLinearMap.id ℂ
      (CircleL2 (T := T)) +
        reflectionL2 (T := T))

def oddPartCLM :
    CircleL2 (T := T) →L[ℂ] CircleL2 (T := T) :=
  (2 : ℂ)⁻¹ •
    (ContinuousLinearMap.id ℂ
      (CircleL2 (T := T)) -
        reflectionL2 (T := T))

@[simp] theorem evenPartCLM_apply
    (f : CircleL2 (T := T)) :
    evenPartCLM (T := T) f =
      evenPart (T := T) f := by
  simp [evenPartCLM, evenPart]

@[simp] theorem oddPartCLM_apply
    (f : CircleL2 (T := T)) :
    oddPartCLM (T := T) f =
      oddPart (T := T) f := by
  simp [oddPartCLM, oddPart]

theorem evenPart_mem (f : CircleL2 (T := T)) :
    evenPart (T := T) f ∈
      evenL2Submodule (T := T) := by
  rw [mem_evenL2Submodule_iff]
  simp [evenPart, add_comm]

theorem oddPart_mem (f : CircleL2 (T := T)) :
    oddPart (T := T) f ∈
      oddL2Submodule (T := T) := by
  rw [mem_oddL2Submodule_iff]
  simp [oddPart]
  module

theorem evenPart_add_oddPart
    (f : CircleL2 (T := T)) :
    evenPart (T := T) f +
      oddPart (T := T) f = f := by
  simp [evenPart, oddPart]
  module

omit hT in
theorem fourier_apply_neg
    (n : ℤ) (x : AddCircle T) :
    fourier n (-x) = fourier (-n) x := by
  simp only [fourier_apply,
    smul_neg, neg_smul]

@[simp] theorem reflectionL2_fourierLp (n : ℤ) :
    reflectionL2 (T := T)
      (fourierLp 2 n) =
        fourierLp 2 (-n) := by
  apply Lp.ext
  have hcomp :=
    (circleNegMeasurePreserving
      (T := T)).quasiMeasurePreserving.tendsto_ae
        (coeFn_fourierLp (T := T) 2 n)
  filter_upwards
    [reflectionL2_ae (T := T)
      (fourierLp 2 n),
    hcomp,
    coeFn_fourierLp (T := T) 2 (-n)]
      with x href hn hneg
  rw [href, hn, hneg, fourier_apply_neg]

theorem fourierCoeff_reflectionL2
    (f : CircleL2 (T := T)) (n : ℤ) :
    fourierCoeff
      (reflectionL2 (T := T) f) n =
        fourierCoeff f (-n) := by
  rw [← fourierCoeffCLM_apply,
    ← fourierCoeffCLM_apply]
  change
    ⟪fourierLp 2 n,
      reflectionL2 (T := T) f⟫_ℂ =
        ⟪fourierLp 2 (-n), f⟫_ℂ
  have h :=
    (Lp.compMeasurePreservingₗᵢ ℂ Neg.neg
      (circleNegMeasurePreserving
        (T := T))).inner_map_map
          (fourierLp 2 n)
          (reflectionL2 (T := T) f)
  change
    ⟪reflectionL2 (T := T)
        (fourierLp 2 n),
      reflectionL2 (T := T)
        (reflectionL2 (T := T) f)⟫_ℂ =
      ⟪fourierLp 2 n,
        reflectionL2 (T := T) f⟫_ℂ at h
  rw [reflectionL2_fourierLp,
    reflectionL2_involutive] at h
  exact h.symm

theorem fourierCoeff_even_of_mem
    {f : CircleL2 (T := T)}
    (hf : f ∈ evenL2Submodule (T := T))
    (n : ℤ) :
    fourierCoeff f (-n) =
      fourierCoeff f n := by
  calc
    fourierCoeff f (-n) =
        fourierCoeff
          (reflectionL2 (T := T) f) n :=
      (fourierCoeff_reflectionL2 f n).symm
    _ = fourierCoeff f n := by
      rw [(mem_evenL2Submodule_iff f).mp hf]

theorem fourierCoeff_odd_of_mem
    {f : CircleL2 (T := T)}
    (hf : f ∈ oddL2Submodule (T := T))
    (n : ℤ) :
    fourierCoeff f (-n) =
      -fourierCoeff f n := by
  calc
    fourierCoeff f (-n) =
        fourierCoeff
          (reflectionL2 (T := T) f) n :=
      (fourierCoeff_reflectionL2 f n).symm
    _ = fourierCoeff (-f) n := by
      rw [(mem_oddL2Submodule_iff f).mp hf]
    _ = -fourierCoeff f n := by
      rw [← fourierCoeffCLM_apply,
        ← fourierCoeffCLM_apply]
      exact map_neg
        (fourierCoeffCLM (T := T) n) f

theorem fourierCoeff_evenPart
    (f : CircleL2 (T := T)) (n : ℤ) :
    fourierCoeff (evenPart (T := T) f) n =
      (2 : ℂ)⁻¹ •
        (fourierCoeff f n +
          fourierCoeff f (-n)) := by
  calc
    fourierCoeff (evenPart (T := T) f) n =
        fourierCoeffCLM (T := T) n
          (evenPart (T := T) f) := by
      rw [fourierCoeffCLM_apply]
    _ = (2 : ℂ)⁻¹ •
        (fourierCoeffCLM (T := T) n f +
          fourierCoeffCLM (T := T) n
            (reflectionL2 (T := T) f)) := by
      rw [evenPart, map_smul, map_add]
    _ = (2 : ℂ)⁻¹ •
        (fourierCoeff f n +
          fourierCoeff f (-n)) := by
      rw [fourierCoeffCLM_apply,
        fourierCoeffCLM_apply,
        fourierCoeff_reflectionL2]

theorem fourierCoeff_oddPart
    (f : CircleL2 (T := T)) (n : ℤ) :
    fourierCoeff (oddPart (T := T) f) n =
      (2 : ℂ)⁻¹ •
        (fourierCoeff f n -
          fourierCoeff f (-n)) := by
  calc
    fourierCoeff (oddPart (T := T) f) n =
        fourierCoeffCLM (T := T) n
          (oddPart (T := T) f) := by
      rw [fourierCoeffCLM_apply]
    _ = (2 : ℂ)⁻¹ •
        (fourierCoeffCLM (T := T) n f -
          fourierCoeffCLM (T := T) n
            (reflectionL2 (T := T) f)) := by
      rw [oddPart, map_smul, map_sub]
    _ = (2 : ℂ)⁻¹ •
        (fourierCoeff f n -
          fourierCoeff f (-n)) := by
      rw [fourierCoeffCLM_apply,
        fourierCoeffCLM_apply,
        fourierCoeff_reflectionL2]

theorem evenPart_eq_self_of_mem
    {f : CircleL2 (T := T)}
    (hf : f ∈ evenL2Submodule (T := T)) :
    evenPart (T := T) f = f := by
  rw [evenPart,
    (mem_evenL2Submodule_iff f).mp hf]
  module

theorem oddPart_eq_self_of_mem
    {f : CircleL2 (T := T)}
    (hf : f ∈ oddL2Submodule (T := T)) :
    oddPart (T := T) f = f := by
  rw [oddPart,
    (mem_oddL2Submodule_iff f).mp hf]
  module

theorem neg_mem_lowIndex
    {N : ℕ} {n : ℤ}
    (hn : n ∈
      Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    -n ∈ Finset.Icc
      (-(N : ℤ)) (N : ℤ) := by
  simp only [Finset.mem_Icc] at hn ⊢
  omega

end ArithmeticHodge.Analysis
```

- [ ] **Step 4: Add the facade import**

Add exactly

```lean
import ArithmeticHodge.Analysis.CenteredAddCircleFourierParity
```

to `ArithmeticHodge/Analysis/CenteredAddCircleFourier.lean`, immediately
after the projection import and before symmetry/tail. Do not modify the root
umbrella.

- [ ] **Step 5: Verify GREEN, axioms, and repository invariants**

Run:

```bash
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/CenteredAddCircleFourierParity.lean
lake build ArithmeticHodge.Analysis.CenteredAddCircleFourierParity
lake env lean -DwarningAsError=true CenteredAddCircleFourierParityScratch.lean
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/CenteredAddCircleFourier.lean
lake build ArithmeticHodge
```

Expected: all exit zero. Audit every theorem in the scratch and the two
`CompleteSpace` instance constructions, require only standard logical
axioms, delete scratch/audit files, run global scans, compare all 159 legacy
files to the archive ref, and inspect only the parity module plus facade import
diff.

- [ ] **Step 6: Commit**

```bash
git add ArithmeticHodge/Analysis/CenteredAddCircleFourierParity.lean \
  ArithmeticHodge/Analysis/CenteredAddCircleFourier.lean
git commit -m "add circle Fourier parity tails"
```
