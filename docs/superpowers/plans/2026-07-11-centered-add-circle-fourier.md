# Centered Additive-Circle Fourier Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to implement this plan task by
> task with TDD and an independent review after every production commit.

**Goal:** Provide the normalized centered-period Fourier API needed to state
and prove Yoshida's parity, high-mode, and finite-tail estimates without
leaking Mathlib's interval/circle plumbing into the number-theory modules.

**Architecture:** Keep smoothness and integration-by-parts arguments on the
real interval. This wrapper uses `AddCircle.liftIoc` only as a measurable L2
representative on the probability-normalized Haar circle. Separate modules
cover the centered lift, coefficient symmetries, and symmetric partial/tail
sums; a thin facade imports the three pieces.

**Tech Stack:** Lean 4, `Mathlib.Analysis.Fourier.AddCircle`, normalized Haar
measure, `Lp ℂ 2`, `HilbertBasis`, and symmetric integer summation filters.

## Global Constraints

- No `sorry`, `admit`, custom `axiom`, unsafe declaration, or RH-equivalent
  proof bypass.
- Preserve all 159 inventoried legacy untracked Lean research files.
- Use the probability measure `AddCircle.haarAddCircle`; never silently
  substitute the standard mass-`2a` circle volume.
- The centered interval is `Ioc (-a) a`, its period is exactly `2 * a`, and
  coefficients use Mathlib's phase `exp (-pi * I * n * x / a)` with the
  normalization factor `(2 * a)⁻¹`.
- Do not claim or construct a smooth structure on `AddCircle`; interval
  differentiability remains outside this wrapper.
- Strict-compile every new module, run the full `lake build ArithmeticHodge`,
  proof/naming/dependency scans, and axiom audits, then commit each task and
  obtain an independent review.

---

### Task 1: Centered lift and L2 Fourier bridge

**Files:**

- Create: `ArithmeticHodge/Analysis/CenteredAddCircleFourierBasic.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `CenteredAddCircleFourierBasicScratch.lean` (temporary; delete before
  commit)

**Imports:**

```lean
import Mathlib.Analysis.Fourier.AddCircle
```

**Produces in `ArithmeticHodge.Analysis`:**

```lean
abbrev CenteredAddCircle (a : ℝ) := AddCircle (2 * a)

def centeredLift (a : ℝ) [Fact (0 < 2 * a)] (f : ℝ → ℂ) :
    CenteredAddCircle a → ℂ :=
  AddCircle.liftIoc (2 * a) (-a) f

def centeredFourierCoeff {a : ℝ} (ha : 0 < a)
    (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn (neg_lt_self ha) f n

theorem centeredLift_apply_Ioc
    {a x : ℝ} [Fact (0 < 2 * a)] (f : ℝ → ℂ)
    (hx : x ∈ Set.Ioc (-a) a) :
    centeredLift a f (x : CenteredAddCircle a) = f x

theorem centeredFourierCoeff_eq_integral
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) (n : ℤ) :
    centeredFourierCoeff ha f n =
      (1 / (2 * a) : ℝ) • ∫ x in -a..a,
        fourier (-n) (x : CenteredAddCircle a) • f x

theorem centeredLift_memLp
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hL2 : MeasureTheory.MemLp f 2
      (volume.restrict (Set.Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    MeasureTheory.MemLp (centeredLift a f) 2
      AddCircle.haarAddCircle

theorem centeredLift_toLp_fourierCoeff
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hL2 : MeasureTheory.MemLp f 2
      (volume.restrict (Set.Ioc (-a) a))) (n : ℤ) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    let hF := centeredLift_memLp ha hL2
    fourierCoeff (hF.toLp (centeredLift a f)) n =
      centeredFourierCoeff ha f n

theorem hasSum_centered_fourier_series_L2
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hL2 : MeasureTheory.MemLp f 2
      (volume.restrict (Set.Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    let hF := centeredLift_memLp ha hL2
    HasSum
      (fun n : ℤ => centeredFourierCoeff ha f n • fourierLp 2 n)
      (hF.toLp (centeredLift a f))
```

- [ ] Write exact scratch uses of all six declarations and record RED from the
  missing production module.
- [ ] Implement centered endpoint arithmetic explicitly; simplify
  `-a + 2 * a` to `a` without changing the half-open seam convention.
- [ ] For the explicit coefficient-integral theorem, use a local
  `NormedSpace ℝ ℂ := NormedSpace.complexToReal` instance matching the
  upstream interval theorem; after endpoint normalization, close the harmless
  scalar-instance diamond by `Complex.ext` and reflexivity.
- [ ] Obtain normalized-Haar `MemLp` via
  `MemLp.memLp_liftIoc.haarAddCircle`.
- [ ] Relate the bundled Lp coefficient to `fourierCoeffOn` with
  `fourierCoeff_congr_ae` and `fourierCoeff_liftIoc_eq`.
- [ ] Specialize `hasSum_fourier_series_L2`, strict-compile scratch and
  production, delete scratch, full-build/audit, and commit as
  `add centered additive-circle Fourier bridge`.

### Task 2: Centered coefficient symmetries

**Files:**

- Create: `ArithmeticHodge/Analysis/CenteredAddCircleFourierSymmetry.lean`
- Test: `CenteredAddCircleFourierSymmetryScratch.lean` (temporary; delete
  before commit)

**Imports:**

```lean
import ArithmeticHodge.Analysis.CenteredAddCircleFourierBasic
```

**Produces in `ArithmeticHodge.Analysis`:**

```lean
theorem fourierCoeff_conj_apply
    {T : ℝ} [Fact (0 < T)] (f : AddCircle T → ℂ) (n : ℤ) :
    fourierCoeff (fun x => conj (f x)) n =
      conj (fourierCoeff f (-n))

theorem fourierCoeff_comp_neg
    {T : ℝ} [Fact (0 < T)] (f : AddCircle T → ℂ) (n : ℤ) :
    fourierCoeff (fun x => f (-x)) n = fourierCoeff f (-n)

theorem centeredFourierCoeff_conj
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) (n : ℤ) :
    centeredFourierCoeff ha (fun x => conj (f x)) n =
      conj (centeredFourierCoeff ha f (-n))

theorem centeredFourierCoeff_reflect
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) (n : ℤ) :
    centeredFourierCoeff ha (fun x => f (-x)) n =
      centeredFourierCoeff ha f (-n)

theorem centeredFourierCoeff_even
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ)
    (hf : ∀ x, f (-x) = f x) (n : ℤ) :
    centeredFourierCoeff ha f (-n) = centeredFourierCoeff ha f n

theorem centeredFourierCoeff_real
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) (n : ℤ) :
    centeredFourierCoeff ha (fun x => (f x : ℂ)) (-n) =
      conj (centeredFourierCoeff ha (fun x => (f x : ℂ)) n)
```

- [ ] Record missing-module RED with exact scratch uses.
- [ ] Prove conjugation by `integral_conj` and `fourier_neg`.
- [ ] Prove reflection through the centered interval substitution
  `intervalIntegral.integral_comp_neg`; do not enlarge the dependency surface
  merely to synthesize Haar neg-invariance. Mark the input-negation helper
  `omit hT in` because it does not use positivity of the period.
- [ ] Derive centered conjugation, reflection, evenness, and real-valued
  coefficient identities; strict-compile, full-build/audit, and commit as
  `prove centered Fourier coefficient symmetries`.

### Task 3: Plancherel, symmetric partial sums, and tails

**Files:**

- Create: `ArithmeticHodge/Analysis/CenteredAddCircleFourierTail.lean`
- Create: `ArithmeticHodge/Analysis/CenteredAddCircleFourier.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `CenteredAddCircleFourierTailScratch.lean` (temporary; delete before
  commit)

**Imports:**

```lean
import ArithmeticHodge.Analysis.CenteredAddCircleFourierSymmetry
import Mathlib.Topology.Algebra.InfiniteSum.ConditionalInt
```

**Produces in `ArithmeticHodge.Analysis`:**

```lean
theorem orthonormal_remainder_norm_sq
    {E ι : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    {v : ι → E} (hv : Orthonormal ℂ v) (x : E) (s : Finset ι) :
    ‖x - ∑ i ∈ s, ⟪v i, x⟫_ℂ • v i‖ ^ 2 =
      ‖x‖ ^ 2 - ∑ i ∈ s, ‖⟪v i, x⟫_ℂ‖ ^ 2

theorem fourier_partial_remainder_norm_sq
    {T : ℝ} [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) (s : Finset ℤ) :
    ‖f - ∑ i ∈ s, fourierCoeff f i • fourierLp 2 i‖ ^ 2 =
      ‖f‖ ^ 2 - ∑ i ∈ s, ‖fourierCoeff f i‖ ^ 2

theorem hasSum_fourier_plancherel
    {T : ℝ} [hT : Fact (0 < T)]
    (f g : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    HasSum (fun i : ℤ =>
      conj (fourierCoeff f i) * fourierCoeff g i) (inner ℂ f g)

theorem fourier_series_symmetric_tendsto
    {T : ℝ} [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        fourierCoeff f n • fourierLp 2 n)
      atTop (𝓝 f)

theorem fourier_series_symmetric_remainder_norm_tendsto_zero
    {T : ℝ} [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    Tendsto
      (fun N : ℕ => ‖f - ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        fourierCoeff f n • fourierLp 2 n‖)
      atTop (𝓝 0)

theorem centered_parseval_symmetric_tendsto
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hL2 : MeasureTheory.MemLp f 2
      (volume.restrict (Set.Ioc (-a) a))) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ‖centeredFourierCoeff ha f n‖ ^ 2)
      atTop (𝓝 ((2 * a)⁻¹ • ∫ x in -a..a, ‖f x‖ ^ 2))

theorem fourier_parseval_tail_tsum_tendsto_zero
    {T : ℝ} [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    Tendsto
      (fun N : ℕ =>
        ∑' n : {n : ℤ // n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)},
          ‖fourierCoeff f n‖ ^ 2)
      atTop (𝓝 0)
```

- [ ] Record missing-module RED using the exact finite remainder and centered
  Parseval interfaces.
- [ ] Prove the generic finite orthonormal remainder identity, then specialize
  it through `fourierBasis_repr` and `coe_fourierBasis`.
- [ ] Specialize `HilbertBasis.hasSum_inner_mul_inner` for one-dimensional
  Plancherel.
- [ ] Transfer unconditional `HasSum` to
  `SummationFilter.symmetricIcc ℤ`, then expose symmetric convergence and the
  norm remainder.
- [ ] Specialize interval Parseval with period `2 * a`, and prove coefficient
  tail convergence via `tendsto_tsum_compl_atTop_zero` and
  `Finset.tendsto_Icc_neg`.
- [ ] Create the thin facade importing Basic, Symmetry, and Tail; add only the
  facade to `ArithmeticHodge.lean`; strict-compile all modules, full-build,
  scan/audit, and commit as `add centered Fourier partial sums and tails`.

## Downstream use

Yoshida modules should import only
`ArithmeticHodge.Analysis.CenteredAddCircleFourier`. High-mode coercivity may
use interval integration by parts directly, but coefficient normalization,
parity, L2 reconstruction, finite low-mode extraction, and tail energy must go
through this wrapper. The next proof layer defines the `N`-tail submodule by
vanishing `centeredFourierCoeff` for `|n| ≤ N` and combines it with the
coercive-correction and finite-certificate modules.
