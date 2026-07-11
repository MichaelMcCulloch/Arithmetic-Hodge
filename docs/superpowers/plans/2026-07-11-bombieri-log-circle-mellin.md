# Bombieri Log-Circle Mellin Implementation Plan

> **For agentic workers:** Use `superpowers:subagent-driven-development` and
> implement one task at a time with a fresh independent review after each
> production commit.

**Goal:** Give every centered compactly supported Bombieri test a canonical
circle `L²` representative and identify each circle Fourier coefficient with
the exact critical Mellin sample at frequency `π n / A` and normalization
`1 / (2A)`.

**Architecture:** Keep the inexpensive carrier construction separate from the
Fourier-transform stack. A generic support-to-whole-line theorem reconciles
the centered circle character with Mathlib's real Fourier character. A final
Bombieri module specializes the generic theorem using the existing logarithmic
support and Mellin--Fourier bridges, then composes it with the carrier API.

**Verified discovery artifacts:** The strict probes are recorded in
`docs/research/yoshida-log-pullback-circle-2026-07-11.md`, including SHA-256
hashes and exact theorem shapes. The implementation must reproduce their
kernel-checked proofs, not introduce the conclusions as assumptions.

## Global constraints

- No `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, or circular
  RH-equivalent dependency.
- Preserve all 159 inventoried legacy root Lean files byte-for-byte.
- Work directly on `main` as authorized, but stage only the paths assigned to
  the current task.
- Strict-compile every new module with warnings as errors, run focused API
  scratches, `lake build ArithmeticHodge`, forbidden-proof/naming scans,
  theorem axiom audits, and the exact legacy archive comparison.
- All exported theorems must use only `propext`, `Classical.choice`, and
  `Quot.sound`, or a subset.
- Do not conflate normalized Haar `L²` with Lebesgue `L²`; the carrier uses
  the existing `centeredLift_memLp` normalization exactly.

---

### Task 1: Critical logarithmic pullback on the centered circle

**Files:**

- Create: `ArithmeticHodge/Analysis/MultiplicativeWeilLogCircle.lean`
- Modify: `ArithmeticHodge.lean`
- Temporary test: `MultiplicativeWeilLogCircleScratch.lean`

**Imports:**

```lean
import ArithmeticHodge.Analysis.CenteredAddCircleFourierBasic
import ArithmeticHodge.Analysis.MultiplicativeWeilDilation
```

**Required public interface in
`ArithmeticHodge.Analysis.MultiplicativeWeil`:**

```lean
theorem criticalLogPullback_memLp_restrict
    (g : BombieriTest) (a : ℝ) :
    MemLp
      (g.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ)
      2 (volume.restrict (Set.Ioc (-a) a))

noncomputable def criticalLogPullbackCircleL2
    (g : BombieriTest) {a : ℝ} (ha : 0 < a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    Lp ℂ 2 (@AddCircle.haarAddCircle (2 * a) ⟨by positivity⟩)

theorem criticalLogPullbackCircleL2_fourierCoeff
    (g : BombieriTest) {a : ℝ} (ha : 0 < a) (n : ℤ) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    fourierCoeff (criticalLogPullbackCircleL2 g ha) n =
      ArithmeticHodge.Analysis.centeredFourierCoeff ha
        (g.logarithmicPullbackSchwartz (1 / 2)) n

theorem support_lt_of_one_lt_ratio
    {a b : ℝ} (ha : 0 < a) (hratio : 1 < b / a) : a < b

noncomputable def logCenteredCriticalCircleL2
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a)
    (hratio : 1 < b / a) :
    let A := logarithmicHalfWidth a b
    letI : Fact (0 < 2 * A) := ⟨by
      have hA := logarithmicHalfWidth_pos ha
        (support_lt_of_one_lt_ratio ha hratio)
      positivity⟩
    Lp ℂ 2 (@AddCircle.haarAddCircle (2 * A) inferInstance)

theorem logCenteredCriticalCircleL2_fourierCoeff
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a)
    (hratio : 1 < b / a) (n : ℤ) :
    let c := logarithmicCenter a b
    let A := logarithmicHalfWidth a b
    letI : Fact (0 < 2 * A) := ⟨by
      have hA := logarithmicHalfWidth_pos ha
        (support_lt_of_one_lt_ratio ha hratio)
      positivity⟩
    fourierCoeff (logCenteredCriticalCircleL2 g ha hratio) n =
      ArithmeticHodge.Analysis.centeredFourierCoeff
        (logarithmicHalfWidth_pos ha
          (support_lt_of_one_lt_ratio ha hratio))
        ((normalizedDilation c (logarithmicCenter_pos a b) g)
          .logarithmicPullbackSchwartz (1 / 2)) n
```

- [ ] Create a strict missing-module RED scratch checking all six names.
- [ ] Reproduce the carrier proof from the verified 98-line probe. Use
  `SchwartzMap.memLp.restrict`, `centeredLift_memLp`, and
  `centeredLift_toLp_fourierCoeff`; do not add a support assumption merely to
  construct the `L²` value.
- [ ] Add exactly one umbrella import, verify all gates and theorem axioms,
  delete scratch, and commit `represent Bombieri pullbacks on centered circles`.

---

### Task 2: Generic centered coefficient as a whole-line Fourier sample

**Files:**

- Create: `ArithmeticHodge/Analysis/CenteredAddCircleFourierMellin.lean`
- Temporary test: `CenteredAddCircleFourierMellinScratch.lean`

**Imports:**

```lean
import ArithmeticHodge.Analysis.CenteredAddCircleFourierBasic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
```

**Required theorem in `ArithmeticHodge.Analysis`:**

```lean
theorem centeredFourierCoeff_eq_fourier_of_support
    {a : ℝ} (ha : 0 < a) (F : SchwartzMap ℝ ℂ)
    (hsupport : ∀ x ∉ Set.Icc (-a) a, F x = 0)
    (n : ℤ) :
    centeredFourierCoeff ha F n =
      (1 / (2 * a) : ℝ) •
        𝓕 (F : ℝ → ℂ) ((n : ℝ) / (2 * a))
```

- [ ] Record missing-module RED.
- [ ] Start from `centeredFourierCoeff_eq_integral`, rewrite the oriented
  interval integral to `Ioc`, replace `Ioc` by `Icc` almost everywhere, and
  extend to the whole line with
  `setIntegral_eq_integral_of_forall_compl_eq_zero`.
- [ ] Rewrite with `Real.fourier_eq'`. Prove the phase identity from
  `fourier_coe_apply`; explicitly reduce the real inner product and clear the
  nonzero denominator using `ha.ne'`. Do not use an informal periodicity
  argument.
- [ ] Strict-check, audit axioms, full-build, scan, compare the 159 artifacts,
  delete scratch, and commit `identify centered coefficients with Fourier samples`.

---

### Task 3: Critical Mellin specialization and direct circle composition

**Files:**

- Create: `ArithmeticHodge/Analysis/MultiplicativeWeilLogCircleMellin.lean`
- Modify: `ArithmeticHodge.lean`
- Temporary test: `MultiplicativeWeilLogCircleMellinScratch.lean`

**Imports:**

```lean
import ArithmeticHodge.Analysis.CenteredAddCircleFourierMellin
import ArithmeticHodge.Analysis.MultiplicativeWeilLogCircle
import ArithmeticHodge.Analysis.MultiplicativeWeilMellinFourier
```

**Required public theorems in
`ArithmeticHodge.Analysis.MultiplicativeWeil`:**

```lean
theorem centeredFourierCoeff_eq_mellin_of_support
    (g : BombieriTest) {a : ℝ} (ha : 0 < a)
    (hsupport : ∀ x ∉ Set.Icc (-a) a,
      g.logarithmicPullbackSchwartz (1 / 2) x = 0)
    (n : ℤ) :
    ArithmeticHodge.Analysis.centeredFourierCoeff ha
        (g.logarithmicPullbackSchwartz (1 / 2)) n =
      (1 / (2 * a) : ℝ) •
        mellin (g : ℝ → ℂ)
          (((1 / 2 : ℝ) : ℂ) +
            ((Real.pi * (n : ℝ) / a : ℝ) : ℂ) * Complex.I)

theorem logCenteredCriticalFourierCoeff_eq_mellin
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hsupport : tsupport g ⊆ Set.Icc a b) (n : ℤ) :
    let c := logarithmicCenter a b
    let A := logarithmicHalfWidth a b
    let gc := normalizedDilation c (logarithmicCenter_pos a b) g
    ArithmeticHodge.Analysis.centeredFourierCoeff
        (logarithmicHalfWidth_pos ha hab)
        (gc.logarithmicPullbackSchwartz (1 / 2)) n =
      (1 / (2 * A) : ℝ) •
        mellin (gc : ℝ → ℂ)
          (((1 / 2 : ℝ) : ℂ) +
            ((Real.pi * (n : ℝ) / A : ℝ) : ℂ) * Complex.I)

theorem logCenteredCriticalCircleL2_fourierCoeff_eq_mellin
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a)
    (hratio : 1 < b / a)
    (hsupport : tsupport g ⊆ Set.Icc a b) (n : ℤ) :
    let c := logarithmicCenter a b
    let A := logarithmicHalfWidth a b
    let gc := normalizedDilation c (logarithmicCenter_pos a b) g
    letI : Fact (0 < 2 * A) := inferInstance
    fourierCoeff (logCenteredCriticalCircleL2 g ha hratio) n =
      (1 / (2 * A) : ℝ) •
        mellin (gc : ℝ → ℂ)
          (((1 / 2 : ℝ) : ℂ) +
            ((Real.pi * (n : ℝ) / A : ℝ) : ℂ) * Complex.I)
```

- [ ] Record missing-module RED checking all three names and an exact
  ratio-two use.
- [ ] Derive the first theorem with
  `bombieriMellin_vertical_eq_fourier`; rewrite
  `SchwartzMap.fourier_coe` and prove
  `(π n / a) / (2π) = n / (2a)` by field arithmetic using
  `Real.pi_ne_zero` and `ha.ne'`.
- [ ] Instantiate centered support with
  `logCenteredNormalizedDilation_logarithmicPullback_eq_zero_outside`.
- [ ] Compose the carrier coefficient theorem with the centered Mellin theorem;
  use `support_lt_of_one_lt_ratio` for the strict endpoint order.
- [ ] Add one umbrella import for this final module, strict-check all modules
  and scratch, run the full build/scans/axiom and inventory audits, delete
  scratch, and commit `sample centered circle coefficients by Mellin transform`.

## Terminal boundary after this plan

This plan proves an exact normalization and sampling bridge only. It does not
assert Yoshida positivity, the finite Gram certificates, Bombieri positivity
for all supports, or RH. Its output is the coefficient coordinate system
consumed by the parity-tail, coercivity, coupling, and Schur-complement stages.
