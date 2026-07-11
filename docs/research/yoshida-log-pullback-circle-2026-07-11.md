# Bombieri logarithmic pullback to Yoshida's circle

Date: 2026-07-11

Status: strict-compiling proof discovery. The circle carrier bridge, exact
Mellin-sampling identity, and their direct coefficient composition are complete
in temporary probes; the next step is productionization.

## Verified probe

The 98-line probe `/tmp/YoshidaLogPullbackCircleProbe.lean` has SHA-256
`5f225683fabf477cc74341fe7690006e7a16c584085f6da5912ae8db44baecf2`.
Root ran

```text
lake env lean -DwarningAsError=true /tmp/YoshidaLogPullbackCircleProbe.lean
```

with exit zero. Its forbidden-proof scan is clean, and the two audited Fourier
coefficient theorems use only
`[propext, Classical.choice, Quot.sound]`.

## Generic critical pullback

Every Bombieri test has a critical logarithmic pullback

```lean
g.logarithmicPullbackSchwartz (1 / 2) : SchwartzMap ℝ ℂ.
```

The probe first makes its local `L²` status explicit:

```lean
theorem criticalLogPullback_memLp_restrict
    (g : BombieriTest) (a : ℝ) :
    MemLp
      (g.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ)
      2 (volume.restrict (Set.Ioc (-a) a))
```

This follows from `SchwartzMap.memLp` followed by measure restriction. No
support hypothesis is needed merely to construct the circle representative.

For `0 < a`, the probe then defines

```lean
noncomputable def criticalLogPullbackCircleL2
    (g : BombieriTest) {a : ℝ} (ha : 0 < a) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (2 * a) ...)
```

by applying `centeredLift_memLp` and `MemLp.toLp` to the logarithmic
pullback. Its Fourier coefficients are definitionally connected to the
centered interval coefficients:

```lean
theorem criticalLogPullbackCircleL2_fourierCoeff
    (g : BombieriTest) {a : ℝ} (ha : 0 < a) (n : ℤ) :
    fourierCoeff (criticalLogPullbackCircleL2 g ha) n =
      centeredFourierCoeff ha
        (g.logarithmicPullbackSchwartz (1 / 2)) n
```

## Centered normalized dilation

For a positive support endpoint `a` and a strict ratio
`1 < b / a`, the elementary bridge

```lean
theorem support_lt_of_one_lt_ratio
    (ha : 0 < a) (hratio : 1 < b / a) :
    a < b
```

combines with `logarithmicHalfWidth_pos`. The centered Bombieri test

```text
normalizedDilation (logarithmicCenter a b) ... g
```

therefore has a canonical circle `L²` representative of period
`2 * logarithmicHalfWidth a b`:

```lean
noncomputable def logCenteredCriticalCircleL2
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a)
    (hratio : 1 < b / a) : Lp ℂ 2 haarAddCircle
```

The probe proves its exact coefficient equation:

```lean
theorem logCenteredCriticalCircleL2_fourierCoeff
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a)
    (hratio : 1 < b / a) (n : ℤ) :
    fourierCoeff
        (logCenteredCriticalCircleL2 g ha hratio) n =
      centeredFourierCoeff
        (logarithmicHalfWidth_pos ha
          (support_lt_of_one_lt_ratio ha hratio))
        ((normalizedDilation
          (logarithmicCenter a b)
          (logarithmicCenter_pos a b) g)
            .logarithmicPullbackSchwartz (1 / 2)) n
```

This uses the already reviewed facts that normalized dilation preserves the
Bombieri quadratic functional and becomes translation in logarithmic
coordinates.

## Exact Mellin sampling

The 85-line probe `/tmp/YoshidaMellinCircleSamplingProbe.lean` has SHA-256
`849a5cb783354ed7b188eb9e8cd1d0c87fcd260ea12114fd245e8b0cf6ecb593`.
It strict-compiles with warnings as errors, its forbidden-proof scan is clean,
and each of its three theorems audits to exactly
`[propext, Classical.choice, Quot.sound]`.

For an arbitrary Schwartz function supported on `Icc (-a) a`, it proves

```lean
theorem centeredFourierCoeff_eq_fourier_of_support
    {a : ℝ} (ha : 0 < a) (F : SchwartzMap ℝ ℂ)
    (hsupport : ∀ x ∉ Set.Icc (-a) a, F x = 0)
    (n : ℤ) :
    centeredFourierCoeff ha F n =
      (1 / (2 * a) : ℝ) •
        𝓕 (F : ℝ → ℂ) ((n : ℝ) / (2 * a))
```

The proof changes the interval integral to `Ioc`, replaces it almost
everywhere by `Icc`, extends it to the whole line using the support hypothesis,
and proves the circle/real Fourier phase identity directly. It then specializes
to Bombieri tests:

```lean
theorem centeredFourierCoeff_eq_mellin_of_support
    (g : BombieriTest) {a : ℝ} (ha : 0 < a)
    (hsupport : ∀ x ∉ Set.Icc (-a) a,
      g.logarithmicPullbackSchwartz (1 / 2) x = 0)
    (n : ℤ) :
    centeredFourierCoeff ha
        (g.logarithmicPullbackSchwartz (1 / 2)) n =
      (1 / (2 * a) : ℝ) •
        mellin (g : ℝ → ℂ)
          (((1 / 2 : ℝ) : ℂ) +
            ((Real.pi * (n : ℝ) / a : ℝ) : ℂ) * Complex.I)
```

Thus the normalization is exactly

```text
mellin g (1/2 + v I)
  = Fourier(logarithmicPullback)(v / (2*pi))
```

and the centered circle frequency
`n / (2*a)`, hence `v = pi*n/a`. Formalization must:
all four previously listed measure, phase, and scalar-normalization obligations
are now discharged by the kernel.

Finally, `logCenteredCriticalFourierCoeff_eq_mellin` instantiates the support
hypothesis from
`logCenteredNormalizedDilation_logarithmicPullback_eq_zero_outside`, yielding
the exact sample formula for a normalized, logarithmically centered Bombieri
test supported in `Icc a b` with `0 < a < b`.

The 42-line composition probe
`/tmp/YoshidaMellinCircleCompositionProbe.lean` has SHA-256
`2c953f736c397ea21b01c0e3f19337a0e31a44afbe6504b638ab8e369cbed00f`.
It strict-compiles, has a clean forbidden-proof scan, and audits to exactly the
three standard Mathlib axioms. Its theorem
`logCenteredCriticalCircleL2_fourierCoeff_eq_mellin` directly identifies
`fourierCoeff (logCenteredCriticalCircleL2 g ha hratio) n` with the normalized
critical Mellin sample of the centered dilation under
`tsupport g ⊆ Icc a b`.

## Production placement

The carrier bridge belongs in a focused module importing
`CenteredAddCircleFourierBasic` and `MultiplicativeWeilDilation`. The
Mellin-sampling theorem should be a second module importing
`MultiplicativeWeilMellinFourier`, so the basic circle construction does not
pull the Fourier-transform stack into every consumer. The production task
should expose the already verified composed theorem equating
`fourierCoeff (logCenteredCriticalCircleL2 ...) n` directly with the normalized
critical Mellin sample.
