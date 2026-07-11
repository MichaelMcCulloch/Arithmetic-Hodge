# Yoshida clipped log-interval domain

Date: 2026-07-11

Status: reviewed architecture with a strict-compiling Lean prototype. The
carrier, exact modes, transform maps, and production split are verified; the
analytic cross-integrability theorem and source equation (5.16-Q) remain to
be proved.

## Decision

Use a direct clipped log-interval domain. Do not extend the local critical
form to all circle `L²`, and do not make smooth approximation the primary
definition.

Yoshida's low modes are smooth on the closed interval but may jump when set
to zero outside it. The smooth `BombieriTest` form cannot be applied to them,
while its logarithmically growing spectral multiplier is not bounded on
ordinary circle `L²`. A weighted approximation topology would therefore
recreate the direct spectral domain and would risk using the positive-tail
completion circularly.

## Verified prototype

The production-shaped probe `/tmp/ClippedModeDomainProbe.lean` has 553 lines
and SHA-256
`8034818815d07ec3769ca510e9e9a23df58206f2f41a122a9096ae475f299feb`.
The reviewed design report `/tmp/clipped-mode-domain-design.md` has 348 lines
and SHA-256
`e6bedec96df557527e450f8c282d267e98864064d30b318e7367633c55619568`.

The probe passes

```text
lake env lean -DwarningAsError=true /tmp/ClippedModeDomainProbe.lean
```

and a forbidden-proof scan. Every audited theorem uses only
`[propext, Classical.choice, Quot.sound]`.

It checks the carrier and clipped modes, complex-linear centered Laplace
evaluation, the exact nonzero-denominator mode transform, the algebraic form
construction conditional on one named cross-integrability theorem,
support-conditional smooth agreement interfaces, the exact shape of (5.16-Q),
and a type-correct external-low-mode Riesz call.

The assumption wrapper used to test the later form architecture is not a
production result and must not be landed as the final API.

## Ambient carrier

Use

```lean
def yoshidaClippedSmoothSubmodule (a : ℝ) : Submodule ℂ (ℝ → ℂ) where
  carrier f :=
    ContDiffOn ℝ ∞ f (Set.Icc (-a) a) ∧
      ∀ x ∉ Set.Icc (-a) a, f x = 0

abbrev YoshidaClippedSmooth (a : ℝ) :=
  yoshidaClippedSmoothSubmodule a
```

Endpoint jumps are intentional. This ambient space contains the clipped
exponentials, source `K(a)`, and cropped smooth critical pullbacks. It is
larger than the eventual positive tail, which must remain a separate genuine
periodic core.

The Lebesgue-normalized mode is

```text
chi_n(x) = (sqrt(2a))^-1 exp(pi*i*n*x/a),  x in [-a,a],
           0,                               otherwise.
```

The later coordinate map to `CircleL2 (T := 2*a)` must preserve the explicit
normalization

```text
integral_{-a}^{a} |f(x)|^2 dx
  = (2*a) * ‖circleCoordinate(f)‖_Haar^2.
```

Thus Yoshida's constants `38/25` and `102/25` multiply the Lebesgue norm,
not raw probability-Haar norm squared.

## Centered Laplace evaluations

For `0 < a`, define the complex-linear map

```text
L_z(f) = integral_{-a}^{a} exp(-z*x) f(x) dx.
```

The three required samples are

```text
Sample_v = L_(i*v),
Pplus    = L_(1/2),
Pminus   = L_(-1/2).
```

For the repository convention

```text
u = -log x,
phi(u) = exp(-u/2) g(exp(-u)),
```

these are exactly `Mg(1/2+iv)`, `Mg(1)`, and `Mg(0)`.

For a clipped mode, put

```text
c = -z + i*pi*n/a.
```

Away from `c = 0`, the probe proves

```text
L_z(chi_n) = (sqrt(2a))^-1 * (exp(c*a)-exp(-c*a))/c.
```

Production must define the removable branch first:

```text
intervalExpQuotient(a,c) =
  if c = 0 then 2*a else (exp(c*a)-exp(-c*a))/c.
```

The full transform theorem can then be used without introducing a false pole
on the critical contour. At `z = +/-1/2`, the denominator is automatically
nonzero.

## Actual clipped critical form

The intended pairing is

```text
B(f,g) = conj(Pplus f) Pminus g + conj(Pminus f) Pplus g
       + (1/(2*pi)) integral K(v) conj(Sample_v f) Sample_v g dv,
```

where `K` is the production `bombieriLocalCriticalKernel`.

The one missing analytic theorem needed to bundle this form is

```lean
theorem yoshidaCriticalCrossIntegrable (ha : 0 < a)
    (f g : YoshidaClippedSmooth a) :
    Integrable (fun v =>
      K v * star (Sample v f) * Sample v g)
```

Use interval integration by parts with `derivWithin` on `Icc (-a) a`:

```text
|Sample_v(f)| <=
  (|f(a)| + |f(-a)| + integral_{-a}^{a} |f'(x)| dx) / |v|.
```

Together with the existing logarithmic digamma bound, the cross integrand is
`O(log|v|/v^2)`. A convenient final majorant is a constant multiple of
`|v|^(-3/2)`. This proves integrability without asserting boundedness on all
ordinary `L²`.

## Smooth agreement

Crop a smooth Bombieri critical pullback to `Icc (-a) a`. Agreement with the
production smooth form must require that the original pullbacks already
vanish outside the interval:

```lean
theorem clippedForm_crop_eq_bombieri
    (hf : CriticalPullbackSupported a f)
    (hg : CriticalPullbackSupported a g) :
    clippedForm ha (crop a f) (crop a g) =
      bombieriLocalCriticalForm f g
```

An unconditional crop theorem is false because cropping discards data.

## Source pairing and sign convention

The repository coordinate `u = -log x` reflects Yoshida's printed additive
coordinate, so repository mode `n` represents source mode `-n`. The endpoint
formula is invariant under simultaneous negation, but production must prove

```text
eq516QBoundaryRhs(-n,-m) = eq516QBoundaryRhs(n,m)
```

rather than relying on prose.

The target off-diagonal theorem is

```lean
theorem yoshida_eq516Q {n m : ℤ} (hnm : n ≠ m) :
  ((-1)^(n+m) : ℂ) * clippedForm ha (chi n) (chi m) =
    (eq516QBoundaryRhs n m : ℂ)
```

Every `tsum` must have a companion `Summable` theorem, and every interchange
with an integral needs a proved majorant/Fubini theorem. The diagonal is the
separate source equation (5.15); (5.16) must never be totalized at `n = m`.

## Positive tail and Riesz interface

Keep low modes external:

```text
A = YoshidaClippedSmooth a,
V = a genuine periodic odd/even high-tail core,
incl : V -> A,
w = a low clipped mode in A.
```

Then `externalLowRieszCorrectionOfSqBound` applies exactly. A bare comap of
the existing `CircleL2` Fourier tail is larger than Yoshida's periodic
`K_N(a)` and cannot inherit the printed coercivity theorem without a new
proof.

Before constructing a positive form, prove the clipped-to-circle coordinate
map injective and prove that supported smooth pullbacks belong to the
periodic core. Endpoint jumps require `derivWithin` throughout.

## Production order

1. `YoshidaClippedDomain.lean`: carrier, modes, removable transform,
   centered Laplace maps, crop, and support predicate.
2. `YoshidaClippedCriticalForm.lean`: Fourier decay, cross-integrability,
   actual Hermitian form, and conditional smooth agreement.
3. `YoshidaClippedModePairing.lean`: reflection, RHS summability,
   (5.16-Q), separate (5.15), and odd/even reductions.
4. `YoshidaClippedTail.lean`: injective circle coordinates, periodic core,
   parity tails, coercivity restriction, and external Riesz corrections.

Smooth approximation may later be proved as a density theorem in an explicit
weighted Fourier norm. It is not the definition of the pairing.
