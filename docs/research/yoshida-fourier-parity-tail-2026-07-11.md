# Yoshida Fourier parity and tail decomposition

Date: 2026-07-11

Status: projection, parity, and normalized-mode layers are in production.
The coefficient-plus-tail decomposition and the clipped-mode pairing extension
remain to be promoted.

## Result

The probe
`/tmp/YoshidaFourierParityTailProbe.lean` strict-compiles with SHA-256
`7823338c6144f7e6c9cb9b9c7623b41af41ca3bebb60666889f0a30ef836bd33`
at the time this note was recorded. It proves:

- the finite Fourier projection and its closed coefficient-kernel tail;
- measure preservation of negation for normalized Haar measure on
  `AddCircle T`;
- a continuous involutive reflection on circle `L²`;
- closed even and odd submodules and complete even/odd Fourier tails;
- exact conversion between probability-Haar Fourier modes and
  Lebesgue-normalized modes;
- Yoshida's normalized sine and cosine families;
- the exact `Fin 10` odd family with frequencies `1, ..., 10`;
- the exact `Fin 200` even family with frequencies `0, ..., 199`;
- equality of those families' spans with the corresponding finite parity
  Fourier spaces; and
- coefficient-plus-tail decompositions ready for a finite corrected Gram
  matrix.

Root independently ran

```text
lake env lean -DwarningAsError=true /tmp/YoshidaFourierParityTailProbe.lean
```

with exit zero. The forbidden-proof scan is clean. Audited declarations depend
only on `[propext, Classical.choice, Quot.sound]`.

## Projection and tail API

For

```lean
abbrev CircleL2 := Lp ℂ 2 (@haarAddCircle T hT)
```

the probe defines a bundled Fourier coefficient functional and the closed
simultaneous kernel of the coefficients in `[-N,N]`:

```lean
def fourierCoeffCLM (n : ℤ) : StrongDual ℂ CircleL2

abbrev LowIndex (N : ℕ) :=
  {n : ℤ // n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)}

def fourierTailSubmodule (N : ℕ) : Submodule ℂ CircleL2

def lowFourierProjection (N : ℕ) (f : CircleL2) : CircleL2

def finiteFourierSubmodule (N : ℕ) : Submodule ℂ CircleL2
```

The main results are:

```lean
fourierTailSubmodule_isClosed
lowFourierProjection_eq_self_of_mem_finiteFourierSubmodule
fourierCoeff_lowFourierProjection
sub_lowFourierProjection_mem_tail
```

Thus the finite expression is a genuine projection onto the finite Fourier
span and its remainder belongs to the exact closed high-frequency tail.

## Reflection and parity API

Negation invariance is proved through uniqueness of probability Haar measure,
not assumed:

```lean
def circleNegMeasurePreserving :
  MeasurePreserving (Neg.neg : AddCircle T → AddCircle T)
    haarAddCircle haarAddCircle

def reflectionL2 : CircleL2 →L[ℂ] CircleL2
```

The probe proves

```text
reflectionL2 (reflectionL2 f) = f
reflectionL2 (fourierLp 2 n) = fourierLp 2 (-n)
fourierCoeff (reflectionL2 f) n = fourierCoeff f (-n).
```

Even and odd spaces are closed kernels of `reflectionL2 - id` and
`reflectionL2 + id`. Their intersections with the Fourier tail are closed
and receive `CompleteSpace` instances. The algebraic projections

```text
evenPart f = 2⁻¹ • (f + reflectionL2 f)
oddPart  f = 2⁻¹ • (f - reflectionL2 f)
```

land in the correct parity spaces and sum to `f`.

## Lebesgue normalization

Mathlib's `fourierLp` is orthonormal for probability Haar measure. Yoshida's
section 6 modes are orthonormal for Lebesgue measure on a circle of length
`T`. The probe therefore defines

```lean
def lebesgueNormalizedExponential (n : ℤ) : CircleL2 :=
  ((Real.sqrt T)⁻¹ : ℂ) • fourierLp 2 n

def lebesgueNormSq (f : CircleL2) : ℝ :=
  T * ‖f‖ ^ 2
```

and proves against the actual volume measure:

```lean
theorem integral_norm_sq_volume_eq_lebesgueNormSq (f : CircleL2) :
  ∫ x : AddCircle T, ‖f x‖ ^ 2 = lebesgueNormSq f

theorem integral_norm_sq_volume_lebesgueNormalizedExponential (n : ℤ) :
  ∫ x : AddCircle T, ‖lebesgueNormalizedExponential n x‖ ^ 2 = 1
```

This prevents a silent factor-of-`T` error between normalized Haar and
Yoshida's Lebesgue convention.

## Exact Yoshida families

The normalized modes are

```lean
def yoshidaOddMode (n : ℕ) : CircleL2 :=
  (-Complex.I / (Real.sqrt 2 : ℂ)) • (chi n - chi (-n))

def yoshidaEvenMode (n : ℕ) : CircleL2 :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (chi n + chi (-n))

def yoshidaEvenZeroMode : CircleL2 := chi 0
```

where `chi` abbreviates the Lebesgue-normalized exponential. The probe proves
their parity, exact Fourier coefficients, mutual exponential orthogonality,
and Lebesgue norm squared one.

The finite indices contain no cutoff ambiguity:

```lean
abbrev YoshidaOddIndex := Fin 10
abbrev YoshidaEvenIndex := Fin 200

def yoshidaOddLowMode (i : Fin 10) :=
  yoshidaOddMode (i.1 + 1)

def yoshidaEvenLowMode (i : Fin 200) :=
  if i.1 = 0 then yoshidaEvenZeroMode else yoshidaEvenMode i.1
```

Consequently the odd frequencies are exactly `1, ..., 10`, while the even
frequencies are exactly `0, ..., 199`.

## Span equalities and matrix-ready decomposition

The difficult reverse inclusions are strict-proved:

```lean
theorem yoshidaOddLowSubmodule_eq_parity_finite :
  yoshidaOddLowSubmodule =
    oddL2Submodule ⊓ finiteFourierSubmodule 10

theorem yoshidaEvenLowSubmodule_eq_parity_finite :
  yoshidaEvenLowSubmodule =
    evenL2Submodule ⊓ finiteFourierSubmodule 199
```

They are not dimension-count placeholders: the proof explicitly expresses
each `fourierLp n - fourierLp (-n)` or
`fourierLp n + fourierLp (-n)` as a nonzero scalar multiple of the matching
Yoshida mode, with the zero even mode treated separately.

The final APIs are:

```lean
theorem exists_yoshida_odd_ten_coefficients_add_tail
    (hf : f ∈ oddL2Submodule) :
  ∃ c : Fin 10 → ℂ,
    f = (∑ i, c i • yoshidaOddLowMode i) +
      (oddTailRemainder 10 hf : CircleL2)

theorem exists_yoshida_even_twoHundred_coefficients_add_tail
    (hf : f ∈ evenL2Submodule) :
  ∃ c : Fin 200 → ℂ,
    f = (∑ i, c i • yoshidaEvenLowMode i) +
      (evenTailRemainder 199 hf : CircleL2)
```

These decompositions are sufficient for the finite-matrix argument: if both
the coefficient function and tail vanish, the displayed equality forces the
original parity function to vanish.

## Production split

Do not land the 1000-line probe as one module. Split it into:

1. `CenteredAddCircleFourierProjection.lean`: bundled coefficients, finite
   projection, finite span, and closed coefficient tail.
2. `CenteredAddCircleFourierParity.lean`: negation invariance, reflection,
   even/odd kernels, parity projections, and complete parity tails.
3. `YoshidaFourierModes.lean`: Lebesgue normalization, normalized
   sine/cosine modes, and the exact `Fin 10`/`Fin 200` families.
4. `YoshidaFourierDecomposition.lean`: span equalities and the final
   coefficient-plus-tail decompositions.

The first three layers landed through commits `95e4e5d`, `1f0753d`, and
`e8ed283`. The fourth is the remaining production port from the strict probe.

The production port must import the existing centered Fourier facade rather
than duplicating its symmetry or Parseval results, and must instantiate
`T = 2 * a` behind the centered-circle boundary.

## Exact Hermitian-pairing formula audit

The independent 509-line strict probe
`/tmp/YoshidaModePairingProbe.lean`, SHA-256
`08ec08875bfaf46d4bdcf362a36d13bedf9a96a9b874af366390ce1c0e6abef6`,
checks the normalization and algebra needed to connect the modes to Yoshida's
source formulas. It passes warning-as-error compilation and a forbidden-proof
scan; every audited theorem uses only
`[propext, Classical.choice, Quot.sound]`.

For `a = log 2 / 2`, write

```text
Delta = exp(a/2) - exp(-a/2),
q_k   = 2k + 1/2,
d_n   = 1 + (2*pi*n/a)^2,
D_kn  = q_k^2 + (pi*n/a)^2,
y_n   = Im psi(1/4 + pi*i*n/(2a)).
```

For distinct integers `n,m`, the audited endpoint specialization of (5.16)
is

```text
(-1)^(n+m) <chi_n,chi_m>
  = (4/a) Delta^2 (1 - 4*pi^2*n*m/a^2)/(d_n*d_m)
    - (1/a) sum_k
        ((q_k^2 - pi^2*n*m/a^2) exp(-2*a*q_k))/(D_kn*D_km)
    + (y_n-y_m)/(2*pi*(n-m)).
```

At this endpoint the prime-power term really vanishes: the only possible
term is `p = 2, e = 1`, and both relevant sine factors are integer multiples
of `2*pi`. This is not an omitted hypothesis.

For positive distinct indices, the probe then represents and algebraically
reduces the odd formula (6.17) to

```text
(-1)^(n+m) <w_n^odd,w_m^odd>
  = -(4/a) Delta^2 (8*pi^2*n*m/a^2)/(d_n*d_m)
    + (2/a) sum_k
        ((pi^2*n*m/a^2) exp(-2*a*q_k))/(D_kn*D_km)
    + (y_n-y_m)/(2*pi*(n-m))
    - (y_n+y_m)/(2*pi*(n+m)),
```

and the nonzero even formula (6.25) to

```text
(-1)^(n+m) <w_n^even,w_m^even>
  = (4/a) Delta^2 2/(d_n*d_m)
    - (2/a) sum_k
        (q_k^2 exp(-2*a*q_k))/(D_kn*D_km)
    + (y_n-y_m)/(2*pi*(n-m))
    + (y_n+y_m)/(2*pi*(n+m)).
```

When one even index is zero, the right side has the additional exact factor
`1/sqrt 2`; the probe proves this from the sesquilinear normalization rather
than copying it as an unexplained constant. The first slot is consistently
conjugate-linear and the second is linear.

## Clipped-mode domain boundary

The smooth Bombieri local critical form can now be polarized, but Yoshida's
`chi_n` is a clipped exponential: it is smooth inside `(-a,a)` and jumps to
zero outside `[-a,a]`. It belongs to Yoshida's extended space `K(a)`, not to
the repository's smooth `BombieriTest` type. Consequently the new smooth form
cannot simply be applied to `yoshidaChi n`, nor may boundedness on ordinary
circle `L2` be assumed.

The smallest honest analytic bridge is a theorem on an admissible compact-
support domain containing the clipped exponentials:

```text
(-1)^(n+m) * B_K(chi_n,chi_m)
  = eq516QBoundaryRhs(n,m),  n != m.
```

Once that theorem is available, the already checked odd/even reductions yield
(6.17), (6.25), and the zero-mode factor. The source-faithful route is to
define the explicit local distribution form on this larger admissible domain
and prove agreement with the smooth Bombieri form where both are defined.
Controlled approximation in the form topology is an alternative, but an
ordinary-`L2` continuity claim would be false at this level of generality.

## Remaining critical obligations

This closes the Fourier decomposition boundary, not Yoshida positivity. The
remaining work is:

1. construct the form-norm completion of each algebraic parity tail;
2. prove Yoshida's high-tail coercivity constants;
3. extend each low-tail pairing continuously in the form norm;
4. form and certify the corrected odd/even finite Gram matrices; and
5. transport strict parity positivity through the local Bombieri functional.
