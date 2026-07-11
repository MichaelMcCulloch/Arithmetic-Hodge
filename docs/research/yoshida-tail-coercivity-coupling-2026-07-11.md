# Yoshida tail coercivity and low/high coupling audit

Date: 2026-07-11

Status: exact arithmetic and generic functional-analysis boundary verified in
strict Lean. The concrete Yoshida coercivity and pairing-decay inequalities
remain unproved and are listed below. This note does not claim ratio-two
positivity.

## Source and conventions

Primary source: Hiroyuki Yoshida, *On Hermitian Forms attached to Zeta
Functions*, Advanced Studies in Pure Mathematics 21 (1992), 281--325,
<https://doi.org/10.2969/aspm/02110281>.

The relevant locations are pp. 289--291 (Lemma 3 and the general tail),
pp. 293--295 (form-norm completion and Riesz correction), and pp. 302--310
(the ratio-two calculation, especially (6.5)--(6.27)). At ratio two,

```text
A = log(2)/2.
```

Yoshida's modes are Lebesgue-normalized on `[-A,A]`. The tail completion uses
the positive Hermitian form norm, not ordinary circle `L²`. The production
formalization must keep this distinct from Mathlib's probability-Haar circle
normalization.

The source's coercivity displays on p. 305 are non-strict:

```text
<phi,phi> >= 1.52 ||phi||_L2^2 on K_10(A),
<phi,phi> >= 4.08 ||phi||_L2^2 on K_199(A).
```

Thus the source constants and cutoffs are

```text
mu_odd  = 38/25,    first odd high mode  = 11,
mu_even = 102/25,   first even high mode = 200.
```

The paper prints `K_10,even` in the later even correction paragraph, but its
own (6.9), low block `w_0,...,w_199`, expansion `eta_k = w_{k+199}`, and
200-by-200 matrix force `K_199,even`. Production must use 199.

## Strict discovery probes

The final reviewed probes are external to the worktree:

```text
/tmp/YoshidaTailCoercivityProbe.lean
SHA-256 2c6e10df8420a8de866bf62139a09f42090ffd661d90697ee1b84307d41c124a

/tmp/YoshidaLowTailCouplingProbe.lean
SHA-256 ebbeee48bc0a96dcde9e9541b135faa54149a5a84d2a46a10875ba10996d76fc
```

Both pass `lake env lean -DwarningAsError=true`. Forbidden-proof scans are
clean. Exhaustive theorem audits report only
`[propext, Classical.choice, Quot.sound]`. The second hash includes the
post-review correction that instantiates the external-low-mode Riesz API.

## Exact coupling constants

Equations (6.19) and (6.27) define

```text
C1 = (2A/pi^2) * (exp(A/2)-exp(-A/2))^2
   + (2A exp(-A))/(pi^2 (1-exp(-4A)))
   + (1/2 + A/(2 pi^2)),

C2 = (2A/pi^2) * (exp(A/2)-exp(-A/2))^2
   + (2A exp(-A))/(pi^2 (1-exp(-4A)))
   + (1/2 + (2A)^2/(10 pi^3)).
```

The source gives decimal checks `C1^2 = 0.3508...` and
`C2^2 = 0.3321...`. The probes replace those decimals with exact kernel
certificates. They prove

```text
exp(-A) = 1/sqrt(2),
exp(-4A) = 1/4,
(exp(A/2)-exp(-A/2))^2 = 3/sqrt(2)-2,
sqrt(2) > 7/5,
log(2) < 7/10,
pi > 3.
```

For production, use one canonical enclosure chain: the tail probe's shared
term bounds `3/250` and `3/40`, with final terms `13/25` and `251/500`.
This gives

```text
C1 < 607/1000,    C1^2 < 19/50,
C2 < 589/1000,    C2^2 <= 10149/25000.
```

The coupling probe contains a second valid but redundant chain using
`1/90` and `2/27`; do not duplicate both in production.

Independent numerical evaluation, used only as a review check and not as a
trusted proof step, was

```text
C1 = 0.592291954285565,  C1^2 = 0.350809759111413,
C2 = 0.576283865784586,  C2^2 = 0.332103093963626.
```

## Exact tail sums and budgets

The probes prove the reciprocal-square telescope and its infinite `tsum`
consequence, rather than assuming a decimal zeta value:

```text
sum_{m >= M} 1/m^2 <= 1/(M-1),  M >= 2.
```

Consequently, once the concrete pointwise decays (6.18) and (6.26) are
available,

```text
odd source sum
  <= C1^2 * sum_{m>=11} 1/m^2
  <= (19/50)/10
  = 19/500,

even source sum
  <= C2^2 * sum_{m>=200} 1/m^2
  <= (10149/25000)/199
  = 51/25000.
```

The correction arithmetic is then exact:

```text
(19/500)/(38/25) = 1/40,
(51/25000)/(102/25) = 1/2000.
```

The even identity uses `10149 = 51 * 199`. Keeping `mu_even = 102/25`
matches the printed source threshold directly; replacing it by `4` would
create an unnecessary strengthening obligation.

## Correct form-completion bridge

Yoshida's low modes are not elements of the positive high-tail vector space.
Therefore the source-faithful correction is not the same-space constructor

```text
FormSpace.formRieszCorrectionOfSqBound (w : V).
```

It is the reviewed external-low-mode constructor

```text
FormSpace.externalLowRieszCorrectionOfSqBound
  (B : A ->ₗ⋆[C] A ->ₗ[C] C)
  (hB : forall x y, star (B y x) = B x y)
  (incl : V ->ₗ[C] A)
  (w : A)
  ...
```

where `V` is the positive tail, `A` is the ambient Yoshida test space, and
`w` is an external low mode. The corrected coupling probe proves generic odd
and even wrappers yielding squared correction norms at most `1/40` and
`1/2000`, respectively. The earlier same-space wrappers remain mathematically
valid but are not the direct Yoshida instantiation.

## Already verified general tail machinery

The tail probe also strict-compiles:

- exact monotonicity on `v >= 0` of
  `Re digamma (1/4 + i v/2)`, derived from the repository's partial-fraction
  series;
- the algebraic cancellation in Yoshida's Fourier multiplier (6.5);
- finite weighted Cauchy--Schwarz;
- one-sided and paired inverse-square tail bounds, antitonicity, and
  convergence to zero;
- the general eventual-smallness statement used in Section 3;
- exact weakening from `38/25` to `3/2`, kept separately from the source
  theorem.

These are reusable ingredients, not a proof of the concrete Section 6 tail
coercivity.

## Honest remaining obligations

The following source-specific results are still missing:

1. Realize the full Fourier identity (6.5) for the actual smooth parity tails.
2. Prove the paired denominator and integral estimate (6.6).
3. Certify the special-function numerics and substitutions in (6.7), yielding
   the non-strict coercivity theorems (6.8) and (6.9).
4. Define the concrete ambient Yoshida Hermitian form and reconcile its
   Lebesgue-normalized modes with the probability-Haar circle carrier.
5. Prove pairing identities (5.16), (6.17), and (6.25), including the
   digamma remainder used after (5.11).
6. Derive the pointwise decays (6.18) and (6.26), thereby discharging the
   conditional source-sum hypotheses.
7. Feed the concrete external low-mode functionals into the form completion,
   then combine the corrections with the exact finite Gram certificates and
   `HilbertTailSchur`.

## Exact Section 6 substitution boundary and source typo

The 426-line strict probe `/tmp/YoshidaCoercivityNumericsProbe.lean` has
SHA-256
`8f46260a97c36c98498b51d2570cb8cb8ce3820fe96bd31b72f5c9c7c2083143`.
It formalizes the exact right side of (6.7), proves the two denominator-domain
conditions, discharges elementary enclosures for `log 2`, `1/sqrt 2`,
`A`, `pi^3`, `log pi`, and the oscillatory window, and reduces the final
substitutions to named source-aligned certificates.

For the odd case it proves that

```text
C(50) in [1609/500, 3219/1000],
D_10(50) <= 283/500,
D_10(t0) <= 77/200
```

imply the exact non-strict output `38/25 <= formValue`, once the analytic
inequality (6.7) is supplied. For the even case it proves that

```text
C(700) in [5857/1000, 5858/1000],
D_199(700) <= 53/2000,
D_199(t0) <= 101/5000
```

imply `102/25 <= formValue`.

Direct inspection of the primary PDF image at printed p. 305 confirms that
the paper says both `t1 = 700` and `C = 5.9914...`, where immediately above
`C = Re psi(1/4 + i t1/2)`. These values are incompatible:

```text
C(700) = 5.857933069449...,
C(800) = 5.991464482003....
```

Thus this is almost certainly a source numerical typo, not OCR or a digamma
convention change. The strict probe records the rational incompatibility and
does not encode the printed `5.9914` as a valid lower bound. The honest
interval `[5.857,5.858]` still has enough margin to prove `4.08` from (6.7).

The remaining substitution certificates are the two digamma intervals, the
four weighted-tail bounds, the `t0`/Gamma-argument low-interval certificate,
and the upstream analytic derivation of (6.7). No floating-point value is a
trusted premise of the Lean results.

## Recommended production order

1. Promote generic tail-series lemmas and one canonical `C1/C2` certificate
   module.
2. Prove the concrete parity multiplier and certified coercivity numerics
   (6.5)--(6.9).
3. Prove concrete mode pairings and decays (5.16), (6.17)--(6.18), and
   (6.25)--(6.26).
4. Instantiate only the external-low-mode Riesz corrections, then assemble
   the odd and even Schur complements.
