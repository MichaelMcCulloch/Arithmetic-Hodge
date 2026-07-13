# Centered Factor-Two Endpoint Plan

**Status:** Exact reduction complete and verified.  The two terminal profile
inequalities remain open; no finite certificate is admitted as their proof.

**Gate-3 obligation:** Keep the archimedean correlation and the retained
`p = 2,3` atoms coupled while transporting both signed factor-two endpoints
to the already developed endpoint-scale clean quadratic.

## Exact centered reduction

Put

```text
A     = log 2 / 2,
alpha = log 2 / sqrt 2,
beta  = log 3 / sqrt 3,
tau   = log(3/2) / A,
Cw(t) = integral[-1,1-t] w(t+x)w(x) dx.
```

For a real critical pullback supported on `[-A,A]`, define

```text
P(w) = A * integral[0,2] symmetricWeight(A t) Cw(t) dt
     - alpha Cw(0) - beta Cw(tau).
```

Prove at equality level

```text
D + R = A * (Q(w) + P(w)),
D - R = A * (Q(w) - P(w)),
```

where `Q` is `yoshidaEndpointOddCleanQuadratic`.  Split an arbitrary complex
test into its canonical coefficient-real and coefficient-imaginary profiles,
then prove normalized-dilation invariance so the canonical logarithmic center
of every ratio-two seed satisfies the support premise.

## Endpoint-pole extraction

On `0 < t < 2`, split the symmetric weight into its regular hyperbolic part
and the two explicit poles

```text
A * symmetricWeight(A t)
  = A * regularWeight(t)
  - 1 / (2(2+t)) - 1 / (2(2-t)).
```

The dangerous reflected pole obeys the structural square estimate

```text
2 * abs(Cw(2-t)) <= boundaryTail(w,t).
```

Prove the quotient is genuinely interval-integrable by an affine
fixed-unit-interval parametrization, reflect `t -> 2-t`, and fold the boundary
tail exactly to obtain

```text
integral[0,2] Cw(t)/(2-t) dt
  <= integral[-1,1] endpointPotential(x) w(x)^2 dx
   + log 2 * integral[-1,1] w(x)^2 dx.
```

This is a reusable infinite-dimensional bound, not a sampled or truncated
estimate.

## Validation

- Strict-check the focused module and root umbrella, then run the sequential
  full build.
- Audit the main public reduction and pole theorems with `#print axioms`.
- Recursively inspect the source closure for forbidden, quarantined,
  protected, missing, cyclic, or untracked dependencies.
- Recheck the archived and fallback inventories byte-for-byte.
- Stage only the production module, umbrella import, this plan, and the
  terminal-distance audit entry.

## Next make-or-break lemma

For every smooth real endpoint-zero profile arising from a centered
ratio-two seed, prove or strictly reverse both

```text
0 <= Q(w) + P(w),
0 <= Q(w) - P(w).
```

The plus sign is numerically weaker.  Scalar mass envelopes lose its small
margin, so the next proof must preserve the even low-mode direction and its
infinite-dimensional reserve.  A strict reverse supplies a genuine negative
factor-two endpoint; sampled positivity alone proves nothing.

## Route audit

The existing scalar reserve APIs cannot prove either sign.  In the
reflection-even sector, splitting the regular part and then bounding the two
poles and the retained prime lag separately leaves a mass coefficient below
`-0.84`, even after retaining the strongest zero-`P0`/`P2` tail reserve.  In
the reflection-odd sector, the reflected pole consumes half of the endpoint
potential while the exported coercivity estimate controls energy plus the
whole potential; the prime-lag correlation has no favorable sign.  These are
structural failures of the scalar route, not merely loose constants.

The next viable proof object is the complete clean-plus-perturbation operator.
On the even sector, project it against `P0` and `P2`, prove coercivity of the
modified zero-moment tail while retaining the regular kernel, both poles, and
the prime-shift operator together, and certify the two principal minors of the
modified Schur complement.  On the odd sector, add the full perturbation to
the existing ten-mode Gram and repeat its low/tail Schur argument; the current
`1/40` tail reserve is already fully spent and cannot absorb a separate norm
bound.

A 500-mode non-proof Galerkin search found no negative profile.  Its weakest
unscaled `D + R` value was about `6.67e-4`, concentrated in the even block;
the odd block remained around `1.43e-2`.  This supports continued positivity
work but supplies no lower bound, and it quantifies why cancellation-preserving
certification is mandatory.
