# Even Tail Representer Structural Reduction

## Goal

Reduce positivity of the clean endpoint quadratic on a continuous even profile
to two fixed analytic statements: positivity of its `P₀/P₂` low Gram matrix
and a uniform weighted dual-Gram inequality for two explicit tail
representers.

## Definitions

- The tail weight is
  `W(x) = 41/60 + yoshidaEndpointPotential x`.
- For a low profile `p`, its regular-kernel representer is
  `rho(p,x) = ∫ y in Icc (-1) 1, K(a*|x-y|) p(y)`.
- Its total even-tail representer is
  `F(p,x) = V(x)p(x) - a*rho(p,x)
    + 2*a*C(p)*cosh(a*x/2)`.
- The two fixed representers are `F₀ = F(P₀)` and `F₂ = F(P₂)`.
- The fixed low Gram entries are the clean quadratic's bilinear values on
  `P₀` and `P₂`.

The scalar mass term is absent from `F` because tails are orthogonal to both
low modes. The logarithmic-difference term is absent because its `P₀` cross
vanishes pointwise and its `P₂` cross is exactly a multiple of the `P₂`
pairing, hence zero on the tail.

## Exact identities

For every continuous even tail `r` with `P₀(r)=P₂(r)=0`, prove structurally
that each low-tail clean bilinear pairing is the interval integral of its
representer against `r`. Prove the regular-kernel identity by Fubini and
kernel symmetry, the `P₂` raw-energy cancellation symbolically, and the
hyperbolic cancellation from evenness. No numerical bounds or finite mode
checks enter these identities.

Use these identities to expand the clean quadratic of
`c*P₀ + b*P₂ + r` exactly into the low Gram quadratic, two representer
pairings, and the tail quadratic.

## Positivity reduction

Assume only:

1. `q₀₀ > 0` and `q₀₀*q₂₂ - q₀₂^2 > 0`;
2. for every real `c,b`, the weighted dual norm of `c*F₀+b*F₂` is at most
   `q₀₀*c^2 + 2*q₀₂*c*b + q₂₂*b^2`;
3. the ordinary measurability and `MemLp` hypotheses required by weighted
   Cauchy.

Weighted Cauchy converts item 2 into the adjugate Schur inequality. The
existing tail reserve bounds the weighted tail norm by the clean tail
quadratic, and `TwoByTwoSchur.quadratic_add_tail_nonneg` finishes positivity.

## Verification

Develop by RED/GREEN with root `just` commands. Before committing, run the
strict checker, focused build, public-theorem axiom audit, and forbidden
computation/certificate dependency scan. Commit only the new module and this
design record.
