/-
  Compatibility import for the sound canonical-product growth API.

  The former `weierstraß_quotient_growth` accepted an arbitrary
  factorization and was false: exponential factors can be shifted between the
  logarithm and a noncanonical product without preserving its claimed bound.
  `CanonicalGrowth` instead fixes the genus, records analytic multiplicities,
  and requires summability at an intermediate exponent.
-/

import ArithmeticHodge.Analysis.EntireFunction.CanonicalGrowth
