import Mathlib

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaOddDigammaRationalCertificate

/-!
# Rational certificate for the odd low-digamma integral

This module contains only the exact rational computation.  Its interpretation
as a Riemann majorant for the negative digamma integral is proved separately,
so rebuilding that analytic proof does not repeatedly evaluate the large
kernel-checked sum.
-/

def gammaUpperQ : ℚ := 5773 / 10000

def gridEndpointQ : ℚ := 51 / 25

def gridCount : ℕ := 1024

def seriesCount : ℕ := 100

def gridStepQ : ℚ := gridEndpointQ / gridCount

def shiftedReciprocalQ (v : ℚ) (k : ℕ) : ℚ :=
  ((1 / 4 : ℚ) + k) /
    (((1 / 4 : ℚ) + k) ^ 2 + (v / 2) ^ 2)

def quarterTermQ (v : ℚ) (n : ℕ) : ℚ :=
  1 / (n + 1 : ℕ) - shiftedReciprocalQ v (n + 1)

def partialLowerQ (v : ℚ) : ℚ :=
  -gammaUpperQ - shiftedReciprocalQ v 0 +
    ∑ n ∈ Finset.range seriesCount, quarterTermQ v n

def cellLossQ (j : ℕ) : ℚ :=
  max (-partialLowerQ (j * gridStepQ)) 0

def riemannLossQ : ℚ :=
  gridStepQ * ∑ j ∈ Finset.range gridCount, cellLossQ j

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem riemannLossQ_lt_target :
    riemannLossQ < (2773 / 1000 : ℚ) := by
  decide +kernel

end ArithmeticHodge.Analysis.YoshidaOddDigammaRationalCertificate
