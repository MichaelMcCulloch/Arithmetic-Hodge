import ArithmeticHodge.Analysis.MultiplicativeWeilPrimeCorrelation

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Exact polarization of the global Bombieri quadratic

A support decomposition creates a genuine mixed Bombieri test.  The exact
global formula below shows that its local Hermitian cross is accompanied by
the corresponding mixed prime term; neither can be discarded.
-/

/-- The mixed part of the quadratic autocorrelation of `f + g`. -/
def bombieriQuadraticCrossTest (f g : BombieriTest) : BombieriTest :=
  bombieriQuadraticTest (f + g) -
    bombieriQuadraticTest f - bombieriQuadraticTest g

/-- Exact quadratic decomposition into two diagonals and their mixed test. -/
theorem bombieriQuadraticTest_add_eq_diagonal_add_cross
    (f g : BombieriTest) :
    bombieriQuadraticTest (f + g) =
      bombieriQuadraticTest f + bombieriQuadraticTest g +
        bombieriQuadraticCrossTest f g := by
  unfold bombieriQuadraticCrossTest
  abel

/-- Applying Bombieri's linear functional preserves the exact diagonal/cross
decomposition. -/
theorem bombieriFunctional_quadratic_add_eq_diagonal_add_cross
    (f g : BombieriTest) :
    bombieriFunctional (bombieriQuadraticTest (f + g)) =
      bombieriFunctional (bombieriQuadraticTest f) +
        bombieriFunctional (bombieriQuadraticTest g) +
          bombieriFunctional (bombieriQuadraticCrossTest f g) := by
  rw [bombieriQuadraticTest_add_eq_diagonal_add_cross]
  simp only [map_add]

/-- The mixed global functional is the symmetric local Hermitian cross minus
the mixed prime correlation. -/
theorem bombieriFunctional_quadraticCross_eq_localCross_sub_prime
    (f g : BombieriTest) :
    bombieriFunctional (bombieriQuadraticCrossTest f g) =
      bombieriLocalCriticalForm f g + bombieriLocalCriticalForm g f -
        primeSum (bombieriQuadraticCrossTest f g) := by
  unfold bombieriQuadraticCrossTest
  change bombieriFunctional
      (bombieriQuadraticTest (f + g) -
        bombieriQuadraticTest f - bombieriQuadraticTest g) =
    bombieriLocalCriticalForm f g + bombieriLocalCriticalForm g f -
      primeSumLinearMap
        (bombieriQuadraticTest (f + g) -
          bombieriQuadraticTest f - bombieriQuadraticTest g)
  simp only [map_sub]
  have hglobal (h : BombieriTest) :
      bombieriFunctional (bombieriQuadraticTest h) =
        bombieriLocalCriticalForm h h -
          primeSumLinearMap (bombieriQuadraticTest h) := by
    exact bombieriFunctional_quadratic_eq_localCritical_sub_prime h
  rw [hglobal (f + g), hglobal f, hglobal g]
  simp only [map_add, LinearMap.add_apply]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
