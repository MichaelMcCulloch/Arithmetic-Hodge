import ArithmeticHodge.Analysis.MultiplicativeWeilFixedLogLatticeGramStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilGlobalCrossZeroExpansionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilCriterion

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ComplexConjugate ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Absolute-mass obstruction on the fixed logarithmic lattice

Under RH, normalized dilation contributes only a unit-modulus phase to every
individual zero-side term.  Consequently the termwise absolute mass of a
fixed-seed lattice cross is exactly its diagonal spectral mass at every lag.
In particular, absolute summation cannot supply far-lag decay.
-/

/-- The individual zero-side summand for a fixed seed at an integer lattice
lag. -/
def fixedLogLatticeZeroSideTerm
    (zeros : ZetaZeroEnumeration) (g : BombieriTest) (k : ℤ) (n : ℕ) : ℂ :=
  ((fixedLogLatticePoint k : ℝ) : ℂ) ^
        ((1 / 2 : ℂ) - (zeros.zero n).val) *
    mellin (g : ℝ → ℂ) (zeros.zero n).val *
      coefficientConjugate (mellin (g : ℝ → ℂ))
        (1 - (zeros.zero n).val)

/-- The preceding summand is exactly the finalized zero-side expansion of
the fixed-seed global cross at lattice lag `k`. -/
theorem bombieriTwoBlockGlobalCrossSymbol_fixedLogLattice_eq_zeroSum
    (zeros : ZetaZeroEnumeration) (g : BombieriTest) (k : ℤ) :
    bombieriTwoBlockGlobalCrossSymbol g
        (normalizedDilation (fixedLogLatticePoint k)
          (fixedLogLatticePoint_pos k) g) =
      ∑' n, fixedLogLatticeZeroSideTerm zeros g k n := by
  simpa only [fixedLogLatticeZeroSideTerm] using
    (bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_zeroSum
      zeros g g (fixedLogLatticePoint k) (fixedLogLatticePoint_pos k))

/-- On the critical line, the fixed-lattice dilation factor has unit norm. -/
theorem norm_fixedLogLatticePoint_cpow_half_sub_eq_one
    (k : ℤ) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖((fixedLogLatticePoint k : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - s)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (fixedLogLatticePoint_pos k)]
  simp [hs]

/-- On the critical line, coefficient conjugation at the reflected argument
is ordinary conjugation at the original argument. -/
theorem coefficientConjugate_one_sub_eq_conj_of_re_eq_half
    (F : ℂ → ℂ) {s : ℂ} (hs : s.re = 1 / 2) :
    coefficientConjugate F (1 - s) = starRingEnd ℂ (F s) := by
  have hreflect : starRingEnd ℂ (1 - s) = s := by
    apply Complex.ext
    · simp only [map_sub, map_one, sub_re, one_re, conj_re]
      linarith
    · simp
  unfold coefficientConjugate
  rw [hreflect]

/-- Under RH, the norm of each fixed-lattice zero-side summand is the same
squared Mellin norm, independently of the lag. -/
theorem norm_fixedLogLatticeZeroSideTerm_eq_normSq_of_rh
    (zeros : ZetaZeroEnumeration) (hRH : RiemannHypothesis)
    (g : BombieriTest) (k : ℤ) (n : ℕ) :
    ‖fixedLogLatticeZeroSideTerm zeros g k n‖ =
      Complex.normSq (mellin (g : ℝ → ℂ) (zeros.zero n).val) := by
  have hcritical : (zeros.zero n).val.re = 1 / 2 :=
    zeros.zero_re_eq_half_of_rh hRH n
  unfold fixedLogLatticeZeroSideTerm
  rw [coefficientConjugate_one_sub_eq_conj_of_re_eq_half _ hcritical,
    norm_mul, norm_mul,
    norm_fixedLogLatticePoint_cpow_half_sub_eq_one k hcritical]
  change
    1 * ‖mellin (g : ℝ → ℂ) (zeros.zero n).val‖ *
        ‖conj (mellin (g : ℝ → ℂ) (zeros.zero n).val)‖ = _
  rw [Complex.norm_conj, Complex.normSq_eq_norm_sq]
  ring

/-- The termwise absolute zero-side mass is independent of the integer lag
and equals the exact norm-square zero sum. -/
theorem fixedLogLattice_zeroSide_absoluteMass_eq_tsum_normSq_of_rh
    (zeros : ZetaZeroEnumeration) (hRH : RiemannHypothesis)
    (g : BombieriTest) (k : ℤ) :
    ∑' n, ‖fixedLogLatticeZeroSideTerm zeros g k n‖ =
      ∑' n, Complex.normSq
        (mellin (g : ℝ → ℂ) (zeros.zero n).val) := by
  apply tsum_congr
  intro n
  exact norm_fixedLogLatticeZeroSideTerm_eq_normSq_of_rh zeros hRH g k n

/-- At every fixed-log-lattice lag, the termwise absolute zero-side mass is
exactly the real Bombieri diagonal.  Thus it cannot decay with the lag unless
the diagonal itself vanishes. -/
theorem fixedLogLattice_zeroSide_absoluteMass_eq_diagonal_of_rh
    (zeros : ZetaZeroEnumeration) (hRH : RiemannHypothesis)
    (g : BombieriTest) (k : ℤ) :
    ∑' n, ‖fixedLogLatticeZeroSideTerm zeros g k n‖ =
      (bombieriFunctional (bombieriQuadraticTest g)).re := by
  let a : ℕ → ℂ := fun n ↦
    (Complex.normSq
      (mellin (g : ℝ → ℂ) (zeros.zero n).val) : ℂ)
  have hterm : ∀ n,
      mellin (bombieriQuadraticTest g : ℝ → ℂ) (zeros.zero n).val = a n := by
    intro n
    exact (bombieriQuadraticTestData_hasMellin g (zeros.zero n).val).2.trans
      (spectralTerm_eq_normSq_of_re_eq_half
        (g : ℝ → ℂ) (zeros.zero_re_eq_half_of_rh hRH n))
  have hsummable : Summable a :=
    (zeros.mellin_summable (bombieriQuadraticTest g)).congr hterm
  have hdiagonal :
      bombieriFunctional (bombieriQuadraticTest g) = ∑' n, a n := by
    simpa only [a] using
      (rh_bombieriFunctional_quadratic_eq_tsum_normSq zeros
        (bombieriZeroSumFormula zeros) hRH g)
  have hrealPart :
      (∑' n, a n).re =
        ∑' n, Complex.normSq
          (mellin (g : ℝ → ℂ) (zeros.zero n).val) := by
    change Complex.reCLM (∑' n, a n) = _
    rw [Complex.reCLM.map_tsum hsummable]
    apply tsum_congr
    intro n
    simp only [a, Complex.reCLM_apply, Complex.ofReal_re]
  rw [fixedLogLattice_zeroSide_absoluteMass_eq_tsum_normSq_of_rh
    zeros hRH g k]
  calc
    ∑' n, Complex.normSq
        (mellin (g : ℝ → ℂ) (zeros.zero n).val) =
        (∑' n, a n).re := hrealPart.symm
    _ = (bombieriFunctional (bombieriQuadraticTest g)).re :=
      (congrArg Complex.re hdiagonal).symm

/-- Explicit lag independence of the termwise absolute zero-side mass. -/
theorem fixedLogLattice_zeroSide_absoluteMass_eq_of_rh
    (zeros : ZetaZeroEnumeration) (hRH : RiemannHypothesis)
    (g : BombieriTest) (k l : ℤ) :
    (∑' n, ‖fixedLogLatticeZeroSideTerm zeros g k n‖) =
      ∑' n, ‖fixedLogLatticeZeroSideTerm zeros g l n‖ := by
  rw [fixedLogLattice_zeroSide_absoluteMass_eq_diagonal_of_rh
      zeros hRH g k,
    fixedLogLattice_zeroSide_absoluteMass_eq_diagonal_of_rh
      zeros hRH g l]

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
