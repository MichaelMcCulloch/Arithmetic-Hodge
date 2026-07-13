import ArithmeticHodge.Analysis.YoshidaFactorTwoParityRealification

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeDomination

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilRestrictedSupportEndpointPositive
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoDiagonalPhysical
open YoshidaFactorTwoParityRealification

/-!
# Signed factor-two channels as local-form/prime domination

The complete positive digamma residual is recombined with the indefinite core.
Each signed real channel is one half of the actual local critical self-form of
`g ± normalizedDilation 2 g`, together with the correctly signed two-prime
symbol.  Thus no residual series or core-only comparison remains in the open
coercivity statement.

The tests `g ± normalizedDilation 2 g` have support hull of ratio at most four,
so their local critical quadratic is not known nonnegative.  These identities
only expose the two endpoint channels `D ± R`; they do not control the mixed
`Ω` channel or the interior phase pencil.
-/

private theorem bombieriLocalCriticalForm_dilation_two_self_re_eq
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (bombieriLocalCriticalForm
        (normalizedDilation 2 (by norm_num) g)
        (normalizedDilation 2 (by norm_num) g)).re =
      (bombieriLocalCriticalForm g g).re := by
  have hsupportD : tsupport (normalizedDilation 2 (by norm_num) g) ⊆
      Set.Icc (a / 2) (b / 2) :=
    normalizedDilation_tsupport_subset_Icc
      2 (by norm_num) g hsupport
  have haD : 0 < a / 2 := by positivity
  have habD : a / 2 ≤ b / 2 := by linarith
  have hratioD : (b / 2) / (a / 2) ≤ 2 := by
    rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0) b a]
    exact hratio
  calc
    (bombieriLocalCriticalForm
        (normalizedDilation 2 (by norm_num) g)
        (normalizedDilation 2 (by norm_num) g)).re =
        (bombieriFunctional
          (bombieriQuadraticTest
            (normalizedDilation 2 (by norm_num) g))).re := by
      exact congrArg Complex.re
        (bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
          (normalizedDilation 2 (by norm_num) g)
          haD habD hsupportD hratioD).symm
    _ = (bombieriFunctional (bombieriQuadraticTest g)).re := by
      exact congrArg Complex.re
        (bombieriFunctional_quadratic_normalizedDilation
          2 (by norm_num) g)
    _ = (bombieriLocalCriticalForm g g).re := by
      exact congrArg Complex.re
        (bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
          g ha hab hsupport hratio)

private theorem bombieriLocalCriticalForm_sub_dilation_two_re
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (bombieriLocalCriticalForm
      (g - normalizedDilation 2 (by norm_num) g)
      (g - normalizedDilation 2 (by norm_num) g)).re =
        2 * ((bombieriLocalCriticalForm g g).re -
          (bombieriLocalCriticalForm g
            (normalizedDilation 2 (by norm_num) g)).re) := by
  let d : BombieriTest := normalizedDilation 2 (by norm_num) g
  have hdd : (bombieriLocalCriticalForm d d).re =
      (bombieriLocalCriticalForm g g).re := by
    simpa only [d] using bombieriLocalCriticalForm_dilation_two_self_re_eq
      g ha hab hsupport hratio
  have hswap : (bombieriLocalCriticalForm d g).re =
      (bombieriLocalCriticalForm g d).re := by
    have h := congrArg Complex.re
      (bombieriLocalCriticalForm_conj_apply g d)
    simpa only [map_sub, Complex.star_def, Complex.conj_re] using h
  change (bombieriLocalCriticalForm (g - d) (g - d)).re = _
  simp only [map_sub, LinearMap.sub_apply, Complex.sub_re]
  rw [hdd, hswap]
  ring

private theorem bombieriLocalCriticalForm_add_dilation_two_re
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (bombieriLocalCriticalForm
      (g + normalizedDilation 2 (by norm_num) g)
      (g + normalizedDilation 2 (by norm_num) g)).re =
        2 * ((bombieriLocalCriticalForm g g).re +
          (bombieriLocalCriticalForm g
            (normalizedDilation 2 (by norm_num) g)).re) := by
  let d : BombieriTest := normalizedDilation 2 (by norm_num) g
  have hdd : (bombieriLocalCriticalForm d d).re =
      (bombieriLocalCriticalForm g g).re := by
    simpa only [d] using bombieriLocalCriticalForm_dilation_two_self_re_eq
      g ha hab hsupport hratio
  have hswap : (bombieriLocalCriticalForm d g).re =
      (bombieriLocalCriticalForm g d).re := by
    have h := congrArg Complex.re
      (bombieriLocalCriticalForm_conj_apply g d)
    simpa only [map_sub, Complex.star_def, Complex.conj_re] using h
  change (bombieriLocalCriticalForm (g + d) (g + d)).re = _
  simp only [map_add, LinearMap.add_apply, Complex.add_re]
  rw [hdd, hswap]
  ring

/-- On one ratio-two cell, the exact physical diagonal is the real local
critical self-form. -/
theorem factorTwoDiagonalCoordinate_eq_localCriticalForm
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoDiagonalCoordinate g =
      (bombieriLocalCriticalForm g g).re := by
  calc
    factorTwoDiagonalCoordinate g =
        (bombieriFunctional (bombieriQuadraticTest g)).re := by
      simpa only [factorTwoDiagonalCoordinate] using
        (bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
          g ha hab hsupport hratio).symm
    _ = _ := congrArg Complex.re
      (bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
        g ha hab hsupport hratio)

/-- On one ratio-two cell, the symmetric folded coordinate is the real local
adjacent form minus the exact two-prime cross symbol. -/
theorem factorTwoSymmetricCoordinate_eq_localPrime
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoSymmetricCoordinate g =
      (bombieriLocalCriticalForm g
          (normalizedDilation 2 (by norm_num) g)).re -
        (factorTwoPrimeCrossSymbol g).re := by
  calc
    factorTwoSymmetricCoordinate g =
        (factorTwoGlobalCrossSymbol g).re := by
      simpa only [factorTwoSymmetricCoordinate] using
        (factorTwoGlobalCrossSymbol_re_eq_parity
          g ha hab hsupport hratio).symm
    _ = _ := by
      unfold factorTwoGlobalCrossSymbol
      simp only [Complex.sub_re]

/-- The `D - R` channel is half the local critical self-form of the antisymmetric
two-cell test plus the real two-prime symbol. -/
theorem factorTwoDiagonalCoordinate_sub_symmetric_eq_localPrime
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoDiagonalCoordinate g - factorTwoSymmetricCoordinate g =
      (1 / 2 : ℝ) *
          (bombieriLocalCriticalForm
            (g - normalizedDilation 2 (by norm_num) g)
            (g - normalizedDilation 2 (by norm_num) g)).re +
        (factorTwoPrimeCrossSymbol g).re := by
  rw [factorTwoDiagonalCoordinate_eq_localCriticalForm
      g ha hab hsupport hratio,
    factorTwoSymmetricCoordinate_eq_localPrime
      g ha hab hsupport hratio,
    bombieriLocalCriticalForm_sub_dilation_two_re
      g ha hab hsupport hratio]
  ring

/-- The `D + R` channel is half the local critical self-form of the symmetric
two-cell test minus the real two-prime symbol. -/
theorem factorTwoDiagonalCoordinate_add_symmetric_eq_localPrime
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g =
      (1 / 2 : ℝ) *
          (bombieriLocalCriticalForm
            (g + normalizedDilation 2 (by norm_num) g)
            (g + normalizedDilation 2 (by norm_num) g)).re -
        (factorTwoPrimeCrossSymbol g).re := by
  rw [factorTwoDiagonalCoordinate_eq_localCriticalForm
      g ha hab hsupport hratio,
    factorTwoSymmetricCoordinate_eq_localPrime
      g ha hab hsupport hratio,
    bombieriLocalCriticalForm_add_dilation_two_re
      g ha hab hsupport hratio]
  ring

/-- Nonnegativity of the antisymmetric signed channel is exactly lower
domination of the negative prime symbol by the exact local self-form. -/
theorem factorTwoRealChannel_sub_nonneg_iff_localPrime
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    0 ≤ factorTwoDiagonalCoordinate g - factorTwoSymmetricCoordinate g ↔
      -(factorTwoPrimeCrossSymbol g).re ≤
        (1 / 2 : ℝ) *
          (bombieriLocalCriticalForm
            (g - normalizedDilation 2 (by norm_num) g)
            (g - normalizedDilation 2 (by norm_num) g)).re := by
  rw [factorTwoDiagonalCoordinate_sub_symmetric_eq_localPrime
    g ha hab hsupport hratio]
  constructor <;> intro h <;> linarith

/-- Nonnegativity of the symmetric signed channel is exactly upper domination
of the prime symbol by the exact local self-form. -/
theorem factorTwoRealChannel_add_nonneg_iff_localPrime
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    0 ≤ factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g ↔
      (factorTwoPrimeCrossSymbol g).re ≤
        (1 / 2 : ℝ) *
          (bombieriLocalCriticalForm
            (g + normalizedDilation 2 (by norm_num) g)
            (g + normalizedDilation 2 (by norm_num) g)).re := by
  rw [factorTwoDiagonalCoordinate_add_symmetric_eq_localPrime
    g ha hab hsupport hratio]
  constructor <;> intro h <;> linarith

/-- Strict failure of the antisymmetric local-form/prime domination is
exactly a negative production functional for the explicit scalar `c = -1`. -/
theorem bombieriFunctional_twoBump_neg_one_neg_iff_localPrime
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (bombieriFunctional
      (bombieriQuadraticTest
        (g + (-1 : ℂ) • normalizedDilation 2 (by norm_num) g))).re < 0 ↔
      (1 / 2 : ℝ) *
          (bombieriLocalCriticalForm
            (g - normalizedDilation 2 (by norm_num) g)
            (g - normalizedDilation 2 (by norm_num) g)).re <
        -(factorTwoPrimeCrossSymbol g).re := by
  have hformula := bombieriFunctional_twoBump_re
    g (-1 : ℂ) ha hab hsupport hratio
  have hD :=
    bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
      g ha hab hsupport hratio
  have hR := factorTwoGlobalCrossSymbol_re_eq_parity
    g ha hab hsupport hratio
  change (bombieriFunctional (bombieriQuadraticTest g)).re =
    factorTwoDiagonalCoordinate g at hD
  change (factorTwoGlobalCrossSymbol g).re =
    factorTwoSymmetricCoordinate g at hR
  have htwo :
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + (-1 : ℂ) • normalizedDilation 2 (by norm_num) g))).re =
        2 * (factorTwoDiagonalCoordinate g -
          factorTwoSymmetricCoordinate g) := by
    rw [hformula, hD]
    simp only [Complex.normSq_neg, Complex.normSq_one, neg_one_mul,
      Complex.neg_re]
    rw [hR]
    ring
  rw [htwo,
    factorTwoDiagonalCoordinate_sub_symmetric_eq_localPrime
      g ha hab hsupport hratio]
  constructor <;> intro h <;> linarith

/-- Strict failure of the symmetric local-form/prime domination is exactly
a negative production functional for the explicit scalar `c = 1`. -/
theorem bombieriFunctional_twoBump_one_neg_iff_localPrime
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (bombieriFunctional
      (bombieriQuadraticTest
        (g + (1 : ℂ) • normalizedDilation 2 (by norm_num) g))).re < 0 ↔
      (1 / 2 : ℝ) *
          (bombieriLocalCriticalForm
            (g + normalizedDilation 2 (by norm_num) g)
            (g + normalizedDilation 2 (by norm_num) g)).re <
        (factorTwoPrimeCrossSymbol g).re := by
  have hformula := bombieriFunctional_twoBump_re
    g (1 : ℂ) ha hab hsupport hratio
  have hD :=
    bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
      g ha hab hsupport hratio
  have hR := factorTwoGlobalCrossSymbol_re_eq_parity
    g ha hab hsupport hratio
  change (bombieriFunctional (bombieriQuadraticTest g)).re =
    factorTwoDiagonalCoordinate g at hD
  change (factorTwoGlobalCrossSymbol g).re =
    factorTwoSymmetricCoordinate g at hR
  have htwo :
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + (1 : ℂ) • normalizedDilation 2 (by norm_num) g))).re =
        2 * (factorTwoDiagonalCoordinate g +
          factorTwoSymmetricCoordinate g) := by
    rw [hformula, hD]
    simp only [Complex.normSq_one, one_mul]
    rw [hR]
    ring
  rw [htwo,
    factorTwoDiagonalCoordinate_add_symmetric_eq_localPrime
      g ha hab hsupport hratio]
  constructor <;> intro h <;> linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeDomination
