import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorCertificateStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhLoewnerStructural

set_option autoImplicit false

open Matrix Polynomial Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhCertificateStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorCertificateStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhLoewnerStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailResidualStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6SelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectPSevenEndpointSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural

/-!
# Direct atanh endpoint certificates for the exact `P6` rows

The direct two-term atanh reciprocal Gram preserves the exact retained mass
and potential slope.  This file makes its two endpoint positive-definiteness
statements the only new hypotheses, then transfers them through the exact
selector certificate and the degree-seven endpoint coefficient API.
-/

/-- Loewner gap formed with the direct two-term atanh upper selector Gram. -/
def factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  factorTwoIntrinsicNineDirectP6ExactTailComplement sigma •
      factorTwoIntrinsicNineDirectP024ExactLowMatrix sigma -
    factorTwoIntrinsicNineDirectP6WeightedMass •
      factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperSelectorGram
        sigma q

/-- The exact selector gap is the direct-atanh gap plus the positive Loewner
correction between the direct upper Gram and the exact selector Gram. -/
theorem factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap_eq_directAtanh_add
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap sigma q =
      factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap sigma q +
        factorTwoIntrinsicNineDirectP6WeightedMass •
          (factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperSelectorGram
              sigma q -
            factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram sigma q) := by
  unfold factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap
    factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap
  module

/-- Positive definiteness of the direct-atanh upper gap transfers to the
exact selector gap by full-matrix Loewner monotonicity. -/
theorem factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap_posDef_of_directAtanh
    (sigma : ℝ) (q : Fin 3 → ℝ[X])
    (hUpper :
      (factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap
        sigma q).PosDef) :
    (factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap sigma q).PosDef := by
  rw [factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap_eq_directAtanh_add]
  exact hUpper.add_posSemidef
    ((factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperSelectorGram_sub_posSemidef
      sigma q).smul factorTwoIntrinsicNineDirectP6WeightedMass_pos.le)

/-- Direct-atanh positive-endpoint certificate. -/
def FactorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorPlusCertificate : Prop :=
  (factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap 1
    factorTwoIntrinsicNineDirectP6ExactSelectorPlus).PosDef

/-- Direct-atanh negative-endpoint certificate. -/
def FactorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorMinusCertificate : Prop :=
  (factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap (-1)
    factorTwoIntrinsicNineDirectP6ExactSelectorMinus).PosDef

/-- The positive direct-atanh certificate implies the existing exact
positive-endpoint certificate. -/
theorem factorTwoIntrinsicNineDirectP6ExactSelectorPlusCertificate_of_directAtanhUpper
    (h : FactorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorPlusCertificate) :
    FactorTwoIntrinsicNineDirectP6ExactSelectorPlusCertificate := by
  exact factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap_posDef_of_directAtanh
    1 factorTwoIntrinsicNineDirectP6ExactSelectorPlus h

/-- The negative direct-atanh certificate implies the existing exact
negative-endpoint certificate. -/
theorem factorTwoIntrinsicNineDirectP6ExactSelectorMinusCertificate_of_directAtanhUpper
    (h : FactorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorMinusCertificate) :
    FactorTwoIntrinsicNineDirectP6ExactSelectorMinusCertificate := by
  exact factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap_posDef_of_directAtanh
    (-1) factorTwoIntrinsicNineDirectP6ExactSelectorMinus h

/-- The two direct-atanh endpoint certificates close both endpoint
coefficients of the degree-seven prefix determinant polynomial. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_endpoint_coefficients_pos_of_directAtanhUpperCertificates
    (hPlus :
      FactorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorPlusCertificate)
    (hMinus :
      FactorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorMinusCertificate) :
    0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 0 ∧
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 7 :=
  factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_endpoint_coefficients_pos_of_exactSelectorCertificates
    (factorTwoIntrinsicNineDirectP6ExactSelectorPlusCertificate_of_directAtanhUpper
      hPlus)
    (factorTwoIntrinsicNineDirectP6ExactSelectorMinusCertificate_of_directAtanhUpper
      hMinus)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhCertificateStructural
