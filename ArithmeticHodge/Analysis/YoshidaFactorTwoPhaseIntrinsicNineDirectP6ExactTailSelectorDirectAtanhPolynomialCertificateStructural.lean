import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhCertificateStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhPolynomialLoewnerStructural

set_option autoImplicit false

open Matrix Polynomial Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhPolynomialCertificateStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailResidualStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorCertificateStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhCertificateStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhLoewnerStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhPolynomialLoewnerStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6SelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural

/-!
# Polynomial direct-atanh endpoint certificates

The degree-twelve reciprocal polynomial makes the direct-atanh selector Gram
enclosure-ready.  Its two concrete endpoint positive-definiteness statements
transfer first to the sharper direct-atanh gaps, then to the exact selector
gaps and the endpoint coefficients of the degree-seven determinant.
-/

/-- Loewner gap formed with the polynomial-majorant upper selector Gram. -/
def factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  factorTwoIntrinsicNineDirectP6ExactTailComplement sigma •
      factorTwoIntrinsicNineDirectP024ExactLowMatrix sigma -
    factorTwoIntrinsicNineDirectP6WeightedMass •
      factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram
        sigma q

/-- The direct-atanh gap is the polynomial gap plus the positive correction
between the polynomial and direct reciprocal selector Grams. -/
theorem factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap_eq_polynomialMajorant_add
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap sigma q =
      factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap
          sigma q +
        factorTwoIntrinsicNineDirectP6WeightedMass •
          (factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram
              sigma q -
            factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperSelectorGram
              sigma q) := by
  unfold factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap
    factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap
  module

/-- The exact selector gap is also the polynomial gap plus the full
polynomial-to-exact Loewner correction. -/
theorem factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap_eq_polynomialMajorant_add
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap sigma q =
      factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap
          sigma q +
        factorTwoIntrinsicNineDirectP6WeightedMass •
          (factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram
              sigma q -
            factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram sigma q) := by
  unfold factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap
    factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap
  module

/-- Positive definiteness of the polynomial gap transfers to the sharper
direct-atanh gap. -/
theorem factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap_posDef_of_polynomialMajorant
    (sigma : ℝ) (q : Fin 3 → ℝ[X])
    (hPolynomial :
      (factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap
        sigma q).PosDef) :
    (factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap
      sigma q).PosDef := by
  rw [factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap_eq_polynomialMajorant_add]
  exact hPolynomial.add_posSemidef
    ((factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram_sub_directAtanh_posSemidef
      sigma q).smul factorTwoIntrinsicNineDirectP6WeightedMass_pos.le)

/-- The same polynomial certificate transfers all the way to the exact
selector gap through the direct-atanh gap. -/
theorem factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap_posDef_of_polynomialMajorant
    (sigma : ℝ) (q : Fin 3 → ℝ[X])
    (hPolynomial :
      (factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap
        sigma q).PosDef) :
    (factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap sigma q).PosDef :=
  factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap_posDef_of_directAtanh
    sigma q
    (factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap_posDef_of_polynomialMajorant
      sigma q hPolynomial)

/-- Polynomial-majorant positive-endpoint certificate. -/
def FactorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorPlusCertificate :
    Prop :=
  (factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap 1
    factorTwoIntrinsicNineDirectP6ExactSelectorPlus).PosDef

/-- Polynomial-majorant negative-endpoint certificate. -/
def FactorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorMinusCertificate :
    Prop :=
  (factorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorLoewnerGap (-1)
    factorTwoIntrinsicNineDirectP6ExactSelectorMinus).PosDef

/-- The positive polynomial certificate implies the sharper direct-atanh
positive endpoint certificate. -/
theorem factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorPlusCertificate_of_polynomialMajorant
    (h :
      FactorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorPlusCertificate) :
    FactorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorPlusCertificate := by
  exact
    factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap_posDef_of_polynomialMajorant
      1 factorTwoIntrinsicNineDirectP6ExactSelectorPlus h

/-- The negative polynomial certificate implies the sharper direct-atanh
negative endpoint certificate. -/
theorem factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorMinusCertificate_of_polynomialMajorant
    (h :
      FactorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorMinusCertificate) :
    FactorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorMinusCertificate := by
  exact
    factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorLoewnerGap_posDef_of_polynomialMajorant
      (-1) factorTwoIntrinsicNineDirectP6ExactSelectorMinus h

/-- The positive polynomial certificate also implies the existing exact
positive endpoint certificate. -/
theorem factorTwoIntrinsicNineDirectP6ExactSelectorPlusCertificate_of_polynomialMajorant
    (h :
      FactorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorPlusCertificate) :
    FactorTwoIntrinsicNineDirectP6ExactSelectorPlusCertificate :=
  factorTwoIntrinsicNineDirectP6ExactSelectorPlusCertificate_of_directAtanhUpper
    (factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorPlusCertificate_of_polynomialMajorant
      h)

/-- The negative polynomial certificate also implies the existing exact
negative endpoint certificate. -/
theorem factorTwoIntrinsicNineDirectP6ExactSelectorMinusCertificate_of_polynomialMajorant
    (h :
      FactorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorMinusCertificate) :
    FactorTwoIntrinsicNineDirectP6ExactSelectorMinusCertificate :=
  factorTwoIntrinsicNineDirectP6ExactSelectorMinusCertificate_of_directAtanhUpper
    (factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorMinusCertificate_of_polynomialMajorant
      h)

/-- The two polynomial endpoint certificates close both endpoint
coefficients of the degree-seven prefix determinant polynomial. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_endpoint_coefficients_pos_of_polynomialMajorantCertificates
    (hPlus :
      FactorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorPlusCertificate)
    (hMinus :
      FactorTwoIntrinsicNineDirectP6PolynomialMajorantUpperSelectorMinusCertificate) :
    0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 0 ∧
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 7 :=
  factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_endpoint_coefficients_pos_of_directAtanhUpperCertificates
    (factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorPlusCertificate_of_polynomialMajorant
      hPlus)
    (factorTwoIntrinsicNineDirectP6DirectAtanhUpperSelectorMinusCertificate_of_polynomialMajorant
      hMinus)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhPolynomialCertificateStructural
