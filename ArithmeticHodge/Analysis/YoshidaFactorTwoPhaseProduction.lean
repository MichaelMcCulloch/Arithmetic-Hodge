import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointChannelRadius
import ArithmeticHodge.Analysis.MultiplicativeWeilLiCriterionClosure

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProduction

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilRestrictedSupportEndpointPositive
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoDiagonalPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoParityRealification

/-!
# Production realization of the endpoint phase form

The complete closed-disk phase form is the normalized production quadratic
of the adjacent two-cell test plus its nonnegative radial gap.  On the unit
circle the gap vanishes, exposing exactly why the ratio-two positivity theorem
does not settle the factor-two problem.
-/

/-- Exact production representation of the complete endpoint phase form.
The last summand is the radial gap; on the unit circle it vanishes. -/
theorem endpointPhaseForm_eq_twoBump_add_radialGap
    (g : BombieriTest) {l r a b : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    let u := factorTwoCenteredProfile (bombieriRealPartTest g)
    let v := factorTwoCenteredProfile (bombieriImagPartTest g)
    factorTwoEndpointChannelCleanSum u v +
          a * factorTwoEndpointChannelSymmetricSum u v +
          b * factorTwoCenteredAlternatingCoupling u v =
      (bombieriFunctional
          (bombieriQuadraticTest
            (g + (⟨a, -b⟩ : ℂ) •
              normalizedDilation 2 (by norm_num) g))).re /
          (2 * yoshidaEndpointA) +
        ((1 - (a ^ 2 + b ^ 2)) / 2) *
          factorTwoEndpointChannelCleanSum u v := by
  let u := factorTwoCenteredProfile (bombieriRealPartTest g)
  let v := factorTwoCenteredProfile (bombieriImagPartTest g)
  let c : ℂ := ⟨a, -b⟩
  have hfunctional :
      (bombieriFunctional (bombieriQuadraticTest g)).re =
        factorTwoDiagonalCoordinate g := by
    simpa only [factorTwoDiagonalCoordinate] using
      bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
        g hl hlr hsupport hratio
  have hD := factorTwoDiagonalCoordinate_eq_endpoint_mul_channelCleanSum
    g hl hlr hsupport hratio hcritical
  have hZ := factorTwoGlobalCrossSymbol_eq_endpoint_mul_channelCoordinate
    g hl hlr hsupport hratio hcritical
  have hF := bombieriFunctional_twoBump_re
    g c hl hlr hsupport hratio
  dsimp only [u, v]
  rw [hF, hfunctional, hD, hZ]
  simp only [c, factorTwoEndpointChannelCoordinate,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero]
  field_simp [yoshidaEndpointA_pos.ne']
  ring

/-- The same identity with the unconditional local-form/prime decomposition
exposed.  This is the exact point at which the ratio-four support and the
mixed prime correction enter. -/
theorem endpointPhaseForm_eq_localSquare_sub_prime_add_radialGap
    (g : BombieriTest) {l r a b : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    let u := factorTwoCenteredProfile (bombieriRealPartTest g)
    let v := factorTwoCenteredProfile (bombieriImagPartTest g)
    let h := g + (⟨a, -b⟩ : ℂ) •
      normalizedDilation 2 (by norm_num) g
    factorTwoEndpointChannelCleanSum u v +
          a * factorTwoEndpointChannelSymmetricSum u v +
          b * factorTwoCenteredAlternatingCoupling u v =
      ((bombieriLocalCriticalForm h h).re -
          (primeSum (bombieriQuadraticTest h)).re) /
          (2 * yoshidaEndpointA) +
        ((1 - (a ^ 2 + b ^ 2)) / 2) *
          factorTwoEndpointChannelCleanSum u v := by
  dsimp only
  rw [endpointPhaseForm_eq_twoBump_add_radialGap
    g hl hlr hsupport hratio hcritical,
    bombieriFunctional_quadratic_eq_localCritical_sub_prime]
  simp only [Complex.sub_re]

/-- At unit phase, the endpoint phase form is exactly the normalized
production quadratic of the adjacent two-cell test. -/
theorem endpointPhaseForm_eq_twoBump_of_unit
    (g : BombieriTest) {l r a b : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g)
    (hunit : a ^ 2 + b ^ 2 = 1) :
    let u := factorTwoCenteredProfile (bombieriRealPartTest g)
    let v := factorTwoCenteredProfile (bombieriImagPartTest g)
    factorTwoEndpointChannelCleanSum u v +
          a * factorTwoEndpointChannelSymmetricSum u v +
          b * factorTwoCenteredAlternatingCoupling u v =
      (bombieriFunctional
          (bombieriQuadraticTest
            (g + (⟨a, -b⟩ : ℂ) •
              normalizedDilation 2 (by norm_num) g))).re /
          (2 * yoshidaEndpointA) := by
  dsimp only
  rw [endpointPhaseForm_eq_twoBump_add_radialGap
    g hl hlr hsupport hratio hcritical, hunit]
  ring

/-- The center in the phase identity is already nonnegative by the proved
ratio-two theorem. -/
theorem canonicalEndpointChannelCleanSum_nonneg
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    0 ≤ factorTwoEndpointChannelCleanSum
      (factorTwoCenteredProfile (bombieriRealPartTest g))
      (factorTwoCenteredProfile (bombieriImagPartTest g)) := by
  have hglobal := bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two
    g hl hlr hsupport hratio
  have hfunctional :
      (bombieriFunctional (bombieriQuadraticTest g)).re =
        factorTwoDiagonalCoordinate g := by
    simpa only [factorTwoDiagonalCoordinate] using
      bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
        g hl hlr hsupport hratio
  have hD := factorTwoDiagonalCoordinate_eq_endpoint_mul_channelCleanSum
    g hl hlr hsupport hratio hcritical
  rw [hfunctional, hD] at hglobal
  exact nonneg_of_mul_nonneg_left
    (by simpa only [mul_comm] using hglobal) yoshidaEndpointA_pos

/-- For the canonical ratio-two seed, phase-uniform positivity is exactly the
single sharp channel-radius inequality: the center sign is already known. -/
theorem canonicalEndpointPhase_nonneg_iff_radius
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    let u := factorTwoCenteredProfile (bombieriRealPartTest g)
    let v := factorTwoCenteredProfile (bombieriImagPartTest g)
    (∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ 1 →
      0 ≤ factorTwoEndpointChannelCleanSum u v +
        a * factorTwoEndpointChannelSymmetricSum u v +
        b * factorTwoCenteredAlternatingCoupling u v) ↔
      Complex.normSq (factorTwoEndpointChannelCoordinate u v) ≤
        factorTwoEndpointChannelCleanSum u v ^ 2 := by
  dsimp only
  rw [factorTwoEndpointChannel_phase_nonneg_iff_radius]
  exact and_iff_right
    (canonicalEndpointChannelCleanSum_nonneg
      g hl hlr hsupport hratio hcritical)

/-- Dually, a strict negative phase for the canonical ratio-two seed is
exactly a strict reversal of its complete channel radius. -/
theorem canonicalEndpointPhase_exists_neg_iff_radius
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    let u := factorTwoCenteredProfile (bombieriRealPartTest g)
    let v := factorTwoCenteredProfile (bombieriImagPartTest g)
    (∃ a b : ℝ, a ^ 2 + b ^ 2 ≤ 1 ∧
      factorTwoEndpointChannelCleanSum u v +
          a * factorTwoEndpointChannelSymmetricSum u v +
          b * factorTwoCenteredAlternatingCoupling u v < 0) ↔
      factorTwoEndpointChannelCleanSum u v ^ 2 <
        Complex.normSq (factorTwoEndpointChannelCoordinate u v) := by
  dsimp only
  rw [factorTwoEndpointChannel_phase_exists_neg_iff_radius]
  have hQ := canonicalEndpointChannelCleanSum_nonneg
    g hl hlr hsupport hratio hcritical
  exact or_iff_right (not_lt_of_ge hQ)

/-- The strict reverse, if present, already has a unit-phase endpoint witness.
This is the boundary on which the exact production radial gap is zero. -/
theorem canonicalEndpointUnitPhase_exists_neg_iff_radius
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    let u := factorTwoCenteredProfile (bombieriRealPartTest g)
    let v := factorTwoCenteredProfile (bombieriImagPartTest g)
    (∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧
      factorTwoEndpointChannelCleanSum u v +
          a * factorTwoEndpointChannelSymmetricSum u v +
          b * factorTwoCenteredAlternatingCoupling u v < 0) ↔
      factorTwoEndpointChannelCleanSum u v ^ 2 <
        Complex.normSq (factorTwoEndpointChannelCoordinate u v) := by
  dsimp only
  rw [factorTwoEndpointChannel_unitPhase_exists_neg_iff_radius]
  have hQ := canonicalEndpointChannelCleanSum_nonneg
    g hl hlr hsupport hratio hcritical
  exact or_iff_right (not_lt_of_ge hQ)

/-- A strict reverse of the canonical endpoint radius is exactly a negative
Bombieri production test in the same-seed adjacent two-cell family. -/
theorem twoBump_exists_negative_iff_endpointRadius_reverse
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    let u := factorTwoCenteredProfile (bombieriRealPartTest g)
    let v := factorTwoCenteredProfile (bombieriImagPartTest g)
    (∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + (⟨a, -b⟩ : ℂ) •
            normalizedDilation 2 (by norm_num) g))).re < 0) ↔
      factorTwoEndpointChannelCleanSum u v ^ 2 <
        Complex.normSq (factorTwoEndpointChannelCoordinate u v) := by
  dsimp only
  have hRadius := canonicalEndpointUnitPhase_exists_neg_iff_radius
    g hl hlr hsupport hratio hcritical
  dsimp only at hRadius
  rw [← hRadius]
  constructor
  · rintro ⟨a, b, hunit, hnegative⟩
    refine ⟨a, b, hunit, ?_⟩
    rw [endpointPhaseForm_eq_twoBump_of_unit
      g hl hlr hsupport hratio hcritical hunit]
    exact div_neg_of_neg_of_pos hnegative
      (mul_pos (by norm_num) yoshidaEndpointA_pos)
  · rintro ⟨a, b, hunit, hnegative⟩
    refine ⟨a, b, hunit, ?_⟩
    rw [endpointPhaseForm_eq_twoBump_of_unit
      g hl hlr hsupport hratio hcritical hunit] at hnegative
    exact neg_of_div_neg_left hnegative
      (mul_nonneg (by norm_num) yoshidaEndpointA_pos.le)

/-- Any strict reverse of the canonical endpoint radius is already a formal
falsification of RH, because its unit-phase witness is a concrete negative
Bombieri quadratic test. -/
theorem not_riemannHypothesis_of_endpointRadius_reverse
    (zeros : ZetaZeroEnumeration)
    (g : BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g)
    (hradius :
      factorTwoEndpointChannelCleanSum
            (factorTwoCenteredProfile (bombieriRealPartTest g))
            (factorTwoCenteredProfile (bombieriImagPartTest g)) ^ 2 <
        Complex.normSq
          (factorTwoEndpointChannelCoordinate
            (factorTwoCenteredProfile (bombieriRealPartTest g))
            (factorTwoCenteredProfile (bombieriImagPartTest g)))) :
    ¬ RiemannHypothesis := by
  obtain ⟨a, b, _hunit, hnegative⟩ :=
    (twoBump_exists_negative_iff_endpointRadius_reverse
      g hl hlr hsupport hratio hcritical).2 hradius
  intro hRH
  have hnonnegative :=
    (rh_implies_bombieriFunctional_quadratic_nonneg
      zeros (bombieriZeroSumFormula zeros) hRH
      (g + (⟨a, -b⟩ : ℂ) •
        normalizedDilation 2 (by norm_num) g)).2
  exact (not_lt_of_ge hnonnegative) hnegative

/-- Consequently the disk phase problem has only one new input: positivity
of the adjacent two-cell production quadratic. -/
theorem endpointPhaseForm_nonneg_of_twoBump_nonneg
    (g : BombieriTest) {l r a b : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g)
    (hdisk : a ^ 2 + b ^ 2 ≤ 1)
    (htwo : 0 ≤ (bombieriFunctional
      (bombieriQuadraticTest
        (g + (⟨a, -b⟩ : ℂ) •
          normalizedDilation 2 (by norm_num) g))).re) :
    let u := factorTwoCenteredProfile (bombieriRealPartTest g)
    let v := factorTwoCenteredProfile (bombieriImagPartTest g)
    0 ≤ factorTwoEndpointChannelCleanSum u v +
      a * factorTwoEndpointChannelSymmetricSum u v +
      b * factorTwoCenteredAlternatingCoupling u v := by
  dsimp only
  rw [endpointPhaseForm_eq_twoBump_add_radialGap
    g hl hlr hsupport hratio hcritical]
  apply add_nonneg
  · exact div_nonneg htwo
      (mul_nonneg (by norm_num) yoshidaEndpointA_pos.le)
  · exact mul_nonneg (div_nonneg (by linarith) (by norm_num))
      (canonicalEndpointChannelCleanSum_nonneg
        g hl hlr hsupport hratio hcritical)

/-- The support estimate available for the production test is ratio four,
not ratio two. -/
theorem twoBump_tsupport_subset_ratio_four
    (g : BombieriTest) (c : ℂ) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2) :
    tsupport (g + c • normalizedDilation 2 (by norm_num) g : ℝ → ℂ) ⊆
        Set.Icc (l / 2) r ∧
      r / (l / 2) ≤ 4 := by
  let d : BombieriTest := normalizedDilation 2 (by norm_num) g
  have hd : tsupport (d : ℝ → ℂ) ⊆ Set.Icc (l / 2) (r / 2) := by
    simpa only [d] using normalizedDilation_tsupport_subset_Icc
      2 (by norm_num) g hsupport
  constructor
  · have hgWide : tsupport (g : ℝ → ℂ) ⊆ Set.Icc (l / 2) r := by
      intro x hx
      have hx' := hsupport hx
      constructor
      · exact (half_le_self hl.le).trans hx'.1
      · exact hx'.2
    have hdWide : tsupport (d : ℝ → ℂ) ⊆ Set.Icc (l / 2) r := by
      intro x hx
      have hx' := hd hx
      constructor
      · exact hx'.1
      · exact hx'.2.trans (half_le_self (hl.le.trans hlr))
    change tsupport (fun x : ℝ ↦ g x + c * d x) ⊆ Set.Icc (l / 2) r
    exact (tsupport_add (g : ℝ → ℂ) (fun x ↦ c * d x)).trans
      (union_subset hgWide
        ((tsupport_smul_subset_right (fun _ : ℝ ↦ c) (d : ℝ → ℂ)).trans
          hdWide))
  · have hl0 : l ≠ 0 := hl.ne'
    rw [show r / (l / 2) = 2 * (r / l) by field_simp [hl0]]
    linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProduction
