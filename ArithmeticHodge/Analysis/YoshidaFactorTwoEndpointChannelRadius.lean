import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointParityPencil

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointChannelRadius

noncomputable section

open YoshidaEndpointOddCleanPositive
open YoshidaEndpointHyperbolicBound
open MultiplicativeWeil
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoDiagonalPhysical
open YoshidaFactorTwoParityRealification
open YoshidaFactorTwoPrimeDomination

/-!
# Numerical radius of the factor-two reflection channels

Each opposite-reflection-parity block has one clean diagonal `Q`, one complete
symmetric perturbation `P`, and one alternating coupling `J`.  This file keeps
`P` and `J` together as the real and imaginary parts of a single complex
coordinate.  Nonnegativity of the whole scalar channel is then exactly the
sharp numerical-radius inequality `P ^ 2 + J ^ 2 ≤ Q ^ 2`.
-/

/-! ## Scalar algebra -/

/-- A rotated real quadratic pencil is nonnegative in every direction exactly
when its center is nonnegative and its two-coordinate radius fits inside the
center. -/
theorem real_rotated_quadratic_pencil_nonneg_iff (Q P J : ℝ) :
    (∀ r s : ℝ,
      0 ≤ (Q + P) * r ^ 2 + 2 * J * r * s + (Q - P) * s ^ 2) ↔
      0 ≤ Q ∧ P ^ 2 + J ^ 2 ≤ Q ^ 2 := by
  rw [real_quadratic_pencil_nonneg_iff]
  constructor
  · rintro ⟨hplus, hminus, hdet⟩
    constructor
    · linarith
    · nlinarith
  · rintro ⟨hQ, hradius⟩
    have hP2 : P ^ 2 ≤ Q ^ 2 := by
      nlinarith [sq_nonneg J]
    have hPabs : |P| ≤ Q := by
      apply (sq_le_sq₀ (abs_nonneg P) hQ).1
      simpa only [sq_abs] using hP2
    constructor
    · linarith [neg_abs_le P]
    constructor
    · linarith [le_abs_self P]
    · nlinarith

/-- Strict failure of the rotated pencil is exactly failure of its center or
of its two-coordinate radius bound. -/
theorem real_rotated_quadratic_pencil_exists_neg_iff (Q P J : ℝ) :
    (∃ r s : ℝ,
      (Q + P) * r ^ 2 + 2 * J * r * s + (Q - P) * s ^ 2 < 0) ↔
      Q < 0 ∨ Q ^ 2 < P ^ 2 + J ^ 2 := by
  have hcriterion := real_rotated_quadratic_pencil_nonneg_iff Q P J
  constructor
  · rintro ⟨r, s, hneg⟩
    have hnot : ¬ ∀ r s : ℝ,
        0 ≤ (Q + P) * r ^ 2 + 2 * J * r * s + (Q - P) * s ^ 2 := by
      intro hnonneg
      exact (not_lt_of_ge (hnonneg r s)) hneg
    rw [hcriterion] at hnot
    push_neg at hnot
    by_cases hQ : 0 ≤ Q
    · exact Or.inr (hnot hQ)
    · exact Or.inl (lt_of_not_ge hQ)
  · intro hfailure
    by_contra hnot
    push_neg at hnot
    have hradius := hcriterion.mp hnot
    rcases hfailure with hQ | hradius'
    · exact (not_lt_of_ge hradius.1) hQ
    · exact (not_lt_of_ge hradius.2) hradius'

/-! ## The complete endpoint channel -/

/-- The clean diagonal shared by a pair of centered real profiles. -/
def factorTwoEndpointChannelCleanSum (u v : ℝ → ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic u +
    yoshidaEndpointOddCleanQuadratic v

/-- The complete symmetric perturbation of a centered real profile pair. -/
def factorTwoEndpointChannelSymmetricSum (u v : ℝ → ℝ) : ℝ :=
  factorTwoCenteredSymmetricPerturbation u +
    factorTwoCenteredSymmetricPerturbation v

/-- The complete complex coordinate of a centered endpoint channel.  Its real
part is the sum of the two symmetric perturbations and its imaginary part is
the alternating cross coupling. -/
def factorTwoEndpointChannelCoordinate (u v : ℝ → ℝ) : ℂ :=
  ⟨factorTwoEndpointChannelSymmetricSum u v,
    factorTwoCenteredAlternatingCoupling u v⟩

@[simp] theorem factorTwoEndpointChannelCoordinate_normSq
    (u v : ℝ → ℝ) :
    Complex.normSq (factorTwoEndpointChannelCoordinate u v) =
      factorTwoEndpointChannelSymmetricSum u v ^ 2 +
        factorTwoCenteredAlternatingCoupling u v ^ 2 := by
  simp only [factorTwoEndpointChannelCoordinate,
    Complex.normSq_apply]
  ring

/-- The scalar pencil attached to one complete endpoint channel. -/
def factorTwoEndpointChannelPencil
    (u v : ℝ → ℝ) (r s : ℝ) : ℝ :=
  (factorTwoEndpointChannelCleanSum u v +
      factorTwoEndpointChannelSymmetricSum u v) * r ^ 2 +
    2 * factorTwoCenteredAlternatingCoupling u v * r * s +
    (factorTwoEndpointChannelCleanSum u v -
      factorTwoEndpointChannelSymmetricSum u v) * s ^ 2

/-- Exact numerical-radius criterion for one complete endpoint channel. -/
theorem factorTwoEndpointChannelPencil_nonneg_iff_radius
    (u v : ℝ → ℝ) :
    (∀ r s : ℝ,
      0 ≤ factorTwoEndpointChannelPencil u v r s) ↔
      0 ≤ factorTwoEndpointChannelCleanSum u v ∧
        Complex.normSq (factorTwoEndpointChannelCoordinate u v) ≤
          factorTwoEndpointChannelCleanSum u v ^ 2 := by
  rw [factorTwoEndpointChannelCoordinate_normSq]
  exact real_rotated_quadratic_pencil_nonneg_iff
    (factorTwoEndpointChannelCleanSum u v)
    (factorTwoEndpointChannelSymmetricSum u v)
    (factorTwoCenteredAlternatingCoupling u v)

/-- Exact strict-reverse criterion for one complete endpoint channel. -/
theorem factorTwoEndpointChannelPencil_exists_neg_iff_radius
    (u v : ℝ → ℝ) :
    (∃ r s : ℝ,
      factorTwoEndpointChannelPencil u v r s < 0) ↔
      factorTwoEndpointChannelCleanSum u v < 0 ∨
        factorTwoEndpointChannelCleanSum u v ^ 2 <
          Complex.normSq (factorTwoEndpointChannelCoordinate u v) := by
  rw [factorTwoEndpointChannelCoordinate_normSq]
  exact real_rotated_quadratic_pencil_exists_neg_iff
    (factorTwoEndpointChannelCleanSum u v)
    (factorTwoEndpointChannelSymmetricSum u v)
    (factorTwoCenteredAlternatingCoupling u v)

/-! ## Exact production coordinates -/

/-- On a ratio-two cell centered at the critical endpoint, the production
diagonal is exactly the endpoint scale times the clean center of the canonical
real/imaginary channel. -/
theorem factorTwoDiagonalCoordinate_eq_endpoint_mul_channelCleanSum
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    factorTwoDiagonalCoordinate g =
      yoshidaEndpointA * factorTwoEndpointChannelCleanSum
        (factorTwoCenteredProfile (bombieriRealPartTest g))
        (factorTwoCenteredProfile (bombieriImagPartTest g)) := by
  let gu := bombieriRealPartTest g
  let gv := bombieriImagPartTest g
  have huSupport : tsupport (gu : ℝ → ℂ) ⊆ Set.Icc a b := by
    exact (bombieriRealPartTest_tsupport_subset g).trans hsupport
  have hvSupport : tsupport (gv : ℝ → ℂ) ⊆ Set.Icc a b := by
    exact (bombieriImagPartTest_tsupport_subset g).trans hsupport
  have huCritical :
      YoshidaCriticalPullbackSupported yoshidaEndpointA gu :=
    bombieriRealPartTest_criticalPullbackSupported g hcritical
  have hvCritical :
      YoshidaCriticalPullbackSupported yoshidaEndpointA gv :=
    bombieriImagPartTest_criticalPullbackSupported g hcritical
  have huReal : ∀ x : ℝ,
      (gu.logarithmicPullbackSchwartz (1 / 2) x).im = 0 :=
    bombieriRealPartTest_criticalPullback_im_eq_zero g
  have hvReal : ∀ x : ℝ,
      (gv.logarithmicPullbackSchwartz (1 / 2) x).im = 0 :=
    bombieriImagPartTest_criticalPullback_im_eq_zero g
  calc
    factorTwoDiagonalCoordinate g =
        factorTwoDiagonalCoordinate gu + factorTwoDiagonalCoordinate gv :=
      factorTwoDiagonalCoordinate_eq_realImag g
    _ = (bombieriLocalCriticalForm gu gu).re +
        (bombieriLocalCriticalForm gv gv).re := by
      rw [factorTwoDiagonalCoordinate_eq_localCriticalForm
          gu ha hab huSupport hratio,
        factorTwoDiagonalCoordinate_eq_localCriticalForm
          gv ha hab hvSupport hratio]
    _ = yoshidaEndpointA * yoshidaEndpointOddCleanQuadratic
          (factorTwoCenteredProfile gu) +
        yoshidaEndpointA * yoshidaEndpointOddCleanQuadratic
          (factorTwoCenteredProfile gv) := by
      rw [bombieriLocalCriticalForm_re_eq_endpoint_mul_clean
          gu huCritical huReal,
        bombieriLocalCriticalForm_re_eq_endpoint_mul_clean
          gv hvCritical hvReal]
    _ = yoshidaEndpointA * factorTwoEndpointChannelCleanSum
        (factorTwoCenteredProfile (bombieriRealPartTest g))
        (factorTwoCenteredProfile (bombieriImagPartTest g)) := by
      dsimp only [gu, gv]
      unfold factorTwoEndpointChannelCleanSum
      ring

/-- On a ratio-two cell centered at the critical endpoint, the production
global cross symbol is exactly the endpoint scale times the complete complex
channel coordinate of the canonical real/imaginary profiles. -/
theorem factorTwoGlobalCrossSymbol_eq_endpoint_mul_channelCoordinate
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    factorTwoGlobalCrossSymbol g =
      (yoshidaEndpointA : ℂ) *
        factorTwoEndpointChannelCoordinate
          (factorTwoCenteredProfile (bombieriRealPartTest g))
          (factorTwoCenteredProfile (bombieriImagPartTest g)) := by
  let gu := bombieriRealPartTest g
  let gv := bombieriImagPartTest g
  have huCritical :
      YoshidaCriticalPullbackSupported yoshidaEndpointA gu :=
    bombieriRealPartTest_criticalPullbackSupported g hcritical
  have hvCritical :
      YoshidaCriticalPullbackSupported yoshidaEndpointA gv :=
    bombieriImagPartTest_criticalPullbackSupported g hcritical
  have huReal : ∀ x : ℝ,
      (gu.logarithmicPullbackSchwartz (1 / 2) x).im = 0 :=
    bombieriRealPartTest_criticalPullback_im_eq_zero g
  have hvReal : ∀ x : ℝ,
      (gv.logarithmicPullbackSchwartz (1 / 2) x).im = 0 :=
    bombieriImagPartTest_criticalPullback_im_eq_zero g
  have hreal : (factorTwoGlobalCrossSymbol g).re =
      yoshidaEndpointA * factorTwoEndpointChannelSymmetricSum
        (factorTwoCenteredProfile gu) (factorTwoCenteredProfile gv) := by
    calc
      (factorTwoGlobalCrossSymbol g).re = factorTwoSymmetricCoordinate g := by
        simpa only [factorTwoSymmetricCoordinate] using
          factorTwoGlobalCrossSymbol_re_eq_parity
            g ha hab hsupport hratio
      _ = factorTwoSymmetricCoordinate gu +
          factorTwoSymmetricCoordinate gv :=
        factorTwoSymmetricCoordinate_eq_realImag
          g ha hab hsupport hratio
      _ = yoshidaEndpointA * factorTwoCenteredSymmetricPerturbation
            (factorTwoCenteredProfile gu) +
          yoshidaEndpointA * factorTwoCenteredSymmetricPerturbation
            (factorTwoCenteredProfile gv) := by
        rw [factorTwoSymmetricCoordinate_eq_endpoint_mul_perturbation
            gu huCritical huReal,
          factorTwoSymmetricCoordinate_eq_endpoint_mul_perturbation
            gv hvCritical hvReal]
      _ = yoshidaEndpointA * factorTwoEndpointChannelSymmetricSum
          (factorTwoCenteredProfile gu) (factorTwoCenteredProfile gv) := by
        unfold factorTwoEndpointChannelSymmetricSum
        ring
  have himag : (factorTwoGlobalCrossSymbol g).im =
      yoshidaEndpointA * factorTwoCenteredAlternatingCoupling
        (factorTwoCenteredProfile gu) (factorTwoCenteredProfile gv) := by
    calc
      (factorTwoGlobalCrossSymbol g).im =
          factorTwoAntisymmetricCoordinate g := by
        simpa only [factorTwoAntisymmetricCoordinate] using
          factorTwoGlobalCrossSymbol_im_eq_parity
            g ha hab hsupport hratio
      _ = factorTwoMixedParityCoupling gu gv := by
        simpa only [gu, gv] using
          factorTwoAntisymmetricCoordinate_eq_realImag g
      _ = yoshidaEndpointA * factorTwoCenteredAlternatingCoupling
          (factorTwoCenteredProfile gu) (factorTwoCenteredProfile gv) :=
        factorTwoMixedParityCoupling_eq_endpoint_mul_centeredAlternating
          gu gv huCritical hvCritical huReal hvReal
  apply Complex.ext
  · simpa only [factorTwoEndpointChannelCoordinate,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, gu, gv] using hreal
  · simpa only [factorTwoEndpointChannelCoordinate,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, gu, gv] using himag

/-- The production cross norm carries exactly the square of the endpoint
scale; no additional realification factor appears. -/
theorem factorTwoGlobalCrossSymbol_normSq_eq_endpoint_sq_mul_channelCoordinate
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    Complex.normSq (factorTwoGlobalCrossSymbol g) =
      yoshidaEndpointA ^ 2 *
        Complex.normSq (factorTwoEndpointChannelCoordinate
          (factorTwoCenteredProfile (bombieriRealPartTest g))
          (factorTwoCenteredProfile (bombieriImagPartTest g))) := by
  rw [factorTwoGlobalCrossSymbol_eq_endpoint_mul_channelCoordinate
    g ha hab hsupport hratio hcritical]
  simp only [factorTwoEndpointChannelCoordinate,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

/-- The production determinant bound is exactly the numerical-radius bound
for the complete canonical endpoint channel. -/
theorem factorTwoGlobalCrossSymbol_normSq_le_diagonal_sq_iff_channelRadius
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    Complex.normSq (factorTwoGlobalCrossSymbol g) ≤
        factorTwoDiagonalCoordinate g ^ 2 ↔
      Complex.normSq (factorTwoEndpointChannelCoordinate
          (factorTwoCenteredProfile (bombieriRealPartTest g))
          (factorTwoCenteredProfile (bombieriImagPartTest g))) ≤
        factorTwoEndpointChannelCleanSum
            (factorTwoCenteredProfile (bombieriRealPartTest g))
            (factorTwoCenteredProfile (bombieriImagPartTest g)) ^ 2 := by
  rw [factorTwoGlobalCrossSymbol_normSq_eq_endpoint_sq_mul_channelCoordinate
      g ha hab hsupport hratio hcritical,
    factorTwoDiagonalCoordinate_eq_endpoint_mul_channelCleanSum
      g ha hab hsupport hratio hcritical]
  have hA2 : 0 < yoshidaEndpointA ^ 2 :=
    sq_pos_of_pos yoshidaEndpointA_pos
  constructor
  · intro hscaled
    apply le_of_mul_le_mul_left (a := yoshidaEndpointA ^ 2) _ hA2
    convert hscaled using 1
    all_goals ring
  · intro hradius
    have hscaled := mul_le_mul_of_nonneg_left hradius hA2.le
    convert hscaled using 1
    all_goals ring

/-- Strict determinant failure is exactly strict overflow of the complete
canonical endpoint-channel radius. -/
theorem diagonal_sq_lt_factorTwoGlobalCrossSymbol_normSq_iff_channelRadius
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    factorTwoDiagonalCoordinate g ^ 2 <
        Complex.normSq (factorTwoGlobalCrossSymbol g) ↔
      factorTwoEndpointChannelCleanSum
            (factorTwoCenteredProfile (bombieriRealPartTest g))
            (factorTwoCenteredProfile (bombieriImagPartTest g)) ^ 2 <
        Complex.normSq (factorTwoEndpointChannelCoordinate
          (factorTwoCenteredProfile (bombieriRealPartTest g))
          (factorTwoCenteredProfile (bombieriImagPartTest g))) := by
  rw [factorTwoGlobalCrossSymbol_normSq_eq_endpoint_sq_mul_channelCoordinate
      g ha hab hsupport hratio hcritical,
    factorTwoDiagonalCoordinate_eq_endpoint_mul_channelCleanSum
      g ha hab hsupport hratio hcritical]
  have hA2 : 0 < yoshidaEndpointA ^ 2 :=
    sq_pos_of_pos yoshidaEndpointA_pos
  constructor
  · intro hscaled
    apply lt_of_mul_lt_mul_left (a := yoshidaEndpointA ^ 2) _ hA2.le
    convert hscaled using 1
    all_goals ring
  · intro hradius
    have hscaled := mul_lt_mul_of_pos_left hradius hA2
    convert hscaled using 1
    all_goals ring

/-- Universal production two-bump positivity is exactly the numerical-radius
bound for the complete canonical endpoint channel. -/
theorem bombieriFunctional_twoBump_nonneg_iff_endpoint_channelRadius
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
      Complex.normSq (factorTwoEndpointChannelCoordinate
          (factorTwoCenteredProfile (bombieriRealPartTest g))
          (factorTwoCenteredProfile (bombieriImagPartTest g))) ≤
        factorTwoEndpointChannelCleanSum
            (factorTwoCenteredProfile (bombieriRealPartTest g))
            (factorTwoCenteredProfile (bombieriImagPartTest g)) ^ 2 := by
  have hfunctional :
      (bombieriFunctional (bombieriQuadraticTest g)).re =
        factorTwoDiagonalCoordinate g := by
    simpa only [factorTwoDiagonalCoordinate] using
      bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
        g ha hab hsupport hratio
  rw [bombieriFunctional_twoBump_nonneg_iff
      g ha hab hsupport hratio,
    hfunctional]
  exact factorTwoGlobalCrossSymbol_normSq_le_diagonal_sq_iff_channelRadius
    g ha hab hsupport hratio hcritical

/-- A negative production two-bump member exists exactly when the complete
canonical endpoint-channel radius strictly exceeds its clean center. -/
theorem exists_bombieriFunctional_twoBump_neg_iff_endpoint_channelRadius
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2)
    (hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA g) :
    (∃ c : ℂ,
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re < 0) ↔
      factorTwoEndpointChannelCleanSum
            (factorTwoCenteredProfile (bombieriRealPartTest g))
            (factorTwoCenteredProfile (bombieriImagPartTest g)) ^ 2 <
        Complex.normSq (factorTwoEndpointChannelCoordinate
          (factorTwoCenteredProfile (bombieriRealPartTest g))
          (factorTwoCenteredProfile (bombieriImagPartTest g))) := by
  have hfunctional :
      (bombieriFunctional (bombieriQuadraticTest g)).re =
        factorTwoDiagonalCoordinate g := by
    simpa only [factorTwoDiagonalCoordinate] using
      bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
        g ha hab hsupport hratio
  rw [exists_bombieriFunctional_twoBump_neg_iff
      g ha hab hsupport hratio,
    hfunctional]
  exact diagonal_sq_lt_factorTwoGlobalCrossSymbol_normSq_iff_channelRadius
    g ha hab hsupport hratio hcritical

/-! ## The two reflection blocks -/

/-- The even--odd reflection block is the generic opposite-parity channel on
the corresponding projected profiles. -/
theorem factorTwoReflectionEvenOddChannelPencil_eq_oppositeParity
    (u v : ℝ → ℝ) (r s : ℝ) :
    factorTwoReflectionEvenOddChannelPencil u v r s =
      factorTwoEndpointChannelPencil
        (factorTwoReflectionEvenPart u) (factorTwoReflectionOddPart v) r s := by
  unfold factorTwoReflectionEvenOddChannelPencil
    factorTwoEndpointChannelPencil
    factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
    factorTwoCenteredEndpointPlus factorTwoCenteredEndpointMinus
  ring

/-- The odd--even reflection block is the generic opposite-parity channel on
the corresponding projected profiles. -/
theorem factorTwoReflectionOddEvenChannelPencil_eq_oppositeParity
    (u v : ℝ → ℝ) (r s : ℝ) :
    factorTwoReflectionOddEvenChannelPencil u v r s =
      factorTwoEndpointChannelPencil
        (factorTwoReflectionOddPart u) (factorTwoReflectionEvenPart v) r s := by
  unfold factorTwoReflectionOddEvenChannelPencil
    factorTwoEndpointChannelPencil
    factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
    factorTwoCenteredEndpointPlus factorTwoCenteredEndpointMinus
  ring

/-! ## The sharp total reflection radius -/

/-- The clean center of the complete reflection-parity pencil. -/
def factorTwoReflectionParityChannelCleanSum (u v : ℝ → ℝ) : ℝ :=
  factorTwoEndpointChannelCleanSum
      (factorTwoReflectionEvenPart u) (factorTwoReflectionOddPart v) +
    factorTwoEndpointChannelCleanSum
      (factorTwoReflectionOddPart u) (factorTwoReflectionEvenPart v)

/-- The complete symmetric coordinate after both reflection blocks are
summed. -/
def factorTwoReflectionParityChannelSymmetricSum (u v : ℝ → ℝ) : ℝ :=
  factorTwoEndpointChannelSymmetricSum
      (factorTwoReflectionEvenPart u) (factorTwoReflectionOddPart v) +
    factorTwoEndpointChannelSymmetricSum
      (factorTwoReflectionOddPart u) (factorTwoReflectionEvenPart v)

/-- The sharp complex coordinate of the full reflection pencil.  The two
block coordinates are added before taking the norm. -/
def factorTwoReflectionParityChannelCoordinate (u v : ℝ → ℝ) : ℂ :=
  ⟨factorTwoReflectionParityChannelSymmetricSum u v,
    factorTwoReflectionParityAlternatingSum u v⟩

@[simp] theorem factorTwoReflectionParityChannelCoordinate_normSq
    (u v : ℝ → ℝ) :
    Complex.normSq (factorTwoReflectionParityChannelCoordinate u v) =
      factorTwoReflectionParityChannelSymmetricSum u v ^ 2 +
        factorTwoReflectionParityAlternatingSum u v ^ 2 := by
  simp only [factorTwoReflectionParityChannelCoordinate,
    Complex.normSq_apply]
  ring

/-- The total reflection coordinate is the complex sum of its two
opposite-parity block coordinates. -/
theorem factorTwoReflectionParityChannelCoordinate_eq_block_add
    (u v : ℝ → ℝ) :
    factorTwoReflectionParityChannelCoordinate u v =
      factorTwoEndpointChannelCoordinate
          (factorTwoReflectionEvenPart u) (factorTwoReflectionOddPart v) +
        factorTwoEndpointChannelCoordinate
          (factorTwoReflectionOddPart u) (factorTwoReflectionEvenPart v) := by
  apply Complex.ext
  · simp only [factorTwoReflectionParityChannelCoordinate,
      factorTwoReflectionParityChannelSymmetricSum,
      factorTwoEndpointChannelCoordinate, Complex.add_re]
  · simp only [factorTwoReflectionParityChannelCoordinate,
      factorTwoEndpointChannelCoordinate, Complex.add_im,
      factorTwoReflectionParityAlternatingSum]

/-- The full reflection pencil is the rotated pencil of its total clean,
symmetric, and alternating coordinates. -/
theorem factorTwoReflectionParityPencil_eq_rotatedChannel
    (u v : ℝ → ℝ) (r s : ℝ) :
    factorTwoReflectionParityPencil u v r s =
      (factorTwoReflectionParityChannelCleanSum u v +
          factorTwoReflectionParityChannelSymmetricSum u v) * r ^ 2 +
        2 * factorTwoReflectionParityAlternatingSum u v * r * s +
        (factorTwoReflectionParityChannelCleanSum u v -
          factorTwoReflectionParityChannelSymmetricSum u v) * s ^ 2 := by
  unfold factorTwoReflectionParityPencil
    factorTwoReflectionParityEndpointPlusSum
    factorTwoReflectionParityEndpointMinusSum
    factorTwoReflectionParityChannelCleanSum
    factorTwoReflectionParityChannelSymmetricSum
    factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
    factorTwoCenteredEndpointPlus factorTwoCenteredEndpointMinus
  ring

/-- Exact numerical-radius criterion for the complete reflection-parity
pencil.  Unlike the blockwise sufficient criterion below, this theorem allows
compensation between the two complex block coordinates. -/
theorem factorTwoReflectionParityPencil_nonneg_iff_totalRadius
    (u v : ℝ → ℝ) :
    (∀ r s : ℝ, 0 ≤ factorTwoReflectionParityPencil u v r s) ↔
      0 ≤ factorTwoReflectionParityChannelCleanSum u v ∧
        Complex.normSq (factorTwoReflectionParityChannelCoordinate u v) ≤
          factorTwoReflectionParityChannelCleanSum u v ^ 2 := by
  rw [factorTwoReflectionParityChannelCoordinate_normSq]
  have hcriterion := real_rotated_quadratic_pencil_nonneg_iff
    (factorTwoReflectionParityChannelCleanSum u v)
    (factorTwoReflectionParityChannelSymmetricSum u v)
    (factorTwoReflectionParityAlternatingSum u v)
  constructor
  · intro hpencil
    apply hcriterion.mp
    intro r s
    rw [← factorTwoReflectionParityPencil_eq_rotatedChannel]
    exact hpencil r s
  · intro hradius r s
    rw [factorTwoReflectionParityPencil_eq_rotatedChannel]
    exact hcriterion.mpr hradius r s

/-- Exact strict-reverse criterion for the complete reflection-parity pencil.
The two block coordinates are summed before their radius is tested. -/
theorem factorTwoReflectionParityPencil_exists_neg_iff_totalRadius
    (u v : ℝ → ℝ) :
    (∃ r s : ℝ, factorTwoReflectionParityPencil u v r s < 0) ↔
      factorTwoReflectionParityChannelCleanSum u v < 0 ∨
        factorTwoReflectionParityChannelCleanSum u v ^ 2 <
          Complex.normSq (factorTwoReflectionParityChannelCoordinate u v) := by
  rw [factorTwoReflectionParityChannelCoordinate_normSq]
  have hcriterion := real_rotated_quadratic_pencil_exists_neg_iff
    (factorTwoReflectionParityChannelCleanSum u v)
    (factorTwoReflectionParityChannelSymmetricSum u v)
    (factorTwoReflectionParityAlternatingSum u v)
  constructor
  · rintro ⟨r, s, hneg⟩
    apply hcriterion.mp
    refine ⟨r, s, ?_⟩
    rw [← factorTwoReflectionParityPencil_eq_rotatedChannel]
    exact hneg
  · intro hfailure
    obtain ⟨r, s, hneg⟩ := hcriterion.mpr hfailure
    refine ⟨r, s, ?_⟩
    rw [factorTwoReflectionParityPencil_eq_rotatedChannel]
    exact hneg

/-- The even--odd block is nonnegative exactly when its complete complex
coordinate lies in the clean radius. -/
theorem factorTwoReflectionEvenOddChannelPencil_nonneg_iff_radius
    (u v : ℝ → ℝ) :
    (∀ r s : ℝ,
      0 ≤ factorTwoReflectionEvenOddChannelPencil u v r s) ↔
      0 ≤ factorTwoEndpointChannelCleanSum
          (factorTwoReflectionEvenPart u) (factorTwoReflectionOddPart v) ∧
        Complex.normSq (factorTwoEndpointChannelCoordinate
          (factorTwoReflectionEvenPart u) (factorTwoReflectionOddPart v)) ≤
          factorTwoEndpointChannelCleanSum
              (factorTwoReflectionEvenPart u)
              (factorTwoReflectionOddPart v) ^ 2 := by
  simpa only [factorTwoReflectionEvenOddChannelPencil_eq_oppositeParity]
    using factorTwoEndpointChannelPencil_nonneg_iff_radius
      (factorTwoReflectionEvenPart u) (factorTwoReflectionOddPart v)

/-- The odd--even block is nonnegative exactly when its complete complex
coordinate lies in the clean radius. -/
theorem factorTwoReflectionOddEvenChannelPencil_nonneg_iff_radius
    (u v : ℝ → ℝ) :
    (∀ r s : ℝ,
      0 ≤ factorTwoReflectionOddEvenChannelPencil u v r s) ↔
      0 ≤ factorTwoEndpointChannelCleanSum
          (factorTwoReflectionOddPart u) (factorTwoReflectionEvenPart v) ∧
        Complex.normSq (factorTwoEndpointChannelCoordinate
          (factorTwoReflectionOddPart u) (factorTwoReflectionEvenPart v)) ≤
          factorTwoEndpointChannelCleanSum
              (factorTwoReflectionOddPart u)
              (factorTwoReflectionEvenPart v) ^ 2 := by
  simpa only [factorTwoReflectionOddEvenChannelPencil_eq_oppositeParity]
    using factorTwoEndpointChannelPencil_nonneg_iff_radius
      (factorTwoReflectionOddPart u) (factorTwoReflectionEvenPart v)

/-- A strict negative direction exists in the even--odd block exactly when
its clean center is negative or its complete complex radius is too large. -/
theorem factorTwoReflectionEvenOddChannelPencil_exists_neg_iff_radius
    (u v : ℝ → ℝ) :
    (∃ r s : ℝ,
      factorTwoReflectionEvenOddChannelPencil u v r s < 0) ↔
      factorTwoEndpointChannelCleanSum
          (factorTwoReflectionEvenPart u) (factorTwoReflectionOddPart v) < 0 ∨
        factorTwoEndpointChannelCleanSum
              (factorTwoReflectionEvenPart u)
              (factorTwoReflectionOddPart v) ^ 2 <
          Complex.normSq (factorTwoEndpointChannelCoordinate
            (factorTwoReflectionEvenPart u)
            (factorTwoReflectionOddPart v)) := by
  simpa only [factorTwoReflectionEvenOddChannelPencil_eq_oppositeParity]
    using factorTwoEndpointChannelPencil_exists_neg_iff_radius
      (factorTwoReflectionEvenPart u) (factorTwoReflectionOddPart v)

/-- A strict negative direction exists in the odd--even block exactly when
its clean center is negative or its complete complex radius is too large. -/
theorem factorTwoReflectionOddEvenChannelPencil_exists_neg_iff_radius
    (u v : ℝ → ℝ) :
    (∃ r s : ℝ,
      factorTwoReflectionOddEvenChannelPencil u v r s < 0) ↔
      factorTwoEndpointChannelCleanSum
          (factorTwoReflectionOddPart u) (factorTwoReflectionEvenPart v) < 0 ∨
        factorTwoEndpointChannelCleanSum
              (factorTwoReflectionOddPart u)
              (factorTwoReflectionEvenPart v) ^ 2 <
          Complex.normSq (factorTwoEndpointChannelCoordinate
            (factorTwoReflectionOddPart u)
            (factorTwoReflectionEvenPart v)) := by
  simpa only [factorTwoReflectionOddEvenChannelPencil_eq_oppositeParity]
    using factorTwoEndpointChannelPencil_exists_neg_iff_radius
      (factorTwoReflectionOddPart u) (factorTwoReflectionEvenPart v)

/-- The two sharp channel-radius inequalities imply nonnegativity of the full
reflection-parity pencil. -/
theorem factorTwoReflectionParityPencil_nonneg_of_channelRadii
    (u v : ℝ → ℝ)
    (hEvenOdd :
      0 ≤ factorTwoEndpointChannelCleanSum
          (factorTwoReflectionEvenPart u) (factorTwoReflectionOddPart v) ∧
        Complex.normSq (factorTwoEndpointChannelCoordinate
          (factorTwoReflectionEvenPart u) (factorTwoReflectionOddPart v)) ≤
          factorTwoEndpointChannelCleanSum
              (factorTwoReflectionEvenPart u)
              (factorTwoReflectionOddPart v) ^ 2)
    (hOddEven :
      0 ≤ factorTwoEndpointChannelCleanSum
          (factorTwoReflectionOddPart u) (factorTwoReflectionEvenPart v) ∧
        Complex.normSq (factorTwoEndpointChannelCoordinate
          (factorTwoReflectionOddPart u) (factorTwoReflectionEvenPart v)) ≤
          factorTwoEndpointChannelCleanSum
              (factorTwoReflectionOddPart u)
              (factorTwoReflectionEvenPart v) ^ 2) :
    ∀ r s : ℝ, 0 ≤ factorTwoReflectionParityPencil u v r s := by
  apply factorTwoReflectionParityPencil_nonneg_of_channels
  · exact
      (factorTwoReflectionEvenOddChannelPencil_nonneg_iff_radius u v).mpr
        hEvenOdd
  · exact
      (factorTwoReflectionOddEvenChannelPencil_nonneg_iff_radius u v).mpr
        hOddEven

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointChannelRadius
