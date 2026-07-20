import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedFiniteSevenClosureStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped Interval

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedFiniteSevenEntryEnclosuresStructural

noncomputable section

open YoshidaRegularKernelBound
open CenteredEndpointCorrelation
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open YoshidaConstantBounds
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFourCellEvenEndpointCoshSchurStructural
open YoshidaFourCellEvenEndpointSeedFiniteSevenClosureStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEvenZeroCoshRegularStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural

/-!
# Degree-eighteen regular-kernel entry enclosures

The finite seven-coordinate endpoint-border certificate reduces its analytic
frontier to twenty-one scalar entry boxes of radius `10⁻⁹`.  This file begins
the structural closure of those boxes with a one-sided degree-eighteen
polynomial envelope for the regular Yoshida kernel on the exact argument range
`[0, 7/8]`.

The proof uses Taylor's theorem once for each hyperbolic factor and exact
rational product identities.  It does not enumerate modes or sample the
kernel.
-/

private def finiteSevenCoshPolynomial18 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 2 + u ^ 4 / 24 + u ^ 6 / 720 + u ^ 8 / 40320 +
    u ^ 10 / 3628800 + u ^ 12 / 479001600 + u ^ 14 / 87178291200 +
    u ^ 16 / 20922789888000 + u ^ 18 / 6402373705728000

private def finiteSevenCoshUpper20 (u : ℝ) : ℝ :=
  finiteSevenCoshPolynomial18 u +
    (4 / 3 : ℝ) * u ^ 20 / 2432902008176640000

private def finiteSevenSinhDivPolynomial18 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 6 + u ^ 4 / 120 + u ^ 6 / 5040 + u ^ 8 / 362880 +
    u ^ 10 / 39916800 + u ^ 12 / 6227020800 +
    u ^ 14 / 1307674368000 + u ^ 16 / 355687428096000 +
    u ^ 18 / 121645100408832000

private def finiteSevenSinhDivUpper20 (u : ℝ) : ℝ :=
  finiteSevenSinhDivPolynomial18 u +
    (4 / 3 : ℝ) * u ^ 20 / 51090942171709440000

private def finiteSevenSechPolynomial18 (u : ℝ) : ℝ :=
  1 - u ^ 2 / 2 + 5 * u ^ 4 / 24 - 61 * u ^ 6 / 720 +
    277 * u ^ 8 / 8064 - 50521 * u ^ 10 / 3628800 +
    540553 * u ^ 12 / 95800320 -
    199360981 * u ^ 14 / 87178291200 +
    3878302429 * u ^ 16 / 4184557977600 -
    2404879675441 * u ^ 18 / 6402373705728000

private def finiteSevenCschRegularPolynomial17 (u : ℝ) : ℝ :=
  -u / 6 + 7 * u ^ 3 / 360 - 31 * u ^ 5 / 15120 +
    127 * u ^ 7 / 604800 - 73 * u ^ 9 / 3421440 +
    1414477 * u ^ 11 / 653837184000 -
    8191 * u ^ 13 / 37362124800 +
    16931177 * u ^ 15 / 762187345920000 -
    5749691557 * u ^ 17 / 2554547108585472000

private def finiteSevenCschMultiplier18 (u : ℝ) : ℝ :=
  1 + u * finiteSevenCschRegularPolynomial17 u

/-- Degree-eighteen polynomial center for the regular Yoshida kernel on the
finite-seven endpoint range. -/
def fourCellEvenFiniteSevenRegularKernelPolynomial18 (t : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
    (finiteSevenSechPolynomial18 (t / 2) +
      finiteSevenCschRegularPolynomial17 (t / 2))

private def finiteSevenSechError18 (u : ℝ) : ℝ :=
  u ^ 20 *
      (2404879675441 * u ^ 16 + 729959377968576 * u ^ 14 +
        174813260803622460 * u ^ 12 +
        31712479703011077120 * u ^ 10 +
        4164736058639407307520 * u ^ 8 +
        371592437619793522728960 * u ^ 6 +
        20467769081636608836249600 * u ^ 4 +
        591036904275677067195187200 * u ^ 2 +
        6240144097187294688659865600) /
    40990389067797283140009984000000

private def finiteSevenCschError17 (u : ℝ) : ℝ :=
  u ^ 19 *
      (28748457785 * u ^ 16 + 9548239898304 * u ^ 14 +
        2580060167318268 * u ^ 12 + 536138362455284736 * u ^ 10 +
        82318533971635987200 * u ^ 8 +
        8824651426252977315840 * u ^ 6 +
        606775801017336881817600 * u ^ 4 +
        23153985672008952899174400 * u ^ 2 +
        354332239612362813970022400) /
    1553740697614856017422078443520000000

private theorem finiteSeven_cosh_lt_four_thirds
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    Real.cosh u < (4 / 3 : ℝ) := by
  have huSq : u ^ 2 < (7 / 10 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hu hu0 (by norm_num)
  have hv0 : 0 ≤ u ^ 2 / 2 := by positivity
  have hvQuarter : u ^ 2 / 2 < (1 / 4 : ℝ) := by
    norm_num at huSq ⊢
    nlinarith
  have hv1 : u ^ 2 / 2 < (1 : ℝ) := hvQuarter.trans (by norm_num)
  have hExp : Real.exp (u ^ 2 / 2) ≤ 1 / (1 - u ^ 2 / 2) :=
    Real.exp_bound_div_one_sub_of_interval hv0 hv1
  have hFrac : 1 / (1 - u ^ 2 / 2) < (4 / 3 : ℝ) := by
    rw [div_lt_iff₀ (sub_pos.mpr hv1)]
    nlinarith
  exact (Real.cosh_le_exp_half_sq u).trans_lt (hExp.trans_lt hFrac)

private theorem finiteSeven_cosh_taylor_bounds
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    finiteSevenCoshPolynomial18 u ≤ Real.cosh u ∧
      Real.cosh u ≤ finiteSevenCoshUpper20 u := by
  rcases eq_or_lt_of_le hu0 with rfl | hupos
  · norm_num [finiteSevenCoshPolynomial18, finiteSevenCoshUpper20]
  · rcases taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.cosh) (x₀ := 0) (x := u) (n := 19) hupos
        Real.contDiff_cosh.contDiffOn with ⟨w, hw, hTaylor⟩
    have hTaylorEval :
        taylorWithinEval Real.cosh 19 (Icc 0 u) 0 u =
          finiteSevenCoshPolynomial18 u := by
      have hder (n : ℕ) :
          iteratedDerivWithin n Real.cosh (Icc 0 u) 0 =
            iteratedDeriv n Real.cosh 0 :=
        Real.iteratedDerivWithin_cosh_Icc n hupos ⟨le_rfl, hu0⟩
      rw [taylor_within_apply]
      simp [hder, Finset.sum_range_succ, finiteSevenCoshPolynomial18]
      ring
    rw [hTaylorEval] at hTaylor
    norm_num [Real.iteratedDeriv_even_cosh] at hTaylor
    have hwBound : Real.cosh w < (4 / 3 : ℝ) :=
      finiteSeven_cosh_lt_four_thirds hw.1.le (hw.2.trans hu)
    have hrem0 : 0 ≤ Real.cosh w * u ^ 20 / 2432902008176640000 := by
      positivity
    have hremUpper :
        Real.cosh w * u ^ 20 / 2432902008176640000 ≤
          (4 / 3 : ℝ) * u ^ 20 / 2432902008176640000 := by
      gcongr
    constructor
    · linarith
    · unfold finiteSevenCoshUpper20
      linarith

private theorem finiteSeven_sinhDiv_taylor_bounds
    {u : ℝ} (hu0 : 0 < u) (hu : u < (7 / 10 : ℝ)) :
    finiteSevenSinhDivPolynomial18 u ≤ Real.sinh u / u ∧
      Real.sinh u / u ≤ finiteSevenSinhDivUpper20 u := by
  rcases taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.sinh) (x₀ := 0) (x := u) (n := 20) hu0
      Real.contDiff_sinh.contDiffOn with ⟨w, hw, hTaylor⟩
  have hTaylorEval :
      taylorWithinEval Real.sinh 20 (Icc 0 u) 0 u =
        u + u ^ 3 / 6 + u ^ 5 / 120 + u ^ 7 / 5040 +
          u ^ 9 / 362880 + u ^ 11 / 39916800 +
          u ^ 13 / 6227020800 + u ^ 15 / 1307674368000 +
          u ^ 17 / 355687428096000 + u ^ 19 / 121645100408832000 := by
    have hder (n : ℕ) :
        iteratedDerivWithin n Real.sinh (Icc 0 u) 0 =
          iteratedDeriv n Real.sinh 0 :=
      Real.iteratedDerivWithin_sinh_Icc n hu0 ⟨le_rfl, hu0.le⟩
    rw [taylor_within_apply]
    simp [hder, Finset.sum_range_succ]
    ring
  rw [hTaylorEval] at hTaylor
  norm_num [Real.iteratedDeriv_odd_sinh] at hTaylor
  have hdiv :
      Real.sinh u / u - finiteSevenSinhDivPolynomial18 u =
        Real.cosh w * u ^ 20 / 51090942171709440000 := by
    unfold finiteSevenSinhDivPolynomial18
    rw [show Real.sinh u / u -
          (1 + u ^ 2 / 6 + u ^ 4 / 120 + u ^ 6 / 5040 +
            u ^ 8 / 362880 + u ^ 10 / 39916800 +
            u ^ 12 / 6227020800 + u ^ 14 / 1307674368000 +
            u ^ 16 / 355687428096000 + u ^ 18 / 121645100408832000) =
        (Real.sinh u -
          (u + u ^ 3 / 6 + u ^ 5 / 120 + u ^ 7 / 5040 +
            u ^ 9 / 362880 + u ^ 11 / 39916800 +
            u ^ 13 / 6227020800 + u ^ 15 / 1307674368000 +
            u ^ 17 / 355687428096000 + u ^ 19 / 121645100408832000)) / u by
      field_simp [hu0.ne'],
      hTaylor]
    field_simp [hu0.ne']
  have hwBound : Real.cosh w < (4 / 3 : ℝ) :=
    finiteSeven_cosh_lt_four_thirds hw.1.le (hw.2.trans hu)
  have hrem0 : 0 ≤ Real.cosh w * u ^ 20 / 51090942171709440000 := by
    positivity
  have hremUpper :
      Real.cosh w * u ^ 20 / 51090942171709440000 ≤
        (4 / 3 : ℝ) * u ^ 20 / 51090942171709440000 := by
    gcongr
  constructor
  · linarith
  · unfold finiteSevenSinhDivUpper20
    linarith

private theorem finiteSeven_sechPolynomial18_nonnegative
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (7 / 16 : ℝ)) :
    0 ≤ finiteSevenSechPolynomial18 u := by
  have huSqRaw : u ^ 2 ≤ (7 / 16 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hu0 hu 2
  have huSq : u ^ 2 ≤ (1 / 5 : ℝ) := by
    norm_num at huSqRaw ⊢
    linarith
  have hbase : 0 ≤ 1 - u ^ 2 / 2 := by nlinarith
  have h₁ : 0 ≤ (5 / 24 : ℝ) - 61 * u ^ 2 / 720 := by nlinarith
  have h₂ : 0 ≤ (277 / 8064 : ℝ) - 50521 * u ^ 2 / 3628800 := by
    nlinarith
  have h₃ :
      0 ≤ (540553 / 95800320 : ℝ) -
        199360981 * u ^ 2 / 87178291200 := by
    nlinarith
  have h₄ :
      0 ≤ (3878302429 / 4184557977600 : ℝ) -
        2404879675441 * u ^ 2 / 6402373705728000 := by
    nlinarith
  have hgroup :
      finiteSevenSechPolynomial18 u =
        (1 - u ^ 2 / 2) +
          u ^ 4 * ((5 / 24 : ℝ) - 61 * u ^ 2 / 720) +
          u ^ 8 * ((277 / 8064 : ℝ) - 50521 * u ^ 2 / 3628800) +
          u ^ 12 * ((540553 / 95800320 : ℝ) -
            199360981 * u ^ 2 / 87178291200) +
          u ^ 16 * ((3878302429 / 4184557977600 : ℝ) -
            2404879675441 * u ^ 2 / 6402373705728000) := by
    unfold finiteSevenSechPolynomial18
    ring
  rw [hgroup]
  positivity

private theorem finiteSeven_cschMultiplier18_nonnegative
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (7 / 16 : ℝ)) :
    0 ≤ finiteSevenCschMultiplier18 u := by
  have huSqRaw : u ^ 2 ≤ (7 / 16 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hu0 hu 2
  have huSq : u ^ 2 ≤ (1 / 5 : ℝ) := by
    norm_num at huSqRaw ⊢
    linarith
  have hbase : 0 ≤ 1 - u ^ 2 / 6 := by nlinarith
  have h₁ : 0 ≤ (7 / 360 : ℝ) - 31 * u ^ 2 / 15120 := by nlinarith
  have h₂ : 0 ≤ (127 / 604800 : ℝ) - 73 * u ^ 2 / 3421440 := by
    nlinarith
  have h₃ :
      0 ≤ (1414477 / 653837184000 : ℝ) -
        8191 * u ^ 2 / 37362124800 := by
    nlinarith
  have h₄ :
      0 ≤ (16931177 / 762187345920000 : ℝ) -
        5749691557 * u ^ 2 / 2554547108585472000 := by
    nlinarith
  have hgroup :
      finiteSevenCschMultiplier18 u =
        (1 - u ^ 2 / 6) +
          u ^ 4 * ((7 / 360 : ℝ) - 31 * u ^ 2 / 15120) +
          u ^ 8 * ((127 / 604800 : ℝ) - 73 * u ^ 2 / 3421440) +
          u ^ 12 * ((1414477 / 653837184000 : ℝ) -
            8191 * u ^ 2 / 37362124800) +
          u ^ 16 * ((16931177 / 762187345920000 : ℝ) -
            5749691557 * u ^ 2 / 2554547108585472000) := by
    unfold finiteSevenCschMultiplier18 finiteSevenCschRegularPolynomial17
    ring
  rw [hgroup]
  positivity

set_option maxHeartbeats 800000 in
private theorem finiteSeven_sech_upper_product_identity (u : ℝ) :
    finiteSevenSechPolynomial18 u * finiteSevenCoshUpper20 u - 1 =
      -(u ^ 20 *
        (2404879675441 * u ^ 18 + 679456904784315 * u ^ 16 +
          208053063791488800 * u ^ 14 +
          49821743203659189900 * u ^ 12 +
          9038056804493497032960 * u ^ 10 +
          1186949776492308275539200 * u ^ 8 +
          105903844722183577305600000 * u ^ 6 +
          5833314188265099690475776000 * u ^ 4 +
          168445517718571165337481216000 * u ^ 2 +
          1778441067698372583894355968000)) /
        11682260884322225694902845440000000 := by
  unfold finiteSevenSechPolynomial18 finiteSevenCoshUpper20
    finiteSevenCoshPolynomial18
  ring

set_option maxHeartbeats 800000 in
private theorem finiteSeven_csch_upper_product_identity (u : ℝ) :
    finiteSevenCschMultiplier18 u * finiteSevenSinhDivUpper20 u - 1 =
      -(u ^ 20 *
        (28748457785 * u ^ 18 + 8772031538109 * u ^ 16 +
          3010495769436960 * u ^ 14 + 812691320840480340 * u ^ 12 +
          168883856693083203840 * u ^ 10 +
          25930335518959823481600 * u ^ 8 +
          2779765225457174748057600 * u ^ 6 +
          191134377072102371104512000 * u ^ 4 +
          7293505488811609420394496000 * u ^ 2 +
          111614655465121550857629696000)) /
        489428319748679645487954709708800000000 := by
  unfold finiteSevenCschMultiplier18 finiteSevenCschRegularPolynomial17
    finiteSevenSinhDivUpper20 finiteSevenSinhDivPolynomial18
  ring

set_option maxHeartbeats 800000 in
private theorem finiteSeven_sech_lower_product_identity (u : ℝ) :
    1 - finiteSevenSechPolynomial18 u * finiteSevenCoshPolynomial18 u =
      finiteSevenSechError18 u := by
  unfold finiteSevenSechPolynomial18 finiteSevenCoshPolynomial18
    finiteSevenSechError18
  ring

set_option maxHeartbeats 800000 in
private theorem finiteSeven_csch_lower_product_identity (u : ℝ) :
    1 - finiteSevenCschMultiplier18 u * finiteSevenSinhDivPolynomial18 u =
      u * finiteSevenCschError17 u := by
  unfold finiteSevenCschMultiplier18 finiteSevenCschRegularPolynomial17
    finiteSevenSinhDivPolynomial18 finiteSevenCschError17
  ring

private theorem finiteSeven_sech_envelope
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (7 / 16 : ℝ)) :
    0 ≤ 1 / Real.cosh u - finiteSevenSechPolynomial18 u ∧
      1 / Real.cosh u - finiteSevenSechPolynomial18 u ≤
        finiteSevenSechError18 u := by
  have huWide : u < (7 / 10 : ℝ) := hu.trans_lt (by norm_num)
  have hTaylor := finiteSeven_cosh_taylor_bounds hu0 huWide
  have hP0 : 0 ≤ finiteSevenSechPolynomial18 u :=
    finiteSeven_sechPolynomial18_nonnegative hu0 hu
  have hPCup :
      finiteSevenSechPolynomial18 u * finiteSevenCoshUpper20 u ≤ 1 := by
    rw [← sub_nonpos, finiteSeven_sech_upper_product_identity]
    have hnonneg :
        0 ≤ u ^ 20 *
          (2404879675441 * u ^ 18 + 679456904784315 * u ^ 16 +
            208053063791488800 * u ^ 14 +
            49821743203659189900 * u ^ 12 +
            9038056804493497032960 * u ^ 10 +
            1186949776492308275539200 * u ^ 8 +
            105903844722183577305600000 * u ^ 6 +
            5833314188265099690475776000 * u ^ 4 +
            168445517718571165337481216000 * u ^ 2 +
            1778441067698372583894355968000) := by
      positivity
    nlinarith
  have hPCosh : finiteSevenSechPolynomial18 u * Real.cosh u ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTaylor.2 hP0).trans hPCup
  have hLower : 0 ≤ 1 / Real.cosh u - finiteSevenSechPolynomial18 u := by
    rw [sub_nonneg, le_div_iff₀ (Real.cosh_pos u)]
    simpa only [one_mul] using hPCosh
  constructor
  · exact hLower
  · have hIdentity :
        1 / Real.cosh u - finiteSevenSechPolynomial18 u =
          (1 - finiteSevenSechPolynomial18 u * Real.cosh u) /
            Real.cosh u := by
      field_simp [(Real.cosh_pos u).ne']
    have hNumerator0 :
        0 ≤ 1 - finiteSevenSechPolynomial18 u * Real.cosh u := by
      linarith
    have hDivide :
        (1 - finiteSevenSechPolynomial18 u * Real.cosh u) / Real.cosh u ≤
          1 - finiteSevenSechPolynomial18 u * Real.cosh u :=
      div_le_self hNumerator0 (Real.one_le_cosh u)
    have hPLower :
        finiteSevenSechPolynomial18 u * finiteSevenCoshPolynomial18 u ≤
          finiteSevenSechPolynomial18 u * Real.cosh u :=
      mul_le_mul_of_nonneg_left hTaylor.1 hP0
    rw [hIdentity]
    calc
      _ ≤ 1 - finiteSevenSechPolynomial18 u * Real.cosh u := hDivide
      _ ≤ 1 - finiteSevenSechPolynomial18 u *
          finiteSevenCoshPolynomial18 u := by nlinarith
      _ = finiteSevenSechError18 u :=
        finiteSeven_sech_lower_product_identity u

private theorem finiteSeven_csch_envelope
    {u : ℝ} (hu0 : 0 < u) (hu : u ≤ (7 / 16 : ℝ)) :
    0 ≤ 1 / Real.sinh u - 1 / u - finiteSevenCschRegularPolynomial17 u ∧
      1 / Real.sinh u - 1 / u - finiteSevenCschRegularPolynomial17 u ≤
        finiteSevenCschError17 u := by
  let A : ℝ := Real.sinh u / u
  have huWide : u < (7 / 10 : ℝ) := hu.trans_lt (by norm_num)
  have hTaylorRaw := finiteSeven_sinhDiv_taylor_bounds hu0 huWide
  have hTaylor :
      finiteSevenSinhDivPolynomial18 u ≤ A ∧
        A ≤ finiteSevenSinhDivUpper20 u := hTaylorRaw
  have hA1 : (1 : ℝ) ≤ A := by
    dsimp only [A]
    rw [le_div_iff₀ hu0]
    simpa using (Real.self_le_sinh_iff.mpr hu0.le)
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA1
  have hQ0 : 0 ≤ finiteSevenCschMultiplier18 u :=
    finiteSeven_cschMultiplier18_nonnegative hu0.le hu
  have hQAup :
      finiteSevenCschMultiplier18 u * finiteSevenSinhDivUpper20 u ≤ 1 := by
    rw [← sub_nonpos, finiteSeven_csch_upper_product_identity]
    have hnonneg :
        0 ≤ u ^ 20 *
          (28748457785 * u ^ 18 + 8772031538109 * u ^ 16 +
            3010495769436960 * u ^ 14 + 812691320840480340 * u ^ 12 +
            168883856693083203840 * u ^ 10 +
            25930335518959823481600 * u ^ 8 +
            2779765225457174748057600 * u ^ 6 +
            191134377072102371104512000 * u ^ 4 +
            7293505488811609420394496000 * u ^ 2 +
            111614655465121550857629696000) := by
      positivity
    nlinarith
  have hQA : finiteSevenCschMultiplier18 u * A ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTaylor.2 hQ0).trans hQAup
  have hQleInv : finiteSevenCschMultiplier18 u ≤ 1 / A := by
    rw [le_div_iff₀ hApos]
    simpa only [one_mul] using hQA
  have hSinhPos : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hMainIdentity :
      1 / Real.sinh u - 1 / u - finiteSevenCschRegularPolynomial17 u =
        (1 / A - finiteSevenCschMultiplier18 u) / u := by
    dsimp only [A]
    unfold finiteSevenCschMultiplier18
    field_simp [hu0.ne', hSinhPos.ne']
    ring
  have hLower :
      0 ≤ 1 / Real.sinh u - 1 / u - finiteSevenCschRegularPolynomial17 u := by
    rw [hMainIdentity]
    exact div_nonneg (sub_nonneg.mpr hQleInv) hu0.le
  constructor
  · exact hLower
  · have hInvIdentity :
        1 / A - finiteSevenCschMultiplier18 u =
          (1 - finiteSevenCschMultiplier18 u * A) / A := by
      field_simp [hApos.ne']
    have hNumerator0 : 0 ≤ 1 - finiteSevenCschMultiplier18 u * A := by
      linarith
    have hDivideA :
        (1 - finiteSevenCschMultiplier18 u * A) / A ≤
          1 - finiteSevenCschMultiplier18 u * A :=
      div_le_self hNumerator0 hA1
    have hQLower :
        finiteSevenCschMultiplier18 u * finiteSevenSinhDivPolynomial18 u ≤
          finiteSevenCschMultiplier18 u * A :=
      mul_le_mul_of_nonneg_left hTaylor.1 hQ0
    have hInner :
        1 / A - finiteSevenCschMultiplier18 u ≤
          u * finiteSevenCschError17 u := by
      rw [hInvIdentity]
      calc
        _ ≤ 1 - finiteSevenCschMultiplier18 u * A := hDivideA
        _ ≤ 1 - finiteSevenCschMultiplier18 u *
            finiteSevenSinhDivPolynomial18 u := by linarith
        _ = u * finiteSevenCschError17 u :=
          finiteSeven_csch_lower_product_identity u
    rw [hMainIdentity]
    rw [div_le_iff₀ hu0]
    simpa only [div_mul_cancel₀ _ hu0.ne', mul_comm] using hInner

private theorem finiteSeven_yoshidaRegularKernel_two_mul
    (u : ℝ) (hu : 0 < u) :
    yoshidaRegularKernel (2 * u) =
      (1 / 4 : ℝ) *
        (1 / Real.cosh u + (1 / Real.sinh u - 1 / u)) := by
  unfold yoshidaRegularKernel
  rw [if_neg (mul_ne_zero (by norm_num) hu.ne')]
  rw [show 2 * u / 2 = u by ring, Real.sinh_two_mul,
    ← Real.cosh_add_sinh]
  field_simp [hu.ne', (Real.sinh_pos_iff.mpr hu).ne',
    (Real.cosh_pos u).ne']
  ring

private theorem finiteSeven_regularKernelPolynomial18_two_mul (u : ℝ) :
    fourCellEvenFiniteSevenRegularKernelPolynomial18 (2 * u) =
      (1 / 4 : ℝ) *
        (finiteSevenSechPolynomial18 u +
          finiteSevenCschRegularPolynomial17 u) := by
  unfold fourCellEvenFiniteSevenRegularKernelPolynomial18
  ring

private theorem finiteSeven_sechError18_upper
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (7 / 16 : ℝ)) :
    finiteSevenSechError18 u ≤
      finiteSevenSechError18 (7 / 16 : ℝ) := by
  unfold finiteSevenSechError18
  gcongr

private theorem finiteSeven_cschError17_upper
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (7 / 16 : ℝ)) :
    finiteSevenCschError17 u ≤
      finiteSevenCschError17 (7 / 16 : ℝ) := by
  unfold finiteSevenCschError17
  gcongr

private theorem finiteSeven_endpoint_kernel_error_lt :
    (1 / 4 : ℝ) *
        (finiteSevenSechError18 (7 / 16 : ℝ) +
          finiteSevenCschError17 (7 / 16 : ℝ)) <
      (1 / 380000000000 : ℝ) := by
  norm_num [finiteSevenSechError18, finiteSevenCschError17]

/-- On the exact finite-seven argument range, the degree-eighteen polynomial
is a one-sided regular-kernel envelope with error below `1/380000000000`.
This uniform analytic statement is the kernel input for all twenty-one
border-entry enclosures. -/
theorem fourCellEvenFiniteSevenRegularKernelPolynomial18_sevenEighths_envelope
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (7 / 8 : ℝ)) :
    0 ≤ yoshidaRegularKernel t -
        fourCellEvenFiniteSevenRegularKernelPolynomial18 t ∧
      yoshidaRegularKernel t -
          fourCellEvenFiniteSevenRegularKernelPolynomial18 t <
        (1 / 380000000000 : ℝ) := by
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · constructor <;>
      norm_num [yoshidaRegularKernel,
        fourCellEvenFiniteSevenRegularKernelPolynomial18,
        finiteSevenSechPolynomial18,
        finiteSevenCschRegularPolynomial17]
  · let u : ℝ := t / 2
    have hu0 : 0 < u := by
      dsimp only [u]
      linarith
    have hu : u ≤ (7 / 16 : ℝ) := by
      dsimp only [u]
      linarith
    have hSech := finiteSeven_sech_envelope hu0.le hu
    have hCsch := finiteSeven_csch_envelope hu0 hu
    have htEq : t = 2 * u := by
      dsimp only [u]
      ring
    have hDifference :
        yoshidaRegularKernel t -
            fourCellEvenFiniteSevenRegularKernelPolynomial18 t =
          (1 / 4 : ℝ) *
            ((1 / Real.cosh u - finiteSevenSechPolynomial18 u) +
              (1 / Real.sinh u - 1 / u -
                finiteSevenCschRegularPolynomial17 u)) := by
      rw [htEq, finiteSeven_yoshidaRegularKernel_two_mul u hu0,
        finiteSeven_regularKernelPolynomial18_two_mul]
      ring
    have hError :
        yoshidaRegularKernel t -
            fourCellEvenFiniteSevenRegularKernelPolynomial18 t ≤
          (1 / 4 : ℝ) *
            (finiteSevenSechError18 u + finiteSevenCschError17 u) := by
      rw [hDifference]
      nlinarith
    have hSechBound := finiteSeven_sechError18_upper hu0.le hu
    have hCschBound := finiteSeven_cschError17_upper hu0.le hu
    constructor
    · rw [hDifference]
      nlinarith [hSech.1, hCsch.1]
    · exact hError.trans_lt <| by
        have :
            (1 / 4 : ℝ) *
                (finiteSevenSechError18 u + finiteSevenCschError17 u) ≤
              (1 / 4 : ℝ) *
                (finiteSevenSechError18 (7 / 16 : ℝ) +
                  finiteSevenCschError17 (7 / 16 : ℝ)) := by
          nlinarith
        exact this.trans_lt finiteSeven_endpoint_kernel_error_lt

/-! ## Uniform control of the six quotient coordinates -/

private theorem finiteSeven_centeredMode_eq_centeredLegendre
    (n : ℕ) (x : ℝ) :
    fourCellEvenFiniteSevenCenteredMode n x =
      (centeredShiftedLegendreReal n).eval x := by
  unfold fourCellEvenFiniteSevenCenteredMode centeredPolynomialLift
  exact (eval_centeredShiftedLegendreReal n x).symm

private theorem finiteSeven_centeredMode_continuous (n : ℕ) :
    Continuous (fourCellEvenFiniteSevenCenteredMode n) := by
  unfold fourCellEvenFiniteSevenCenteredMode centeredPolynomialLift
  fun_prop

private theorem finiteSeven_centeredMode_even (k : ℕ) :
    Function.Even (fourCellEvenFiniteSevenCenteredMode (2 * k)) := by
  intro x
  rw [finiteSeven_centeredMode_eq_centeredLegendre,
    finiteSeven_centeredMode_eq_centeredLegendre]
  exact even_eval_centeredShiftedLegendreReal k x

private theorem finiteSeven_centeredMode_sq_integral (n : ℕ) :
    (∫ x : ℝ in -1..1, fourCellEvenFiniteSevenCenteredMode n x ^ 2) =
      2 / (2 * (n : ℝ) + 1) := by
  have h := centeredLegendreL2Diagonal_closed n
  unfold centeredLegendreL2Diagonal centeredPolynomialPair at h
  simpa only [finiteSeven_centeredMode_eq_centeredLegendre, pow_two] using h

private theorem finiteSeven_centeredMode_sq_integral_zero_one_le_one
    (k : ℕ) :
    (∫ x : ℝ in 0..1,
      fourCellEvenFiniteSevenCenteredMode (2 * k) x ^ 2) ≤ 1 := by
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ fourCellEvenFiniteSevenCenteredMode (2 * k) x ^ 2)
    ((finiteSeven_centeredMode_continuous (2 * k)).pow 2
      |>.intervalIntegrable (-1) 1)
    (by
      intro x
      change fourCellEvenFiniteSevenCenteredMode (2 * k) (-x) ^ 2 =
        fourCellEvenFiniteSevenCenteredMode (2 * k) x ^ 2
      rw [finiteSeven_centeredMode_even k x])
  have hfull := finiteSeven_centeredMode_sq_integral (2 * k)
  have hden : (1 : ℝ) ≤ 2 * ((2 * k : ℕ) : ℝ) + 1 := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hfullLe :
      (∫ x : ℝ in -1..1,
        fourCellEvenFiniteSevenCenteredMode (2 * k) x ^ 2) ≤ 2 := by
    rw [hfull]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((2 * k : ℕ) : ℝ) + 1)]
    nlinarith
  nlinarith

private theorem finiteSeven_coshCoordinate_zero_one_le :
    (1 : ℝ) ≤ fourCellEvenFiniteSevenCoshCoordinate 0 := by
  unfold fourCellEvenFiniteSevenCoshCoordinate fourCellPositiveCoshMoment
  simp_rw [finiteSeven_centeredMode_eq_centeredLegendre,
    eval_centeredShiftedLegendreReal_zero, mul_one]
  calc
    (1 : ℝ) = ∫ _x : ℝ in 0..1, (1 : ℝ) := by norm_num
    _ ≤ ∫ x : ℝ in 0..1,
        Real.cosh ((fourCellOperatorHalfWidth / 2) * x) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (Continuous.intervalIntegrable continuous_const 0 1)
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
      intro x _hx
      exact Real.one_le_cosh _

private theorem finiteSeven_cosh_sq_integral_le :
    (∫ x : ℝ in 0..1,
      Real.cosh ((fourCellOperatorHalfWidth / 2) * x) ^ 2) ≤
        (16 / 9 : ℝ) := by
  have hlog : Real.log 2 < (1 : ℝ) :=
    strict_log_two_bounds.2.trans (by norm_num)
  calc
    _ ≤ ∫ _x : ℝ in 0..1, (16 / 9 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
        (Continuous.intervalIntegrable continuous_const 0 1)
      intro x hx
      have hu0 : 0 ≤ (fourCellOperatorHalfWidth / 2) * x := by
        exact mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) hx.1
      have hu : (fourCellOperatorHalfWidth / 2) * x < (7 / 10 : ℝ) := by
        unfold fourCellOperatorHalfWidth
        norm_num at hx ⊢
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      have hc := finiteSeven_cosh_lt_four_thirds hu0 hu
      have hc0 := Real.cosh_pos ((fourCellOperatorHalfWidth / 2) * x)
      nlinarith
    _ = (16 / 9 : ℝ) := by norm_num

private theorem finiteSeven_coshCoordinate_evenMode_sq_lt_two (k : ℕ) :
    fourCellEvenFiniteSevenCoshCoordinate (2 * k) ^ 2 < 2 := by
  let f : ℝ → ℝ := fun x ↦
    Real.cosh ((fourCellOperatorHalfWidth / 2) * x)
  let g : ℝ → ℝ := fourCellEvenFiniteSevenCenteredMode (2 * k)
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hg : Continuous g := finiteSeven_centeredMode_continuous (2 * k)
  have habs :
      |∫ x : ℝ in 0..1, f x * g x| ≤
        ∫ x : ℝ in 0..1, |f x * g x| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have hyoung :
      (∫ x : ℝ in 0..1, |f x * g x|) ≤
        ∫ x : ℝ in 0..1, (f x ^ 2 + g x ^ 2) / 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((hf.mul hg).abs.intervalIntegrable 0 1)
      (((hf.pow 2).add (hg.pow 2)).div_const 2 |>.intervalIntegrable 0 1)
    intro x _hx
    change |f x * g x| ≤ (f x ^ 2 + g x ^ 2) / 2
    rw [abs_mul]
    nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]
  have hsplit :
      (∫ x : ℝ in 0..1, (f x ^ 2 + g x ^ 2) / 2) =
        ((∫ x : ℝ in 0..1, f x ^ 2) +
          (∫ x : ℝ in 0..1, g x ^ 2)) / 2 := by
    rw [show (fun x : ℝ ↦ (f x ^ 2 + g x ^ 2) / 2) =
        fun x ↦ (1 / 2 : ℝ) * (f x ^ 2 + g x ^ 2) by
      funext x
      ring,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add
        ((hf.pow 2).intervalIntegrable 0 1)
        ((hg.pow 2).intervalIntegrable 0 1)]
    ring
  have hfSq : (∫ x : ℝ in 0..1, f x ^ 2) ≤ (16 / 9 : ℝ) := by
    simpa only [f] using finiteSeven_cosh_sq_integral_le
  have hgSq : (∫ x : ℝ in 0..1, g x ^ 2) ≤ 1 := by
    simpa only [g] using
      finiteSeven_centeredMode_sq_integral_zero_one_le_one k
  have hcoordAbs :
      |fourCellEvenFiniteSevenCoshCoordinate (2 * k)| ≤ (25 / 18 : ℝ) := by
    unfold fourCellEvenFiniteSevenCoshCoordinate fourCellPositiveCoshMoment
    change |∫ x : ℝ in 0..1, f x * g x| ≤ _
    calc
      _ ≤ ∫ x : ℝ in 0..1, |f x * g x| := habs
      _ ≤ ∫ x : ℝ in 0..1, (f x ^ 2 + g x ^ 2) / 2 := hyoung
      _ = ((∫ x : ℝ in 0..1, f x ^ 2) +
          (∫ x : ℝ in 0..1, g x ^ 2)) / 2 := hsplit
      _ ≤ (25 / 18 : ℝ) := by nlinarith
  have hsq := pow_le_pow_left₀
    (abs_nonneg (fourCellEvenFiniteSevenCoshCoordinate (2 * k)))
    hcoordAbs 2
  rw [sq_abs] at hsq
  norm_num at hsq ⊢
  linarith

private theorem finiteSeven_cosh_le_fortyOne_fortieths
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (7 / 32 : ℝ)) :
    Real.cosh u ≤ (41 / 40 : ℝ) := by
  have huSqRaw : u ^ 2 ≤ (7 / 32 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hu0 hu 2
  have hv0 : 0 ≤ u ^ 2 / 2 := by positivity
  have hv : u ^ 2 / 2 ≤ (49 / 2048 : ℝ) := by
    norm_num at huSqRaw ⊢
    linarith
  have hv1 : u ^ 2 / 2 < 1 := hv.trans_lt (by norm_num)
  have hexp : Real.exp (u ^ 2 / 2) ≤ 1 / (1 - u ^ 2 / 2) :=
    Real.exp_bound_div_one_sub_of_interval hv0 hv1
  have hfrac : 1 / (1 - u ^ 2 / 2) ≤ (41 / 40 : ℝ) := by
    rw [div_le_iff₀ (sub_pos.mpr hv1)]
    nlinarith
  exact (Real.cosh_le_exp_half_sq u).trans (hexp.trans hfrac)

private theorem finiteSeven_centeredNonconstantEvenMode_integral_zero_one
    (k : ℕ) :
    (∫ x : ℝ in 0..1,
      fourCellEvenFiniteSevenCenteredMode (2 * (k + 1)) x) = 0 := by
  let n : ℕ := 2 * (k + 1)
  have hn0 : n ≠ 0 := by
    dsimp only [n]
    omega
  have hgram := centeredLegendreL2Gram n 0
  rw [if_neg hn0] at hgram
  unfold centeredPolynomialPair at hgram
  simp only [eval_centeredShiftedLegendreReal_zero, mul_one] at hgram
  have hfull :
      (∫ x : ℝ in -1..1,
        fourCellEvenFiniteSevenCenteredMode n x) = 0 := by
    simpa only [finiteSeven_centeredMode_eq_centeredLegendre] using hgram
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fourCellEvenFiniteSevenCenteredMode n)
    ((finiteSeven_centeredMode_continuous n).intervalIntegrable (-1) 1)
    (by
      dsimp only [n]
      exact finiteSeven_centeredMode_even (k + 1))
  dsimp only [n] at hfull hfold ⊢
  linarith

private theorem finiteSeven_centeredEvenMode_abs_integral_zero_one_le_one
    (k : ℕ) :
    (∫ x : ℝ in 0..1,
      |fourCellEvenFiniteSevenCenteredMode (2 * k) x|) ≤ 1 := by
  let p : ℝ → ℝ := fourCellEvenFiniteSevenCenteredMode (2 * k)
  have hp : Continuous p := finiteSeven_centeredMode_continuous (2 * k)
  have hmono :
      (∫ x : ℝ in 0..1, |p x|) ≤
        ∫ x : ℝ in 0..1, (p x ^ 2 + 1) / 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hp.abs.intervalIntegrable 0 1)
      (((hp.pow 2).add continuous_const).div_const 2 |>.intervalIntegrable 0 1)
    intro x _hx
    change |p x| ≤ (p x ^ 2 + 1) / 2
    nlinarith [sq_nonneg (|p x| - 1), sq_abs (p x)]
  have hsplit :
      (∫ x : ℝ in 0..1, (p x ^ 2 + 1) / 2) =
        ((∫ x : ℝ in 0..1, p x ^ 2) + 1) / 2 := by
    rw [show (fun x : ℝ ↦ (p x ^ 2 + 1) / 2) =
        fun x ↦ (1 / 2 : ℝ) * (p x ^ 2 + 1) by
      funext x
      ring,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add
        ((hp.pow 2).intervalIntegrable 0 1)
        (Continuous.intervalIntegrable continuous_const 0 1)]
    norm_num
    ring
  have hpSq : (∫ x : ℝ in 0..1, p x ^ 2) ≤ 1 := by
    simpa only [p] using
      finiteSeven_centeredMode_sq_integral_zero_one_le_one k
  calc
    _ ≤ ∫ x : ℝ in 0..1, (p x ^ 2 + 1) / 2 := hmono
    _ = ((∫ x : ℝ in 0..1, p x ^ 2) + 1) / 2 := hsplit
    _ ≤ 1 := by linarith

private theorem finiteSeven_nonconstantEven_coshCoordinate_abs_le
    (k : ℕ) :
    |fourCellEvenFiniteSevenCoshCoordinate (2 * (k + 1))| ≤
      (1 / 40 : ℝ) := by
  let p : ℝ → ℝ := fourCellEvenFiniteSevenCenteredMode (2 * (k + 1))
  let q : ℝ → ℝ := fun x ↦
    Real.cosh ((fourCellOperatorHalfWidth / 2) * x) - 1
  have hp : Continuous p := finiteSeven_centeredMode_continuous (2 * (k + 1))
  have hq : Continuous q := by
    dsimp only [q]
    fun_prop
  have hmean : (∫ x : ℝ in 0..1, p x) = 0 := by
    simpa only [p] using
      finiteSeven_centeredNonconstantEvenMode_integral_zero_one k
  have hrewrite :
      fourCellEvenFiniteSevenCoshCoordinate (2 * (k + 1)) =
        ∫ x : ℝ in 0..1, q x * p x := by
    unfold fourCellEvenFiniteSevenCoshCoordinate fourCellPositiveCoshMoment
    change (∫ x : ℝ in 0..1,
      Real.cosh ((fourCellOperatorHalfWidth / 2) * x) * p x) = _
    rw [show (fun x : ℝ ↦
        Real.cosh ((fourCellOperatorHalfWidth / 2) * x) * p x) =
      fun x ↦ q x * p x + p x by
        funext x
        dsimp only [q]
        ring]
    change (∫ x : ℝ in 0..1, ((q * p) + p) x) = _
    calc
      _ = (∫ x : ℝ in 0..1, (q * p) x) +
          ∫ x : ℝ in 0..1, p x :=
        intervalIntegral.integral_add
          ((hq.mul hp).intervalIntegrable 0 1)
          (hp.intervalIntegrable 0 1)
      _ = ∫ x : ℝ in 0..1, q x * p x := by
        rw [hmean, add_zero]
        apply intervalIntegral.integral_congr
        intro x _hx
        rfl
  have habs :
      |∫ x : ℝ in 0..1, q x * p x| ≤
        ∫ x : ℝ in 0..1, |q x * p x| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have hmono :
      (∫ x : ℝ in 0..1, |q x * p x|) ≤
        (1 / 40 : ℝ) * (∫ x : ℝ in 0..1, |p x|) := by
    calc
      _ ≤ ∫ x : ℝ in 0..1, (1 / 40 : ℝ) * |p x| := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          ((hq.mul hp).abs.intervalIntegrable 0 1)
          ((hp.abs.const_mul (1 / 40 : ℝ)).intervalIntegrable 0 1)
        intro x hx
        have hu0 : 0 ≤ (fourCellOperatorHalfWidth / 2) * x :=
          mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) hx.1
        have hu : (fourCellOperatorHalfWidth / 2) * x ≤ (7 / 32 : ℝ) := by
          have hlog := strict_log_two_bounds.2.le
          unfold fourCellOperatorHalfWidth
          norm_num at hx ⊢
          nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
        have hcosh := finiteSeven_cosh_le_fortyOne_fortieths hu0 hu
        have hq0 : 0 ≤ q x := by
          dsimp only [q]
          exact sub_nonneg.mpr (Real.one_le_cosh _)
        have hq1 : q x ≤ (1 / 40 : ℝ) := by
          dsimp only [q]
          linarith
        change |q x * p x| ≤ (1 / 40 : ℝ) * |p x|
        rw [abs_mul, abs_of_nonneg hq0]
        exact mul_le_mul_of_nonneg_right hq1 (abs_nonneg (p x))
      _ = (1 / 40 : ℝ) * (∫ x : ℝ in 0..1, |p x|) := by
        rw [intervalIntegral.integral_const_mul]
  have hpAbs : (∫ x : ℝ in 0..1, |p x|) ≤ 1 := by
    simpa only [p] using
      finiteSeven_centeredEvenMode_abs_integral_zero_one_le_one (k + 1)
  rw [hrewrite]
  have hscaled := mul_le_mul_of_nonneg_left hpAbs
    (by norm_num : (0 : ℝ) ≤ 1 / 40)
  simpa only [mul_one] using habs.trans (hmono.trans hscaled)

private theorem finiteSeven_nonconstantEven_coshQuotient_sq_le (k : ℕ) :
    (fourCellEvenFiniteSevenCoshCoordinate (2 * (k + 1)) /
        fourCellEvenFiniteSevenCoshCoordinate 0) ^ 2 ≤
      (1 / 1600 : ℝ) := by
  have hnumAbs := finiteSeven_nonconstantEven_coshCoordinate_abs_le k
  have hnumSq := pow_le_pow_left₀
    (abs_nonneg (fourCellEvenFiniteSevenCoshCoordinate (2 * (k + 1))))
    hnumAbs 2
  rw [sq_abs] at hnumSq
  have hden := finiteSeven_coshCoordinate_zero_one_le
  have hdenPos : 0 < fourCellEvenFiniteSevenCoshCoordinate 0 :=
    lt_of_lt_of_le (by norm_num) hden
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos hdenPos)]
  have hdenSq : (1 : ℝ) ≤
      fourCellEvenFiniteSevenCoshCoordinate 0 ^ 2 := by
    nlinarith [sq_nonneg (fourCellEvenFiniteSevenCoshCoordinate 0 - 1)]
  norm_num at hnumSq ⊢
  nlinarith

private theorem finiteSeven_nonconstantQuotientMode_sq_integral_lt_one
    (k : ℕ) :
    (∫ x : ℝ in -1..1,
      fourCellEvenFiniteSevenQuotientMode (2 * (k + 1)) x ^ 2) < 1 := by
  let c : ℝ := fourCellEvenFiniteSevenCoshCoordinate (2 * (k + 1)) /
    fourCellEvenFiniteSevenCoshCoordinate 0
  let p : ℝ → ℝ := fourCellEvenFiniteSevenCenteredMode (2 * (k + 1))
  let p₀ : ℝ → ℝ := fourCellEvenFiniteSevenCenteredMode 0
  let q : ℝ → ℝ := fourCellEvenFiniteSevenQuotientMode (2 * (k + 1))
  have hp : Continuous p := finiteSeven_centeredMode_continuous (2 * (k + 1))
  have hp₀ : Continuous p₀ := finiteSeven_centeredMode_continuous 0
  have hq : Continuous q := by
    dsimp only [q]
    unfold fourCellEvenFiniteSevenQuotientMode
    exact hp.sub (continuous_const.mul hp₀)
  have hmono :
      (∫ x : ℝ in -1..1, q x ^ 2) ≤
        ∫ x : ℝ in -1..1, 2 * p x ^ 2 + 2 * c ^ 2 * p₀ x ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((hq.pow 2).intervalIntegrable (-1) 1)
      (((hp.pow 2).const_mul 2).add
        ((hp₀.pow 2).const_mul (2 * c ^ 2)) |>.intervalIntegrable (-1) 1)
    intro x _hx
    change q x ^ 2 ≤ 2 * p x ^ 2 + 2 * c ^ 2 * p₀ x ^ 2
    dsimp only [q, p, p₀, c]
    unfold fourCellEvenFiniteSevenQuotientMode
    nlinarith [sq_nonneg
      (fourCellEvenFiniteSevenCenteredMode (2 * (k + 1)) x +
        (fourCellEvenFiniteSevenCoshCoordinate (2 * (k + 1)) /
          fourCellEvenFiniteSevenCoshCoordinate 0) *
            fourCellEvenFiniteSevenCenteredMode 0 x)]
  have hsplit :
      (∫ x : ℝ in -1..1, 2 * p x ^ 2 + 2 * c ^ 2 * p₀ x ^ 2) =
        2 * (∫ x : ℝ in -1..1, p x ^ 2) +
          2 * c ^ 2 * (∫ x : ℝ in -1..1, p₀ x ^ 2) := by
    rw [intervalIntegral.integral_add
        ((hp.pow 2).const_mul 2 |>.intervalIntegrable (-1) 1)
        ((hp₀.pow 2).const_mul (2 * c ^ 2) |>.intervalIntegrable (-1) 1),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hpSq : (∫ x : ℝ in -1..1, p x ^ 2) ≤ (2 / 5 : ℝ) := by
    dsimp only [p]
    rw [finiteSeven_centeredMode_sq_integral]
    have hk : (5 : ℝ) ≤ 2 * ((2 * (k + 1) : ℕ) : ℝ) + 1 := by
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    rw [div_le_iff₀ (by positivity :
      (0 : ℝ) < 2 * ((2 * (k + 1) : ℕ) : ℝ) + 1)]
    nlinarith
  have hp₀Sq : (∫ x : ℝ in -1..1, p₀ x ^ 2) = 2 := by
    dsimp only [p₀]
    simpa using finiteSeven_centeredMode_sq_integral 0
  have hcSq : c ^ 2 ≤ (1 / 1600 : ℝ) := by
    simpa only [c] using finiteSeven_nonconstantEven_coshQuotient_sq_le k
  calc
    _ ≤ ∫ x : ℝ in -1..1, 2 * p x ^ 2 + 2 * c ^ 2 * p₀ x ^ 2 :=
      hmono
    _ = 2 * (∫ x : ℝ in -1..1, p x ^ 2) +
        2 * c ^ 2 * (∫ x : ℝ in -1..1, p₀ x ^ 2) := hsplit
    _ < 1 := by nlinarith [sq_nonneg c]

private theorem finiteSeven_coshQuotient_evenMode_sq_lt_two (k : ℕ) :
    (fourCellEvenFiniteSevenCoshCoordinate (2 * k) /
        fourCellEvenFiniteSevenCoshCoordinate 0) ^ 2 < 2 := by
  have hnum := finiteSeven_coshCoordinate_evenMode_sq_lt_two k
  have hden := finiteSeven_coshCoordinate_zero_one_le
  have hdenPos : 0 < fourCellEvenFiniteSevenCoshCoordinate 0 :=
    lt_of_lt_of_le (by norm_num) hden
  rw [div_pow, div_lt_iff₀ (sq_pos_of_pos hdenPos)]
  nlinarith [sq_nonneg (fourCellEvenFiniteSevenCoshCoordinate 0 - 1)]

private theorem finiteSeven_quotientMode_continuous (n : ℕ) :
    Continuous (fourCellEvenFiniteSevenQuotientMode n) := by
  unfold fourCellEvenFiniteSevenQuotientMode
  exact (finiteSeven_centeredMode_continuous n).sub
    (continuous_const.mul (finiteSeven_centeredMode_continuous 0))

private theorem finiteSeven_quotientMode_sq_integral_lt_twelve (k : ℕ) :
    (∫ x : ℝ in -1..1,
      fourCellEvenFiniteSevenQuotientMode (2 * k) x ^ 2) < 12 := by
  let c : ℝ := fourCellEvenFiniteSevenCoshCoordinate (2 * k) /
    fourCellEvenFiniteSevenCoshCoordinate 0
  let p : ℝ → ℝ := fourCellEvenFiniteSevenCenteredMode (2 * k)
  let p₀ : ℝ → ℝ := fourCellEvenFiniteSevenCenteredMode 0
  have hp : Continuous p := finiteSeven_centeredMode_continuous (2 * k)
  have hp₀ : Continuous p₀ := finiteSeven_centeredMode_continuous 0
  have hq : Continuous (fourCellEvenFiniteSevenQuotientMode (2 * k)) :=
    finiteSeven_quotientMode_continuous (2 * k)
  have hpoint (x : ℝ) :
      fourCellEvenFiniteSevenQuotientMode (2 * k) x ^ 2 ≤
        2 * p x ^ 2 + 2 * c ^ 2 * p₀ x ^ 2 := by
    unfold fourCellEvenFiniteSevenQuotientMode
    dsimp only [c, p, p₀]
    nlinarith [sq_nonneg
      (fourCellEvenFiniteSevenCenteredMode (2 * k) x +
        (fourCellEvenFiniteSevenCoshCoordinate (2 * k) /
          fourCellEvenFiniteSevenCoshCoordinate 0) *
            fourCellEvenFiniteSevenCenteredMode 0 x)]
  have hmono :
      (∫ x : ℝ in -1..1,
        fourCellEvenFiniteSevenQuotientMode (2 * k) x ^ 2) ≤
      ∫ x : ℝ in -1..1, 2 * p x ^ 2 + 2 * c ^ 2 * p₀ x ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((hq.pow 2).intervalIntegrable (-1) 1)
      (((hp.pow 2).const_mul 2).add
        ((hp₀.pow 2).const_mul (2 * c ^ 2)) |>.intervalIntegrable (-1) 1)
    intro x _hx
    exact hpoint x
  have hsplit :
      (∫ x : ℝ in -1..1, 2 * p x ^ 2 + 2 * c ^ 2 * p₀ x ^ 2) =
        2 * (∫ x : ℝ in -1..1, p x ^ 2) +
          2 * c ^ 2 * (∫ x : ℝ in -1..1, p₀ x ^ 2) := by
    rw [intervalIntegral.integral_add
        ((hp.pow 2).const_mul 2 |>.intervalIntegrable (-1) 1)
        ((hp₀.pow 2).const_mul (2 * c ^ 2) |>.intervalIntegrable (-1) 1),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hpSq : (∫ x : ℝ in -1..1, p x ^ 2) ≤ 2 := by
    dsimp only [p]
    rw [finiteSeven_centeredMode_sq_integral]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((2 * k : ℕ) : ℝ) + 1)]
    nlinarith
  have hp₀Sq : (∫ x : ℝ in -1..1, p₀ x ^ 2) = 2 := by
    dsimp only [p₀]
    simpa using finiteSeven_centeredMode_sq_integral 0
  have hcSq : c ^ 2 < 2 := by
    simpa only [c] using finiteSeven_coshQuotient_evenMode_sq_lt_two k
  calc
    _ ≤ ∫ x : ℝ in -1..1,
        2 * p x ^ 2 + 2 * c ^ 2 * p₀ x ^ 2 := hmono
    _ = 2 * (∫ x : ℝ in -1..1, p x ^ 2) +
        2 * c ^ 2 * (∫ x : ℝ in -1..1, p₀ x ^ 2) := hsplit
    _ < 12 := by nlinarith [sq_nonneg c]

private theorem finiteSeven_quotientMode_abs_integral_lt_five (k : ℕ) :
    (∫ x : ℝ in -1..1,
      |fourCellEvenFiniteSevenQuotientMode (2 * k) x|) < 5 := by
  let q : ℝ → ℝ := fourCellEvenFiniteSevenQuotientMode (2 * k)
  have hq : Continuous q := finiteSeven_quotientMode_continuous (2 * k)
  have hpoint (x : ℝ) : |q x| ≤ q x ^ 2 / 6 + (3 / 2 : ℝ) := by
    nlinarith [sq_nonneg (|q x| - 3), sq_abs (q x)]
  have hmono :
      (∫ x : ℝ in -1..1, |q x|) ≤
        ∫ x : ℝ in -1..1, q x ^ 2 / 6 + (3 / 2 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hq.abs.intervalIntegrable (-1) 1)
      (((hq.pow 2).div_const 6).add continuous_const
        |>.intervalIntegrable (-1) 1)
    intro x _hx
    exact hpoint x
  have hsplit :
      (∫ x : ℝ in -1..1, q x ^ 2 / 6 + (3 / 2 : ℝ)) =
        (1 / 6 : ℝ) * (∫ x : ℝ in -1..1, q x ^ 2) + 3 := by
    rw [intervalIntegral.integral_add
        ((hq.pow 2).div_const 6 |>.intervalIntegrable (-1) 1)
        (Continuous.intervalIntegrable continuous_const (-1) 1),
      show (fun x : ℝ ↦ q x ^ 2 / 6) =
        fun x ↦ (1 / 6 : ℝ) * q x ^ 2 by
        funext x
        ring,
      intervalIntegral.integral_const_mul]
    norm_num
  have hsq : (∫ x : ℝ in -1..1, q x ^ 2) < 12 := by
    simpa only [q] using finiteSeven_quotientMode_sq_integral_lt_twelve k
  calc
    _ ≤ ∫ x : ℝ in -1..1, q x ^ 2 / 6 + (3 / 2 : ℝ) := hmono
    _ = (1 / 6 : ℝ) * (∫ x : ℝ in -1..1, q x ^ 2) + 3 := hsplit
    _ < 5 := by linarith

/-! ## The genuine regular row versus its polynomial replacement -/

private theorem finiteSeven_regularKernelEnvelope_pointwise
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    0 ≤ yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
        fourCellEvenFiniteSevenRegularKernelPolynomial18
          (fourCellOperatorHalfWidth * t) ∧
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
          fourCellEvenFiniteSevenRegularKernelPolynomial18
            (fourCellOperatorHalfWidth * t) <
        (1 / 380000000000 : ℝ) := by
  apply fourCellEvenFiniteSevenRegularKernelPolynomial18_sevenEighths_envelope
  · exact mul_nonneg
      (by unfold fourCellOperatorHalfWidth; positivity) ht.1
  · have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
    have hlog := strict_log_two_bounds.2
    calc
      fourCellOperatorHalfWidth * t ≤
          fourCellOperatorHalfWidth * 2 := hmul
      _ = 5 * Real.log 2 / 4 := by
        unfold fourCellOperatorHalfWidth
        ring
      _ ≤ (7 / 8 : ℝ) := by linarith

/-- Signed error in one complete regular autocorrelation row after replacing
the Yoshida kernel by the degree-eighteen envelope center. -/
def fourCellEvenFiniteSevenRegularEnvelopeQuadratic (w : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ in 0..2,
    (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
      fourCellEvenFiniteSevenRegularKernelPolynomial18
        (fourCellOperatorHalfWidth * t)) *
      centeredEndpointCorrelation w t

private theorem finiteSeven_regularEnvelopeQuadratic_intervalIntegrable
    (w : ℝ → ℝ) (hw : Continuous w) :
    IntervalIntegrable
      (fun t : ℝ ↦
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
          fourCellEvenFiniteSevenRegularKernelPolynomial18
            (fourCellOperatorHalfWidth * t)) *
          centeredEndpointCorrelation w t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
      fourCellEvenFiniteSevenRegularKernelPolynomial18
        (fourCellOperatorHalfWidth * t)) *
      centeredEndpointCorrelation w t
  let g : ℝ → ℝ := fun t ↦
    (1 / 380000000000 : ℝ) * |centeredEndpointCorrelation w t|
  have hcorr : Continuous (centeredEndpointCorrelation w) :=
    continuous_centeredEndpointCorrelation_of_continuous w hw
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hcorr.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact ((measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)).sub
        (by
          unfold fourCellEvenFiniteSevenRegularKernelPolynomial18
            finiteSevenSechPolynomial18 finiteSevenCschRegularPolynomial17
          fun_prop)).mul hcorr.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2⟩
    have henv := finiteSeven_regularKernelEnvelope_pointwise htIcc
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg henv.1]
    exact mul_le_mul_of_nonneg_right henv.2.le
      (abs_nonneg (centeredEndpointCorrelation w t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

private theorem finiteSeven_abs_regularEnvelopeQuadratic_le_energy
    (w : ℝ → ℝ) (hw : Continuous w) :
    |fourCellEvenFiniteSevenRegularEnvelopeQuadratic w| ≤
      (1 / 380000000000 : ℝ) *
        (∫ x : ℝ in -1..1, w x ^ 2) := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
      fourCellEvenFiniteSevenRegularKernelPolynomial18
        (fourCellOperatorHalfWidth * t)) *
      centeredEndpointCorrelation w t
  let g : ℝ → ℝ := fun t ↦
    (1 / 380000000000 : ℝ) * |centeredEndpointCorrelation w t|
  have hf : IntervalIntegrable f volume 0 2 := by
    dsimp only [f]
    exact finiteSeven_regularEnvelopeQuadratic_intervalIntegrable w hw
  have hcorr : Continuous (centeredEndpointCorrelation w) :=
    continuous_centeredEndpointCorrelation_of_continuous w hw
  have hg : IntervalIntegrable g volume 0 2 := by
    dsimp only [g]
    exact (hcorr.abs.const_mul (1 / 380000000000 : ℝ))
      |>.intervalIntegrable 0 2
  have hmono :
      (∫ t : ℝ in 0..2, |f t|) ≤ ∫ t : ℝ in 0..2, g t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf.abs hg
    intro t ht
    have henv := finiteSeven_regularKernelEnvelope_pointwise ht
    dsimp only [f, g]
    rw [abs_mul, abs_of_nonneg henv.1]
    exact mul_le_mul_of_nonneg_right henv.2.le
      (abs_nonneg (centeredEndpointCorrelation w t))
  have habs :
      |fourCellEvenFiniteSevenRegularEnvelopeQuadratic w| ≤
        (1 / 380000000000 : ℝ) *
          (∫ t : ℝ in 0..2, |centeredEndpointCorrelation w t|) := by
    calc
      _ = |∫ t : ℝ in 0..2, f t| := by
        unfold fourCellEvenFiniteSevenRegularEnvelopeQuadratic
        rfl
      _ ≤ ∫ t : ℝ in 0..2, |f t| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ t : ℝ in 0..2, g t := hmono
      _ = (1 / 380000000000 : ℝ) *
          (∫ t : ℝ in 0..2, |centeredEndpointCorrelation w t|) := by
        dsimp only [g]
        rw [intervalIntegral.integral_const_mul]
  exact habs.trans <| mul_le_mul_of_nonneg_left
    (integral_abs_centeredEndpointCorrelation_le_energy w hw) (by norm_num)

/-- Polarized regular-kernel error.  This is the only analytic remainder
introduced by replacing the genuine regular row with the degree-eighteen
polynomial row. -/
def fourCellEvenFiniteSevenRegularEnvelopePolarization
    (u v : ℝ → ℝ) : ℝ :=
  (fourCellEvenFiniteSevenRegularEnvelopeQuadratic (u + v) -
      fourCellEvenFiniteSevenRegularEnvelopeQuadratic u -
      fourCellEvenFiniteSevenRegularEnvelopeQuadratic v) / 2

private theorem finiteSeven_sum_quotientMode_sq_integral_lt_fortyEight
    (k l : ℕ) :
    (∫ x : ℝ in -1..1,
      (fourCellEvenFiniteSevenQuotientMode (2 * k) x +
        fourCellEvenFiniteSevenQuotientMode (2 * l) x) ^ 2) < 48 := by
  let u : ℝ → ℝ := fourCellEvenFiniteSevenQuotientMode (2 * k)
  let v : ℝ → ℝ := fourCellEvenFiniteSevenQuotientMode (2 * l)
  have hu : Continuous u := finiteSeven_quotientMode_continuous (2 * k)
  have hv : Continuous v := finiteSeven_quotientMode_continuous (2 * l)
  have hmono :
      (∫ x : ℝ in -1..1, (u x + v x) ^ 2) ≤
        ∫ x : ℝ in -1..1, 2 * u x ^ 2 + 2 * v x ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (((hu.add hv).pow 2).intervalIntegrable (-1) 1)
      ((((hu.pow 2).const_mul 2).add ((hv.pow 2).const_mul 2))
        |>.intervalIntegrable (-1) 1)
    intro x _hx
    change (u x + v x) ^ 2 ≤ 2 * u x ^ 2 + 2 * v x ^ 2
    nlinarith [sq_nonneg (u x - v x)]
  have hsplit :
      (∫ x : ℝ in -1..1, 2 * u x ^ 2 + 2 * v x ^ 2) =
        2 * (∫ x : ℝ in -1..1, u x ^ 2) +
          2 * (∫ x : ℝ in -1..1, v x ^ 2) := by
    rw [intervalIntegral.integral_add
        ((hu.pow 2).const_mul 2 |>.intervalIntegrable (-1) 1)
        ((hv.pow 2).const_mul 2 |>.intervalIntegrable (-1) 1),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have huSq : (∫ x : ℝ in -1..1, u x ^ 2) < 12 := by
    simpa only [u] using finiteSeven_quotientMode_sq_integral_lt_twelve k
  have hvSq : (∫ x : ℝ in -1..1, v x ^ 2) < 12 := by
    simpa only [v] using finiteSeven_quotientMode_sq_integral_lt_twelve l
  calc
    _ ≤ ∫ x : ℝ in -1..1, 2 * u x ^ 2 + 2 * v x ^ 2 := hmono
    _ = 2 * (∫ x : ℝ in -1..1, u x ^ 2) +
        2 * (∫ x : ℝ in -1..1, v x ^ 2) := hsplit
    _ < 48 := by linarith

/-- Every one of the twenty-one regular-row quotient entries changes by
less than `10⁻¹⁰` when the genuine kernel is replaced by the checked
degree-eighteen polynomial.  The indices are all even and the proof is
uniform in them; no finite mode enumeration occurs. -/
theorem abs_fourCellEvenFiniteSevenRegularEnvelopePolarization_lt
    (k l : ℕ) :
    |fourCellEvenFiniteSevenRegularEnvelopePolarization
      (fourCellEvenFiniteSevenQuotientMode (2 * k))
      (fourCellEvenFiniteSevenQuotientMode (2 * l))| <
        (1 / 10000000000 : ℝ) := by
  let u : ℝ → ℝ := fourCellEvenFiniteSevenQuotientMode (2 * k)
  let v : ℝ → ℝ := fourCellEvenFiniteSevenQuotientMode (2 * l)
  let A : ℝ := fourCellEvenFiniteSevenRegularEnvelopeQuadratic (u + v)
  let B : ℝ := fourCellEvenFiniteSevenRegularEnvelopeQuadratic u
  let C : ℝ := fourCellEvenFiniteSevenRegularEnvelopeQuadratic v
  have hu : Continuous u := finiteSeven_quotientMode_continuous (2 * k)
  have hv : Continuous v := finiteSeven_quotientMode_continuous (2 * l)
  have hAraw := finiteSeven_abs_regularEnvelopeQuadratic_le_energy
    (u + v) (hu.add hv)
  have hBraw := finiteSeven_abs_regularEnvelopeQuadratic_le_energy u hu
  have hCraw := finiteSeven_abs_regularEnvelopeQuadratic_le_energy v hv
  have hsumEnergy :
      (∫ x : ℝ in -1..1, (u x + v x) ^ 2) < 48 := by
    simpa only [u, v] using
      finiteSeven_sum_quotientMode_sq_integral_lt_fortyEight k l
  have huEnergy : (∫ x : ℝ in -1..1, u x ^ 2) < 12 := by
    simpa only [u] using finiteSeven_quotientMode_sq_integral_lt_twelve k
  have hvEnergy : (∫ x : ℝ in -1..1, v x ^ 2) < 12 := by
    simpa only [v] using finiteSeven_quotientMode_sq_integral_lt_twelve l
  have hdelta : (0 : ℝ) < 1 / 380000000000 := by norm_num
  have hA : |A| < (48 / 380000000000 : ℝ) := by
    calc
      |A| ≤ (1 / 380000000000 : ℝ) *
          (∫ x : ℝ in -1..1, (u + v) x ^ 2) := by
        simpa only [A] using hAraw
      _ < (1 / 380000000000 : ℝ) * 48 :=
        mul_lt_mul_of_pos_left hsumEnergy hdelta
      _ = (48 / 380000000000 : ℝ) := by ring
  have hB : |B| < (12 / 380000000000 : ℝ) := by
    calc
      |B| ≤ (1 / 380000000000 : ℝ) *
          (∫ x : ℝ in -1..1, u x ^ 2) := by
        simpa only [B] using hBraw
      _ < (1 / 380000000000 : ℝ) * 12 :=
        mul_lt_mul_of_pos_left huEnergy hdelta
      _ = (12 / 380000000000 : ℝ) := by ring
  have hC : |C| < (12 / 380000000000 : ℝ) := by
    calc
      |C| ≤ (1 / 380000000000 : ℝ) *
          (∫ x : ℝ in -1..1, v x ^ 2) := by
        simpa only [C] using hCraw
      _ < (1 / 380000000000 : ℝ) * 12 :=
        mul_lt_mul_of_pos_left hvEnergy hdelta
      _ = (12 / 380000000000 : ℝ) := by ring
  have habc : |A - B - C| ≤ |A| + |B| + |C| := by
    calc
      |A - B - C| ≤ |A - B| + |C| := abs_sub _ _
      _ ≤ (|A| + |B|) + |C| := by
        linarith [abs_sub A B]
  have htotal : |A - B - C| < (72 / 380000000000 : ℝ) := by
    exact habc.trans_lt (by linarith)
  change |(A - B - C) / 2| < _
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num at htotal ⊢
  linarith

private theorem finiteSeven_sum_nonconstantQuotientMode_sq_integral_lt_four
    (k l : ℕ) :
    (∫ x : ℝ in -1..1,
      (fourCellEvenFiniteSevenQuotientMode (2 * (k + 1)) x +
        fourCellEvenFiniteSevenQuotientMode (2 * (l + 1)) x) ^ 2) < 4 := by
  let u : ℝ → ℝ := fourCellEvenFiniteSevenQuotientMode (2 * (k + 1))
  let v : ℝ → ℝ := fourCellEvenFiniteSevenQuotientMode (2 * (l + 1))
  have hu : Continuous u := finiteSeven_quotientMode_continuous (2 * (k + 1))
  have hv : Continuous v := finiteSeven_quotientMode_continuous (2 * (l + 1))
  have hmono :
      (∫ x : ℝ in -1..1, (u x + v x) ^ 2) ≤
        ∫ x : ℝ in -1..1, 2 * u x ^ 2 + 2 * v x ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (((hu.add hv).pow 2).intervalIntegrable (-1) 1)
      ((((hu.pow 2).const_mul 2).add ((hv.pow 2).const_mul 2))
        |>.intervalIntegrable (-1) 1)
    intro x _hx
    change (u x + v x) ^ 2 ≤ 2 * u x ^ 2 + 2 * v x ^ 2
    nlinarith [sq_nonneg (u x - v x)]
  have hsplit :
      (∫ x : ℝ in -1..1, 2 * u x ^ 2 + 2 * v x ^ 2) =
        2 * (∫ x : ℝ in -1..1, u x ^ 2) +
          2 * (∫ x : ℝ in -1..1, v x ^ 2) := by
    rw [intervalIntegral.integral_add
        ((hu.pow 2).const_mul 2 |>.intervalIntegrable (-1) 1)
        ((hv.pow 2).const_mul 2 |>.intervalIntegrable (-1) 1),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have huSq : (∫ x : ℝ in -1..1, u x ^ 2) < 1 := by
    simpa only [u] using
      finiteSeven_nonconstantQuotientMode_sq_integral_lt_one k
  have hvSq : (∫ x : ℝ in -1..1, v x ^ 2) < 1 := by
    simpa only [v] using
      finiteSeven_nonconstantQuotientMode_sq_integral_lt_one l
  calc
    _ ≤ ∫ x : ℝ in -1..1, 2 * u x ^ 2 + 2 * v x ^ 2 := hmono
    _ = 2 * (∫ x : ℝ in -1..1, u x ^ 2) +
        2 * (∫ x : ℝ in -1..1, v x ^ 2) := hsplit
    _ < 4 := by linarith

/-- On the six actual nonconstant coordinates, constant-mode cancellation
sharpens the regular-row replacement error by a further factor ten. -/
theorem abs_fourCellEvenFiniteSevenRegularEnvelopePolarization_nonconstant_lt
    (k l : ℕ) :
    |fourCellEvenFiniteSevenRegularEnvelopePolarization
      (fourCellEvenFiniteSevenQuotientMode (2 * (k + 1)))
      (fourCellEvenFiniteSevenQuotientMode (2 * (l + 1)))| <
        (1 / 100000000000 : ℝ) := by
  let u : ℝ → ℝ := fourCellEvenFiniteSevenQuotientMode (2 * (k + 1))
  let v : ℝ → ℝ := fourCellEvenFiniteSevenQuotientMode (2 * (l + 1))
  let A : ℝ := fourCellEvenFiniteSevenRegularEnvelopeQuadratic (u + v)
  let B : ℝ := fourCellEvenFiniteSevenRegularEnvelopeQuadratic u
  let C : ℝ := fourCellEvenFiniteSevenRegularEnvelopeQuadratic v
  have hu : Continuous u := finiteSeven_quotientMode_continuous (2 * (k + 1))
  have hv : Continuous v := finiteSeven_quotientMode_continuous (2 * (l + 1))
  have hAraw := finiteSeven_abs_regularEnvelopeQuadratic_le_energy
    (u + v) (hu.add hv)
  have hBraw := finiteSeven_abs_regularEnvelopeQuadratic_le_energy u hu
  have hCraw := finiteSeven_abs_regularEnvelopeQuadratic_le_energy v hv
  have hsumEnergy :
      (∫ x : ℝ in -1..1, (u x + v x) ^ 2) < 4 := by
    simpa only [u, v] using
      finiteSeven_sum_nonconstantQuotientMode_sq_integral_lt_four k l
  have huEnergy : (∫ x : ℝ in -1..1, u x ^ 2) < 1 := by
    simpa only [u] using
      finiteSeven_nonconstantQuotientMode_sq_integral_lt_one k
  have hvEnergy : (∫ x : ℝ in -1..1, v x ^ 2) < 1 := by
    simpa only [v] using
      finiteSeven_nonconstantQuotientMode_sq_integral_lt_one l
  have hdelta : (0 : ℝ) < 1 / 380000000000 := by norm_num
  have hA : |A| < (4 / 380000000000 : ℝ) := by
    calc
      |A| ≤ (1 / 380000000000 : ℝ) *
          (∫ x : ℝ in -1..1, (u + v) x ^ 2) := by
        simpa only [A] using hAraw
      _ < (1 / 380000000000 : ℝ) * 4 :=
        mul_lt_mul_of_pos_left hsumEnergy hdelta
      _ = (4 / 380000000000 : ℝ) := by ring
  have hB : |B| < (1 / 380000000000 : ℝ) := by
    calc
      |B| ≤ (1 / 380000000000 : ℝ) *
          (∫ x : ℝ in -1..1, u x ^ 2) := by
        simpa only [B] using hBraw
      _ < (1 / 380000000000 : ℝ) * 1 :=
        mul_lt_mul_of_pos_left huEnergy hdelta
      _ = (1 / 380000000000 : ℝ) := by ring
  have hC : |C| < (1 / 380000000000 : ℝ) := by
    calc
      |C| ≤ (1 / 380000000000 : ℝ) *
          (∫ x : ℝ in -1..1, v x ^ 2) := by
        simpa only [C] using hCraw
      _ < (1 / 380000000000 : ℝ) * 1 :=
        mul_lt_mul_of_pos_left hvEnergy hdelta
      _ = (1 / 380000000000 : ℝ) := by ring
  have habc : |A - B - C| ≤ |A| + |B| + |C| := by
    calc
      |A - B - C| ≤ |A - B| + |C| := abs_sub _ _
      _ ≤ (|A| + |B|) + |C| := by linarith [abs_sub A B]
  have htotal : |A - B - C| < (6 / 380000000000 : ℝ) :=
    habc.trans_lt (by linarith)
  change |(A - B - C) / 2| < _
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num at htotal ⊢
  linarith

/-! ## Lossless transport into the true bordered entries -/

/-- The polar-free quadratic with only the regular Yoshida kernel replaced
by its degree-eighteen polynomial center.  All singular, endpoint-potential,
scalar, and retained-prime terms remain exact. -/
def fourCellEvenFiniteSevenPolynomialPolarFreeOperator (w : ℝ → ℝ) : ℝ :=
  fourCellEvenZeroCoshCoupledCore w -
    (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in -1..1, w x ^ 2) -
    2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        fourCellEvenFiniteSevenRegularKernelPolynomial18
            (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation w t)

/-- Polarization of the kernel-polynomial polar-free quadratic. -/
def fourCellEvenFiniteSevenPolynomialPolarFreePolarization
    (u v : ℝ → ℝ) : ℝ :=
  (fourCellEvenFiniteSevenPolynomialPolarFreeOperator (u + v) -
      fourCellEvenFiniteSevenPolynomialPolarFreeOperator u -
      fourCellEvenFiniteSevenPolynomialPolarFreeOperator v) / 2

private theorem finiteSeven_regularKernelIntegral_eq_polynomial_add_envelope
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation w t) =
      (∫ t : ℝ in 0..2,
        fourCellEvenFiniteSevenRegularKernelPolynomial18
            (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation w t) +
        fourCellEvenFiniteSevenRegularEnvelopeQuadratic w := by
  have hcorr : Continuous (centeredEndpointCorrelation w) :=
    continuous_centeredEndpointCorrelation_of_continuous w hw
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦
        fourCellEvenFiniteSevenRegularKernelPolynomial18
            (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation w t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    unfold fourCellEvenFiniteSevenRegularKernelPolynomial18
      finiteSevenSechPolynomial18 finiteSevenCschRegularPolynomial17
    fun_prop
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation w t) = fun t ↦
      fourCellEvenFiniteSevenRegularKernelPolynomial18
          (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation w t +
      (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) -
        fourCellEvenFiniteSevenRegularKernelPolynomial18
          (fourCellOperatorHalfWidth * t)) *
        centeredEndpointCorrelation w t by
      funext t
      ring,
    intervalIntegral.integral_add hpoly
      (finiteSeven_regularEnvelopeQuadratic_intervalIntegrable w hw)]
  rfl

private theorem finiteSeven_polarFreeOperator_eq_polynomial_sub_envelope
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w) :
    fourCellEvenPolarFreeOperator w =
      fourCellEvenFiniteSevenPolynomialPolarFreeOperator w -
        2 * fourCellOperatorHalfWidth *
          fourCellEvenFiniteSevenRegularEnvelopeQuadratic w := by
  rw [fourCellEvenPolarFreeOperator_eq_coupledCore_sub_scalar_sub_regular_of_even
    w hw hlocal heven,
    finiteSeven_regularKernelIntegral_eq_polynomial_add_envelope w hw]
  unfold fourCellEvenFiniteSevenPolynomialPolarFreeOperator
  ring

private theorem finiteSeven_quotientMode_even (k : ℕ) :
    Function.Even (fourCellEvenFiniteSevenQuotientMode (2 * k)) := by
  intro x
  unfold fourCellEvenFiniteSevenQuotientMode
  rw [finiteSeven_centeredMode_even k x,
    finiteSeven_centeredMode_even 0 x]

private theorem finiteSeven_centeredMode_contDiff (n : ℕ) :
    ContDiff ℝ 1 (fourCellEvenFiniteSevenCenteredMode n) := by
  have hp : ContDiff ℝ 1
      (fun y : ℝ ↦ (shiftedLegendreReal n).eval y) := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      (shiftedLegendreReal n).contDiff_aeval (𝕜 := ℝ) 1
  have haff : ContDiff ℝ 1 (fun x : ℝ ↦ (x + 1) / 2) := by
    fun_prop
  unfold fourCellEvenFiniteSevenCenteredMode centeredPolynomialLift
  simpa only [Function.comp_apply] using hp.comp haff

private theorem finiteSeven_quotientMode_locallyLipschitzOn (k : ℕ) :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fourCellEvenFiniteSevenQuotientMode (2 * k)) := by
  unfold fourCellEvenFiniteSevenQuotientMode
  have hdiff : ContDiff ℝ 1
      (fun x : ℝ ↦ fourCellEvenFiniteSevenCenteredMode (2 * k) x -
        (fourCellEvenFiniteSevenCoshCoordinate (2 * k) /
          fourCellEvenFiniteSevenCoshCoordinate 0) *
            fourCellEvenFiniteSevenCenteredMode 0 x) :=
    (finiteSeven_centeredMode_contDiff (2 * k)).sub
      (contDiff_const.mul (finiteSeven_centeredMode_contDiff 0))
  exact hdiff.locallyLipschitz.locallyLipschitzOn

private theorem finiteSeven_truePolarFreePolarization_eq_polynomial_sub_envelope
    (k l : ℕ) :
    fourCellEvenFiniteSevenPolarFreePolarization
        (fourCellEvenFiniteSevenQuotientMode (2 * k))
        (fourCellEvenFiniteSevenQuotientMode (2 * l)) =
      fourCellEvenFiniteSevenPolynomialPolarFreePolarization
        (fourCellEvenFiniteSevenQuotientMode (2 * k))
        (fourCellEvenFiniteSevenQuotientMode (2 * l)) -
      2 * fourCellOperatorHalfWidth *
        fourCellEvenFiniteSevenRegularEnvelopePolarization
          (fourCellEvenFiniteSevenQuotientMode (2 * k))
          (fourCellEvenFiniteSevenQuotientMode (2 * l)) := by
  let u : ℝ → ℝ := fourCellEvenFiniteSevenQuotientMode (2 * k)
  let v : ℝ → ℝ := fourCellEvenFiniteSevenQuotientMode (2 * l)
  have hu : Continuous u := finiteSeven_quotientMode_continuous (2 * k)
  have hv : Continuous v := finiteSeven_quotientMode_continuous (2 * l)
  have huLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u :=
    finiteSeven_quotientMode_locallyLipschitzOn k
  have hvLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v :=
    finiteSeven_quotientMode_locallyLipschitzOn l
  have huEven : Function.Even u := finiteSeven_quotientMode_even k
  have hvEven : Function.Even v := finiteSeven_quotientMode_even l
  have huv := finiteSeven_polarFreeOperator_eq_polynomial_sub_envelope
    (u + v) (hu.add hv) (huLocal.add hvLocal) (huEven.add hvEven)
  have huEq := finiteSeven_polarFreeOperator_eq_polynomial_sub_envelope
    u hu huLocal huEven
  have hvEq := finiteSeven_polarFreeOperator_eq_polynomial_sub_envelope
    v hv hvLocal hvEven
  unfold fourCellEvenFiniteSevenPolarFreePolarization
    fourCellEvenFiniteSevenPolynomialPolarFreePolarization
    fourCellEvenFiniteSevenRegularEnvelopePolarization
  change (fourCellEvenPolarFreeOperator (u + v) -
      fourCellEvenPolarFreeOperator u - fourCellEvenPolarFreeOperator v) / 2 = _
  rw [huv, huEq, hvEq]
  ring

private theorem finiteSeven_endpointSeedCorrelation_nonnegative
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    0 ≤ centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t := by
  unfold centeredEndpointCorrelation
  apply intervalIntegral.integral_nonneg (by linarith [ht.2])
  intro x hx
  have hxLower : (-1 : ℝ) ≤ x := hx.1
  have hxUpper : x ≤ 1 := by linarith [hx.2, ht.1]
  have htxLower : (-1 : ℝ) ≤ t + x := by linarith [ht.1, hx.1]
  have htxUpper : t + x ≤ 1 := by linarith [hx.2]
  unfold fourCellEvenEndpointCoshSeed
  exact mul_nonneg
    (by nlinarith [sq_nonneg (t + x)])
    (by nlinarith [sq_nonneg x])

private theorem finiteSeven_endpointSeed_regularCorrelation_nonnegative :
    0 ≤ ∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
    mul_nonneg ha0 ht.1
  have hargUpper : fourCellOperatorHalfWidth * t ≤
      5 * Real.log 2 / 4 := by
    calc
      fourCellOperatorHalfWidth * t ≤ fourCellOperatorHalfWidth * 2 :=
        mul_le_mul_of_nonneg_left ht.2 ha0
      _ = 5 * Real.log 2 / 4 := by
        unfold fourCellOperatorHalfWidth
        ring
  exact mul_nonneg
    (yoshidaRegularKernel_nonneg_fourCellRange harg0 hargUpper)
    (finiteSeven_endpointSeedCorrelation_nonnegative ht)

private theorem finiteSeven_endpointSeed_coshMoment_nonnegative_le :
    0 ≤ fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
        (fourCellOperatorHalfWidth / 2) ∧
      fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
          (fourCellOperatorHalfWidth / 2) ≤ (4 / 3 : ℝ) := by
  unfold fourCellPositiveCoshMoment
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    unfold fourCellEvenEndpointCoshSeed
    exact mul_nonneg (Real.cosh_pos _).le
      (by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)])
  · calc
      (∫ x : ℝ in 0..1,
        Real.cosh ((fourCellOperatorHalfWidth / 2) * x) *
          fourCellEvenEndpointCoshSeed x) ≤
          ∫ _x : ℝ in 0..1, (4 / 3 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          ((Continuous.mul (by fun_prop)
            fourCellEvenEndpointCoshSeed_continuous).intervalIntegrable 0 1)
          (Continuous.intervalIntegrable continuous_const 0 1)
        intro x hx
        have hu0 : 0 ≤ (fourCellOperatorHalfWidth / 2) * x :=
          mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) hx.1
        have hu : (fourCellOperatorHalfWidth / 2) * x < (7 / 10 : ℝ) := by
          have hlog := strict_log_two_bounds.2
          unfold fourCellOperatorHalfWidth
          norm_num at hx ⊢
          nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
        have hcosh := finiteSeven_cosh_lt_four_thirds hu0 hu
        have hseed0 : 0 ≤ fourCellEvenEndpointCoshSeed x := by
          unfold fourCellEvenEndpointCoshSeed
          nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
        have hseed1 : fourCellEvenEndpointCoshSeed x ≤ 1 := by
          unfold fourCellEvenEndpointCoshSeed
          nlinarith [sq_nonneg x]
        have hmul := mul_le_mul hcosh.le hseed1
          hseed0 (by norm_num : (0 : ℝ) ≤ 4 / 3)
        change Real.cosh ((fourCellOperatorHalfWidth / 2) * x) *
          fourCellEvenEndpointCoshSeed x ≤ 4 / 3
        nlinarith
      _ = (4 / 3 : ℝ) := by norm_num

private theorem finiteSeven_fourCellScalar_nonnegative :
    0 ≤ Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hwidth :
      Real.log (2 * fourCellOperatorHalfWidth) =
        Real.log (5 / 4 : ℝ) + Real.log (Real.log 2) := by
    rw [show 2 * fourCellOperatorHalfWidth =
        (5 / 4 : ℝ) * Real.log 2 by
      unfold fourCellOperatorHalfWidth
      ring,
      Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  rw [hwidth]
  have hfive : 0 ≤ Real.log (5 / 4 : ℝ) :=
    Real.log_nonneg (by norm_num)
  linarith [strict_log_log_two_bounds.1,
    strict_euler_gamma_bounds.1, strict_log_pi_bounds.1]

/-- A coarse but fully structural upper bound for the fixed positive seed
bracket.  Its only role is to transport the `10⁻¹⁰` regular-row error
through the final bordered entry. -/
theorem fourCellEvenExactBracket_endpointCoshSeed_lt_eight :
    fourCellEvenExactBracket fourCellEvenEndpointCoshSeed < 8 := by
  let L : ℝ := Real.log 2
  let S : ℝ := Real.log (2 * fourCellOperatorHalfWidth) +
    Real.eulerMascheroniConstant + Real.log Real.pi
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation fourCellEvenEndpointCoshSeed t
  let H : ℝ := fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
    (fourCellOperatorHalfWidth / 2)
  have hL0 : 0 ≤ L := (Real.log_pos (by norm_num)).le
  have hL : L < (7 / 10 : ℝ) := by
    dsimp only [L]
    linarith [strict_log_two_bounds.2]
  have hS : 0 ≤ S := by
    simpa only [S] using finiteSeven_fourCellScalar_nonnegative
  have hR : 0 ≤ R := by
    simpa only [R] using finiteSeven_endpointSeed_regularCorrelation_nonnegative
  have hH := finiteSeven_endpointSeed_coshMoment_nonnegative_le
  have hH0 : 0 ≤ H := by simpa only [H] using hH.1
  have hHle : H ≤ (4 / 3 : ℝ) := by simpa only [H] using hH.2
  have hHsq : H ^ 2 ≤ (16 / 9 : ℝ) := by
    have := pow_le_pow_left₀ hH0 hHle 2
    norm_num at this ⊢
    exact this
  have hLHsq : L * H ^ 2 ≤ (7 / 10 : ℝ) * (16 / 9 : ℝ) := by
    calc
      L * H ^ 2 ≤ (7 / 10 : ℝ) * H ^ 2 :=
        mul_le_mul_of_nonneg_right hL.le (sq_nonneg H)
      _ ≤ (7 / 10 : ℝ) * (16 / 9 : ℝ) :=
        mul_le_mul_of_nonneg_left hHsq (by norm_num)
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [fourCellEvenExactBracket_endpointCoshSeed_formula]
  change 248 / 225 - (16 / 15 : ℝ) * L - S * (16 / 15) -
      (5 * L / 4) * R + 5 * L * H ^ 2 -
        Real.sqrt 2 * L * (1616 / 46875) < 8
  nlinarith

/-- The true bordered entry with only its regular kernel row replaced by the
degree-eighteen polynomial. -/
def fourCellEvenFiniteSevenPolynomialBorderEntry (m n : ℕ) : ℝ :=
  fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
      fourCellEvenFiniteSevenPolynomialPolarFreePolarization
        (fourCellEvenFiniteSevenQuotientMode m)
        (fourCellEvenFiniteSevenQuotientMode n) -
    (251 / 250 : ℝ) *
      fourCellEvenEndpointSeedRow (fourCellEvenFiniteSevenQuotientMode m) *
      fourCellEvenEndpointSeedRow (fourCellEvenFiniteSevenQuotientMode n)

theorem fourCellEvenFiniteSevenTrueBorderEntry_eq_polynomial_sub_envelope
    (k l : ℕ) :
    fourCellEvenFiniteSevenTrueBorderEntry (2 * k) (2 * l) =
      fourCellEvenFiniteSevenPolynomialBorderEntry (2 * k) (2 * l) -
        fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
          (2 * fourCellOperatorHalfWidth) *
          fourCellEvenFiniteSevenRegularEnvelopePolarization
            (fourCellEvenFiniteSevenQuotientMode (2 * k))
            (fourCellEvenFiniteSevenQuotientMode (2 * l)) := by
  unfold fourCellEvenFiniteSevenTrueBorderEntry
    fourCellEvenFiniteSevenBorderPolarization
    fourCellEvenFiniteSevenPolynomialBorderEntry
  rw [finiteSeven_truePolarFreePolarization_eq_polynomial_sub_envelope k l]
  ring

/-- Actual entrywise analytic enclosure: every one of the twenty-one true
border entries lies within the certificate radius `10⁻⁹` of its fully
kernel-polynomial counterpart. -/
theorem abs_fourCellEvenFiniteSevenTrueBorderEntry_sub_polynomial_lt
    (k l : ℕ) :
    |fourCellEvenFiniteSevenTrueBorderEntry (2 * k) (2 * l) -
      fourCellEvenFiniteSevenPolynomialBorderEntry (2 * k) (2 * l)| <
        (1 / 1000000000 : ℝ) := by
  have hseed0 : 0 < fourCellEvenExactBracket fourCellEvenEndpointCoshSeed :=
    fourCellEvenExactBracket_endpointCoshSeed_pos
  have hseed8 := fourCellEvenExactBracket_endpointCoshSeed_lt_eight
  have hwidth0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hwidth1 : 2 * fourCellOperatorHalfWidth < 1 := by
    have hlog := strict_log_two_bounds.2
    unfold fourCellOperatorHalfWidth
    nlinarith
  have henv := abs_fourCellEvenFiniteSevenRegularEnvelopePolarization_lt k l
  rw [fourCellEvenFiniteSevenTrueBorderEntry_eq_polynomial_sub_envelope]
  rw [show (fourCellEvenFiniteSevenPolynomialBorderEntry (2 * k) (2 * l) -
      fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
          (2 * fourCellOperatorHalfWidth) *
          fourCellEvenFiniteSevenRegularEnvelopePolarization
            (fourCellEvenFiniteSevenQuotientMode (2 * k))
            (fourCellEvenFiniteSevenQuotientMode (2 * l)) -
      fourCellEvenFiniteSevenPolynomialBorderEntry (2 * k) (2 * l)) =
        -(fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
          (2 * fourCellOperatorHalfWidth) *
          fourCellEvenFiniteSevenRegularEnvelopePolarization
            (fourCellEvenFiniteSevenQuotientMode (2 * k))
            (fourCellEvenFiniteSevenQuotientMode (2 * l))) by ring,
    abs_neg, abs_mul, abs_mul,
    abs_of_pos hseed0, abs_of_nonneg hwidth0]
  have hmul1 :
      fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
          (2 * fourCellOperatorHalfWidth) < 8 := by
    nlinarith
  have henv0 :
      0 ≤ |fourCellEvenFiniteSevenRegularEnvelopePolarization
        (fourCellEvenFiniteSevenQuotientMode (2 * k))
        (fourCellEvenFiniteSevenQuotientMode (2 * l))| := abs_nonneg _
  calc
    _ < 8 * (1 / 10000000000 : ℝ) := by
      exact (mul_le_mul_of_nonneg_right hmul1.le henv0).trans_lt
        (mul_lt_mul_of_pos_left henv (by norm_num))
    _ < (1 / 1000000000 : ℝ) := by norm_num

/-- Sharpened actual-entry enclosure on precisely the six retained modes
`P₂,P₄,…,P₁₂`.  At least nine tenths of the `10⁻⁹` certificate box
therefore remains for enclosing the exact polynomialized entry itself. -/
theorem abs_fourCellEvenFiniteSevenTrueBorderEntry_sub_polynomial_nonconstant_lt
    (k l : ℕ) :
    |fourCellEvenFiniteSevenTrueBorderEntry (2 * (k + 1)) (2 * (l + 1)) -
      fourCellEvenFiniteSevenPolynomialBorderEntry
        (2 * (k + 1)) (2 * (l + 1))| <
        (1 / 10000000000 : ℝ) := by
  have hseed0 : 0 < fourCellEvenExactBracket fourCellEvenEndpointCoshSeed :=
    fourCellEvenExactBracket_endpointCoshSeed_pos
  have hseed8 := fourCellEvenExactBracket_endpointCoshSeed_lt_eight
  have hwidth0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hwidth1 : 2 * fourCellOperatorHalfWidth < 1 := by
    have hlog := strict_log_two_bounds.2
    unfold fourCellOperatorHalfWidth
    nlinarith
  have henv :=
    abs_fourCellEvenFiniteSevenRegularEnvelopePolarization_nonconstant_lt k l
  rw [fourCellEvenFiniteSevenTrueBorderEntry_eq_polynomial_sub_envelope]
  rw [show
      (fourCellEvenFiniteSevenPolynomialBorderEntry
          (2 * (k + 1)) (2 * (l + 1)) -
        fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
            (2 * fourCellOperatorHalfWidth) *
            fourCellEvenFiniteSevenRegularEnvelopePolarization
              (fourCellEvenFiniteSevenQuotientMode (2 * (k + 1)))
              (fourCellEvenFiniteSevenQuotientMode (2 * (l + 1))) -
        fourCellEvenFiniteSevenPolynomialBorderEntry
          (2 * (k + 1)) (2 * (l + 1))) =
      -(fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
        (2 * fourCellOperatorHalfWidth) *
        fourCellEvenFiniteSevenRegularEnvelopePolarization
          (fourCellEvenFiniteSevenQuotientMode (2 * (k + 1)))
          (fourCellEvenFiniteSevenQuotientMode (2 * (l + 1)))) by ring,
    abs_neg, abs_mul, abs_mul,
    abs_of_pos hseed0, abs_of_nonneg hwidth0]
  have hmul8 :
      fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
          (2 * fourCellOperatorHalfWidth) < 8 := by
    nlinarith
  have henv0 :
      0 ≤ |fourCellEvenFiniteSevenRegularEnvelopePolarization
        (fourCellEvenFiniteSevenQuotientMode (2 * (k + 1)))
        (fourCellEvenFiniteSevenQuotientMode (2 * (l + 1)))| := abs_nonneg _
  calc
    _ < 8 * (1 / 100000000000 : ℝ) := by
      exact (mul_le_mul_of_nonneg_right hmul8.le henv0).trans_lt
        (mul_lt_mul_of_pos_left henv (by norm_num))
    _ < (1 / 10000000000 : ℝ) := by norm_num

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedFiniteSevenEntryEnclosuresStructural
