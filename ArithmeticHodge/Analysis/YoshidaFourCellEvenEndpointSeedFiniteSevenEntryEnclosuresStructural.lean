import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedFiniteSevenClosureStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped Interval

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedFiniteSevenEntryEnclosuresStructural

noncomputable section

open YoshidaRegularKernelBound

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

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedFiniteSevenEntryEnclosuresStructural
