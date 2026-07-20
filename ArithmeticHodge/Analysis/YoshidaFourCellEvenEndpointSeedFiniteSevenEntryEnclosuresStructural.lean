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

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedFiniteSevenEntryEnclosuresStructural
