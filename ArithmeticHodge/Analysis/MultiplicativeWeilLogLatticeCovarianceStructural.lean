import ArithmeticHodge.Analysis.MultiplicativeWeilCellAssemblyStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Exact logarithmic-lattice covariance of the global Bombieri form

Normalized multiplicative dilation is a translation on the critical
logarithmic line.  The diagonal Bombieri functional is already known to be
invariant under this action.  Here we prove that its *complete* polarized
cross symbol is invariant under simultaneous dilation as well.  This retains
the cancellation between the local critical form and the prime cross.

Consequently the concrete Gram data of a geometric dilation orbit are
Toeplitz: the diagonal is constant and every cross entry is unchanged by a
common shift of its two lattice indices.  No positivity assumption enters
these identities.
-/

/-! ## Algebra of normalized dilation -/

theorem normalizedDilation_add
    (lambda : ℝ) (hlambda : 0 < lambda) (f g : BombieriTest) :
    normalizedDilation lambda hlambda (f + g) =
      normalizedDilation lambda hlambda f +
        normalizedDilation lambda hlambda g := by
  ext x
  simp only [normalizedDilation_apply, TestFunction.coe_add, Pi.add_apply]
  ring

theorem normalizedDilation_smul
    (lambda : ℝ) (hlambda : 0 < lambda) (c : ℂ) (g : BombieriTest) :
    normalizedDilation lambda hlambda (c • g) =
      c • normalizedDilation lambda hlambda g := by
  ext x
  simp only [normalizedDilation_apply, TestFunction.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem normalizedDilation_comp
    (lambda mu : ℝ) (hlambda : 0 < lambda) (hmu : 0 < mu)
    (g : BombieriTest) :
    normalizedDilation lambda hlambda
        (normalizedDilation mu hmu g) =
      normalizedDilation (lambda * mu) (mul_pos hlambda hmu) g := by
  ext x
  simp only [normalizedDilation_apply]
  rw [Real.sqrt_mul hlambda.le]
  push_cast
  rw [show mu * (lambda * x) = (lambda * mu) * x by ring]
  ring

@[simp]
theorem normalizedDilation_one (g : BombieriTest) :
    normalizedDilation 1 (by norm_num) g = g := by
  ext x
  simp only [normalizedDilation_apply, Real.sqrt_one, Complex.ofReal_one,
    one_mul]

/-- A dilation by `mu` factors through any positive common scale `lambda`
and the relative dilation `mu / lambda`. -/
theorem normalizedDilation_eq_comp_div
    (lambda mu : ℝ) (hlambda : 0 < lambda) (hmu : 0 < mu)
    (g : BombieriTest) :
    normalizedDilation mu hmu g =
      normalizedDilation lambda hlambda
        (normalizedDilation (mu / lambda) (div_pos hmu hlambda) g) := by
  have hcomp := normalizedDilation_comp lambda (mu / lambda)
    hlambda (div_pos hmu hlambda) g
  have hproduct : lambda * (mu / lambda) = mu := by
    field_simp [hlambda.ne']
  simpa only [hproduct] using hcomp.symm

/-! ## Full global covariance -/

/-- The real Bombieri diagonal is exactly constant along every normalized
dilation orbit. -/
theorem bombieriGlobalDiagonal_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    (bombieriFunctional
        (bombieriQuadraticTest
          (normalizedDilation lambda hlambda g))).re =
      (bombieriFunctional (bombieriQuadraticTest g)).re := by
  rw [bombieriFunctional_quadratic_normalizedDilation]

/-- The complete local-minus-prime cross is invariant under a common
normalized dilation.  The proof reconstructs both complex coordinates from
the exact global quadratic expansion, so it does not split the cancellation
between the archimedean and prime terms. -/
theorem bombieriTwoBlockGlobalCrossSymbol_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (f g : BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol
        (normalizedDilation lambda hlambda f)
        (normalizedDilation lambda hlambda g) =
      bombieriTwoBlockGlobalCrossSymbol f g := by
  have hquadratic (c : ℂ) :
      (bombieriFunctional
          (bombieriQuadraticTest
            (normalizedDilation lambda hlambda f +
              c • normalizedDilation lambda hlambda g))).re =
        (bombieriFunctional
          (bombieriQuadraticTest (f + c • g))).re := by
    rw [← normalizedDilation_smul lambda hlambda c g,
      ← normalizedDilation_add lambda hlambda f (c • g),
      bombieriFunctional_quadratic_normalizedDilation]
  apply Complex.ext
  · have h := hquadratic 1
    rw [bombieriFunctional_twoBlock_re,
      bombieriFunctional_twoBlock_re] at h
    rw [bombieriFunctional_quadratic_normalizedDilation,
      bombieriFunctional_quadratic_normalizedDilation] at h
    simp only [Complex.normSq_one, one_mul] at h
    linarith
  · have h := hquadratic Complex.I
    rw [bombieriFunctional_twoBlock_re,
      bombieriFunctional_twoBlock_re] at h
    rw [bombieriFunctional_quadratic_normalizedDilation,
      bombieriFunctional_quadratic_normalizedDilation] at h
    simp only [Complex.normSq_I, one_mul, Complex.mul_re,
      Complex.I_re, Complex.I_im, zero_mul] at h
    linarith

/-- Sharp relative-scale formula: after removing the common dilation of the
first block, the cross depends only on the ratio `mu / lambda`. -/
theorem bombieriTwoBlockGlobalCrossSymbol_relativeDilation
    (lambda mu : ℝ) (hlambda : 0 < lambda) (hmu : 0 < mu)
    (f g : BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol
        (normalizedDilation lambda hlambda f)
        (normalizedDilation mu hmu g) =
      bombieriTwoBlockGlobalCrossSymbol f
        (normalizedDilation (mu / lambda) (div_pos hmu hlambda) g) := by
  rw [normalizedDilation_eq_comp_div lambda mu hlambda hmu g]
  exact bombieriTwoBlockGlobalCrossSymbol_normalizedDilation
    lambda hlambda f
      (normalizedDilation (mu / lambda) (div_pos hmu hlambda) g)

/-! ## Hermitian symmetry of the complete cross -/

private theorem bombieriQuadraticCrossTest_comm
    (f g : BombieriTest) :
    bombieriQuadraticCrossTest f g = bombieriQuadraticCrossTest g f := by
  ext x
  simp only [bombieriQuadraticCrossTest_apply]
  ac_rfl

private theorem bombieriQuadraticCrossTest_I_swap
    (f g : BombieriTest) :
    bombieriQuadraticCrossTest g (Complex.I • f) =
      -bombieriQuadraticCrossTest f (Complex.I • g) := by
  ext x
  rw [bombieriQuadraticCrossTest_apply]
  simp only [TestFunction.coe_neg, Pi.neg_apply]
  rw [bombieriQuadraticCrossTest_apply]
  simp only [
    bombieriDirectedCorrelation_smul_left,
    bombieriDirectedCorrelation_smul_right]
  simp only [starRingEnd_apply]
  rw [show star (Complex.I : ℂ) = -Complex.I from Complex.conj_I]
  ring

private theorem primeSum_neg (h : BombieriTest) :
    primeSum (-h) = -primeSum h := by
  have hscale := primeSum_smul (-1 : ℂ) h
  simpa only [neg_one_smul, neg_one_mul] using hscale

/-- The polarized prime cross is Hermitian. -/
theorem bombieriPolarizedPrimeCross_conj_swap
    (f g : BombieriTest) :
    star (bombieriPolarizedPrimeCross g f) =
      bombieriPolarizedPrimeCross f g := by
  have hcomm := bombieriQuadraticCrossTest_comm f g
  have hI := bombieriQuadraticCrossTest_I_swap f g
  unfold bombieriPolarizedPrimeCross
  rw [← hcomm, hI, primeSum_neg]
  simp only [Complex.star_def, map_sub, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.neg_re]
  push_cast
  ring

/-- The concrete global cross symbol is Hermitian, including its prime
contribution. -/
theorem bombieriTwoBlockGlobalCrossSymbol_conj_swap
    (f g : BombieriTest) :
    star (bombieriTwoBlockGlobalCrossSymbol g f) =
      bombieriTwoBlockGlobalCrossSymbol f g := by
  unfold bombieriTwoBlockGlobalCrossSymbol
  rw [star_sub, bombieriLocalCriticalForm_conj_apply,
    bombieriPolarizedPrimeCross_conj_swap]

/-- On the diagonal the polarized global cross is exactly the original
Bombieri quadratic value, not merely its real part. -/
theorem bombieriTwoBlockGlobalCrossSymbol_self
    (g : BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol g g =
      bombieriFunctional (bombieriQuadraticTest g) := by
  have hsum : g + (1 : ℂ) • g = (2 : ℂ) • g := by
    ext x
    simp only [TestFunction.coe_add, Pi.add_apply, TestFunction.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hreal := bombieriFunctional_twoBlock_re g g (1 : ℂ)
  rw [hsum, bombieriFunctional_quadratic_smul] at hreal
  norm_num only [Complex.normSq_natCast, Complex.normSq_one,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, one_mul] at hreal
  have hnorm : Complex.normSq (2 : ℂ) = 4 := by
    norm_num [Complex.normSq_apply]
  rw [hnorm] at hreal
  have hstar := bombieriTwoBlockGlobalCrossSymbol_conj_swap g g
  have himag := congrArg Complex.im hstar
  simp only [Complex.star_def, Complex.conj_im] at himag
  apply Complex.ext
  · linarith
  · rw [bombieriFunctional_bombieriQuadraticTest_im_eq_zero]
    linarith

/-! ## Geometric logarithmic lattices -/

/-- The normalized `n`th point of the geometric dilation orbit of `g`. -/
def bombieriLogLatticeTest
    (q : ℝ) (hq : 0 < q) (g : BombieriTest) (n : ℕ) : BombieriTest :=
  normalizedDilation (q ^ n) (pow_pos hq n) g

/-- The concrete real diagonal along a geometric dilation orbit. -/
def bombieriLogLatticeDiagonal
    (q : ℝ) (hq : 0 < q) (g : BombieriTest) (n : ℕ) : ℝ :=
  (bombieriFunctional
    (bombieriQuadraticTest (bombieriLogLatticeTest q hq g n))).re

/-- The complete global cross matrix along two geometric dilation orbits. -/
def bombieriLogLatticeCross
    (q : ℝ) (hq : 0 < q) (f g : BombieriTest) (i j : ℕ) : ℂ :=
  bombieriTwoBlockGlobalCrossSymbol
    (bombieriLogLatticeTest q hq f i)
    (bombieriLogLatticeTest q hq g j)

/-- Every lattice cross entry is the cross at the exact relative scale. -/
theorem bombieriLogLatticeCross_eq_relativeScale
    (q : ℝ) (hq : 0 < q) (f g : BombieriTest) (i j : ℕ) :
    bombieriLogLatticeCross q hq f g i j =
      bombieriTwoBlockGlobalCrossSymbol f
        (normalizedDilation ((q ^ j) / (q ^ i))
          (div_pos (pow_pos hq j) (pow_pos hq i)) g) := by
  unfold bombieriLogLatticeCross bombieriLogLatticeTest
  exact bombieriTwoBlockGlobalCrossSymbol_relativeDilation
    (q ^ i) (q ^ j) (pow_pos hq i) (pow_pos hq j) f g

/-- Every diagonal entry of a logarithmic dilation orbit is the original
Bombieri diagonal. -/
theorem bombieriLogLatticeDiagonal_eq
    (q : ℝ) (hq : 0 < q) (g : BombieriTest) (n : ℕ) :
    bombieriLogLatticeDiagonal q hq g n =
      (bombieriFunctional (bombieriQuadraticTest g)).re := by
  unfold bombieriLogLatticeDiagonal bombieriLogLatticeTest
  exact bombieriGlobalDiagonal_normalizedDilation
    (q ^ n) (pow_pos hq n) g

/-- The diagonal of the concrete cross matrix is exactly the Bombieri
quadratic value of the seed. -/
theorem bombieriLogLatticeCross_self
    (q : ℝ) (hq : 0 < q) (g : BombieriTest) (n : ℕ) :
    bombieriLogLatticeCross q hq g g n n =
      bombieriFunctional (bombieriQuadraticTest g) := by
  unfold bombieriLogLatticeCross bombieriLogLatticeTest
  rw [bombieriTwoBlockGlobalCrossSymbol_self,
    bombieriFunctional_quadratic_normalizedDilation]

/-- Thus the separately exposed real lattice diagonal is the real part of
the diagonal cross entry. -/
theorem bombieriLogLatticeCross_self_re
    (q : ℝ) (hq : 0 < q) (g : BombieriTest) (n : ℕ) :
    (bombieriLogLatticeCross q hq g g n n).re =
      bombieriLogLatticeDiagonal q hq g n := by
  rw [bombieriLogLatticeCross_self,
    bombieriLogLatticeDiagonal_eq]

/-- Adding lattice indices is composition of their normalized dilations. -/
theorem bombieriLogLatticeTest_add
    (q : ℝ) (hq : 0 < q) (g : BombieriTest) (k n : ℕ) :
    bombieriLogLatticeTest q hq g (k + n) =
      normalizedDilation (q ^ k) (pow_pos hq k)
        (bombieriLogLatticeTest q hq g n) := by
  ext x
  unfold bombieriLogLatticeTest
  simp only [normalizedDilation_apply]
  rw [pow_add, Real.sqrt_mul (pow_nonneg hq.le k)]
  push_cast
  rw [show q ^ n * (q ^ k * x) = (q ^ k * q ^ n) * x by ring]
  ring

/-- Exact Toeplitz covariance: a common shift of the two logarithmic lattice
indices leaves the full global cross entry unchanged. -/
theorem bombieriLogLatticeCross_add_left
    (q : ℝ) (hq : 0 < q) (f g : BombieriTest) (k i j : ℕ) :
    bombieriLogLatticeCross q hq f g (k + i) (k + j) =
      bombieriLogLatticeCross q hq f g i j := by
  have hf :
      bombieriLogLatticeTest q hq f (k + i) =
        normalizedDilation (q ^ k) (pow_pos hq k)
          (bombieriLogLatticeTest q hq f i) := by
    exact bombieriLogLatticeTest_add q hq f k i
  have hg :
      bombieriLogLatticeTest q hq g (k + j) =
        normalizedDilation (q ^ k) (pow_pos hq k)
          (bombieriLogLatticeTest q hq g j) := by
    exact bombieriLogLatticeTest_add q hq g k j
  unfold bombieriLogLatticeCross
  rw [hf, hg,
    bombieriTwoBlockGlobalCrossSymbol_normalizedDilation]

/-- Above the diagonal, each cross entry is exactly the lag-`j - i` entry in
the zeroth row.  This is the usual one-sided Toeplitz normal form. -/
theorem bombieriLogLatticeCross_eq_lag_of_le
    (q : ℝ) (hq : 0 < q) (f g : BombieriTest) (i j : ℕ)
    (hij : i ≤ j) :
    bombieriLogLatticeCross q hq f g i j =
      bombieriTwoBlockGlobalCrossSymbol f
        (bombieriLogLatticeTest q hq g (j - i)) := by
  have hshift := bombieriLogLatticeCross_add_left
    q hq f g i 0 (j - i)
  have hadd : i + (j - i) = j := Nat.add_sub_of_le hij
  simpa only [Nat.add_zero, hadd, bombieriLogLatticeCross,
    bombieriLogLatticeTest, pow_zero, normalizedDilation_one] using hshift

/-- The one-seed lattice cross matrix is Hermitian. -/
theorem bombieriLogLatticeCross_conj_swap
    (q : ℝ) (hq : 0 < q) (g : BombieriTest) (i j : ℕ) :
    star (bombieriLogLatticeCross q hq g g j i) =
      bombieriLogLatticeCross q hq g g i j := by
  unfold bombieriLogLatticeCross
  exact bombieriTwoBlockGlobalCrossSymbol_conj_swap _ _

/-- Below the diagonal, a one-seed cross entry is the conjugate of the
corresponding positive-lag entry. -/
theorem bombieriLogLatticeCross_eq_conj_lag_of_le
    (q : ℝ) (hq : 0 < q) (g : BombieriTest) (i j : ℕ)
    (hji : j ≤ i) :
    bombieriLogLatticeCross q hq g g i j =
      star (bombieriTwoBlockGlobalCrossSymbol g
        (bombieriLogLatticeTest q hq g (i - j))) := by
  rw [← bombieriLogLatticeCross_conj_swap q hq g i j]
  rw [bombieriLogLatticeCross_eq_lag_of_le q hq g g j i hji]

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
