import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointClean

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointBilinear

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaCauchyPairing
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoDiagonalPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoParityDeterminant
open YoshidaFactorTwoParityRealification

/-!
# Bilinear form of the centered factor-two perturbation

The factor-two endpoint perturbation is kept as one symmetric polarization.
In particular, its smooth correlation kernel and both retained prime atoms are
never estimated separately in the identities below.  Bilinearity is not
claimed until the singular folded integral has been justified explicitly.
-/

/-- The ordered centered cross-correlation on the endpoint interval. -/
def factorTwoCenteredCrossCorrelation
    (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ in -1..1 - t, u (t + x) * v x

/-- The symmetric polarization of centered endpoint correlation. -/
def factorTwoCenteredCorrelationBilinear
    (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  (factorTwoCenteredCrossCorrelation u v t +
      factorTwoCenteredCrossCorrelation v u t) / 2

theorem factorTwoCenteredCrossCorrelation_self
    (w : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCrossCorrelation w w t =
      centeredEndpointCorrelation w t := by
  rfl

/-- The symmetric cross-correlation specializes exactly to the existing
centered autocorrelation on the diagonal. -/
theorem factorTwoCenteredCorrelationBilinear_self
    (w : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCorrelationBilinear w w t =
      centeredEndpointCorrelation w t := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation centeredEndpointCorrelation
  ring

/-- The symmetric polarization of the complete centered perturbation.  The
smooth archimedean kernel and both prime atoms remain coupled in every term
of this definition. -/
def factorTwoCenteredSymmetricPerturbationPolarization
    (u v : ℝ → ℝ) : ℝ :=
  (factorTwoCenteredSymmetricPerturbation (u + v) -
      factorTwoCenteredSymmetricPerturbation u -
      factorTwoCenteredSymmetricPerturbation v) / 2

/-- The perturbation polarization has the original quadratic perturbation as its
diagonal. -/
theorem factorTwoCenteredSymmetricPerturbationPolarization_self
    (w : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationPolarization w w =
      factorTwoCenteredSymmetricPerturbation w := by
  have hcorr (t : ℝ) : centeredEndpointCorrelation (w + w) t =
      4 * centeredEndpointCorrelation w t := by
    unfold centeredEndpointCorrelation
    rw [show (fun x : ℝ ↦ (w + w) (t + x) * (w + w) x) =
        fun x ↦ 4 * (w (t + x) * w x) by
      funext x
      simp only [Pi.add_apply]
      ring,
      intervalIntegral.integral_const_mul]
  unfold factorTwoCenteredSymmetricPerturbationPolarization
    factorTwoCenteredSymmetricPerturbation
  simp_rw [hcorr]
  rw [show (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
      (4 * centeredEndpointCorrelation w t)) =
      fun t ↦ 4 * (factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        centeredEndpointCorrelation w t) by
    funext t
    ring,
    intervalIntegral.integral_const_mul]
  ring

/-- Symmetry is exact and does not use any analytic estimate. -/
theorem factorTwoCenteredCorrelationBilinear_comm
    (u v : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCorrelationBilinear u v t =
      factorTwoCenteredCorrelationBilinear v u t := by
  unfold factorTwoCenteredCorrelationBilinear
  ring

theorem factorTwoCenteredSymmetricPerturbationPolarization_comm
    (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationPolarization u v =
      factorTwoCenteredSymmetricPerturbationPolarization v u := by
  unfold factorTwoCenteredSymmetricPerturbationPolarization
  rw [add_comm]
  ring

/-- Ordered cross-correlation is additive in its left input for continuous
profiles. -/
theorem factorTwoCenteredCrossCorrelation_add_left
    (u v w : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) (t : ℝ) :
    factorTwoCenteredCrossCorrelation (u + v) w t =
      factorTwoCenteredCrossCorrelation u w t +
        factorTwoCenteredCrossCorrelation v w t := by
  have huInt : IntervalIntegrable (fun x : ℝ ↦ u (t + x) * w x)
      volume (-1) (1 - t) :=
    ((hu.comp (continuous_const.add continuous_id)).mul hw).intervalIntegrable _ _
  have hvInt : IntervalIntegrable (fun x : ℝ ↦ v (t + x) * w x)
      volume (-1) (1 - t) :=
    ((hv.comp (continuous_const.add continuous_id)).mul hw).intervalIntegrable _ _
  unfold factorTwoCenteredCrossCorrelation
  rw [show (fun x : ℝ ↦ (u + v) (t + x) * w x) =
      fun x ↦ u (t + x) * w x + v (t + x) * w x by
    funext x
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add huInt hvInt]

/-- Ordered cross-correlation is additive in its right input for continuous
profiles. -/
theorem factorTwoCenteredCrossCorrelation_add_right
    (u v w : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) (t : ℝ) :
    factorTwoCenteredCrossCorrelation u (v + w) t =
      factorTwoCenteredCrossCorrelation u v t +
        factorTwoCenteredCrossCorrelation u w t := by
  have hvInt : IntervalIntegrable (fun x : ℝ ↦ u (t + x) * v x)
      volume (-1) (1 - t) :=
    ((hu.comp (continuous_const.add continuous_id)).mul hv).intervalIntegrable _ _
  have hwInt : IntervalIntegrable (fun x : ℝ ↦ u (t + x) * w x)
      volume (-1) (1 - t) :=
    ((hu.comp (continuous_const.add continuous_id)).mul hw).intervalIntegrable _ _
  unfold factorTwoCenteredCrossCorrelation
  rw [show (fun x : ℝ ↦ u (t + x) * (v + w) x) =
      fun x ↦ u (t + x) * v x + u (t + x) * w x by
    funext x
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add hvInt hwInt]

/-- Exact quadratic polarization of centered endpoint correlation. -/
theorem centeredEndpointCorrelation_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (t : ℝ) :
    centeredEndpointCorrelation (u + v) t =
      centeredEndpointCorrelation u t +
        2 * factorTwoCenteredCorrelationBilinear u v t +
      centeredEndpointCorrelation v t := by
  rw [← factorTwoCenteredCorrelationBilinear_self (u + v) t]
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_add_left u v (u + v) hu hv
      (hu.add hv) t,
    factorTwoCenteredCrossCorrelation_add_right u u v hu hu hv t,
    factorTwoCenteredCrossCorrelation_add_right v u v hv hu hv t,
    factorTwoCenteredCrossCorrelation_self u t,
    factorTwoCenteredCrossCorrelation_self v t]
  ring

/-- Exact quadratic polarization of the complete perturbation.  This is the
mixed term required by a cancellation-preserving low/tail Schur argument. -/
theorem factorTwoCenteredSymmetricPerturbation_add
    (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbation (u + v) =
      factorTwoCenteredSymmetricPerturbation u +
        2 * factorTwoCenteredSymmetricPerturbationPolarization u v +
      factorTwoCenteredSymmetricPerturbation v := by
  unfold factorTwoCenteredSymmetricPerturbationPolarization
  ring

/-! ## The alternating centered channel -/

/-- Two real supported critical pullbacks reduce their whole-line ordered
cross-correlation to the exact overlap interval. -/
theorem crossCorrelation_re_eq_interval_of_supported_real
    {a s : ℝ} (F G : SchwartzMap ℝ ℂ)
    (hFsupport : ∀ x ∉ Set.Icc (-a) a, F x = 0)
    (hGsupport : ∀ x ∉ Set.Icc (-a) a, G x = 0)
    (hFreal : ∀ x : ℝ, (F x).im = 0)
    (hGreal : ∀ x : ℝ, (G x).im = 0)
    (hs : s ≤ 2 * a) :
    (crossCorrelation (F : ℝ → ℂ) (G : ℝ → ℂ) s).re =
      ∫ x : ℝ in -a..a - s, (G (s + x)).re * (F x).re := by
  have hFreal' (x : ℝ) : F x = ((F x).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hFreal x
  have hGreal' (x : ℝ) : G x = ((G x).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hGreal x
  rw [crossCorrelation_apply]
  have hle : -a ≤ a - s := by linarith
  have hrestrict :
      (∫ x : ℝ, star (F x) * G (s + x)) =
        ∫ x : ℝ in -a..a - s, star (F x) * G (s + x) := by
    rw [intervalIntegral.integral_of_le hle,
      ← integral_Icc_eq_integral_Ioc]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      by_cases hxf : x ∈ Icc (-a) a
      · have hxgt : a - s < x := by
          by_contra hnot
          exact hx ⟨hxf.1, le_of_not_gt hnot⟩
        have hsx : s + x ∉ Icc (-a) a := by
          intro hmem
          linarith [hmem.2]
        rw [hGsupport (s + x) hsx, mul_zero]
      · rw [hFsupport x hxf, star_zero, zero_mul])).symm
  rw [hrestrict]
  have hrealIntegral :
      (∫ x : ℝ in -a..a - s, star (F x) * G (s + x)) =
        ((∫ x : ℝ in -a..a - s,
          (G (s + x)).re * (F x).re : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    change star (F x) * G (s + x) =
      (((G (s + x)).re * (F x).re : ℝ) : ℂ)
    rw [hFreal' x, hGreal' (s + x)]
    simp
    ring
  rw [hrealIntegral]
  rfl

/-- After endpoint rescaling, an ordered Bombieri critical correlation is the
centered ordered correlation with the exact Jacobian `yoshidaEndpointA`. -/
theorem bombieriCriticalCrossCorrelation_re_eq_endpoint_mul_centeredCross
    (u v : BombieriTest)
    (huSupport : YoshidaCriticalPullbackSupported yoshidaEndpointA u)
    (hvSupport : YoshidaCriticalPullbackSupported yoshidaEndpointA v)
    (huReal : ∀ x : ℝ,
      (u.logarithmicPullbackSchwartz (1 / 2) x).im = 0)
    (hvReal : ∀ x : ℝ,
      (v.logarithmicPullbackSchwartz (1 / 2) x).im = 0)
    {s : ℝ} (hs2 : s ≤ 2 * yoshidaEndpointA) :
    (bombieriCriticalCrossCorrelation u v s).re =
      yoshidaEndpointA *
        factorTwoCenteredCrossCorrelation
          (factorTwoCenteredProfile v) (factorTwoCenteredProfile u)
          (s / yoshidaEndpointA) := by
  let F : SchwartzMap ℝ ℂ :=
    u.logarithmicPullbackSchwartz (1 / 2)
  let G : SchwartzMap ℝ ℂ :=
    v.logarithmicPullbackSchwartz (1 / 2)
  let p : ℝ → ℝ := fun x ↦ (G (s + x)).re * (F x).re
  have hinterval := crossCorrelation_re_eq_interval_of_supported_real
    F G huSupport hvSupport huReal hvReal hs2
  change (bombieriCriticalCrossCorrelation u v s).re = _
  change (crossCorrelation (F : ℝ → ℂ) (G : ℝ → ℂ) s).re = _
  rw [hinterval]
  have hsubst := intervalIntegral.smul_integral_comp_mul_add
    (a := (-1 : ℝ)) (b := 1 - s / yoshidaEndpointA)
    p yoshidaEndpointA 0
  have htransport :
      (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA - s, p x) =
        yoshidaEndpointA *
          ∫ y : ℝ in -1..1 - s / yoshidaEndpointA,
            p (yoshidaEndpointA * y) := by
    calc
      (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA - s, p x) =
          ∫ x : ℝ in yoshidaEndpointA * (-1) + 0..
              yoshidaEndpointA * (1 - s / yoshidaEndpointA) + 0, p x := by
        congr 1 <;> field_simp [yoshidaEndpointA_pos.ne'] <;> ring
      _ = _ := by
        simpa only [smul_eq_mul, add_zero] using hsubst.symm
  change (∫ x : ℝ in -yoshidaEndpointA..yoshidaEndpointA - s, p x) = _
  rw [htransport]
  congr 1
  unfold factorTwoCenteredCrossCorrelation factorTwoCenteredProfile
  apply intervalIntegral.integral_congr
  intro y _hy
  dsimp only [p, F, G]
  congr 2
  field_simp [yoshidaEndpointA_pos.ne']

/-- The exact centered alternating channel.  Its ordered correlation
difference is the profile-level form of `factorTwoMixedParityCoupling`. -/
def factorTwoCenteredAlternatingCoupling (u v : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA *
      (∫ t : ℝ in 0..2,
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
          (factorTwoCenteredCrossCorrelation v u t -
            factorTwoCenteredCrossCorrelation u v t)) -
    (Real.log 3 / Real.sqrt 3) *
      (factorTwoCenteredCrossCorrelation v u
          (factorTwoPrimeShift / yoshidaEndpointA) -
        factorTwoCenteredCrossCorrelation u v
          (factorTwoPrimeShift / yoshidaEndpointA))

/-- The centered alternating channel vanishes on the diagonal. -/
theorem factorTwoCenteredAlternatingCoupling_self (u : ℝ → ℝ) :
    factorTwoCenteredAlternatingCoupling u u = 0 := by
  unfold factorTwoCenteredAlternatingCoupling
  simp

/-- The centered alternating channel changes sign when its arguments are
exchanged. -/
theorem factorTwoCenteredAlternatingCoupling_comm
    (u v : ℝ → ℝ) :
    factorTwoCenteredAlternatingCoupling v u =
      -factorTwoCenteredAlternatingCoupling u v := by
  unfold factorTwoCenteredAlternatingCoupling
  rw [show (fun t : ℝ ↦
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation u v t -
          factorTwoCenteredCrossCorrelation v u t)) =
      fun t ↦ -(factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation v u t -
          factorTwoCenteredCrossCorrelation u v t)) by
    funext t
    ring,
    intervalIntegral.integral_neg]
  ring

/-- For two real critical pullbacks on the endpoint interval, the production
alternating mixed coordinate is exactly the endpoint scale times the centered
alternating channel. -/
theorem factorTwoMixedParityCoupling_eq_endpoint_mul_centeredAlternating
    (u v : BombieriTest)
    (huSupport : YoshidaCriticalPullbackSupported yoshidaEndpointA u)
    (hvSupport : YoshidaCriticalPullbackSupported yoshidaEndpointA v)
    (huReal : ∀ x : ℝ,
      (u.logarithmicPullbackSchwartz (1 / 2) x).im = 0)
    (hvReal : ∀ x : ℝ,
      (v.logarithmicPullbackSchwartz (1 / 2) x).im = 0) :
    factorTwoMixedParityCoupling u v =
      yoshidaEndpointA *
        factorTwoCenteredAlternatingCoupling
          (factorTwoCenteredProfile u) (factorTwoCenteredProfile v) := by
  let q : ℝ → ℝ := fun s ↦
    factorTwoAntisymmetricWeight s *
      ((bombieriCriticalCrossCorrelation u v s).re -
        (bombieriCriticalCrossCorrelation v u s).re)
  have huv {s : ℝ} (hs : s ≤ 2 * yoshidaEndpointA) :=
    bombieriCriticalCrossCorrelation_re_eq_endpoint_mul_centeredCross
      u v huSupport hvSupport huReal hvReal hs
  have hvu {s : ℝ} (hs : s ≤ 2 * yoshidaEndpointA) :=
    bombieriCriticalCrossCorrelation_re_eq_endpoint_mul_centeredCross
      v u hvSupport huSupport hvReal huReal hs
  have hsubst := intervalIntegral.smul_integral_comp_mul_add
    (a := (0 : ℝ)) (b := 2) q yoshidaEndpointA 0
  have hchange :
      (∫ s : ℝ in 0..2 * yoshidaEndpointA, q s) =
        yoshidaEndpointA *
          ∫ t : ℝ in 0..2, q (yoshidaEndpointA * t) := by
    simpa only [smul_eq_mul, mul_zero, zero_add, add_zero, mul_comm]
      using hsubst.symm
  have hintegral :
      (∫ s : ℝ in 0..2 * yoshidaEndpointA, q s) =
        yoshidaEndpointA ^ 2 *
          ∫ t : ℝ in 0..2,
            factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
              (factorTwoCenteredCrossCorrelation
                  (factorTwoCenteredProfile v)
                  (factorTwoCenteredProfile u) t -
                factorTwoCenteredCrossCorrelation
                  (factorTwoCenteredProfile u)
                  (factorTwoCenteredProfile v) t) := by
    rw [hchange]
    have hinner :
        (∫ t : ℝ in 0..2, q (yoshidaEndpointA * t)) =
          ∫ t : ℝ in 0..2,
            yoshidaEndpointA *
              (factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
                (factorTwoCenteredCrossCorrelation
                    (factorTwoCenteredProfile v)
                    (factorTwoCenteredProfile u) t -
                  factorTwoCenteredCrossCorrelation
                    (factorTwoCenteredProfile u)
                    (factorTwoCenteredProfile v) t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
      have hst : yoshidaEndpointA * t ≤ 2 * yoshidaEndpointA := by
        nlinarith [ht.2, yoshidaEndpointA_pos]
      dsimp only [q]
      rw [huv hst, hvu hst]
      have hdiv : yoshidaEndpointA * t / yoshidaEndpointA = t := by
        field_simp [yoshidaEndpointA_pos.ne']
      rw [hdiv]
      ring
    rw [hinner, intervalIntegral.integral_const_mul]
    ring
  have hprimeUV := huv factorTwoPrimeShift_mem_endpointInterval.2
  have hprimeVU := hvu factorTwoPrimeShift_mem_endpointInterval.2
  unfold factorTwoMixedParityCoupling
    factorTwoCenteredAlternatingCoupling
  rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
  change (∫ s : ℝ in 0..2 * yoshidaEndpointA, q s) - _ = _
  rw [hintegral, hprimeUV, hprimeVU]
  ring

/-- The two signed centered endpoint energies. -/
def factorTwoCenteredEndpointPlus (w : ℝ → ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic w +
    factorTwoCenteredSymmetricPerturbation w

def factorTwoCenteredEndpointMinus (w : ℝ → ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic w -
    factorTwoCenteredSymmetricPerturbation w

/-- The antisymmetric folded coordinate is invariant under normalized
multiplicative dilation. -/
theorem factorTwoAntisymmetricCoordinate_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    factorTwoAntisymmetricCoordinate
        (normalizedDilation lambda hlambda g) =
      factorTwoAntisymmetricCoordinate g := by
  unfold factorTwoAntisymmetricCoordinate
  simp_rw [factorTwoSelfCorrelation_normalizedDilation lambda hlambda g]

/-- Canonical logarithmic centering puts the full alternating production
coordinate into the same two real profile coordinates as the signed endpoint
energies. -/
theorem factorTwoAntisymmetricCoordinate_eq_logCentered_profiles
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    let gc := normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g
    factorTwoAntisymmetricCoordinate g =
      yoshidaEndpointA *
        factorTwoCenteredAlternatingCoupling
          (factorTwoCenteredProfile (bombieriRealPartTest gc))
          (factorTwoCenteredProfile (bombieriImagPartTest gc)) := by
  let lambda : ℝ := logarithmicCenter a b
  have hlambda : 0 < lambda := logarithmicCenter_pos a b
  let gc : BombieriTest := normalizedDilation lambda hlambda g
  have hcritical : YoshidaCriticalPullbackSupported yoshidaEndpointA gc := by
    simpa only [gc, lambda, hlambda] using
      logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaEndpointA
        g ha hab hsupport hratio
  have huCritical := bombieriRealPartTest_criticalPullbackSupported
    gc hcritical
  have hvCritical := bombieriImagPartTest_criticalPullbackSupported
    gc hcritical
  have hcentered :=
    factorTwoMixedParityCoupling_eq_endpoint_mul_centeredAlternating
      (bombieriRealPartTest gc) (bombieriImagPartTest gc)
      huCritical hvCritical
      (bombieriRealPartTest_criticalPullback_im_eq_zero gc)
      (bombieriImagPartTest_criticalPullback_im_eq_zero gc)
  calc
    factorTwoAntisymmetricCoordinate g =
        factorTwoAntisymmetricCoordinate gc := by
      simpa only [gc] using
        (factorTwoAntisymmetricCoordinate_normalizedDilation
          lambda hlambda g).symm
    _ = factorTwoMixedParityCoupling
          (bombieriRealPartTest gc) (bombieriImagPartTest gc) :=
      factorTwoAntisymmetricCoordinate_eq_realImag gc
    _ = _ := hcentered

/-- The exact folded determinant inequality is equivalent, after cancelling
the positive endpoint-scale square, to the product of the two signed centered
endpoint energies dominating the centered alternating square. -/
theorem factorTwo_folded_determinant_iff_logCentered_profiles
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    let gc := normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g
    let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
    let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
    factorTwoSymmetricCoordinate g ^ 2 +
          factorTwoAntisymmetricCoordinate g ^ 2 ≤
        factorTwoDiagonalCoordinate g ^ 2 ↔
      factorTwoCenteredAlternatingCoupling u v ^ 2 ≤
        (factorTwoCenteredEndpointPlus u +
          factorTwoCenteredEndpointPlus v) *
        (factorTwoCenteredEndpointMinus u +
          factorTwoCenteredEndpointMinus v) := by
  let lambda : ℝ := logarithmicCenter a b
  have hlambda : 0 < lambda := logarithmicCenter_pos a b
  let gc : BombieriTest := normalizedDilation lambda hlambda g
  let u : ℝ → ℝ := factorTwoCenteredProfile (bombieriRealPartTest gc)
  let v : ℝ → ℝ := factorTwoCenteredProfile (bombieriImagPartTest gc)
  let Eplus : ℝ := factorTwoCenteredEndpointPlus u +
    factorTwoCenteredEndpointPlus v
  let Eminus : ℝ := factorTwoCenteredEndpointMinus u +
    factorTwoCenteredEndpointMinus v
  let J : ℝ := factorTwoCenteredAlternatingCoupling u v
  have hplus0 := factorTwoDiagonal_add_symmetric_eq_logCentered_two_profiles
    g ha hab hsupport hratio
  have hminus0 := factorTwoDiagonal_sub_symmetric_eq_logCentered_two_profiles
    g ha hab hsupport hratio
  have hJ0 := factorTwoAntisymmetricCoordinate_eq_logCentered_profiles
    g ha hab hsupport hratio
  have hplus : factorTwoDiagonalCoordinate g +
      factorTwoSymmetricCoordinate g = yoshidaEndpointA * Eplus := by
    simpa only [gc, lambda, hlambda, u, v, Eplus,
      factorTwoCenteredEndpointPlus] using hplus0
  have hminus : factorTwoDiagonalCoordinate g -
      factorTwoSymmetricCoordinate g = yoshidaEndpointA * Eminus := by
    simpa only [gc, lambda, hlambda, u, v, Eminus,
      factorTwoCenteredEndpointMinus] using hminus0
  have hJ : factorTwoAntisymmetricCoordinate g =
      yoshidaEndpointA * J := by
    simpa only [gc, lambda, hlambda, u, v, J] using hJ0
  have hAsq : 0 < yoshidaEndpointA ^ 2 := sq_pos_of_pos yoshidaEndpointA_pos
  dsimp only
  change factorTwoSymmetricCoordinate g ^ 2 +
        factorTwoAntisymmetricCoordinate g ^ 2 ≤
      factorTwoDiagonalCoordinate g ^ 2 ↔ J ^ 2 ≤ Eplus * Eminus
  constructor
  · intro hdet
    have hprod : factorTwoAntisymmetricCoordinate g ^ 2 ≤
        (factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g) *
          (factorTwoDiagonalCoordinate g -
            factorTwoSymmetricCoordinate g) := by
      nlinarith
    rw [hJ, hplus, hminus] at hprod
    have hscaled : yoshidaEndpointA ^ 2 * J ^ 2 ≤
        yoshidaEndpointA ^ 2 * (Eplus * Eminus) := by
      calc
        yoshidaEndpointA ^ 2 * J ^ 2 =
            (yoshidaEndpointA * J) ^ 2 := by ring
        _ ≤ (yoshidaEndpointA * Eplus) *
            (yoshidaEndpointA * Eminus) := hprod
        _ = yoshidaEndpointA ^ 2 * (Eplus * Eminus) := by ring
    exact le_of_mul_le_mul_left hscaled hAsq
  · intro hcentered
    have hscaled : yoshidaEndpointA ^ 2 * J ^ 2 ≤
        yoshidaEndpointA ^ 2 * (Eplus * Eminus) :=
      mul_le_mul_of_nonneg_left hcentered hAsq.le
    have hprod : factorTwoAntisymmetricCoordinate g ^ 2 ≤
        (factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g) *
          (factorTwoDiagonalCoordinate g -
            factorTwoSymmetricCoordinate g) := by
      rw [hJ, hplus, hminus]
      calc
        (yoshidaEndpointA * J) ^ 2 =
            yoshidaEndpointA ^ 2 * J ^ 2 := by ring
        _ ≤ yoshidaEndpointA ^ 2 * (Eplus * Eminus) := hscaled
        _ = (yoshidaEndpointA * Eplus) *
            (yoshidaEndpointA * Eminus) := by ring
    nlinarith

/-- The strict reverse of the folded determinant is the strict reverse of the
single centered profile-product inequality. -/
theorem factorTwo_folded_determinant_strict_iff_logCentered_profiles
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    let gc := normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g
    let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
    let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
    factorTwoDiagonalCoordinate g ^ 2 <
        factorTwoSymmetricCoordinate g ^ 2 +
          factorTwoAntisymmetricCoordinate g ^ 2 ↔
      (factorTwoCenteredEndpointPlus u +
          factorTwoCenteredEndpointPlus v) *
        (factorTwoCenteredEndpointMinus u +
          factorTwoCenteredEndpointMinus v) <
        factorTwoCenteredAlternatingCoupling u v ^ 2 := by
  have hdet := factorTwo_folded_determinant_iff_logCentered_profiles
    g ha hab hsupport hratio
  dsimp only at hdet ⊢
  constructor
  · intro hstrict
    rw [← not_le]
    intro hcentered
    exact (not_le.mpr hstrict) (hdet.mpr hcentered)
  · intro hstrict
    rw [← not_le]
    intro hfolded
    exact (not_le.mpr hstrict) (hdet.mp hfolded)

/-- Universal same-seed factor-two Bombieri positivity is now exactly one
inequality between the two complete signed endpoint energies and the complete
alternating centered channel. -/
theorem bombieriFunctional_twoBump_nonneg_iff_logCentered_profiles
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
      let gc := normalizedDilation (logarithmicCenter a b)
        (logarithmicCenter_pos a b) g
      let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
      let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
      factorTwoCenteredAlternatingCoupling u v ^ 2 ≤
        (factorTwoCenteredEndpointPlus u +
          factorTwoCenteredEndpointPlus v) *
        (factorTwoCenteredEndpointMinus u +
          factorTwoCenteredEndpointMinus v) := by
  have hfold := bombieriFunctional_twoBump_nonneg_iff_foldedParity
    g ha hab hsupport hratio
  change
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
      factorTwoSymmetricCoordinate g ^ 2 +
          factorTwoAntisymmetricCoordinate g ^ 2 ≤
        factorTwoDiagonalCoordinate g ^ 2 at hfold
  exact hfold.trans
    (factorTwo_folded_determinant_iff_logCentered_profiles
      g ha hab hsupport hratio)

/-- A strict reverse of the centered profile-product inequality is exactly the
existence of a negative member of the production two-bump family. -/
theorem exists_bombieriFunctional_twoBump_neg_iff_logCentered_profiles
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∃ c : ℂ,
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re < 0) ↔
      let gc := normalizedDilation (logarithmicCenter a b)
        (logarithmicCenter_pos a b) g
      let u := factorTwoCenteredProfile (bombieriRealPartTest gc)
      let v := factorTwoCenteredProfile (bombieriImagPartTest gc)
      (factorTwoCenteredEndpointPlus u +
          factorTwoCenteredEndpointPlus v) *
        (factorTwoCenteredEndpointMinus u +
          factorTwoCenteredEndpointMinus v) <
        factorTwoCenteredAlternatingCoupling u v ^ 2 := by
  have hfold := exists_bombieriFunctional_twoBump_neg_iff_foldedParity
    g ha hab hsupport hratio
  change
    (∃ c : ℂ,
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re < 0) ↔
      factorTwoDiagonalCoordinate g ^ 2 <
        factorTwoSymmetricCoordinate g ^ 2 +
          factorTwoAntisymmetricCoordinate g ^ 2 at hfold
  exact hfold.trans
    (factorTwo_folded_determinant_strict_iff_logCentered_profiles
      g ha hab hsupport hratio)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointBilinear
