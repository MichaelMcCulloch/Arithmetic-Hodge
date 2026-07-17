import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointBilinear

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoFixedLagRepresenterStructural

open YoshidaFactorTwoEndpointBilinear

noncomputable section

/-!
# Representers for a fixed endpoint lag

A shift `τ ∈ [0,2]` acts by translation on the two boundary pieces of the
centered interval.  The right and left translates below give exact
one-variable representers for the two ordered correlations.  Their sum and
difference are the symmetric and alternating channels used by the retained
prime atom.
-/

/-- Right translate at lag `τ`, supported on the surviving left boundary
piece. -/
def factorTwoFixedLagRightRepresenter
    (τ : ℝ) (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Icc (-1 : ℝ) (1 - τ)).indicator (fun z ↦ p (τ + z)) x

/-- Left translate at lag `τ`, supported on the surviving right boundary
piece. -/
def factorTwoFixedLagLeftRepresenter
    (τ : ℝ) (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Icc (-1 + τ) 1).indicator (fun z ↦ p (z - τ)) x

/-- Symmetric fixed-lag representer. -/
def factorTwoFixedLagK (τ : ℝ) (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  factorTwoFixedLagRightRepresenter τ p x +
    factorTwoFixedLagLeftRepresenter τ p x

/-- Alternating fixed-lag representer, with right-minus-left sign. -/
def factorTwoFixedLagJ (τ : ℝ) (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  factorTwoFixedLagRightRepresenter τ p x -
    factorTwoFixedLagLeftRepresenter τ p x

/-! ## Ordered pairing identities -/

/-- The ordered correlation at a fixed lag is represented in its second
profile by the right translate of the first. -/
theorem crossCorrelation_eq_fixedLagRight
    (τ : ℝ) (p r : ℝ → ℝ) (hτ : τ ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation p r τ =
      ∫ x : ℝ in -1..1,
        factorTwoFixedLagRightRepresenter τ p x * r x := by
  have hle : (-1 : ℝ) ≤ 1 - τ := by linarith [hτ.2]
  have hzero (x : ℝ) (hx : x ∉ Icc (-1 : ℝ) 1) :
      factorTwoFixedLagRightRepresenter τ p x * r x = 0 := by
    have hxSupport : x ∉ Icc (-1 : ℝ) (1 - τ) := by
      intro hxSupport
      apply hx
      exact ⟨hxSupport.1, by linarith [hxSupport.2, hτ.1]⟩
    unfold factorTwoFixedLagRightRepresenter
    rw [Set.indicator_of_notMem hxSupport, zero_mul]
  unfold factorTwoCenteredCrossCorrelation
  calc
    (∫ x : ℝ in -1..1 - τ, p (τ + x) * r x) =
        ∫ x : ℝ in Icc (-1 : ℝ) (1 - τ),
          p (τ + x) * r x := by
      rw [intervalIntegral.integral_of_le hle,
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ x : ℝ,
        (Icc (-1 : ℝ) (1 - τ)).indicator
          (fun z ↦ p (τ + z) * r z) x :=
      (integral_indicator measurableSet_Icc).symm
    _ = ∫ x : ℝ,
        factorTwoFixedLagRightRepresenter τ p x * r x := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ Icc (-1 : ℝ) (1 - τ)
      · simp [factorTwoFixedLagRightRepresenter, hx]
      · simp [factorTwoFixedLagRightRepresenter, hx]
    _ = ∫ x : ℝ in Icc (-1 : ℝ) 1,
        factorTwoFixedLagRightRepresenter τ p x * r x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x : ℝ in -1..1,
        factorTwoFixedLagRightRepresenter τ p x * r x := by
      symm
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]

/-- The same ordered correlation is represented in its first profile by the
left translate of the second. -/
theorem crossCorrelation_eq_fixedLagLeft
    (τ : ℝ) (p r : ℝ → ℝ) (hτ : τ ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation p r τ =
      ∫ x : ℝ in -1..1,
        p x * factorTwoFixedLagLeftRepresenter τ r x := by
  have hle : (-1 : ℝ) ≤ 1 - τ := by linarith [hτ.2]
  have hshift :
      (∫ x : ℝ in -1..1 - τ, p (τ + x) * r x) =
        ∫ x : ℝ in -1 + τ..1, p x * r (x - τ) := by
    rw [show (fun x : ℝ ↦ p (τ + x) * r x) =
        fun x ↦ (fun y ↦ p y * r (y - τ)) (τ + x) by
      funext x
      congr 1
      ring,
      intervalIntegral.integral_comp_add_left
        (fun y : ℝ ↦ p y * r (y - τ)) τ]
    congr 1 <;> ring
  have hzero (x : ℝ) (hx : x ∉ Icc (-1 : ℝ) 1) :
      p x * factorTwoFixedLagLeftRepresenter τ r x = 0 := by
    have hxSupport : x ∉ Icc (-1 + τ) 1 := by
      intro hxSupport
      apply hx
      exact ⟨by linarith [hxSupport.1, hτ.1], hxSupport.2⟩
    unfold factorTwoFixedLagLeftRepresenter
    rw [Set.indicator_of_notMem hxSupport, mul_zero]
  unfold factorTwoCenteredCrossCorrelation
  rw [hshift]
  calc
    (∫ x : ℝ in -1 + τ..1, p x * r (x - τ)) =
        ∫ x : ℝ in Icc (-1 + τ) 1, p x * r (x - τ) := by
      rw [intervalIntegral.integral_of_le (by linarith [hτ.2]),
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ x : ℝ,
        (Icc (-1 + τ) 1).indicator
          (fun z ↦ p z * r (z - τ)) x :=
      (integral_indicator measurableSet_Icc).symm
    _ = ∫ x : ℝ,
        p x * factorTwoFixedLagLeftRepresenter τ r x := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ Icc (-1 + τ) 1
      · simp [factorTwoFixedLagLeftRepresenter, hx]
      · simp [factorTwoFixedLagLeftRepresenter, hx]
    _ = ∫ x : ℝ in Icc (-1 : ℝ) 1,
        p x * factorTwoFixedLagLeftRepresenter τ r x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x : ℝ in -1..1,
        p x * factorTwoFixedLagLeftRepresenter τ r x := by
      symm
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]

/-! ## Integrability and channel assembly -/

theorem intervalIntegrable_mul_factorTwoFixedLagRightRepresenter
    (τ : ℝ) (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r) :
    IntervalIntegrable
      (fun x ↦ factorTwoFixedLagRightRepresenter τ p x * r x)
      volume (-1) 1 := by
  let A : Set ℝ := Icc (-1 : ℝ) (1 - τ)
  let f : ℝ → ℝ := fun x ↦ p (τ + x) * r x
  have hf : Continuous f := by
    dsimp only [f]
    exact (hp.comp (by fun_prop)).mul hr
  have hOn : IntegrableOn f A := by
    exact hf.continuousOn.integrableOn_compact isCompact_Icc
  have hInd : Integrable (A.indicator f) :=
    hOn.integrable_indicator measurableSet_Icc
  have hEq : A.indicator f = fun x ↦
      factorTwoFixedLagRightRepresenter τ p x * r x := by
    funext x
    by_cases hx : x ∈ A
    · simp [A, f, factorTwoFixedLagRightRepresenter, hx]
    · simp [A, f, factorTwoFixedLagRightRepresenter, hx]
  rw [hEq] at hInd
  exact hInd.intervalIntegrable

theorem intervalIntegrable_mul_factorTwoFixedLagLeftRepresenter
    (τ : ℝ) (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r) :
    IntervalIntegrable
      (fun x ↦ p x * factorTwoFixedLagLeftRepresenter τ r x)
      volume (-1) 1 := by
  let A : Set ℝ := Icc (-1 + τ) 1
  let f : ℝ → ℝ := fun x ↦ p x * r (x - τ)
  have hf : Continuous f := by
    dsimp only [f]
    exact hp.mul (hr.comp (by fun_prop))
  have hOn : IntegrableOn f A := by
    exact hf.continuousOn.integrableOn_compact isCompact_Icc
  have hInd : Integrable (A.indicator f) :=
    hOn.integrable_indicator measurableSet_Icc
  have hEq : A.indicator f = fun x ↦
      p x * factorTwoFixedLagLeftRepresenter τ r x := by
    funext x
    by_cases hx : x ∈ A
    · simp [A, f, factorTwoFixedLagLeftRepresenter, hx]
    · simp [A, f, factorTwoFixedLagLeftRepresenter, hx]
  rw [hEq] at hInd
  exact hInd.intervalIntegrable

/-- The symmetric fixed-lag correlation is represented by `K`. -/
theorem correlationBilinear_eq_fixedLagK
    (τ : ℝ) (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r)
    (hτ : τ ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCorrelationBilinear p r τ =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        factorTwoFixedLagK τ p x * r x := by
  have hrightI :=
    intervalIntegrable_mul_factorTwoFixedLagRightRepresenter τ p r hp hr
  have hleftI :=
    intervalIntegrable_mul_factorTwoFixedLagLeftRepresenter τ r p hr hp
  have hpair :
      (∫ x : ℝ in -1..1,
          factorTwoFixedLagRightRepresenter τ p x * r x) +
        (∫ x : ℝ in -1..1,
          r x * factorTwoFixedLagLeftRepresenter τ p x) =
        ∫ x : ℝ in -1..1, factorTwoFixedLagK τ p x * r x := by
    rw [← intervalIntegral.integral_add hrightI hleftI]
    apply intervalIntegral.integral_congr
    intro x _hx
    unfold factorTwoFixedLagK
    ring
  unfold factorTwoCenteredCorrelationBilinear
  rw [crossCorrelation_eq_fixedLagRight τ p r hτ,
    crossCorrelation_eq_fixedLagLeft τ r p hτ,
    hpair]
  ring

/-- The ordered cross-difference at a fixed lag is represented by `J`. -/
theorem crossDifference_eq_fixedLagJ
    (τ : ℝ) (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (hτ : τ ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation o e τ -
        factorTwoCenteredCrossCorrelation e o τ =
      ∫ x : ℝ in -1..1, factorTwoFixedLagJ τ o x * e x := by
  have hrightI :=
    intervalIntegrable_mul_factorTwoFixedLagRightRepresenter τ o e ho he
  have hleftI :=
    intervalIntegrable_mul_factorTwoFixedLagLeftRepresenter τ e o he ho
  rw [crossCorrelation_eq_fixedLagRight τ o e hτ,
    crossCorrelation_eq_fixedLagLeft τ e o hτ,
    ← intervalIntegral.integral_sub hrightI hleftI]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold factorTwoFixedLagJ
  ring

/-- Equivalent cross-difference representation in the first profile. -/
theorem crossDifference_eq_neg_fixedLagJ
    (τ : ℝ) (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (hτ : τ ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation o e τ -
        factorTwoCenteredCrossCorrelation e o τ =
      -(∫ x : ℝ in -1..1, factorTwoFixedLagJ τ e x * o x) := by
  have hswap := crossDifference_eq_fixedLagJ τ o e ho he hτ
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoFixedLagRepresenterStructural
