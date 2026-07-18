import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenConstantEnclosuresStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenLowerMatrixStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenRobustCertificateStructural

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenEntryEnclosuresStructural

noncomputable section

open RatInterval
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenCleanPolynomialGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenConstantEnclosuresStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenLowerMatrixStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenPerturbationGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenRobustCertificateStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhasePerturbationConstantEnclosures
open YoshidaFactorTwoPhasePerturbationMomentSeries
open YoshidaFactorTwoPrimeTrigEnclosures
open YoshidaSineMomentEnclosures

/-!
# Exact entry enclosures and obstruction for the intrinsic even P6 endpoint matrices

The expressions below form a tiny exact arithmetic language.  Evaluating an
expression over reals gives the analytic matrix entry; evaluating the same
expression over rational intervals gives its enclosure.  Soundness is proved
once by structural induction, so the endpoint proof contains no sampling or
grid search.  The resulting enclosure of the first diagonal entry is strictly
negative for both proposed lower matrices.  Consequently these particular
matrices cannot supply the intended positive-definite endpoint certificate.
-/

inductive EndpointExpr where
  | rat (q : ℚ)
  | var (i : Fin 6)
  | neg (e : EndpointExpr)
  | add (e f : EndpointExpr)
  | sub (e f : EndpointExpr)
  | mul (e f : EndpointExpr)

namespace EndpointExpr

instance : Neg EndpointExpr := ⟨neg⟩
instance : Add EndpointExpr := ⟨add⟩
instance : Sub EndpointExpr := ⟨sub⟩
instance : Mul EndpointExpr := ⟨mul⟩

@[simp]
def evalReal (env : Fin 6 → ℝ) : EndpointExpr → ℝ
  | rat q => (q : ℝ)
  | var i => env i
  | neg e => -evalReal env e
  | add e f => evalReal env e + evalReal env f
  | sub e f => evalReal env e - evalReal env f
  | mul e f => evalReal env e * evalReal env f

@[simp]
def evalInterval (env : Fin 6 → RatInterval) : EndpointExpr → RatInterval
  | rat q => pure q
  | var i => env i
  | neg e => -evalInterval env e
  | add e f => evalInterval env e + evalInterval env f
  | sub e f => evalInterval env e - evalInterval env f
  | mul e f => evalInterval env e * evalInterval env f

/-- Scalar rational endpoints of the interval evaluator.  Keeping these as
one recursively computed pair lets `norm_num` normalize a rational endpoint
without first reducing projections through a large tree of interval
structures. -/
def evalBounds (env : Fin 6 → RatInterval) :
    EndpointExpr → ℚ × ℚ
  | rat q => (q, q)
  | var i => ((env i).lower, (env i).upper)
  | neg e =>
      let b := evalBounds env e
      (-b.2, -b.1)
  | add e f =>
      let b := evalBounds env e
      let c := evalBounds env f
      (b.1 + c.1, b.2 + c.2)
  | sub e f =>
      let b := evalBounds env e
      let c := evalBounds env f
      (b.1 - c.2, b.2 - c.1)
  | mul e f =>
      let b := evalBounds env e
      let c := evalBounds env f
      (min (min (b.1 * c.1) (b.1 * c.2))
          (min (b.2 * c.1) (b.2 * c.2)),
        max (max (b.1 * c.1) (b.1 * c.2))
          (max (b.2 * c.1) (b.2 * c.2)))

def evalLower (env : Fin 6 → RatInterval) (e : EndpointExpr) : ℚ :=
  (evalBounds env e).1

def evalUpper (env : Fin 6 → RatInterval) (e : EndpointExpr) : ℚ :=
  (evalBounds env e).2

theorem evalBounds_eq_evalInterval
    (env : Fin 6 → RatInterval) (e : EndpointExpr) :
    evalBounds env e =
      ((evalInterval env e).lower, (evalInterval env e).upper) := by
  induction e with
  | rat q => rfl
  | var i => rfl
  | neg e ih =>
      rw [evalBounds, ih]
      change (-(evalInterval env e).upper, -(evalInterval env e).lower) =
        ((RatInterval.neg (evalInterval env e)).lower,
          (RatInterval.neg (evalInterval env e)).upper)
      rfl
  | add e f ihe ihf =>
      rw [evalBounds, ihe, ihf]
      change ((evalInterval env e).lower + (evalInterval env f).lower,
          (evalInterval env e).upper + (evalInterval env f).upper) =
        ((RatInterval.add (evalInterval env e) (evalInterval env f)).lower,
          (RatInterval.add (evalInterval env e) (evalInterval env f)).upper)
      rfl
  | sub e f ihe ihf =>
      rw [evalBounds, ihe, ihf]
      change ((evalInterval env e).lower - (evalInterval env f).upper,
          (evalInterval env e).upper - (evalInterval env f).lower) =
        ((RatInterval.sub (evalInterval env e) (evalInterval env f)).lower,
          (RatInterval.sub (evalInterval env e) (evalInterval env f)).upper)
      rfl
  | mul e f ihe ihf =>
      rw [evalBounds, ihe, ihf]
      change
        (min
              (min ((evalInterval env e).lower * (evalInterval env f).lower)
                ((evalInterval env e).lower * (evalInterval env f).upper))
              (min ((evalInterval env e).upper * (evalInterval env f).lower)
                ((evalInterval env e).upper * (evalInterval env f).upper)),
          max
              (max ((evalInterval env e).lower * (evalInterval env f).lower)
                ((evalInterval env e).lower * (evalInterval env f).upper))
              (max ((evalInterval env e).upper * (evalInterval env f).lower)
                ((evalInterval env e).upper * (evalInterval env f).upper))) =
        ((RatInterval.mul (evalInterval env e) (evalInterval env f)).lower,
          (RatInterval.mul (evalInterval env e) (evalInterval env f)).upper)
      rfl

@[simp]
theorem evalLower_eq_evalInterval
    (env : Fin 6 → RatInterval) (e : EndpointExpr) :
    evalLower env e = (evalInterval env e).lower := by
  exact congrArg Prod.fst (evalBounds_eq_evalInterval env e)

@[simp]
theorem evalUpper_eq_evalInterval
    (env : Fin 6 → RatInterval) (e : EndpointExpr) :
    evalUpper env e = (evalInterval env e).upper := by
  exact congrArg Prod.snd (evalBounds_eq_evalInterval env e)

def pow (e : EndpointExpr) : ℕ → EndpointExpr
  | 0 => rat 1
  | n + 1 => pow e n * e

@[simp]
theorem evalReal_pow (env : Fin 6 → ℝ) (e : EndpointExpr) :
    ∀ n, evalReal env (pow e n) = evalReal env e ^ n := by
  intro n
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow, ih, pow_succ]

theorem evalInterval_contains
    {realEnv : Fin 6 → ℝ} {intervalEnv : Fin 6 → RatInterval}
    (henv : ∀ i, (intervalEnv i).Contains (realEnv i)) :
    ∀ e, (evalInterval intervalEnv e).Contains (evalReal realEnv e) := by
  intro e
  induction e with
  | rat q => exact contains_pure q
  | var i => exact henv i
  | neg e ih => exact contains_neg ih
  | add e f ihe ihf => exact contains_add ihe ihf
  | sub e f ihe ihf => exact contains_sub ihe ihf
  | mul e f ihe ihf => exact contains_mul ihe ihf

end EndpointExpr

/-! ## The six analytic constants -/

def factorTwoP6EvenRealEnvironment : Fin 6 → ℝ :=
  ![yoshidaEndpointA, Real.log 2, yoshidaEndpointScalarMassLoss,
    Real.log 2 / Real.sqrt 2, Real.log 3 / Real.sqrt 3,
    factorTwoP6EvenPrimeHeight]

def factorTwoP6EvenIntervalEnvironment : Fin 6 → RatInterval :=
  ![factorTwoP6EvenEndpointAInterval, logTwoFineInterval,
    factorTwoP6EvenScalarMassInterval,
    factorTwoP6EvenPrimeTwoCoefficientInterval,
    factorTwoPrimeBetaInterval, factorTwoP6EvenPrimeHeightInterval]

theorem factorTwoP6EvenIntervalEnvironment_contains (i : Fin 6) :
    (factorTwoP6EvenIntervalEnvironment i).Contains
      (factorTwoP6EvenRealEnvironment i) := by
  fin_cases i
  · simpa [factorTwoP6EvenIntervalEnvironment,
      factorTwoP6EvenRealEnvironment] using
      factorTwoP6EvenEndpointAInterval_contains
  · simpa [factorTwoP6EvenIntervalEnvironment,
      factorTwoP6EvenRealEnvironment,
      YoshidaOddGramPrefix.yoshidaLength] using
      logTwoFineInterval_contains
  · simpa [factorTwoP6EvenIntervalEnvironment,
      factorTwoP6EvenRealEnvironment] using
      factorTwoP6EvenScalarMassInterval_contains
  · simpa [factorTwoP6EvenIntervalEnvironment,
      factorTwoP6EvenRealEnvironment] using
      factorTwoP6EvenPrimeTwoCoefficientInterval_contains
  · simpa [factorTwoP6EvenIntervalEnvironment,
      factorTwoP6EvenRealEnvironment] using
      factorTwoPrimeBetaInterval_contains
  · simpa [factorTwoP6EvenIntervalEnvironment,
      factorTwoP6EvenRealEnvironment] using
      factorTwoP6EvenPrimeHeightInterval_contains

/-- The same six intervals with all positive interval divisions already
resolved to their rational endpoints.  This is definitionally convenient for
the final `norm_num` certificates. -/
private def factorTwoP6EvenNormalizedIntervalEnvironment :
    Fin 6 → RatInterval :=
  ![⟨(69314718055 / 100000000000 : ℚ) / 2,
      (69314718057 / 100000000000 : ℚ) / 2⟩,
    ⟨69314718055 / 100000000000, 69314718057 / 100000000000⟩,
    ⟨13554324 / 10000000, 13554329 / 10000000⟩,
    ⟨(69314718055 / 100000000000 : ℚ) /
        (1414213562373096 / 1000000000000000),
      (69314718057 / 100000000000 : ℚ) /
        (1414213562373095 / 1000000000000000)⟩,
    ⟨((69314718055994 / 100000000000000 : ℚ) +
          40546510810816 / 100000000000000) /
        (1732050807568878 / 1000000000000000),
      ((69314718055995 / 100000000000000 : ℚ) +
          40546510810817 / 100000000000000) /
        (1732050807568877 / 1000000000000000)⟩,
    ⟨(2 * (40546510810816 / 100000000000000 : ℚ)) /
        (69314718055995 / 100000000000000),
      (2 * (40546510810817 / 100000000000000 : ℚ)) /
        (69314718055994 / 100000000000000)⟩]

private theorem ratIntervalMul_expanded (I J : RatInterval) :
    I * J =
      ⟨min (min (I.lower * J.lower) (I.lower * J.upper))
          (min (I.upper * J.lower) (I.upper * J.upper)),
        max (max (I.lower * J.lower) (I.lower * J.upper))
          (max (I.upper * J.lower) (I.upper * J.upper))⟩ := by
  rfl

private theorem ratIntervalDiv_expanded (I J : RatInterval) :
    I / J =
      ⟨min (min (I.lower * J.upper⁻¹) (I.lower * J.lower⁻¹))
          (min (I.upper * J.upper⁻¹) (I.upper * J.lower⁻¹)),
        max (max (I.lower * J.upper⁻¹) (I.lower * J.lower⁻¹))
          (max (I.upper * J.upper⁻¹) (I.upper * J.lower⁻¹))⟩ := by
  rfl

private theorem ratIntervalAdd_expanded (I J : RatInterval) :
    I + J = ⟨I.lower + J.lower, I.upper + J.upper⟩ := by
  rfl

private theorem ratIntervalSub_expanded (I J : RatInterval) :
    I - J = ⟨I.lower - J.upper, I.upper - J.lower⟩ := by
  rfl

private theorem matrixCons_val_five {m : ℕ} {R : Type*}
    (x : R) (u : Fin m.succ.succ.succ.succ.succ → R) :
    Matrix.vecCons x u 5 =
      Matrix.vecHead
        (Matrix.vecTail
          (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))) := by
  rfl

private theorem factorTwoP6EvenNormalizedIntervalEnvironment_eq :
    factorTwoP6EvenNormalizedIntervalEnvironment =
      factorTwoP6EvenIntervalEnvironment := by
  funext i
  fin_cases i <;>
    norm_num [factorTwoP6EvenNormalizedIntervalEnvironment,
      factorTwoP6EvenIntervalEnvironment,
      factorTwoP6EvenEndpointAInterval,
      factorTwoP6EvenScalarMassInterval,
      factorTwoP6EvenPrimeTwoCoefficientInterval,
      factorTwoP6EvenPrimeHeightInterval,
      factorTwoPrimeBetaInterval, factorTwoPrimeLogThreeInterval,
      factorTwoPrimeSqrtThreeInterval,
      factorTwoPrimeAffineHeightInterval,
      factorTwoPrimeLogTwoInterval, factorTwoPrimeShiftInterval,
      logTwoFineInterval, sqrtTwoInterval,
      ratIntervalDiv_expanded, ratIntervalMul_expanded,
      ratIntervalAdd_expanded, ratIntervalSub_expanded,
      RatInterval.pure]

/-! ## Expression constructors -/

private def Q (q : ℚ) : EndpointExpr := .rat q
private def A : EndpointExpr := .var 0
private def L : EndpointExpr := .var 1
private def M : EndpointExpr := .var 2
private def B₂ : EndpointExpr := .var 3
private def B₃ : EndpointExpr := .var 4
private def T : EndpointExpr := .var 5
private def P (e : EndpointExpr) (n : ℕ) : EndpointExpr := e.pow n

private def symmetricExprMatrix
    (q00 q02 q04 q06 q22 q24 q26 q44 q46 q66 : EndpointExpr) :
    Matrix (Fin 4) (Fin 4) EndpointExpr :=
  !![q00, q02, q04, q06;
    q02, q22, q24, q26;
    q04, q24, q44, q46;
    q06, q26, q46, q66]

private def corr00 (x : EndpointExpr) : EndpointExpr := Q 2 - x

private def corr02 (x : EndpointExpr) : EndpointExpr :=
  -(x * (x - Q 2) * (x - Q 1)) * Q (1 / 2)

private def corr22 (x : EndpointExpr) : EndpointExpr :=
  -((x - Q 2) *
    (Q 3 * P x 4 + Q 6 * P x 3 - Q 8 * P x 2 - Q 16 * x + Q 8)) *
      Q (1 / 40)

private def corr04 (x : EndpointExpr) : EndpointExpr :=
  -(x * (x - Q 2) * (x - Q 1) *
    (Q 7 * P x 2 - Q 14 * x + Q 4)) * Q (1 / 8)

private def corr24 (x : EndpointExpr) : EndpointExpr :=
  -(x * (x - Q 2) *
    (P x 5 + Q 2 * P x 4 - Q 6 * P x 3 - Q 12 * P x 2 +
      Q 24 * x - Q 8)) * Q (1 / 16)

private def corr44 (x : EndpointExpr) : EndpointExpr :=
  -((x - Q 2) *
    (Q 35 * P x 8 + Q 70 * P x 7 - Q 220 * P x 6 -
      Q 440 * P x 5 + Q 416 * P x 4 + Q 832 * P x 3 -
      Q 256 * P x 2 - Q 512 * x + Q 128)) * Q (1 / 1152)

private def corr06 (x : EndpointExpr) : EndpointExpr :=
  -(x * (x - Q 2) * (x - Q 1) *
    (Q 33 * P x 4 - Q 132 * P x 3 + Q 168 * P x 2 -
      Q 72 * x + Q 8)) * Q (1 / 16)

private def corr26 (x : EndpointExpr) : EndpointExpr :=
  -(x * (x - Q 2) *
    (Q 11 * P x 7 + Q 22 * P x 6 - Q 124 * P x 5 -
      Q 248 * P x 4 + Q 1184 * P x 3 - Q 1328 * P x 2 +
      Q 544 * x - Q 64)) * Q (1 / 128)

private def corr46 (x : EndpointExpr) : EndpointExpr :=
  -(x * (x - Q 2) *
    (Q 7 * P x 9 + Q 14 * P x 8 - Q 62 * P x 7 -
      Q 124 * P x 6 + Q 200 * P x 5 + Q 400 * P x 4 -
      Q 320 * P x 3 - Q 640 * P x 2 + Q 640 * x - Q 128)) *
        Q (1 / 256)

private def corr66 (x : EndpointExpr) : EndpointExpr :=
  -((x - Q 2) *
    (Q 231 * P x 12 + Q 462 * P x 11 - Q 2352 * P x 10 -
      Q 4704 * P x 9 + Q 8792 * P x 8 + Q 17584 * P x 7 -
      Q 14752 * P x 6 - Q 29504 * P x 5 + Q 10880 * P x 4 +
      Q 21760 * P x 3 - Q 3072 * P x 2 - Q 6144 * x + Q 1024)) *
        Q (1 / 13312)

/-! ## Clean and retained hyperbolic expressions -/

private def regular00 : EndpointExpr :=
  Q 1 - Q (1 / 18) * A - Q (1 / 12) * P A 2 +
    Q (7 / 3600) * P A 3 + Q (1 / 72) * P A 4 -
    Q (31 / 317520) * P A 5 - Q (61 / 20160) * P A 6

private def regular02 : EndpointExpr :=
  -(Q (1 / 180) * A) - Q (1 / 60) * P A 2 +
    Q (1 / 1800) * P A 3 + Q (5 / 1008) * P A 4 -
    Q (31 / 762048) * P A 5 - Q (61 / 43200) * P A 6

private def regular04 : EndpointExpr :=
  Q (1 / 64800) * P A 3 + Q (1 / 3024) * P A 4 -
    Q (31 / 6985440) * P A 5 - Q (61 / 285120) * P A 6

private def regular06 : EndpointExpr :=
  -(Q (31 / 544864320) * P A 5) - Q (61 / 8648640) * P A 6

private def regular22 : EndpointExpr :=
  Q (1 / 630) * A + Q (1 / 10800) * P A 3 +
    Q (1 / 720) * P A 4 - Q (31 / 2095632) * P A 5 -
    Q (61 / 100800) * P A 6

private def regular24 : EndpointExpr :=
  -(Q (1 / 3780) * A) - Q (1 / 178200) * P A 3 -
    Q (31 / 36324288) * P A 5 - Q (61 / 907200) * P A 6

private def regular26 : EndpointExpr :=
  Q (1 / 3088800) * P A 3 + Q (31 / 1362160800) * P A 5

private def regular44 : EndpointExpr :=
  Q (1 / 4158) * A + Q (1 / 514800) * P A 3 +
    Q (31 / 408648240) * P A 5

private def regular46 : EndpointExpr :=
  -(Q (1 / 15444) * A) - Q (1 / 2316600) * P A 3 -
    Q (31 / 3087564480) * P A 5

private def regular66 : EndpointExpr :=
  Q (1 / 12870) * A + Q (7 / 26254800) * P A 3 +
    Q (31 / 8799558768) * P A 5

private def cleanExprMatrix : Matrix (Fin 4) (Fin 4) EndpointExpr :=
  symmetricExprMatrix
    (Q 2 - Q 2 * L - Q 2 * M - A * regular00)
    (Q (1 / 3) - A * regular02)
    (Q (1 / 10) - A * regular04)
    (Q (1 / 21) - A * regular06)
    (Q (3 / 5) + (Q (41 / 75) - Q (2 / 5) * L) -
      Q (2 / 5) * M - A * regular22)
    (Q (1 / 7) - A * regular24)
    (Q (1 / 18) - A * regular26)
    (Q (25 / 54) + (Q (1739 / 5670) - Q (2 / 9) * L) -
      Q (2 / 9) * M - A * regular44)
    (Q (1 / 11) - A * regular46)
    (Q (49 / 130) + (Q (249251 / 1171170) - Q (2 / 13) * L) -
      Q (2 / 13) * M - A * regular66)

private def cosh0 : EndpointExpr :=
  Q 2 + Q (1 / 12) * P A 2 + Q (1 / 960) * P A 4 +
    Q (1 / 161280) * P A 6

private def cosh2 : EndpointExpr :=
  Q (1 / 30) * P A 2 + Q (1 / 1680) * P A 4 +
    Q (1 / 241920) * P A 6

private def cosh4 : EndpointExpr :=
  Q (1 / 7560) * P A 4 + Q (1 / 665280) * P A 6

private def cosh6 : EndpointExpr := Q (1 / 4324320) * P A 6

private def hyperError : EndpointExpr :=
  Q 4 * A * Q (1 / 48000000000) * Q (1 / 48000000000)

private def hyperExprMatrix : Matrix (Fin 4) (Fin 4) EndpointExpr :=
  symmetricExprMatrix
    (A * cosh0 * cosh0 - hyperError * Q 2)
    (A * cosh0 * cosh2)
    (A * cosh0 * cosh4)
    (A * cosh0 * cosh6)
    (A * cosh2 * cosh2 - hyperError * Q (2 / 5))
    (A * cosh2 * cosh4)
    (A * cosh2 * cosh6)
    (A * cosh4 * cosh4 - hyperError * Q (2 / 9))
    (A * cosh4 * cosh6)
    (A * cosh6 * cosh6 - hyperError * Q (2 / 13))

private def chargeCoefficient : EndpointExpr :=
  Q (1 / 250000) * A + Q (3 / 40000)

private def chargeExprMatrix : Matrix (Fin 4) (Fin 4) EndpointExpr :=
  symmetricExprMatrix
    (Q 2 * chargeCoefficient) (Q 0) (Q 0) (Q 0)
    (Q (2 / 5) * chargeCoefficient) (Q 0) (Q 0)
    (Q (2 / 9) * chargeCoefficient) (Q 0)
    (Q (2 / 13) * chargeCoefficient)

/-! ## Perturbation expressions -/

private def poleFree0 : EndpointExpr :=
  Q (7 / 2) * A + Q (1 / 12) * P A 2 + Q (9 / 4) * P A 3 -
    Q (7 / 720) * P A 4 + Q (1 / 16) * P A 5 +
    Q (31 / 30240) * P A 6 + Q (23 / 480) * P A 7

private def poleFree2 : EndpointExpr :=
  Q (9 / 16) * P A 3 - Q (7 / 960) * P A 4 +
    Q (3 / 32) * P A 5 + Q (31 / 12096) * P A 6 +
    Q (23 / 128) * P A 7

private def poleFree4 : EndpointExpr :=
  Q (1 / 256) * P A 5 + Q (31 / 96768) * P A 6 +
    Q (23 / 512) * P A 7

private def poleFree6 : EndpointExpr :=
  Q (23 / 30720) * P A 7

private def kernelExprMatrix : Matrix (Fin 4) (Fin 4) EndpointExpr :=
  symmetricExprMatrix
    (Q 2 * poleFree0 + Q (4 / 3) * poleFree2 +
      Q (32 / 15) * poleFree4 + Q (32 / 7) * poleFree6)
    (Q (4 / 15) * poleFree2 + Q (16 / 21) * poleFree4 +
      Q (32 / 15) * poleFree6)
    (Q (16 / 315) * poleFree4 + Q (32 / 99) * poleFree6)
    (Q (32 / 3003) * poleFree6)
    (Q (16 / 75) * poleFree4 + Q (32 / 35) * poleFree6)
    (Q (32 / 315) * poleFree6)
    (Q 0) (Q 0) (Q 0) (Q 0)

private def reflectedExprMatrix : Matrix (Fin 4) (Fin 4) EndpointExpr :=
  symmetricExprMatrix
    (-(Q 2 * L))
    (Q 4 - Q 6 * L)
    (Q (187 / 3) - Q 90 * L)
    (Q (6259 / 5) - Q 1806 * L)
    (Q (1 / 5) - Q (2 / 5) * L)
    (Q (29 / 3) - Q 14 * L)
    (Q (2071 / 6) - Q 498 * L)
    (Q (7 / 54) - Q (2 / 9) * L)
    (Q (457 / 30) - Q 22 * L)
    (Q (37 / 390) - Q (2 / 13) * L)

private def primeTwoExprMatrix : Matrix (Fin 4) (Fin 4) EndpointExpr :=
  symmetricExprMatrix
    (-(B₂ * Q 2)) (Q 0) (Q 0) (Q 0)
    (-(B₂ * Q (2 / 5))) (Q 0) (Q 0)
    (-(B₂ * Q (2 / 9))) (Q 0)
    (-(B₂ * Q (2 / 13)))

private def primeThreeExprMatrix : Matrix (Fin 4) (Fin 4) EndpointExpr :=
  symmetricExprMatrix
    (-(B₃ * corr00 T))
    (-(B₃ * corr02 T))
    (-(B₃ * corr04 T))
    (-(B₃ * corr06 T))
    (-(B₃ * corr22 T))
    (-(B₃ * corr24 T))
    (-(B₃ * corr26 T))
    (-(B₃ * corr44 T))
    (-(B₃ * corr46 T))
    (-(B₃ * corr66 T))

private def perturbExprMatrix : Matrix (Fin 4) (Fin 4) EndpointExpr :=
  kernelExprMatrix + reflectedExprMatrix +
    primeTwoExprMatrix + primeThreeExprMatrix

private def plusExprMatrix : Matrix (Fin 4) (Fin 4) EndpointExpr :=
  cleanExprMatrix + hyperExprMatrix + perturbExprMatrix - chargeExprMatrix

private def minusExprMatrix : Matrix (Fin 4) (Fin 4) EndpointExpr :=
  cleanExprMatrix + hyperExprMatrix - perturbExprMatrix - chargeExprMatrix

/-! ## Exact real evaluation -/

private theorem corr00_eval :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment (corr00 T) =
      evenStructuralCorrelation00 factorTwoP6EvenPrimeHeight := by
  simp [corr00, Q, T, factorTwoP6EvenRealEnvironment,
    evenStructuralCorrelation00]

private theorem corr02_eval :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment (corr02 T) =
      evenStructuralCorrelation02 factorTwoP6EvenPrimeHeight := by
  simp [corr02, Q, T, factorTwoP6EvenRealEnvironment,
    evenStructuralCorrelation02]
  ring

private theorem corr22_eval :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment (corr22 T) =
      evenStructuralCorrelation22 factorTwoP6EvenPrimeHeight := by
  simp [corr22, Q, T, P, factorTwoP6EvenRealEnvironment,
    evenStructuralCorrelation22]
  ring

private theorem corr04_eval :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment (corr04 T) =
      factorTwoIntrinsicP4Correlation04 factorTwoP6EvenPrimeHeight := by
  simp [corr04, Q, T, P, factorTwoP6EvenRealEnvironment,
    factorTwoIntrinsicP4Correlation04]
  ring

private theorem corr24_eval :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment (corr24 T) =
      factorTwoIntrinsicP4Correlation24 factorTwoP6EvenPrimeHeight := by
  simp [corr24, Q, T, P, factorTwoP6EvenRealEnvironment,
    factorTwoIntrinsicP4Correlation24]
  ring

private theorem corr44_eval :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment (corr44 T) =
      factorTwoIntrinsicP4Correlation44 factorTwoP6EvenPrimeHeight := by
  simp [corr44, Q, T, P, factorTwoP6EvenRealEnvironment,
    factorTwoIntrinsicP4Correlation44]
  ring

private theorem corr06_eval :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment (corr06 T) =
      factorTwoIntrinsicP6Correlation06 factorTwoP6EvenPrimeHeight := by
  simp [corr06, Q, T, P, factorTwoP6EvenRealEnvironment,
    factorTwoIntrinsicP6Correlation06]
  ring

private theorem corr26_eval :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment (corr26 T) =
      factorTwoIntrinsicP6Correlation26 factorTwoP6EvenPrimeHeight := by
  simp [corr26, Q, T, P, factorTwoP6EvenRealEnvironment,
    factorTwoIntrinsicP6Correlation26]
  ring

private theorem corr46_eval :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment (corr46 T) =
      factorTwoIntrinsicP6Correlation46 factorTwoP6EvenPrimeHeight := by
  simp [corr46, Q, T, P, factorTwoP6EvenRealEnvironment,
    factorTwoIntrinsicP6Correlation46]
  ring

private theorem corr66_eval :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment (corr66 T) =
      factorTwoIntrinsicP6Correlation66 factorTwoP6EvenPrimeHeight := by
  simp [corr66, Q, T, P, factorTwoP6EvenRealEnvironment,
    factorTwoIntrinsicP6Correlation66]
  ring

private theorem cleanExprMatrix_evalReal (i j : Fin 4) :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment
        (cleanExprMatrix i j) =
      factorTwoP6EvenNonHyperbolicCleanMatrix i j := by
  fin_cases i <;> fin_cases j <;>
    simp [cleanExprMatrix, symmetricExprMatrix, Q, A, L, M, P,
      regular00, regular02, regular04, regular06, regular22,
      regular24, regular26, regular44, regular46, regular66,
      factorTwoP6EvenRealEnvironment,
      factorTwoP6EvenNonHyperbolicCleanMatrix,
      factorTwoP6EvenPolarizedMatrix,
      factorTwoP6EvenCleanPolynomialGram00,
      factorTwoP6EvenCleanPolynomialGram02,
      factorTwoP6EvenCleanPolynomialGram04,
      factorTwoP6EvenCleanPolynomialGram06,
      factorTwoP6EvenCleanPolynomialGram22,
      factorTwoP6EvenCleanPolynomialGram24,
      factorTwoP6EvenCleanPolynomialGram26,
      factorTwoP6EvenCleanPolynomialGram44,
      factorTwoP6EvenCleanPolynomialGram46,
      factorTwoP6EvenCleanPolynomialGram66,
      factorTwoP6EvenRegularGram00, factorTwoP6EvenRegularGram02,
      factorTwoP6EvenRegularGram04, factorTwoP6EvenRegularGram06,
      factorTwoP6EvenRegularGram22, factorTwoP6EvenRegularGram24,
      factorTwoP6EvenRegularGram26, factorTwoP6EvenRegularGram44,
      factorTwoP6EvenRegularGram46, factorTwoP6EvenRegularGram66] <;>
    ring <;> simp

private theorem hyperExprMatrix_evalReal (i j : Fin 4) :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment
        (hyperExprMatrix i j) =
      factorTwoP6EvenRetainedHyperbolicMatrix i j := by
  fin_cases i <;> fin_cases j <;>
    simp [hyperExprMatrix, symmetricExprMatrix, hyperError,
      cosh0, cosh2, cosh4, cosh6, Q, A, P,
      factorTwoP6EvenRealEnvironment,
      factorTwoP6EvenRetainedHyperbolicMatrix,
      factorTwoP6EvenPolarizedMatrix,
      factorTwoP6EvenCoshCoordinate0, factorTwoP6EvenCoshCoordinate2,
      factorTwoP6EvenCoshCoordinate4, factorTwoP6EvenCoshCoordinate6] <;>
    ring

private theorem chargeExprMatrix_evalReal (i j : Fin 4) :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment
        (chargeExprMatrix i j) =
      factorTwoP6EvenEndpointEnergyChargeMatrix i j := by
  fin_cases i <;> fin_cases j <;>
    simp [chargeExprMatrix, symmetricExprMatrix, chargeCoefficient,
      Q, A, factorTwoP6EvenRealEnvironment,
      factorTwoP6EvenEndpointEnergyChargeMatrix,
      factorTwoP6EvenEnergyMatrix, factorTwoP6EvenPolarizedMatrix] <;>
    ring

private theorem perturbExprMatrix_evalReal (i j : Fin 4) :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment
        (perturbExprMatrix i j) =
      factorTwoP6EvenPerturbationGramMatrix i j := by
  fin_cases i <;> fin_cases j <;>
    simp [perturbExprMatrix, kernelExprMatrix, reflectedExprMatrix,
      primeTwoExprMatrix, primeThreeExprMatrix, symmetricExprMatrix,
      poleFree0, poleFree2, poleFree4, poleFree6,
      Q, A, L, B₂, B₃, P, factorTwoP6EvenRealEnvironment,
      factorTwoP6EvenPerturbationGramMatrix,
      factorTwoP6EvenDegreeSixKernelGramMatrix,
      factorTwoP6EvenReflectedPoleGramMatrix,
      factorTwoP6EvenPrimeTwoAtomGramMatrix,
      factorTwoP6EvenPrimeThreeAtomGramMatrix,
      factorTwoP6EvenSymmetricMatrix,
      poleFreeCoeff0, poleFreeCoeff2, poleFreeCoeff4, poleFreeCoeff6,
      corr00, corr02, corr04, corr06, corr22, corr24, corr26, corr44,
      corr46, corr66, T,
      evenStructuralCorrelation00, evenStructuralCorrelation02,
      evenStructuralCorrelation22,
      factorTwoIntrinsicP4Correlation04,
      factorTwoIntrinsicP4Correlation24,
      factorTwoIntrinsicP4Correlation44,
      factorTwoIntrinsicP6Correlation06,
      factorTwoIntrinsicP6Correlation26,
      factorTwoIntrinsicP6Correlation46,
      factorTwoIntrinsicP6Correlation66] <;>
    ring

private theorem plusExprMatrix_evalReal (i j : Fin 4) :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment
        (plusExprMatrix i j) =
      factorTwoP6EvenPlusLowerMatrix i j := by
  simp [plusExprMatrix, factorTwoP6EvenPlusLowerMatrix,
    cleanExprMatrix_evalReal, hyperExprMatrix_evalReal,
    perturbExprMatrix_evalReal, chargeExprMatrix_evalReal]

private theorem minusExprMatrix_evalReal (i j : Fin 4) :
    EndpointExpr.evalReal factorTwoP6EvenRealEnvironment
        (minusExprMatrix i j) =
      factorTwoP6EvenMinusLowerMatrix i j := by
  simp [minusExprMatrix, factorTwoP6EvenMinusLowerMatrix,
    cleanExprMatrix_evalReal, hyperExprMatrix_evalReal,
    perturbExprMatrix_evalReal, chargeExprMatrix_evalReal]

/-! ## Rational interval certificates -/

private theorem plusExprMatrix_contains (i j : Fin 4) :
    (EndpointExpr.evalInterval factorTwoP6EvenIntervalEnvironment
        (plusExprMatrix i j)).Contains
      (factorTwoP6EvenPlusLowerMatrix i j) := by
  have h := EndpointExpr.evalInterval_contains
    factorTwoP6EvenIntervalEnvironment_contains (plusExprMatrix i j)
  simpa only [plusExprMatrix_evalReal] using h

private theorem minusExprMatrix_contains (i j : Fin 4) :
    (EndpointExpr.evalInterval factorTwoP6EvenIntervalEnvironment
        (minusExprMatrix i j)).Contains
      (factorTwoP6EvenMinusLowerMatrix i j) := by
  have h := EndpointExpr.evalInterval_contains
    factorTwoP6EvenIntervalEnvironment_contains (minusExprMatrix i j)
  simpa only [minusExprMatrix_evalReal] using h

macro "p6_plus_interval_norm" : tactic =>
  `(tactic|
    norm_num [EndpointExpr.evalLower, EndpointExpr.evalUpper,
      EndpointExpr.evalBounds, EndpointExpr.pow,
      plusExprMatrix, cleanExprMatrix, hyperExprMatrix,
      perturbExprMatrix, chargeExprMatrix, kernelExprMatrix,
      reflectedExprMatrix, primeTwoExprMatrix, primeThreeExprMatrix,
      symmetricExprMatrix, regular00, regular02, regular04, regular06,
      regular22, regular24, regular26, regular44, regular46, regular66,
      cosh0, cosh2, cosh4, cosh6, hyperError, chargeCoefficient,
      poleFree0, poleFree2, poleFree4, poleFree6,
      corr00, corr02, corr04, corr06, corr22, corr24, corr26, corr44,
      corr46, corr66, Q, A, L, M, B₂, B₃, T, P,
      factorTwoP6EvenNormalizedIntervalEnvironment,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      matrixCons_val_five, Matrix.cons_val_succ, Matrix.vecHead,
      Matrix.vecTail, Fin.ext_iff])

macro "p6_minus_interval_norm" : tactic =>
  `(tactic|
    norm_num [EndpointExpr.evalLower, EndpointExpr.evalUpper,
      EndpointExpr.evalBounds, EndpointExpr.pow,
      minusExprMatrix, cleanExprMatrix, hyperExprMatrix,
      perturbExprMatrix, chargeExprMatrix, kernelExprMatrix,
      reflectedExprMatrix, primeTwoExprMatrix, primeThreeExprMatrix,
      symmetricExprMatrix, regular00, regular02, regular04, regular06,
      regular22, regular24, regular26, regular44, regular46, regular66,
      cosh0, cosh2, cosh4, cosh6, hyperError, chargeCoefficient,
      poleFree0, poleFree2, poleFree4, poleFree6,
      corr00, corr02, corr04, corr06, corr22, corr24, corr26, corr44,
      corr46, corr66, Q, A, L, M, B₂, B₃, T, P,
      factorTwoP6EvenNormalizedIntervalEnvironment,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      matrixCons_val_five, Matrix.cons_val_succ, Matrix.vecHead,
      Matrix.vecTail, Fin.ext_iff])

private theorem plusExprMatrix_zero_zero_upper_neg :
    EndpointExpr.evalUpper factorTwoP6EvenNormalizedIntervalEnvironment
        (plusExprMatrix 0 0) < 0 := by
  p6_plus_interval_norm

private theorem minusExprMatrix_zero_zero_upper_neg :
    EndpointExpr.evalUpper factorTwoP6EvenNormalizedIntervalEnvironment
        (minusExprMatrix 0 0) < 0 := by
  p6_minus_interval_norm

theorem factorTwoP6EvenPlusLowerMatrix_zero_zero_neg :
    factorTwoP6EvenPlusLowerMatrix 0 0 < 0 := by
  have hcontains := plusExprMatrix_contains 0 0
  have hupperRat :
      (EndpointExpr.evalInterval factorTwoP6EvenIntervalEnvironment
          (plusExprMatrix 0 0)).upper < 0 := by
    rw [← EndpointExpr.evalUpper_eq_evalInterval,
      ← factorTwoP6EvenNormalizedIntervalEnvironment_eq]
    exact plusExprMatrix_zero_zero_upper_neg
  have hupper :
      ((EndpointExpr.evalInterval factorTwoP6EvenIntervalEnvironment
          (plusExprMatrix 0 0)).upper : ℝ) < 0 := by
    exact_mod_cast hupperRat
  exact lt_of_le_of_lt hcontains.2 hupper

theorem factorTwoP6EvenMinusLowerMatrix_zero_zero_neg :
    factorTwoP6EvenMinusLowerMatrix 0 0 < 0 := by
  have hcontains := minusExprMatrix_contains 0 0
  have hupperRat :
      (EndpointExpr.evalInterval factorTwoP6EvenIntervalEnvironment
          (minusExprMatrix 0 0)).upper < 0 := by
    rw [← EndpointExpr.evalUpper_eq_evalInterval,
      ← factorTwoP6EvenNormalizedIntervalEnvironment_eq]
    exact minusExprMatrix_zero_zero_upper_neg
  have hupper :
      ((EndpointExpr.evalInterval factorTwoP6EvenIntervalEnvironment
          (minusExprMatrix 0 0)).upper : ℝ) < 0 := by
    exact_mod_cast hupperRat
  exact lt_of_le_of_lt hcontains.2 hupper

theorem factorTwoP6EvenPlusLowerMatrix_not_posDef :
    ¬ factorTwoP6EvenPlusLowerMatrix.PosDef := by
  intro h
  exact (not_lt_of_ge (le_of_lt factorTwoP6EvenPlusLowerMatrix_zero_zero_neg))
    h.diag_pos

theorem factorTwoP6EvenMinusLowerMatrix_not_posDef :
    ¬ factorTwoP6EvenMinusLowerMatrix.PosDef := by
  intro h
  exact (not_lt_of_ge (le_of_lt factorTwoP6EvenMinusLowerMatrix_zero_zero_neg))
    h.diag_pos

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenEntryEnclosuresStructural
