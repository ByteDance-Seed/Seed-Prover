-- In carleson/Carleson/Defs.lean

import Carleson.ToMathlib.DoublingMeasure
import Carleson.ToMathlib.WeakType
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star

open MeasureTheory Measure NNReal Metric Complex Set TopologicalSpace Bornology Function
open scoped ENNReal
noncomputable section

-- todo: rename and protect `Real.RCLike`

/-! Miscellaneous definitions.
These are mostly the definitions used to state the metric Carleson theorem.
We should move them to separate files once we start proving things about them. -/

section DoublingMeasure
universe u

variable {𝕜 X : Type*} {A : ℕ} [_root_.RCLike 𝕜] [PseudoMetricSpace X]

section localOscillation

/-- The local oscillation of two functions w.r.t. a set `E`. This is `d_E` in the blueprint. -/
def localOscillation (E : Set X) (f g : C(X, 𝕜)) : ℝ≥0∞ :=
  ⨆ z ∈ E ×ˢ E, ENNReal.ofReal ‖f z.1 - g z.1 - f z.2 + g z.2‖

-- example (E : Set X) (hE : IsBounded E) (f : C(X, ℝ)) :
--     BddAbove (range fun z : E ↦ f z) := by
--   have : IsCompact (closure E) := IsBounded.isCompact_closure hE
--   sorry

-- lemma bddAbove_localOscillation (E : Set X) [Fact (IsBounded E)] (f g : C(X, 𝕜)) :
--     BddAbove ((fun z : X × X ↦ ‖f z.1 - g z.1 - f z.2 + g z.2‖) '' E ×ˢ E) := sorry

variable {E : Set X} {f g : C(X, 𝕜)}

--old
/-- A ball w.r.t. the distance `localOscillation` -/
def localOscillationBall (E : Set X) (f : C(X, 𝕜)) (r : ℝ) :
    Set C(X, 𝕜) :=
  { g : C(X, 𝕜) | localOscillation E f g < ENNReal.ofReal r }

end localOscillation

lemma fact_isCompact_ball (x : X) (r : ℝ) : Fact (IsBounded (ball x r)) :=
  ⟨isBounded_ball⟩
attribute [local instance] fact_isCompact_ball

/-- A class stating that continuous functions have distances associated to every ball.
We use a separate type to conveniently index these functions. -/
class FunctionDistances (𝕜 : outParam Type*) (X : Type u)
    [NormedField 𝕜] [TopologicalSpace X] where
  Θ : Type u
  coeΘ : Θ → C(X, 𝕜)
  coeΘ_injective {f g : Θ} (h : ∀ x, coeΘ f x = coeΘ g x) : f = g
  metric : ∀ (_x : X) (_r : ℝ), PseudoMetricSpace Θ

export FunctionDistances (Θ coeΘ)

section FunctionDistances
variable [FunctionDistances 𝕜 X]

instance : Coe (Θ X) C(X, 𝕜) := ⟨FunctionDistances.coeΘ⟩
instance : FunLike (Θ X) X 𝕜 where
  coe := fun f ↦ (f : C(X, 𝕜))
  coe_injective' _ _ hfg := FunctionDistances.coeΘ_injective fun x ↦ congrFun hfg x
instance : ContinuousMapClass (Θ X) X 𝕜 := ⟨fun f ↦ (f : C(X, 𝕜)).2⟩

set_option linter.unusedVariables false in
@[nolint unusedArguments]
def WithFunctionDistance (x : X) (r : ℝ) := Θ X

variable {x : X} {r : ℝ}

def toWithFunctionDistance [FunctionDistances 𝕜 X] : Θ X ≃ WithFunctionDistance x r :=
  .refl _

-- instance : FunLike (WithFunctionDistance Θ x r) X 𝕜 := ContinuousMap.funLike
-- instance : ContinuousMapClass (WithFunctionDistance Θ x r) X 𝕜 :=
--   ContinuousMap.toContinuousMapClass

instance [d : FunctionDistances 𝕜 X] : PseudoMetricSpace (WithFunctionDistance x r) :=
  d.metric x r

end FunctionDistances

notation3 "dist_{" x " ," r "}" => @dist (WithFunctionDistance x r) _
notation3 "nndist_{" x " ," r "}" => @nndist (WithFunctionDistance x r) _
notation3 "ball_{" x " ," r "}" => @ball (WithFunctionDistance x r) _ in

/-- A set `Θ` of (continuous) functions is compatible. `A` will usually be `2 ^ a`. -/
class CompatibleFunctions (𝕜 : outParam Type*) (X : Type u) (A : outParam ℕ)
  [RCLike 𝕜] [PseudoMetricSpace X] extends FunctionDistances 𝕜 X where
  eq_zero : ∃ o : X, ∀ f : Θ, f o = 0
  /-- The distance is bounded below by the local oscillation. (1.0.7) -/
  localOscillation_le_cdist {x : X} {r : ℝ} {f g : Θ} :
    localOscillation (ball x r) (coeΘ f) (coeΘ g) ≤ ENNReal.ofReal (dist_{x, r} f g)
  /-- The distance is monotone in the ball. (1.0.9) -/
  cdist_mono {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : Θ}
    (h : ball x₁ r₁ ⊆ ball x₂ r₂) : dist_{x₁, r₁} f g ≤ dist_{x₂, r₂} f g
  /-- The distance of a ball with large radius is bounded above. (1.0.8) -/
  cdist_le {x₁ x₂ : X} {r : ℝ} {f g : Θ} (h : dist x₁ x₂ < 2 * r) :
    dist_{x₂, 2 * r} f g ≤ A * dist_{x₁, r} f g
  /-- The distance of a ball with large radius is bounded below. (1.0.10) -/
  le_cdist {x₁ x₂ : X} {r : ℝ} {f g : Θ} (h1 : ball x₁ r ⊆ ball x₂ (A * r)) :
    /-(h2 : A * r ≤ Metric.diam (univ : Set X))-/
    2 * dist_{x₁, r} f g ≤ dist_{x₂, A * r} f g
  /-- The distance of a ball with large radius is bounded below. (1.0.11) -/
  ballsCoverBalls {x : X} {r R : ℝ} :
    BallsCoverBalls (X := WithFunctionDistance x r) (2 * R) R A

instance nonempty_Space [CompatibleFunctions 𝕜 X A] : Nonempty X := by
  obtain ⟨x,_⟩ := ‹CompatibleFunctions 𝕜 X A›.eq_zero
  use x

instance inhabited_Space [CompatibleFunctions 𝕜 X A] : Inhabited X :=
  ⟨nonempty_Space.some⟩

lemma le_localOscillation [CompatibleFunctions 𝕜 X A] (x : X) (r : ℝ) (f g : Θ X) {y z : X}
    (hy : y ∈ ball x r) (hz : z ∈ ball x r) : ‖coeΘ f y - coeΘ g y - coeΘ f z + coeΘ g z‖ ≤
    ENNReal.toReal (localOscillation (ball x r) (coeΘ f) (coeΘ g)) := by
  rw [(ENNReal.toReal_ofReal (norm_nonneg _)).symm]
  let f (z) := ⨆ (_ : z ∈ ball x r ×ˢ ball x r), ENNReal.ofReal ‖f z.1 - g z.1 - f z.2 + g z.2‖
  apply ENNReal.toReal_mono
  · exact lt_of_le_of_lt CompatibleFunctions.localOscillation_le_cdist ENNReal.ofReal_lt_top |>.ne
  · exact le_of_eq_of_le (Eq.symm (iSup_pos ⟨hy, hz⟩)) (le_iSup f ⟨y, z⟩)

lemma oscillation_le_cdist [CompatibleFunctions 𝕜 X A] (x : X) (r : ℝ) (f g : Θ X) {y z : X}
    (hy : y ∈ ball x r) (hz : z ∈ ball x r) :
    ‖coeΘ f y - coeΘ g y - coeΘ f z + coeΘ g z‖ ≤ dist_{x, r} f g := by
  apply le_trans <| le_localOscillation x r f g hy hz
  rw [← ENNReal.toReal_ofReal dist_nonneg]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top CompatibleFunctions.localOscillation_le_cdist

export CompatibleFunctions (localOscillation_le_cdist cdist_mono cdist_le le_cdist)

lemma dist_congr [FunctionDistances 𝕜 X] {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : Θ X}
    (e₁ : x₁ = x₂) (e₂ : r₁ = r₂) : dist_{x₁, r₁} f g = dist_{x₂, r₂} f g := by congr

variable (X) in
/-- The point `o` in the blueprint -/
def cancelPt [CompatibleFunctions 𝕜 X A] : X :=
  CompatibleFunctions.eq_zero (𝕜 := 𝕜) |>.choose
lemma cancelPt_eq_zero [CompatibleFunctions 𝕜 X A] {f : Θ X} : f (cancelPt X) = 0 :=
  CompatibleFunctions.eq_zero (𝕜 := 𝕜) |>.choose_spec f

-- not sure if needed
-- lemma CompatibleFunctions.IsSeparable [CompatibleFunctions 𝕜 X A] :
--   IsSeparable (range (coeΘ (X := X))) :=
--   sorry

set_option linter.unusedVariables false in
/-- The inhomogeneous Lipschitz norm on a ball. -/
def iLipNorm {𝕜} [NormedField 𝕜] (ϕ : X → 𝕜) (x₀ : X) (R : ℝ) : ℝ :=
  (⨆ x ∈ ball x₀ R, ‖ϕ x‖) + R * ⨆ (x : X) (y : X) (h : x ≠ y), ‖ϕ x - ϕ y‖ / dist x y

lemma iLipNorm_nonneg {𝕜} [NormedField 𝕜] {ϕ : X → 𝕜} {x₀ : X} {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ iLipNorm ϕ x₀ R :=
  add_nonneg (Real.iSup_nonneg fun _ ↦ Real.iSup_nonneg fun _ ↦ norm_nonneg _)
    (mul_nonneg hR (Real.iSup_nonneg fun _ ↦ Real.iSup_nonneg fun _ ↦ Real.iSup_nonneg
    fun _ ↦ div_nonneg (norm_nonneg _) dist_nonneg))

variable [DoublingMeasure X A]

variable (X) in
/-- Θ is τ-cancellative. `τ` will usually be `1 / a` -/
class IsCancellative (τ : ℝ) [CompatibleFunctions ℝ X A] : Prop where
  norm_integral_exp_le {x : X} {r : ℝ} {ϕ : X → ℂ} {K : ℝ≥0} (h1 : LipschitzWith K ϕ)
    (h2 : tsupport ϕ ⊆ ball x r) {f g : Θ X} :
    ‖∫ x in ball x r, exp (I * (f x - g x)) * ϕ x‖ ≤
    A * volume.real (ball x r) * iLipNorm ϕ x r * (1 + dist_{x, r} f g) ^ (- τ)

export IsCancellative (norm_integral_exp_le)

/-- The "volume function" `V`. Note that we will need to assume
`IsFiniteMeasureOnCompacts` and `ProperSpace` to actually know that this volume is finite. -/
def Real.vol {X : Type*} [PseudoMetricSpace X] [MeasureSpace X] (x y : X) : ℝ :=
  volume.real (ball x (dist x y))

-- /-- In Mathlib we only have the operator norm for continuous linear maps,
-- and `T_*` is not linear.
-- Here is the norm for an arbitrary map `T` between normed spaces
-- (the infimum is defined to be 0 if the operator is not bounded). -/
-- def operatorNorm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (T : E → F) : ℝ :=
--   sInf { c | 0 ≤ c ∧ ∀ x, ‖T x‖ ≤ c * ‖x‖ }

/-- The Calderon Zygmund operator `T_r` in chapter Two-sided Metric Space Carleson -/
def CZOperator (K : X → X → ℂ) (r : ℝ) (f : X → ℂ) (x : X) : ℂ :=
  ∫ y in (ball x r)ᶜ, K x y * f y

/-- `R_Q(θ, x)` defined in (1.0.20). -/
def upperRadius [FunctionDistances ℝ X] (Q : X → Θ X) (θ : Θ X) (x : X) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : dist_{x, r} θ (Q x) < 1), ENNReal.ofReal r

lemma le_upperRadius [FunctionDistances ℝ X] {Q : X → Θ X} {θ : Θ X} {x : X} {r : ℝ}
    (hr : dist_{x, r} θ (Q x) < 1) : ENNReal.ofReal r ≤ upperRadius Q θ x := by
  apply le_iSup₂ (f := fun r _ ↦ ENNReal.ofReal r) r hr

/-- The linearized maximally truncated nontangential Calderon Zygmund operator `T_Q^θ` -/
def linearizedNontangentialOperator [FunctionDistances ℝ X] (Q : X → Θ X) (θ : Θ X)
    (K : X → X → ℂ) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (R₁ : ℝ) (x' : X) (_ : dist x x' ≤ R₁),
  ‖∫ y in {y | ENNReal.ofReal (dist x' y) ∈ Ioo (ENNReal.ofReal R₁) (upperRadius Q θ x')},
    K x' y * f y‖₊

/-- The maximally truncated nontangential Calderon Zygmund operator `T_*` -/
def nontangentialOperator (K : X → X → ℂ) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (R₁ : ℝ) (R₂ : ℝ) (_ : R₁ < R₂) (x' : X) (_ : dist x x' < R₁),
  ‖∫ y in {y | dist x' y ∈ Ioo R₁ R₂}, K x' y * f y‖₊

/-- The linearized generalized Carleson operator `T_Q`, taking values in `ℝ≥0∞`.
Use `ENNReal.toReal` to get the corresponding real number. -/
def linearizedCarlesonOperator [FunctionDistances ℝ X] (Q : X → Θ X) (K : X → X → ℂ)
    (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (R₁ : ℝ) (R₂ : ℝ) (_ : 0 < R₁) (_ : R₁ < R₂),
  ‖∫ y in {y | dist x y ∈ Ioo R₁ R₂}, K x y * f y * exp (I * Q x y)‖₊

/-- The generalized Carleson operator `T`, taking values in `ℝ≥0∞`.
Use `ENNReal.toReal` to get the corresponding real number. -/
def carlesonOperator [FunctionDistances ℝ X] (K : X → X → ℂ) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (θ : Θ X), linearizedCarlesonOperator (fun _ ↦ θ) K f x

end DoublingMeasure

/-- This is usually the value of the argument `A` in `DoublingMeasure`
and `CompatibleFunctions` -/
@[simp] abbrev defaultA (a : ℕ) : ℕ := 2 ^ a
@[simp] def defaultD (a : ℕ) : ℕ := 2 ^ (100 * a ^ 2)
@[simp] def defaultκ (a : ℕ) : ℝ := 2 ^ (-10 * (a : ℝ))
@[simp] def defaultZ (a : ℕ) : ℕ := 2 ^ (12 * a)
@[simp] def defaultτ (a : ℕ) : ℝ := a⁻¹

lemma defaultD_pos (a : ℕ) : 0 < (defaultD a : ℝ) := by rw [defaultD]; positivity

lemma defaultD_pos' (a : ℕ) : 0 < defaultD a := by exact_mod_cast defaultD_pos a

lemma defaultD_pow_pos (a : ℕ) (z : ℤ) : 0 < (defaultD a : ℝ) ^ z :=
  zpow_pos (defaultD_pos _) _

lemma mul_defaultD_pow_pos (a : ℕ) {r : ℝ} (hr : 0 < r) (z : ℤ) : 0 < r * (defaultD a : ℝ) ^ z :=
  mul_pos hr (defaultD_pow_pos a z)

section Kernel

variable {X : Type*} {a : ℕ} {K : X → X → ℂ} [PseudoMetricSpace X] [MeasureSpace X]
open Real (vol)
open Function

/-- The constant used twice in the definition of the Calderon-Zygmund kernel. -/
@[simp] def C_K (a : ℝ) : ℝ := 2 ^ a ^ 3

lemma C_K_pos (a : ℝ) : 0 < C_K a := by unfold C_K; positivity

/-- `K` is a one-sided Calderon-Zygmund kernel
In the formalization `K x y` is defined everywhere, even for `x = y`. The assumptions on `K` show
that `K x x = 0`. -/
class IsOneSidedKernel (a : outParam ℕ) (K : X → X → ℂ) : Prop where
  measurable_K : Measurable (uncurry K)
  norm_K_le_vol_inv (x y : X) : ‖K x y‖ ≤ C_K a / vol x y
  norm_K_sub_le {x y y' : X} (h : 2 * dist y y' ≤ dist x y) :
    ‖K x y - K x y'‖ ≤ (dist y y' / dist x y) ^ (a : ℝ)⁻¹ * (C_K a / vol x y)

export IsOneSidedKernel (measurable_K norm_K_le_vol_inv norm_K_sub_le)

lemma MeasureTheory.stronglyMeasurable_K [IsOneSidedKernel a K] :
    StronglyMeasurable (uncurry K) :=
  measurable_K.stronglyMeasurable

lemma MeasureTheory.aestronglyMeasurable_K [IsOneSidedKernel a K] :
    AEStronglyMeasurable (uncurry K) :=
  measurable_K.aestronglyMeasurable

lemma measurable_K_left [IsOneSidedKernel a K] (y : X) : Measurable (K · y) :=
  measurable_K.of_uncurry_right

lemma measurable_K_right [IsOneSidedKernel a K] (x : X) : Measurable (K x) :=
  measurable_K.of_uncurry_left

lemma integrableOn_K_Icc [IsOpenPosMeasure (volume : Measure X)] [ProperSpace X]
    [Regular (volume : Measure X)] [IsOneSidedKernel a K] {x : X} {r R : ℝ} (hr : r > 0) :
    IntegrableOn (K x) {y | dist x y ∈ Icc r R} volume := by
  use Measurable.aestronglyMeasurable (measurable_K_right x)
  rw [hasFiniteIntegral_def]
  calc ∫⁻ (y : X) in {y | dist x y ∈ Icc r R}, ‖K x y‖ₑ
    _ ≤ ∫⁻ (y : X) in {y | dist x y ∈ Icc r R},
          ENNReal.ofReal (C_K a / volume.real (ball x r)) := by
      refine setLIntegral_mono measurable_const (fun y hy ↦ ?_)
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal <| (norm_K_le_vol_inv x y).trans ?_
      gcongr
      · exact (C_K_pos a).le
      · rw [measureReal_def]
        apply ENNReal.toReal_pos (ne_of_gt <| measure_ball_pos volume x hr)
        exact measure_ball_ne_top x r
      · exact measureReal_mono (ball_subset_ball hy.1)
    _ < _ := by
      rw [lintegral_const]
      apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
      refine (Ne.lt_top fun h ↦ ?_)
      have : {y | dist x y ∈ Icc r R} ⊆ closedBall x R := by
        intro y ⟨_, hy⟩
        exact mem_closedBall_comm.mp hy
      exact measure_closedBall_lt_top.ne (measure_mono_top this h)

/-- `K` is a two-sided Calderon-Zygmund kernel
In the formalization `K x y` is defined everywhere, even for `x = y`. The assumptions on `K` show
that `K x x = 0`. -/
class IsTwoSidedKernel (a : outParam ℕ) (K : X → X → ℂ) extends IsOneSidedKernel a K where
  norm_K_sub_le' {x x' y : X} (h : 2 * dist x x' ≤ dist x y) :
    ‖K x y - K x' y‖ ≤ (dist x x' / dist x y) ^ (a : ℝ)⁻¹ * (C_K a / vol x y)

export IsTwoSidedKernel (norm_K_sub_le')

-- maybe show: `K` is a 2-sided kernel iff `K` and `fun x y ↦ K y x` are one-sided kernels.

end Kernel

-- to show: K is locally bounded and hence integrable outside the diagonal

/- A constant used on the boundedness of `T_*`. We generally assume
`HasBoundedStrongType (nontangentialOperator K) volume volume 2 2 (C_Ts a)`
throughout this formalization. -/
def C_Ts (a : ℝ) : ℝ≥0 := 2 ^ a ^ 3

/-- Data common through most of chapters 2-9. -/
class PreProofData {X : Type*} (a : outParam ℕ) (q : outParam ℝ) (K : outParam (X → X → ℂ))
  (σ₁ σ₂ : outParam (X → ℤ)) (F G : outParam (Set X)) [PseudoMetricSpace X] where
  d : DoublingMeasure X (defaultA a)
  four_le_a : 4 ≤ a
  cf : CompatibleFunctions ℝ X (defaultA a)
  c : IsCancellative X (defaultτ a)
  hcz : IsOneSidedKernel a K
  hasBoundedStrongType_Tstar :
    HasBoundedStrongType (nontangentialOperator K · ·) 2 2 volume volume (C_Ts a)
  measurableSet_F : MeasurableSet F
  measurableSet_G : MeasurableSet G
  measurable_σ₁ : Measurable σ₁
  measurable_σ₂ : Measurable σ₂
  finite_range_σ₁ : Finite (range σ₁)
  finite_range_σ₂ : Finite (range σ₂)
  σ₁_le_σ₂ : σ₁ ≤ σ₂
  Q : SimpleFunc X (Θ X)
  q_mem_Ioc : q ∈ Ioc 1 2

export PreProofData (four_le_a hasBoundedStrongType_Tstar measurableSet_F measurableSet_G
  measurable_σ₁ measurable_σ₂ finite_range_σ₁ finite_range_σ₂ σ₁_le_σ₂ Q q_mem_Ioc)
attribute [instance] PreProofData.d PreProofData.cf PreProofData.c PreProofData.hcz

section ProofData

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [PreProofData a q K σ₁ σ₂ F G]

section Iterate

lemma le_cdist_iterate {x : X} {r : ℝ} (hr : 0 ≤ r) (f g : Θ X) (k : ℕ) :
    2 ^ k * dist_{x, r} f g ≤ dist_{x, (defaultA a) ^ k * r} f g := by
  induction k with
  | zero => rw [pow_zero, one_mul]; congr! <;> simp
  | succ k ih =>
    trans 2 * dist_{x, (defaultA a) ^ k * r} f g
    · rw [pow_succ', mul_assoc]
      exact (mul_le_mul_left zero_lt_two).mpr ih
    · convert le_cdist (ball_subset_ball _) using 1
      · exact dist_congr rfl (by rw [← mul_assoc, pow_succ'])
      · nth_rw 1 [← one_mul ((defaultA a) ^ k * r)]; gcongr
        rw [← Nat.cast_one, Nat.cast_le]; exact Nat.one_le_two_pow

lemma cdist_le_iterate {x : X} {r : ℝ} (hr : 0 < r) (f g : Θ X) (k : ℕ) :
    dist_{x, 2 ^ k * r} f g ≤ (defaultA a) ^ k * dist_{x, r} f g := by
  induction k with
  | zero => simp_rw [pow_zero, one_mul]; congr! <;> simp
  | succ k ih =>
    trans defaultA a * dist_{x, 2 ^ k * r} f g
    · convert cdist_le _ using 1
      · exact dist_congr rfl (by ring)
      · rw [dist_self]; positivity
    · replace ih := (mul_le_mul_left (show 0 < (defaultA a : ℝ) by positivity)).mpr ih
      rwa [← mul_assoc, ← pow_succ'] at ih

lemma ballsCoverBalls_iterate_nat {x : X} {d r : ℝ} {n : ℕ} :
    BallsCoverBalls (WithFunctionDistance x d) (2 ^ n * r) r (defaultA a ^ n) := by
  have double := fun s ↦ PreProofData.cf.ballsCoverBalls (x := x) (r := d) (R := s)
  apply BallsCoverBalls.pow_mul double

lemma ballsCoverBalls_iterate {x : X} {d R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    BallsCoverBalls (WithFunctionDistance x d) R r (defaultA a ^ ⌈Real.logb 2 (R / r)⌉₊) := by
  apply ballsCoverBalls_iterate_nat.mono
  calc
    _ = R / r * r := by rw [div_mul_cancel₀ R hr.ne']
    _ = 2 ^ Real.logb 2 (R / r) * r := by
      rw [Real.rpow_logb zero_lt_two one_lt_two.ne' (by positivity)]
    _ ≤ _ := by
      gcongr
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil _)

end Iterate

@[fun_prop]
lemma measurable_Q₂ : Measurable fun p : X × X ↦ Q p.1 p.2 := fun s meass ↦ by
  have : (fun p : X × X ↦ (Q p.1) p.2) ⁻¹' s = ⋃ θ ∈ Q.range, (Q ⁻¹' {θ}) ×ˢ (θ ⁻¹' s) := by
    ext ⟨x, y⟩
    simp only [mem_preimage, SimpleFunc.mem_range, mem_range, iUnion_exists, iUnion_iUnion_eq',
      mem_iUnion, mem_prod, mem_singleton_iff]
    constructor <;> intro h
    · use x
    · obtain ⟨j, hj⟩ := h; exact congr($(hj.1) y).symm ▸ hj.2
  rw [this]
  exact Q.range.measurableSet_biUnion fun θ _ ↦
    (Q.measurableSet_fiber θ).prod (meass.preimage (map_continuous θ).measurable)

lemma stronglyMeasurable_Q₂ : StronglyMeasurable fun p : X × X ↦ Q p.1 p.2 :=
  measurable_Q₂.stronglyMeasurable

@[fun_prop]
lemma aestronglyMeasurable_Q₂ : AEStronglyMeasurable fun p : X × X ↦ Q p.1 p.2 :=
  measurable_Q₂.aestronglyMeasurable

@[fun_prop]
lemma measurable_Q₁ (x : X) : Measurable (Q x) :=
  let Q' : X → X → ℝ := fun x' y ↦ Q x' y
  have : (fun y ↦ Q' x y) = Q x := rfl
  this ▸ measurable_Q₂.of_uncurry_left

include a q K σ₁ σ₂ F G

variable (X) in
lemma S_spec : ∃ n : ℕ, ∀ x, -n ≤ σ₁ x ∧ σ₂ x ≤ n := by
  have h1 : (range σ₁).Finite := finite_range_σ₁
  have h2 : (range σ₂).Finite := finite_range_σ₂
  have h1' := bddBelow_def.mp h1.bddBelow
  have h2' := bddAbove_def.mp h2.bddAbove
  refine ⟨(max (-h1'.choose) h2'.choose).toNat, fun x ↦ ?_⟩
  simp only [Int.ofNat_toNat, ← min_neg_neg, neg_neg, min_le_iff, le_max_iff]
  exact ⟨Or.inl (Or.inl (h1'.choose_spec _ (mem_range_self x))),
    Or.inl (Or.inr (h2'.choose_spec _ (mem_range_self x)))⟩

section DBounds

variable (X)

-- used in 4.1.7 (`small_boundary`)
lemma twentyfive_le_realD : (25 : ℝ) ≤ defaultD a := by
  simp only [defaultD, Nat.ofNat_le_cast]
  have : 4 ≤ a := four_le_a X
  calc
    (25 : ℕ)
      ≤ 32 := Nat.le_of_ble_eq_true rfl
    _ = 2 ^ (5) := by rfl
    _ ≤ 2 ^ (100 * 4 ^ 2) := Nat.le_of_ble_eq_true (by norm_num)
    _ ≤ 2 ^ (100 * a ^ 2) := Nat.pow_le_pow_right (by norm_num)
      (mul_le_mul_of_nonneg_left (Nat.pow_le_pow_of_le_left this 2) (by norm_num))

-- used in 4.1.3 (`I3_prop_3_1`)
lemma eight_le_realD : (8 : ℝ) ≤ defaultD a := by
  linarith [twentyfive_le_realD X]

-- used in 4.1.6 (`transitive_boundary`)
lemma five_le_realD : (5 : ℝ) ≤ defaultD a := by
  linarith [twentyfive_le_realD X]

-- used in various places in `Carleson.TileExistence`
lemma four_le_realD : (4 : ℝ) ≤ defaultD a := by
  linarith [twentyfive_le_realD X]

lemma one_le_realD : (1 : ℝ) ≤ defaultD a := by
  linarith [twentyfive_le_realD X]

open Classical in
def defaultS : ℕ := Nat.find (S_spec X)

end DBounds

lemma range_σ₁_subset : range σ₁ ⊆ Icc (- defaultS X) (defaultS X) := by
  classical
  rw [range_subset_iff]
  exact fun x ↦ ⟨(Nat.find_spec (S_spec X) x).1, (σ₁_le_σ₂ x).trans (Nat.find_spec (S_spec X) x).2⟩

lemma range_σ₂_subset : range σ₂ ⊆ Icc (- defaultS X) (defaultS X) := by
  classical
  rw [range_subset_iff]
  exact fun x ↦ ⟨(Nat.find_spec (S_spec X) x).1.trans (σ₁_le_σ₂ x), (Nat.find_spec (S_spec X) x).2⟩

lemma Icc_σ_subset_Icc_S {x : X} : Icc (σ₁ x) (σ₂ x) ⊆ Icc (- defaultS X) (defaultS X) :=
  fun _ h ↦ ⟨(range_σ₁_subset ⟨x, rfl⟩).1.trans h.1, h.2.trans (range_σ₂_subset ⟨x, rfl⟩).2⟩

lemma neg_S_mem_or_S_mem [Nonempty X] :
    (- defaultS X : ℤ) ∈ range σ₁ ∨ (defaultS X : ℤ) ∈ range σ₂ := by
  by_cases h₀ : defaultS X = 0
  · right
    simp only [h₀, CharP.cast_eq_zero, mem_range]
    have : range σ₂ ⊆ Icc (- defaultS X) (defaultS X) := range_σ₂_subset
    simp only [h₀, CharP.cast_eq_zero, neg_zero, Icc_self, subset_singleton_iff, mem_range,
      forall_exists_index, forall_apply_eq_imp_iff] at this
    let x : X := Classical.choice inferInstance
    exact ⟨x, this x⟩
  by_contra! h
  let n := (defaultS X) - 1
  have h1 (x : X) : -n ≤ σ₁ x := by
    rw [Int.natCast_sub (Nat.one_le_iff_ne_zero.mpr h₀), neg_sub, sub_eq_add_neg, add_comm]
    exact lt_iff_le_and_ne.mpr ⟨(range_σ₁_subset (mem_range_self x)).1,
      fun h' ↦ h.1 <| mem_range.mpr ⟨x, h'.symm⟩⟩
  have h2 (x : X) : σ₂ x ≤ n :=
    Int.natCast_sub (Nat.one_le_iff_ne_zero.mpr h₀) ▸ le_sub_right_of_add_le (lt_iff_le_and_ne.mpr
      ⟨(range_σ₂_subset (mem_range_self x)).2, fun h' ↦ h.2 <| mem_range.mpr ⟨x, h'⟩⟩)
  have hn : n < defaultS X := by
    simp only [tsub_lt_self_iff, zero_lt_one, and_true, n]
    exact Nat.zero_lt_of_ne_zero h₀
  classical
  exact Nat.find_min (S_spec X) hn fun x ↦ ⟨h1 x, h2 x⟩

variable (X)

lemma a_pos : 0 < a := by linarith [four_le_a X]
lemma cast_a_pos : 0 < (a : ℝ) := by norm_cast; exact a_pos X
lemma τ_pos : 0 < defaultτ a := inv_pos.mpr (cast_a_pos X)
lemma τ_nonneg : 0 ≤ defaultτ a := (τ_pos X).le

/-- `τ` as an element of `ℝ≥0`. -/
def nnτ : ℝ≥0 := ⟨defaultτ a, τ_nonneg X⟩

lemma one_lt_q : 1 < q := (q_mem_Ioc X).1
lemma q_le_two : q ≤ 2 := (q_mem_Ioc X).2
lemma q_pos : 0 < q := zero_lt_one.trans (one_lt_q X)
lemma q_nonneg : 0 ≤ q := (q_pos X).le
lemma inv_q_sub_half_nonneg : 0 ≤ q⁻¹ - 2⁻¹ := by
  simp [inv_le_inv₀ zero_lt_two (q_pos X), q_le_two X]

/-- `q` as an element of `ℝ≥0`. -/
def nnq : ℝ≥0 := ⟨q, q_nonneg X⟩

lemma one_lt_nnq : 1 < nnq X := one_lt_q X
lemma nnq_le_two : nnq X ≤ 2 := q_le_two X
lemma nnq_pos : 0 < nnq X := q_pos X
lemma nnq_mem_Ioc : nnq X ∈ Ioc 1 2 :=
  ⟨NNReal.coe_lt_coe.mp (q_mem_Ioc X).1, NNReal.coe_le_coe.mp (q_mem_Ioc X).2⟩

end ProofData

class ProofData {X : Type*} (a : outParam ℕ) (q : outParam ℝ) (K : outParam (X → X → ℂ))
    (σ₁ σ₂ : outParam (X → ℤ)) (F G : outParam (Set X)) [PseudoMetricSpace X]
    extends PreProofData a q K σ₁ σ₂ F G where
  F_subset : F ⊆ ball (cancelPt X) (defaultD a ^ defaultS X / 4)
  G_subset : G ⊆ ball (cancelPt X) (defaultD a ^ defaultS X / 4)
  /- The next two conditions are not in the blueprint, but will be useful in various steps.
  It is easy to prove finitary_carleson (or metric_carleson) separately when either of these
  fails. -/
  volume_F_pos : 0 < volume F
  volume_G_pos : 0 < volume G

namespace ShortVariables
-- open this section to get shorter 1-letter names for a bunch of variables

set_option hygiene false
scoped notation "D" => defaultD a
scoped notation "κ" => defaultκ a
scoped notation "Z" => defaultZ a
scoped notation "τ" => defaultτ a
scoped notation "o" => cancelPt X
scoped notation "S" => defaultS X
scoped notation "nnτ" => nnτ X
scoped notation "nnq" => nnq X

end ShortVariables

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}

lemma one_lt_D [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] : 1 < (D : ℝ) := by
  exact_mod_cast one_lt_pow₀ Nat.one_lt_two (by nlinarith [four_le_a X])

lemma one_le_D : 1 ≤ (D : ℝ) := by
  rw [← Nat.cast_one, Nat.cast_le, defaultD, ← pow_zero 2]
  exact pow_le_pow_right' one_le_two (by positivity)

lemma D_nonneg : 0 ≤ (D : ℝ) := zero_le_one.trans one_le_D

lemma κ_nonneg : 0 ≤ κ := by
  rw [defaultκ]
  exact Real.rpow_nonneg (by norm_num) _

/-- Used in `third_exception` (Lemma 5.2.10). -/
lemma two_le_κZ [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] : 2 ≤ κ * Z := by
  rw [defaultκ, defaultZ, Nat.cast_pow, show ((2 : ℕ) : ℝ) = 2 by rfl,
    show (2 : ℝ) ^ (12 * a) = 2 ^ (12 * a : ℝ) by norm_cast, ← Real.rpow_add zero_lt_two,
    show (-10 * a + 12 * a : ℝ) = 2 * a by ring]
  norm_cast; change 2 ^ 1 ≤ _
  exact Nat.pow_le_pow_of_le one_lt_two (by linarith [four_le_a X])

/-- Used in `third_exception` (Lemma 5.2.10). -/
lemma DκZ_le_two_rpow_100 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] :
    (D : ℝ≥0∞) ^ (-κ * Z) ≤ 2 ^ (-100 : ℝ) := by
  rw [defaultD, Nat.cast_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show ((2 : ℕ) : ℝ≥0∞) = 2 by rfl]
  apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
  rw [defaultκ, defaultZ, Nat.cast_pow, show ((2 : ℕ) : ℝ) = 2 by rfl, neg_mul,
    show (2 : ℝ) ^ (12 * a) = 2 ^ (12 * a : ℝ) by norm_cast, mul_neg,
    ← Real.rpow_add zero_lt_two, show (-10 * a + 12 * a : ℝ) = 2 * a by ring,
    neg_le_neg_iff]
  norm_cast
  calc
    _ ≤ 100 * a ^ 2 := by nlinarith [four_le_a X]
    _ ≤ _ := by
      nth_rw 1 [← mul_one (a ^ 2), ← mul_assoc]
      gcongr; exact Nat.one_le_two_pow

lemma four_le_Z [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] : 4 ≤ Z := by
  rw [defaultZ, show 4 = 2 ^ 2 by rfl]
  exact Nat.pow_le_pow_right zero_lt_two (by linarith [four_le_a X])

variable (a) in
/-- `D` as an element of `ℝ≥0`. -/
def nnD : ℝ≥0 := ⟨D, by simp [D_nonneg]⟩

namespace ShortVariables

set_option hygiene false
scoped notation "nnD" => nnD a

end ShortVariables

variable [PseudoMetricSpace X] [h : ProofData a q K σ₁ σ₂ F G]

lemma volume_F_lt_top : volume F < ⊤ :=
  lt_of_le_of_lt (measure_mono ProofData.F_subset) measure_ball_lt_top

lemma volume_F_ne_top : volume F ≠ ⊤ := volume_F_lt_top.ne

/- Start of proof attempt -/
lemma round1_volume_G_lt_top : volume G < ⊤ := by
  have h1 : G ⊆ ball (cancelPt X) (defaultD a ^ defaultS X / 4) := ProofData.G_subset
  have h2 : volume G ≤ volume (ball (cancelPt X) (defaultD a ^ defaultS X / 4)) := by
    apply MeasureTheory.measure_mono
    exact h1
  have h3 : volume (ball (cancelPt X) (defaultD a ^ defaultS X / 4)) < ⊤ := by
    apply measure_ball_lt_top
  exact lt_of_le_of_lt h2 h3

theorem volume_G_lt_top : volume G < ⊤  := by

  exact round1_volume_G_lt_top
