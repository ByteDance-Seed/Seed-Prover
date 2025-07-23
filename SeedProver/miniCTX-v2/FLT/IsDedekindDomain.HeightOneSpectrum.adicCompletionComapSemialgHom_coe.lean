-- In FLT/FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean

import Mathlib -- because there are sorries in this file
import FLT.Mathlib.Algebra.Order.Hom.Monoid
import FLT.Mathlib.Algebra.Algebra.Hom
import FLT.Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.Topology.Algebra.UniformRing

/-!

# Base change of adele rings.

If `A` is a Dedekind domain with field of fractions `K`, if `L/K` is a finite separable
extension and if `B` is the integral closure of `A` in `L`, then `B` is also a Dedekind
domain. Hence the rings of finite adeles `𝔸_K^∞` and `𝔸_L^∞` (defined using `A` and `B`)
are defined. In this file we define the natural `K`-algebra map `𝔸_K^∞ → 𝔸_L^∞` and
the natural `L`-algebra map `𝔸_K^∞ ⊗[K] L → 𝔸_L^∞`, and show that the latter map
is an isomorphism.

## Main definition

* `FiniteAdeleRing.baseChangeEquiv : L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L`

-/

open scoped Multiplicative

-- The general set-up.

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L]

variable [Algebra.IsSeparable K L]

example : Function.Injective (algebraMap B L) := IsIntegralClosure.algebraMap_injective' A

example : IsDomain B := by
  have foo : Function.Injective (algebraMap B L) := IsIntegralClosure.algebraMap_injective' A
  have bar : IsDomain L := inferInstance
  exact Function.Injective.isDomain _ foo -- exact? failed
variable [IsDomain B]

example : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
variable [Algebra.IsIntegral A B]

example : Module.Finite A B :=
  have := IsIntegralClosure.isNoetherian A K L B
  Module.IsNoetherian.finite A B
variable [Module.Finite A B]

example : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B
variable [IsDedekindDomain B]

example : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
variable [IsFractionRing B L]

-- We start by filling in some holes in the API for finite extensions of Dedekind domains.
namespace IsDedekindDomain

namespace HeightOneSpectrum

-- first need a way to pull back valuations on B to A
variable {B L} in
def comap (w : HeightOneSpectrum B) : HeightOneSpectrum A where
  asIdeal := w.asIdeal.comap (algebraMap A B)
  isPrime := Ideal.comap_isPrime (algebraMap A B) w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

omit [Module.Finite A B] in
lemma mk_count_factors_map
    (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) (I : Ideal A) [DecidableEq (Associates (Ideal A))]
  [DecidableEq (Associates (Ideal B))] [∀ p : Associates (Ideal A), Decidable (Irreducible p)]
  [∀ p : Associates (Ideal B), Decidable (Irreducible p)] :
    (Associates.mk w.asIdeal).count (Associates.mk (Ideal.map (algebraMap A B) I)).factors =
    Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal *
      (Associates.mk (comap A w).asIdeal).count (Associates.mk I).factors := by
  classical
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [Associates.mk_zero, Ideal.zero_eq_bot, Ideal.map_bot, ← Ideal.zero_eq_bot,
      Associates.mk_zero]
    simp [Associates.count, Associates.factors_zero, w.associates_irreducible,
      associates_irreducible (comap A w), Associates.bcount]
  | h₂ I hI =>
    obtain rfl : I = ⊤ := by simpa using hI
    simp only [Submodule.zero_eq_bot, ne_eq, top_ne_bot, not_false_eq_true, Ideal.map_top]
    simp only [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
    rw [Associates.count_zero (associates_irreducible _),
      Associates.count_zero (associates_irreducible _), mul_zero]
  | h₃ I p hI hp IH =>
    simp only [Ideal.map_mul, ← Associates.mk_mul_mk]
    have hp_bot : p ≠ ⊥ := hp.ne_zero
    have hp_bot' := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hp_bot
    have hI_bot := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hI
    rw [Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot) (Associates.mk_ne_zero.mpr hI)
      (associates_irreducible _), Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot')
      (Associates.mk_ne_zero.mpr hI_bot) (associates_irreducible _)]
    simp only [IH, mul_add]
    congr 1
    by_cases hw : (w.comap A).asIdeal = p
    · have : Irreducible (Associates.mk p) := Associates.irreducible_mk.mpr hp.irreducible
      rw [hw, Associates.factors_self this, Associates.count_some this]
      simp only [UniqueFactorizationMonoid.factors_eq_normalizedFactors, Multiset.nodup_singleton,
        Multiset.mem_singleton, Multiset.count_eq_one_of_mem, mul_one]
      rw [count_associates_factors_eq hp_bot' w.2 w.3,
        Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp_bot' w.2 w.3]
    · have : (Associates.mk (comap A w).asIdeal).count (Associates.mk p).factors = 0 :=
        Associates.count_eq_zero_of_ne (associates_irreducible _)
          (Associates.irreducible_mk.mpr hp.irreducible)
          (by rwa [ne_eq, Associates.mk_eq_mk_iff_associated, associated_iff_eq])
      rw [this, mul_zero, eq_comm]
      by_contra H
      rw [eq_comm, ← ne_eq, Associates.count_ne_zero_iff_dvd hp_bot' (irreducible w),
        Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at H
      apply hw (((Ideal.isPrime_of_prime hp).isMaximal hp_bot).eq_of_le (comap A w).2.ne_top H).symm

omit [Module.Finite A B] in
lemma intValuation_comap (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) (x : A) :
    (comap A w).intValuation x ^
    (Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal) =
    w.intValuation (algebraMap A B x) := by
  classical
  have h_ne_zero : Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero
      ((Ideal.map_eq_bot_iff_of_injective hAB).not.mpr (comap A w).3) w.2 Ideal.map_comap_le
  by_cases hx : x = 0
  · simpa [hx]
  simp only [intValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  show (ite _ _ _) ^ _ = ite _ _ _
  by_cases hx : x = 0
  · subst hx; simp [h_ne_zero]
  rw [map_eq_zero_iff _ hAB, if_neg hx, if_neg hx, ← Set.image_singleton, ← Ideal.map_span,
    mk_count_factors_map _ _ hAB, mul_comm]
  simp

-- Need to know how the valuation `w` and its pullback are related on elements of `K`.
omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite A B] in
lemma valuation_comap (w : HeightOneSpectrum B) (x : K) :
    (comap A w).valuation x ^
    (Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal) =
    w.valuation (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [valuation, ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
    ← intValuation_comap A B (algebraMap_injective_of_field_isFractionRing A B K L), div_pow]

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite A B] in
lemma _root_.IsDedekindDomain.HeightOneSpectrum.adicValued.continuous_algebraMap
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : v = comap A w) :
    letI : UniformSpace K := v.adicValued.toUniformSpace;
    letI : UniformSpace L := w.adicValued.toUniformSpace;
    Continuous (algebraMap K L) := by
  letI : UniformSpace K := v.adicValued.toUniformSpace;
  letI : UniformSpace L := w.adicValued.toUniformSpace;
  subst hvw
  refine continuous_of_continuousAt_zero (algebraMap K L) ?hf
  delta ContinuousAt
  simp only [map_zero]
  rw [(@Valued.hasBasis_nhds_zero K _ _ _ (comap A w).adicValued).tendsto_iff
    (@Valued.hasBasis_nhds_zero L _ _ _ w.adicValued)]
  simp only [HeightOneSpectrum.adicValued_apply, Set.mem_setOf_eq, true_and, true_implies]
  rw [WithZero.unitsWithZeroEquiv.forall_congr_left, Multiplicative.forall]
  intro a
  rw [WithZero.unitsWithZeroEquiv.exists_congr_left, Multiplicative.exists]
  let m := Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal
  let e : ℤ ≃ ℤₘ₀ˣ := Multiplicative.ofAdd.trans OrderMonoidIso.unitsWithZero.symm.toEquiv
  have e_apply (a : ℤ) : e a = OrderMonoidIso.unitsWithZero.symm (Multiplicative.ofAdd a) := rfl
  have hm : m ≠ 0 := by
    refine Ideal.IsDedekindDomain.ramificationIdx_ne_zero ?_ w.2 Ideal.map_comap_le
    exact (Ideal.map_eq_bot_iff_of_injective
      (algebraMap_injective_of_field_isFractionRing A B K L)).not.mpr (comap A w).3
  refine ⟨a / m, fun x hx ↦ ?_⟩
  simp_rw [← valuation_comap A]
  calc
    (comap A w).valuation x ^ m < e (a / ↑m) ^ m := by gcongr; exacts [zero_le', hx]
  _ = e (m • (a / ↑m)) := by
    dsimp [e]
    norm_cast
    rw [map_pow]
  _ ≤ e a := by
    simp only [nsmul_eq_mul, e_apply, Units.val_le_val, OrderIsoClass.map_le_map_iff]
    rw [mul_comm]
    exact Int.mul_le_of_le_ediv (by positivity) le_rfl

noncomputable def adicCompletionComapSemialgHom (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    (hvw : v = comap A w) :
    (HeightOneSpectrum.adicCompletion K v) →ₛₐ[algebraMap K L]
      (HeightOneSpectrum.adicCompletion L w) :=
  letI : UniformSpace K := v.adicValued.toUniformSpace;
  letI : UniformSpace L := w.adicValued.toUniformSpace;
  UniformSpace.Completion.mapSemialgHom _ <|
  IsDedekindDomain.HeightOneSpectrum.adicValued.continuous_algebraMap A K L B v w hvw

-- Do we even need to prove that this map is continuous? It will follow from
-- the fact that it's K_v-linear once we know L_w has the K_v-module topology,
-- which is the next lemma.
-- omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
--     [Module.Finite A B] in
-- lemma adicCompletionComapSemialgHom_continuous
--     (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : v = comap A w) :
--     Continuous (adicCompletionComapSemialgHom A K L B v w hvw) := by
--   convert UniformSpace.Completion.continuous_extension (β := (adicCompletion L w))

lemma adicCompletionComap_isModuleTopology
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : v = comap A w) :
    -- temporarily make L_w a K_v-algebra
    let inst_alg : Algebra (HeightOneSpectrum.adicCompletion K v)
      (HeightOneSpectrum.adicCompletion L w) := RingHom.toAlgebra <|
        adicCompletionComapSemialgHom A K L B v w hvw
    -- the claim that L_w has the module topology.
    IsModuleTopology (HeightOneSpectrum.adicCompletion K v)
      (HeightOneSpectrum.adicCompletion L w) := by
  sorry -- FLT#326

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite A B] in

/- Start of proof attempt -/
lemma round1_adicCompletionComapSemialgHom_coe
    (v : IsDedekindDomain.HeightOneSpectrum A) (w : IsDedekindDomain.HeightOneSpectrum B)
    (hvw : v = IsDedekindDomain.HeightOneSpectrum.comap A w) (x : K) :
    IsDedekindDomain.HeightOneSpectrum.adicCompletionComapSemialgHom A K L B v w hvw x = algebraMap K L x := by
  have h1 := (IsDedekindDomain.HeightOneSpectrum.adicCompletionComapSemialgHom A K L B v w hvw).commutes x
  simpa using h1

theorem adicCompletionComapSemialgHom_coe
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : v = comap A w) (x : K) :
    adicCompletionComapSemialgHom A K L B v w hvw x = algebraMap K L x  := by

  have h1 := (adicCompletionComapSemialgHom A K L B v w hvw).commutes x
  simpa using h1
