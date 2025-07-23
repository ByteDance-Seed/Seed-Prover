-- In FLT/FLT/Mathlib/NumberTheory/Padics/PadicIntegers.lean

import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.Padics.PadicIntegers
import FLT.Mathlib.GroupTheory.Index

/-!
# TODO

* Rename `Coe.ringHom` to `coeRingHom`
* Protect `PadicInt.norm_mul`, `PadicInt.norm_units`, `PadicInt.norm_pow`
-/

open Function Topology Subgroup
open scoped NNReal nonZeroDivisors Pointwise

variable {p : ℕ} [Fact p.Prime]

namespace PadicInt
variable {x : ℤ_[p]}

attribute [simp] coe_eq_zero

@[simp, norm_cast] lemma coe_coeRingHom : ⇑(Coe.ringHom (p := p)) = (↑) := rfl

lemma coe_injective : Injective ((↑) : ℤ_[p] → ℚ_[p]) := Subtype.val_injective

@[simp] lemma coe_inj {x y : ℤ_[p]} : (x : ℚ_[p]) = (y : ℚ_[p]) ↔ x = y := coe_injective.eq_iff

instance : Infinite ℤ_[p] := CharZero.infinite _

@[simp]
protected lemma nnnorm_mul (x y : ℤ_[p]) : ‖x * y‖₊ = ‖x‖₊ * ‖y‖₊ := by simp [nnnorm, NNReal]

@[simp]
protected lemma nnnorm_pow (x : ℤ_[p]) (n : ℕ) : ‖x ^ n‖₊ = ‖x‖₊ ^ n := by simp [nnnorm, NNReal]

@[simp] lemma nnnorm_p : ‖(p : ℤ_[p])‖₊ = (p : ℝ≥0)⁻¹ := by simp [nnnorm]; rfl

@[simp] protected lemma nnnorm_units (u : ℤ_[p]ˣ) : ‖(u : ℤ_[p])‖₊ = 1 := by simp [nnnorm, NNReal]

lemma exists_unit_mul_p_pow_eq (hx : x ≠ 0) : ∃ (u : ℤ_[p]ˣ) (n : ℕ), (u : ℤ_[p]) * p ^ n = x :=
  ⟨_, _, (unitCoeff_spec hx).symm⟩

lemma isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℤ_[p] → ℚ_[p]) := by
  refine (?_ : IsOpen {y : ℚ_[p] | ‖y‖ ≤ 1}).isOpenEmbedding_subtypeVal
  simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
    IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero

@[simp] lemma image_coe_smul_set (x : ℤ_[p]) (s : Set ℤ_[p]) :
    ((↑) '' (x • s) : Set ℚ_[p]) = x • (↑) '' s := Set.image_comm fun _ ↦ rfl

-- Yaël: Do we really want this as a coercion?
noncomputable instance : Coe ℤ_[p]ˣ ℚ_[p]ˣ where coe := Units.map Coe.ringHom.toMonoidHom

/-- For a `ℤ_[p]`-submodule `s` of `ℚ_[p]`, `x • s` has index `‖x‖⁻¹` in `s`.

Note that `s` is of the form `yℤ_[p]` for some `y : ℚ_[p]`, but this is syntactically less
general. -/
lemma smul_submodule_relindex (x : ℤ_[p]) (s : Submodule ℤ_[p] ℚ_[p]) :
    (x • s.toAddSubgroup).relindex s.toAddSubgroup = ‖x‖₊⁻¹ :=
  -- https://github.com/ImperialCollegeLondon/FLT/issues/279
  -- Note: You might need to prove `smul_submoduleSpan_finiteRelIndex_submoduleSpan` first
  sorry

/-- For a `ℤ_[p]`-submodule `s` of `ℚ_[p]`, `x • s` has finite index if `x ≠ 0`.

Note that `s` is the form `yℤ_[p]` for some `y : ℚ_[p]`, but this is syntactically less
general. -/
lemma smul_submodule_finiteRelIndex (hx : x ≠ 0) (s : Submodule ℤ_[p] ℚ_[p]) :
    (x • s.toAddSubgroup).FiniteRelIndex s.toAddSubgroup where
  relIndex_ne_zero := by simpa [← Nat.cast_ne_zero (R := ℝ≥0), smul_submodule_relindex]

-- Yaël: Do we really want this as a coercion?
noncomputable instance : Coe ℤ_[p]⁰ ℚ_[p]ˣ where
  coe x := .mk0 x.1 <| map_ne_zero_of_mem_nonZeroDivisors (M := ℤ_[p]) Coe.ringHom coe_injective x.2

/- Start of proof attempt -/
lemma round1_h11 (p : ℕ) [Fact p.Prime] (y : ℚ_[p]ˣ) :
  ∃ n : ℕ, ‖(y : ℚ_[p]) * (p : ℚ_[p]) ^ n‖ ≤ 1 := by
  have h1111 : 0 < ‖(p : ℚ_[p])‖ := by
    have h11111 : (p : ℚ_[p]) ≠ 0 := by
      have h111111 : p ≠ 0 := by
        have h111112 : p ≥ 2 := (Fact.out : Nat.Prime p).two_le
        linarith
      simpa using h111111
    exact norm_pos_iff.mpr h11111
  have h1112 : ‖(p : ℚ_[p])‖ < 1 := by
    have h11121 : ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := by simp [norm_p]
    have h11122 : (p : ℝ) ≥ 2 := by exact_mod_cast (Fact.out : Nat.Prime p).two_le
    have h11123 : (p : ℝ) > 0 := by positivity
    have h11124 : (p : ℝ)⁻¹ < 1 := by
      apply inv_lt_one
      <;> linarith
    linarith
  have h1113 : 0 < ‖(y : ℚ_[p])‖ := by
    have h11131 : (y : ℚ_[p]) ≠ 0 := by exact?
    exact norm_pos_iff.mpr h11131
  have h11132 : 0 < 1 / ‖(y : ℚ_[p])‖ := by positivity
  have h1114 : ∃ (n : ℕ), ‖(p : ℚ_[p])‖ ^ n < 1 / ‖(y : ℚ_[p])‖ := by
    apply exists_pow_lt_of_lt_one
    all_goals linarith
  rcases h1114 with ⟨n, h1114⟩
  use n
  have h1121 : ‖(p : ℚ_[p]) ^ n‖ ≤ ‖(p : ℚ_[p])‖ ^ n := by
    have h : ∀ n : ℕ, ‖(p : ℚ_[p]) ^ n‖ ≤ ‖(p : ℚ_[p])‖ ^ n := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        calc
          ‖(p : ℚ_[p]) ^ (n + 1)‖ = ‖(p : ℚ_[p]) ^ n * (p : ℚ_[p])‖ := by ring_nf
          _ ≤ ‖(p : ℚ_[p]) ^ n‖ * ‖(p : ℚ_[p])‖ := by apply norm_mul_le
          _ ≤ (‖(p : ℚ_[p])‖ ^ n) * ‖(p : ℚ_[p])‖ := by gcongr <;> linarith
          _ = ‖(p : ℚ_[p])‖ ^ (n + 1) := by ring
    exact h n
  have h1122 : ‖(y : ℚ_[p]) * (p : ℚ_[p]) ^ n‖ ≤ ‖(y : ℚ_[p])‖ * ‖(p : ℚ_[p]) ^ n‖ := by
    apply norm_mul_le
  have h1123 : ‖(y : ℚ_[p]) * (p : ℚ_[p]) ^ n‖ ≤ ‖(y : ℚ_[p])‖ * ‖(p : ℚ_[p])‖ ^ n := by
    calc
      ‖(y : ℚ_[p]) * (p : ℚ_[p]) ^ n‖ ≤ ‖(y : ℚ_[p])‖ * ‖(p : ℚ_[p]) ^ n‖ := h1122
      _ ≤ ‖(y : ℚ_[p])‖ * ‖(p : ℚ_[p])‖ ^ n := by gcongr <;> linarith
  have h113 : ‖(y : ℚ_[p])‖ * ‖(p : ℚ_[p])‖ ^ n < 1 := by
    have h1131 : 0 < ‖(y : ℚ_[p])‖ := by linarith
    have h1132 : ‖(p : ℚ_[p])‖ ^ n < 1 / ‖(y : ℚ_[p])‖ := h1114
    have h1133 : ‖(y : ℚ_[p])‖ * ‖(p : ℚ_[p])‖ ^ n < 1 := by
      calc
        ‖(y : ℚ_[p])‖ * ‖(p : ℚ_[p])‖ ^ n < ‖(y : ℚ_[p])‖ * (1 / ‖(y : ℚ_[p])‖) := by gcongr
        _ = 1 := by
          field_simp [h1131.ne'] <;> ring
    linarith
  linarith

lemma round1_h121 (p : ℕ) [Fact p.Prime] (y : ℚ_[p]ˣ) (n : ℕ) (h115 : ‖(y : ℚ_[p]) * (p : ℚ_[p]) ^ n‖ ≤ 1) :
  ∃ (z' : ℤ_[p]), (z' : ℚ_[p]) = (y : ℚ_[p]) * (p : ℚ_[p]) ^ n := by
  refine ⟨⟨(y : ℚ_[p]) * (p : ℚ_[p]) ^ n,?_⟩,?_⟩ <;> simp_all

lemma round1_h_z'_ne_zero (p : ℕ) [Fact p.Prime] (y : ℚ_[p]ˣ) (n : ℕ) (h115 : ‖(y : ℚ_[p]) * (p : ℚ_[p]) ^ n‖ ≤ 1)
  (z' : ℤ_[p]) (h121 : (z' : ℚ_[p]) = (y : ℚ_[p]) * (p : ℚ_[p]) ^ n) : z' ≠ 0 := by
  by_contra h1231
  have h12311 : z' = 0 := by simpa using h1231
  have h12312 : (z' : ℚ_[p]) = 0 := by simpa [h12311]
  have h12313 : (y : ℚ_[p]) * (p : ℚ_[p]) ^ n = 0 := by
    have h123131 : (y : ℚ_[p]) * (p : ℚ_[p]) ^ n = (z' : ℚ_[p]) := by rw [h121]
    rw [h123131]
    rw [h12312]
    <;> simp
  have h12314 : (y : ℚ_[p]) ≠ 0 := by
    exact?
  have h12315 : (p : ℚ_[p]) ≠ 0 := by
    have h123151 : p ≠ 0 := by
      have h123152 : p ≥ 2 := (Fact.out : Nat.Prime p).two_le
      linarith
    have h : (p : ℚ_[p]) ≠ 0 := by exact?
    exact h
  have h12316 : (p : ℚ_[p]) ^ n ≠ 0 := by
    apply pow_ne_zero
    exact h12315
  have h12317 : (y : ℚ_[p]) * (p : ℚ_[p]) ^ n ≠ 0 := mul_ne_zero h12314 h12316
  contradiction

lemma round1_h_z'_in_nonZeroDivisors (p : ℕ) [Fact p.Prime] (y : ℚ_[p]ˣ) (n : ℕ) (h115 : ‖(y : ℚ_[p]) * (p : ℚ_[p]) ^ n‖ ≤ 1)
  (z' : ℤ_[p]) (h121 : (z' : ℚ_[p]) = (y : ℚ_[p]) * (p : ℚ_[p]) ^ n) : z' ∈ ℤ_[p]⁰ := by
  have h1231 : z' ≠ 0 := round1_h_z'_ne_zero p y n h115 z' h121
  exact?

lemma round1_h_p_in_nonZeroDivisors (p : ℕ) [Fact p.Prime] : (p : ℤ_[p]) ∈ ℤ_[p]⁰ := by
  have h1272 : (p : ℤ_[p]) ≠ 0 := by
    have h12721 : p ≠ 0 := by
      have h12722 : p ≥ 2 := (Fact.out : Nat.Prime p).two_le
      linarith
    intro h
    have h12723 : (p : ℤ_[p]) = 0 := by simpa using h
    have h12724 : (p : ℚ_[p]) = 0 := by simpa using congr_arg (fun x : ℤ_[p] => (x : ℚ_[p])) h12723
    have h12725 : (p : ℚ_[p]) ≠ 0 := by
      simpa using h12721
    contradiction
  exact?

/-- Non-zero p-adic integers generate non-zero p-adic numbers as a group. -/
theorem closure_nonZeroDivisors_padicInt :
    Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ)) = ⊤  := by

  have h1 : ∀ (y : ℚ_[p]ˣ), y ∈ Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ)) := by
    intro y
    have h11 : ∃ (n : ℕ), ‖(y : ℚ_[p]) * (p : ℚ_[p]) ^ n‖ ≤ 1 := by
      exact round1_h11 p y
    rcases h11 with ⟨n, h115⟩
    have h1211 : ∃ (z' : ℤ_[p]), (z' : ℚ_[p]) = (y : ℚ_[p]) * (p : ℚ_[p]) ^ n := by
      exact round1_h121 p y n h115
    rcases h1211 with ⟨z', h121⟩
    have h123 : z' ∈ ℤ_[p]⁰ := by
      exact round1_h_z'_in_nonZeroDivisors p y n h115 z' h121
    have h1262 : ((⟨z', h123⟩ : ℤ_[p]⁰) : ℚ_[p]ˣ) ∈ Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ) := by
      refine ⟨⟨z', h123⟩, rfl⟩
    have h1263 : ((⟨z', h123⟩ : ℤ_[p]⁰) : ℚ_[p]ˣ) ∈ Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ)) := by
      apply Subgroup.subset_closure
      exact h1262
    have h131 : (p : ℤ_[p]) ∈ ℤ_[p]⁰ := by
      exact round1_h_p_in_nonZeroDivisors p
    have h1312 : ((⟨(p : ℤ_[p]), h131⟩ : ℤ_[p]⁰) : ℚ_[p]ˣ) ∈ Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ) := by
      refine ⟨⟨(p : ℤ_[p]), h131⟩, rfl⟩
    have h1313 : ((⟨(p : ℤ_[p]), h131⟩ : ℤ_[p]⁰) : ℚ_[p]ˣ) ∈ Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ)) := by
      apply Subgroup.subset_closure
      exact h1312
    have h1314 : ((⟨(p : ℤ_[p]), h131⟩ : ℤ_[p]⁰) : ℚ_[p]ˣ) ^ n ∈ Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ)) := by
      apply Subgroup.pow_mem (Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ))) h1313
    have h132 : (((⟨(p : ℤ_[p]), h131⟩ : ℤ_[p]⁰) : ℚ_[p]ˣ) ^ n)⁻¹ ∈ Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ)) := by
      apply Subgroup.inv_mem (Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ))) h1314
    have h133 : ((⟨z', h123⟩ : ℤ_[p]⁰) : ℚ_[p]ˣ) * (((⟨(p : ℤ_[p]), h131⟩ : ℤ_[p]⁰) : ℚ_[p]ˣ) ^ n)⁻¹ ∈ Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ)) := by
      apply Subgroup.mul_mem (Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ))) h1263 h132
    have h134 : ((⟨z', h123⟩ : ℤ_[p]⁰) : ℚ_[p]ˣ) = (y : ℚ_[p]ˣ) * ((⟨(p : ℤ_[p]), h131⟩ : ℤ_[p]⁰) : ℚ_[p]ˣ) ^ n := by
      apply Units.ext
      simp [h121]
      <;> ring
    have h135 : ((⟨z', h123⟩ : ℤ_[p]⁰) : ℚ_[p]ˣ) * (((⟨(p : ℤ_[p]), h131⟩ : ℤ_[p]⁰) : ℚ_[p]ˣ) ^ n)⁻¹ = (y : ℚ_[p]ˣ) := by
      rw [h134]
      group
    rw [h135] at h133
    exact h133
  have h2 : Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ)) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact h1 x
  exact h2
