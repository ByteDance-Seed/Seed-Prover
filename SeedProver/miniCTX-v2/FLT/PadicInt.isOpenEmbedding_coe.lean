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

/- Start of proof attempt -/
lemma round1_h1 (p : ℕ)
  [Fact p.Prime]
  (h_nonarchimedean : ∀ (x y : ℚ_[p]), ‖x + y‖ ≤ max ‖x‖ ‖y‖):
  ∀ (y : ℚ_[p]), ‖y‖ ≤ 1 → ∀ (z : ℚ_[p]), ‖z - y‖ < 1 → ‖z‖ ≤ 1 := by
  intro y hy z hz
  have h11 : ‖z‖ ≤ max (‖z - y‖) (‖y‖) := by
    have h111 : ‖(z - y) + y‖ ≤ max (‖z - y‖) (‖y‖) := h_nonarchimedean (z - y) y
    have h112 : (z - y) + y = z := by ring
    rw [h112] at h111
    exact h111
  have h12 : ‖z - y‖ ≤ 1 := by linarith
  have h13 : max (‖z - y‖) (‖y‖) ≤ 1 := by
    apply max_le
    · linarith
    · linarith
  linarith

lemma round1_h2 (p : ℕ)
  [Fact p.Prime]:
  Set.range ((↑) : ℤ_[p] → ℚ_[p]) = {x : ℚ_[p] | ‖x‖ ≤ 1} := by
  ext x
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    refine ⟨⟨x, hx⟩, ?_⟩
    simp

lemma round1_h_open_range (p : ℕ)
  [Fact p.Prime]
  (h1 : ∀ (y : ℚ_[p]), ‖y‖ ≤ 1 → ∀ (z : ℚ_[p]), ‖z - y‖ < 1 → ‖z‖ ≤ 1)
  (h2 : Set.range ((↑) : ℤ_[p] → ℚ_[p]) = {x : ℚ_[p] | ‖x‖ ≤ 1}):
  IsOpen (Set.range ((↑) : ℤ_[p] → ℚ_[p])) := by
  rw [h2]
  apply isOpen_iff_forall_mem_open.mpr
  intro y hy
  have hy1 : ‖y‖ ≤ 1 := hy
  have h3 : Metric.ball y 1 ⊆ {x : ℚ_[p] | ‖x‖ ≤ 1} := by
    intro z hz
    have h31 : ‖z - y‖ < 1 := by
      have h311 : z ∈ Metric.ball y 1 := hz
      have h312 : dist z y < 1 := Metric.mem_ball.mp h311
      simpa [dist_eq_norm] using h312
    have h32 : ‖z‖ ≤ 1 := h1 y hy1 z h31
    exact h32
  have h4 : y ∈ Metric.ball y 1 := by
    simp [Metric.mem_ball, dist_eq_norm]
    <;> norm_num
  refine ⟨Metric.ball y 1, h3, Metric.isOpen_ball, h4⟩

lemma round1_h_inj (p : ℕ)
  [Fact p.Prime]:
  Injective ((↑) : ℤ_[p] → ℚ_[p]) := by
  exact coe_injective

lemma round1_h_continuous (p : ℕ)
  [Fact p.Prime]:
  Continuous ((↑) : ℤ_[p] → ℚ_[p]) := by
  continuity

lemma round1_h_inducing (p : ℕ)
  [Fact p.Prime]
  (h_continuous : Continuous ((↑) : ℤ_[p] → ℚ_[p])):
  IsInducing ((↑) : ℤ_[p] → ℚ_[p]) := by
  exact inducing_subtype_val

lemma round1_h_is_embedding (p : ℕ)
  [Fact p.Prime]
  (h_inj : Injective ((↑) : ℤ_[p] → ℚ_[p]))
  (h_inducing : IsInducing ((↑) : ℤ_[p] → ℚ_[p])):
  IsEmbedding ((↑) : ℤ_[p] → ℚ_[p]) := by
  exact IsEmbedding.mk h_inducing h_inj

theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℤ_[p] → ℚ_[p])  := by

  have h_nonarchimedean : ∀ (x y : ℚ_[p]), ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
    intro x y
    exact?
  have h1 : ∀ (y : ℚ_[p]), ‖y‖ ≤ 1 → ∀ (z : ℚ_[p]), ‖z - y‖ < 1 → ‖z‖ ≤ 1 := by
    exact round1_h1 p h_nonarchimedean
  have h2 : Set.range ((↑) : ℤ_[p] → ℚ_[p]) = {x : ℚ_[p] | ‖x‖ ≤ 1} := by
    exact round1_h2 p
  have h_open_range : IsOpen (Set.range ((↑) : ℤ_[p] → ℚ_[p])) := by
    exact round1_h_open_range p h1 h2
  have h_inj : Injective ((↑) : ℤ_[p] → ℚ_[p]) := by
    exact round1_h_inj p
  have h_continuous : Continuous ((↑) : ℤ_[p] → ℚ_[p]) := by
    exact round1_h_continuous p
  have h_inducing : IsInducing ((↑) : ℤ_[p] → ℚ_[p]) := by
    exact round1_h_inducing p h_continuous
  have h_is_embedding : IsEmbedding ((↑) : ℤ_[p] → ℚ_[p]) := by
    exact round1_h_is_embedding p h_inj h_inducing
  refine' ⟨h_is_embedding, _⟩
  exact h_open_range
