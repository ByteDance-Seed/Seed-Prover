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

/- Start of proof attempt -/
lemma round1_h1 (u : ℤ_[p]ˣ):
  ∃ (v : ℤ_[p]), (u : ℤ_[p]) * v = 1 := by
  refine' ⟨u.inv, _⟩
  exact?

lemma round1_h6 :
  ∀ (x : ℤ_[p]), ‖x‖₊ ≤ 1 := by
  intro x
  have h61 : ‖(x : ℚ_[p])‖ ≤ 1 := x.2
  have h62 : ‖x‖₊ = ‖(x : ℚ_[p])‖₊ := rfl
  have h63 : ‖(x : ℚ_[p])‖₊ ≤ 1 := by
    exact?
  rw [h62]
  exact h63

lemma round1_h4 (u : ℤ_[p]ˣ) (v : ℤ_[p]) (hv : (u : ℤ_[p]) * v = 1) :
  ‖(u : ℤ_[p])‖₊ * ‖v‖₊ = 1 := by
  have h2 : ‖(u : ℤ_[p]) * v‖₊ = 1 := by
    rw [hv]
    norm_num
  have h3 : ‖(u : ℤ_[p]) * v‖₊ = ‖(u : ℤ_[p])‖₊ * ‖v‖₊ := by
    exact?
  have h21 : ‖(u : ℤ_[p]) * v‖₊ = 1 := h2
  have h31 : ‖(u : ℤ_[p]) * v‖₊ = ‖(u : ℤ_[p])‖₊ * ‖v‖₊ := h3
  rw [h31] at h21
  exact h21

lemma round1_h_final (u : ℤ_[p]ˣ) (v : ℤ_[p]) (h4 : ‖(u : ℤ_[p])‖₊ * ‖v‖₊ = 1) (h61 : ‖(u : ℤ_[p])‖₊ ≤ 1) (h62 : ‖v‖₊ ≤ 1) :
  ‖(u : ℤ_[p])‖₊ = 1 := by
  have h4' : (‖(u : ℤ_[p])‖₊ : ℝ) * (‖v‖₊ : ℝ) = 1 := by exact_mod_cast h4
  have h61' : (‖(u : ℤ_[p])‖₊ : ℝ) ≤ 1 := by exact_mod_cast h61
  have h62' : (‖v‖₊ : ℝ) ≤ 1 := by exact_mod_cast h62
  have h_nonneg1 : (0 : ℝ) ≤ (‖(u : ℤ_[p])‖₊ : ℝ) := by positivity
  have h_nonneg2 : (0 : ℝ) ≤ (‖v‖₊ : ℝ) := by positivity
  have h14 : (‖(u : ℤ_[p])‖₊ : ℝ) ≥ 1 := by
    by_contra h
    have h15 : (‖(u : ℤ_[p])‖₊ : ℝ) < 1 := by linarith
    have h16 : (‖(u : ℤ_[p])‖₊ : ℝ) * (‖v‖₊ : ℝ) < (‖v‖₊ : ℝ) := by
      nlinarith
    have h17 : (‖(u : ℤ_[p])‖₊ : ℝ) * (‖v‖₊ : ℝ) < 1 := by nlinarith
    linarith
  have h18 : (‖(u : ℤ_[p])‖₊ : ℝ) = 1 := by linarith
  exact_mod_cast h18

theorem nnnorm_units (u : ℤ_[p]ˣ) : ‖(u : ℤ_[p])‖₊ = 1  := by

  have h1 : ∃ (v : ℤ_[p]), (u : ℤ_[p]) * v = 1 := by
    exact round1_h1 u
  rcases h1 with ⟨v, hv⟩
  have h4 : ‖(u : ℤ_[p])‖₊ * ‖v‖₊ = 1 := by
    exact round1_h4 u v hv
  have h6 : ∀ (x : ℤ_[p]), ‖x‖₊ ≤ 1 := by
    exact round1_h6
  have h61 : ‖(u : ℤ_[p])‖₊ ≤ 1 := h6 (u : ℤ_[p])
  have h62 : ‖v‖₊ ≤ 1 := h6 v
  exact round1_h_final u v h4 h61 h62
