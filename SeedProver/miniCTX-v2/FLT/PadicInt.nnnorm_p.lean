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

/- Start of proof attempt -/
lemma round1_h1 : ‖(p : ℤ_[p])‖ = (p : ℝ)⁻¹ := by
  have h11 : PadicInt.valuation (p : ℤ_[p]) = 1 := by
    simp
  have h12 : ‖(p : ℤ_[p])‖ = (p : ℝ) ^ (-(PadicInt.valuation (p : ℤ_[p]) : ℤ)) := by
    simp [PadicInt.norm_eq_pow_val]
  rw [h12]
  rw [h11]
  norm_num
  <;> field_simp

lemma round1_h3 (h1 : ‖(p : ℤ_[p])‖ = (p : ℝ)⁻¹) :
  (‖(p : ℤ_[p])‖₊ : ℝ) = (p : ℝ)⁻¹ := by
  exact_mod_cast h1

lemma round1_h4 : ((p : ℝ≥0)⁻¹ : ℝ) = (p : ℝ)⁻¹ := by
  simp

theorem nnnorm_p : ‖(p : ℤ_[p])‖₊ = (p : ℝ≥0)⁻¹  := by

  have h1 : ‖(p : ℤ_[p])‖ = (p : ℝ)⁻¹ := by
    exact round1_h1
  have h3 : (‖(p : ℤ_[p])‖₊ : ℝ) = (p : ℝ)⁻¹ := by
    exact round1_h3 h1
  have h4 : ((p : ℝ≥0)⁻¹ : ℝ) = (p : ℝ)⁻¹ := by
    exact round1_h4
  have h5 : (‖(p : ℤ_[p])‖₊ : ℝ) = ((p : ℝ≥0)⁻¹ : ℝ) := by
    linarith
  have h6 : ‖(p : ℤ_[p])‖₊ = (p : ℝ≥0)⁻¹ := by
    exact_mod_cast h5
  exact h6
