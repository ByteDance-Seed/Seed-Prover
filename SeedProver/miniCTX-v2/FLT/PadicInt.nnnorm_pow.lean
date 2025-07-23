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

/- Start of proof attempt -/
lemma round1_nnnorm_pow (x : ℤ_[p]) (n : ℕ) : ‖x ^ n‖₊ = ‖x‖₊ ^ n := by
  induction n with
  | zero =>
    simp [pow_zero]
  | succ n ih =>
    calc
      ‖x ^ (n + 1)‖₊ = ‖x ^ n * x‖₊ := by rw [pow_succ]
      _ = ‖x ^ n‖₊ * ‖x‖₊ := by
        rw [PadicInt.nnnorm_mul]
      _ = ‖x‖₊ ^ n * ‖x‖₊ := by rw [ih]
      _ = ‖x‖₊ ^ (n + 1) := by simp [pow_succ]

theorem nnnorm_pow (x : ℤ_[p]) (n : ℕ) : ‖x ^ n‖₊ = ‖x‖₊ ^ n  := by

  exact round1_nnnorm_pow x n
