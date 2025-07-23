-- In mathlib/Mathlib/Algebra/Order/Ring/Canonical.lean

/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# Canonically ordered rings and semirings.
-/

open Function

universe u

variable {α : Type u}

set_option linter.deprecated false in
/-- A canonically ordered commutative semiring is an ordered, commutative semiring in which `a ≤ b`
iff there exists `c` with `b = a + c`. This is satisfied by the natural numbers, for example, but
not the integers or other ordered groups. -/
@[deprecated "Use `[OrderedCommSemiring α] [CanonicallyOrderedAdd α] [NoZeroDivisors α]` instead."
  (since := "2025-01-13")]
structure CanonicallyOrderedCommSemiring (α : Type*) extends CanonicallyOrderedAddCommMonoid α,
    CommSemiring α where
  /-- No zero divisors. -/
  protected eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : α}, a * b = 0 → a = 0 ∨ b = 0

attribute [nolint docBlame] CanonicallyOrderedCommSemiring.toCommSemiring

-- see Note [lower instance priority]
instance (priority := 10) CanonicallyOrderedAdd.toZeroLEOneClass
    [AddZeroClass α] [One α] [LE α] [CanonicallyOrderedAdd α] : ZeroLEOneClass α where
  zero_le_one := zero_le _

-- this holds more generally if we refactor `Odd` to use
-- either `2 • t` or `t + t` instead of `2 * t`.
lemma Odd.pos [Semiring α] [PartialOrder α] [CanonicallyOrderedAdd α] [Nontrivial α] {a : α} :
    Odd a → 0 < a := by
  rintro ⟨k, rfl⟩; simp

namespace CanonicallyOrderedAdd

-- see Note [lower instance priority]
instance (priority := 100) toMulLeftMono [NonUnitalNonAssocSemiring α]
    [LE α] [CanonicallyOrderedAdd α] : MulLeftMono α := by
  refine ⟨fun a b c h => ?_⟩; dsimp
  rcases exists_add_of_le h with ⟨c, rfl⟩
  rw [mul_add]
  apply self_le_add_right

variable [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]

-- See note [reducible non-instances]
/-- Construct an `OrderedCommMonoid` from a canonically ordered `CommSemiring`. -/
abbrev toOrderedCommMonoid : OrderedCommMonoid α where
  mul_le_mul_left _ _ := mul_le_mul_left'

-- See note [reducible non-instances]
/-- Construct an `OrderedCommSemiring` from a canonically ordered `CommSemiring`. -/
abbrev toOrderedCommSemiring : OrderedCommSemiring α where
  mul_comm := mul_comm
  zero_le_one := zero_le _
  add_le_add_left _ _ := add_le_add_left
  mul_le_mul_of_nonneg_left := fun _ _ _ h _ => mul_le_mul_left' h _
  mul_le_mul_of_nonneg_right := fun _ _ _ h _ => mul_le_mul_right' h _

@[simp]
protected theorem mul_pos [NoZeroDivisors α] {a b : α} :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]

/- Start of proof attempt -/
lemma round1_pow_pos [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α] [NoZeroDivisors α]
    {a : α} (ha : 0 < a) (n : ℕ) : 0 < a ^ n := by
  induction n with
  | zero =>
    have h1 : 0 ≤ (1 : α) := zero_le_one
    have h2 : 0 ≠ (1 : α) := by
      by_contra h
      have h3 : a = 0 := by
        calc
          a = a * 1 := by simp
          _ = a * 0 := by rw [h]
          _ = 0 := by simp
      have h4 : 0 < a := ha
      rw [h3] at h4
      <;> simp at h4 <;> tauto
    have h4 : 0 < (1 : α) := by
      exact?
    simpa using h4
  | succ n ih =>
    have h5 : 0 < a ^ n * a := by
      rw [CanonicallyOrderedAdd.mul_pos]
      exact ⟨ih, ha⟩
    simpa [pow_succ] using h5

theorem pow_pos [NoZeroDivisors α] {a : α} (ha : 0 < a) (n : ℕ) : 0 < a ^ n  := by

  exact round1_pow_pos ha n
