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


/- Start of proof attempt -/
lemma round1_mul_pos_forward [NoZeroDivisors α] {a b : α} (h : 0 < a * b) : 0 < a ∧ 0 < b := by
  have ha : 0 < a := by
    have h1 : 0 ≤ a := zero_le a
    have h2 : a ≠ 0 := by
      intro h21
      have h22 : a = 0 := h21
      have h23 : a * b = 0 := by
        rw [h22]
        <;> simp
      rw [h23] at h
      <;> simp at h
    have h11 : 0 ≤ a := h1
    have h12 : a ≠ 0 := h2
    exact?
  have hb : 0 < b := by
    have h3 : 0 ≤ b := zero_le b
    have h4 : b ≠ 0 := by
      intro h41
      have h42 : b = 0 := h41
      have h43 : a * b = 0 := by
        rw [h42]
        <;> simp
      rw [h43] at h
      <;> simp at h
    have h31 : 0 ≤ b := h3
    have h32 : b ≠ 0 := h4
    exact?
  exact ⟨ha, hb⟩

lemma round1_mul_pos_backward [NoZeroDivisors α] {a b : α} (h1 : 0 < a) (h2 : 0 < b) : 0 < a * b := by
  have ha1 : 0 ≤ a := by
    exact le_of_lt h1
  have hb1 : 0 ≤ b := by
    exact le_of_lt h2
  have h3 : 0 ≤ a * b := mul_nonneg ha1 hb1
  have h5 : a * b ≠ 0 := by
    by_contra h51
    have h52 : a = 0 ∨ b = 0 := NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h51
    have h53 : a ≠ 0 := by
      intro h531
      rw [h531] at h1
      <;> simp at h1 <;> contradiction
    have h54 : b ≠ 0 := by
      intro h541
      rw [h541] at h2
      <;> simp at h2 <;> contradiction
    cases h52 with
    | inl h52 =>
      contradiction
    | inr h52 =>
      contradiction
  have h6 : 0 < a * b := by
    by_cases h61 : 0 < a * b
    · exact h61
    · -- Case ¬(0 < a * b)
      have h62 : a * b = 0 := by
        by_contra h621
        have h63 : 0 < a * b := by
          exact?
        contradiction
      contradiction
  exact h6

theorem mul_pos [NoZeroDivisors α] {a b : α} :
    0 < a * b ↔ 0 < a ∧ 0 < b  := by

  constructor
  · exact round1_mul_pos_forward
  · rintro ⟨h1, h2⟩
    exact round1_mul_pos_backward h1 h2
