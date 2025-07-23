-- In mathlib/Mathlib/Algebra/Ring/Subsemiring/Defs.lean

/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.RingTheory.NonUnitalSubsemiring.Defs

/-!
# Bundled subsemirings

We define bundled subsemirings and some standard constructions: `subtype` and `inclusion`
ring homomorphisms.
-/

universe u v w

section AddSubmonoidWithOneClass

/-- `AddSubmonoidWithOneClass S R` says `S` is a type of subsets `s ≤ R` that contain `0`, `1`,
and are closed under `(+)` -/
class AddSubmonoidWithOneClass (S : Type*) (R : outParam Type*) [AddMonoidWithOne R]
  [SetLike S R] extends AddSubmonoidClass S R, OneMemClass S R : Prop

variable {S R : Type*} [AddMonoidWithOne R] [SetLike S R] (s : S)

@[aesop safe apply (rule_sets := [SetLike])]
theorem natCast_mem [AddSubmonoidWithOneClass S R] (n : ℕ) : (n : R) ∈ s := by
  induction n <;> simp [zero_mem, add_mem, one_mem, *]

@[aesop safe apply (rule_sets := [SetLike])]
lemma ofNat_mem [AddSubmonoidWithOneClass S R] (s : S) (n : ℕ) [n.AtLeastTwo] :
    ofNat(n) ∈ s := by
  rw [← Nat.cast_ofNat]; exact natCast_mem s n

instance (priority := 74) AddSubmonoidWithOneClass.toAddMonoidWithOne
    [AddSubmonoidWithOneClass S R] : AddMonoidWithOne s :=
  { AddSubmonoidClass.toAddMonoid s with
    one := ⟨_, one_mem s⟩
    natCast := fun n => ⟨n, natCast_mem s n⟩
    natCast_zero := Subtype.ext Nat.cast_zero
    natCast_succ := fun _ => Subtype.ext (Nat.cast_succ _) }

end AddSubmonoidWithOneClass

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

section SubsemiringClass

/-- `SubsemiringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative and an additive submonoid. -/
class SubsemiringClass (S : Type*) (R : outParam (Type u)) [NonAssocSemiring R]
  [SetLike S R] extends SubmonoidClass S R, AddSubmonoidClass S R : Prop

-- See note [lower instance priority]
instance (priority := 100) SubsemiringClass.addSubmonoidWithOneClass (S : Type*)
    (R : Type u) {_ : NonAssocSemiring R} [SetLike S R] [h : SubsemiringClass S R] :
    AddSubmonoidWithOneClass S R :=
  { h with }

instance (priority := 100) SubsemiringClass.nonUnitalSubsemiringClass (S : Type*)
    (R : Type u) [NonAssocSemiring R] [SetLike S R] [SubsemiringClass S R] :
    NonUnitalSubsemiringClass S R where
  mul_mem := mul_mem

variable [SetLike S R] [hSR : SubsemiringClass S R] (s : S)

namespace SubsemiringClass

-- Prefer subclasses of `NonAssocSemiring` over subclasses of `SubsemiringClass`.
/-- A subsemiring of a `NonAssocSemiring` inherits a `NonAssocSemiring` structure -/
instance (priority := 75) toNonAssocSemiring : NonAssocSemiring s := fast_instance%
  Subtype.coe_injective.nonAssocSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

instance nontrivial [Nontrivial R] : Nontrivial s :=
  nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)

instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s :=
  Subtype.coe_injective.noZeroDivisors _ rfl fun _ _ => rfl

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
def subtype : s →+* R :=
  { SubmonoidClass.subtype s, AddSubmonoidClass.subtype s with toFun := (↑) }

@[simp]
theorem coe_subtype : (subtype s : s → R) = ((↑) : s → R) :=
  rfl

-- Prefer subclasses of `Semiring` over subclasses of `SubsemiringClass`.
/-- A subsemiring of a `Semiring` is a `Semiring`. -/
instance (priority := 75) toSemiring {R} [Semiring R] [SetLike S R] [SubsemiringClass S R] :
    Semiring s := fast_instance%
  Subtype.coe_injective.semiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

@[simp, norm_cast]
theorem coe_pow {R} [Semiring R] [SetLike S R] [SubsemiringClass S R] (x : s) (n : ℕ) :
    ((x ^ n : s) : R) = (x : R) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- A subsemiring of a `CommSemiring` is a `CommSemiring`. -/
instance toCommSemiring {R} [CommSemiring R] [SetLike S R] [SubsemiringClass S R] :
    CommSemiring s := fast_instance%
  Subtype.coe_injective.commSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

end SubsemiringClass

end SubsemiringClass

variable [NonAssocSemiring S]

/-- A subsemiring of a semiring `R` is a subset `s` that is both a multiplicative and an additive
submonoid. -/
structure Subsemiring (R : Type u) [NonAssocSemiring R] extends Submonoid R, AddSubmonoid R

/-- Reinterpret a `Subsemiring` as a `Submonoid`. -/
add_decl_doc Subsemiring.toSubmonoid

/-- Reinterpret a `Subsemiring` as an `AddSubmonoid`. -/
add_decl_doc Subsemiring.toAddSubmonoid

namespace Subsemiring

instance : SetLike (Subsemiring R) R where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h

instance : SubsemiringClass (Subsemiring R) R where
  zero_mem := zero_mem'
  add_mem {s} := AddSubsemigroup.add_mem' s.toAddSubmonoid.toAddSubsemigroup
  one_mem {s} := Submonoid.one_mem' s.toSubmonoid
  mul_mem {s} := Subsemigroup.mul_mem' s.toSubmonoid.toSubsemigroup

initialize_simps_projections Subsemiring (carrier → coe, as_prefix coe)

/-- Turn a `Subsemiring` into a `NonUnitalSubsemiring` by forgetting that it contains `1`. -/
def toNonUnitalSubsemiring (S : Subsemiring R) : NonUnitalSubsemiring R where __ := S

@[simp]
theorem mem_toSubmonoid {s : Subsemiring R} {x : R} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

/- Start of proof attempt -/
lemma round1_mem_toNonUnitalSubsemiring {S : Subsemiring R} {x : R} :
    x ∈ S.toNonUnitalSubsemiring ↔ x ∈ S := by
  rfl

theorem mem_toNonUnitalSubsemiring {S : Subsemiring R} {x : R} :
    x ∈ S.toNonUnitalSubsemiring ↔ x ∈ S  := by

  exact round1_mem_toNonUnitalSubsemiring
