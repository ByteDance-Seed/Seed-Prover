-- In mathlib/Mathlib/Order/Atoms.lean

/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.ModularLattice
import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Nontriviality
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Atoms, Coatoms, and Simple Lattices

This module defines atoms, which are minimal non-`⊥` elements in bounded lattices, simple lattices,
which are lattices with only two elements, and related ideas.

## Main definitions

### Atoms and Coatoms
  * `IsAtom a` indicates that the only element below `a` is `⊥`.
  * `IsCoatom a` indicates that the only element above `a` is `⊤`.

### Atomic and Atomistic Lattices
  * `IsAtomic` indicates that every element other than `⊥` is above an atom.
  * `IsCoatomic` indicates that every element other than `⊤` is below a coatom.
  * `IsAtomistic` indicates that every element is the `sSup` of a set of atoms.
  * `IsCoatomistic` indicates that every element is the `sInf` of a set of coatoms.
  * `IsStronglyAtomic` indicates that for all `a < b`, there is some `x` with `a ⋖ x ≤ b`.
  * `IsStronglyCoatomic` indicates that for all `a < b`, there is some `x` with `a ≤ x ⋖ b`.

### Simple Lattices
  * `IsSimpleOrder` indicates that an order has only two unique elements, `⊥` and `⊤`.
  * `IsSimpleOrder.boundedOrder`
  * `IsSimpleOrder.distribLattice`
  * Given an instance of `IsSimpleOrder`, we provide the following definitions. These are not
    made global instances as they contain data :
    * `IsSimpleOrder.booleanAlgebra`
    * `IsSimpleOrder.completeLattice`
    * `IsSimpleOrder.completeBooleanAlgebra`

## Main results
  * `isAtom_dual_iff_isCoatom` and `isCoatom_dual_iff_isAtom` express the (definitional) duality
   of `IsAtom` and `IsCoatom`.
  * `isSimpleOrder_iff_isAtom_top` and `isSimpleOrder_iff_isCoatom_bot` express the
  connection between atoms, coatoms, and simple lattices
  * `IsCompl.isAtom_iff_isCoatom` and `IsCompl.isCoatom_if_isAtom`: In a modular
  bounded lattice, a complement of an atom is a coatom and vice versa.
  * `isAtomic_iff_isCoatomic`: A modular complemented lattice is atomic iff it is coatomic.

-/

variable {ι : Sort*} {α β : Type*}

section Atoms

section IsAtom

section Preorder

variable [Preorder α] [OrderBot α] {a b x : α}

/-- An atom of an `OrderBot` is an element with no other element between it and `⊥`,
  which is not `⊥`. -/
def IsAtom (a : α) : Prop :=
  a ≠ ⊥ ∧ ∀ b, b < a → b = ⊥

theorem IsAtom.Iic (ha : IsAtom a) (hax : a ≤ x) : IsAtom (⟨a, hax⟩ : Set.Iic x) :=
  ⟨fun con => ha.1 (Subtype.mk_eq_mk.1 con), fun ⟨b, _⟩ hba => Subtype.mk_eq_mk.2 (ha.2 b hba)⟩

theorem IsAtom.of_isAtom_coe_Iic {a : Set.Iic x} (ha : IsAtom a) : IsAtom (a : α) :=
  ⟨fun con => ha.1 (Subtype.ext con), fun b hba =>
    Subtype.mk_eq_mk.1 (ha.2 ⟨b, hba.le.trans a.prop⟩ hba)⟩

theorem isAtom_iff_le_of_ge : IsAtom a ↔ a ≠ ⊥ ∧ ∀ b ≠ ⊥, b ≤ a → a ≤ b :=
  and_congr Iff.rfl <|
    forall_congr' fun b => by
      simp only [Ne, @not_imp_comm (b = ⊥), Classical.not_imp, lt_iff_le_not_le]

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderBot α] {a b x : α}

theorem IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥ :=
  ⟨h.2 x, fun hx => hx.symm ▸ h.1.bot_lt⟩

theorem IsAtom.le_iff (h : IsAtom a) : x ≤ a ↔ x = ⊥ ∨ x = a := by rw [le_iff_lt_or_eq, h.lt_iff]

/- Start of proof attempt -/
lemma round1_IsAtom.bot_lt [PartialOrder α] [OrderBot α] {a : α} (h : IsAtom a) : ⊥ < a := by
  have h1 : ⊥ ≤ a := bot_le
  have h2 : a ≠ ⊥ := h.1
  exact lt_of_le_of_ne h1 (Ne.symm h2)

theorem IsAtom.bot_lt (h : IsAtom a) : ⊥ < a  := by

  exact round1_IsAtom.bot_lt h
