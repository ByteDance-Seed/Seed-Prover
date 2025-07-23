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

lemma IsAtom.bot_lt (h : IsAtom a) : ⊥ < a :=
  h.lt_iff.mpr rfl

lemma IsAtom.le_iff_eq (ha : IsAtom a) (hb : b ≠ ⊥) : b ≤ a ↔ b = a :=
  ha.le_iff.trans <| or_iff_right hb

theorem IsAtom.Iic_eq (h : IsAtom a) : Set.Iic a = {⊥, a} :=
  Set.ext fun _ => h.le_iff

@[simp]
theorem bot_covBy_iff : ⊥ ⋖ a ↔ IsAtom a := by
  simp only [CovBy, bot_lt_iff_ne_bot, IsAtom, not_imp_not]

alias ⟨CovBy.is_atom, IsAtom.bot_covBy⟩ := bot_covBy_iff

end PartialOrder

theorem atom_le_iSup [Order.Frame α] {a : α} (ha : IsAtom a) {f : ι → α} :
    a ≤ iSup f ↔ ∃ i, a ≤ f i := by
  refine ⟨?_, fun ⟨i, hi⟩ => le_trans hi (le_iSup _ _)⟩
  show (a ≤ ⨆ i, f i) → _
  refine fun h => of_not_not fun ha' => ?_
  push_neg at ha'
  have ha'' : Disjoint a (⨆ i, f i) :=
    disjoint_iSup_iff.2 fun i => fun x hxa hxf => le_bot_iff.2 <| of_not_not fun hx =>
      have hxa : x < a := (le_iff_eq_or_lt.1 hxa).resolve_left (by rintro rfl; exact ha' _ hxf)
      hx (ha.2 _ hxa)
  obtain rfl := le_bot_iff.1 (ha'' le_rfl h)
  exact ha.1 rfl

end IsAtom

section IsCoatom

section Preorder

variable [Preorder α]

/-- A coatom of an `OrderTop` is an element with no other element between it and `⊤`,
  which is not `⊤`. -/
def IsCoatom [OrderTop α] (a : α) : Prop :=
  a ≠ ⊤ ∧ ∀ b, a < b → b = ⊤

@[simp]
theorem isCoatom_dual_iff_isAtom [OrderBot α] {a : α} :
    IsCoatom (OrderDual.toDual a) ↔ IsAtom a :=
  Iff.rfl

@[simp]
theorem isAtom_dual_iff_isCoatom [OrderTop α] {a : α} :
    IsAtom (OrderDual.toDual a) ↔ IsCoatom a :=
  Iff.rfl

alias ⟨_, IsAtom.dual⟩ := isCoatom_dual_iff_isAtom

alias ⟨_, IsCoatom.dual⟩ := isAtom_dual_iff_isCoatom

variable [OrderTop α] {a x : α}

theorem IsCoatom.Ici (ha : IsCoatom a) (hax : x ≤ a) : IsCoatom (⟨a, hax⟩ : Set.Ici x) :=
  ha.dual.Iic hax

theorem IsCoatom.of_isCoatom_coe_Ici {a : Set.Ici x} (ha : IsCoatom a) : IsCoatom (a : α) :=
  @IsAtom.of_isAtom_coe_Iic αᵒᵈ _ _ x a ha

theorem isCoatom_iff_ge_of_le : IsCoatom a ↔ a ≠ ⊤ ∧ ∀ b ≠ ⊤, a ≤ b → b ≤ a :=
  isAtom_iff_le_of_ge (α := αᵒᵈ)

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderTop α] {a b x : α}

theorem IsCoatom.lt_iff (h : IsCoatom a) : a < x ↔ x = ⊤ :=
  h.dual.lt_iff

theorem IsCoatom.le_iff (h : IsCoatom a) : a ≤ x ↔ x = ⊤ ∨ x = a :=
  h.dual.le_iff

lemma IsCoatom.lt_top (h : IsCoatom a) : a < ⊤ :=
  h.lt_iff.mpr rfl

lemma IsCoatom.le_iff_eq (ha : IsCoatom a) (hb : b ≠ ⊤) : a ≤ b ↔ b = a := ha.dual.le_iff_eq hb

theorem IsCoatom.Ici_eq (h : IsCoatom a) : Set.Ici a = {⊤, a} :=
  h.dual.Iic_eq

@[simp]
theorem covBy_top_iff : a ⋖ ⊤ ↔ IsCoatom a :=
  toDual_covBy_toDual_iff.symm.trans bot_covBy_iff

alias ⟨CovBy.isCoatom, IsCoatom.covBy_top⟩ := covBy_top_iff

namespace SetLike

variable {A B : Type*} [SetLike A B]

theorem isAtom_iff [OrderBot A] {K : A} :
    IsAtom K ↔ K ≠ ⊥ ∧ ∀ H g, H ≤ K → g ∉ H → g ∈ K → H = ⊥ := by
  simp_rw [IsAtom, lt_iff_le_not_le, SetLike.not_le_iff_exists,
    and_comm (a := _ ≤ _), and_imp, exists_imp, ← and_imp, and_comm]

theorem isCoatom_iff [OrderTop A] {K : A} :
    IsCoatom K ↔ K ≠ ⊤ ∧ ∀ H g, K ≤ H → g ∉ K → g ∈ H → H = ⊤ := by
  simp_rw [IsCoatom, lt_iff_le_not_le, SetLike.not_le_iff_exists,
    and_comm (a := _ ≤ _), and_imp, exists_imp, ← and_imp, and_comm]

theorem covBy_iff {K L : A} :
    K ⋖ L ↔ K < L ∧ ∀ H g, K ≤ H → H ≤ L → g ∉ K → g ∈ H → H = L := by
  refine and_congr_right fun _ ↦ forall_congr' fun H ↦ not_iff_not.mp ?_
  push_neg
  rw [lt_iff_le_not_le, lt_iff_le_and_ne, and_and_and_comm]
  simp_rw [exists_and_left, and_assoc, and_congr_right_iff, ← and_assoc, and_comm, exists_and_left,
    SetLike.not_le_iff_exists, and_comm, implies_true]

/- Start of proof attempt -/
lemma round1_covBy_iff' {A B : Type*} [SetLike A B] {K L : A} :
    K ⋖ L ↔ K < L ∧ ∀ H g, K ≤ H → H ≤ L → g ∉ H → g ∈ L → H = K := by
  constructor
  · -- Assume K ⋖ L, we need to prove K < L ∧ ∀ H g, K ≤ H → H ≤ L → g ∉ H → g ∈ L → H = K
    intro h1
    have h11 : K < L := by exact?
    have h12 : ∀ H g, K ≤ H → H ≤ L → g ∉ K → g ∈ H → H = L := by
      have h121 : K ⋖ L := h1
      have h122 : K < L ∧ ∀ H g, K ≤ H → H ≤ L → g ∉ K → g ∈ H → H = L := (covBy_iff.mp h121)
      exact h122.2
    have h13 : ∀ H g, K ≤ H → H ≤ L → g ∉ H → g ∈ L → H = K := by
      intro H g h131 h132 h133 h134
      by_cases h135 : H = K
      · -- Case 1: H = K, we are done
        exact h135
      · -- Case 2: H ≠ K
        have h136 : K < H := by
          exact?
        have h137 : ∃ (x : B), x ∈ H ∧ x ∉ K := by
          have h1361 : K < H := h136
          have h1 : K < H := h1361
          have h2 : K ≤ H := le_of_lt h1
          have h3 : K ≠ H := by tauto
          have h4 : ∃ (x : B), x ∈ H ∧ x ∉ K := by
            by_contra h
            push_neg at h
            have h5 : ∀ (x : B), x ∈ H → x ∈ K := by tauto
            have h6 : H ≤ K := by
              intro x hx
              exact h5 x hx
            have h7 : H = K := le_antisymm h6 h2
            tauto
          exact h4
        rcases h137 with ⟨x, hx1, hx2⟩
        have h138 : H = L := by
          exact h12 H x h131 h132 hx2 hx1
        have h139 : g ∉ L := by
          rw [h138] at h133
          tauto
        contradiction
    exact ⟨h11, h13⟩
  · -- Assume K < L ∧ ∀ H g, K ≤ H → H ≤ L → g ∉ H → g ∈ L → H = K, we need to prove K ⋖ L
    rintro ⟨h11, h12⟩
    have h13 : ∀ H g, K ≤ H → H ≤ L → g ∉ K → g ∈ H → H = L := by
      intro H g h131 h132 h133 h134
      by_cases h135 : H = L
      · -- Case 1: H = L, we are done
        exact h135
      · -- Case 2: H ≠ L
        have h136 : H < L := by
          exact?
        have h137 : ∃ (z : B), z ∈ L ∧ z ∉ H := by
          have h1361 : H < L := h136
          have h1 : H < L := h1361
          have h2 : H ≤ L := le_of_lt h1
          have h3 : H ≠ L := by tauto
          have h4 : ∃ (z : B), z ∈ L ∧ z ∉ H := by
            by_contra h
            push_neg at h
            have h5 : ∀ (z : B), z ∈ L → z ∈ H := by tauto
            have h6 : L ≤ H := by
              intro x hx
              exact h5 x hx
            have h7 : L = H := by
              apply le_antisymm <;> tauto
            tauto
          exact h4
        rcases h137 with ⟨z, hz1, hz2⟩
        have h138 : H = K := h12 H z h131 h132 hz2 hz1
        have h139 : g ∈ K := by
          rw [h138] at h134
          tauto
        contradiction
    have h14 : K ⋖ L := by
      rw [covBy_iff]
      exact ⟨h11, h13⟩
    exact h14

/-- Dual variant of `SetLike.covBy_iff` -/
theorem covBy_iff' {K L : A} :
    K ⋖ L ↔ K < L ∧ ∀ H g, K ≤ H → H ≤ L → g ∉ H → g ∈ L → H = K  := by

  exact round1_covBy_iff'
