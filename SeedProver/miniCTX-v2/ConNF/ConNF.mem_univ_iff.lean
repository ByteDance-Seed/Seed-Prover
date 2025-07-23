-- In ConNF/ConNF/External/Basic.lean

import ConNF.Model.Result

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal ConNF.TSet

namespace ConNF

variable [Params.{u}] {α β γ δ ε ζ : Λ} (hβ : (β : TypeIndex) < α) (hγ : (γ : TypeIndex) < β)
  (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < δ) (hζ : (ζ : TypeIndex) < ε)

def union (x y : TSet α) : TSet α :=
  (xᶜ' ⊓' yᶜ')ᶜ'

notation:68 x:68 " ⊔[" h "] " y:68 => _root_.ConNF.union h x y
notation:68 x:68 " ⊔' " y:68 => x ⊔[by assumption] y

@[simp]
theorem mem_union_iff (x y : TSet α) :
    ∀ z : TSet β, z ∈' x ⊔' y ↔ z ∈' x ∨ z ∈' y := by
  rw [union]
  intro z
  rw [mem_compl_iff, mem_inter_iff, mem_compl_iff, mem_compl_iff, or_iff_not_and_not]

def higherIndex (α : Λ) : Λ :=
  (exists_gt α).choose

theorem lt_higherIndex {α : Λ} :
    (α : TypeIndex) < higherIndex α :=
  WithBot.coe_lt_coe.mpr (exists_gt α).choose_spec

theorem tSet_nonempty (h : ∃ β : Λ, (β : TypeIndex) < α) : Nonempty (TSet α) := by
  obtain ⟨α', hα⟩ := h
  constructor
  apply typeLower lt_higherIndex lt_higherIndex lt_higherIndex hα
  apply cardinalOne lt_higherIndex lt_higherIndex

def empty : TSet α :=
  (tSet_nonempty ⟨β, hβ⟩).some ⊓' (tSet_nonempty ⟨β, hβ⟩).someᶜ'

@[simp]
theorem mem_empty_iff :
    ∀ x : TSet β, ¬x ∈' empty hβ := by
  intro x
  rw [empty, mem_inter_iff, mem_compl_iff]
  exact and_not_self

def univ : TSet α :=
  (empty hβ)ᶜ'

/- Start of proof attempt -/
lemma round1_mem_univ_iff (hβ : (β : TypeIndex) < α) :
    ∀ x : TSet β, x ∈' univ hβ := by
  intro x
  have h1 : ¬(x ∈' empty hβ) := by
    exact mem_empty_iff hβ x
  simp only [univ, mem_compl_iff]
  tauto

theorem mem_univ_iff :
    ∀ x : TSet β, x ∈' univ hβ  := by

  exact round1_mem_univ_iff hβ
