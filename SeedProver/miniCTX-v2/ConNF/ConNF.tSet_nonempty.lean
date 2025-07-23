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

/- Start of proof attempt -/
lemma round1_main (α : Λ) (h : ∃ β : Λ, (β : TypeIndex) < α) : Nonempty (TSet α) := by
  rcases h with ⟨β₀, h1⟩
  have h2 : (α : TypeIndex) < higherIndex α := ConNF.lt_higherIndex
  have h3 : (higherIndex α : TypeIndex) < higherIndex (higherIndex α) := ConNF.lt_higherIndex
  have h4 : (higherIndex (higherIndex α) : TypeIndex) < higherIndex (higherIndex (higherIndex α)) := ConNF.lt_higherIndex
  set y₁ := higherIndex α with hy₁
  set y₂ := higherIndex (higherIndex α) with hy₂
  set y₃ := higherIndex (higherIndex (higherIndex α)) with hy₃
  have h5 : (α : TypeIndex) < y₁ := h2
  have h6 : (y₁ : TypeIndex) < y₂ := h3
  have h7 : (y₂ : TypeIndex) < y₃ := h4
  have h7' : (y₂ : TypeIndex) < (y₃ : TypeIndex) := h7
  have h6' : (y₁ : TypeIndex) < (y₂ : TypeIndex) := h6
  have h5' : (α : TypeIndex) < (y₁ : TypeIndex) := h5
  have h1' : (β₀ : TypeIndex) < (α : TypeIndex) := h1
  have h10 : ∃ (x : ConNF.TSet y₃), True := by
    refine ⟨ConNF.subset' h7' h6' h5' h1', by trivial⟩
  rcases h10 with ⟨x, _⟩
  have h11 : ∃ (y : ConNF.TSet α), True := by
    refine ⟨ConNF.typeLower h7' h6' h5' h1' x, by trivial⟩
  rcases h11 with ⟨y, _⟩
  exact ⟨y⟩

theorem tSet_nonempty (h : ∃ β : Λ, (β : TypeIndex) < α) : Nonempty (TSet α)  := by

  exact round1_main α h
