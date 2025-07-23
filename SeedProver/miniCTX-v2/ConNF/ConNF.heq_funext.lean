-- In ConNF/ConNF/Model/Externalise.lean

import ConNF.Model.RunInduction

/-!
# Externalisation

In this file, we convert many of our *internal* results (i.e. inside the induction) to *external*
ones (i.e. defined using the global `TSet`/`AllPerm` definitions).

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal WithBot

namespace ConNF

variable [Params.{u}]

instance globalModelData : {α : TypeIndex} → ModelData α
  | (α : Λ) => (motive α).data
  | ⊥ => botModelData

instance globalPosition : {α : TypeIndex} → Position (Tangle α)
  | (α : Λ) => (motive α).pos
  | ⊥ => botPosition

instance globalTypedNearLitters {α : Λ} : TypedNearLitters α :=
  (motive α).typed

instance globalLtData [Level] : LtData where

instance globalLeData [Level] : LeData where

omit [Params] in

/- Start of proof attempt -/
lemma round1_h1 {α : Sort _} {β γ : α → Sort _} {f : (x : α) → β x} {g : (x : α) → γ x}
  (h : ∀ x, HEq (f x) (g x)):
  ∀ x : α, β x = γ x := by
  intro x
  have h11 : HEq (f x) (g x) := h x
  have h12 : β x = γ x := by
    exact?
  exact h12

lemma round1_h2 {α : Sort _} {β γ : α → Sort _} {f : (x : α) → β x} {g : (x : α) → γ x}
  (h : ∀ x, HEq (f x) (g x))
  (h1 : ∀ x : α, β x = γ x):
  β = γ := by
  funext x
  exact h1 x

lemma round1_h5 {α : Sort _} {β : α → Sort _} {f g : (x : α) → β x}
  (h : ∀ x, HEq (f x) (g x)):
  ∀ x : α, f x = g x := by
  intro x
  have h6 : HEq (f x) (g x) := h x
  have h7 : f x = g x := by
    exact eq_of_heq h6
  exact h7

theorem heq_funext {α : Sort _} {β γ : α → Sort _} {f : (x : α) → β x} {g : (x : α) → γ x}
    (h : ∀ x, HEq (f x) (g x)) : HEq f g  := by

  have h1 : ∀ x : α, β x = γ x := round1_h1 h
  have h2 : β = γ := round1_h2 h h1
  subst h2
  have h5 : ∀ x : α, f x = g x := round1_h5 h
  have h6 : f = g := by
    funext x
    exact h5 x
  rw [h6]
  <;> rfl
