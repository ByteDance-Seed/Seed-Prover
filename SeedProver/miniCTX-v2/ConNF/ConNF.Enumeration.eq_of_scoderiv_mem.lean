-- In ConNF/ConNF/ModelData/PathEnumeration.lean

import ConNF.ModelData.Enumeration
import ConNF.Levels.StrPerm

/-!
# Enumerations over paths

In this file, we provide extra features to `Enumeration`s that take values of the form `α ↝ ⊥ × X`.

## Main declarations

* `ConNF.Enumeration.ext_path`: An extensionality principle for such `Enumeration`s.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}]

namespace Enumeration

/-- A helper function for making relations with domain and codomain of the form `α ↝ ⊥ × X`
by defining it on each branch. -/
def relWithPath {X Y : Type u} {α : TypeIndex} (f : α ↝ ⊥ → Rel X Y) :
    Rel (α ↝ ⊥ × X) (α ↝ ⊥ × Y) :=
  λ x y ↦ x.1 = y.1 ∧ f x.1 x.2 y.2

theorem relWithPath_coinjective {X Y : Type u} {α : TypeIndex} {f : α ↝ ⊥ → Rel X Y}
    (hf : ∀ A, (f A).Coinjective) :
    (relWithPath f).Coinjective := by
  constructor
  rintro ⟨_, y₁⟩ ⟨_, y₂⟩ ⟨A, x⟩ ⟨rfl, h₁⟩ ⟨rfl, h₂⟩
  cases (hf A).coinjective h₁ h₂
  rfl

instance (X : Type u) (α β : TypeIndex) :
    Derivative (Enumeration (α ↝ ⊥ × X)) (Enumeration (β ↝ ⊥ × X)) α β where
  deriv E A := E.invImage (λ x ↦ (x.1 ⇗ A, x.2))
    (λ x y h ↦ Prod.ext (Path.deriv_right_injective
      ((Prod.mk.injEq _ _ _ _).mp h).1) ((Prod.mk.injEq _ _ _ _).mp h).2)

theorem deriv_rel {X : Type _} {α β : TypeIndex} (E : Enumeration (α ↝ ⊥ × X)) (A : α ↝ β)
    (i : κ) (x : β ↝ ⊥ × X) :
    (E ⇘ A).rel i x ↔ E.rel i (x.1 ⇗ A, x.2) :=
  Iff.rfl

instance (X : Type u) (α β : TypeIndex) :
    Coderivative (Enumeration (β ↝ ⊥ × X)) (Enumeration (α ↝ ⊥ × X)) α β where
  coderiv E A := E.image (λ x ↦ (x.1 ⇗ A, x.2))

theorem coderiv_rel {X : Type _} {α β : TypeIndex} (E : Enumeration (β ↝ ⊥ × X)) (A : α ↝ β)
    (i : κ) (x : α ↝ ⊥ × X) :
    (E ⇗ A).rel i x ↔ ∃ B, x.1 = A ⇘ B ∧ E.rel i (B, x.2) := by
  constructor
  · rintro ⟨x, h, rfl⟩
    exact ⟨_, rfl, h⟩
  · rintro ⟨B, h₁, h₂⟩
    refine ⟨(B, x.2), h₂, ?_⟩
    apply Prod.ext
    · dsimp only
      exact h₁.symm
    · rfl

theorem scoderiv_rel {X : Type _} {α β : TypeIndex} (E : Enumeration (β ↝ ⊥ × X)) (h : β < α)
    (i : κ) (x : α ↝ ⊥ × X) :
    (E ↗ h).rel i x ↔ ∃ B, x.1 = B ↗ h ∧ E.rel i (B, x.2) :=
  coderiv_rel E (.single h) i x

/- Start of proof attempt -/
lemma round1_main {X : Type _} {α β γ : TypeIndex} (E : Enumeration (β ↝ ⊥ × X))
    (h1 : β < α) (h2 : γ < α)
    (i : κ) (A : γ ↝ ⊥) (x : X) (h3 : (E ↗ h1).rel i ⟨A ↗ h2, x⟩) :
    β = γ := by
  have h4 : ∃ (B : β ↝ ⊥), (A ↗ h2) = B ↗ h1 ∧ E.rel i (B, x) := by
    simpa [scoderiv_rel] using h3
  rcases h4 with ⟨B, h41, h42⟩
  have h41' : B ↗ h1 = A ↗ h2 := by tauto
  exact ConNF.Path.scoderiv_index_injective h41'

theorem eq_of_scoderiv_mem {X : Type _} {α β γ : TypeIndex} (E : Enumeration (β ↝ ⊥ × X))
    (h : β < α) (h' : γ < α)
    (i : κ) (A : γ ↝ ⊥) (x : X) (h : (E ↗ h).rel i ⟨A ↗ h', x⟩) :
    β = γ  := by

  have h1 : β < α := by assumption
  exact round1_main E h1 h' i A x h
