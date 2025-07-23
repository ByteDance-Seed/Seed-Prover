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

/- Start of proof attempt -/
lemma round1_scoderiv_rel_forward
  {X : Type _}
  {α β : TypeIndex}
  (E : Enumeration (β ↝ ⊥ × X))
  (h : β < α)
  (i : κ)
  (x : α ↝ ⊥ × X)
  (h1 : (E ↗ h).rel i x):
  ∃ B, x.1 = B ↗ h ∧ E.rel i (B, x.2) := by
  rcases h1 with ⟨y, hy1, hy2⟩
  have h31 : y.2 = x.2 := by
    simp [Prod.ext_iff] at hy2
    tauto
  have h32 : y.1 ↗ h = x.1 := by
    simp [Prod.ext_iff] at hy2
    tauto
  refine ⟨y.1, ?_, ?_⟩
  · -- Prove x.1 = y.1 ↗ h
    rw [← h32]
    <;> rfl
  · -- Prove E.rel i (y.1, x.2)
    have h4 : E.rel i (y.1, y.2) := hy1
    have h5 : y.2 = x.2 := h31
    have h6 : E.rel i (y.1, x.2) := by
      have h61 : E.rel i (y.1, y.2) := h4
      have h62 : y.2 = x.2 := h5
      have h63 : E.rel i (y.1, x.2) := by
        have h64 : (y.1, y.2) = (y.1, x.2) := by
          simp [h62]
        rw [h64] at h61
        tauto
      exact h63
    tauto

lemma round1_scoderiv_rel_backward
  {X : Type _}
  {α β : TypeIndex}
  (E : Enumeration (β ↝ ⊥ × X))
  (h : β < α)
  (i : κ)
  (x : α ↝ ⊥ × X)
  (h2 : ∃ B, x.1 = B ↗ h ∧ E.rel i (B, x.2)):
  (E ↗ h).rel i x := by
  rcases h2 with ⟨B, h1, h2⟩
  refine ⟨(B, x.2), h2, ?_⟩
  simp [h1]
  <;> aesop

theorem scoderiv_rel {X : Type _} {α β : TypeIndex} (E : Enumeration (β ↝ ⊥ × X)) (h : β < α)
    (i : κ) (x : α ↝ ⊥ × X) :
    (E ↗ h).rel i x ↔ ∃ B, x.1 = B ↗ h ∧ E.rel i (B, x.2)  := by

  constructor
  · exact round1_scoderiv_rel_forward E h i x
  · exact round1_scoderiv_rel_backward E h i x
