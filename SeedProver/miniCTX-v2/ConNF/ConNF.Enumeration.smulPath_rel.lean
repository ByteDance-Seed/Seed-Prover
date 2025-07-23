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

theorem eq_of_scoderiv_mem {X : Type _} {α β γ : TypeIndex} (E : Enumeration (β ↝ ⊥ × X))
    (h : β < α) (h' : γ < α)
    (i : κ) (A : γ ↝ ⊥) (x : X) (h : (E ↗ h).rel i ⟨A ↗ h', x⟩) :
    β = γ := by
  rw [scoderiv_rel] at h
  obtain ⟨B, h₁, h₂⟩ := h
  exact Path.scoderiv_index_injective h₁.symm

instance (X : Type u) (α : TypeIndex) :
    BotDerivative (Enumeration (α ↝ ⊥ × X)) (Enumeration X) α where
  botDeriv E A := E.invImage (λ x ↦ (A, x)) (Prod.mk.inj_left A)
  botSderiv E := E.invImage (λ x ↦ (Path.nil ↘., x)) (Prod.mk.inj_left (Path.nil ↘.))
  botDeriv_single E h := by
    cases α using WithBot.recBotCoe with
    | bot => cases lt_irrefl ⊥ h
    | coe => rfl

theorem derivBot_rel {X : Type _} {α : TypeIndex} (E : Enumeration (α ↝ ⊥ × X)) (A : α ↝ ⊥)
    (i : κ) (x : X) :
    (E ⇘. A).rel i x ↔ E.rel i (A, x) :=
  Iff.rfl

@[simp]
theorem mem_path_iff {X : Type _} {α : TypeIndex} (E : Enumeration (α ↝ ⊥ × X))
    (A : α ↝ ⊥) (x : X) :
    (A, x) ∈ E ↔ x ∈ E ⇘. A :=
  Iff.rfl

theorem ext_path {X : Type u} {α : TypeIndex} {E F : Enumeration (α ↝ ⊥ × X)}
    (h : ∀ A, E ⇘. A = F ⇘. A) :
    E = F := by
  ext i x
  · have := congr_arg bound (h (Path.nil ↘.))
    exact this
  · have := congr_arg rel (h x.1)
    exact iff_of_eq (congr_fun₂ this i x.2)

theorem deriv_derivBot {X : Type _} {α β : TypeIndex} (E : Enumeration (α ↝ ⊥ × X))
    (A : α ↝ β) (B : β ↝ ⊥) :
    E ⇘ A ⇘. B = E ⇘. (A ⇘ B) :=
  rfl

@[simp]
theorem coderiv_deriv_eq {X : Type _} {α β : TypeIndex} (E : Enumeration (β ↝ ⊥ × X)) (A : α ↝ β) :
    E ⇗ A ⇘ A = E := by
  apply ext_path
  intro B
  ext i x
  · rfl
  · simp only [derivBot_rel, deriv_rel, coderiv_rel,
      Path.coderiv_eq_deriv, Path.deriv_right_inj, exists_eq_left']

theorem eq_of_mem_scoderiv_botDeriv {X : Type _} {α β : TypeIndex} {S : Enumeration (β ↝ ⊥ × X)}
    {A : α ↝ ⊥} {h : β < α} {x : X} (hx : x ∈ S ↗ h ⇘. A) :
    ∃ B : β ↝ ⊥, A = B ↗ h := by
  obtain ⟨i, ⟨B, y⟩, hi₁, hi₂⟩ := hx
  cases hi₂
  exact ⟨B, rfl⟩

@[simp]
theorem scoderiv_botDeriv_eq {X : Type _} {α β : TypeIndex} (S : Enumeration (β ↝ ⊥ × X))
    (A : β ↝ ⊥) (h : β < α) :
    S ↗ h ⇘. (A ↗ h) = S ⇘. A := by
  ext i x
  · rfl
  · simp only [derivBot_rel, scoderiv_rel, Path.scoderiv_left_inj, exists_eq_left']

theorem mulAction_aux {X : Type _} {α : TypeIndex} [MulAction BasePerm X] (π : StrPerm α) :
    Function.Injective (λ x : α ↝ ⊥ × X ↦ (x.1, (π x.1)⁻¹ • x.2)) := by
  rintro ⟨A₁, x₁⟩ ⟨A₂, x₂⟩ h
  rw [Prod.mk.injEq] at h
  cases h.1
  exact Prod.ext h.1 (smul_left_cancel _ h.2)

instance {X : Type _} {α : TypeIndex} [MulAction BasePerm X] :
    SMul (StrPerm α) (Enumeration (α ↝ ⊥ × X)) where
  smul π E := E.invImage (λ x ↦ (x.1, (π x.1)⁻¹ • x.2)) (mulAction_aux π)

/- Start of proof attempt -/
lemma round1_smulPath_rel {X : Type _} {α : TypeIndex} [MulAction BasePerm X]
    (π : StrPerm α) (E : Enumeration (α ↝ ⊥ × X)) (i : κ) (x : α ↝ ⊥ × X) :
    (π • E).rel i x ↔ E.rel i (x.1, (π x.1)⁻¹ • x.2) := by
  rfl

theorem smulPath_rel {X : Type _} {α : TypeIndex} [MulAction BasePerm X]
    (π : StrPerm α) (E : Enumeration (α ↝ ⊥ × X)) (i : κ) (x : α ↝ ⊥ × X) :
    (π • E).rel i x ↔ E.rel i (x.1, (π x.1)⁻¹ • x.2)  := by

  exact round1_smulPath_rel π E i x
