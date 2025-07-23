-- In ConNF/ConNF/Levels/Tree.lean

import ConNF.Levels.Path

/-!
# Trees

In this file, we define the notion of a tree on a type.

## Main declarations

* `ConNF.Tree`: The type family of trees parametrised by a given type.
-/

universe u

open Cardinal

namespace ConNF

variable [Params.{u}] {X Y : Type _} {α β γ : TypeIndex}

/-- An `α`-tree of `X` associates an object of type `X` to each path `α ↝ ⊥`. -/
def Tree (X : Type _) (α : TypeIndex) :=
  (α ↝ ⊥) → X

namespace Tree

instance : Derivative (Tree X α) (Tree X β) α β where
  deriv T A B := T (A ⇘ B)

@[simp]
theorem deriv_apply (T : Tree X α) (A : α ↝ β) (B : β ↝ ⊥) :
    (T ⇘ A) B = T (A ⇘ B) :=
  rfl

@[simp]
theorem deriv_nil (T : Tree X α) :
    T ⇘ .nil = T := by
  funext A
  rw [deriv_apply, Path.nil_deriv]

theorem deriv_deriv (T : Tree X α) (A : α ↝ β) (B : β ↝ γ) :
    T ⇘ A ⇘ B = T ⇘ (A ⇘ B) := by
  funext C
  simp only [deriv_apply, Path.deriv_assoc]

theorem deriv_sderiv (T : Tree X α) (A : α ↝ β) (h : γ < β) :
    T ⇘ A ↘ h = T ⇘ (A ↘ h) := by
  rw [← Derivative.deriv_single, ← Derivative.deriv_single, deriv_deriv]

@[simp]
theorem sderiv_apply (T : Tree X α) (h : β < α) (B : β ↝ ⊥) :
    (T ↘ h) B = T (B ↗ h) :=
  rfl

instance : BotDerivative (Tree X α) X α where
  botDeriv T A := T A
  botSderiv T := T <| Path.nil ↘.
  botDeriv_single T h := by
    cases α using WithBot.recBotCoe with
      | bot => cases lt_irrefl ⊥ h
      | coe => rfl

@[simp]
theorem botDeriv_eq (T : Tree X α) (A : α ↝ ⊥) :
    T ⇘. A = T A :=
  rfl

theorem botSderiv_eq (T : Tree X α) :
    T ↘. = T (Path.nil ↘.) :=
  rfl

/-- The group structure on the type of `α`-trees of `X` is given by "branchwise" multiplication,
given by `Pi.group`. -/
instance group [Group X] : Group (Tree X α) :=
  Pi.group

@[simp]
theorem one_apply [Group X] (A : α ↝ ⊥) :
    (1 : Tree X α) A = 1 :=
  rfl

@[simp]
theorem one_deriv [Group X] (A : α ↝ β) :
    (1 : Tree X α) ⇘ A = 1 :=
  rfl

@[simp]
theorem one_sderiv [Group X] (h : β < α) :
    (1 : Tree X α) ↘ h = 1 :=
  rfl

@[simp]
theorem one_sderivBot [Group X] :
    (1 : Tree X α) ↘. = 1 :=
  rfl

@[simp]
theorem mul_apply [Group X] (T₁ T₂ : Tree X α) (A : α ↝ ⊥) :
    (T₁ * T₂) A = T₁ A * T₂ A :=
  rfl

/- Start of proof attempt -/
lemma round1_mul_deriv [Group X] (T₁ T₂ : Tree X α) (A : α ↝ β) :
    (T₁ * T₂) ⇘ A = T₁ ⇘ A * T₂ ⇘ A := by
  funext B
  simp only [deriv_apply, mul_apply]
  <;> rfl

theorem mul_deriv [Group X] (T₁ T₂ : Tree X α) (A : α ↝ β) :
    (T₁ * T₂) ⇘ A = T₁ ⇘ A * T₂ ⇘ A  := by

  exact round1_mul_deriv T₁ T₂ A
