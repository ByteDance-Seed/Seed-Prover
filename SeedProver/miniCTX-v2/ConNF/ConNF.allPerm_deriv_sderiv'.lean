-- In ConNF/ConNF/Model/TTT.lean

import ConNF.Model.RaiseStrong

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal

open scoped Pointwise

namespace ConNF

variable [Params.{u}]

/-- A redefinition of the derivative of allowable permutations that is invariant of level,
but still has nice definitional properties. -/
@[default_instance 200]
instance {β γ : TypeIndex} : Derivative (AllPerm β) (AllPerm γ) β γ where
  deriv ρ A :=
    A.recSderiv
    (motive := λ (δ : TypeIndex) (A : β ↝ δ) ↦
      letI : Level := ⟨δ.recBotCoe (Nonempty.some inferInstance) id⟩
      letI : LeLevel δ := ⟨δ.recBotCoe (λ _ ↦ bot_le) (λ _ h ↦ WithBot.coe_le_coe.mpr h.le)
        (show δ.recBotCoe (Nonempty.some inferInstance) id = Level.α from rfl)⟩
      AllPerm δ)
    ρ (λ δ ε A h ρ ↦
      letI : Level := ⟨δ.recBotCoe (Nonempty.some inferInstance) id⟩
      letI : LeLevel δ := ⟨δ.recBotCoe (λ _ ↦ bot_le) (λ _ h ↦ WithBot.coe_le_coe.mpr h.le)
        (show δ.recBotCoe (Nonempty.some inferInstance) id = Level.α from rfl)⟩
      letI : LeLevel ε := ⟨h.le.trans LeLevel.elim⟩
      PreCoherentData.allPermSderiv h ρ)

@[simp]
theorem allPerm_deriv_nil' {β : TypeIndex}
    (ρ : AllPerm β) :
    ρ ⇘ (.nil : β ↝ β) = ρ :=
  rfl

/- Start of proof attempt -/
lemma round1_allPerm_deriv_sderiv' {β γ δ : TypeIndex}
    (ρ : AllPerm β) (A : β ↝ γ) (h : δ < γ) :
    ρ ⇘ (A ↘ h) = ρ ⇘ A ↘ h  := by
  rfl

theorem allPerm_deriv_sderiv' {β γ δ : TypeIndex}
    (ρ : AllPerm β) (A : β ↝ γ) (h : δ < γ) :
    ρ ⇘ (A ↘ h) = ρ ⇘ A ↘ h  := by

  exact round1_allPerm_deriv_sderiv' ρ A h
