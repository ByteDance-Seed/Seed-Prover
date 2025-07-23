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

@[simp]
theorem allPerm_deriv_sderiv' {β γ δ : TypeIndex}
    (ρ : AllPerm β) (A : β ↝ γ) (h : δ < γ) :
    ρ ⇘ (A ↘ h) = ρ ⇘ A ↘ h :=
  rfl

@[simp]
theorem allPermSderiv_forget' {β γ : TypeIndex} (h : γ < β) (ρ : AllPerm β) :
    (ρ ↘ h)ᵁ = ρᵁ ↘ h :=
  letI : Level := ⟨β.recBotCoe (Nonempty.some inferInstance) id⟩
  letI : LeLevel β := ⟨β.recBotCoe (λ _ ↦ bot_le) (λ _ h ↦ WithBot.coe_le_coe.mpr h.le)
    (show β.recBotCoe (Nonempty.some inferInstance) id = Level.α from rfl)⟩
  letI : LeLevel γ := ⟨h.le.trans LeLevel.elim⟩
  allPermSderiv_forget h ρ

/- Start of proof attempt -/
lemma round1_allPerm_inv_sderiv' {β γ : TypeIndex} (h : γ < β) (ρ : AllPerm β) :
    ρ⁻¹ ↘ h = (ρ ↘ h)⁻¹  := by
  have h1 : (ρ⁻¹ ↘ h)ᵁ = ((ρ ↘ h)⁻¹)ᵁ := by
    have h2 : ((ρ⁻¹) ↘ h)ᵁ = (ρ⁻¹)ᵁ ↘ h := allPermSderiv_forget' h (ρ⁻¹)
    have h3 : ((ρ ↘ h)⁻¹)ᵁ = ((ρ ↘ h)ᵁ)⁻¹ := by aesop
    have h4 : (ρ ↘ h)ᵁ = ρᵁ ↘ h := allPermSderiv_forget' h ρ
    have h5 : (ρ⁻¹)ᵁ = (ρᵁ)⁻¹ := by aesop
    simp [h2, h3, h4, h5]
    <;> aesop
  have h6 : (ρ⁻¹ ↘ h)ᵁ = ((ρ ↘ h)⁻¹)ᵁ := h1
  have h7 : ρ⁻¹ ↘ h = (ρ ↘ h)⁻¹ := by
    have h71 : (ρ⁻¹ ↘ h)ᵁ = ((ρ ↘ h)⁻¹)ᵁ := h6
    have h72 : ρ⁻¹ ↘ h = (ρ ↘ h)⁻¹ := by
      exact?
    exact h72
  exact h7

theorem allPerm_inv_sderiv' {β γ : TypeIndex} (h : γ < β) (ρ : AllPerm β) :
    ρ⁻¹ ↘ h = (ρ ↘ h)⁻¹  := by

  exact round1_allPerm_inv_sderiv' h ρ

end ConNF
