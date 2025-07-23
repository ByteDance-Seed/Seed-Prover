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

@[simp]
theorem allPerm_inv_sderiv' {β γ : TypeIndex} (h : γ < β) (ρ : AllPerm β) :
    ρ⁻¹ ↘ h = (ρ ↘ h)⁻¹ := by
  apply allPermForget_injective
  rw [allPermSderiv_forget', allPermForget_inv, Tree.inv_sderiv, allPermForget_inv,
    allPermSderiv_forget']

def Symmetric {α β : Λ} (s : Set (TSet β)) (hβ : (β : TypeIndex) < α) : Prop :=
  ∃ S : Support α, ∀ ρ : AllPerm α, ρᵁ • S = S → ρ ↘ hβ • s = s

def newSetEquiv {α : Λ} :
    letI : Level := ⟨α⟩
    @TSet _ α newModelData.toPreModelData ≃ TSet α :=
  letI : Level := ⟨α⟩
  castTSet (D₁ := newModelData) (D₂ := globalModelData) rfl
    (by rw [globalModelData, motive_eq, constructMotive, globalLtData_eq])

@[simp]
theorem newSetEquiv_forget {α : Λ}
    (x : letI : Level := ⟨α⟩; @TSet _ α newModelData.toPreModelData) :
    (newSetEquiv x)ᵁ = xᵁ :=
  letI : Level := ⟨α⟩
  castTSet_forget (D₁ := newModelData) (D₂ := globalModelData) _ x

def allPermEquiv {α : Λ} :
    letI : Level := ⟨α⟩
    NewPerm ≃ AllPerm α :=
  letI : Level := ⟨α⟩
  castAllPerm (D₁ := newModelData) (D₂ := globalModelData) rfl
    (by rw [globalModelData, motive_eq, constructMotive, globalLtData_eq])

@[simp]
theorem allPermEquiv_forget {α : Λ} (ρ : letI : Level := ⟨α⟩; NewPerm) :
    (allPermEquiv ρ)ᵁ = ρᵁ :=
  letI : Level := ⟨α⟩
  castAllPerm_forget (D₁ := newModelData) (D₂ := globalModelData) _ ρ

theorem allPermEquiv_sderiv {α β : Λ}
    (ρ : letI : Level := ⟨α⟩; NewPerm) (hβ : (β : TypeIndex) < α) :
    letI : Level := ⟨α⟩
    letI : LtLevel β := ⟨hβ⟩
    allPermEquiv ρ ↘ hβ = ρ.sderiv β := by
  letI : Level := ⟨α⟩
  letI : LeLevel α := ⟨le_rfl⟩
  letI : LtLevel β := ⟨hβ⟩
  apply allPermForget_injective
  rw [allPermSderiv_forget, allPermEquiv_forget, NewPerm.forget_sderiv]

theorem TSet.exists_of_symmetric {α β : Λ} (s : Set (TSet β)) (hβ : (β : TypeIndex) < α)
    (hs : Symmetric s hβ) :
    ∃ x : TSet α, ∀ y : TSet β, y ∈[hβ] x ↔ y ∈ s := by
  letI : Level := ⟨α⟩
  letI : LtLevel β := ⟨hβ⟩
  suffices ∃ x : (@TSet _ α newModelData.toPreModelData), ∀ y : TSet β, yᵁ ∈[hβ] xᵁ ↔ y ∈ s by
    obtain ⟨x, hx⟩ := this
    use newSetEquiv x
    intro y
    rw [← hx, ← TSet.forget_mem_forget, newSetEquiv_forget]
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · use none
    intro y
    simp only [Set.mem_empty_iff_false, iff_false]
    exact not_mem_none y
  · use some (Code.toSet ⟨β, s, hs'⟩ ?_)
    · intro y
      erw [mem_some_iff]
      exact Code.mem_toSet _
    · obtain ⟨S, hS⟩ := hs
      use S
      intro ρ hρS
      have := hS (allPermEquiv ρ) ?_
      · simp only [NewPerm.smul_mk, Code.mk.injEq, heq_eq_eq, true_and]
        rwa [allPermEquiv_sderiv] at this
      · rwa [allPermEquiv_forget]

theorem TSet.exists_support {α : Λ} (x : TSet α) :
    ∃ S : Support α, ∀ ρ : AllPerm α, ρᵁ • S = S → ρ • x = x := by
  letI : Level := ⟨α⟩
  obtain ⟨S, hS⟩ := NewSet.exists_support (newSetEquiv.symm x)
  use S
  intro ρ hρ
  have := @Support.Supports.supports _ _ _ newPreModelData _ _ _ hS (allPermEquiv.symm ρ) ?_
  · apply tSetForget_injective
    have := congr_arg (·ᵁ) this
    simp only at this
    erw [@smul_forget _ _ newModelData (allPermEquiv.symm ρ) (newSetEquiv.symm x),
      ← allPermEquiv_forget, ← newSetEquiv_forget, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply] at this
    rwa [smul_forget]
  · rwa [← allPermEquiv_forget, Equiv.apply_symm_apply]

theorem TSet.symmetric {α β : Λ} (x : TSet α) (hβ : (β : TypeIndex) < α) :
    Symmetric {y : TSet β | y ∈[hβ] x} hβ := by
  obtain ⟨S, hS⟩ := exists_support x
  use S
  intro ρ hρ
  conv_rhs => rw [← hS ρ hρ]
  simp only [← forget_mem_forget, smul_forget, StrSet.mem_smul_iff]
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_setOf_eq, Set.mem_setOf_eq,
    smul_forget, allPermForget_inv, allPermSderiv_forget']

theorem tSet_ext' {α β : Λ} (hβ : (β : TypeIndex) < α) (x y : TSet α)
    (h : ∀ z : TSet β, z ∈[hβ] x ↔ z ∈[hβ] y) : x = y :=
  letI : Level := ⟨α⟩
  letI : LeLevel α := ⟨le_rfl⟩
  letI : LtLevel β := ⟨hβ⟩
  tSet_ext hβ x y h

@[simp]
theorem TSet.mem_smul_iff' {α β : TypeIndex}
    {x : TSet β} {y : TSet α} (h : β < α) (ρ : AllPerm α) :
    x ∈[h] ρ • y ↔ ρ⁻¹ ↘ h • x ∈[h] y := by
  letI : Level := ⟨α.recBotCoe (Nonempty.some inferInstance) id⟩
  letI : LeLevel α := ⟨α.recBotCoe (λ _ ↦ bot_le) (λ _ h ↦ WithBot.coe_le_coe.mpr h.le)
    (show α.recBotCoe (Nonempty.some inferInstance) id = Level.α from rfl)⟩
  letI : LtLevel β := ⟨h.trans_le LeLevel.elim⟩
  exact mem_smul_iff h ρ  -- For some reason, using `exact` instead of term mode speeds this up!

def singleton {α β : Λ} (hβ : (β : TypeIndex) < α) (x : TSet β) : TSet α :=
  letI : Level := ⟨α⟩
  letI : LeLevel α := ⟨le_rfl⟩
  letI : LtLevel β := ⟨hβ⟩
  PreCoherentData.singleton hβ x

/- Start of proof attempt -/
lemma round1_main {α β : Λ} (hβ : (β : TypeIndex) < α) (x y : TSet β) :
    y ∈[hβ] ConNF.singleton hβ x ↔ y = x := by
  constructor
  · intro h
    unfold ConNF.singleton at h
    aesop
  · intro h
    rw [h]
    unfold ConNF.singleton
    aesop

theorem typedMem_singleton_iff' {α β : Λ} (hβ : (β : TypeIndex) < α) (x y : TSet β) :
    y ∈[hβ] singleton hβ x ↔ y = x  := by

  exact round1_main hβ x y
