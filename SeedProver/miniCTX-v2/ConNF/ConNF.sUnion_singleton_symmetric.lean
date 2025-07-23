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

@[simp]
theorem typedMem_singleton_iff' {α β : Λ} (hβ : (β : TypeIndex) < α) (x y : TSet β) :
    y ∈[hβ] singleton hβ x ↔ y = x :=
  letI : Level := ⟨α⟩
  letI : LeLevel α := ⟨le_rfl⟩
  letI : LtLevel β := ⟨hβ⟩
  typedMem_singleton_iff hβ x y

@[simp]
theorem smul_singleton {α β : Λ} (hβ : (β : TypeIndex) < α) (x : TSet β) (ρ : AllPerm α) :
    ρ • singleton hβ x = singleton hβ (ρ ↘ hβ • x) := by
  apply tSet_ext' hβ
  intro z
  rw [TSet.mem_smul_iff', allPerm_inv_sderiv', typedMem_singleton_iff', typedMem_singleton_iff',
    inv_smul_eq_iff]

theorem singleton_injective {α β : Λ} (hβ : (β : TypeIndex) < α) :
    Function.Injective (singleton hβ) := by
  intro x y hxy
  have := typedMem_singleton_iff' hβ x y
  rw [hxy, typedMem_singleton_iff'] at this
  exact (this.mp rfl).symm

@[simp]
theorem singleton_inj {α β : Λ} {hβ : (β : TypeIndex) < α} {x y : TSet β} :
    singleton hβ x = singleton hβ y ↔ x = y :=
  (singleton_injective hβ).eq_iff

theorem sUnion_singleton_symmetric_aux' {α β γ : Λ}
    (hγ : (γ : TypeIndex) < β) (hβ : (β : TypeIndex) < α) (s : Set (TSet γ)) (S : Support α)
    (hS : ∀ ρ : AllPerm α, ρᵁ • S = S → ρ ↘ hβ • singleton hγ '' s = singleton hγ '' s) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    ∀ (ρ : AllPerm β), ρᵁ • S.strong ↘ hβ = S.strong ↘ hβ → ρ ↘ hγ • s ⊆ s := by
  letI : Level := ⟨α⟩
  letI : LeLevel α := ⟨le_rfl⟩
  letI : LtLevel β := ⟨hβ⟩
  rintro ρ hρ _ ⟨x, hx, rfl⟩
  obtain ⟨T, hT⟩ := exists_support x
  obtain ⟨ρ', hρ'₁, hρ'₂⟩ := Support.exists_allowable_of_fixes S.strong S.strong_strong T ρ hγ hρ
  have hρ's := hS ρ' (smul_eq_of_le (S.subsupport_strong.le) hρ'₁)
  have hρ'x : ρ' ↘ hβ ↘ hγ • x = ρ ↘ hγ • x := by
    apply hT.smul_eq_smul
    simp only [allPermSderiv_forget', allPermSderiv_forget, WithBot.recBotCoe_coe, id_eq, hρ'₂]
  dsimp only
  rw [← hρ'x]
  have := (Set.ext_iff.mp hρ's (ρ' ↘ hβ • singleton hγ x)).mp ⟨_, Set.mem_image_of_mem _ hx, rfl⟩
  rw [smul_singleton] at this
  rwa [(singleton_injective hγ).mem_set_image] at this

theorem sUnion_singleton_symmetric_aux {α β γ : Λ}
    (hγ : (γ : TypeIndex) < β) (hβ : (β : TypeIndex) < α) (s : Set (TSet γ)) (S : Support α)
    (hS : ∀ ρ : AllPerm α, ρᵁ • S = S → ρ ↘ hβ • singleton hγ '' s = singleton hγ '' s) :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    ∀ (ρ : AllPerm β), ρᵁ • S.strong ↘ hβ = S.strong ↘ hβ → ρ ↘ hγ • s = s := by
  intro ρ hρ
  apply subset_antisymm
  · exact sUnion_singleton_symmetric_aux' hγ hβ s S hS ρ hρ
  · have := sUnion_singleton_symmetric_aux' hγ hβ s S hS ρ⁻¹ ?_
    · rwa [allPerm_inv_sderiv', Set.set_smul_subset_iff, inv_inv] at this
    · rw [allPermForget_inv, inv_smul_eq_iff, hρ]

/- Start of proof attempt -/
lemma round1_main {α β γ : Λ} (hγ : (γ : TypeIndex) < β) (hβ : (β : TypeIndex) < α)
    (s : Set (TSet γ)) (hs : Symmetric (singleton hγ '' s) hβ) :
    Symmetric s hγ := by
  rcases hs with ⟨S, hS⟩
  letI : Level := ⟨α⟩
  letI : LeLevel α := ⟨le_rfl⟩
  have h1 : ∀ (ρ : AllPerm β), ρᵁ • S.strong ↘ hβ = S.strong ↘ hβ → ρ ↘ hγ • s = s := by
    exact sUnion_singleton_symmetric_aux hγ hβ s S hS
  refine' ⟨S.strong ↘ hβ, _⟩
  intro ρ hρ
  exact h1 ρ hρ

theorem sUnion_singleton_symmetric {α β γ : Λ} (hγ : (γ : TypeIndex) < β) (hβ : (β : TypeIndex) < α)
    (s : Set (TSet γ)) (hs : Symmetric (singleton hγ '' s) hβ) :
    Symmetric s hγ  := by

  exact round1_main hγ hβ s hs
