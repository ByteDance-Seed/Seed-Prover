-- In ConNF/ConNF/ModelData/Support.lean

import ConNF.ModelData.PathEnumeration

/-!
# Supports

In this file, we define the notion of a support.

## Main declarations

* `ConNF.BaseSupport`: The type of supports of atoms.
* `ConNF.Support`: The type of supports of objects of arbitrary type indices.
-/

universe u

open Cardinal

namespace ConNF

variable [Params.{u}]

/-!
## Base supports
-/

structure BaseSupport where
  atoms : Enumeration Atom
  nearLitters : Enumeration NearLitter

namespace BaseSupport

instance : SuperA BaseSupport (Enumeration Atom) where
  superA := atoms

instance : SuperN BaseSupport (Enumeration NearLitter) where
  superN := nearLitters

@[simp]
theorem mk_atoms {a : Enumeration Atom} {N : Enumeration NearLitter} :
    (BaseSupport.mk a N)ᴬ = a :=
  rfl

@[simp]
theorem mk_nearLitters {a : Enumeration Atom} {N : Enumeration NearLitter} :
    (BaseSupport.mk a N)ᴺ = N :=
  rfl

theorem atoms_congr {S T : BaseSupport} (h : S = T) :
    Sᴬ = Tᴬ :=
  h ▸ rfl

theorem nearLitters_congr {S T : BaseSupport} (h : S = T) :
    Sᴺ = Tᴺ :=
  h ▸ rfl

@[ext]
theorem ext {S T : BaseSupport} (h₁ : Sᴬ = Tᴬ) (h₂ : Sᴺ = Tᴺ) : S = T := by
  obtain ⟨SA, SN⟩ := S
  obtain ⟨TA, TN⟩ := T
  cases h₁
  cases h₂
  rfl

instance : SMul BasePerm BaseSupport where
  smul π S := ⟨π • Sᴬ, π • Sᴺ⟩

@[simp]
theorem smul_atoms (π : BasePerm) (S : BaseSupport) :
    (π • S)ᴬ = π • Sᴬ :=
  rfl

@[simp]
theorem smul_nearLitters (π : BasePerm) (S : BaseSupport) :
    (π • S)ᴺ = π • Sᴺ :=
  rfl

@[simp]
theorem smul_atoms_eq_of_smul_eq {π : BasePerm} {S : BaseSupport}
    (h : π • S = S) :
    π • Sᴬ = Sᴬ := by
  rw [← smul_atoms, h]

@[simp]
theorem smul_nearLitters_eq_of_smul_eq {π : BasePerm} {S : BaseSupport}
    (h : π • S = S) :
    π • Sᴺ = Sᴺ := by
  rw [← smul_nearLitters, h]

instance : MulAction BasePerm BaseSupport where
  one_smul S := by
    apply ext
    · rw [smul_atoms, one_smul]
    · rw [smul_nearLitters, one_smul]
  mul_smul π₁ π₂ S := by
    apply ext
    · rw [smul_atoms, smul_atoms, smul_atoms, mul_smul]
    · rw [smul_nearLitters, smul_nearLitters, smul_nearLitters, mul_smul]

theorem smul_eq_smul_iff (π₁ π₂ : BasePerm) (S : BaseSupport) :
    π₁ • S = π₂ • S ↔ (∀ a ∈ Sᴬ, π₁ • a = π₂ • a) ∧ (∀ N ∈ Sᴺ, π₁ • N = π₂ • N) := by
  constructor
  · intro h
    constructor
    · rintro a ⟨i, ha⟩
      have := congr_arg (·ᴬ.rel i (π₁ • a)) h
      simp only [smul_atoms, Enumeration.smul_rel, inv_smul_smul, eq_iff_iff] at this
      have := Sᴬ.rel_coinjective.coinjective ha (this.mp ha)
      rw [eq_inv_smul_iff] at this
      rw [this]
    · rintro N ⟨i, hN⟩
      have := congr_arg (·ᴺ.rel i (π₁ • N)) h
      simp only [smul_nearLitters, Enumeration.smul_rel, inv_smul_smul, eq_iff_iff] at this
      have := Sᴺ.rel_coinjective.coinjective hN (this.mp hN)
      rw [eq_inv_smul_iff] at this
      rw [this]
  · intro h
    ext : 2
    · rfl
    · ext i a : 3
      rw [smul_atoms, smul_atoms, Enumeration.smul_rel, Enumeration.smul_rel]
      constructor
      · intro ha
        have := h.1 _ ⟨i, ha⟩
        rw [smul_inv_smul, ← inv_smul_eq_iff] at this
        rwa [this]
      · intro ha
        have := h.1 _ ⟨i, ha⟩
        rw [smul_inv_smul, smul_eq_iff_eq_inv_smul] at this
        rwa [← this]
    · rfl
    · ext i a : 3
      rw [smul_nearLitters, smul_nearLitters, Enumeration.smul_rel, Enumeration.smul_rel]
      constructor
      · intro hN
        have := h.2 _ ⟨i, hN⟩
        rw [smul_inv_smul, ← inv_smul_eq_iff] at this
        rwa [this]
      · intro hN
        have := h.2 _ ⟨i, hN⟩
        rw [smul_inv_smul, smul_eq_iff_eq_inv_smul] at this
        rwa [← this]

theorem smul_eq_iff (π : BasePerm) (S : BaseSupport) :
    π • S = S ↔ (∀ a ∈ Sᴬ, π • a = a) ∧ (∀ N ∈ Sᴺ, π • N = N) := by
  have := smul_eq_smul_iff π 1 S
  simp only [one_smul] at this
  exact this

noncomputable instance : Add BaseSupport where
  add S T := ⟨Sᴬ + Tᴬ, Sᴺ + Tᴺ⟩

@[simp]
theorem add_atoms (S T : BaseSupport) :
    (S + T)ᴬ = Sᴬ + Tᴬ :=
  rfl

@[simp]
theorem add_nearLitters (S T : BaseSupport) :
    (S + T)ᴺ = Sᴺ + Tᴺ :=
  rfl

end BaseSupport

def baseSupportEquiv : BaseSupport ≃ Enumeration Atom × Enumeration NearLitter where
  toFun S := (Sᴬ, Sᴺ)
  invFun S := ⟨S.1, S.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_baseSupport : #BaseSupport = #μ := by
  rw [Cardinal.eq.mpr ⟨baseSupportEquiv⟩, mk_prod, lift_id, lift_id,
    card_enumeration_eq card_atom, card_enumeration_eq card_nearLitter, mul_eq_self aleph0_lt_μ.le]

/-!
## Structural supports
-/

structure Support (α : TypeIndex) where
  atoms : Enumeration (α ↝ ⊥ × Atom)
  nearLitters : Enumeration (α ↝ ⊥ × NearLitter)

namespace Support

variable {α β : TypeIndex}

instance : SuperA (Support α) (Enumeration (α ↝ ⊥ × Atom)) where
  superA := atoms

instance : SuperN (Support α) (Enumeration (α ↝ ⊥ × NearLitter)) where
  superN := nearLitters

@[simp]
theorem mk_atoms (E : Enumeration (α ↝ ⊥ × Atom)) (F : Enumeration (α ↝ ⊥ × NearLitter)) :
    (⟨E, F⟩ : Support α)ᴬ = E :=
  rfl

@[simp]
theorem mk_nearLitters (E : Enumeration (α ↝ ⊥ × Atom)) (F : Enumeration (α ↝ ⊥ × NearLitter)) :
    (⟨E, F⟩ : Support α)ᴺ = F :=
  rfl

instance : Derivative (Support α) (Support β) α β where
  deriv S A := ⟨Sᴬ ⇘ A, Sᴺ ⇘ A⟩

instance : Coderivative (Support β) (Support α) α β where
  coderiv S A := ⟨Sᴬ ⇗ A, Sᴺ ⇗ A⟩

instance : BotDerivative (Support α) BaseSupport α where
  botDeriv S A := ⟨Sᴬ ⇘. A, Sᴺ ⇘. A⟩
  botSderiv S := ⟨Sᴬ ↘., Sᴺ ↘.⟩
  botDeriv_single S h := by dsimp only; rw [botDeriv_single, botDeriv_single]

@[simp]
theorem deriv_atoms {α β : TypeIndex} (S : Support α) (A : α ↝ β) :
    Sᴬ ⇘ A = (S ⇘ A)ᴬ :=
  rfl

@[simp]
theorem deriv_nearLitters {α β : TypeIndex} (S : Support α) (A : α ↝ β) :
    Sᴺ ⇘ A = (S ⇘ A)ᴺ :=
  rfl

@[simp]
theorem sderiv_atoms {α β : TypeIndex} (S : Support α) (h : β < α) :
    Sᴬ ↘ h = (S ↘ h)ᴬ :=
  rfl

@[simp]
theorem sderiv_nearLitters {α β : TypeIndex} (S : Support α) (h : β < α) :
    Sᴺ ↘ h = (S ↘ h)ᴺ :=
  rfl

@[simp]
theorem coderiv_atoms {α β : TypeIndex} (S : Support β) (A : α ↝ β) :
    Sᴬ ⇗ A = (S ⇗ A)ᴬ :=
  rfl

@[simp]
theorem coderiv_nearLitters {α β : TypeIndex} (S : Support β) (A : α ↝ β) :
    Sᴺ ⇗ A = (S ⇗ A)ᴺ :=
  rfl

@[simp]
theorem scoderiv_atoms {α β : TypeIndex} (S : Support β) (h : β < α) :
    Sᴬ ↗ h = (S ↗ h)ᴬ :=
  rfl

@[simp]
theorem scoderiv_nearLitters {α β : TypeIndex} (S : Support β) (h : β < α) :
    Sᴺ ↗ h = (S ↗ h)ᴺ :=
  rfl

@[simp]
theorem derivBot_atoms {α : TypeIndex} (S : Support α) (A : α ↝ ⊥) :
    Sᴬ ⇘. A = (S ⇘. A)ᴬ :=
  rfl

@[simp]
theorem derivBot_nearLitters {α : TypeIndex} (S : Support α) (A : α ↝ ⊥) :
    Sᴺ ⇘. A = (S ⇘. A)ᴺ :=
  rfl

theorem ext' {S T : Support α} (h₁ : Sᴬ = Tᴬ) (h₂ : Sᴺ = Tᴺ) : S = T := by
  obtain ⟨SA, SN⟩ := S
  obtain ⟨TA, TN⟩ := T
  cases h₁
  cases h₂
  rfl

@[ext]
theorem ext {S T : Support α} (h : ∀ A, S ⇘. A = T ⇘. A) : S = T := by
  obtain ⟨SA, SN⟩ := S
  obtain ⟨TA, TN⟩ := T
  rw [mk.injEq]
  constructor
  · apply Enumeration.ext_path
    intro A
    exact BaseSupport.atoms_congr (h A)
  · apply Enumeration.ext_path
    intro A
    exact BaseSupport.nearLitters_congr (h A)

@[simp]
theorem deriv_derivBot {α : TypeIndex} (S : Support α)
    (A : α ↝ β) (B : β ↝ ⊥) :
    S ⇘ A ⇘. B = S ⇘. (A ⇘ B) :=
  rfl

@[simp]
theorem coderiv_deriv_eq {α β : TypeIndex} (S : Support β) (A : α ↝ β) :
    S ⇗ A ⇘ A = S :=
  ext' (Sᴬ.coderiv_deriv_eq A) (Sᴺ.coderiv_deriv_eq A)

theorem eq_of_atom_mem_scoderiv_botDeriv {α β : TypeIndex} {S : Support β} {A : α ↝ ⊥}
    {h : β < α} {a : Atom} (ha : a ∈ (S ↗ h ⇘. A)ᴬ) :
    ∃ B : β ↝ ⊥, A = B ↗ h :=
  Enumeration.eq_of_mem_scoderiv_botDeriv ha

theorem eq_of_nearLitter_mem_scoderiv_botDeriv {α β : TypeIndex} {S : Support β} {A : α ↝ ⊥}
    {h : β < α} {N : NearLitter} (hN : N ∈ (S ↗ h ⇘. A)ᴺ) :
    ∃ B : β ↝ ⊥, A = B ↗ h :=
  Enumeration.eq_of_mem_scoderiv_botDeriv hN

@[simp]
theorem scoderiv_botDeriv_eq {α β : TypeIndex} (S : Support β) (A : β ↝ ⊥) (h : β < α) :
    S ↗ h ⇘. (A ↗ h) = S ⇘. A :=
  BaseSupport.ext (Enumeration.scoderiv_botDeriv_eq _ _ _) (Enumeration.scoderiv_botDeriv_eq _ _ _)

@[simp]
theorem scoderiv_deriv_eq {α β γ : TypeIndex} (S : Support β) (A : β ↝ γ) (h : β < α) :
    S ↗ h ⇘ (A ↗ h) = S ⇘ A := by
  apply ext
  intro B
  simp only [deriv_derivBot, ← scoderiv_botDeriv_eq S (A ⇘ B) h, Path.coderiv_deriv']

@[simp]
theorem coderiv_inj {α β : TypeIndex} (S T : Support β) (A : α ↝ β) :
    S ⇗ A = T ⇗ A ↔ S = T := by
  constructor
  swap
  · rintro rfl
    rfl
  intro h
  ext B : 1
  have : S ⇗ A ⇘ A ⇘. B = T ⇗ A ⇘ A ⇘. B := by rw [h]
  rwa [coderiv_deriv_eq, coderiv_deriv_eq] at this

@[simp]
theorem scoderiv_inj {α β : TypeIndex} (S T : Support β) (h : β < α) :
    S ↗ h = T ↗ h ↔ S = T :=
  coderiv_inj S T (.single h)

instance {α : TypeIndex} : SMul (StrPerm α) (Support α) where
  smul π S := ⟨π • Sᴬ, π • Sᴺ⟩

@[simp]
theorem smul_atoms {α : TypeIndex} (π : StrPerm α) (S : Support α) :
    (π • S)ᴬ = π • Sᴬ :=
  rfl

@[simp]
theorem smul_nearLitters {α : TypeIndex} (π : StrPerm α) (S : Support α) :
    (π • S)ᴺ = π • Sᴺ :=
  rfl

theorem smul_atoms_eq_of_smul_eq {α : TypeIndex} {π : StrPerm α} {S : Support α}
    (h : π • S = S) :
    π • Sᴬ = Sᴬ := by
  rw [← smul_atoms, h]

theorem smul_nearLitters_eq_of_smul_eq {α : TypeIndex} {π : StrPerm α} {S : Support α}
    (h : π • S = S) :
    π • Sᴺ = Sᴺ := by
  rw [← smul_nearLitters, h]

instance {α : TypeIndex} : MulAction (StrPerm α) (Support α) where
  one_smul S := by
    apply ext'
    · rw [smul_atoms, one_smul]
    · rw [smul_nearLitters, one_smul]
  mul_smul π₁ π₂ S := by
    apply ext'
    · rw [smul_atoms, smul_atoms, smul_atoms, mul_smul]
    · rw [smul_nearLitters, smul_nearLitters, smul_nearLitters, mul_smul]

@[simp]
theorem smul_derivBot {α : TypeIndex} (π : StrPerm α) (S : Support α) (A : α ↝ ⊥) :
    (π • S) ⇘. A = π A • (S ⇘. A) :=
  rfl

theorem smul_coderiv {α : TypeIndex} (π : StrPerm α) (S : Support β) (A : α ↝ β) :
    π • S ⇗ A = (π ⇘ A • S) ⇗ A := by
  ext B i x
  · rfl
  · constructor
    · rintro ⟨⟨C, x⟩, hS, hx⟩
      simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨⟨C, x⟩, hS, rfl⟩
    · rintro ⟨⟨C, x⟩, hS, hx⟩
      simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨⟨C, _⟩, hS, rfl⟩
  · rfl
  · constructor
    · rintro ⟨⟨C, x⟩, hS, hx⟩
      simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨⟨C, x⟩, hS, rfl⟩
    · rintro ⟨⟨C, a⟩, hS, hx⟩
      simp only [Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨⟨C, _⟩, hS, rfl⟩

theorem smul_scoderiv {α : TypeIndex} (π : StrPerm α) (S : Support β) (h : β < α) :
    π • S ↗ h = (π ↘ h • S) ↗ h :=
  smul_coderiv π S (Path.single h)

theorem smul_eq_smul_iff (π₁ π₂ : StrPerm β) (S : Support β) :
    π₁ • S = π₂ • S ↔
      ∀ A, (∀ a ∈ (S ⇘. A)ᴬ, π₁ A • a = π₂ A • a) ∧ (∀ N ∈ (S ⇘. A)ᴺ, π₁ A • N = π₂ A • N) := by
  constructor
  · intro h A
    have := congr_arg (· ⇘. A) h
    simp only [smul_derivBot, BaseSupport.smul_eq_smul_iff] at this
    exact this
  · intro h
    apply ext
    intro A
    simp only [smul_derivBot, BaseSupport.smul_eq_smul_iff]
    exact h A

theorem smul_eq_iff (π : StrPerm β) (S : Support β) :
    π • S = S ↔ ∀ A, (∀ a ∈ (S ⇘. A)ᴬ, π A • a = a) ∧ (∀ N ∈ (S ⇘. A)ᴺ, π A • N = N) := by
  have := smul_eq_smul_iff π 1 S
  simp only [one_smul, Tree.one_apply] at this
  exact this

noncomputable instance : Add (Support α) where
  add S T := ⟨Sᴬ + Tᴬ, Sᴺ + Tᴺ⟩

@[simp]
theorem add_derivBot (S T : Support α) (A : α ↝ ⊥) :
    (S + T) ⇘. A = (S ⇘. A) + (T ⇘. A) :=
  rfl

theorem smul_add (S T : Support α) (π : StrPerm α) :
    π • (S + T) = π • S + π • T :=
  rfl

theorem add_inj_of_bound_eq_bound {S T U V : Support α}
    (ha : Sᴬ.bound = Tᴬ.bound) (hN : Sᴺ.bound = Tᴺ.bound)
    (h' : S + U = T + V) : S = T ∧ U = V := by
  have ha' := Enumeration.add_inj_of_bound_eq_bound ha (congr_arg (·ᴬ) h')
  have hN' := Enumeration.add_inj_of_bound_eq_bound hN (congr_arg (·ᴺ) h')
  constructor
  · exact Support.ext' ha'.1 hN'.1
  · exact Support.ext' ha'.2 hN'.2

end Support

def supportEquiv {α : TypeIndex} : Support α ≃
    Enumeration (α ↝ ⊥ × Atom) × Enumeration (α ↝ ⊥ × NearLitter) where
  toFun S := (Sᴬ, Sᴺ)
  invFun S := ⟨S.1, S.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_support {α : TypeIndex} : #(Support α) = #μ := by
  rw [Cardinal.eq.mpr ⟨supportEquiv⟩, mk_prod, lift_id, lift_id,
    card_enumeration_eq, card_enumeration_eq, mul_eq_self aleph0_lt_μ.le]
  · rw [mk_prod, lift_id, lift_id, card_nearLitter,
      mul_eq_right aleph0_lt_μ.le (card_path_lt' α ⊥).le (card_path_ne_zero α)]
  · rw [mk_prod, lift_id, lift_id, card_atom,
      mul_eq_right aleph0_lt_μ.le (card_path_lt' α ⊥).le (card_path_ne_zero α)]

/-!
## Orders on supports
-/

-- TODO: Is this order used?
instance : LE BaseSupport where
  le S T := (∀ a ∈ Sᴬ, a ∈ Tᴬ) ∧ (∀ N ∈ Sᴺ, N ∈ Tᴺ)

instance : Preorder BaseSupport where
  le_refl S := ⟨λ _ ↦ id, λ _ ↦ id⟩
  le_trans S T U h₁ h₂ := ⟨λ a h ↦ h₂.1 _ (h₁.1 a h), λ N h ↦ h₂.2 _ (h₁.2 N h)⟩

theorem BaseSupport.smul_le_smul {S T : BaseSupport} (h : S ≤ T) (π : BasePerm) :
    π • S ≤ π • T := by
  constructor
  · intro a
    exact h.1 (π⁻¹ • a)
  · intro N
    exact h.2 (π⁻¹ • N)

theorem BaseSupport.le_add_right {S T : BaseSupport} :
    S ≤ S + T := by
  constructor
  · intro a ha
    simp only [Support.add_derivBot, BaseSupport.add_atoms, Enumeration.mem_add_iff]
    exact Or.inl ha
  · intro N hN
    simp only [Support.add_derivBot, BaseSupport.add_nearLitters, Enumeration.mem_add_iff]
    exact Or.inl hN

theorem BaseSupport.le_add_left {S T : BaseSupport} :
    S ≤ T + S := by
  constructor
  · intro a ha
    simp only [add_atoms, Enumeration.mem_add_iff]
    exact Or.inr ha
  · intro N hN
    simp only [add_nearLitters, Enumeration.mem_add_iff]
    exact Or.inr hN

def BaseSupport.Subsupport (S T : BaseSupport) : Prop :=
  Sᴬ.rel ≤ Tᴬ.rel ∧ Sᴺ.rel ≤ Tᴺ.rel

theorem BaseSupport.Subsupport.le {S T : BaseSupport}
    (h : S.Subsupport T) : S ≤ T := by
  constructor
  · rintro a ⟨i, hi⟩
    exact ⟨i, h.1 i a hi⟩
  · rintro N ⟨i, hi⟩
    exact ⟨i, h.2 i N hi⟩

theorem BaseSupport.Subsupport.trans {S T U : BaseSupport}
    (h₁ : S.Subsupport T) (h₂ : T.Subsupport U) :
    S.Subsupport U :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem BaseSupport.smul_subsupport_smul {S T : BaseSupport} (h : S.Subsupport T) (π : BasePerm) :
    (π • S).Subsupport (π • T) := by
  constructor
  · intro i a ha
    exact h.1 i _ ha
  · intro i N hN
    exact h.2 i _ hN

instance {α : TypeIndex} : LE (Support α) where
  le S T := ∀ A, S ⇘. A ≤ T ⇘. A

instance {α : TypeIndex} : Preorder (Support α) where
  le_refl S := λ A ↦ le_rfl
  le_trans S T U h₁ h₂ := λ A ↦ (h₁ A).trans (h₂ A)

theorem Support.smul_le_smul {α : TypeIndex} {S T : Support α} (h : S ≤ T) (π : StrPerm α) :
    π • S ≤ π • T :=
  λ A ↦ BaseSupport.smul_le_smul (h A) (π A)

theorem Support.le_add_right {α : TypeIndex} {S T : Support α} :
    S ≤ S + T := by
  intro A
  rw [add_derivBot]
  exact BaseSupport.le_add_right

/- Start of proof attempt -/
lemma round1_Support_le_add_left {α : TypeIndex} (S T : Support α) :
    S ≤ T + S := by
  intro A
  have h1 : S ⇘. A ≤ (T ⇘. A) + (S ⇘. A) := BaseSupport.le_add_left
  have h2 : (T + S) ⇘. A = (T ⇘. A) + (S ⇘. A) := by
    simp [Support.add_derivBot]
  rw [h2]
  exact h1

theorem Support.le_add_left {α : TypeIndex} {S T : Support α} :
    S ≤ T + S  := by

  exact round1_Support_le_add_left S T
