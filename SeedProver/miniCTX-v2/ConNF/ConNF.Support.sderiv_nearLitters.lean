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

/- Start of proof attempt -/
lemma round1_sderiv_nearLitters {α β : TypeIndex} (S : Support α) (h : β < α) :
    Sᴺ ↘ h = (S ↘ h)ᴺ := by
  rfl

theorem sderiv_nearLitters {α β : TypeIndex} (S : Support α) (h : β < α) :
    Sᴺ ↘ h = (S ↘ h)ᴺ  := by

  exact round1_sderiv_nearLitters S h
