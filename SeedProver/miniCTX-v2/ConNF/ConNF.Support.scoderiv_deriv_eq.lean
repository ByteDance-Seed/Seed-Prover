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

/- Start of proof attempt -/
lemma round1_h11 (α β γ : TypeIndex)
  (S : Support β)
  (A : β ↝ γ)
  (h : β < α):
  ∀ (i : κ) (x : γ ↝ ⊥ × Atom), ((Sᴬ ↗ h) ⇘ (A ↗ h)).rel i x ↔ (Sᴬ ⇘ A).rel i x := by
  intro i x
  have h_path : x.1 ⇗ (A ↗ h) = (x.1 ⇗ A) ↗ h := by
    have h1 : x.1 ⇗ (A ↗ h) = (A ↗ h) ⇘ x.1 := by
      rw [ConNF.Path.coderiv_eq_deriv]
    have h2 : (A ↗ h) ⇘ x.1 = (A ⇘ x.1) ↗ h := by
      apply ConNF.Path.coderiv_deriv'
    have h3 : A ⇘ x.1 = x.1 ⇗ A := by
      rw [ConNF.Path.coderiv_eq_deriv]
    rw [h1, h2, h3]
  have h4 : ((Sᴬ ↗ h) ⇘ (A ↗ h)).rel i x ↔ ∃ (B : β ↝ ⊥), (x.1 ⇗ (A ↗ h)) = B ↗ h ∧ Sᴬ.rel i (B, x.2) := by
    rw [ConNF.Enumeration.deriv_rel]
    <;> rw [ConNF.Enumeration.scoderiv_rel]
    <;> aesop
  have h5 : ((Sᴬ ↗ h) ⇘ (A ↗ h)).rel i x ↔ ∃ (B : β ↝ ⊥), ((x.1 ⇗ A) ↗ h) = B ↗ h ∧ Sᴬ.rel i (B, x.2) := by
    rw [h4]
    constructor
    · rintro ⟨B, hB1, hB2⟩
      have h6 : (x.1 ⇗ (A ↗ h)) = B ↗ h := hB1
      have h7 : ((x.1 ⇗ A) ↗ h) = B ↗ h := by
        rw [h_path] at h6
        tauto
      refine ⟨B, h7, hB2⟩
    · rintro ⟨B, hB1, hB2⟩
      have h6 : ((x.1 ⇗ A) ↗ h) = B ↗ h := hB1
      have h7 : (x.1 ⇗ (A ↗ h)) = B ↗ h := by
        rw [h_path]
        tauto
      refine ⟨B, h7, hB2⟩
  have h6 : (∃ (B : β ↝ ⊥), ((x.1 ⇗ A) ↗ h) = B ↗ h ∧ Sᴬ.rel i (B, x.2)) ↔ Sᴬ.rel i (x.1 ⇗ A, x.2) := by
    constructor
    · rintro ⟨B, hB1, hB2⟩
      have hB3 : (x.1 ⇗ A) = B := by
        have h9 : ((x.1 ⇗ A) ↗ h) = B ↗ h := hB1
        exact (ConNF.Path.scoderiv_left_inj).mp h9
      have hB3' : B = x.1 ⇗ A := by rw [hB3]
      rw [hB3'] at hB2
      tauto
    · intro hB2
      refine ⟨x.1 ⇗ A, rfl, hB2⟩
  have h7 : ((Sᴬ ↗ h) ⇘ (A ↗ h)).rel i x ↔ Sᴬ.rel i (x.1 ⇗ A, x.2) := by
    rw [h5, h6]
  have h8 : (Sᴬ ⇘ A).rel i x ↔ Sᴬ.rel i (x.1 ⇗ A, x.2) := by
    rw [ConNF.Enumeration.deriv_rel]
    <;> aesop
  tauto

lemma round1_h11' (α β γ : TypeIndex)
  (S : Support β)
  (A : β ↝ γ)
  (h : β < α)
  (h11 : ∀ (i : κ) (x : γ ↝ ⊥ × Atom), ((Sᴬ ↗ h) ⇘ (A ↗ h)).rel i x ↔ (Sᴬ ⇘ A).rel i x):
  ∀ (x : γ ↝ ⊥ × Atom), (∃ i, ((Sᴬ ↗ h) ⇘ (A ↗ h)).rel i x) ↔ (∃ i, (Sᴬ ⇘ A).rel i x) := by
  intro x
  constructor
  · rintro ⟨i, h111⟩
    have h112 : (Sᴬ ⇘ A).rel i x := by
      have h113 := (h11 i x).mp h111
      tauto
    refine ⟨i, h112⟩
  · rintro ⟨i, h111⟩
    have h112 : ((Sᴬ ↗ h) ⇘ (A ↗ h)).rel i x := by
      have h113 := (h11 i x).mpr h111
      tauto
    refine ⟨i, h112⟩

lemma round1_h21 (α β γ : TypeIndex)
  (S : Support β)
  (A : β ↝ γ)
  (h : β < α):
  ∀ (i : κ) (x : γ ↝ ⊥ × NearLitter), ((Sᴺ ↗ h) ⇘ (A ↗ h)).rel i x ↔ (Sᴺ ⇘ A).rel i x := by
  intro i x
  have h_path : x.1 ⇗ (A ↗ h) = (x.1 ⇗ A) ↗ h := by
    have h1 : x.1 ⇗ (A ↗ h) = (A ↗ h) ⇘ x.1 := by
      rw [ConNF.Path.coderiv_eq_deriv]
    have h2 : (A ↗ h) ⇘ x.1 = (A ⇘ x.1) ↗ h := by
      apply ConNF.Path.coderiv_deriv'
    have h3 : A ⇘ x.1 = x.1 ⇗ A := by
      rw [ConNF.Path.coderiv_eq_deriv]
    rw [h1, h2, h3]
  have h4 : ((Sᴺ ↗ h) ⇘ (A ↗ h)).rel i x ↔ ∃ (B : β ↝ ⊥), (x.1 ⇗ (A ↗ h)) = B ↗ h ∧ Sᴺ.rel i (B, x.2) := by
    rw [ConNF.Enumeration.deriv_rel]
    <;> rw [ConNF.Enumeration.scoderiv_rel]
    <;> aesop
  have h5 : ((Sᴺ ↗ h) ⇘ (A ↗ h)).rel i x ↔ ∃ (B : β ↝ ⊥), ((x.1 ⇗ A) ↗ h) = B ↗ h ∧ Sᴺ.rel i (B, x.2) := by
    rw [h4]
    constructor
    · rintro ⟨B, hB1, hB2⟩
      have h6 : (x.1 ⇗ (A ↗ h)) = B ↗ h := hB1
      have h7 : ((x.1 ⇗ A) ↗ h) = B ↗ h := by
        rw [h_path] at h6
        tauto
      refine ⟨B, h7, hB2⟩
    · rintro ⟨B, hB1, hB2⟩
      have h6 : ((x.1 ⇗ A) ↗ h) = B ↗ h := hB1
      have h7 : (x.1 ⇗ (A ↗ h)) = B ↗ h := by
        rw [h_path]
        tauto
      refine ⟨B, h7, hB2⟩
  have h6 : (∃ (B : β ↝ ⊥), ((x.1 ⇗ A) ↗ h) = B ↗ h ∧ Sᴺ.rel i (B, x.2)) ↔ Sᴺ.rel i (x.1 ⇗ A, x.2) := by
    constructor
    · rintro ⟨B, hB1, hB2⟩
      have hB3 : (x.1 ⇗ A) = B := by
        have h9 : ((x.1 ⇗ A) ↗ h) = B ↗ h := hB1
        exact (ConNF.Path.scoderiv_left_inj).mp h9
      have hB3' : B = x.1 ⇗ A := by rw [hB3]
      rw [hB3'] at hB2
      tauto
    · intro hB2
      refine ⟨x.1 ⇗ A, rfl, hB2⟩
  have h7 : ((Sᴺ ↗ h) ⇘ (A ↗ h)).rel i x ↔ Sᴺ.rel i (x.1 ⇗ A, x.2) := by
    rw [h5, h6]
  have h8 : (Sᴺ ⇘ A).rel i x ↔ Sᴺ.rel i (x.1 ⇗ A, x.2) := by
    rw [ConNF.Enumeration.deriv_rel]
    <;> aesop
  tauto

lemma round1_h21' (α β γ : TypeIndex)
  (S : Support β)
  (A : β ↝ γ)
  (h : β < α)
  (h21 : ∀ (i : κ) (x : γ ↝ ⊥ × NearLitter), ((Sᴺ ↗ h) ⇘ (A ↗ h)).rel i x ↔ (Sᴺ ⇘ A).rel i x):
  ∀ (x : γ ↝ ⊥ × NearLitter), (∃ i, ((Sᴺ ↗ h) ⇘ (A ↗ h)).rel i x) ↔ (∃ i, (Sᴺ ⇘ A).rel i x) := by
  intro x
  constructor
  · rintro ⟨i, h211⟩
    have h212 : (Sᴺ ⇘ A).rel i x := by
      have h213 := (h21 i x).mp h211
      tauto
    refine ⟨i, h212⟩
  · rintro ⟨i, h211⟩
    have h212 : ((Sᴺ ↗ h) ⇘ (A ↗ h)).rel i x := by
      have h213 := (h21 i x).mpr h211
      tauto
    refine ⟨i, h212⟩

lemma round1_h12 (α β γ : TypeIndex)
  (S : Support β)
  (A : β ↝ γ)
  (h : β < α)
  (h11 : ∀ (i : κ) (x : γ ↝ ⊥ × Atom), ((Sᴬ ↗ h) ⇘ (A ↗ h)).rel i x ↔ (Sᴬ ⇘ A).rel i x)
  (h11' : ∀ (x : γ ↝ ⊥ × Atom), (∃ i, ((Sᴬ ↗ h) ⇘ (A ↗ h)).rel i x) ↔ (∃ i, (Sᴬ ⇘ A).rel i x)):
  (Sᴬ ↗ h) ⇘ (A ↗ h) = Sᴬ ⇘ A := by
  have h121 : (Sᴬ ↗ h) ⇘ (A ↗ h) = Sᴬ ⇘ A := by
    apply Enumeration.ext
    <;> aesop
  exact h121

lemma round1_h22 (α β γ : TypeIndex)
  (S : Support β)
  (A : β ↝ γ)
  (h : β < α)
  (h21 : ∀ (i : κ) (x : γ ↝ ⊥ × NearLitter), ((Sᴺ ↗ h) ⇘ (A ↗ h)).rel i x ↔ (Sᴺ ⇘ A).rel i x)
  (h21' : ∀ (x : γ ↝ ⊥ × NearLitter), (∃ i, ((Sᴺ ↗ h) ⇘ (A ↗ h)).rel i x) ↔ (∃ i, (Sᴺ ⇘ A).rel i x)):
  (Sᴺ ↗ h) ⇘ (A ↗ h) = Sᴺ ⇘ A := by
  have h221 : (Sᴺ ↗ h) ⇘ (A ↗ h) = Sᴺ ⇘ A := by
    apply Enumeration.ext
    <;> aesop
  exact h221

theorem scoderiv_deriv_eq {α β γ : TypeIndex} (S : Support β) (A : β ↝ γ) (h : β < α) :
    S ↗ h ⇘ (A ↗ h) = S ⇘ A  := by

  have h11 : ∀ (i : κ) (x : γ ↝ ⊥ × Atom), ((Sᴬ ↗ h) ⇘ (A ↗ h)).rel i x ↔ (Sᴬ ⇘ A).rel i x := by
    exact round1_h11 α β γ S A h
  have h11' : ∀ (x : γ ↝ ⊥ × Atom), (∃ i, ((Sᴬ ↗ h) ⇘ (A ↗ h)).rel i x) ↔ (∃ i, (Sᴬ ⇘ A).rel i x) := by
    exact round1_h11' α β γ S A h h11
  have h12 : (Sᴬ ↗ h) ⇘ (A ↗ h) = Sᴬ ⇘ A := by
    exact round1_h12 α β γ S A h h11 h11'
  have h21 : ∀ (i : κ) (x : γ ↝ ⊥ × NearLitter), ((Sᴺ ↗ h) ⇘ (A ↗ h)).rel i x ↔ (Sᴺ ⇘ A).rel i x := by
    exact round1_h21 α β γ S A h
  have h21' : ∀ (x : γ ↝ ⊥ × NearLitter), (∃ i, ((Sᴺ ↗ h) ⇘ (A ↗ h)).rel i x) ↔ (∃ i, (Sᴺ ⇘ A).rel i x) := by
    exact round1_h21' α β γ S A h h21
  have h22 : (Sᴺ ↗ h) ⇘ (A ↗ h) = Sᴺ ⇘ A := by
    exact round1_h22 α β γ S A h h21 h21'
  have h1 : ((S ↗ h) ⇘ (A ↗ h))ᴬ = (S ⇘ A)ᴬ := by
    simpa using h12
  have h2 : ((S ↗ h) ⇘ (A ↗ h))ᴺ = (S ⇘ A)ᴺ := by
    simpa using h22
  apply Support.ext'
  · simpa using h1
  · simpa using h2
