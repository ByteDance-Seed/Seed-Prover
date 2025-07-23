-- In ConNF/ConNF/Levels/Path.lean

import ConNF.Base.TypeIndex

/-!
# Paths of type indices

In this file, we define the notion of a *path*, and the derivative and coderivative operations.

## Main declarations

* `ConNF.Path`: A path of type indices.
* `ConNF.Path.recSderiv`, `ConNF.Path.recSderivLe`, `ConNF.Path.recSderivGlobal`:
    Downwards induction principles for paths.
* `ConNF.Path.recScoderiv`: An upwards induction principle for paths.
-/

universe u

open Cardinal WithBot

namespace ConNF

variable [Params.{u}] {α β γ δ : TypeIndex}

/-- A path of type indices starting at `α` and ending at `β` is a finite sequence of type indices
`α > ... > β`. -/
inductive Path (α : TypeIndex) : TypeIndex → Type u
  | nil : Path α α
  | cons {β γ : TypeIndex} : Path α β → γ < β → Path α γ

@[inherit_doc] infix:70 " ↝ "  => Path

def Path.single {α β : TypeIndex} (h : β < α) : α ↝ β :=
  .cons .nil h

/-- Typeclass for the `↘` notation. -/
class SingleDerivative (X : Type _) (Y : outParam <| Type _)
    (β : outParam TypeIndex) (γ : TypeIndex) where
  sderiv : X → γ < β → Y

/-- Typeclass for the `⇘` notation. -/
class Derivative (X : Type _) (Y : outParam <| Type _)
    (β : outParam TypeIndex) (γ : TypeIndex) extends SingleDerivative X Y β γ where
  deriv : X → β ↝ γ → Y
  sderiv x h := deriv x (.single h)
  deriv_single : ∀ x : X, ∀ h : γ < β, deriv x (.single h) = sderiv x h := by intros; rfl

/-- Typeclass for the `↘.` notation. -/
class BotSingleDerivative (X : Type _) (Y : outParam <| Type _) where
  botSderiv : X → Y

/-- Typeclass for the `⇘.` notation. -/
class BotDerivative (X : Type _) (Y : outParam <| Type _) (β : outParam TypeIndex)
    extends BotSingleDerivative X Y where
  botDeriv : X → β ↝ ⊥ → Y
  /-- We often need to do case analysis on `β` to show that it's a proper type index here.
  This case check doesn't need to be done in most actual use cases of the notation. -/
  botDeriv_single : ∀ x : X, ∀ h : ⊥ < β, botDeriv x (.single h) = botSderiv x

/-- Typeclass for the `↗` notation. -/
class SingleCoderivative (X : Type _) (Y : outParam <| Type _)
    (β : TypeIndex) (γ : outParam TypeIndex) where
  scoderiv : X → γ < β → Y

/-- Typeclass for the `⇗` notation. -/
class Coderivative (X : Type _) (Y : outParam <| Type _)
    (β : TypeIndex) (γ : outParam TypeIndex) extends SingleCoderivative X Y β γ where
  coderiv : X → β ↝ γ → Y
  scoderiv x h := coderiv x (.single h)
  coderiv_single : ∀ x : X, ∀ h : γ < β, coderiv x (.single h) = scoderiv x h := by intros; rfl

infixl:75 " ↘ " => SingleDerivative.sderiv
infixl:75 " ⇘ " => Derivative.deriv
postfix:75 " ↘." => BotSingleDerivative.botSderiv
infixl:75 " ⇘. " => BotDerivative.botDeriv
infixl:75 " ↗ " => SingleCoderivative.scoderiv
infixl:75 " ⇗ " => Coderivative.coderiv

@[simp]
theorem deriv_single {X Y : Type _} [Derivative X Y β γ] (x : X) (h : γ < β) :
    x ⇘ .single h = x ↘ h :=
  Derivative.deriv_single x h

@[simp]
theorem coderiv_single {X Y : Type _} [Coderivative X Y β γ] (x : X) (h : γ < β) :
    x ⇗ .single h = x ↗ h :=
  Coderivative.coderiv_single x h

@[simp]
theorem botDeriv_single {X Y : Type _} [BotDerivative X Y β] (x : X) (h : ⊥ < β) :
    x ⇘. .single h = x ↘. :=
  BotDerivative.botDeriv_single x h

/-!
## Downwards recursion along paths
-/

instance : SingleDerivative (α ↝ β) (α ↝ γ) β γ where
  sderiv := .cons

/-- The downwards recursion principle for paths. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def Path.recSderiv {motive : ∀ β, α ↝ β → Sort _}
    (nil : motive α .nil)
    (sderiv : ∀ β γ (A : α ↝ β) (h : γ < β), motive β A → motive γ (A ↘ h)) :
    {β : TypeIndex} → (A : α ↝ β) → motive β A
  | _, .nil => nil
  | _, .cons A h => sderiv _ _ A h (recSderiv nil sderiv A)

@[simp]
theorem Path.recSderiv_nil {motive : ∀ β, α ↝ β → Sort _}
    (nil : motive α .nil)
    (sderiv : ∀ β γ (A : α ↝ β) (h : γ < β), motive β A → motive γ (A ↘ h)) :
    recSderiv (motive := motive) nil sderiv .nil = nil :=
  rfl

@[simp]
theorem Path.recSderiv_sderiv {motive : ∀ β, α ↝ β → Sort _}
    (nil : motive α .nil)
    (sderiv : ∀ β γ (A : α ↝ β) (h : γ < β), motive β A → motive γ (A ↘ h))
    {β γ : TypeIndex} (A : α ↝ β) (h : γ < β) :
    recSderiv (motive := motive) nil sderiv (A ↘ h) = sderiv β γ A h (recSderiv nil sderiv A) :=
  rfl

theorem Path.le (A : α ↝ β) : β ≤ α := by
  induction A with
  | nil => exact le_rfl
  | sderiv β γ _A h h' => exact h.le.trans h'

/-- The downwards recursion principle for paths, specialised to the case where the motive at `β`
only depends on the fact that `β ≤ α`. -/
def Path.recSderivLe {motive : ∀ β ≤ α, Sort _}
    (nil : motive α le_rfl)
    (sderiv : ∀ β γ, ∀ (A : α ↝ β) (h : γ < β), motive β A.le → motive γ (h.le.trans A.le)) :
    {β : TypeIndex} → (A : α ↝ β) → motive β A.le :=
  Path.recSderiv (motive := λ β A ↦ motive β A.le) nil sderiv

@[simp]
theorem Path.recSderivLe_nil {motive : ∀ β ≤ α, Sort _}
    (nil : motive α le_rfl)
    (sderiv : ∀ β γ (A : α ↝ β) (h : γ < β), motive β A.le → motive γ (h.le.trans A.le)) :
    recSderivLe (motive := motive) nil sderiv .nil = nil :=
  rfl

@[simp]
theorem Path.recSderivLe_sderiv {motive : ∀ β ≤ α, Sort _}
    (nil : motive α le_rfl)
    (sderiv : ∀ β γ (A : α ↝ β) (h : γ < β), motive β A.le → motive γ (h.le.trans A.le))
    {β γ : TypeIndex} (A : α ↝ β) (h : γ < β) :
    recSderivLe (motive := motive) nil sderiv (A ↘ h) = sderiv β γ A h (recSderiv nil sderiv A) :=
  rfl

/-- The downwards recursion principle for paths, specialised to the case where the motive is not
dependent on the relation of `β` to `α`. -/
@[elab_as_elim]
def Path.recSderivGlobal {motive : TypeIndex → Sort _}
    (nil : motive α)
    (sderiv : ∀ β γ, α ↝ β → γ < β → motive β → motive γ) :
    {β : TypeIndex} → α ↝ β → motive β :=
  Path.recSderiv (motive := λ β _ ↦ motive β) nil sderiv

@[simp]
theorem Path.recSderivGlobal_nil {motive : TypeIndex → Sort _}
    (nil : motive α)
    (sderiv : ∀ β γ, α ↝ β → γ < β → motive β → motive γ) :
    recSderivGlobal (motive := motive) nil sderiv .nil = nil :=
  rfl

@[simp]
theorem Path.recSderivGlobal_sderiv {motive : TypeIndex → Sort _}
    (nil : motive α)
    (sderiv : ∀ β γ, α ↝ β → γ < β → motive β → motive γ)
    {β γ : TypeIndex} (A : α ↝ β) (h : γ < β) :
    recSderivGlobal (motive := motive) nil sderiv (A ↘ h) =
      sderiv β γ A h (recSderiv nil sderiv A) :=
  rfl

/-!
## Derivatives of paths
-/

instance : Derivative (α ↝ β) (α ↝ γ) β γ where
  deriv A := Path.recSderivGlobal A (λ _ _ _ h B ↦ B ↘ h)

instance : BotDerivative (α ↝ β) (α ↝ ⊥) β where
  botDeriv A B := A ⇘ B
  botSderiv A :=
    match β with
      | ⊥ => A
      | (β : Λ) => A ↘ bot_lt_coe β
  botDeriv_single A h := by
    cases β using WithBot.recBotCoe with
    | bot => cases lt_irrefl ⊥ h
    | coe => rfl

instance : Coderivative (β ↝ γ) (α ↝ γ) α β where
  coderiv A B := B ⇘ A

@[simp]
theorem Path.deriv_nil (A : α ↝ β) :
    A ⇘ .nil = A :=
  rfl

@[simp]
theorem Path.deriv_sderiv (A : α ↝ β) (B : β ↝ γ) (h : δ < γ) :
    A ⇘ (B ↘ h) = A ⇘ B ↘ h :=
  rfl

@[simp]
theorem Path.nil_deriv (A : α ↝ β) :
    (.nil : α ↝ α) ⇘ A = A := by
  induction A with
  | nil => rfl
  | sderiv γ δ A h ih => rw [deriv_sderiv, ih]

@[simp]
theorem Path.deriv_sderivBot (A : α ↝ β) (B : β ↝ γ) :
    A ⇘ (B ↘.) = A ⇘ B ↘. := by
  cases γ using WithBot.recBotCoe with
  | bot => rfl
  | coe => rfl

@[simp]
theorem Path.botSderiv_bot_eq (A : α ↝ ⊥) :
    A ↘. = A :=
  rfl

@[simp]
theorem Path.botSderiv_coe_eq {β : Λ} (A : α ↝ β) :
    A ↘ bot_lt_coe β = A ↘. :=
  rfl

@[simp]
theorem Path.deriv_assoc (A : α ↝ β) (B : β ↝ γ) (C : γ ↝ δ) :
    A ⇘ (B ⇘ C) = A ⇘ B ⇘ C := by
  induction C with
  | nil => rfl
  | sderiv ε ζ C h ih => simp only [deriv_sderiv, ih]

@[simp]
theorem Path.deriv_sderiv_assoc (A : α ↝ β) (B : β ↝ γ) (h : δ < γ) :
    A ⇘ (B ↘ h) = A ⇘ B ↘ h :=
  rfl

@[simp]
theorem Path.deriv_scoderiv (A : α ↝ β) (B : γ ↝ δ) (h : γ < β) :
    A ⇘ (B ↗ h) = A ↘ h ⇘ B := by
  induction B with
  | nil => rfl
  | sderiv ε ζ B h' ih =>
    rw [deriv_sderiv, ← ih]
    rfl

@[simp]
theorem Path.botDeriv_scoderiv (A : α ↝ β) (B : γ ↝ ⊥) (h : γ < β) :
    A ⇘. (B ↗ h) = A ↘ h ⇘. B :=
  deriv_scoderiv A B h

theorem Path.coderiv_eq_deriv (A : α ↝ β) (B : β ↝ γ) :
    B ⇗ A = A ⇘ B :=
  rfl

theorem Path.coderiv_deriv (A : β ↝ γ) (h₁ : β < α) (h₂ : δ < γ) :
    A ↗ h₁ ↘ h₂ = A ↘ h₂ ↗ h₁ :=
  rfl

theorem Path.coderiv_deriv' (A : β ↝ γ) (h : β < α) (B : γ ↝ δ) :
    A ↗ h ⇘ B = A ⇘ B ↗ h := by
  induction B with
  | nil => rfl
  | sderiv ε ζ B h' ih =>
    rw [deriv_sderiv, ih]
    rfl

theorem Path.eq_nil (A : β ↝ β) :
    A = .nil := by
  cases A with
  | nil => rfl
  | sderiv γ _ A h => cases A.le.not_lt h

theorem Path.sderiv_index_injective {A : α ↝ β} {B : α ↝ γ} {hδβ : δ < β} {hδγ : δ < γ}
    (h : A ↘ hδβ = B ↘ hδγ) :
    β = γ := by
  cases h
  rfl

theorem Path.sderivBot_index_injective {β γ : Λ} {A : α ↝ β} {B : α ↝ γ}
    (h : A ↘. = B ↘.) :
    β = γ := by
  cases h
  rfl

theorem Path.sderiv_path_injective {A B : α ↝ β} {hγ : γ < β} (h : A ↘ hγ = B ↘ hγ) :
    A = B := by
  cases h
  rfl

theorem Path.sderivBot_path_injective {β : Λ} {A B : α ↝ β} (h : A ↘. = B ↘.) :
    A = B := by
  cases h
  rfl

theorem Path.deriv_left_injective {A B : α ↝ β} {C : β ↝ γ} (h : A ⇘ C = B ⇘ C) :
    A = B := by
  induction C with
  | nil => exact h
  | sderiv δ ε C hε ih =>
    rw [deriv_sderiv_assoc, deriv_sderiv_assoc] at h
    exact ih (Path.sderiv_path_injective h)

theorem Path.deriv_right_injective {A : α ↝ β} {B C : β ↝ γ} (h : A ⇘ B = A ⇘ C) :
    B = C := by
  induction C with
  | nil => exact B.eq_nil
  | sderiv δ ε C hε ih =>
    cases B with
    | nil => cases C.le.not_lt hε
    | sderiv ζ η B hε' =>
      cases Path.sderiv_index_injective h
      rw [deriv_sderiv_assoc, deriv_sderiv_assoc] at h
      rw [ih (Path.sderiv_path_injective h)]

@[simp]
theorem Path.sderiv_left_inj {A B : α ↝ β} {h : γ < β} :
    A ↘ h = B ↘ h ↔ A = B :=
  ⟨Path.sderiv_path_injective, λ h ↦ h ▸ rfl⟩

@[simp]
theorem Path.deriv_left_inj {A B : α ↝ β} {C : β ↝ γ} :
    A ⇘ C = B ⇘ C ↔ A = B :=
  ⟨deriv_left_injective, λ h ↦ h ▸ rfl⟩

@[simp]
theorem Path.deriv_right_inj {A : α ↝ β} {B C : β ↝ γ} :
    A ⇘ B = A ⇘ C ↔ B = C :=
  ⟨deriv_right_injective, λ h ↦ h ▸ rfl⟩

/- Start of proof attempt -/
lemma round1_scoderiv_left_inj {A B : β ↝ γ} {h : β < α} :
    A ↗ h = B ↗ h ↔ A = B := by
  constructor
  · intro h1
    have h2 : (.single h : α ↝ β) ⇘ A = (.single h : α ↝ β) ⇘ B := h1
    exact Path.deriv_right_injective h2
  · intro h4
    rw [h4]

theorem Path.scoderiv_left_inj {A B : β ↝ γ} {h : β < α} :
    A ↗ h = B ↗ h ↔ A = B  := by

  exact round1_scoderiv_left_inj
