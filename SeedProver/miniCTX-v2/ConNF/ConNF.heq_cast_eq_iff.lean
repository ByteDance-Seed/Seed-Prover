-- In ConNF/ConNF/Model/Externalise.lean

import ConNF.Model.RunInduction

/-!
# Externalisation

In this file, we convert many of our *internal* results (i.e. inside the induction) to *external*
ones (i.e. defined using the global `TSet`/`AllPerm` definitions).

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal WithBot

namespace ConNF

variable [Params.{u}]

instance globalModelData : {α : TypeIndex} → ModelData α
  | (α : Λ) => (motive α).data
  | ⊥ => botModelData

instance globalPosition : {α : TypeIndex} → Position (Tangle α)
  | (α : Λ) => (motive α).pos
  | ⊥ => botPosition

instance globalTypedNearLitters {α : Λ} : TypedNearLitters α :=
  (motive α).typed

instance globalLtData [Level] : LtData where

instance globalLeData [Level] : LeData where

omit [Params] in
theorem heq_funext {α : Sort _} {β γ : α → Sort _} {f : (x : α) → β x} {g : (x : α) → γ x}
    (h : ∀ x, HEq (f x) (g x)) : HEq f g := by
  cases funext λ x ↦ type_eq_of_heq (h x)
  simp only [heq_eq_eq] at h ⊢
  exact funext h

theorem globalLtData_eq [Level] :
    globalLtData = ltData (λ β _ ↦ motive β) := by
  apply LtData.ext
  · ext β hβ
    induction β using recBotCoe
    case bot => rfl
    case coe β => rfl
  · apply heq_funext
    intro β
    induction β using recBotCoe
    case bot => rfl
    case coe β => rfl
  · rfl

theorem globalLeData_eq [Level] :
    globalLeData = leData (λ β _ ↦ motive β) := by
  apply LeData.ext
  · ext β hβ
    induction β using recBotCoe
    case bot => rfl
    case coe β =>
      by_cases h : (β : TypeIndex) = α
      · cases coe_injective h
        rw [leData_data_eq]
        unfold globalLeData globalModelData
        dsimp only
        rw [motive_eq]
        rfl
      · rw [leData_data_lt _ (hβ.elim.lt_of_ne h)]
        rfl
  · apply heq_funext
    intro β
    apply heq_funext
    intro hβ
    induction β using recBotCoe
    case bot => rfl
    case coe β =>
      rw [leData]
      simp only [coe_inj, id_eq, eq_mpr_eq_cast, recBotCoe_bot, recBotCoe_coe, LtLevel.elim.ne]
      exact HEq.symm (cast_heq _ _)

instance globalPreCoherentData [Level] : PreCoherentData where
  allPermSderiv h := cast (by rw [globalLeData_eq])
    ((preCoherentData (λ β _ ↦ motive β) (λ β _ ↦ hypothesis β)).allPermSderiv h)
  singleton h := cast (by rw [globalLeData_eq])
    ((preCoherentData (λ β _ ↦ motive β) (λ β _ ↦ hypothesis β)).singleton h)

omit [Params] in

/- Start of proof attempt -/
lemma round1_heq_cast_eq_iff {α β γ : Type _} {x : α} {y : β} {h : α = γ} :
    HEq (cast h x) y ↔ HEq x y := by
  subst h
  <;> simp

theorem heq_cast_eq_iff {α β γ : Type _} {x : α} {y : β} {h : α = γ} :
    HEq (cast h x) y ↔ HEq x y  := by

  exact round1_heq_cast_eq_iff
