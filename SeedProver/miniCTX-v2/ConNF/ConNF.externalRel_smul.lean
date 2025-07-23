-- In ConNF/ConNF/External/WellOrder.lean

import ConNF.External.Basic

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal ConNF.TSet

namespace ConNF

variable [Params.{u}] {α β γ δ ε ζ : Λ} (hβ : (β : TypeIndex) < α) (hγ : (γ : TypeIndex) < β)
  (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < δ) (hζ : (ζ : TypeIndex) < ε)

/-- A set in our model that is a well-order. Internal well-orders are exactly external well-orders,
so we externalise the definition for convenience. -/
def InternalWellOrder (r : TSet α) : Prop :=
  IsWellOrder (ExternalRel hβ hγ hδ r).field
    (InvImage (ExternalRel hβ hγ hδ r) Subtype.val)

def InternallyWellOrdered (x : TSet γ) : Prop :=
  {y : TSet δ | y ∈' x}.Subsingleton ∨ (∃ r, InternalWellOrder hβ hγ hδ r ∧ x = field hβ hγ hδ r)

/- Start of proof attempt -/
lemma round1_externalRel_smul (r : TSet α) (ρ : AllPerm α) :
    ExternalRel hβ hγ hδ (ρ • r) =
      InvImage (ExternalRel hβ hγ hδ r) ((ρ ↘ hβ ↘ hγ ↘ hδ)⁻¹ • ·) := by
  ext x y
  simp [ExternalRel, Set.mem_setOf_eq, Subtype.ext_iff]
  <;>
  aesop

theorem externalRel_smul (r : TSet α) (ρ : AllPerm α) :
    ExternalRel hβ hγ hδ (ρ • r) =
      InvImage (ExternalRel hβ hγ hδ r) ((ρ ↘ hβ ↘ hγ ↘ hδ)⁻¹ • ·)  := by

  exact round1_externalRel_smul hβ hγ hδ r ρ
