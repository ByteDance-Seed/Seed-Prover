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

@[simp]
theorem externalRel_smul (r : TSet α) (ρ : AllPerm α) :
    ExternalRel hβ hγ hδ (ρ • r) =
      InvImage (ExternalRel hβ hγ hδ r) ((ρ ↘ hβ ↘ hγ ↘ hδ)⁻¹ • ·) := by
  ext a b
  simp only [ExternalRel, mem_smul_iff', allPerm_inv_sderiv', smul_op, InvImage]

omit [Params] in

/- Start of proof attempt -/
lemma round1_h1 (X : Type _) (r : Rel X X) (f : X → X) (hr : IsWellOrder X r) (hf : Function.Bijective f) 
    (hf' : ∀ x y, r x y ↔ r (f x) (f y)) : ∀ x, ¬ r (f x) x := by
  intro x
  induction x using WellFounded.induction hr.wf with
  | h x ih =>
    intro h
    have h2 : r (f (f x)) (f x) := by
      have h21 : r (f x) x := h
      have h22 : r (f x) x ↔ r (f (f x)) (f x) := by
        specialize hf' (f x) x
        exact hf'
      exact (h22.mp h21)
    have h3 : r (f (f x)) x := by
      have h31 : r (f (f x)) (f x) := h2
      have h32 : r (f x) x := h
      exact Trans.trans h31 h32
    have h4 : ¬ r (f (f (f x))) (f (f x)) := by
      specialize ih (f (f x)) h3
      exact ih
    have h5 : r (f (f x)) (f x) := h2
    have h6 : r (f (f x)) (f x) ↔ r (f (f (f x))) (f (f x)) := by
      specialize hf' (f (f x)) (f x)
      exact hf'
    have h7 : r (f (f (f x))) (f (f x)) := (h6.mp h5)
    contradiction

lemma round1_h4 (X : Type _) (r : Rel X X) (f : X → X) (hr : IsWellOrder X r) (hf : Function.Bijective f) 
    (hf' : ∀ x y, r x y ↔ r (f x) (f y)) : ∀ x, ¬ r x (f x) := by
  intro x
  induction x using WellFounded.induction hr.wf with
  | h x ih =>
    intro h
    have hfx : Function.Surjective f := hf.surjective
    obtain ⟨z, hz : f z = x⟩ := hfx x
    have h5 : r (f z) (f (f z)) := by
      have h51 : x = f z := by rw [hz]
      have h52 : r x (f x) := h
      have h53 : r (f z) (f (f z)) := by
        have h54 : x = f z := by rw [hz]
        have h55 : r x (f x) := h
        have h56 : r (f z) (f (f z)) ↔ r x (f x) := by
          have h57 : x = f z := by rw [hz]
          simp [h57]
          <;> aesop
        tauto
      exact h53
    have h6 : r z (f z) := by
      have h61 : r z (f z) ↔ r (f z) (f (f z)) := by
        specialize hf' z (f z)
        exact hf'
      have h62 : r (f z) (f (f z)) := h5
      exact (h61.mpr h62)
    have h7 : r z x := by
      have h71 : f z = x := hz
      have h72 : r z (f z) := h6
      have h73 : r z x := by
        rw [h71] at h72
        exact h72
      exact h73
    have h8 : ¬ r z (f z) := by
      specialize ih z h7
      exact ih
    contradiction

/-- Well-orders are rigid. -/
theorem apply_eq_of_isWellOrder {X : Type _} {r : Rel X X} {f : X → X}
    (hr : IsWellOrder X r) (hf : Function.Bijective f) (hf' : ∀ x y, r x y ↔ r (f x) (f y)) :
    ∀ x, f x = x  := by

  have h1 : ∀ x, ¬ r (f x) x := by
    exact round1_h1 X r f hr hf hf'
  have h4 : ∀ x, ¬ r x (f x) := by
    exact round1_h4 X r f hr hf hf'
  intro x
  have h11 : r x (f x) ∨ x = f x ∨ r (f x) x := by
    have h111 : r x (f x) ∨ x = f x ∨ r (f x) x := hr.trichotomous x (f x)
    tauto
  rcases h11 with (h111 | h112 | h113)
  · -- Case 1: r x (f x)
    exfalso
    exact h4 x h111
  · -- Case 2: x = f x
    have h12 : f x = x := by
      exact h112.symm
    exact h12
  · -- Case 3: r (f x) x
    exfalso
    exact h1 x h113
