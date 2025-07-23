-- In foundation/Foundation/Modal/NNFormula.lean

import Foundation.Modal.Formula

namespace LO.Modal

variable {α : Type u}

inductive NNFormula (α : Type u) : Type u where
  | atom   : α → NNFormula α
  | natom  : α → NNFormula α
  | falsum : NNFormula α
  | verum  : NNFormula α
  | or     : NNFormula α → NNFormula α → NNFormula α
  | and    : NNFormula α → NNFormula α → NNFormula α
  | box    : NNFormula α → NNFormula α
  | dia    : NNFormula α → NNFormula α
  deriving DecidableEq

namespace NNFormula

variable {φ ψ χ : NNFormula α}

def neg : NNFormula α → NNFormula α
  | atom a  => natom a
  | natom a => atom a
  | falsum  => verum
  | verum   => falsum
  | or φ ψ  => and (neg φ) (neg ψ)
  | and φ ψ => or (neg φ) (neg ψ)
  | box φ   => dia (neg φ)
  | dia φ   => box (neg φ)

def imp (φ ψ : NNFormula α) : NNFormula α := or (neg φ) ψ

instance : BasicModalLogicalConnective (NNFormula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum
  box := box
  dia := dia

lemma or_eq : or φ ψ = φ ⋎ ψ := rfl

lemma and_eq : and φ ψ = φ ⋏ ψ := rfl

lemma imp_eq : imp φ ψ = φ ➝ ψ := rfl

lemma box_eq : box φ = □φ := rfl

lemma dia_eq : dia φ = ◇φ := rfl

@[simp] lemma imp_eq' : φ ➝ ψ = ∼φ ⋎ ψ := rfl

@[simp] lemma iff_eq : φ ⭤ ψ = (φ ➝ ψ) ⋏ (ψ ➝ φ) := rfl

lemma falsum_eq : (falsum : NNFormula α) = ⊥ := rfl

lemma verum_eq : (verum : NNFormula α) = ⊤ := rfl

@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Wedge.wedge]

@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Vee.vee]

@[simp] lemma imp_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ➝ φ₂ = ψ₁ ➝ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp[Arrow.arrow]

@[simp] lemma neg_inj (φ ψ : Formula α) : ∼φ = ∼ψ ↔ φ = ψ := by simp [NegAbbrev.neg];

lemma neg_eq : neg φ = ∼φ := rfl

@[simp] lemma neg_atom (a : α) : ∼atom a = natom a := by rfl

@[simp] lemma neg_natom (a : α) : ∼natom a = atom a := by rfl

lemma negneg : ∼∼φ = φ := by
  induction φ with
  | and φ ψ ihφ ihψ =>
    simp only [←neg_eq, neg, and.injEq];
    exact ⟨ihφ, ihψ⟩;
  | or φ ψ ihφ ihψ =>
    simp only [←neg_eq, neg, or.injEq];
    exact ⟨ihφ, ihψ⟩;
  | box φ ihφ =>
    simp only [←neg_eq, neg, box.injEq];
    exact ihφ;
  | dia φ ihφ =>
    simp only [←neg_eq, neg, dia.injEq];
    exact ihφ;
  | _ => tauto;

instance : ModalDeMorgan (NNFormula α) where
  verum := by tauto;
  falsum := by tauto;
  and := by tauto;
  or := by tauto;
  box := by tauto;
  dia := by tauto;
  neg := λ _ => negneg
  imply := by tauto;

section toString

variable [ToString α]
def toStr : NNFormula α → String
  | atom a  => s!"+{a}"
  | natom a => s!"-{a}"
  | falsum  => "⊥"
  | verum   => "⊤"
  | or φ ψ  => s!"({φ.toStr} ∨ {ψ.toStr})"
  | and φ ψ => s!"({φ.toStr} ∧ {ψ.toStr})"
  | box φ   => s!"□{φ.toStr}"
  | dia φ   => s!"◇{φ.toStr}"
instance : Repr (NNFormula α) := ⟨fun t _ => toStr t⟩

end toString

section toFormula

def toFormula : NNFormula α → Formula α
  | atom a  => Formula.atom a
  | natom a => ∼Formula.atom a
  | ⊥       => ⊥
  | ⊤       => ⊤
  | φ ⋎ ψ   => φ.toFormula ⋎ ψ.toFormula
  | φ ⋏ ψ   => φ.toFormula ⋏ ψ.toFormula
  | □φ      => □(φ.toFormula)
  | ◇φ      => ◇(φ.toFormula)
instance : Coe (NNFormula α) (Formula α) := ⟨toFormula⟩

@[simp] lemma toFormula_atom (a : α) : toFormula  (.atom a) = Formula.atom a := rfl

/- Start of proof attempt -/
lemma round1_toFormula_natom (a : α) : NNFormula.toFormula (.natom a) = ∼Formula.atom a := by
  simp [NNFormula.toFormula]

theorem toFormula_natom (a : α) : toFormula (.natom a) = ∼Formula.atom a  := by

  exact round1_toFormula_natom a
