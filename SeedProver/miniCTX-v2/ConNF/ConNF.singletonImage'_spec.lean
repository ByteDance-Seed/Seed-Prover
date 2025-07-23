-- In ConNF/ConNF/Model/Result.lean

import ConNF.Model.Hailperin

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

theorem ext (x y : TSet α) :
    (∀ z : TSet β, z ∈' x ↔ z ∈' y) → x = y :=
  tSet_ext' hβ x y

def inter (x y : TSet α) : TSet α :=
  (TSet.exists_inter hβ x y).choose

notation:69 x:69 " ⊓[" h "] " y:69 => _root_.ConNF.inter h x y
notation:69 x:69 " ⊓' " y:69 => x ⊓[by assumption] y

@[simp]
theorem mem_inter_iff (x y : TSet α) :
    ∀ z : TSet β, z ∈' x ⊓' y ↔ z ∈' x ∧ z ∈' y :=
  (TSet.exists_inter hβ x y).choose_spec

def compl (x : TSet α) : TSet α :=
  (TSet.exists_compl hβ x).choose

notation:1024 x:1024 " ᶜ[" h "]" => _root_.ConNF.compl h x
notation:1024 x:1024 " ᶜ'" => xᶜ[by assumption]

@[simp]
theorem mem_compl_iff (x : TSet α) :
    ∀ z : TSet β, z ∈' xᶜ' ↔ ¬z ∈' x :=
  (TSet.exists_compl hβ x).choose_spec

notation:1024 "{" x "}[" h "]" => _root_.ConNF.singleton h x
notation:1024 "{" x "}'" => {x}[by assumption]

@[simp]
theorem mem_singleton_iff (x y : TSet β) :
    y ∈' {x}' ↔ y = x :=
  typedMem_singleton_iff' hβ x y

notation:1024 "{" x ", " y "}[" h "]" => _root_.ConNF.TSet.up h x y
notation:1024 "{" x ", " y "}'" => {x, y}[by assumption]

@[simp]
theorem mem_up_iff (x y z : TSet β) :
    z ∈' {x, y}' ↔ z = x ∨ z = y :=
  TSet.mem_up_iff hβ x y z

notation:1024 "⟨" x ", " y "⟩[" h ", " h' "]" => _root_.ConNF.TSet.op h h' x y
notation:1024 "⟨" x ", " y "⟩'" => ⟨x, y⟩[by assumption, by assumption]

theorem op_def (x y : TSet γ) :
    (⟨x, y⟩' : TSet α) = { {x}', {x, y}' }' :=
  rfl

def singletonImage' (x : TSet β) : TSet α :=
  (TSet.exists_singletonImage hβ hγ hδ hε x).choose

/- Start of proof attempt -/
lemma round1_singletonImage'_spec (x : TSet β) :
    ∀ z w,
    ⟨ {z}', {w}' ⟩' ∈' singletonImage' hβ hγ hδ hε x ↔ ⟨z, w⟩' ∈' x := by
  intro z w
  exact (TSet.exists_singletonImage hβ hγ hδ hε x).choose_spec z w

theorem singletonImage'_spec (x : TSet β) :
    ∀ z w,
    ⟨ {z}', {w}' ⟩' ∈' singletonImage' hβ hγ hδ hε x ↔ ⟨z, w⟩' ∈' x  := by

  exact round1_singletonImage'_spec hβ hγ hδ hε x
