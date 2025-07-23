-- In ConNF/ConNF/External/Basic.lean

import ConNF.Model.Result

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

def union (x y : TSet α) : TSet α :=
  (xᶜ' ⊓' yᶜ')ᶜ'

notation:68 x:68 " ⊔[" h "] " y:68 => _root_.ConNF.union h x y
notation:68 x:68 " ⊔' " y:68 => x ⊔[by assumption] y

@[simp]
theorem mem_union_iff (x y : TSet α) :
    ∀ z : TSet β, z ∈' x ⊔' y ↔ z ∈' x ∨ z ∈' y := by
  rw [union]
  intro z
  rw [mem_compl_iff, mem_inter_iff, mem_compl_iff, mem_compl_iff, or_iff_not_and_not]

def higherIndex (α : Λ) : Λ :=
  (exists_gt α).choose

theorem lt_higherIndex {α : Λ} :
    (α : TypeIndex) < higherIndex α :=
  WithBot.coe_lt_coe.mpr (exists_gt α).choose_spec

theorem tSet_nonempty (h : ∃ β : Λ, (β : TypeIndex) < α) : Nonempty (TSet α) := by
  obtain ⟨α', hα⟩ := h
  constructor
  apply typeLower lt_higherIndex lt_higherIndex lt_higherIndex hα
  apply cardinalOne lt_higherIndex lt_higherIndex

def empty : TSet α :=
  (tSet_nonempty ⟨β, hβ⟩).some ⊓' (tSet_nonempty ⟨β, hβ⟩).someᶜ'

@[simp]
theorem mem_empty_iff :
    ∀ x : TSet β, ¬x ∈' empty hβ := by
  intro x
  rw [empty, mem_inter_iff, mem_compl_iff]
  exact and_not_self

def univ : TSet α :=
  (empty hβ)ᶜ'

@[simp]
theorem mem_univ_iff :
    ∀ x : TSet β, x ∈' univ hβ := by
  intro x
  simp only [univ, mem_compl_iff, mem_empty_iff, not_false_eq_true]

/-- The set of all ordered pairs. -/
def orderedPairs : TSet α :=
  vCross hβ hγ hδ (univ hδ)

@[simp]
theorem mem_orderedPairs_iff (x : TSet β) :
    x ∈' orderedPairs hβ hγ hδ ↔ ∃ a b, x = ⟨a, b⟩' := by
  simp only [orderedPairs, vCross_spec, mem_univ_iff, and_true]

def converse (x : TSet α) : TSet α :=
  converse' hβ hγ hδ x ⊓' orderedPairs hβ hγ hδ

@[simp]
theorem op_mem_converse_iff (x : TSet α) :
    ∀ a b, ⟨a, b⟩' ∈' converse hβ hγ hδ x ↔ ⟨b, a⟩' ∈' x := by
  intro a b
  simp only [converse, mem_inter_iff, converse'_spec, mem_orderedPairs_iff, op_inj, exists_and_left,
    exists_eq', and_true]

def cross (x y : TSet γ) : TSet α :=
  converse hβ hγ hδ (vCross hβ hγ hδ x) ⊓' vCross hβ hγ hδ y

@[simp]
theorem mem_cross_iff (x y : TSet γ) :
    ∀ a, a ∈' cross hβ hγ hδ x y ↔ ∃ b c, a = ⟨b, c⟩' ∧ b ∈' x ∧ c ∈' y := by
  intro a
  rw [cross, mem_inter_iff, vCross_spec]
  constructor
  · rintro ⟨h₁, b, c, rfl, h₂⟩
    simp only [op_mem_converse_iff, vCross_spec, op_inj] at h₁
    obtain ⟨b', c', ⟨rfl, rfl⟩, h₁⟩ := h₁
    exact ⟨b, c, rfl, h₁, h₂⟩
  · rintro ⟨b, c, rfl, h₁, h₂⟩
    simp only [op_mem_converse_iff, vCross_spec, op_inj]
    exact ⟨⟨c, b, ⟨rfl, rfl⟩, h₁⟩, ⟨b, c, ⟨rfl, rfl⟩, h₂⟩⟩

def singletonImage (x : TSet β) : TSet α :=
  singletonImage' hβ hγ hδ hε x ⊓' (cross hβ hγ hδ (cardinalOne hδ hε) (cardinalOne hδ hε))

@[simp]
theorem singletonImage_spec (x : TSet β) :
    ∀ z w,
    ⟨ {z}', {w}' ⟩' ∈' singletonImage hβ hγ hδ hε x ↔ ⟨z, w⟩' ∈' x := by
  intro z w
  rw [singletonImage, mem_inter_iff, singletonImage'_spec, and_iff_left_iff_imp]
  intro hzw
  rw [mem_cross_iff]
  refine ⟨{z}', {w}', rfl, ?_⟩
  simp only [mem_cardinalOne_iff, singleton_inj, exists_eq', and_self]

theorem exists_of_mem_singletonImage {x : TSet β} {z w : TSet δ}
    (h : ⟨z, w⟩' ∈' singletonImage hβ hγ hδ hε x) :
    ∃ a b, z = {a}' ∧ w = {b}' := by
  simp only [singletonImage, mem_inter_iff, mem_cross_iff, op_inj, mem_cardinalOne_iff] at h
  obtain ⟨-, _, _, ⟨rfl, rfl⟩, ⟨a, rfl⟩, ⟨b, rfl⟩⟩ := h
  exact ⟨a, b, rfl, rfl⟩

/-- Turn a model element encoding a relation into an actual relation. -/
def ExternalRel (r : TSet α) : Rel (TSet δ) (TSet δ) :=
  λ x y ↦ ⟨x, y⟩' ∈' r

@[simp]
theorem externalRel_converse (r : TSet α) :
    ExternalRel hβ hγ hδ (converse hβ hγ hδ r) = (ExternalRel hβ hγ hδ r).inv := by
  ext
  simp only [ExternalRel, op_mem_converse_iff, Rel.inv_apply]

/-- The codomain of a relation. -/
def codom (r : TSet α) : TSet γ :=
  (typeLower lt_higherIndex hβ hγ hδ (singletonImage lt_higherIndex hβ hγ hδ r)ᶜ[lt_higherIndex])ᶜ'

@[simp]
theorem mem_codom_iff (r : TSet α) (x : TSet δ) :
    x ∈' codom hβ hγ hδ r ↔ x ∈ (ExternalRel hβ hγ hδ r).codom := by
  simp only [codom, mem_compl_iff, mem_typeLower_iff, not_forall, not_not]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨a, b, rfl, hb⟩ := exists_of_mem_singletonImage lt_higherIndex hβ hγ hδ hy
    rw [singleton_inj] at hb
    subst hb
    rw [singletonImage_spec] at hy
    exact ⟨a, hy⟩
  · rintro ⟨a, ha⟩
    use {a}'
    rw [singletonImage_spec]
    exact ha

/-- The domain of a relation. -/
def dom (r : TSet α) : TSet γ :=
  codom hβ hγ hδ (converse hβ hγ hδ r)

@[simp]
theorem mem_dom_iff (r : TSet α) (x : TSet δ) :
    x ∈' dom hβ hγ hδ r ↔ x ∈ (ExternalRel hβ hγ hδ r).dom := by
  rw [dom, mem_codom_iff, externalRel_converse, Rel.inv_codom]

/-- The field of a relation. -/
def field (r : TSet α) : TSet γ :=
  dom hβ hγ hδ r ⊔' codom hβ hγ hδ r

/- Start of proof attempt -/
lemma round1_mem_field_iff (r : TSet α) (x : TSet δ) :
    x ∈' field hβ hγ hδ r ↔ x ∈ (ExternalRel hβ hγ hδ r).field := by
  simp only [field, mem_union_iff, mem_dom_iff, mem_codom_iff, Rel.field, Set.mem_union]
  <;> aesop

theorem mem_field_iff (r : TSet α) (x : TSet δ) :
    x ∈' field hβ hγ hδ r ↔ x ∈ (ExternalRel hβ hγ hδ r).field  := by

  exact round1_mem_field_iff hβ hγ hδ r x
