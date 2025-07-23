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

@[simp]
theorem mem_field_iff (r : TSet α) (x : TSet δ) :
    x ∈' field hβ hγ hδ r ↔ x ∈ (ExternalRel hβ hγ hδ r).field := by
  rw [field, mem_union_iff, mem_dom_iff, mem_codom_iff, Rel.field, Set.mem_union]

def subset : TSet α :=
  subset' hβ hγ hδ hε ⊓' orderedPairs hβ hγ hδ

@[simp]
theorem subset_spec :
    ∀ a b, ⟨a, b⟩' ∈' subset hβ hγ hδ hε ↔ a ⊆[TSet ε] b := by
  intro a b
  simp only [subset, mem_inter_iff, subset'_spec, mem_orderedPairs_iff, op_inj, exists_and_left,
    exists_eq', and_true]

def membership : TSet α :=
  subset hβ hγ hδ hε ⊓' cross hβ hγ hδ (cardinalOne hδ hε) (univ hδ)

@[simp]
theorem membership_spec :
    ∀ a b, ⟨{a}', b⟩' ∈' membership hβ hγ hδ hε ↔ a ∈' b := by
  intro a b
  rw [membership, mem_inter_iff, subset_spec]
  simp only [mem_cross_iff, op_inj, mem_cardinalOne_iff, mem_univ_iff, and_true, exists_and_right,
    exists_and_left, exists_eq', exists_eq_left', singleton_inj]
  constructor
  · intro h
    exact h a ((typedMem_singleton_iff' hε a a).mpr rfl)
  · intro h c hc
    simp only [typedMem_singleton_iff'] at hc
    cases hc
    exact h

def powerset (x : TSet β) : TSet α :=
  dom lt_higherIndex lt_higherIndex hβ
    (subset lt_higherIndex lt_higherIndex hβ hγ ⊓[lt_higherIndex]
      vCross lt_higherIndex lt_higherIndex hβ {x}')

@[simp]
theorem mem_powerset_iff (x y : TSet β) :
    x ∈' powerset hβ hγ y ↔ x ⊆[TSet γ] y := by
  rw [powerset, mem_dom_iff]
  constructor
  · rintro ⟨z, h⟩
    simp only [ExternalRel, mem_inter_iff, subset_spec, vCross_spec, op_inj,
      typedMem_singleton_iff', exists_eq_right, exists_and_right, exists_eq', true_and] at h
    cases h.2
    exact h.1
  · intro h
    refine ⟨y, ?_⟩
    simp only [ExternalRel, mem_inter_iff, subset_spec, h, vCross_spec, op_inj,
      typedMem_singleton_iff', exists_eq_right, and_true, exists_eq', and_self]

/-- The set `ι²''x = {{{a}} | a ∈ x}`. -/
def doubleSingleton (x : TSet γ) : TSet α :=
  cross hβ hγ hδ x x ⊓' cardinalOne hβ hγ

/- Start of proof attempt -/
lemma round1_mem_doubleSingleton_iff (x : TSet γ) :
    ∀ y : TSet β, y ∈' doubleSingleton hβ hγ hδ x ↔
    ∃ z : TSet δ, z ∈' x ∧ y = { {z}' }' := by
  intro y
  constructor
  · -- The forward direction is the same as before
    intro h
    have h1 : y ∈' cross hβ hγ hδ x x := by
      have h11 : y ∈' doubleSingleton hβ hγ hδ x := h
      have h12 : y ∈' (cross hβ hγ hδ x x ⊓' cardinalOne hβ hγ) := h11
      have h13 : y ∈' cross hβ hγ hδ x x ∧ y ∈' cardinalOne hβ hγ := (ConNF.mem_inter_iff hβ (cross hβ hγ hδ x x) (cardinalOne hβ hγ) y).mp h12
      exact h13.1
    have h2 : y ∈' cardinalOne hβ hγ := by
      have h11 : y ∈' doubleSingleton hβ hγ hδ x := h
      have h12 : y ∈' (cross hβ hγ hδ x x ⊓' cardinalOne hβ hγ) := h11
      have h13 : y ∈' cross hβ hγ hδ x x ∧ y ∈' cardinalOne hβ hγ := (ConNF.mem_inter_iff hβ (cross hβ hγ hδ x x) (cardinalOne hβ hγ) y).mp h12
      exact h13.2
    have h14 : y ∈' vCross hβ hγ hδ x := by
      have h15 : y ∈' cross hβ hγ hδ x x := h1
      have h16 : y ∈' converse hβ hγ hδ (vCross hβ hγ hδ x) ⊓' vCross hβ hγ hδ x := h15
      have h17 : y ∈' vCross hβ hγ hδ x := ((ConNF.mem_inter_iff hβ (converse hβ hγ hδ (vCross hβ hγ hδ x)) (vCross hβ hγ hδ x) y).mp h16).2
      exact h17
    have h18 : ∃ (b c : TSet δ), y = ⟨b, c⟩[hγ, hδ] ∧ c ∈' x := by
      have h19 : y ∈' vCross hβ hγ hδ x := h14
      exact (ConNF.vCross_spec hβ hγ hδ x y).mp h19
    obtain ⟨b, c, h20, h21⟩ := h18
    have h22 : y = ⟨b, c⟩[hγ, hδ] := h20
    have h23 : c ∈' x := h21
    have h24 : y ∈' cardinalOne hβ hγ := h2
    have h25 : ∃ (b' : TSet γ), y = {b'}[hγ] := (ConNF.mem_cardinalOne_iff hβ hγ y).mp h24
    obtain ⟨b', h26⟩ := h25
    have h27 : ⟨b, c⟩[hγ, hδ] = {b'}[hγ] := by
      rw [h22] at h26
      exact h26
    have h28 : {b}[hδ] = b' ∧ {c}[hδ] = b' := by
      have h29 : ⟨b, c⟩[hγ, hδ] = {b'}[hγ] := h27
      exact (ConNF.TSet.op_eq_singleton_iff hγ hδ b c b').mp h29
    have h29 : {b}[hδ] = b' := h28.1
    have h30 : {c}[hδ] = b' := h28.2
    have h31 : {b}[hδ] = {c}[hδ] := by
      rw [h29, h30]
    have h32 : b = c := by
      have h33 : {b}[hδ] = {c}[hδ] := h31
      exact (ConNF.singleton_inj).mp h33
    have h34 : b ∈' x := by
      have h35 : c ∈' x := h23
      have h36 : b = c := h32
      rw [h36]
      exact h35
    refine ⟨b, h34, ?_⟩
    have h37 : y = ⟨b, b⟩[hγ, hδ] := by
      have h38 : y = ⟨b, c⟩[hγ, hδ] := h22
      have h39 : c = b := by
        have h40 : b = c := h32
        tauto
      rw [h38]
      rw [h39]
      <;> rfl
    have h40 : ⟨b, b⟩[hγ, hδ] = {{b}[hδ]}[hγ] := by
      have h41 : {b}[hδ] = {b}[hδ] := rfl
      have h42 : {b}[hδ] = {b}[hδ] := rfl
      have h43 : {b}[hδ] = {b}[hδ] ∧ {b}[hδ] = {b}[hδ] := ⟨h41, h42⟩
      have h44 : ⟨b, b⟩[hγ, hδ] = {{b}[hδ]}[hγ] := by
        rw [ConNF.TSet.op_eq_singleton_iff]
        tauto
      tauto
    have h45 : y = {{b}[hδ]}[hγ] := by
      rw [h37]
      rw [h40]
      <;> rfl
    tauto
  · -- The backward direction
    rintro ⟨z, hz1, hz2⟩
    have h9 : y ∈' cardinalOne hβ hγ := by
      have h91 : ∃ (b : TSet γ), y = {b}[hγ] := ⟨{z}[hδ], by
        refine' Eq.symm _
        simp [hz2]
        <;> aesop
      ⟩
      exact (ConNF.mem_cardinalOne_iff hβ hγ y).mpr h91
    have h10 : ⟨z, z⟩[hγ, hδ] = {{z}[hδ]}[hγ] := by
      have h101 : {z}[hδ] = {z}[hδ] := rfl
      have h102 : {z}[hδ] = {z}[hδ] := rfl
      have h103 : {z}[hδ] = {z}[hδ] ∧ {z}[hδ] = {z}[hδ] := ⟨h101, h102⟩
      have h104 : ⟨z, z⟩[hγ, hδ] = {{z}[hδ]}[hγ] := by
        rw [ConNF.TSet.op_eq_singleton_iff]
        tauto
      tauto
    have h105 : y = ⟨z, z⟩[hγ, hδ] := by
      have h1051 : y = {{z}[hδ]}[hγ] := hz2
      have h1052 : ⟨z, z⟩[hγ, hδ] = {{z}[hδ]}[hγ] := h10
      have h1053 : y = {{z}[hδ]}[hγ] := h1051
      have h1054 : ⟨z, z⟩[hγ, hδ] = {{z}[hδ]}[hγ] := h1052
      have h1055 : y = ⟨z, z⟩[hγ, hδ] := by
        rw [h1053]
        rw [←h1054]
        <;> rfl
      tauto
    have h11 : y ∈' vCross hβ hγ hδ x := by
      rw [ConNF.vCross_spec]
      refine' ⟨z, z, _⟩
      constructor
      · exact h105
      · exact hz1
    have h12 : y ∈' converse hβ hγ hδ (vCross hβ hγ hδ x) := by
      have h121 : y ∈' converse' hβ hγ hδ (vCross hβ hγ hδ x) ∧ y ∈' orderedPairs hβ hγ hδ := by
        constructor
        · -- Prove y ∈' converse' hβ hγ hδ (vCross hβ hγ hδ x)
          have h1211 : y = ⟨z, z⟩[hγ, hδ] := h105
          have h1212 : ⟨z, z⟩[hγ, hδ] ∈' vCross hβ hγ hδ x := by
            rw [h1211] at h11
            exact h11
          have h1213 : ⟨z, z⟩[hγ, hδ] ∈' converse' hβ hγ hδ (vCross hβ hγ hδ x) ↔ ⟨z, z⟩[hγ, hδ] ∈' vCross hβ hγ hδ x := by
            exact (ConNF.converse'_spec hβ hγ hδ (vCross hβ hγ hδ x) z z)
          have h1214 : ⟨z, z⟩[hγ, hδ] ∈' converse' hβ hγ hδ (vCross hβ hγ hδ x) := by
            rw [h1213]
            exact h1212
          rw [h1211]
          exact h1214
        · -- Prove y ∈' orderedPairs hβ hγ hδ
          have h1222 : ∃ a b, y = ⟨a, b⟩' := ⟨z, z, by
            have h1223 : y = ⟨z, z⟩[hγ, hδ] := h105
            tauto
          ⟩
          have h1223 : y ∈' orderedPairs hβ hγ hδ := by
            simp only [mem_orderedPairs_iff]
            tauto
          exact h1223
      have h123 : y ∈' converse hβ hγ hδ (vCross hβ hγ hδ x) := by
        simp only [converse, mem_inter_iff]
        tauto
      tauto
    have h13 : y ∈' cross hβ hγ hδ x x := by
      have h131 : y ∈' converse hβ hγ hδ (vCross hβ hγ hδ x) := h12
      have h132 : y ∈' vCross hβ hγ hδ x := h11
      have h133 : y ∈' converse hβ hγ hδ (vCross hβ hγ hδ x) ⊓' vCross hβ hγ hδ x := by
        simp only [ConNF.mem_inter_iff hβ] <;> tauto
      simpa [cross] using h133
    have h14 : y ∈' cross hβ hγ hδ x x ⊓' cardinalOne hβ hγ := by
      simp only [ConNF.mem_inter_iff hβ]
      exact ⟨h13, h9⟩
    simpa [doubleSingleton] using h14

theorem mem_doubleSingleton_iff (x : TSet γ) :
    ∀ y : TSet β, y ∈' doubleSingleton hβ hγ hδ x ↔
    ∃ z : TSet δ, z ∈' x ∧ y = { {z}' }'  := by

  intro y
  exact round1_mem_doubleSingleton_iff hβ hγ hδ x y
