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
/-- Well-orders are rigid. -/
theorem apply_eq_of_isWellOrder {X : Type _} {r : Rel X X} {f : X → X}
    (hr : IsWellOrder X r) (hf : Function.Bijective f) (hf' : ∀ x y, r x y ↔ r (f x) (f y)) :
    ∀ x, f x = x := by
  let emb : r ≼i r := ⟨⟨⟨f, hf.injective⟩, λ {a b} ↦ (hf' a b).symm⟩, ?_⟩
  · have : emb = InitialSeg.refl r := Subsingleton.elim _ _
    intro x
    exact congr_arg (λ f ↦ f x) this
  · intro a b h
    exact hf.surjective _

omit [Params] in
theorem apply_eq_of_isWellOrder' {X : Type _} {r : Rel X X} {f : X → X}
    (hr : IsWellOrder r.field (InvImage r Subtype.val)) (hf : Function.Bijective f)
    (hf' : ∀ x y, r x y ↔ r (f x) (f y)) :
    ∀ x ∈ r.field, f x = x := by
  have : ∀ x ∈ r.field, f x ∈ r.field := by
    rintro x (⟨y, h⟩ | ⟨y, h⟩)
    · exact Or.inl ⟨f y, (hf' x y).mp h⟩
    · exact Or.inr ⟨f y, (hf' y x).mp h⟩
  have := apply_eq_of_isWellOrder (f := λ x ↦ ⟨f x.val, this x.val x.prop⟩) hr ⟨?_, ?_⟩ ?_
  · intro x hx
    exact congr_arg Subtype.val (this ⟨x, hx⟩)
  · intro x y h
    rw [Subtype.mk.injEq] at h
    exact Subtype.val_injective (hf.injective h)
  · intro x
    obtain ⟨y, hy⟩ := hf.surjective x.val
    refine ⟨⟨y, ?_⟩, ?_⟩
    · obtain (⟨z, h⟩ | ⟨z, h⟩) := x.prop <;>
          rw [← hy] at h <;>
          obtain ⟨z, rfl⟩ := hf.surjective z
      · exact Or.inl ⟨z, (hf' y z).mpr h⟩
      · exact Or.inr ⟨z, (hf' z y).mpr h⟩
    · simp only [hy]
  · intros
    apply hf'

theorem exists_common_support_of_internallyWellOrdered' {x : TSet δ}
    (h : InternallyWellOrdered hγ hδ hε x) :
    ∃ S : Support β, ∀ y, y ∈' x → S.Supports { { {y}' }' }[hγ] := by
  obtain (h | ⟨r, h, rfl⟩) := h
  · obtain (h | ⟨y, hy⟩) := h.eq_empty_or_singleton
    · use ⟨Enumeration.empty, Enumeration.empty⟩
      intro y hy
      rw [Set.eq_empty_iff_forall_not_mem] at h
      cases h y hy
    · obtain ⟨S, hS⟩ := TSet.exists_support y
      use S ↗ hε ↗ hδ ↗ hγ
      intro z hz
      rw [Set.eq_singleton_iff_unique_mem] at hy
      cases hy.2 z hz
      refine ⟨?_, λ h ↦ by cases h⟩
      intro ρ hρ
      simp only [Support.smul_scoderiv, ← allPermSderiv_forget', Support.scoderiv_inj] at hρ
      simp only [smul_singleton, singleton_inj]
      exact hS _ hρ
  obtain ⟨S, hS⟩ := TSet.exists_support r
  use S
  intro a ha
  refine ⟨?_, λ h ↦ by cases h⟩
  intro ρ hρ
  have := hS ρ hρ
  simp only [smul_singleton, singleton_inj]
  apply apply_eq_of_isWellOrder' (r := ExternalRel hγ hδ hε r)
  · exact h
  · exact MulAction.bijective (ρ ↘ hγ ↘ hδ ↘ hε)
  · intro x y
    conv_rhs => rw [← this]
    simp only [externalRel_smul, InvImage, inv_smul_smul]
  · rwa [mem_field_iff] at ha

include hγ in
theorem Support.Supports.ofSingleton {S : Support α} {x : TSet β}
    (h : S.Supports {x}') :
    letI : Level := ⟨α⟩
    letI : LeLevel α := ⟨le_rfl⟩
    (S.strong ↘ hβ).Supports x := by
  refine ⟨?_, λ h ↦ by cases h⟩
  intro ρ hρ
  open scoped Pointwise in
  have := sUnion_singleton_symmetric_aux hγ hβ {y | y ∈' x} S ?_ ρ hρ
  · apply ConNF.ext hγ
    intro z
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_smul_set_iff_inv_smul_mem] at this
    rw [mem_smul_iff', allPerm_inv_sderiv', this]
  · intro ρ hρ
    ext z
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_image, Set.mem_setOf_eq]
    have := h.supports ρ hρ
    simp only [smul_singleton, singleton_inj] at this
    constructor
    · rintro ⟨y, h₁, h₂⟩
      rw [← smul_eq_iff_eq_inv_smul, smul_singleton] at h₂
      refine ⟨_, ?_, h₂⟩
      rw [← this]
      simp only [mem_smul_iff', allPerm_inv_sderiv', inv_smul_smul]
      exact h₁
    · rintro ⟨y, h, rfl⟩
      refine ⟨(ρ ↘ hβ ↘ hγ)⁻¹ • y, ?_, ?_⟩
      · rwa [← allPerm_inv_sderiv', ← mem_smul_iff', this]
      · simp only [smul_singleton, allPerm_inv_sderiv']

include hγ in
theorem supports_of_supports_singletons {S : Support α} {s : Set (TSet β)}
    (h : ∀ x ∈ s, S.Supports {x}') :
    ∃ S : Support β, ∀ x ∈ s, S.Supports x :=
  ⟨_, λ x hx ↦ (h x hx).ofSingleton hβ hγ⟩

theorem exists_common_support_of_internallyWellOrdered {x : TSet δ}
    (h : InternallyWellOrdered hγ hδ hε x) :
    ∃ S : Support δ, ∀ y, y ∈' x → S.Supports {y}' := by
  obtain ⟨S, hS⟩ := exists_common_support_of_internallyWellOrdered' hγ hδ hε h
  have := supports_of_supports_singletons (S := S)
      (s := singleton hδ '' (singleton hε '' {y | y ∈' x})) hγ hδ ?_
  swap
  · simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    exact hS
  obtain ⟨T, hT⟩ := this
  have := supports_of_supports_singletons (S := T)
      (s := singleton hε '' {y | y ∈' x}) hδ hε ?_
  swap
  · simp only [Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hT ⊢
    exact hT
  simp only [Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at this
  exact this

theorem internallyWellOrdered_of_common_support_of_nontrivial {x : TSet γ}
    (hx : {y : TSet δ | y ∈' x}.Nontrivial)
    (S : Support δ) (hS : ∀ y : TSet δ, y ∈' x → S.Supports y) :
    InternallyWellOrdered hβ hγ hδ x := by
  have := exists_of_symmetric
      {p : TSet β | ∃ a b : TSet δ, p = ⟨a, b⟩' ∧ a ∈' x ∧ b ∈' x ∧ WellOrderingRel a b} hβ ?_
  swap
  · use S ↗ hδ ↗ hγ ↗ hβ
    intro ρ hρ
    ext z
    simp only [Support.smul_scoderiv, ← allPermSderiv_forget', Support.scoderiv_inj] at hρ
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, b, h₁, h₂, h₃, h₄⟩
      refine ⟨a, b, ?_, h₂, h₃, h₄⟩
      rw [inv_smul_eq_iff] at h₁
      rw [h₁, smul_op, op_inj]
      exact ⟨(hS a h₂).supports _ hρ, (hS b h₃).supports _ hρ⟩
    · rintro ⟨a, b, h₁, h₂, h₃, h₄⟩
      refine ⟨a, b, ?_, h₂, h₃, h₄⟩
      rw [h₁, smul_op, op_inj]
      simp only [allPerm_inv_sderiv', inv_smul_eq_iff]
      rw [(hS a h₂).supports _ hρ, (hS b h₃).supports _ hρ]
      exact ⟨rfl, rfl⟩
  obtain ⟨r, hr⟩ := this
  right
  use r
  have hr' : ∀ a b, ExternalRel hβ hγ hδ r a b ↔ a ∈' x ∧ b ∈' x ∧ WellOrderingRel a b := by
    intro a b
    rw [ExternalRel, hr]
    simp only [Set.mem_setOf_eq, op_inj]
    constructor
    · rintro ⟨a, b, ⟨rfl, rfl⟩, h⟩
      exact h
    · intro h
      exact ⟨a, b, ⟨rfl, rfl⟩, h⟩
  have hrx : ∀ a, a ∈ (ExternalRel hβ hγ hδ r).field ↔ a ∈' x := by
    intro a
    constructor
    · rintro (⟨b, h⟩ | ⟨b, h⟩)
      · rw [hr'] at h
        exact h.1
      · rw [hr'] at h
        exact h.2.1
    · intro h
      obtain ⟨b, h₁, h₂⟩ := hx.exists_ne a
      obtain (h₃ | h₃ | h₃) := WellOrderingRel.isWellOrder.trichotomous a b
      · refine Or.inl ⟨b, ?_⟩
        rw [hr']
        exact ⟨h, h₁, h₃⟩
      · cases h₂ h₃.symm
      · refine Or.inr ⟨b, ?_⟩
        rw [hr']
        exact ⟨h₁, h, h₃⟩
  refine ⟨?_, ?_⟩
  swap
  · apply ext hδ
    intro z
    rw [mem_field_iff, hrx]
  refine @IsWellOrder.mk _ _ ?_ ?_ ?_
  · constructor
    intro a b
    obtain (h | h | h) := WellOrderingRel.isWellOrder.trichotomous a.val b.val
    · apply Or.inl
      rw [InvImage, hr']
      exact ⟨(hrx a).mp a.prop, (hrx b).mp b.prop, h⟩
    · exact Or.inr (Or.inl (Subtype.val_injective h))
    · apply Or.inr ∘ Or.inr
      rw [InvImage, hr']
      exact ⟨(hrx b).mp b.prop, (hrx a).mp a.prop, h⟩
  · constructor
    intro a b c h₁ h₂
    rw [InvImage, hr'] at h₁ h₂ ⊢
    exact ⟨h₁.1, h₂.2.1, WellOrderingRel.isWellOrder.trans _ _ _ h₁.2.2 h₂.2.2⟩
  · constructor
    apply InvImage.wf
    refine Subrelation.wf ?_ WellOrderingRel.isWellOrder.wf
    intro a b h
    rw [hr'] at h
    exact h.2.2

/- Start of proof attempt -/
lemma round1_internallyWellOrdered_of_common_support {x : TSet γ}
    (S : Support δ) (hS : ∀ y : TSet δ, y ∈' x → S.Supports y) :
    InternallyWellOrdered hβ hγ hδ x := by
  by_cases h : Set.Nontrivial {y : TSet δ | y ∈' x}
  · -- Case 1: {y : TSet δ | y ∈' x} is nontrivial
    exact internallyWellOrdered_of_common_support_of_nontrivial hβ hγ hδ h S hS
  · -- Case 2: {y : TSet δ | y ∈' x} is not nontrivial
    have h1 : Set.Subsingleton {y : TSet δ | y ∈' x} := by
      have h2 : ¬ Set.Nontrivial {y : TSet δ | y ∈' x} := h
      intro a ha b hb
      by_contra h3
      have h4 : Set.Nontrivial {y : TSet δ | y ∈' x} := ⟨a, ha, b, hb, h3⟩
      contradiction
    left
    exact h1

theorem internallyWellOrdered_of_common_support {x : TSet γ}
    (S : Support δ) (hS : ∀ y : TSet δ, y ∈' x → S.Supports y) :
    InternallyWellOrdered hβ hγ hδ x  := by

  exact round1_internallyWellOrdered_of_common_support hβ hγ hδ S hS
