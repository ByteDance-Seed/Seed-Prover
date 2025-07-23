-- In HepLean/HepLean/PerturbationTheory/WickContraction/Join.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.TimeContract
import HepLean.PerturbationTheory.WickContraction.StaticContract
import HepLean.PerturbationTheory.FieldOpAlgebra.TimeContraction
import HepLean.PerturbationTheory.WickContraction.SubContraction
import HepLean.PerturbationTheory.WickContraction.Singleton

/-!

# Join of contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open FieldOpAlgebra

/-- Given a list `φs` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs` and a Wick contraction
  `φsucΛ` of `[φsΛ]ᵘᶜ`, `join φsΛ φsucΛ` is defined as the Wick contraction of `φs` consisting of
  the contractions in `φsΛ` and those in `φsucΛ`.

  As an example, for `φs = [φ1, φ2, φ3, φ4]`,
  `φsΛ = {{0, 1}}` corresponding to the contraction of `φ1` and `φ2` in `φs` and
  `φsucΛ = {{0, 1}}`
  corresponding to the contraction of `φ3` and `φ4` in `[φsΛ]ᵘᶜ = [φ3, φ4]`, then
  `join φsΛ φsucΛ` is the contraction `{{0, 1}, {2, 3}}` of `φs`. -/
def join {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) : WickContraction φs.length :=
  ⟨φsΛ.1 ∪ φsucΛ.1.map (Finset.mapEmbedding uncontractedListEmd).toEmbedding, by
    intro a ha
    simp only [Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding] at ha
    rcases ha with ha | ha
    · exact φsΛ.2.1 a ha
    · obtain ⟨a, ha, rfl⟩ := ha
      rw [Finset.mapEmbedding_apply]
      simp only [Finset.card_map]
      exact φsucΛ.2.1 a ha, by
    intro a ha b hb
    simp only [Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact φsΛ.2.2 a ha b hb
    · obtain ⟨b, hb, rfl⟩ := hb
      right
      symm
      rw [Finset.mapEmbedding_apply]
      apply uncontractedListEmd_finset_disjoint_left
      exact ha
    · obtain ⟨a, ha, rfl⟩ := ha
      right
      rw [Finset.mapEmbedding_apply]
      apply uncontractedListEmd_finset_disjoint_left
      exact hb
    · obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, rfl⟩ := hb
      simp only [EmbeddingLike.apply_eq_iff_eq]
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply]
      rw [Finset.disjoint_map]
      exact φsucΛ.2.2 a ha b hb⟩

lemma join_congr {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} {φsΛ' : WickContraction φs.length}
    (h1 : φsΛ = φsΛ') :
    join φsΛ φsucΛ = join φsΛ' (congr (by simp [h1]) φsucΛ) := by
  subst h1
  rfl

/-- Given a contracting pair within `φsΛ` the corresponding contracting pair within
  `(join φsΛ φsucΛ)`. -/
def joinLiftLeft {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : φsΛ.1 → (join φsΛ φsucΛ).1 :=
  fun a => ⟨a, by simp [join]⟩

lemma jointLiftLeft_injective {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} :
    Function.Injective (@joinLiftLeft _ _ φsΛ φsucΛ) := by
  intro a b h
  simp only [joinLiftLeft] at h
  rw [Subtype.mk_eq_mk] at h
  refine Subtype.eq h

/-- Given a contracting pair within `φsucΛ` the corresponding contracting pair within
  `(join φsΛ φsucΛ)`. -/
def joinLiftRight {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : φsucΛ.1 → (join φsΛ φsucΛ).1 :=
  fun a => ⟨a.1.map uncontractedListEmd, by
    simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding]
    right
    use a.1
    simp only [Finset.coe_mem, true_and]
    rfl⟩

lemma joinLiftRight_injective {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} :
    Function.Injective (@joinLiftRight _ _ φsΛ φsucΛ) := by
  intro a b h
  simp only [joinLiftRight] at h
  rw [Subtype.mk_eq_mk] at h
  simp only [Finset.map_inj] at h
  refine Subtype.eq h

lemma jointLiftLeft_disjoint_joinLiftRight {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} (a : φsΛ.1) (b : φsucΛ.1) :
    Disjoint (@joinLiftLeft _ _ _ φsucΛ a).1 (joinLiftRight b).1 := by
  simp only [joinLiftLeft, joinLiftRight]
  symm
  apply uncontractedListEmd_finset_disjoint_left
  exact a.2

lemma jointLiftLeft_neq_joinLiftRight {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} (a : φsΛ.1) (b : φsucΛ.1) :
    joinLiftLeft a ≠ joinLiftRight b := by
  by_contra hn
  have h1 := jointLiftLeft_disjoint_joinLiftRight a b
  rw [hn] at h1
  simp only [disjoint_self, Finset.bot_eq_empty] at h1
  have hj := (join φsΛ φsucΛ).2.1 (joinLiftRight b).1 (joinLiftRight b).2
  rw [h1] at hj
  simp at hj

/-- The map from contracted pairs of `φsΛ` and `φsucΛ` to contracted pairs in
  `(join φsΛ φsucΛ)`. -/
def joinLift {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : φsΛ.1 ⊕ φsucΛ.1 → (join φsΛ φsucΛ).1 := fun a =>
  match a with
  | Sum.inl a => joinLiftLeft a
  | Sum.inr a => joinLiftRight a

lemma joinLift_injective {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : Function.Injective (@joinLift _ _ φsΛ φsucΛ) := by
  intro a b h
  match a, b with
  | Sum.inl a, Sum.inl b =>
    simp only [Sum.inl.injEq]
    exact jointLiftLeft_injective h
  | Sum.inr a, Sum.inr b =>
    simp only [Sum.inr.injEq]
    exact joinLiftRight_injective h
  | Sum.inl a, Sum.inr b =>
    simp only [joinLift] at h
    have h1 := jointLiftLeft_neq_joinLiftRight a b
    simp_all
  | Sum.inr a, Sum.inl b =>
    simp only [joinLift] at h
    have h1 := jointLiftLeft_neq_joinLiftRight b a
    simp_all

lemma joinLift_surjective {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : Function.Surjective (@joinLift _ _ φsΛ φsucΛ) := by
  intro a
  have ha2 := a.2
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at ha2
  rcases ha2 with ha2 | ⟨a2, ha3⟩
  · use Sum.inl ⟨a, ha2⟩
    simp [joinLift, joinLiftLeft]
  · rw [Finset.mapEmbedding_apply] at ha3
    use Sum.inr ⟨a2, ha3.1⟩
    simp only [joinLift, joinLiftRight]
    refine Subtype.eq ?_
    exact ha3.2

lemma joinLift_bijective {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : Function.Bijective (@joinLift _ _ φsΛ φsucΛ) := by
  apply And.intro
  · exact joinLift_injective
  · exact joinLift_surjective

lemma prod_join {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (f : (join φsΛ φsucΛ).1 → M) [CommMonoid M]:
      ∏ (a : (join φsΛ φsucΛ).1), f a = (∏ (a : φsΛ.1), f (joinLiftLeft a)) *
      ∏ (a : φsucΛ.1), f (joinLiftRight a) := by
  let e1 := Equiv.ofBijective (@joinLift _ _ φsΛ φsucΛ) joinLift_bijective
  rw [← e1.prod_comp]
  simp only [Fintype.prod_sum_type, Finset.univ_eq_attach]
  rfl

lemma joinLiftLeft_or_joinLiftRight_of_mem_join {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) {a : Finset (Fin φs.length)}
    (ha : a ∈ (join φsΛ φsucΛ).1) :
    (∃ b, a = (joinLiftLeft (φsucΛ := φsucΛ) b).1) ∨
    (∃ b, a = (joinLiftRight (φsucΛ := φsucΛ) b).1) := by
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at ha
  rcases ha with ha | ⟨a, ha, rfl⟩
  · left
    use ⟨a, ha⟩
    rfl
  · right
    use ⟨a, ha⟩
    rfl

@[simp]
lemma join_fstFieldOfContract_joinLiftRight {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsucΛ.1) :
    (join φsΛ φsucΛ).fstFieldOfContract (joinLiftRight a) =
    uncontractedListEmd (φsucΛ.fstFieldOfContract a) := by
  apply eq_fstFieldOfContract_of_mem _ _ _ (uncontractedListEmd (φsucΛ.sndFieldOfContract a))
  · simp [joinLiftRight]
  · simp [joinLiftRight]
  · apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract φsucΛ a

@[simp]
lemma join_sndFieldOfContract_joinLiftRight {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsucΛ.1) :
    (join φsΛ φsucΛ).sndFieldOfContract (joinLiftRight a) =
    uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by
  apply eq_sndFieldOfContract_of_mem _ _ (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
  · simp [joinLiftRight]
  · simp [joinLiftRight]
  · apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract φsucΛ a

/- Start of proof attempt -/
lemma round1_join_fstFieldOfContract_joinLiftLeft {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsΛ.1) :
    (join φsΛ φsucΛ).fstFieldOfContract (joinLiftLeft a) =
    (φsΛ.fstFieldOfContract a) := by
  simp [joinLiftLeft]
  <;>
  aesop

theorem join_fstFieldOfContract_joinLiftLeft {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsΛ.1) :
    (join φsΛ φsucΛ).fstFieldOfContract (joinLiftLeft a) =
    (φsΛ.fstFieldOfContract a)  := by

  exact round1_join_fstFieldOfContract_joinLiftLeft φsΛ φsucΛ a
