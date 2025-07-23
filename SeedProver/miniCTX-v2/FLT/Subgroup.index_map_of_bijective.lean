-- In FLT/FLT/Mathlib/GroupTheory/Index.lean

import Mathlib.GroupTheory.Index

/-!
# TODO

* Rename `relindex` to `relIndex`
* Rename `FiniteIndex.finiteIndex` to `FiniteIndex.index_ne_zero`
-/

open Function
open scoped Pointwise

-- This is cool notation. Should mathlib have it? And what should the `relindex` version be?
scoped[GroupTheory] notation "[" G ":" H "]" => @AddSubgroup.index G _ H

namespace Subgroup
variable {G G' : Type*} [Group G] [Group G'] {f : G →* G'} {H K : Subgroup G}

class _root_.AddSubgroup.FiniteRelIndex {G : Type*} [AddGroup G] (H K : AddSubgroup G) : Prop where
  protected relIndex_ne_zero : H.relindex K ≠ 0

@[to_additive] class FiniteRelIndex (H K : Subgroup G) : Prop where
  protected relIndex_ne_zero : H.relindex K ≠ 0

@[to_additive]
lemma relIndex_ne_zero [H.FiniteRelIndex K] : H.relindex K ≠ 0 := FiniteRelIndex.relIndex_ne_zero

@[to_additive]
instance FiniteRelIndex.to_finiteIndex_subgroupOf [H.FiniteRelIndex K] :
    (H.subgroupOf K).FiniteIndex where
  finiteIndex := relIndex_ne_zero

/- Start of proof attempt -/
lemma round1_h8 (G G' : Type*) [Group G] [Group G'] (f : G →* G') (S : Subgroup G) (hf : Bijective f) (φ : G ≃* G') (hφ : φ.toMonoidHom = f) : (φ.toMonoidHom).range = ⊤ := by
  have h81 : Function.Surjective (φ.toMonoidHom) := by
    have h_f_surj : Function.Surjective f := hf.surjective
    have h1 : φ.toMonoidHom = f := by rw [hφ]
    rw [h1]
    exact h_f_surj
  ext y
  simp only [Subgroup.mem_top]
  constructor
  · intro _; trivial
  · intro _
    have h82 : ∃ (x : G), φ.toMonoidHom x = y := by
      exact h81 y
    rcases h82 with ⟨x, hx⟩
    refine ⟨x,?_⟩
    simpa using hx

lemma round1_h7 (G G' : Type*) [Group G] [Group G'] (f : G →* G') (S : Subgroup G) (hf : Bijective f) (φ : G ≃* G') (hφ : φ.toMonoidHom = f) : (φ.toMonoidHom).ker = ⊥ := by
  ext x
  simp [MonoidHom.mem_ker]
  <;>
  (try simp [hφ] at * <;> aesop) <;>
  (try
    {
      have h1 := (hf.injective)
      aesop
    }
  )

lemma round1_h9 (G G' : Type*) [Group G] [Group G'] (f : G →* G') (S : Subgroup G) (φ : G ≃* G') (h7 : (φ.toMonoidHom).ker = ⊥) : S ⊔ (φ.toMonoidHom).ker = S := by
  rw [h7]
  simp

lemma round1_h11 (G G' : Type*) [Group G] [Group G'] (f : G →* G') (S : Subgroup G) (φ : G ≃* G') (h8 : (φ.toMonoidHom).range = ⊤) : ((φ.toMonoidHom).range).index = 1 := by
  rw [h8]
  simp

lemma round1_h12 (G G' : Type*) [Group G] [Group G'] (f : G →* G') (S : Subgroup G) (φ : G ≃* G') : (S.map (φ.toMonoidHom)).index = (S ⊔ (φ.toMonoidHom).ker).index * ((φ.toMonoidHom).range).index := by
  rw [Subgroup.index_map]
  <;>
  aesop

lemma round1_h13 (G G' : Type*) [Group G] [Group G'] (f : G →* G') (S : Subgroup G) (φ : G ≃* G') (h10 : (S ⊔ (φ.toMonoidHom).ker).index = S.index) (h11 : ((φ.toMonoidHom).range).index = 1) (h12 : (S.map (φ.toMonoidHom)).index = (S ⊔ (φ.toMonoidHom).ker).index * ((φ.toMonoidHom).range).index) : (S.map (φ.toMonoidHom)).index = S.index := by
  rw [h12, h10, h11]
  <;> simp [mul_one]

lemma round1_h6 (G G' : Type*) [Group G] [Group G'] (f : G →* G') (S : Subgroup G) (φ : G ≃* G') (hφ : φ.toMonoidHom = f) : (S.map f).index = (S.map (φ.toMonoidHom)).index := by
  rw [hφ]

theorem index_map_of_bijective (S : Subgroup G) (hf : Bijective f) : (S.map f).index = S.index  := by

  have h2 : ∃ (φ : G ≃* G'), φ.toMonoidHom = f := by
    refine ⟨MulEquiv.ofBijective f hf, rfl⟩
  obtain ⟨φ, hφ⟩ := h2
  have h8 : (φ.toMonoidHom).range = ⊤ := by
    exact round1_h8 G G' f S hf φ hφ
  have h7 : (φ.toMonoidHom).ker = ⊥ := by
    exact round1_h7 G G' f S hf φ hφ
  have h9 : S ⊔ (φ.toMonoidHom).ker = S := by
    exact round1_h9 G G' f S φ h7
  have h10 : (S ⊔ (φ.toMonoidHom).ker).index = S.index := by
    rw [h9]
  have h11 : ((φ.toMonoidHom).range).index = 1 := by
    exact round1_h11 G G' f S φ h8
  have h12 : (S.map (φ.toMonoidHom)).index = (S ⊔ (φ.toMonoidHom).ker).index * ((φ.toMonoidHom).range).index := by
    exact round1_h12 G G' f S φ
  have h13 : (S.map (φ.toMonoidHom)).index = S.index := by
    exact round1_h13 G G' f S φ h10 h11 h12
  have h6 : (S.map f).index = (S.map (φ.toMonoidHom)).index := by
    exact round1_h6 G G' f S φ hφ
  rw [h6, h13]
