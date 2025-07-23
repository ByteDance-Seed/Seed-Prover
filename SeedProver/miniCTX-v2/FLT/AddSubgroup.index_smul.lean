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

@[to_additive]
lemma index_map_of_bijective (S : Subgroup G) (hf : Bijective f) : (S.map f).index = S.index :=
  index_map_eq _ hf.2 (by rw [f.ker_eq_bot_iff.2 hf.1]; exact bot_le)

end Subgroup

namespace AddSubgroup
variable {G A : Type*} [Group G] [AddGroup A] [DistribMulAction G A]

-- TODO: Why does making this lemma simp make `NumberTheory.Padic.PadicIntegers` time out?

/- Start of proof attempt -/
lemma round1_index_smul (a : G) (S : AddSubgroup A) : (a • S).index = S.index := by
  have h1 : ∀ (a : G) (x y : A), a • (x + y) = a • x + a • y := by
    intro a x y
    exact?
  have h2 : ∀ (a : G), ∃ (f : A →+ A), ∀ (x : A), f x = a • x := by
    intro a
    refine ⟨{ toFun := fun x => a • x,
              map_zero' := by simp,
              map_add' := by
                intro x y
                exact h1 a x y }, fun x => rfl⟩
  rcases h2 a with ⟨f, hf⟩
  have h_inj : Function.Injective f := by
    intro x y h
    have h3 : f x = f y := h
    have h4 : a • x = a • y := by
      have h41 : f x = a • x := by rw [hf x]
      have h42 : f y = a • y := by rw [hf y]
      rw [h41] at h3
      rw [h42] at h3
      exact h3
    have h5 : a⁻¹ • (a • x) = a⁻¹ • (a • y) := by rw [h4]
    have h6 : a⁻¹ • (a • x) = x := by
      simp [smul_smul]
      <;> simp
    have h7 : a⁻¹ • (a • y) = y := by
      simp [smul_smul]
      <;> simp
    rw [h6] at h5
    rw [h7] at h5
    exact h5
  have h_surj : Function.Surjective f := by
    intro y
    use a⁻¹ • y
    have h8 : f (a⁻¹ • y) = a • (a⁻¹ • y) := by
      rw [hf (a⁻¹ • y)]
      <;> simp
    have h9 : a • (a⁻¹ • y) = y := by
      simp [smul_smul]
      <;> simp
    rw [h8, h9]
    <;> simp
  have h_bij : Function.Bijective f := ⟨h_inj, h_surj⟩
  have h10 : (S.map f).index = S.index := by
    exact?
  have h11 : S.map f = a • S := by
    ext x
    simp [hf]
    <;> aesop
  rw [h11] at h10
  exact h10

theorem index_smul (a : G) (S : AddSubgroup A) : (a • S).index = S.index  := by

  exact round1_index_smul a S
