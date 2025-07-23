-- In HepLean/HepLean/PerturbationTheory/FieldOpAlgebra/Grading.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpAlgebra.Basic
/-!

# Grading on the field operation algebra

-/

namespace FieldSpecification
open FieldOpFreeAlgebra
open HepLean.List
open FieldStatistic

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

/-- The submodule of `𝓕.FieldOpAlgebra` spanned by lists of field statistic `f`. -/
def statSubmodule (f : FieldStatistic) : Submodule ℂ 𝓕.FieldOpAlgebra :=
  Submodule.span ℂ {a | ∃ φs, a = ofCrAnList φs ∧ (𝓕 |>ₛ φs) = f}

lemma ofCrAnList_mem_statSubmodule_of_eq (φs : List 𝓕.CrAnFieldOp) (f : FieldStatistic)
    (h : (𝓕 |>ₛ φs) = f) : ofCrAnList φs ∈ statSubmodule f :=
  Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩

lemma ofCrAnList_mem_statSubmodule (φs : List 𝓕.CrAnFieldOp) :
    ofCrAnList φs ∈ statSubmodule (𝓕 |>ₛ φs) :=
  Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, rfl⟩⟩

lemma mem_bosonic_of_mem_free_bosonic (a : 𝓕.FieldOpFreeAlgebra)
    (h : a ∈ statisticSubmodule bosonic) : ι a ∈ statSubmodule .bosonic := by
  let p (a : 𝓕.FieldOpFreeAlgebra) (hx : a ∈ statisticSubmodule bosonic) : Prop :=
    ι a ∈ statSubmodule .bosonic
  change p a h
  apply Submodule.span_induction
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp [p]
    apply ofCrAnList_mem_statSubmodule_of_eq
    exact h
  · simp only [map_zero, p]
    exact Submodule.zero_mem (statSubmodule bosonic)
  · intro x y hx hy hpx hpy
    simp_all only [p, map_add]
    exact Submodule.add_mem _ hpx hpy
  · intro a x hx hy
    simp_all only [p, map_smul]
    exact Submodule.smul_mem _ _ hy

lemma mem_fermionic_of_mem_free_fermionic (a : 𝓕.FieldOpFreeAlgebra)
    (h : a ∈ statisticSubmodule fermionic) : ι a ∈ statSubmodule .fermionic := by
  let p (a : 𝓕.FieldOpFreeAlgebra) (hx : a ∈ statisticSubmodule fermionic) : Prop :=
    ι a ∈ statSubmodule .fermionic
  change p a h
  apply Submodule.span_induction
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp [p]
    apply ofCrAnList_mem_statSubmodule_of_eq
    exact h
  · simp only [map_zero, p]
    exact Submodule.zero_mem (statSubmodule fermionic)
  · intro x y hx hy hpx hpy
    simp_all only [p, map_add]
    exact Submodule.add_mem _ hpx hpy
  · intro a x hx hy
    simp_all only [p, map_smul]
    exact Submodule.smul_mem _ _ hy

lemma mem_statSubmodule_of_mem_statisticSubmodule (f : FieldStatistic) (a : 𝓕.FieldOpFreeAlgebra)
    (h : a ∈ statisticSubmodule f) : ι a ∈ statSubmodule f := by
  fin_cases f
  · exact mem_bosonic_of_mem_free_bosonic a h
  · exact mem_fermionic_of_mem_free_fermionic a h

/-- The projection of `statisticSubmodule (𝓕 := 𝓕) f` defined in the free algebra to
  `statSubmodule (𝓕 := 𝓕) f`. -/
def ιStateSubmodule (f : FieldStatistic) :
    statisticSubmodule (𝓕 := 𝓕) f →ₗ[ℂ] statSubmodule (𝓕 := 𝓕) f where
  toFun a := ⟨a.1, mem_statSubmodule_of_mem_statisticSubmodule f a.1 a.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable section

/-!

## Defining bosonicProj

-/

/-- The projection of `𝓕.FieldOpFreeAlgebra` to `statSubmodule (𝓕 := 𝓕) bosonic`. -/
def bosonicProjFree : 𝓕.FieldOpFreeAlgebra →ₗ[ℂ] statSubmodule (𝓕 := 𝓕) bosonic :=
  ιStateSubmodule .bosonic ∘ₗ bosonicProjF

lemma bosonicProjFree_eq_ι_bosonicProjF (a : 𝓕.FieldOpFreeAlgebra) :
    (bosonicProjFree a).1 = ι (bosonicProjF a) := rfl

lemma bosonicProjFree_zero_of_ι_zero (a : 𝓕.FieldOpFreeAlgebra) (h : ι a = 0) :
    bosonicProjFree a = 0 := by
  rw [ι_eq_zero_iff_ι_bosonicProjF_fermonicProj_zero] at h
  apply Subtype.eq
  rw [bosonicProjFree_eq_ι_bosonicProjF]
  exact h.1

lemma bosonicProjFree_eq_of_equiv (a b : 𝓕.FieldOpFreeAlgebra) (h : a ≈ b) :
    bosonicProjFree a = bosonicProjFree b := by
  rw [equiv_iff_sub_mem_ideal, ← ι_eq_zero_iff_mem_ideal] at h
  rw [LinearMap.sub_mem_ker_iff.mp]
  simp only [LinearMap.mem_ker, ← map_sub]
  exact bosonicProjFree_zero_of_ι_zero (a - b) h

/-- The projection of `𝓕.FieldOpAlgebra` to `statSubmodule (𝓕 := 𝓕) bosonic`. -/
def bosonicProj : 𝓕.FieldOpAlgebra →ₗ[ℂ] statSubmodule (𝓕 := 𝓕) bosonic where
  toFun := Quotient.lift bosonicProjFree bosonicProjFree_eq_of_equiv
  map_add' x y := by
    obtain ⟨x, hx⟩ := ι_surjective x
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hx hy
    rw [← map_add, ι_apply, ι_apply, ι_apply]
    rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
    simp
  map_smul' c y := by
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hy
    rw [← map_smul, ι_apply, ι_apply]
    simp

lemma bosonicProj_eq_bosonicProjFree (a : 𝓕.FieldOpFreeAlgebra) :
    bosonicProj (ι a) = bosonicProjFree a := rfl

/-!

## Defining fermionicProj

-/

/-- The projection of `𝓕.FieldOpFreeAlgebra` to `statSubmodule (𝓕 := 𝓕) fermionic`. -/
def fermionicProjFree : 𝓕.FieldOpFreeAlgebra →ₗ[ℂ] statSubmodule (𝓕 := 𝓕) fermionic :=
  ιStateSubmodule .fermionic ∘ₗ fermionicProjF

lemma fermionicProjFree_eq_ι_fermionicProjF (a : 𝓕.FieldOpFreeAlgebra) :
    (fermionicProjFree a).1 = ι (fermionicProjF a) := rfl

/- Start of proof attempt -/
lemma round1_h_fermionic_proj_zero (a : 𝓕.FieldOpFreeAlgebra) (h : ι a = 0) :
    ι ((fermionicProjF a).1) = 0 := by
  rw [ι_eq_zero_iff_ι_bosonicProjF_fermonicProj_zero] at h
  exact h.2

lemma round1_h_main (a : 𝓕.FieldOpFreeAlgebra) (h_fermionic_proj_zero : ι ((fermionicProjF a).1) = 0) :
    (fermionicProjFree a).1 = 0 := by
  have h1 : (fermionicProjFree a).1 = ι ((fermionicProjF a).1) := fermionicProjFree_eq_ι_fermionicProjF a
  rw [h1]
  exact h_fermionic_proj_zero

lemma round1_h_final (a : 𝓕.FieldOpFreeAlgebra) (h_main : (fermionicProjFree a).1 = 0) :
    fermionicProjFree a = 0 := by
  apply Subtype.eq
  simpa using h_main

theorem fermionicProjFree_zero_of_ι_zero (a : 𝓕.FieldOpFreeAlgebra) (h : ι a = 0) :
    fermionicProjFree a = 0  := by

  have h_fermionic_proj_zero : ι ((fermionicProjF a).1) = 0 := by
    exact round1_h_fermionic_proj_zero a h
  have h_main : (fermionicProjFree a).1 = 0 := by
    exact round1_h_main a h_fermionic_proj_zero
  have h_final : fermionicProjFree a = 0 := by
    exact round1_h_final a h_main
  exact h_final
