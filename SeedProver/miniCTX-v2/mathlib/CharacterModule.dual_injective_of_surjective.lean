-- In mathlib/Mathlib/Algebra/Module/CharacterModule.lean

/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Topology.Instances.AddCircle
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Character module of a module

For commutative ring `R` and an `R`-module `M` and an injective module `D`, its character module
`M⋆` is defined to be `R`-linear maps `M ⟶ D`.

`M⋆` also has an `R`-module structure given by `(r • f) m = f (r • m)`.

## Main results

- `CharacterModuleFunctor` : the contravariant functor of `R`-modules where `M ↦ M⋆` and
an `R`-linear map `l : M ⟶ N` induces an `R`-linear map `l⋆ : f ↦ f ∘ l` where `f : N⋆`.
- `LinearMap.dual_surjective_of_injective` : If `l` is injective then `l⋆` is surjective,
  in another word taking character module as a functor sends monos to epis.
- `CharacterModule.homEquiv` : there is a bijection between linear map `Hom(N, M⋆)` and
  `(N ⊗ M)⋆` given by `curry` and `uncurry`.

-/

open CategoryTheory

universe uR uA uB

variable (R : Type uR) [CommRing R]
variable (A : Type uA) [AddCommGroup A]
variable (A' : Type*) [AddCommGroup A']
variable (B : Type uB) [AddCommGroup B]

/--
The character module of an abelian group `A` in the unit rational circle is `A⋆ := Hom_ℤ(A, ℚ ⧸ ℤ)`.
-/
def CharacterModule : Type uA := A →+ AddCircle (1 : ℚ)

namespace CharacterModule

instance : FunLike (CharacterModule A) A (AddCircle (1 : ℚ)) where
  coe c := c.toFun
  coe_injective' _ _ _ := by aesop

instance : LinearMapClass (CharacterModule A) ℤ A (AddCircle (1 : ℚ)) where
  map_add _ _ _ := by rw [AddMonoidHom.map_add]
  map_smulₛₗ _ _ _ := by rw [AddMonoidHom.map_zsmul, RingHom.id_apply]

instance : AddCommGroup (CharacterModule A) :=
  inferInstanceAs (AddCommGroup (A →+ _))

@[ext] theorem ext {c c' : CharacterModule A} (h : ∀ x, c x = c' x) : c = c' := DFunLike.ext _ _ h

section module

variable [Module R A] [Module R A'] [Module R B]

instance : Module R (CharacterModule A) :=
  Module.compHom (A →+ _) (RingEquiv.toOpposite _ |>.toRingHom : R →+* Rᵈᵐᵃ)

variable {R A B}

@[simp] lemma smul_apply (c : CharacterModule A) (r : R) (a : A) : (r • c) a = c (r • a) := rfl

/--
Given an abelian group homomorphism `f : A → B`, `f⋆(L) := L ∘ f` defines a linear map
from `B⋆` to `A⋆`.
-/
@[simps] def dual (f : A →ₗ[R] B) : CharacterModule B →ₗ[R] CharacterModule A where
  toFun L := L.comp f.toAddMonoidHom
  map_add' := by aesop
  map_smul' r c := by ext x; exact congr(c $(f.map_smul r x)).symm

@[simp]
lemma dual_zero : dual (0 : A →ₗ[R] B) = 0 := by
  ext f
  exact map_zero f

lemma dual_comp {C : Type*} [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    dual (g.comp f) = (dual f).comp (dual g) := by
  ext
  rfl

/- Start of proof attempt -/
lemma round1_dual_injective_of_surjective (f : A →ₗ[R] B) (hf : Function.Surjective f) :
    Function.Injective (dual f) := by
  intro x y h
  have h1 : (x.comp f.toAddMonoidHom) = (y.comp f.toAddMonoidHom) := by
    simpa [dual] using h
  have h2 : ∀ (b : B), x b = y b := by
    intro b
    have h21 : ∃ a : A, f a = b := hf b
    obtain ⟨a, ha⟩ := h21
    have h3 : (x.comp f.toAddMonoidHom) a = (y.comp f.toAddMonoidHom) a := by
      rw [h1]
    have h4 : x (f a) = y (f a) := by simpa using h3
    rw [ha] at h4
    exact h4
  have h3 : x = y := by
    ext b
    exact h2 b
  simpa using h3

theorem dual_injective_of_surjective (f : A →ₗ[R] B) (hf : Function.Surjective f) :
    Function.Injective (dual f)  := by

  exact round1_dual_injective_of_surjective f hf
