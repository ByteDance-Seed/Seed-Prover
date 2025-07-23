-- In mathlib/Mathlib/Condensed/AB.lean

/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveColimits
import Mathlib.Condensed.Equivalence
import Mathlib.Condensed.Limits
/-!

# AB axioms in condensed modules

This file proves that the category of condensed modules over a ring satisfies Grothendieck's axioms
AB5, AB4, and AB4*.
-/

universe u

open Condensed CategoryTheory Limits

namespace Condensed

variable (A J : Type*) [Category A] [Category J] [Preadditive A]
  [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]
  [HasWeakSheafify (coherentTopology CompHaus.{u}) A]
  [HasWeakSheafify (extensiveTopology Stonean.{u}) A]
-- One of the `HasWeakSheafify` instances could be deduced from the other using the dense subsite
-- API, but when `A` is a concrete category, these will both be synthesized anyway.

lemma hasExactColimitsOfShape [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    [HasFiniteLimits A] : HasExactColimitsOfShape J (Condensed.{u} A) := by
  let e : Condensed.{u} A ≌ Sheaf (extensiveTopology Stonean.{u}) A :=
    (StoneanCompHaus.equivalence A).symm.trans Presheaf.coherentExtensiveEquivalence
  have : HasColimitsOfShape J (Sheaf (extensiveTopology Stonean.{u}) A) :=
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape e.inverse
  exact HasExactColimitsOfShape.domain_of_functor _ e.functor

/- Start of proof attempt -/
lemma round1_h1 (A J : Type*) [Category A] [Category J] [Preadditive A]
  [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]
  [HasWeakSheafify (coherentTopology CompHaus.{u}) A]
  [HasWeakSheafify (extensiveTopology Stonean.{u}) A]
  [HasLimitsOfShape J A] [HasExactLimitsOfShape J A] [HasFiniteColimits A]:
  HasLimitsOfShape J (Sheaf (extensiveTopology Stonean.{u}) A) := by
  infer_instance

theorem hasExactLimitsOfShape [HasLimitsOfShape J A] [HasExactLimitsOfShape J A]
    [HasFiniteColimits A] : HasExactLimitsOfShape J (Condensed.{u} A)  := by

  have h1 : HasLimitsOfShape J (Sheaf (extensiveTopology Stonean.{u}) A) := by
    exact round1_h1 A J
  exact HasExactLimitsOfShape.domain_of_functor _ 
    ((StoneanCompHaus.equivalence A).symm.trans Presheaf.coherentExtensiveEquivalence).functor
