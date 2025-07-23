-- In FLT/FLT/NumberField/Embeddings.lean

import Mathlib.NumberTheory.NumberField.Embeddings

/-!
# Embeddings of number fields
-/

namespace NumberField.InfinitePlace

variable {K : Type*} (L : Type*) [Field K] [Field L]

/--
If `L / K` are fields and `v` is an infinite place of `K`, then we say an infinite place `w`
of `L` _extends_ `v` if `w` can be constructed from a complex embedding `L →+* ℂ` whose
restriction to `K` is an associated complex embedding `K →+* ℂ` of `v`.
-/
abbrev ExtensionPlace [Algebra K L] (v : InfinitePlace K) :=
  { w : InfinitePlace L // w.comap (algebraMap K L) = v }

variable {L}

/- Start of proof attempt -/
lemma round1_comap_apply (w : NumberField.InfinitePlace L) (f : K →+* L) (x : K) :
    w.comap f x = w (f x) := by
  rfl

theorem comap_apply (w : InfinitePlace L) (f : K →+* L) (x : K) :
    w.comap f x = w (f x)  := by

  exact round1_comap_apply w f x
