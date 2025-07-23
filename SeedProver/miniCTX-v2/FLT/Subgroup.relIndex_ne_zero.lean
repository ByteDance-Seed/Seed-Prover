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

/- Start of proof attempt -/
lemma round1_relIndex_ne_zero [H.FiniteRelIndex K] : H.relindex K ≠ 0 := by
  exact?

theorem relIndex_ne_zero [H.FiniteRelIndex K] : H.relindex K ≠ 0  := by

  exact round1_relIndex_ne_zero
