-- In FLT/FLT/Mathlib/Topology/Algebra/UniformRing.lean

import Mathlib.Topology.Algebra.UniformRing
import FLT.Mathlib.Algebra.Algebra.Hom

/-!
# Completion of topological rings
-/

namespace UniformSpace.Completion

variable {α : Type*} [Ring α] [UniformSpace α] [TopologicalRing α] [UniformAddGroup α]
  {β : Type*} [UniformSpace β] [Ring β] [UniformAddGroup β] [TopologicalRing β]
  (f : α →+* β) (hf : Continuous f)

/- Start of proof attempt -/
lemma round1_mapRingHom_apply {α : Type*} [Ring α] [UniformSpace α] [TopologicalRing α] [UniformAddGroup α]
  {β : Type*} [UniformSpace β] [Ring β] [UniformAddGroup β] [TopologicalRing β]
  (f : α →+* β) (hf : Continuous f) {x : UniformSpace.Completion α} :
  UniformSpace.Completion.mapRingHom f hf x = UniformSpace.Completion.map f x := by
  rfl

theorem mapRingHom_apply {x : UniformSpace.Completion α} :
    UniformSpace.Completion.mapRingHom f hf x = UniformSpace.Completion.map f x  := by

  exact round1_mapRingHom_apply f hf
