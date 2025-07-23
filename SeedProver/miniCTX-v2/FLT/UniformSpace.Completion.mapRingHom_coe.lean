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

theorem mapRingHom_apply {x : UniformSpace.Completion α} :
    UniformSpace.Completion.mapRingHom f hf x = UniformSpace.Completion.map f x := rfl

variable {f}

/- Start of proof attempt -/
lemma round1_h1 (α : Type*) [Ring α] [UniformSpace α] [TopologicalRing α] [UniformAddGroup α]
  (β : Type*) [UniformSpace β] [Ring β] [UniformAddGroup β] [TopologicalRing β]
  (f : α →+* β) (hf : UniformContinuous f) (a : α):
  (UniformSpace.Completion.mapRingHom f hf.continuous (a : UniformSpace.Completion α)) =
  (UniformSpace.Completion.map f (a : UniformSpace.Completion α)) := by
  exact?

lemma round1_h2 (α : Type*) [Ring α] [UniformSpace α] [TopologicalRing α] [UniformAddGroup α]
  (β : Type*) [UniformSpace β] [Ring β] [UniformAddGroup β] [TopologicalRing β]
  (f : α →+* β) (hf : UniformContinuous f) (a : α):
  (UniformSpace.Completion.map f (a : UniformSpace.Completion α)) = (f a : UniformSpace.Completion β) := by
  exact?

theorem mapRingHom_coe (hf : UniformContinuous f) (a : α) :
    mapRingHom f hf.continuous a = f a  := by

  have h1 := round1_h1 α β f hf a
  have h2 := round1_h2 α β f hf a
  rw [h1, h2]
  <;> simp
  <;> aesop
