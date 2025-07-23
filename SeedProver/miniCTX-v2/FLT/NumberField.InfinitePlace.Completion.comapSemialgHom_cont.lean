-- In FLT/FLT/NumberField/Completion.lean

import Mathlib.NumberTheory.NumberField.Completion
import Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.Analysis.Normed.Ring.WithAbs
import FLT.Mathlib.Topology.Algebra.UniformRing
import FLT.NumberField.Embeddings

open scoped TensorProduct

/-!
# The completion of a number field at an infinite place
-/

noncomputable section

namespace NumberField.InfinitePlace.Completion

open AbsoluteValue.Completion UniformSpace.Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}

def comapSemialgHom (h : w.comap (algebraMap K L) = v) :
    v.Completion →ₛₐ[algebraMap (WithAbs v.1) (WithAbs w.1)] w.Completion :=
  mapSemialgHom _ <| (WithAbs.uniformContinuous_algebraMap (v.comp_of_comap_eq _ h)).continuous

/- Start of proof attempt -/
lemma round1_comapSemialgHom_cont (h : w.comap (algebraMap K L) = v) :
    Continuous (comapSemialgHom h) := by
  have h5 : ∀ (x : v.Completion), (comapSemialgHom h) x = UniformSpace.Completion.map (algebraMap (WithAbs v.1) (WithAbs w.1)) x := by
    intro x
    rfl
  have h6 : (comapSemialgHom h : v.Completion → w.Completion) = UniformSpace.Completion.map (algebraMap (WithAbs v.1) (WithAbs w.1)) := by
    funext x
    exact h5 x
  have h4 : Continuous (UniformSpace.Completion.map (algebraMap (WithAbs v.1) (WithAbs w.1))) := by
    apply UniformSpace.Completion.continuous_map
  rw [h6]
  exact h4

theorem comapSemialgHom_cont (h : w.comap (algebraMap K L) = v) :
    Continuous (comapSemialgHom h)  := by

  exact round1_comapSemialgHom_cont h
