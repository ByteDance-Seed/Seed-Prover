-- In FLT/FLT/Mathlib/NumberTheory/Padics/PadicIntegers.lean

import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.Padics.PadicIntegers
import FLT.Mathlib.GroupTheory.Index

/-!
# TODO

* Rename `Coe.ringHom` to `coeRingHom`
* Protect `PadicInt.norm_mul`, `PadicInt.norm_units`, `PadicInt.norm_pow`
-/

open Function Topology Subgroup
open scoped NNReal nonZeroDivisors Pointwise

variable {p : ℕ} [Fact p.Prime]

namespace PadicInt
variable {x : ℤ_[p]}

attribute [simp] coe_eq_zero

/- Start of proof attempt -/
lemma round1_coe_coeRingHom : ⇑(Coe.ringHom (p := p)) = (↑) := by
  funext x
  rfl

theorem coe_coeRingHom : ⇑(Coe.ringHom (p := p)) = (↑)  := by

  exact round1_coe_coeRingHom
