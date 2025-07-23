-- In ConNF/ConNF/ModelData/Enumeration.lean

import ConNF.Background.Rel
import ConNF.Base.Small

/-!
# Enumerations

In this file, we define enumerations of a type.

## Main declarations

* `ConNF.Enumeration`: The type family of enumerations.
-/

universe u

open Cardinal

namespace ConNF

variable [Params.{u}] {X Y : Type u}

@[ext]
structure Enumeration (X : Type u) where
  bound : κ
  rel : Rel κ X
  lt_bound : ∀ i ∈ rel.dom, i < bound
  rel_coinjective : rel.Coinjective

variable {E F G : Enumeration X}

namespace Enumeration

instance : CoeTC (Enumeration X) (Set X) where
  coe E := E.rel.codom

instance : Membership X (Enumeration X) where
  mem E x := x ∈ E.rel.codom

theorem mem_iff (x : X) (E : Enumeration X) :
    x ∈ E ↔ x ∈ E.rel.codom :=
  Iff.rfl

theorem mem_congr {E F : Enumeration X} (h : E = F) :
    ∀ x, x ∈ E ↔ x ∈ F := by
  intro x
  rw [h]

theorem dom_small (E : Enumeration X) :
    Small E.rel.dom :=
  (iio_small E.bound).mono E.lt_bound

theorem coe_small (E : Enumeration X) :
    Small (E : Set X) :=
  small_codom_of_small_dom E.rel_coinjective E.dom_small

theorem graph'_small (E : Enumeration X) :
    Small E.rel.graph' :=
  small_graph' E.dom_small E.coe_small

noncomputable def empty : Enumeration X where
  bound := 0
  rel _ _ := False
  lt_bound _ h := by cases h; contradiction
  rel_coinjective := by constructor; intros; contradiction

/- Start of proof attempt -/
lemma round1_not_mem_empty (x : X) : x ∉ Enumeration.empty := by
  intro h
  have h1 : x ∈ Enumeration.empty.rel.codom := h
  rcases h1 with ⟨i, hi⟩
  <;> simp [Enumeration.empty] at hi <;> tauto

theorem not_mem_empty (x : X) : x ∉ Enumeration.empty  := by

  exact round1_not_mem_empty x
