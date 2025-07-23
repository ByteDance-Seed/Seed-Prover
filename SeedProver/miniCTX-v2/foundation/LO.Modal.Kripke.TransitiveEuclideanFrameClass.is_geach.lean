-- In foundation/Foundation/Modal/Kripke/Geach/Basic.lean

import Foundation.Vorspiel.BinaryRelations
import Foundation.Modal.Kripke.Completeness
import Foundation.Modal.Hilbert.Geach

namespace LO.Modal

namespace Kripke

abbrev GeachConfluentFrameClass (t : GeachConfluent.Taple) : FrameClass := { F | (GeachConfluent t) F.Rel }

instance GeachConfluentFrameClass.nonempty : (GeachConfluentFrameClass t).Nonempty := by
  use reflexivePointFrame.toFrame;
  intros x _ _ _; use x;
  constructor <;> { apply Rel.iterate.true_any; tauto; }

abbrev MultiGeachConfluentFrameClass (ts : List GeachConfluent.Taple) : FrameClass := { F | (MultiGeachConfluent ts) F.Rel }

namespace MultiGeachConfluentFrameClass

@[simp] lemma def_nil : MultiGeachConfluentFrameClass [] = AllFrameClass := by rfl;

lemma def_one (t : GeachConfluent.Taple) : MultiGeachConfluentFrameClass [t] = GeachConfluentFrameClass t := by rfl;

lemma def_cons {t : GeachConfluent.Taple} {ts : List GeachConfluent.Taple} (ts_nil : ts ≠ [])
  : MultiGeachConfluentFrameClass (t :: ts) = GeachConfluentFrameClass t ∩ MultiGeachConfluentFrameClass ts := by
  apply Set.eq_of_subset_of_subset;
  . rintro F hF;
    apply MultiGeachConfluent.iff_cons ts_nil |>.mp;
    exact hF;
  . rintro F ⟨hF₁, hF₂⟩;
    apply MultiGeachConfluent.iff_cons ts_nil |>.mpr;
    constructor;
    . apply hF₁;
    . apply hF₂;

@[simp]
instance nonempty : (MultiGeachConfluentFrameClass ts).Nonempty := by
  use ⟨PUnit,  λ _ _ => True⟩;
  induction ts using List.induction_with_singleton with
  | hnil => simp only [def_nil, Set.mem_univ];
  | hsingle t =>
    simp [GeachConfluentFrameClass];
    intros x _ _ _; use x;
    constructor <;> { apply Rel.iterate.true_any; tauto; }
  | hcons t ts ts_nil ih =>
    simp [MultiGeachConfluentFrameClass.def_cons ts_nil];
    constructor;
    . intro x _ _ _; use x;
      constructor <;> { apply Rel.iterate.true_any; tauto; }
    . exact ih;

end MultiGeachConfluentFrameClass

abbrev FrameClass.IsGeach (C : FrameClass) (ts : List GeachConfluent.Taple) := C = MultiGeachConfluentFrameClass ts

section

/-- Frame class of `Hilbert.KT` -/
abbrev ReflexiveFrameClass : FrameClass := { F | Reflexive F.Rel }
lemma ReflexiveFrameClass.is_geach : ReflexiveFrameClass.IsGeach [⟨0, 0, 1, 0⟩] := by
  simp only [FrameClass.IsGeach, ReflexiveFrameClass, GeachConfluent.reflexive_def,
    MultiGeachConfluentFrameClass.def_one, GeachConfluentFrameClass];

/-- Frame class of `Hilbert.KD` -/
abbrev SerialFrameClass : FrameClass := { F | Serial F.Rel }
lemma SerialFrameClass.is_geach : SerialFrameClass.IsGeach [⟨0, 0, 1, 1⟩] := by
  simp only [FrameClass.IsGeach, SerialFrameClass, GeachConfluent.serial_def,
    MultiGeachConfluentFrameClass.def_one, GeachConfluentFrameClass];

/-- Frame class of `Hilbert.KB` -/
abbrev SymmetricFrameClass : FrameClass := { F | Symmetric F.Rel }
lemma SymmetricFrameClass.is_geach : SymmetricFrameClass.IsGeach [⟨0, 1, 0, 1⟩] := by
  simp only [FrameClass.IsGeach, SymmetricFrameClass, GeachConfluent.symmetric_def,
    MultiGeachConfluentFrameClass.def_one, GeachConfluentFrameClass];

/-- Frame class of `Hilbert.K4` -/
abbrev TransitiveFrameClass : FrameClass := { F | Transitive F.Rel }
lemma TransitiveFrameClass.is_geach : TransitiveFrameClass.IsGeach ([⟨0, 2, 1, 0⟩]) := by
  simp only [FrameClass.IsGeach, TransitiveFrameClass, GeachConfluent.transitive_def,
    MultiGeachConfluentFrameClass.def_one, GeachConfluentFrameClass];

/-- Frame class of `Hilbert.K5` -/
abbrev EuclideanFrameClass : FrameClass := { F | Euclidean F.Rel }
lemma EuclideanFrameClass.is_geach : EuclideanFrameClass.IsGeach ([⟨1, 1, 0, 1⟩]) := by
  simp only [FrameClass.IsGeach, EuclideanFrameClass, GeachConfluent.euclidean_def,
    MultiGeachConfluentFrameClass, MultiGeachConfluent];

/-- Frame class of `Hilbert.S5` -/
abbrev ReflexiveEuclideanFrameClass : FrameClass := { F | Reflexive F.Rel ∧ Euclidean F.Rel }
lemma ReflexiveEuclideanFrameClass.is_geach : ReflexiveEuclideanFrameClass.IsGeach ([⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩]) := by
  simp only [FrameClass.IsGeach, ReflexiveEuclideanFrameClass, GeachConfluent.reflexive_def,
    GeachConfluent.euclidean_def, MultiGeachConfluentFrameClass, MultiGeachConfluent];

/-- Frame class of `Hilbert.KTB` -/
abbrev ReflexiveSymmetricFrameClass : FrameClass := { F | Reflexive F ∧ Symmetric F }
lemma ReflexiveSymmetricFrameClass.is_geach : ReflexiveSymmetricFrameClass.IsGeach ([⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩]) := by
  simp only [FrameClass.IsGeach, ReflexiveSymmetricFrameClass, GeachConfluent.reflexive_def,
    GeachConfluent.symmetric_def, MultiGeachConfluentFrameClass, MultiGeachConfluent];

/-- Frame class of `Hilbert.S4` -/
abbrev ReflexiveTransitiveFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F }
lemma ReflexiveTransitiveFrameClass.is_geach : ReflexiveTransitiveFrameClass.IsGeach ([⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩]) := by
  simp only [FrameClass.IsGeach, ReflexiveTransitiveFrameClass, GeachConfluent.reflexive_def,
    GeachConfluent.transitive_def, MultiGeachConfluentFrameClass, MultiGeachConfluent];

/-- Frame class of `Hilbert.S4Dot2` -/
abbrev ReflexiveTransitiveConfluentFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Confluent F }
lemma ReflexiveTransitiveConfluentFrameClass.is_geach : ReflexiveTransitiveConfluentFrameClass.IsGeach ([⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩]) := by
  simp only [FrameClass.IsGeach, ReflexiveTransitiveConfluentFrameClass,
    GeachConfluent.reflexive_def, GeachConfluent.transitive_def, GeachConfluent.confluent_def,
    MultiGeachConfluentFrameClass, MultiGeachConfluent];

/-- Frame class of `Hilbert.KT4B` -/
abbrev ReflexiveTransitiveSymmetricFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Symmetric F }
lemma ReflexiveTransitiveSymmetricFrameClass.is_geach : ReflexiveTransitiveSymmetricFrameClass.IsGeach ([⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩]) := by
  simp only [FrameClass.IsGeach, ReflexiveTransitiveSymmetricFrameClass,
    GeachConfluent.reflexive_def, GeachConfluent.transitive_def, GeachConfluent.symmetric_def,
    MultiGeachConfluentFrameClass, MultiGeachConfluent];

/-- Frame class of `Hilbert.KD45` -/
abbrev SerialTransitiveEuclideanFrameClass : FrameClass := { F | Serial F ∧ Transitive F ∧ Euclidean F }
lemma SerialTransitiveEuclideanFrameClass.is_geach : SerialTransitiveEuclideanFrameClass.IsGeach ([⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩]) := by
  simp only [FrameClass.IsGeach, SerialTransitiveEuclideanFrameClass,
    GeachConfluent.serial_def, GeachConfluent.transitive_def, GeachConfluent.euclidean_def,
    MultiGeachConfluentFrameClass, MultiGeachConfluent];

/-- Frame class of `Hilbert.K45` -/
abbrev TransitiveEuclideanFrameClass : FrameClass := { F | Transitive F ∧ Euclidean F }

/- Start of proof attempt -/
lemma round1_TransitiveEuclideanFrameClass_is_geach : TransitiveEuclideanFrameClass.IsGeach ([⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩]) := by
  simp only [FrameClass.IsGeach, TransitiveEuclideanFrameClass, Set.ext_iff, MultiGeachConfluentFrameClass, MultiGeachConfluent, GeachConfluent.transitive_def, GeachConfluent.euclidean_def]
  <;> aesop

theorem TransitiveEuclideanFrameClass.is_geach : TransitiveEuclideanFrameClass.IsGeach ([⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩])  := by

  exact round1_TransitiveEuclideanFrameClass_is_geach
