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
lemma TransitiveEuclideanFrameClass.is_geach : TransitiveEuclideanFrameClass.IsGeach ([⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩]) := by
  simp only [FrameClass.IsGeach, TransitiveEuclideanFrameClass,
    GeachConfluent.transitive_def, GeachConfluent.euclidean_def,
    MultiGeachConfluentFrameClass, MultiGeachConfluent];

/-- Frame class of `Hilbert.KB4` -/
abbrev SymmetricTransitiveFrameClass : FrameClass := { F | Symmetric F ∧ Transitive F }
lemma SymmetricTransitiveFrameClass.is_geach : SymmetricTransitiveFrameClass.IsGeach ([⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩]) := by
  simp only [FrameClass.IsGeach, SymmetricTransitiveFrameClass,
    GeachConfluent.symmetric_def, GeachConfluent.transitive_def,
    MultiGeachConfluentFrameClass, MultiGeachConfluent];

/-- Frame class of `Hilbert.KB5` -/
abbrev SymmetricEuclideanFrameClass : FrameClass := { F | Symmetric F ∧ Euclidean F }

/- Start of proof attempt -/
lemma round1_h1 :
  GeachConfluentFrameClass (⟨0, 1, 0, 1⟩) = { F : Frame | Symmetric F.Rel } := by
  ext F
  simp [GeachConfluentFrameClass, GeachConfluent.symmetric_def]
  <;> aesop

lemma round1_h2 :
  GeachConfluentFrameClass (⟨1, 1, 0, 1⟩) = { F : Frame | Euclidean F.Rel } := by
  ext F
  simp [GeachConfluentFrameClass, GeachConfluent.euclidean_def]
  <;> aesop

lemma round1_h3 :
  MultiGeachConfluentFrameClass [⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩] =
    GeachConfluentFrameClass (⟨0, 1, 0, 1⟩) ∩ GeachConfluentFrameClass (⟨1, 1, 0, 1⟩) := by
  have h31 : MultiGeachConfluentFrameClass (⟨0, 1, 0, 1⟩ :: [⟨1, 1, 0, 1⟩]) =
      GeachConfluentFrameClass (⟨0, 1, 0, 1⟩) ∩ MultiGeachConfluentFrameClass [⟨1, 1, 0, 1⟩] := by
    apply MultiGeachConfluentFrameClass.def_cons
    simp
  have h32 : MultiGeachConfluentFrameClass [⟨1, 1, 0, 1⟩] = GeachConfluentFrameClass (⟨1, 1, 0, 1⟩) := by
    rw [MultiGeachConfluentFrameClass.def_one]
  have h33 : MultiGeachConfluentFrameClass [⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩] = MultiGeachConfluentFrameClass (⟨0, 1, 0, 1⟩ :: [⟨1, 1, 0, 1⟩]) := by simp
  rw [h33, h31, h32]
  <;> aesop

lemma round1_h4 (h1 : GeachConfluentFrameClass (⟨0, 1, 0, 1⟩) = { F : Frame | Symmetric F.Rel })
  (h2 : GeachConfluentFrameClass (⟨1, 1, 0, 1⟩) = { F : Frame | Euclidean F.Rel })
  (h3 : MultiGeachConfluentFrameClass [⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩] =
    GeachConfluentFrameClass (⟨0, 1, 0, 1⟩) ∩ GeachConfluentFrameClass (⟨1, 1, 0, 1⟩)):
  MultiGeachConfluentFrameClass [⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩] = { F : Frame | Symmetric F.Rel ∧ Euclidean F.Rel } := by
  rw [h3, h1, h2]
  ext F
  simp
  <;> aesop

lemma round1_h5 :
  SymmetricEuclideanFrameClass = { F : Frame | Symmetric F.Rel ∧ Euclidean F.Rel } := by
  rfl

lemma round1_h6 (h1 : GeachConfluentFrameClass (⟨0, 1, 0, 1⟩) = { F : Frame | Symmetric F.Rel })
  (h2 : GeachConfluentFrameClass (⟨1, 1, 0, 1⟩) = { F : Frame | Euclidean F.Rel })
  (h3 : MultiGeachConfluentFrameClass [⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩] =
    GeachConfluentFrameClass (⟨0, 1, 0, 1⟩) ∩ GeachConfluentFrameClass (⟨1, 1, 0, 1⟩))
  (h4 : MultiGeachConfluentFrameClass [⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩] = { F : Frame | Symmetric F.Rel ∧ Euclidean F.Rel })
  (h5 : SymmetricEuclideanFrameClass = { F : Frame | Symmetric F.Rel ∧ Euclidean F.Rel }):
  SymmetricEuclideanFrameClass = MultiGeachConfluentFrameClass [⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩] := by
  rw [h4, h5]

theorem SymmetricEuclideanFrameClass.is_geach : SymmetricEuclideanFrameClass.IsGeach ([⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩])  := by

  have h1 : GeachConfluentFrameClass (⟨0, 1, 0, 1⟩) = { F : Frame | Symmetric F.Rel } := by
    exact round1_h1
  have h2 : GeachConfluentFrameClass (⟨1, 1, 0, 1⟩) = { F : Frame | Euclidean F.Rel } := by
    exact round1_h2
  have h3 : MultiGeachConfluentFrameClass [⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩] =
      GeachConfluentFrameClass (⟨0, 1, 0, 1⟩) ∩ GeachConfluentFrameClass (⟨1, 1, 0, 1⟩) := by
    exact round1_h3
  have h4 : MultiGeachConfluentFrameClass [⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩] = { F : Frame | Symmetric F.Rel ∧ Euclidean F.Rel } := by
    exact round1_h4 h1 h2 h3
  have h5 : SymmetricEuclideanFrameClass = { F : Frame | Symmetric F.Rel ∧ Euclidean F.Rel } := by
    exact round1_h5
  have h6 : SymmetricEuclideanFrameClass = MultiGeachConfluentFrameClass [⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩] := by
    exact round1_h6 h1 h2 h3 h4 h5
  simp only [FrameClass.IsGeach]
  exact h6
