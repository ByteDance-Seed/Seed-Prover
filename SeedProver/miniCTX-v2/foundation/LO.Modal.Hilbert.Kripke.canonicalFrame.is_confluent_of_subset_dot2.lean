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
lemma SymmetricEuclideanFrameClass.is_geach : SymmetricEuclideanFrameClass.IsGeach ([⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩]) := by
  simp only [FrameClass.IsGeach, SymmetricEuclideanFrameClass,
    GeachConfluent.symmetric_def, GeachConfluent.euclidean_def,
    MultiGeachConfluentFrameClass, MultiGeachConfluent];

/-- Frame class of `Hilbert.KDB` -/
abbrev SerialSymmetricFrameClass : FrameClass := { F | Serial F ∧ Symmetric F }
lemma SerialSymmetricFrameClass.is_geach : SerialSymmetricFrameClass.IsGeach ([⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 1⟩]) := by
  simp only [FrameClass.IsGeach, SerialSymmetricFrameClass,
    GeachConfluent.serial_def, GeachConfluent.symmetric_def,
    MultiGeachConfluentFrameClass, MultiGeachConfluent];

/-- Frame class of `Hilbert.KD4` -/
abbrev SerialTransitiveFrameClass : FrameClass := { F | Serial F ∧ Transitive F }
lemma SerialTransitiveFrameClass.is_geach : SerialTransitiveFrameClass.IsGeach ([⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩]) := by
  simp only [FrameClass.IsGeach, SerialTransitiveFrameClass,
    GeachConfluent.serial_def, GeachConfluent.transitive_def,
    MultiGeachConfluentFrameClass, MultiGeachConfluent]

/-- Frame class of `Hilbert.KD5` -/
abbrev SerialEuclideanFrameClass : FrameClass := { F | Serial F ∧ Euclidean F }
lemma SerialEuclideanFrameClass.is_geach : SerialEuclideanFrameClass.IsGeach ([⟨0, 0, 1, 1⟩, ⟨1, 1, 0, 1⟩]) := by
  simp only [FrameClass.IsGeach, SerialEuclideanFrameClass,
    GeachConfluent.serial_def, GeachConfluent.euclidean_def,
    MultiGeachConfluentFrameClass, MultiGeachConfluent];

end

section definability

open Kripke
open Formula
open Formula.Kripke (Satisfies)
open Formula.Kripke.Satisfies

lemma GeachConfluentFrameClass.isDefinedBy {t : GeachConfluent.Taple} : (GeachConfluentFrameClass t).DefinedBy 𝗴𝗲(t) := by
  intro F;
  constructor;
  . intro hG;
    simp [GeachConfluentFrameClass];
    intro φ V x him;
    apply Satisfies.multibox_def.mpr;
    intro z Rxz;
    apply Satisfies.multidia_def.mpr;
    obtain ⟨y, Rxy, hbp⟩ := multidia_def.mp him;
    obtain ⟨u, Ryu, Rzu⟩ := hG ⟨Rxy, Rxz⟩;
    use u;
    constructor;
    . assumption;
    . exact (Satisfies.multibox_def.mp hbp) Ryu;
  . rintro h x y z ⟨hi, hj⟩;
    simp [Kripke.ValidOnFrame] at h;
    let M : Model := ⟨F, λ v _ => y ≺^[t.m] v ⟩;
    have him_x : Satisfies M x (◇^[t.i](□^[t.m](atom 0))) := by
      apply Satisfies.multidia_def.mpr;
      use y;
      constructor;
      . exact hi;
      . apply Satisfies.multibox_def.mpr; aesop;
    have hjn_x : Kripke.Satisfies M x (□^[t.j](◇^[t.n](atom 0))) := Satisfies.imp_def.mp (h (atom 0) M.Val x) him_x;
    have hn_z : Kripke.Satisfies M z (◇^[t.n](atom 0)) := Satisfies.multibox_def.mp hjn_x hj;
    obtain ⟨u, hzu, hyu⟩ := Kripke.Satisfies.multidia_def.mp hn_z;
    use u;
    exact ⟨hyu, hzu⟩;

lemma MultiGeachConfluentFrameClass.isDefinedBy {ts : List GeachConfluent.Taple} : (MultiGeachConfluentFrameClass ts).DefinedBy 𝗚𝗲(ts) := by
  intro F;
  induction ts using List.induction_with_singleton with
  | hnil => simp [MultiGeachConfluentFrameClass];
  | hsingle t =>
    simp only [MultiGeachConfluentFrameClass.def_one, Axioms.MultiGeach.def_one];
    apply GeachConfluentFrameClass.isDefinedBy;
  | hcons t ts ts_nil ih =>
    simp [MultiGeachConfluentFrameClass.def_cons (ts_nil := ts_nil)];
    constructor;
    . rintro ⟨ht, hts⟩;
      constructor;
      . intro φ
        apply Semantics.realizeSet_iff.mp $ @GeachConfluentFrameClass.isDefinedBy (t := t) F |>.mp ht
        tauto;
      . apply ih.mp;
        exact hts;
    . rintro ⟨ht, hts⟩;
      constructor;
      . apply @GeachConfluentFrameClass.isDefinedBy t F |>.mpr;
        apply Semantics.realizeSet_iff.mpr;
        simpa using ht;
      . apply ih.mpr hts;

lemma ReflexiveFrameClass.isDefinedBy : (ReflexiveFrameClass).DefinedBy 𝗧 := by
  rw [ReflexiveFrameClass.is_geach, Axioms.T.is_geach];
  apply GeachConfluentFrameClass.isDefinedBy;

lemma SerialFrameClass.isDefinedBy : (SerialFrameClass).DefinedBy 𝗗 := by
  rw [SerialFrameClass.is_geach, Axioms.D.is_geach];
  apply GeachConfluentFrameClass.isDefinedBy;

lemma TransitiveFrameClass.isDefinedBy : (TransitiveFrameClass).DefinedBy 𝟰 := by
  rw [TransitiveFrameClass.is_geach, Axioms.Four.is_geach];
  apply GeachConfluentFrameClass.isDefinedBy;

end definability

end Kripke

namespace Hilbert

open Modal.Kripke

namespace Kripke

open System
open Theory MaximalConsistentTheory
open canonicalFrame

namespace canonicalFrame

variable {Ax : Theory ℕ} [(Hilbert.ExtK Ax).Consistent]

lemma is_geachConfluent_of_subset_Geach (h : 𝗴𝗲(t) ⊆ Ax) : GeachConfluent t (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
  rintro Ω₁ Ω₂ Ω₃ h;
  have ⟨r₁₂, r₁₃⟩ := h; clear h;
  have ⟨Ω, hΩ⟩ := lindenbaum (H := (Hilbert.ExtK Ax)) (T := □''⁻¹^[t.m]Ω₂.theory ∪ □''⁻¹^[t.n]Ω₃.theory) $ by
    apply intro_union_consistent;
    rintro Γ Δ ⟨hΓ, hΔ⟩ hC;

    replace hΓ : ∀ φ ∈ Γ, □^[t.m]φ ∈ Ω₂.theory := by simpa using hΓ;
    have hΓconj : □^[t.m]⋀Γ ∈ Ω₂.theory := iff_mem_multibox_conj.mpr hΓ;

    replace hΔ : ∀ φ ∈ Δ, □^[t.n]φ ∈ Ω₃.theory := by simpa using hΔ;
    have : □^[t.n]⋀Δ ∈ Ω₃.theory := iff_mem_multibox_conj.mpr hΔ;

    have : □^[t.j](◇^[t.n]⋀Γ) ∈ Ω₁.theory := iff_mem_imp.mp
      (membership_iff.mpr $ Context.of! $ Hilbert.ExtK.maxm! (by aesop))
      (multirel_def_multidia.mp r₁₂ hΓconj)
    have : ◇^[t.n]⋀Γ ∈ Ω₃.theory := multirel_def_multibox.mp r₁₃ this;

    have : (Hilbert.ExtK Ax) ⊢! □^[t.n]⋀Δ ⋏ ◇^[t.n]⋀Γ ➝ ⊥ := by {
      apply and_imply_iff_imply_imply'!.mpr;
      exact imp_trans''!
        (show _ ⊢! □^[t.n]⋀Δ ➝ □^[t.n](∼⋀Γ) by exact imply_multibox_distribute'! $ contra₁'! $ imp_trans''! (and_imply_iff_imply_imply'!.mp hC) (and₂'! neg_equiv!))
        (show _ ⊢! □^[t.n](∼⋀Γ) ➝ (◇^[t.n]⋀Γ) ➝ ⊥ by exact imp_trans''! (contra₁'! $ and₁'! $ multidia_duality!) (and₁'! neg_equiv!));
    }
    have : (Hilbert.ExtK Ax) ⊬ □^[t.n]⋀Δ ⋏ ◇^[t.n]⋀Γ ➝ ⊥ := by simpa using (def_consistent.mp Ω₃.consistent) (Γ := [□^[t.n]⋀Δ, ◇^[t.n]⋀Γ]) (by simp_all)

    contradiction;

  use Ω; simp only [Set.union_subset_iff] at hΩ;
  constructor;
  . apply multirel_def_multibox.mpr; apply hΩ.1;
  . apply multirel_def_multibox.mpr; apply hΩ.2;

lemma is_multiGeachConfluent_of_subset_MultiGeach (h : 𝗚𝗲(ts) ⊆ Ax) : MultiGeachConfluent ts (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
  induction ts using List.induction_with_singleton with
  | hnil => simp [MultiGeachConfluent];
  | hsingle t =>
    simp [MultiGeachConfluent.iff_singleton] at h;
    exact is_geachConfluent_of_subset_Geach h;
  | hcons t ts ts_nil ih =>
    simp [(MultiGeachConfluent.iff_cons ts_nil)];
    constructor;
    . apply is_geachConfluent_of_subset_Geach; simp_all;
    . apply ih; simp_all;

lemma is_reflexive_of_subset_T (h : 𝗧 ⊆ Ax) : Reflexive (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
  rw [GeachConfluent.reflexive_def, Axioms.T.is_geach] at *
  apply is_geachConfluent_of_subset_Geach;
  exact h;

lemma is_serial_of_subset_D (h : 𝗗 ⊆ Ax) : Serial (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
  rw [GeachConfluent.serial_def, Axioms.D.is_geach] at *
  apply is_geachConfluent_of_subset_Geach;
  exact h;

lemma is_transitive_of_subset_Four (h : 𝟰 ⊆ Ax) : Transitive (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
  rw [GeachConfluent.transitive_def, Axioms.Four.is_geach] at *
  apply is_geachConfluent_of_subset_Geach;
  exact h;

lemma is_euclidean_of_subset_Five (h : 𝟱 ⊆ Ax) : Euclidean (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
  rw [GeachConfluent.euclidean_def, Axioms.Five.is_geach] at *
  apply is_geachConfluent_of_subset_Geach;
  exact h;

lemma is_symmetric_of_subset_B (h : 𝗕 ⊆ Ax) : Symmetric (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
  rw [GeachConfluent.symmetric_def, Axioms.B.is_geach] at *
  apply is_geachConfluent_of_subset_Geach;
  exact h;

/- Start of proof attempt -/
lemma round1_h3 :
  (MultiGeachConfluent [⟨1, 1, 1, 1⟩] (canonicalFrame (Hilbert.ExtK Ax)).Rel) ↔ (GeachConfluent ⟨1, 1, 1, 1⟩ (canonicalFrame (Hilbert.ExtK Ax)).Rel) := by
  have h31 : MultiGeachConfluentFrameClass [⟨1, 1, 1, 1⟩] = GeachConfluentFrameClass ⟨1, 1, 1, 1⟩ := by
    exact MultiGeachConfluentFrameClass.def_one (⟨1, 1, 1, 1⟩ : GeachConfluent.Taple)
  have h32 : ∀ (F : Frame), (F ∈ MultiGeachConfluentFrameClass [⟨1, 1, 1, 1⟩]) ↔ (F ∈ GeachConfluentFrameClass ⟨1, 1, 1, 1⟩) := by
    intro F
    rw [h31]
    <;> simp
  have h33 := h32 (canonicalFrame (Hilbert.ExtK Ax))
  simpa [MultiGeachConfluentFrameClass, GeachConfluentFrameClass] using h33

lemma round1_h7 (h2 : MultiGeachConfluent [⟨1, 1, 1, 1⟩] (canonicalFrame (Hilbert.ExtK Ax)).Rel)
  (h3 : (MultiGeachConfluent [⟨1, 1, 1, 1⟩] (canonicalFrame (Hilbert.ExtK Ax)).Rel) ↔ (GeachConfluent ⟨1, 1, 1, 1⟩ (canonicalFrame (Hilbert.ExtK Ax)).Rel)):
  GeachConfluent ⟨1, 1, 1, 1⟩ (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
  exact h3.mp h2

theorem is_confluent_of_subset_dot2 (h : .𝟮 ⊆ Ax) : Confluent (canonicalFrame (Hilbert.ExtK Ax)).Rel  := by

  have h1 : 𝗚𝗲([⟨1, 1, 1, 1⟩]) ⊆ Ax := by simpa using h
  have h2 : MultiGeachConfluent [⟨1, 1, 1, 1⟩] (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
    exact canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach h1
  have h3 : (MultiGeachConfluent [⟨1, 1, 1, 1⟩] (canonicalFrame (Hilbert.ExtK Ax)).Rel) ↔ (GeachConfluent ⟨1, 1, 1, 1⟩ (canonicalFrame (Hilbert.ExtK Ax)).Rel) := by
    exact round1_h3 
  have h7 : GeachConfluent ⟨1, 1, 1, 1⟩ (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
    exact round1_h7 h2 h3
  have h10 : Confluent (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
    rw [GeachConfluent.confluent_def]
    exact h7
  exact h10
