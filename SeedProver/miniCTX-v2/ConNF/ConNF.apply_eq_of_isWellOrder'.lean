-- In ConNF/ConNF/External/WellOrder.lean

import ConNF.External.Basic

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal ConNF.TSet

namespace ConNF

variable [Params.{u}] {α β γ δ ε ζ : Λ} (hβ : (β : TypeIndex) < α) (hγ : (γ : TypeIndex) < β)
  (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < δ) (hζ : (ζ : TypeIndex) < ε)

/-- A set in our model that is a well-order. Internal well-orders are exactly external well-orders,
so we externalise the definition for convenience. -/
def InternalWellOrder (r : TSet α) : Prop :=
  IsWellOrder (ExternalRel hβ hγ hδ r).field
    (InvImage (ExternalRel hβ hγ hδ r) Subtype.val)

def InternallyWellOrdered (x : TSet γ) : Prop :=
  {y : TSet δ | y ∈' x}.Subsingleton ∨ (∃ r, InternalWellOrder hβ hγ hδ r ∧ x = field hβ hγ hδ r)

@[simp]
theorem externalRel_smul (r : TSet α) (ρ : AllPerm α) :
    ExternalRel hβ hγ hδ (ρ • r) =
      InvImage (ExternalRel hβ hγ hδ r) ((ρ ↘ hβ ↘ hγ ↘ hδ)⁻¹ • ·) := by
  ext a b
  simp only [ExternalRel, mem_smul_iff', allPerm_inv_sderiv', smul_op, InvImage]

omit [Params] in
/-- Well-orders are rigid. -/
theorem apply_eq_of_isWellOrder {X : Type _} {r : Rel X X} {f : X → X}
    (hr : IsWellOrder X r) (hf : Function.Bijective f) (hf' : ∀ x y, r x y ↔ r (f x) (f y)) :
    ∀ x, f x = x := by
  let emb : r ≼i r := ⟨⟨⟨f, hf.injective⟩, λ {a b} ↦ (hf' a b).symm⟩, ?_⟩
  · have : emb = InitialSeg.refl r := Subsingleton.elim _ _
    intro x
    exact congr_arg (λ f ↦ f x) this
  · intro a b h
    exact hf.surjective _

omit [Params] in

/- Start of proof attempt -/
lemma round1_h11 {X : Type _} {r : Rel X X} {f : X → X} (hf : Function.Bijective f)
  (hf' : ∀ x y, r x y ↔ r (f x) (f y)) :
  ∀ z : X, z ∈ r.field → f z ∈ r.field := by
  intro z hz
  rcases hz with (h111 | h112)
  · -- Case 1: z ∈ r.dom
    have h1111 : ∃ w, r z w := h111
    rcases h1111 with ⟨w, h1112⟩
    have h1113 : r (f z) (f w) := by
      have h1114 : r z w := h1112
      have h1115 : r z w ↔ r (f z) (f w) := hf' z w
      tauto
    have h1116 : ∃ w', r (f z) w' := ⟨f w, h1113⟩
    have h1117 : f z ∈ r.dom := h1116
    have h1118 : f z ∈ r.field := Or.inl h1117
    tauto
  · -- Case 2: z ∈ r.codom
    have h1121 : ∃ w, r w z := h112
    rcases h1121 with ⟨w, h1122⟩
    have h1123 : r (f w) (f z) := by
      have h1124 : r w z := h1122
      have h1125 : r w z ↔ r (f w) (f z) := hf' w z
      tauto
    have h1126 : ∃ w', r w' (f z) := ⟨f w, h1123⟩
    have h1127 : f z ∈ r.codom := h1126
    have h1128 : f z ∈ r.field := Or.inr h1127
    tauto

lemma round1_h12 {X : Type _} {r : Rel X X} {f : X → X} (hf : Function.Bijective f)
  (hf' : ∀ x y, r x y ↔ r (f x) (f y)) :
  ∀ z : X, f z ∈ r.field → z ∈ r.field := by
  intro z hfz
  rcases hfz with (h121 | h122)
  · -- Case 1: f z ∈ r.dom
    have h1211 : ∃ w, r (f z) w := h121
    rcases h1211 with ⟨w, h1212⟩
    have h1213 : ∃ w', f w' = w := hf.surjective w
    rcases h1213 with ⟨w', hw'⟩
    have h1214 : r (f z) (f w') := by
      rw [← hw'] at h1212
      tauto
    have h1215 : r z w' := by
      have h1216 : r z w' ↔ r (f z) (f w') := hf' z w'
      tauto
    have h1216 : ∃ w', r z w' := ⟨w', h1215⟩
    have h1217 : z ∈ r.dom := h1216
    have h1218 : z ∈ r.field := Or.inl h1217
    tauto
  · -- Case 2: f z ∈ r.codom
    have h1221 : ∃ w, r w (f z) := h122
    rcases h1221 with ⟨w, h1222⟩
    have h1223 : ∃ w', f w' = w := hf.surjective w
    rcases h1223 with ⟨w', hw'⟩
    have h1224 : r (f w') (f z) := by
      rw [← hw'] at h1222
      tauto
    have h1225 : r w' z := by
      have h1226 : r w' z ↔ r (f w') (f z) := hf' w' z
      tauto
    have h1226 : ∃ w', r w' z := ⟨w', h1225⟩
    have h1227 : z ∈ r.codom := h1226
    have h1228 : z ∈ r.field := Or.inr h1227
    tauto

lemma round1_g_inj {X : Type _} {r : Rel X X} {f : X → X} (hf : Function.Bijective f)
  (h11 : ∀ z : X, z ∈ r.field → f z ∈ r.field) :
  Function.Injective (fun (a : r.field) => (⟨f a.val, h11 a.val a.property⟩ : r.field)) := by
  intro a b h
  have h14 : ((⟨f a.val, h11 a.val a.property⟩ : r.field)).val = ((⟨f b.val, h11 b.val b.property⟩ : r.field)).val := by
    exact congr_arg Subtype.val h
  have h15 : f a.val = f b.val := by simpa using h14
  have h16 : a.val = b.val := by
    have h17 : Function.Injective f := hf.injective
    exact h17 h15
  have h18 : a = b := by
    apply Subtype.ext
    exact h16
  exact h18

lemma round1_g_surj {X : Type _} {r : Rel X X} {f : X → X} (hf : Function.Bijective f)
  (h11 : ∀ z : X, z ∈ r.field → f z ∈ r.field)
  (h12 : ∀ z : X, f z ∈ r.field → z ∈ r.field) :
  Function.Surjective (fun (a : r.field) => (⟨f a.val, h11 a.val a.property⟩ : r.field)) := by
  intro y
  have h4 : ∃ x : X, f x = y.val := hf.surjective y.val
  rcases h4 with ⟨x, hx⟩
  have hy1 : y.val ∈ r.field := y.property
  have hfx_in_field : f x ∈ r.field := by
    rw [hx]
    exact hy1
  have hx_in_field : x ∈ r.field := h12 x hfx_in_field
  have h20 : ∃ (a : r.field), a.val = x := ⟨⟨x, hx_in_field⟩, rfl⟩
  rcases h20 with ⟨a, ha⟩
  refine ⟨a,?_⟩
  simp [ha, hx]
  <;> aesop

lemma round1_h2 {X : Type _} {r : Rel X X} {f : X → X} (hf' : ∀ x y, r x y ↔ r (f x) (f y))
  (h11 : ∀ z : X, z ∈ r.field → f z ∈ r.field) :
  ∀ (a b : r.field), (InvImage r Subtype.val) a b ↔ (InvImage r Subtype.val) (⟨f a.val, h11 a.val a.property⟩ : r.field) (⟨f b.val, h11 b.val b.property⟩ : r.field) := by
  intro a b
  simp only [InvImage]
  have h21 : r a.val b.val ↔ r (f a.val) (f b.val) := by
    exact hf' a.val b.val
  tauto

theorem apply_eq_of_isWellOrder' {X : Type _} {r : Rel X X} {f : X → X}
    (hr : IsWellOrder r.field (InvImage r Subtype.val)) (hf : Function.Bijective f)
    (hf' : ∀ x y, r x y ↔ r (f x) (f y)) :
    ∀ x ∈ r.field, f x = x  := by

  have h11 : ∀ z : X, z ∈ r.field → f z ∈ r.field := by
    exact round1_h11 hf hf'
  
  have h12 : ∀ z : X, f z ∈ r.field → z ∈ r.field := by
    exact round1_h12 hf hf'
  
  have g_inj : Function.Injective (fun (a : r.field) => (⟨f a.val, h11 a.val a.property⟩ : r.field)) := by
    exact round1_g_inj hf h11
  
  have g_surj : Function.Surjective (fun (a : r.field) => (⟨f a.val, h11 a.val a.property⟩ : r.field)) := by
    exact round1_g_surj hf h11 h12
  
  have hg_bij : Function.Bijective (fun (a : r.field) => (⟨f a.val, h11 a.val a.property⟩ : r.field)) := ⟨g_inj, g_surj⟩
  
  have h2 : ∀ (a b : r.field), (InvImage r Subtype.val) a b ↔ (InvImage r Subtype.val) (⟨f a.val, h11 a.val a.property⟩ : r.field) (⟨f b.val, h11 b.val b.property⟩ : r.field) := by
    exact round1_h2 hf' h11
  
  have h3 : ∀ (a : r.field), (⟨f a.val, h11 a.val a.property⟩ : r.field) = a := by
    exact apply_eq_of_isWellOrder hr hg_bij h2
  
  intro x hx
  have h22 : ∃ (a : r.field), a.val = x := ⟨⟨x, hx⟩, rfl⟩
  rcases h22 with ⟨a, ha⟩
  have h23 := h3 a
  have h24 : (⟨f a.val, h11 a.val a.property⟩ : r.field).val = a.val := by
    have h241 : (⟨f a.val, h11 a.val a.property⟩ : r.field).val = f a.val := rfl
    have h242 : (a : r.field).val = a.val := rfl
    have h243 : (⟨f a.val, h11 a.val a.property⟩ : r.field) = a := h23
    have h244 : (⟨f a.val, h11 a.val a.property⟩ : r.field).val = (a : r.field).val := by rw [h243]
    simp [h241, h242] at h244 ⊢
    <;> tauto
  have h25 : f a.val = a.val := by
    simpa using h24
  have h26 : a.val = x := by tauto
  rw [h26] at h25
  tauto
