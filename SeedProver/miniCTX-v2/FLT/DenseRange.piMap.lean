-- In FLT/FLT/Mathlib/Topology/Constructions.lean

import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn

theorem TopologicalSpace.prod_mono {α β : Type*} {σ₁ σ₂ : TopologicalSpace α}
    {τ₁ τ₂ : TopologicalSpace β} (hσ : σ₁ ≤ σ₂) (hτ : τ₁ ≤ τ₂) :
    @instTopologicalSpaceProd α β σ₁ τ₁ ≤ @instTopologicalSpaceProd α β σ₂ τ₂ :=
  le_inf (inf_le_left.trans  <| induced_mono hσ)
         (inf_le_right.trans  <| induced_mono hτ)

/- Start of proof attempt -/
lemma round1_h1 (ι : Type*) (X Y : ι → Type*) [∀ i, TopologicalSpace (Y i)]
  (f : (i : ι) → (X i) → (Y i)) (hf : ∀ i, DenseRange (f i)) :
  ∀ i : ι, closure (Set.range (f i)) = Set.univ := by
  intro i
  have h11 : Dense (Set.range (f i)) := hf i
  exact?

lemma round1_h3 (ι : Type*) (X Y : ι → Type*) [∀ i, TopologicalSpace (Y i)]
  (f : (i : ι) → (X i) → (Y i)) :
  Set.range (Pi.map f) = Set.univ.pi fun i => Set.range (f i) := by
  ext x
  simp [Set.mem_range, Set.mem_pi, Set.mem_univ]
  <;> aesop

lemma round1_h_main (ι : Type*) (X Y : ι → Type*) [∀ i, TopologicalSpace (Y i)]
  (f : (i : ι) → (X i) → (Y i)) (hf : ∀ i, DenseRange (f i)) :
  ∀ (g : (i : ι) → Y i), g ∈ closure (Set.range (Pi.map f)) := by
  have h1 : ∀ i : ι, closure (Set.range (f i)) = Set.univ := round1_h1 ι X Y f hf
  have h3 : Set.range (Pi.map f) = Set.univ.pi fun i => Set.range (f i) := round1_h3 ι X Y f
  intro g
  have h4 : ∀ i : ι, g i ∈ closure (Set.range (f i)) := by
    intro i
    have h1i : closure (Set.range (f i)) = Set.univ := h1 i
    rw [h1i]
    <;> simp
  have h5 : closure (Set.univ.pi fun i => Set.range (f i)) = Set.pi Set.univ fun i => closure (Set.range (f i)) := by
    exact?
  have h61 : g ∈ Set.pi Set.univ fun i => closure (Set.range (f i)) := by
    simpa [Set.mem_pi] using h4
  have h62 : g ∈ closure (Set.univ.pi fun i => Set.range (f i)) := by
    rw [h5]
    exact h61
  rw [h3]
  exact h62

theorem DenseRange.piMap {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {f : (i : ι) → (X i) → (Y i)} (hf : ∀ i, DenseRange (f i)):
    DenseRange (Pi.map f)  := by

  have h_main : ∀ (g : (i : ι) → Y i), g ∈ closure (Set.range (Pi.map f)) := round1_h_main ι X Y f hf
  have h7 : closure (Set.range (Pi.map f)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    exact h_main g
  exact?
