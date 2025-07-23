-- In carleson/Carleson/GridStructure.lean

import Carleson.Defs

open Set MeasureTheory Metric Function Complex Bornology
open scoped NNReal ENNReal ComplexConjugate
noncomputable section

section Generic
universe u
variable {𝕜 : Type*} [_root_.RCLike 𝕜]

variable (X) in
/-- A grid structure on `X`.
I expect we prefer `coeGrid : Grid → Set X` over `Grid : Set (Set X)`
Note: the `s` in this paper is `-s` of Christ's paper.
-/
class GridStructure {A : outParam ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]
    (D : outParam ℕ) (κ : outParam ℝ) (S : outParam ℕ) (o : outParam X) where
  /-- indexing set for a grid structure -/
  protected Grid : Type u
  fintype_Grid : Fintype Grid
  /-- The collection of dyadic cubes -/
  coeGrid : Grid → Set X
  /-- scale functions -/
  s : Grid → ℤ
  /-- Center functions -/
  c : Grid → X
  inj : Injective (fun i ↦ (coeGrid i, s i))
  range_s_subset : range s ⊆ Icc (-S) S
  topCube : Grid
  s_topCube : s topCube = S
  c_topCube : c topCube = o
  subset_topCube {i} : coeGrid i ⊆ coeGrid topCube
  Grid_subset_biUnion {i} : ∀ k ∈ Ico (-S : ℤ) (s i), coeGrid i ⊆ ⋃ j ∈ s ⁻¹' {k}, coeGrid j
  fundamental_dyadic' {i j} : s i ≤ s j → coeGrid i ⊆ coeGrid j ∨ Disjoint (coeGrid i) (coeGrid j)
  ball_subset_Grid {i} : ball (c i) (D ^ s i / 4) ⊆ coeGrid i --2.0.10
  Grid_subset_ball {i} : coeGrid i ⊆ ball (c i) (4 * D ^ s i) --2.0.10
  small_boundary {i} {t : ℝ≥0} (ht : D ^ (- S - s i) ≤ t) :
    volume.real { x ∈ coeGrid i | EMetric.infEdist x (coeGrid i)ᶜ ≤ t * (D ^ (s i):ℝ≥0∞)} ≤ 2 * t ^ κ * volume.real (coeGrid i)
  coeGrid_measurable {i} : MeasurableSet (coeGrid i)

export GridStructure (range_s_subset Grid_subset_biUnion ball_subset_Grid Grid_subset_ball small_boundary
  topCube s_topCube c_topCube subset_topCube coeGrid_measurable) -- should `X` be explicit in topCube?

attribute [coe] GridStructure.coeGrid

variable {X : Type u} {A : ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]
variable {D : ℕ} {κ : ℝ} {S : ℕ} {o : X}
variable [GridStructure X D κ S o]

variable (X) in
/-- The indexing type of the grid structure. Elements are called (dyadic) cubes.
Note that this type has instances for both `≤` and `⊆`, but they do *not* coincide. -/
abbrev Grid : Type u := GridStructure.Grid X

def s : Grid X → ℤ := GridStructure.s
def c : Grid X → X := GridStructure.c

variable {i j : Grid X}

instance : Inhabited (Grid X) := ⟨topCube⟩
instance : Fintype (Grid X) := GridStructure.fintype_Grid
instance : Coe (Grid X) (Set X) := ⟨GridStructure.coeGrid⟩
instance : Membership X (Grid X) := ⟨fun i x ↦ x ∈ (i : Set X)⟩
instance : PartialOrder (Grid X) := PartialOrder.lift _ GridStructure.inj
/- These should probably not/only rarely be used. I comment them out for now,
so that we don't accidentally use it. We can put it back if useful after all. -/
-- instance : HasSubset (Grid X) := ⟨fun i j ↦ (i : Set X) ⊆ (j : Set X)⟩
-- instance : HasSSubset (Grid X) := ⟨fun i j ↦ (i : Set X) ⊂ (j : Set X)⟩
-- @[simp] lemma Grid.subset_def : i ⊆ j ↔ (i : Set X) ⊆ (j : Set X) := .rfl
-- @[simp] lemma Grid.ssubset_def : i ⊂ j ↔ (i : Set X) ⊂ (j : Set X) := .rfl

/- not sure whether these should be simp lemmas, but that might be required if we want to
  conveniently rewrite/simp with Set-lemmas -/
@[simp] lemma Grid.mem_def {x : X} : x ∈ i ↔ x ∈ (i : Set X) := .rfl
@[simp] lemma Grid.le_def : i ≤ j ↔ (i : Set X) ⊆ (j : Set X) ∧ s i ≤ s j := .rfl

lemma fundamental_dyadic :
    s i ≤ s j → (i : Set X) ⊆ (j : Set X) ∨ Disjoint (i : Set X) (j : Set X) :=
  GridStructure.fundamental_dyadic'

lemma le_or_disjoint (h : s i ≤ s j) : i ≤ j ∨ Disjoint (i : Set X) (j : Set X) :=
  fundamental_dyadic h |>.imp (⟨·, h⟩) id

lemma le_or_ge_or_disjoint : i ≤ j ∨ j ≤ i ∨ Disjoint (i : Set X) (j : Set X) := by
  rcases le_or_lt (s i) (s j) with h | h
  · have := le_or_disjoint h; tauto
  · have := le_or_disjoint h.le; tauto

lemma le_or_ge_of_mem_of_mem {c : X} (mi : c ∈ i) (mj : c ∈ j) : i ≤ j ∨ j ≤ i :=
  (or_assoc.mpr le_or_ge_or_disjoint).resolve_right (not_disjoint_iff.mpr ⟨c, mi, mj⟩)

lemma le_of_mem_of_mem (h : s i ≤ s j) {c : X} (mi : c ∈ i) (mj : c ∈ j) : i ≤ j :=
  ⟨(fundamental_dyadic h).resolve_right (not_disjoint_iff.mpr ⟨c, mi, mj⟩), h⟩

lemma eq_or_disjoint (hs : s i = s j) : i = j ∨ Disjoint (i : Set X) (j : Set X) :=
  Or.elim (le_or_disjoint hs.le) (fun ij ↦ Or.elim (le_or_disjoint hs.ge)
     (fun ji ↦ Or.inl (le_antisymm ij ji)) (fun h ↦ Or.inr h.symm)) (fun h ↦ Or.inr h)

lemma subset_of_nmem_Iic_of_not_disjoint (i : Grid X) (j : Grid X)
    (h : i ∉ Iic j)
    (notDisjoint : ¬ Disjoint (i : Set X) j) :
    (j : Set X) ⊆ i := by
  rw [Iic, Set.nmem_setOf_iff, Grid.le_def, not_and_or] at h
  have h_le_cases := le_or_ge_or_disjoint (i := i) (j := j)
  rcases h_le_cases with i_le | j_le | disjoint
  · exact (h.neg_resolve_left i_le.1 i_le.2).elim
  · rw [disjoint_comm] at notDisjoint
    exact (GridStructure.fundamental_dyadic' j_le.2).resolve_right notDisjoint
  · exact (notDisjoint disjoint).elim

lemma scale_mem_Icc : s i ∈ Icc (-S : ℤ) S := mem_Icc.mp (range_s_subset ⟨i, rfl⟩)

lemma volume_coeGrid_pos (hD : 0 < D) : 0 < volume (i : Set X) := by
  have hD : 0 < (D : ℝ) ^ GridStructure.s i / 4 := by
    simp only [Nat.ofNat_pos, div_pos_iff_of_pos_right]
    exact zpow_pos (Nat.cast_pos'.mpr hD) _
  exact measure_pos_of_superset ball_subset_Grid (ne_of_gt (measure_ball_pos _ _ hD))

@[aesop (rule_sets := [finiteness]) safe apply]
lemma volume_coeGrid_lt_top : volume (i : Set X) < ⊤ :=
  measure_lt_top_of_subset Grid_subset_ball (measure_ball_ne_top _ _)

namespace Grid

protected lemma inj : Injective (fun i : Grid X ↦ ((i : Set X), s i)) := GridStructure.inj

lemma le_topCube : i ≤ topCube :=
  ⟨subset_topCube, scale_mem_Icc.2.trans_eq s_topCube.symm⟩

lemma isTop_topCube : IsTop (topCube : Grid X) := fun _ ↦ le_topCube

lemma isMax_iff : IsMax i ↔ i = topCube := isTop_topCube.isMax_iff

/-- The set `I ↦ Iᵒ` in the blueprint. -/
def int (i : Grid X) : Set X := ball (c i) (D ^ s i / 4)

postfix:max "ᵒ" => Grid.int

/-- An auxiliary measure used in the well-foundedness of `Ω` in Lemma `tile_structure`. -/
def opSize (i : Grid X) : ℕ := (S - s i).toNat

lemma int_subset : i.int ⊆ i := ball_subset_Grid

end Grid
end Generic

namespace Grid

open scoped ShortVariables
variable {X : Type*} [PseudoMetricSpace X] {a : ℕ} {q : ℝ} {K : X → X → ℂ}
  {σ₁ σ₂ : X → ℤ} {F G : Set X} [ProofData a q K σ₁ σ₂ F G]

notation "dist_{" I "}" => @dist (WithFunctionDistance (c I) (D ^ s I / 4)) _
notation "nndist_{" I "}" => @nndist (WithFunctionDistance (c I) (D ^ s I / 4)) _
notation "ball_{" I "}" => @ball (WithFunctionDistance (c I) (D ^ s I / 4)) _

section GridManipulation

variable [GridStructure X D κ S o]

lemma c_mem_Grid {i : Grid X} : c i ∈ (i : Set X) := by
  obtain ⟨hD⟩ := NeZero.of_pos <| zero_lt_one.trans_le one_le_D
  exact mem_of_mem_of_subset (Metric.mem_ball_self (by positivity)) ball_subset_Grid

lemma nonempty (i : Grid X) : (i : Set X).Nonempty := ⟨c i, c_mem_Grid⟩

lemma le_dyadic {i j k : Grid X} (h : s i ≤ s j) (li : k ≤ i) (lj : k ≤ j) : i ≤ j := by
  obtain ⟨c, mc⟩ := k.nonempty
  exact le_of_mem_of_mem h (mem_of_mem_of_subset mc li.1) (mem_of_mem_of_subset mc lj.1)

@[simp] lemma lt_def {i j : Grid X} : i < j ↔ (i : Set X) ⊆ (j : Set X) ∧ s i < s j := by
  constructor <;> intro h
  · obtain ⟨a₁, a₂⟩ := h.le
    refine ⟨a₁, lt_of_le_of_ne a₂ ?_⟩
    by_contra a₃
    have l : i < i := h.trans_le (le_dyadic a₃.ge h.le le_rfl)
    rwa [lt_self_iff_false] at l
  · apply lt_of_le_of_ne (le_def.mpr ⟨h.1, h.2.le⟩)
    by_contra a; rw [a, lt_self_iff_false] at h; exact h.2

lemma isMin_iff {i : Grid X} : IsMin i ↔ s i = - S := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · apply le_antisymm ?_ scale_mem_Icc.1
    contrapose! h
    have : -(S : ℤ) ∈ Ico (-(S : ℤ)) (s i) := by simp [h]
    have := Grid_subset_biUnion (i := i) (-S) this c_mem_Grid
    simp only [defaultA, defaultD.eq_1, defaultκ.eq_1, mem_preimage, mem_singleton_iff, mem_iUnion,
      exists_prop] at this
    rcases this with ⟨j, (hj : s j = -(S : ℤ)), h'j⟩
    have sji : s j < s i := by simpa [hj] using h
    have : (j : Set X) ⊆ i := by
      rcases fundamental_dyadic sji.le with hji | h_disj
      · exact hji
      · exact (disjoint_right.1 h_disj c_mem_Grid h'j).elim
    have : j < i := by simp [this, sji]
    exact this.not_isMin
  · intro j hj
    have : s i ≤ s j := by rw [h]; exact (scale_mem_Icc (i := j)).1
    rcases le_or_disjoint this with h' | h_disj
    · exact h'
    · exact False.elim (disjoint_right.1 h_disj c_mem_Grid (hj.1 c_mem_Grid))

/-- There exists a unique successor of each non-maximal cube. -/
lemma exists_unique_succ (i : Grid X) (h : ¬IsMax i) :
    ∃! j ∈ Finset.univ, i < j ∧ ∀ j', i < j' → j ≤ j' := by
  simp_rw [Finset.mem_univ, true_and]
  classical let incs : Finset (Grid X) := { j | i < j }
  have ine : incs.Nonempty := by
    use topCube; simp only [incs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_of_le_of_ne le_topCube (isMax_iff.not.mp h)
  obtain ⟨j, mj, hj⟩ := incs.exists_minimal ine
  simp only [gt_iff_lt, Finset.mem_filter, Finset.mem_univ, true_and, incs] at mj hj
  replace hj : ∀ (x : Grid X), i < x → j ≤ x := fun x mx ↦ by
    rcases lt_or_le (s x) (s j) with c | c
    · exact (eq_of_le_of_not_lt (le_dyadic c.le mx.le mj.le) (hj x mx)).symm.le
    · exact le_dyadic c mj.le mx.le
  use j, ⟨mj, hj⟩, fun k ⟨hk₁, hk₂⟩ ↦ le_antisymm (hk₂ j mj) (hj k hk₁)

open Classical in
/-- If `i` is not a maximal element, this is the (unique) minimal element greater than i.
This is not a `SuccOrder` since an element can be the successor of multiple other elements. -/
def succ (i : Grid X) : Grid X := if h : IsMax i then i else Finset.choose (hp := exists_unique_succ i h)

variable {i j : Grid X}

lemma succ_spec (h : ¬IsMax i) : i < i.succ ∧ ∀ j, i < j → i.succ ≤ j := by
  simp only [succ, h, dite_false]
  classical exact Finset.choose_spec (hp := exists_unique_succ i h).2

lemma succ_unique (h : ¬IsMax i) : i < j → (∀ j', i < j' → j ≤ j') → i.succ = j := fun k₁ k₂ ↦
  ((exists_unique_succ i h).unique ⟨by simp, k₁, k₂⟩ ⟨by simp, succ_spec h⟩).symm

lemma le_succ : i ≤ i.succ := by
  by_cases h : IsMax i
  · simp [h, succ]
  · exact (succ_spec h).1.le

lemma max_of_le_succ : i.succ ≤ i → IsMax i := fun h ↦ by
  contrapose! h; by_contra! k; have l := (succ_spec h).1.trans_le k
  rwa [lt_self_iff_false] at l

lemma not_isMax_of_scale_lt {j W : Grid X} (h : s j < s W) : ¬IsMax j := by
  rw [Grid.isMax_iff]
  intro top
  rw [top, show s topCube = ↑S by exact s_topCube (X := X)] at h
  linarith [(scale_mem_Icc (i := W)).2]

lemma succ_le_of_lt (h : i < j) : i.succ ≤ j := by
  by_cases k : IsMax i
  · simp only [k, succ, dite_true]; exact h.le
  · exact (succ_spec k).2 j h

lemma exists_containing_subcube (l : ℤ) (h : l ∈ Icc (-S : ℤ) (s i)) {x : X} (mx : x ∈ i) :
    ∃ j, s j = l ∧ x ∈ j := by
  obtain ⟨lb, ub⟩ := h
  rcases ub.eq_or_lt with ub | ub
  · exact ⟨i, ub.symm, mx⟩
  · simpa [mem_iUnion₂, mem_preimage, mem_singleton_iff, exists_prop] using
      Grid_subset_biUnion l ⟨lb, ub⟩ mx

lemma exists_supercube (l : ℤ) (h : l ∈ Icc (s i) S) : ∃ j, s j = l ∧ i ≤ j := by
  obtain ⟨lb, ub⟩ := h
  rcases ub.eq_or_lt with ub | ub; · exact ⟨topCube, by simpa [ub] using s_topCube, le_topCube⟩
  obtain ⟨x, hx⟩ := i.nonempty
  have bound_i : -S ≤ s i ∧ s i ≤ S := scale_mem_Icc
  have ts := Grid_subset_biUnion (X := X) (i := topCube) l
    (by rw [s_topCube, mem_Ico]; omega)
  have := mem_of_mem_of_subset hx ((le_topCube (i := i)).1.trans ts)
  simp_rw [mem_preimage, mem_singleton_iff, mem_iUnion, exists_prop] at this
  obtain ⟨j, (sj : s j = l), mj⟩ := this; use j, sj
  exact le_of_mem_of_mem (by omega) hx mj

lemma exists_sandwiched (h : i ≤ j) (l : ℤ) (hl : l ∈ Icc (s i) (s j)) :
    ∃ k, s k = l ∧ i ≤ k ∧ k ≤ j := by
  have bound_q : -S ≤ s j ∧ s j ≤ S := scale_mem_Icc
  rw [mem_Icc] at hl
  obtain ⟨K, sK, lbK⟩ := exists_supercube l (by change s i ≤ _ ∧ _; omega)
  use K, sK, lbK
  exact le_dyadic (by omega) lbK h

/- Start of proof attempt -/
lemma round1_scale_succ (h : ¬IsMax i) : s i.succ = s i + 1 := by
  have h1 : i < i.succ := (succ_spec h).1
  have h1' : (i : Set X) ⊆ (i.succ : Set X) ∧ s i < s i.succ := by
    rw [lt_def] at h1
    tauto
  have h2 : s i < s i.succ := h1'.2
  by_cases h3 : s i.succ > s i + 1
  · -- Case 1: s i.succ > s i + 1
    have h4 : s i.succ ≥ s i + 2 := by linarith
    have h5 : s i ≤ s i + 1 := by linarith
    have h6 : s i + 1 ≤ s i.succ := by linarith
    have h7 : (s i + 1) ∈ Set.Icc (s i) (s i.succ) := ⟨by linarith, by linarith⟩
    have h8 : i ≤ i.succ := le_succ
    obtain ⟨k, hk1, hk2, hk3⟩ := exists_sandwiched h8 (s i + 1) h7
    have h91 : (i : Set X) ⊆ (k : Set X) := hk2.1
    have h92 : s i < s k := by
      linarith [hk1]
    have h9 : i < k := by
      rw [lt_def]
      exact ⟨h91, h92⟩
    have h10 : i.succ ≤ k := (succ_spec h).2 k h9
    have h11 : k ≤ i.succ := hk3
    have h12 : k = i.succ := by
      have h121 : k ≤ i.succ := h11
      have h122 : i.succ ≤ k := h10
      have h123 : k = i.succ := by
        apply le_antisymm h121 h122
      exact h123
    have h13 : s k = s i + 1 := by simpa using hk1
    have h14 : s i.succ = s k := by rw [h12]
    have h15 : s i.succ = s i + 1 := by linarith
    linarith
  · -- Case 2: ¬ (s i.succ > s i + 1)
    have h3' : s i.succ ≤ s i + 1 := by linarith
    have h2' : s i.succ ≥ s i + 1 := by linarith
    have h15 : s i.succ = s i + 1 := by linarith
    exact h15

theorem scale_succ (h : ¬IsMax i) : s i.succ = s i + 1  := by

  exact round1_scale_succ h
