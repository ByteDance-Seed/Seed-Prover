-- In carleson/Carleson/Discrete/ForestUnion.lean

import Carleson.Discrete.Defs
import Carleson.ForestOperator.Forests
import Carleson.Discrete.SumEstimates

open MeasureTheory Measure NNReal Metric Complex Set
open scoped ENNReal
open Classical -- We use quite some `Finset.filter`
noncomputable section

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

variable {k n j l : ℕ} {p p' u u' : 𝔓 X} {x : X}

/-! ## Section 5.3 -/

/-! Note: the lemmas 5.3.1-5.3.3 are in `TileStructure`. -/

/-- Lemma 5.3.4 -/
lemma ordConnected_tilesAt : OrdConnected (TilesAt k : Set (𝔓 X)) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  simp_rw [TilesAt, mem_preimage, 𝓒, mem_diff, aux𝓒, mem_setOf] at mp mp'' ⊢
  constructor
  · obtain ⟨J, hJ, _⟩ := mp''.1
    use J, mp'.2.1.trans hJ
  · push_neg at mp ⊢
    exact fun J hJ ↦ mp.2 J (mp'.1.1.trans hJ)

/-- Lemma 5.3.5 -/
lemma ordConnected_C : OrdConnected (ℭ k n : Set (𝔓 X)) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  rw [ℭ, mem_setOf] at mp mp'' ⊢
  have z := mem_of_mem_of_subset mp' (ordConnected_tilesAt.out mp.1 mp''.1)
  refine ⟨z, ?_⟩
  have hk : ∀ q' ∈ TilesAt (X := X) k, ∀ q ≤ q', dens' k {q'} ≤ dens' k {q} := fun q' _ q hq ↦ by
    simp_rw [dens', mem_singleton_iff, iSup_iSup_eq_left]; gcongr with l hl a _
    exact iSup_const_mono fun h ↦
      wiggle_order_11_10 hq (C5_3_3_le (X := X).trans (by norm_num) |>.trans hl) |>.trans h
  exact ⟨mp''.2.1.trans_le (hk _ mp''.1 _ mp'.2), (hk _ z _ mp'.1).trans mp.2.2⟩

/-- Lemma 5.3.6 -/
lemma ordConnected_C1 : OrdConnected (ℭ₁ k n j : Set (𝔓 X)) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  have mp'₁ : p' ∈ ℭ (X := X) k n := mem_of_mem_of_subset mp'
    (ordConnected_C.out (mem_of_mem_of_subset mp ℭ₁_subset_ℭ)
      (mem_of_mem_of_subset mp'' ℭ₁_subset_ℭ))
  simp_rw [ℭ₁, mem_diff, preℭ₁, mem_setOf, not_and, not_le] at mp mp'' ⊢
  simp_rw [mp.1.1, true_and, true_implies] at mp
  simp_rw [mp'₁, true_and, true_implies]
  simp_rw [mp''.1.1, true_and, true_implies] at mp''
  constructor
  · refine mp''.1.trans (Finset.card_le_card fun b mb ↦ ?_)
    simp_rw [Finset.mem_filter, Finset.mem_univ, true_and, 𝔅, mem_setOf] at mb ⊢
    have h100 := wiggle_order_11_10 (n := 100) mp'.2 (C5_3_3_le (X := X).trans (by norm_num))
    exact ⟨mb.1, h100.trans mb.2⟩
  · refine (Finset.card_le_card fun b mb ↦ ?_).trans_lt mp.2
    simp_rw [Finset.mem_filter, Finset.mem_univ, true_and, 𝔅, mem_setOf] at mb ⊢
    have h100 := wiggle_order_11_10 (n := 100) mp'.1 (C5_3_3_le (X := X).trans (by norm_num))
    exact ⟨mb.1, h100.trans mb.2⟩

/-- Lemma 5.3.7 -/
lemma ordConnected_C2 : OrdConnected (ℭ₂ k n j : Set (𝔓 X)) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  have mp₁ := mem_of_mem_of_subset mp ℭ₂_subset_ℭ₁
  have mp'₁ : p' ∈ ℭ₁ (X := X) k n j := mem_of_mem_of_subset mp'
    (ordConnected_C1.out mp₁ (mem_of_mem_of_subset mp'' ℭ₂_subset_ℭ₁))
  by_cases e : p = p'; · rwa [e] at mp
  simp_rw [ℭ₂, layersAbove, mem_diff, mp'₁, true_and]
  by_contra h; rw [mem_iUnion₂] at h; obtain ⟨l', bl', p'm⟩ := h
  rw [minLayer, mem_setOf, minimal_iff] at p'm
  have pnm : p ∉ ⋃ l'', ⋃ (_ : l'' < l'), 𝔏₁ k n j l'' := by
    replace mp := mp.2; contrapose! mp
    exact mem_of_mem_of_subset mp
      (iUnion_mono'' fun i ↦ iUnion_subset_iUnion_const fun hi ↦ (hi.trans_le bl').le)
  exact absurd (p'm.2 ⟨mp.1, pnm⟩ mp'.1).symm e

/-- Lemma 5.3.8 -/
lemma ordConnected_C3 : OrdConnected (ℭ₃ k n j : Set (𝔓 X)) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  have mp₁ := mem_of_mem_of_subset mp ℭ₃_subset_ℭ₂
  have mp''₁ := mem_of_mem_of_subset mp'' ℭ₃_subset_ℭ₂
  have mp'₁ : p' ∈ ℭ₂ (X := X) k n j := mem_of_mem_of_subset mp' (ordConnected_C2.out mp₁ mp''₁)
  rw [ℭ₃_def] at mp'' ⊢
  obtain ⟨-, u, mu, 𝓘nu, su⟩ := mp''; refine ⟨mp'₁, ⟨u, mu, ?_⟩⟩
  exact ⟨(mp'.2.1.trans_lt (lt_of_le_of_ne su.1 𝓘nu)).ne,
    (wiggle_order_11_10 mp'.2 (C5_3_3_le (X := X).trans (by norm_num))).trans su⟩

/-- Lemma 5.3.9 -/
lemma ordConnected_C4 : OrdConnected (ℭ₄ k n j : Set (𝔓 X)) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  have mp''₁ := mem_of_mem_of_subset mp'' ℭ₄_subset_ℭ₃
  have mp'₁ : p' ∈ ℭ₃ (X := X) k n j := mem_of_mem_of_subset mp'
    (ordConnected_C3.out (mem_of_mem_of_subset mp ℭ₄_subset_ℭ₃) mp''₁)
  by_cases e : p' = p''; · rwa [← e] at mp''
  simp_rw [ℭ₄, layersBelow, mem_diff, mp'₁, true_and]
  by_contra h; simp_rw [mem_iUnion] at h; obtain ⟨l', hl', p'm⟩ := h
  rw [maxLayer_def, mem_setOf, maximal_iff] at p'm
  simp_rw [mem_diff] at p'm
  have p''nm : p'' ∉ ⋃ l'', ⋃ (_ : l'' < l'), 𝔏₃ k n j l'' := by
    replace mp'' := mp''.2; contrapose! mp''
    refine mem_of_mem_of_subset mp'' <| iUnion₂_mono' fun i hi ↦ ⟨i, hi.le.trans hl', subset_rfl⟩
  exact absurd (p'm.2 ⟨mp''₁, p''nm⟩ mp'.2) e

/-- Lemma 5.3.10 -/
lemma ordConnected_C5 : OrdConnected (ℭ₅ k n j : Set (𝔓 X)) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  have mp₁ := mem_of_mem_of_subset mp ℭ₅_subset_ℭ₄
  have mp'₁ : p' ∈ ℭ₄ (X := X) k n j := mem_of_mem_of_subset mp'
    (ordConnected_C4.out mp₁ (mem_of_mem_of_subset mp'' ℭ₅_subset_ℭ₄))
  simp_rw [ℭ₅, mem_diff, mp₁, mp'₁, true_and, 𝔏₄, mem_setOf,
    mp₁, mp'₁, true_and] at mp ⊢
  contrapose! mp; obtain ⟨u, mu, s𝓘u⟩ := mp; use u, mu, mp'.1.1.1.trans s𝓘u

/-! ## Section 5.4 and Lemma 5.1.2 -/

/-- The subset `ℭ₆(k, n, j)` of `ℭ₅(k, n, j)`, given above (5.4.1). -/
def ℭ₆ (k n j : ℕ) : Set (𝔓 X) :=
  { p ∈ ℭ₅ k n j | ¬ (𝓘 p : Set X) ⊆ G' }

lemma ℭ₆_subset_ℭ₅ : ℭ₆ (X := X) k n j ⊆ ℭ₅ k n j := sep_subset ..
lemma ℭ₆_subset_ℭ : ℭ₆ (X := X) k n j ⊆ ℭ k n := ℭ₆_subset_ℭ₅.trans ℭ₅_subset_ℭ

/-- The subset `𝔗₁(u)` of `ℭ₁(k, n, j)`, given in (5.4.1).
In lemmas, we will assume `u ∈ 𝔘₁ k n l` -/
def 𝔗₁ (k n j : ℕ) (u : 𝔓 X) : Set (𝔓 X) :=
  { p ∈ ℭ₁ k n j | 𝓘 p ≠ 𝓘 u ∧ smul 2 p ≤ smul 1 u }

lemma 𝓘_lt_of_mem_𝔗₁ (h : p ∈ 𝔗₁ k n j p') : 𝓘 p < 𝓘 p' := by
  rw [𝔗₁, mem_setOf] at h; exact lt_of_le_of_ne h.2.2.1 h.2.1

/-- The subset `𝔘₂(k, n, j)` of `𝔘₁(k, n, j)`, given in (5.4.2). -/
def 𝔘₂ (k n j : ℕ) : Set (𝔓 X) :=
  { u ∈ 𝔘₁ k n j | ¬ Disjoint (𝔗₁ k n j u) (ℭ₆ k n j) }

lemma 𝔘₂_subset_𝔘₁ : 𝔘₂ k n j ⊆ 𝔘₁ (X := X) k n j := fun _ mu ↦ mu.1

/-- The relation `∼` defined below (5.4.2). It is an equivalence relation on `𝔘₂ k n j`. -/
def URel (k n j : ℕ) (u u' : 𝔓 X) : Prop :=
  u = u' ∨ ∃ p ∈ 𝔗₁ k n j u, smul 10 p ≤ smul 1 u'

nonrec lemma URel.rfl : URel k n j u u := Or.inl rfl

/-- Lemma 5.4.1, part 2. -/
lemma URel.not_disjoint (hu : u ∈ 𝔘₂ k n j) (hu' : u' ∈ 𝔘₂ k n j) (huu' : URel k n j u u') :
    ¬Disjoint (ball_(u) (𝒬 u) 100) (ball_(u') (𝒬 u') 100) := by
  by_cases e : u = u'; · rw [e]; simp
  simp_rw [URel, e, false_or, 𝔗₁, mem_setOf] at huu'; obtain ⟨p, ⟨mp, np, sl₁⟩, sl₂⟩ := huu'
  by_cases e' : 𝓘 p = 𝓘 u'
  · refine not_disjoint_iff.mpr ⟨𝒬 u, mem_ball_self (by positivity), ?_⟩
    rw [@mem_ball]
    have i1 : ball_{𝓘 u} (𝒬 u) 1 ⊆ ball_{𝓘 p} (𝒬 p) 2 := sl₁.2
    have i2 : ball_{𝓘 u'} (𝒬 u') 1 ⊆ ball_{𝓘 p} (𝒬 p) 10 := sl₂.2
    replace i1 : 𝒬 u ∈ ball_{𝓘 p} (𝒬 p) 2 := i1 (mem_ball_self zero_lt_one)
    replace i2 : 𝒬 u' ∈ ball_{𝓘 p} (𝒬 p) 10 := i2 (mem_ball_self zero_lt_one)
    rw [e', @mem_ball] at i1 i2
    calc
      _ ≤ dist_{𝓘 u'} (𝒬 u) (𝒬 p) + dist_{𝓘 u'} (𝒬 u') (𝒬 p) := dist_triangle_right ..
      _ < 2 + 10 := add_lt_add i1 i2
      _ < 100 := by norm_num
  have plu : smul 100 p ≤ smul 100 u := wiggle_order_100 (smul_mono sl₁ le_rfl (by norm_num)) np
  have plu' : smul 100 p ≤ smul 100 u' := wiggle_order_100 sl₂ e'
  by_contra h
  have 𝔅dj : Disjoint (𝔅 k n u) (𝔅 k n u') := by
    simp_rw [𝔅, disjoint_left, mem_setOf, not_and]; intro q ⟨_, sl⟩ _
    simp_rw [TileLike.le_def, smul_fst, smul_snd, not_and_or] at sl ⊢; right
    have := disjoint_left.mp (h.mono_left sl.2) (mem_ball_self zero_lt_one)
    rw [not_subset]; use 𝒬 q, mem_ball_self zero_lt_one
  have usp : 𝔅 k n u ⊆ 𝔅 k n p := fun q mq ↦ by
    rw [𝔅, mem_setOf] at mq ⊢; exact ⟨mq.1, plu.trans mq.2⟩
  have u'sp : 𝔅 k n u' ⊆ 𝔅 k n p := fun q mq ↦ by
    rw [𝔅, mem_setOf] at mq ⊢; exact ⟨mq.1, plu'.trans mq.2⟩
  rw [𝔘₂, mem_setOf, 𝔘₁, mem_setOf] at hu hu'
  apply absurd (card_𝔅_of_mem_ℭ₁ mp).2; rw [not_lt]
  calc
    _ = 2 ^ j + 2 ^ j := Nat.two_pow_succ j
    _ ≤ (𝔅 k n u).toFinset.card + (𝔅 k n u').toFinset.card :=
      add_le_add (card_𝔅_of_mem_ℭ₁ hu.1.1).1 (card_𝔅_of_mem_ℭ₁ hu'.1.1).1
    _ = (𝔅 k n u ∪ 𝔅 k n u').toFinset.card := by
      rw [toFinset_union]; refine (Finset.card_union_of_disjoint ?_).symm
      simpa using 𝔅dj
    _ ≤ _ := by
      apply Finset.card_le_card
      simp_rw [toFinset_union, subset_toFinset, Finset.coe_union, coe_toFinset, union_subset_iff]
      exact ⟨usp, u'sp⟩

/-- Lemma 5.4.1, part 1. -/
lemma URel.eq (hu : u ∈ 𝔘₂ k n j) (hu' : u' ∈ 𝔘₂ k n j) (huu' : URel k n j u u') : 𝓘 u = 𝓘 u' := by
  by_cases e : u = u'; · rw [e]
  have ndj := not_disjoint hu hu' huu'
  have n₁ := (hu.1.2 _ hu'.1.1).mt ndj
  rw [disjoint_comm] at ndj
  have n₂ := (hu'.1.2 _ hu.1.1).mt ndj
  simp_rw [URel, e, false_or, 𝔗₁, mem_setOf] at huu'; obtain ⟨p, ⟨_, _, sl₁⟩, sl₂⟩ := huu'
  rcases le_or_lt (𝔰 u) (𝔰 u') with h | h
  · exact eq_of_le_of_not_lt (Grid.le_dyadic h sl₁.1 sl₂.1) n₁
  · exact (eq_of_le_of_not_lt (Grid.le_dyadic h.le sl₂.1 sl₁.1) n₂).symm

/-- Helper for 5.4.2 that is also used in 5.4.9. -/
lemma urel_of_not_disjoint {x y : 𝔓 X} (my : y ∈ 𝔘₂ k n j) (xye : 𝓘 x = 𝓘 y)
    (nd : ¬Disjoint (ball_(x) (𝒬 x) 100) (ball_(y) (𝒬 y) 100)) : URel k n j y x := by
  rw [not_disjoint_iff] at nd
  obtain ⟨(ϑ : Θ X), (ϑx : ϑ ∈ ball_{𝓘 x} (𝒬 x) 100), (ϑy : ϑ ∈ ball_{𝓘 y} (𝒬 y) 100)⟩ := nd
  rw [𝔘₂, mem_setOf, not_disjoint_iff] at my; obtain ⟨p, hp, _⟩ := my.2
  suffices w : ball_(x) (𝒬 x) 1 ⊆ ball_(y) (𝒬 y) 500 by
    right; use p, hp; obtain ⟨_, np, sl⟩ := hp
    have hpy : smul 10 p ≤ smul 500 y :=
      (smul_mono_left (by norm_num)).trans (wiggle_order_500 sl np)
    exact ⟨(xye ▸ sl.1 : 𝓘 p ≤ 𝓘 x), hpy.2.trans w⟩
  intro (q : Θ X) (mq : q ∈ ball_{𝓘 x} (𝒬 x) 1)
  rw [@mem_ball] at mq ⊢
  calc
    _ ≤ dist_(y) q ϑ + dist_(y) ϑ (𝒬 y) := dist_triangle ..
    _ ≤ dist_(y) q (𝒬 x) + dist_(y) ϑ (𝒬 x) + dist_(y) ϑ (𝒬 y) := by
      gcongr; apply dist_triangle_right
    _ < 1 + 100 + 100 := by
      gcongr
      · rwa [xye] at mq
      · rwa [@mem_ball, xye] at ϑx
      · rwa [@mem_ball] at ϑy
    _ < _ := by norm_num

/-- Lemma 5.4.2. -/
lemma equivalenceOn_urel : EquivalenceOn (URel (X := X) k n j) (𝔘₂ k n j) where
  refl _ _ := .rfl
  trans {x y z} mx my mz xy yz := by
    by_cases xny : x = y; · rwa [xny]
    have xye := URel.eq mx my xy
    have hxy := URel.not_disjoint mx my xy
    rw [not_disjoint_iff] at hxy
    obtain ⟨(ϑ : Θ X), (ϑx : ϑ ∈ ball_{𝓘 x} (𝒬 x) 100), (ϑy : ϑ ∈ ball_{𝓘 y} (𝒬 y) 100)⟩ := hxy
    have yze := URel.eq my mz yz
    have hyz := URel.not_disjoint my mz yz
    rw [not_disjoint_iff] at hyz
    obtain ⟨(θ : Θ X), (θy : θ ∈ ball_{𝓘 y} (𝒬 y) 100), (θz : θ ∈ ball_{𝓘 z} (𝒬 z) 100)⟩ := hyz
    simp_rw [URel, xny, false_or] at xy; obtain ⟨p, mp, sp⟩ := xy
    suffices ball_(z) (𝒬 z) 1 ⊆ ball_(x) (𝒬 x) 500 by
      right; use p, mp; obtain ⟨_, np, sl⟩ := mp
      have w : ball_(x) (𝒬 x) 500 ⊆ ball_(p) (𝒬 p) 4 := (wiggle_order_500 sl np).2
      exact ⟨(yze ▸ xye ▸ sl.1 : 𝓘 p ≤ 𝓘 z), (this.trans w).trans (ball_subset_ball (by norm_num))⟩
    intro (q : Θ X) (mq : q ∈ ball_{𝓘 z} (𝒬 z) 1)
    rw [@mem_ball] at mq ⊢
    calc
      _ ≤ dist_(x) q ϑ + dist_(x) ϑ (𝒬 x) := dist_triangle ..
      _ < dist_(x) q ϑ + 100 := by gcongr; rwa [@mem_ball] at ϑx
      _ ≤ dist_(x) q (𝒬 y) + dist_(x) ϑ (𝒬 y) + 100 := by gcongr; exact dist_triangle_right ..
      _ < dist_(x) q (𝒬 y) + 100 + 100 := by gcongr; rwa [@mem_ball, ← xye] at ϑy
      _ ≤ dist_(x) q θ + dist_(x) θ (𝒬 y) + 100 + 100 := by gcongr; exact dist_triangle ..
      _ < dist_(x) q θ + 100 + 100 + 100 := by gcongr; rwa [@mem_ball, ← xye] at θy
      _ ≤ dist_(x) q (𝒬 z) + dist_(x) θ (𝒬 z) + 100 + 100 + 100 := by
        gcongr; exact dist_triangle_right ..
      _ < 1 + 100 + 100 + 100 + 100 := by
        gcongr
        · rwa [← yze, ← xye] at mq
        · rwa [@mem_ball, ← yze, ← xye] at θz
      _ < _ := by norm_num
  symm {x y} mx my xy := urel_of_not_disjoint my (URel.eq mx my xy) (URel.not_disjoint mx my xy)

/-- `𝔘₃(k, n, j) ⊆ 𝔘₂ k n j` is an arbitary set of representatives of `URel` on `𝔘₂ k n j`,
given above (5.4.5). -/
def 𝔘₃ (k n j : ℕ) : Set (𝔓 X) :=
  (equivalenceOn_urel (k := k) (n := n) (j := j)).reprs

lemma 𝔘₃_subset_𝔘₂ : 𝔘₃ k n j ⊆ 𝔘₂ (X := X) k n j := EquivalenceOn.reprs_subset

/-- The subset `𝔗₂(u)` of `ℭ₆(k, n, j)`, given in (5.4.5).
In lemmas, we will assume `u ∈ 𝔘₃ k n l` -/
def 𝔗₂ (k n j : ℕ) (u : 𝔓 X) : Set (𝔓 X) :=
  ℭ₆ k n j ∩ ⋃ (u' ∈ 𝔘₂ k n j) (_ : URel k n j u u'), 𝔗₁ k n j u'

lemma 𝔗₂_subset_ℭ₆ : 𝔗₂ k n j u ⊆ ℭ₆ k n j := inter_subset_left ..

/-- Lemma 5.4.3 -/
lemma C6_forest : ℭ₆ (X := X) k n j = ⋃ u ∈ 𝔘₃ k n j, 𝔗₂ k n j u := by
  ext p; constructor <;> intro h
  · have hp : p ∈ ℭ₃ k n j := (ℭ₆_subset_ℭ₅ |>.trans ℭ₅_subset_ℭ₄ |>.trans ℭ₄_subset_ℭ₃) h
    rw [ℭ₃, mem_diff, 𝔏₂, mem_setOf] at hp
    have mp := hp.1
    simp_rw [hp.1, true_and, not_not] at hp
    obtain ⟨u, mu, np, sl⟩ := hp
    have mp' : p ∈ 𝔗₁ k n j u := by
      rw [𝔗₁, mem_setOf]; exact ⟨ℭ₂_subset_ℭ₁ mp, np, sl⟩
    have mu' : u ∈ 𝔘₂ k n j := by
      rw [𝔘₂, mem_setOf]; exact ⟨mu, not_disjoint_iff.mpr ⟨_, mp', h⟩⟩
    let rr := equivalenceOn_urel (X := X) (k := k) (n := n) (j := j)
    rw [mem_iUnion₂]; use rr.out u, (rr.out_mem_reprs mu')
    refine ⟨h, ?_⟩; rw [mem_iUnion₂]; use u, mu'; rw [mem_iUnion]; use rr.out_rel mu'
  · rw [mem_iUnion₂] at h; obtain ⟨_, _, mp, _⟩ := h; exact mp

/-- This one could deserve a lemma in the blueprint, as it is needed to decompose the sum
of Carleson operators over disjoint subfamilies. -/
lemma forest_disjoint : (𝔘₃ k n j).PairwiseDisjoint (fun u ↦ 𝔗₂ (X := X) k n j u) := by
  intro u hu u' hu' huu'
  simp only [Function.onFun]
  apply disjoint_left.2 (fun p pu pu' ↦ huu' ?_)
  simp only [𝔗₂, mem_inter_iff, mem_iUnion, exists_prop, exists_and_left] at pu pu'
  rcases pu.2 with ⟨v, v_mem, v_rel, pv⟩
  rcases pu'.2 with ⟨v', v'_mem, v'_rel, pv'⟩
  have E : URel k n j v v' :=
    Or.inr ⟨p, pv, smul_mono pv'.2.2 le_rfl (by norm_num)⟩
  have : URel k n j u v' :=
    (equivalenceOn_urel (X := X)).trans (𝔘₃_subset_𝔘₂ hu) v_mem v'_mem v_rel E
  have : URel k n j u u' := by
    apply (equivalenceOn_urel (X := X)).trans (𝔘₃_subset_𝔘₂ hu) v'_mem (𝔘₃_subset_𝔘₂ hu') this
    exact (equivalenceOn_urel (X := X)).symm (𝔘₃_subset_𝔘₂ hu') v'_mem v'_rel
  exact (equivalenceOn_urel (X := X)).reprs_inj hu hu' this

/-- Lemma 5.4.4, verifying (2.0.32) -/
lemma forest_geometry (hu : u ∈ 𝔘₃ k n j) (hp : p ∈ 𝔗₂ k n j u) : smul 4 p ≤ smul 1 u := by
  rw [𝔗₂, mem_inter_iff, mem_iUnion₂] at hp
  obtain ⟨_, u', mu', w⟩ := hp; rw [mem_iUnion] at w; obtain ⟨ru, mp'⟩ := w
  rw [𝔗₁, mem_setOf] at mp'; obtain ⟨_, np, sl⟩ := mp'
  have xye := URel.eq (EquivalenceOn.reprs_subset hu) mu' ru
  have huu' := URel.not_disjoint (EquivalenceOn.reprs_subset hu) mu' ru
  rw [not_disjoint_iff] at huu'
  obtain ⟨(ϑ : Θ X), (ϑx : ϑ ∈ ball_{𝓘 u} (𝒬 u) 100), (ϑy : ϑ ∈ ball_{𝓘 u'} (𝒬 u') 100)⟩ := huu'
  suffices ball_(u) (𝒬 u) 1 ⊆ ball_(u') (𝒬 u') 500 by
    have w : smul 4 p ≤ smul 500 u' := (wiggle_order_500 sl np)
    exact ⟨(xye ▸ sl.1 : 𝓘 p ≤ 𝓘 u), w.2.trans this⟩
  intro (q : Θ X) (mq : q ∈ ball_{𝓘 u} (𝒬 u) 1)
  rw [@mem_ball] at mq ⊢
  calc
    _ ≤ dist_(u') q ϑ + dist_(u') ϑ (𝒬 u') := dist_triangle ..
    _ ≤ dist_(u') q (𝒬 u) + dist_(u') ϑ (𝒬 u) + dist_(u') ϑ (𝒬 u') := by
      gcongr; apply dist_triangle_right
    _ < 1 + 100 + 100 := by
      gcongr
      · rwa [xye] at mq
      · rwa [@mem_ball, xye] at ϑx
      · rwa [@mem_ball] at ϑy
    _ < _ := by norm_num

/-- Lemma 5.4.5, verifying (2.0.33) -/
lemma forest_convex : OrdConnected (𝔗₂ k n j u) := by
  rw [ordConnected_def]; intro p mp p'' mp'' p' mp'
  have mp'₅ : p' ∈ ℭ₅ (X := X) k n j :=
    (ordConnected_C5.out ((𝔗₂_subset_ℭ₆.trans ℭ₆_subset_ℭ₅) mp)
      ((𝔗₂_subset_ℭ₆.trans ℭ₆_subset_ℭ₅) mp'')) mp'
  have mp'₆ : p' ∈ ℭ₆ k n j := by
    have hp := 𝔗₂_subset_ℭ₆ mp; rw [ℭ₆, mem_setOf] at hp ⊢
    refine ⟨mp'₅, ?_⟩; have hpG := hp.2; contrapose! hpG
    exact mp'.1.1.1.trans hpG
  simp_rw [𝔗₂, mem_inter_iff, mp'₆, true_and, mem_iUnion₂, mem_iUnion] at mp'' ⊢
  obtain ⟨u', mu', ru, _, np'', sl⟩ := mp''.2
  have pnu : 𝓘 p' < 𝓘 u' := (mp'.2.1).trans_lt (lt_of_le_of_ne sl.1 np'')
  use u', mu', ru; rw [𝔗₁, mem_setOf]
  use (ℭ₅_subset_ℭ₄ |>.trans ℭ₄_subset_ℭ₃ |>.trans ℭ₃_subset_ℭ₂ |>.trans ℭ₂_subset_ℭ₁) mp'₅, pnu.ne
  exact (wiggle_order_11_10 mp'.2 (C5_3_3_le (X := X).trans (by norm_num))).trans sl

/-- Lemma 5.4.6, verifying (2.0.36)
Note: swapped `u` and `u'` to match (2.0.36) -/
lemma forest_separation (hu : u ∈ 𝔘₃ k n j) (hu' : u' ∈ 𝔘₃ k n j) (huu' : u ≠ u')
    (hp : p ∈ 𝔗₂ k n j u') (h : 𝓘 p ≤ 𝓘 u) : 2 ^ (Z * (n + 1)) < dist_(p) (𝒬 p) (𝒬 u) := by
  simp_rw [𝔗₂, mem_inter_iff, mem_iUnion₂, mem_iUnion] at hp
  obtain ⟨mp₆, v, mv, rv, ⟨-, np, sl⟩⟩ := hp
  obtain ⟨p', mp', lp', sp'⟩ := exists_scale_add_le_of_mem_layersAbove <|
    (ℭ₆_subset_ℭ₅ |>.trans ℭ₅_subset_ℭ₄ |>.trans ℭ₄_subset_ℭ₃ |>.trans ℭ₃_subset_ℭ₂) mp₆
  have np'u : ¬URel k n j v u := by
    by_contra h; apply absurd (Eq.symm _) huu'
    replace h := equivalenceOn_urel.trans (𝔘₃_subset_𝔘₂ hu') mv (𝔘₃_subset_𝔘₂ hu) rv h
    exact EquivalenceOn.reprs_inj hu' hu h
  have vnu : v ≠ u := by by_contra h; subst h; exact absurd URel.rfl np'u
  simp_rw [URel, vnu, false_or, not_exists, not_and] at np'u
  have mpt : p' ∈ 𝔗₁ k n j v := by
    refine ⟨minLayer_subset mp', ?_, ?_⟩
    · exact (lp'.1.trans_lt (lt_of_le_of_ne sl.1 np)).ne
    · exact (wiggle_order_11_10 lp' (C5_3_3_le (X := X).trans (by norm_num))).trans sl
  specialize np'u p' mpt
  have 𝓘p'u : 𝓘 p' ≤ 𝓘 u := lp'.1.trans h
  simp_rw [TileLike.le_def, smul_fst, smul_snd, 𝓘p'u, true_and,
    not_subset_iff_exists_mem_not_mem] at np'u
  obtain ⟨(q : Θ X), mq, nq⟩ := np'u
  simp_rw [mem_ball, not_lt] at mq nq
  have d8 : 8 < dist_(p') (𝒬 p) (𝒬 u) :=
    calc
      _ = 10 - 1 - 1 := by norm_num
      _ < 10 - 1 - dist_(u) q (𝒬 u) := by gcongr
      _ ≤ 10 - 1 - dist_(p') q (𝒬 u) := tsub_le_tsub_left (Grid.dist_mono 𝓘p'u) _
      _ ≤ dist_(p') q (𝒬 p') - 1 - dist_(p') q (𝒬 u) := by gcongr
      _ < dist_(p') q (𝒬 p') - dist_(p') (𝒬 p) (𝒬 p') - dist_(p') q (𝒬 u) := by
        gcongr; rw [← @mem_ball]; exact subset_cball (lp'.2 𝒬_mem_Ω)
      _ ≤ _ := by
        rw [sub_le_iff_le_add', sub_le_iff_le_add]
        nth_rw 3 [dist_comm]; apply dist_triangle4
  have Znpos : 0 < Z * (n + 1) := by rw [defaultZ]; positivity
  let d : ℕ := (𝔰 p - 𝔰 p').toNat
  have sd : 𝔰 p' + d = 𝔰 p := by simp_rw [d]; rw [Int.toNat_sub_of_le] <;> omega
  have d1 : dist_(p') (𝒬 p) (𝒬 u) ≤ C2_1_2 a ^ d * dist_(p) (𝒬 p) (𝒬 u) :=
    Grid.dist_strictMono_iterate lp'.1 sd
  have Cdpos : 0 < C2_1_2 a ^ d := by rw [C2_1_2]; positivity
  have Cidpos : 0 < (C2_1_2 a)⁻¹ ^ d := by rw [C2_1_2]; positivity
  calc
    _ ≤ (C2_1_2 a)⁻¹ ^ (Z * (n + 1)) := by
      refine pow_le_pow_left₀ zero_le_two ?_ _
      nth_rw 1 [C2_1_2, ← Real.inv_rpow zero_le_two, ← Real.rpow_neg_one,
        ← Real.rpow_mul zero_le_two, neg_one_mul, neg_mul, neg_neg, ← Real.rpow_one 2]
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      norm_cast; linarith [four_le_a X]
    _ ≤ (C2_1_2 a)⁻¹ ^ d := by
      refine pow_le_pow_right₀ ?_ (by omega)
      simp_rw [one_le_inv_iff₀, C2_1_2_le_one (X := X), and_true, C2_1_2]; positivity
    _ ≤ (C2_1_2 a)⁻¹ ^ d * 8 := by nth_rw 1 [← mul_one (_ ^ d)]; gcongr; norm_num
    _ < (C2_1_2 a)⁻¹ ^ d * dist_(p') (𝒬 p) (𝒬 u) := by gcongr
    _ ≤ _ := by
      rwa [← mul_le_mul_iff_of_pos_left Cdpos, inv_pow, ← mul_assoc, mul_inv_cancel₀ Cdpos.ne',
        one_mul]

/-- Lemma 5.4.7, verifying (2.0.37) -/
lemma forest_inner (hu : u ∈ 𝔘₃ k n j) (hp : p ∈ 𝔗₂ k n j u) :
    ball (𝔠 p) (8 * D ^ 𝔰 p) ⊆ 𝓘 u := by
  have p₄ := (𝔗₂_subset_ℭ₆.trans ℭ₆_subset_ℭ₅ |>.trans ℭ₅_subset_ℭ₄) hp
  have p₁ := (ℭ₄_subset_ℭ₃.trans ℭ₃_subset_ℭ₂ |>.trans ℭ₂_subset_ℭ₁) p₄
  obtain ⟨q, mq, lq, sq⟩ := exists_le_add_scale_of_mem_layersBelow p₄
  obtain ⟨-, u'', mu'', nu'', sl⟩ := ℭ₃_def.mp (maxLayer_subset mq)
  replace nu'' : 𝓘 q < 𝓘 u'' := lt_of_le_of_ne sl.1 nu''
  have s2 : smul 2 p ≤ smul 2 q := wiggle_order_11_10 lq (C5_3_3_le (X := X).trans (by norm_num))
  have s2' : smul 2 p ≤ smul 1 u'' := s2.trans sl
  have s10 : smul 10 p ≤ smul 1 u'' := smul_mono s2' le_rfl (by norm_num)
  simp_rw [𝔗₂, mem_inter_iff, mem_iUnion₂, mem_iUnion] at hp
  obtain ⟨p₆, u', mu', ru', pu'⟩ := hp
  have ur : URel k n j u' u'' := Or.inr ⟨p, pu', s10⟩
  have hu'' : u'' ∈ 𝔘₂ k n j := by
    rw [𝔘₂, mem_setOf, not_disjoint_iff]
    refine ⟨mu'', ⟨p, ?_, p₆⟩⟩
    simpa [𝔗₁, p₁, s2'] using (lq.1.trans_lt nu'').ne
  have ru'' : URel k n j u u'' := equivalenceOn_urel.trans (𝔘₃_subset_𝔘₂ hu) mu' hu'' ru' ur
  have qlu : 𝓘 q < 𝓘 u := URel.eq (𝔘₃_subset_𝔘₂ hu) hu'' ru'' ▸ nu''
  have squ : 𝔰 q < 𝔰 u := (Grid.lt_def.mp qlu).2
  have spu : 𝔰 p ≤ 𝔰 u - (Z * (n + 1) : ℕ) - 1 := by omega
  have ⟨I, sI, plI, Ilu⟩ : ∃ I, s I = 𝔰 u - (Z * (n + 1) : ℕ) - 1 ∧ 𝓘 p ≤ I ∧ I ≤ 𝓘 u := by
    apply Grid.exists_sandwiched (lq.1.trans qlu.le) (𝔰 u - (Z * (n + 1) : ℕ) - 1)
    refine ⟨spu, ?_⟩
    change _ ≤ 𝔰 u
    omega
  have bI : I ∉ 𝓛 n u := by
    have p₅ := ℭ₆_subset_ℭ₅ p₆
    rw [ℭ₅_def] at p₅; replace p₅ := p₅.2; contrapose! p₅
    use u, (𝔘₃_subset_𝔘₂.trans 𝔘₂_subset_𝔘₁) hu, plI.1.trans (subset_biUnion_of_mem p₅)
  rw [𝓛, mem_setOf, not_and] at bI; specialize bI Ilu
  rw [not_and, not_not] at bI; specialize bI (by omega); rw [← sI] at spu
  rcases spu.eq_or_lt with h | h
  · have hI : 𝓘 p = I := by
      apply eq_of_le_of_not_lt plI; rw [Grid.lt_def, not_and_or, not_lt]; exact Or.inr h.symm.le
    rwa [← hI] at bI
  · apply subset_trans (ball_subset_ball' _) bI
    have ds : c (𝓘 p) ∈ ball (c I) (4 * D ^ s I) := (plI.1.trans Grid_subset_ball) Grid.c_mem_Grid
    rw [mem_ball] at ds
    calc
      _ ≤ 4 * D * (D : ℝ) ^ 𝔰 p + 4 * D ^ s I := by
        gcongr
        · linarith [four_le_realD X]
        · exact ds.le
      _ = 4 * D ^ (𝔰 p + 1) + 4 * D ^ s I := by
        rw [mul_assoc]; congr; rw [mul_comm, ← zpow_add_one₀ (defaultD_pos _).ne']
      _ ≤ 4 * D ^ s I + 4 * D ^ s I := by
        gcongr
        · exact one_le_D
        · omega
      _ = _ := by ring

/-- The multiplicity appearing in Lemma 5.4.8. -/
def C5_4_8 (n : ℕ) : ℕ := (4 * n + 12) * 2 ^ n

lemma exists_smul_le_of_𝔘₃ (u : 𝔘₃ k n j) : ∃ m : 𝔐 (X := X) k n, smul 100 u.1 ≤ smul 1 m.1 := by
  obtain ⟨u, mu⟩ := u
  replace mu := (𝔘₃_subset_𝔘₂.trans 𝔘₂_subset_𝔘₁ |>.trans 𝔘₁_subset_ℭ₁) mu
  rw [ℭ₁, mem_diff, preℭ₁, mem_setOf, filter_mem_univ_eq_toFinset] at mu
  replace mu := (show 0 < 2 ^ j by positivity).trans_le mu.1.2
  rw [Finset.card_pos] at mu; obtain ⟨m, hm⟩ := mu
  rw [mem_toFinset, 𝔅] at hm; exact ⟨⟨m, hm.1⟩, hm.2⟩

variable (k n j) in
/-- The good choice of an element to get a contradiction in the proof of Lemma 5.4.8. -/
def mf (u : 𝔘₃ (X := X) k n j) : 𝔐 (X := X) k n := (exists_smul_le_of_𝔘₃ u).choose

lemma mf_injOn : InjOn (mf k n j) {u | x ∈ 𝓘 u.1} := fun u mu u' mu' e ↦ by
  set m := mf k n j u
  have iu : smul 100 u.1 ≤ smul 1 m.1 := (exists_smul_le_of_𝔘₃ u).choose_spec
  have iu' : smul 100 u'.1 ≤ smul 1 m.1 := e ▸ (exists_smul_le_of_𝔘₃ u').choose_spec
  have su : ball_{𝓘 m.1} (𝒬 m.1) 1 ⊆ ball_{𝓘 u.1} (𝒬 u.1) 100 := iu.2
  have su' : ball_{𝓘 m.1} (𝒬 m.1) 1 ⊆ ball_{𝓘 u'.1} (𝒬 u'.1) 100 := iu'.2
  have nd : ¬Disjoint (ball_{𝓘 u.1} (𝒬 u.1) 100) (ball_{𝓘 u'.1} (𝒬 u'.1) 100) := by
    rw [not_disjoint_iff]
    use 𝒬 m.1, su (mem_ball_self zero_lt_one), su' (mem_ball_self zero_lt_one)
  by_contra! h; rw [← Subtype.coe_ne_coe] at h; apply absurd _ nd
  have nr : ¬URel k n j u.1 u'.1 := by contrapose! h; exact EquivalenceOn.reprs_inj u.2 u'.2 h
  have n𝓘 : 𝓘 u.1 ≠ 𝓘 u'.1 := by
    contrapose! nr; rw [disjoint_comm] at nd
    exact urel_of_not_disjoint (𝔘₃_subset_𝔘₂ u.2) nr.symm nd
  rcases le_or_lt (s (𝓘 u.1)) (s (𝓘 u'.1)) with hs | hs
  · have hu := lt_of_le_of_ne ((le_or_disjoint hs).resolve_right
      (not_disjoint_iff.mpr ⟨_, mu, mu'⟩)) n𝓘
    have u₁ := (𝔘₃_subset_𝔘₂.trans 𝔘₂_subset_𝔘₁) u.2
    exact u₁.2 u' ((𝔘₃_subset_𝔘₂.trans 𝔘₂_subset_𝔘₁ |>.trans 𝔘₁_subset_ℭ₁) u'.2) hu
  · have hu := lt_of_le_of_ne ((le_or_disjoint hs.le).resolve_right
      (not_disjoint_iff.mpr ⟨_, mu', mu⟩)) n𝓘.symm
    have u'₁ := (𝔘₃_subset_𝔘₂.trans 𝔘₂_subset_𝔘₁) u'.2
    exact (u'₁.2 u ((𝔘₃_subset_𝔘₂.trans 𝔘₂_subset_𝔘₁ |>.trans 𝔘₁_subset_ℭ₁) u.2) hu).symm

lemma stackSize_𝔘₃_le_𝔐 (x : X) : stackSize (𝔘₃ k n j) x ≤ stackSize (𝔐 k n) x := by
  let mf' : 𝔓 X → 𝔓 X := fun u ↦ if mu : u ∈ 𝔘₃ k n j then mf k n j ⟨u, mu⟩ else default
  simp_rw [stackSize, indicator_apply, Pi.one_apply, Finset.sum_boole, Nat.cast_id]
  refine Finset.card_le_card_of_injOn mf' (fun u mu ↦ ?_) (fun u mu u' mu' e ↦ ?_)
  · simp_rw [Finset.mem_filter, Finset.mem_univ, true_and] at mu ⊢
    simp_rw [mf', mu.1, dite_true]
    have hu : 𝓘 u ≤ 𝓘 (mf k n j ⟨u, mu.1⟩) := (exists_smul_le_of_𝔘₃ ⟨u, mu.1⟩).choose_spec.1
    exact ⟨(mf k n j ⟨u, mu.1⟩).2, hu.1 mu.2⟩
  · simp_rw [Finset.coe_filter, mem_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at mu mu'
    simp_rw [mf', mu.1, mu'.1, dite_true, Subtype.val_inj] at e
    simpa using mf_injOn mu.2 mu'.2 e

/-- Lemma 5.4.8, used to verify that 𝔘₄ satisfies 2.0.34. -/
lemma forest_stacking (x : X) (hkn : k ≤ n) : stackSize (𝔘₃ (X := X) k n j) x ≤ C5_4_8 n := by
  by_contra! h
  let C : Finset (𝔓 X) := { u | u ∈ 𝔘₃ (X := X) k n j ∧ x ∈ 𝓘 u }
  have Cc : C.card = stackSize (𝔘₃ k n j) x := by
    simp_rw [stackSize, indicator_apply, Pi.one_apply, Finset.sum_boole, Nat.cast_id,
      C, Grid.mem_def, Finset.filter_filter]
  have Cn : C.Nonempty := by
    by_contra! Ce; rw [Finset.not_nonempty_iff_eq_empty] at Ce
    simp_rw [← Cc, Ce, Finset.card_empty, not_lt_zero'] at h
  let C' : Finset (Grid X) := C.image 𝓘
  have C'n : C'.Nonempty := by rwa [Finset.image_nonempty]
  obtain ⟨i, mi, li⟩ := C'.exists_minimal C'n
  simp_rw [C', Finset.mem_image, C, Finset.mem_filter, Finset.mem_univ, true_and] at mi
  obtain ⟨u, ⟨mu, mx⟩, uei⟩ := mi; subst uei
  have uA : (𝓘 u : Set X) ⊆ setA (2 * n + 6) k n := fun y my ↦
    calc
      _ = (4 * n + 12) * 2 ^ n := by ring
      _ < stackSize (𝔘₃ k n j) x := h
      _ ≤ stackSize (𝔘₃ k n j) y := by
        simp_rw [stackSize, indicator_apply, Pi.one_apply, Finset.sum_boole, Nat.cast_id]
        apply Finset.card_le_card fun v mv ↦ ?_
        simp_rw [Finset.mem_filter, Finset.mem_univ, true_and] at mv ⊢
        have mvC' : 𝓘 v ∈ C' := by
          simp_rw [C', Finset.mem_image]; use v
          simp_rw [C, Finset.mem_filter, Finset.mem_univ, true_and, and_true]; exact mv
        specialize li _ mvC'
        have inc := (or_assoc.mpr (le_or_ge_or_disjoint (i := 𝓘 u) (j := 𝓘 v))).resolve_right
          (not_disjoint_iff.mpr ⟨_, mx, mv.2⟩)
        simp_rw [le_iff_eq_or_lt] at inc
        replace inc : 𝓘 u = 𝓘 v ∨ 𝓘 u < 𝓘 v := by tauto
        rw [← le_iff_eq_or_lt] at inc
        exact ⟨mv.1, inc.1 my⟩
      _ ≤ _ := stackSize_𝔘₃_le_𝔐 _
  refine absurd (disjoint_left.mpr fun v mv ↦ ?_) (𝔘₃_subset_𝔘₂ mu).2
  rw [𝔗₁, mem_setOf] at mv; rw [ℭ₆, mem_setOf, not_and, not_not]
  refine fun _ ↦ (mv.2.2.1).1.trans ?_
  calc
    _ ⊆ setA (2 * n + 6) k n := uA
    _ ⊆ G₂ := subset_iUnion₂_of_subset n k (subset_iUnion_of_subset hkn subset_rfl)
    _ ⊆ _ := subset_union_of_subset_left subset_union_right G₃

/-- Define `𝔘₄ k n j l` as the union of `2 ^ n` disjoint subfamilies in `𝔘₃ k n j`, to make sure
the multiplicity is at most `2 ^ n` to get a forest. -/
def 𝔘₄ (k n j l : ℕ) : Set (𝔓 X) :=
  ⋃ i ∈ Ico (l * 2 ^ n) ((l + 1) * 2 ^ n), iteratedMaximalSubfamily (𝔘₃ k n j) i

lemma 𝔘₄_subset_𝔘₃ {k n j l} : 𝔘₄ (X := X) k n j l ⊆ 𝔘₃ k n j := by
  simp [𝔘₄, iteratedMaximalSubfamily_subset]

/-- The sets `(𝔘₄(k, n, j, l))_l` form a partition of `𝔘₃ k n j`. -/
lemma iUnion_𝔘₄ (hkn : k ≤ n) : ⋃ l ∈ Iio (4 * n + 12), 𝔘₄ (X := X) k n j l = 𝔘₃ k n j := by
  have : ⋃ l ∈ Iio (4 * n + 12), 𝔘₄ (X := X) k n j l =
      ⋃ i < (4 * n + 12) * 2 ^ n, iteratedMaximalSubfamily (𝔘₃ k n j) i := by
    apply Subset.antisymm
    · simp only [mem_Iio, 𝔘₄, mem_Ico, biUnion_and', iUnion_subset_iff]
      intro l i hi hl h'i
      apply subset_biUnion_of_mem
      change i + 1 ≤ (4 * n + 12) * 2 ^ n
      suffices i < (4 * n + 12) * 2 ^ n by omega
      exact h'i.trans_le (mul_le_mul' (by omega) le_rfl)
    · simp only [𝔘₄, iUnion_subset_iff]
      intro i hi
      let l := i / 2 ^ n
      have : iteratedMaximalSubfamily (𝔘₃ k n j) i ⊆ ⋃ i ∈ Ico (l * 2 ^ n) ((l + 1) * 2 ^ n),
          iteratedMaximalSubfamily (X := X) (𝔘₃ k n j) i := by
        apply subset_biUnion_of_mem
        refine ⟨Nat.div_mul_le_self _ _, ?_⟩
        rw [← Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)]
        exact lt_add_one _
      apply this.trans
      apply subset_biUnion_of_mem (u := fun l ↦
        ⋃ i ∈ Ico (l * 2 ^ n) ((l + 1) * 2 ^ n), iteratedMaximalSubfamily (𝔘₃ k n j) i)
      simp only [mem_Iio, l]
      rwa [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)]
  rw [this, eq_comm]
  apply eq_biUnion_iteratedMaximalSubfamily
  intro x
  apply forest_stacking x hkn

lemma C6_forest' (hkn : k ≤ n) :
    ℭ₆ (X := X) k n j = ⋃ l ∈ Iio (4 * n + 12), ⋃ u ∈ 𝔘₄ k n j l, 𝔗₂ k n j u := by
  rw [C6_forest, ← iUnion_𝔘₄ hkn]
  simp

lemma pairwiseDisjoint_𝔘₄ : univ.PairwiseDisjoint (𝔘₄ (X := X) k n j) := by
  intro l hl m hm hml
  apply disjoint_iff_forall_ne.2 (fun x hx y hy ↦ ?_)
  simp only [𝔘₄, mem_Ico, mem_iUnion, exists_prop] at hx hy
  rcases hx with ⟨a, ⟨ha, h'a⟩, xa⟩
  rcases hy with ⟨b, ⟨hb, h'b⟩, yb⟩
  have h : a ≠ b := by
    rcases lt_or_gt_of_ne hml with h | h
    · exact (h'a.trans_le (le_trans (mul_le_mul' h le_rfl) hb)).ne
    · exact (h'b.trans_le (le_trans (mul_le_mul' h le_rfl) ha)).ne'
  have := pairwiseDisjoint_iteratedMaximalSubfamily (𝔘₃ (X := X) k n j) (mem_univ a) (mem_univ b) h
  exact disjoint_iff_forall_ne.1 this xa yb

lemma stackSize_𝔘₄_le (x : X) : stackSize (𝔘₄ (X := X) k n j l) x ≤ 2 ^ n := calc
  stackSize (𝔘₄ (X := X) k n j l) x
  _ = ∑ i ∈ Finset.Ico (l * 2 ^ n) ((l + 1) * 2 ^ n),
        stackSize (iteratedMaximalSubfamily (𝔘₃ k n j) i) x := by
    simp only [stackSize, 𝔘₄]
    rw [← Finset.sum_biUnion]; swap
    · intro a ha b hb hab
      apply Finset.disjoint_coe.1
      apply disjoint_iff_forall_ne.2 (fun p hp q hq ↦ ?_)
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, setOf_mem_eq] at hp hq
      have := pairwiseDisjoint_iteratedMaximalSubfamily (𝔘₃ (X := X) k n j)
        (mem_univ a) (mem_univ b) hab
      exact disjoint_iff_forall_ne.1 this hp hq
    congr
    ext p
    simp
  _ ≤ ∑ i ∈ Finset.Ico (l * 2 ^ n) ((l + 1) * 2 ^ n), 1 := by
    gcongr with i hi
    apply stackSize_le_one_of_pairwiseDisjoint
    apply pairwiseDisjoint_iteratedMaximalSubfamily_image
  _ = 2 ^ n := by simp [add_mul]

open TileStructure
variable (k n j l) in
/-- The forest based on `𝔘₄ k n j l`. -/
def forest : Forest X n where
  𝔘 := 𝔘₄ k n j l
  𝔗 := 𝔗₂ k n j
  nonempty' {u} hu := by
    have m : u ∈ 𝔘₂ k n j := (𝔘₃_subset_𝔘₂ (𝔘₄_subset_𝔘₃ hu))
    have : ℭ₆ k n j ∩ 𝔗₁ k n j u ⊆ 𝔗₂ k n j u := by
      apply inter_subset_inter_right
      have : 𝔗₁ k n j u ⊆ ⋃ (_ : URel k n j u u), 𝔗₁ k n j u := by
        have : URel k n j u u := (equivalenceOn_urel (X := X)).refl _ m
        simp [this]
      apply this.trans
      apply subset_biUnion_of_mem (u := fun u' ↦ ⋃ (_ : URel k n j u u'), 𝔗₁ k n j u') m
    apply Nonempty.mono this
    rw [inter_comm]
    simp only [𝔘₂, not_disjoint_iff_nonempty_inter, mem_setOf_eq] at m
    exact m.2
  ordConnected' {u} hu := forest_convex
  𝓘_ne_𝓘' {u} hu p hp := by
    have := hp.2
    simp only [mem_iUnion, exists_prop, exists_and_left] at this
    rcases this with ⟨u', hu', u'rel, hu'I⟩
    rw [URel.eq (𝔘₃_subset_𝔘₂ (𝔘₄_subset_𝔘₃ hu)) hu' u'rel]
    exact (𝓘_lt_of_mem_𝔗₁ hu'I).ne
  smul_four_le' {u} hu := forest_geometry <| 𝔘₄_subset_𝔘₃ hu
  stackSize_le' {x} := stackSize_𝔘₄_le x
  dens₁_𝔗_le' {u} hu := dens1_le <| 𝔗₂_subset_ℭ₆.trans ℭ₆_subset_ℭ
  lt_dist' hu hu' huu' p hp := forest_separation (𝔘₄_subset_𝔘₃ hu) (𝔘₄_subset_𝔘₃ hu') huu' hp
  ball_subset' hu p hp := forest_inner (𝔘₄_subset_𝔘₃ hu) hp

/-- From the fact that the `ℭ₅ k n j` are disjoint, one can rewrite the whole Carleson sum over
`𝔓₁` (the union of the `ℭ₅ k n j`) as a sum of Carleson sums over the `ℭ₅ k n j`. -/
lemma carlesonSum_𝔓₁_eq_sum {f : X → ℂ} {x : X} :
    carlesonSum 𝔓₁ f x = ∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3, carlesonSum (ℭ₅ k n j) f x := by
  simp only [Finset.sum_sigma']
  rw [sum_carlesonSum_of_pairwiseDisjoint]; swap
  · rintro ⟨n, k, j⟩ - ⟨n', k', j'⟩ - h
    simp only [ne_eq, Sigma.mk.inj_iff, heq_eq_eq] at h
    simp only [Function.onFun, Finset.disjoint_filter, Finset.mem_univ, forall_const]
    have W := pairwiseDisjoint_ℭ₅ (X := X) (mem_univ ⟨k, n, j⟩) (mem_univ ⟨k', n', j'⟩)
      (by simp [-not_and]; tauto)
    simpa [Function.onFun, disjoint_left] using W
  congr
  ext p
  simp only [𝔓₁, mem_iUnion, exists_prop, Finset.mem_sigma, Finset.mem_Iic, Sigma.exists]
  constructor
  · rintro ⟨n, k, hk, j, hj, hp⟩
    refine ⟨n, k, j, ⟨?_, hk, hj⟩, hp⟩
    have : (ℭ (X := X) k n).Nonempty := ⟨p, ℭ₅_subset_ℭ hp⟩
    exact le_maxℭ_of_nonempty this
  · rintro ⟨n, k, j, ⟨hn, hk, hj⟩, hp⟩
    exact ⟨n, k, hk, j, hj, hp⟩

/-- The Carleson sum over `ℭ₅` and `ℭ₆` coincide, for points in `G \ G'`. -/
lemma carlesonSum_ℭ₅_eq_ℭ₆ {f : X → ℂ} {x : X} (hx : x ∈ G \ G') {k n j : ℕ} :
    carlesonSum (ℭ₅ k n j) f x = carlesonSum (ℭ₆ k n j) f x := by
  simp only [carlesonSum]
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [mem_iUnion, exists_prop, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ℭ₆_subset_ℭ₅ hp
  · intro p hp h'p
    simp only [mem_iUnion, exists_prop, Finset.mem_filter,
      Finset.mem_univ, true_and, not_exists, not_and] at hp h'p
    have : x ∉ 𝓘 p := by
      simp only [ℭ₆, mem_setOf_eq, not_and, Decidable.not_not] at h'p
      intro h'x
      exact hx.2 (h'p hp h'x)
    have : x ∉ E p := by simp at this; simp [E, this]
    simp [carlesonOn, this]

/-- The Carleson sum over `ℭ₆` can be decomposed as a sum over `4 n + 12` forests
based on `𝔘₄ k n j l`. -/
lemma carlesonSum_ℭ₆_eq_sum {f : X → ℂ} {x : X} {k n j : ℕ} (hkn : k ≤ n) :
    carlesonSum (ℭ₆ k n j) f x =
      ∑ l < 4 * n + 12, carlesonSum (⋃ u ∈ 𝔘₄ k n j l, 𝔗₂ k n j u) f x := by
  rw [sum_carlesonSum_of_pairwiseDisjoint]; swap
  · intro a ha b hb hab
    simp only [Function.onFun, disjoint_iff_forall_ne, mem_iUnion, exists_prop, ne_eq,
      forall_exists_index, and_imp]
    intro q p hp hq q' p' hp' hq'
    have := pairwiseDisjoint_𝔘₄ (X := X) (k := k) (n := n) (j := j) (mem_univ a) (mem_univ b) hab
    have : p ≠ p' := disjoint_iff_forall_ne.1 this hp hp'
    have := forest_disjoint (𝔘₄_subset_𝔘₃ hp) (𝔘₄_subset_𝔘₃ hp') this
    exact disjoint_iff_forall_ne.1 this hq hq'
  congr
  ext p
  simp [C6_forest' hkn]

/-- For each forest, the integral of the norm of the Carleson sum can be controlled thanks to
the forest theorem and to the density control coming from the fact we are away from `G₁`. -/
lemma lintegral_carlesonSum_forest
    {f : X → ℂ} (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G \ G', ‖carlesonSum (⋃ u ∈ 𝔘₄ k n j l, 𝔗₂ k n j u) f x‖₊ ≤
    C2_0_4 a q n * (2 ^ (2 * a + 5) * volume F / volume G) ^ (q⁻¹ - 2⁻¹) *
    (volume F) ^ (1/2 : ℝ) * (volume G) ^ (1/2 : ℝ) := by
  let 𝔉 := forest (X := X) k n j l
  have : ∫⁻ x in G \ G', ‖carlesonSum (⋃ u ∈ 𝔘₄ k n j l, 𝔗₂ k n j u) f x‖₊ =
      ∫⁻ x in G \ G', ‖∑ u ∈ { p | p ∈ 𝔉 }, carlesonSum (𝔉 u) f x‖₊ := by
    congr with x
    congr
    rw [sum_carlesonSum_of_pairwiseDisjoint]; swap
    · intro a ha b hb hab
      simp only [Function.onFun, disjoint_iff_forall_ne]
      intro x hx y hy
      simp only [forest, Forest.mem_mk, Finset.coe_filter, Finset.mem_univ, true_and, setOf_mem_eq,
        𝔉] at ha hb hx hy
      have := forest_disjoint (X := X) (𝔘₄_subset_𝔘₃ ha) (𝔘₄_subset_𝔘₃ hb) hab
      exact disjoint_iff_forall_ne.1 this hx hy
    congr with p
    simp only [mem_iUnion, exists_prop, Finset.mem_filter,
      Finset.mem_univ, true_and, forest, Finset.mem_biUnion, 𝔉]
    exact Iff.rfl
  rw [this]
  have W := forest_operator_le_volume 𝔉 hf h2f (A := G \ G') (measurableSet_G.diff measurable_G')
    (isBounded_G.subset diff_subset)
  apply W.trans
  gcongr
  · simp only [sub_nonneg, ge_iff_le, inv_le_inv₀ zero_lt_two (q_pos X)]
    exact (q_mem_Ioc (X := X)).2
  · rw [dens₂_eq_biSup_dens₂]
    simp only [mem_iUnion, exists_prop, iSup_exists, iSup_le_iff, and_imp]
    intro p q hq hp
    replace hp : p ∈ ℭ₆ k n j := 𝔗₂_subset_ℭ₆ hp
    have : ¬ (𝓘 p : Set X) ⊆ G₁ := by
      have W := hp.2
      contrapose! W
      exact W.trans (subset_union_left.trans subset_union_left)
    contrapose! this
    have : p ∈ highDensityTiles := by simp [highDensityTiles, this]
    apply subset_biUnion_of_mem this
  · exact diff_subset

/-- For each forest, the integral of the norm of the Carleson sum can be controlled thanks to
the forest theorem and to the density control coming from the fact we are away from `G₁`. Second
version, with the volume of `F`. -/
lemma lintegral_carlesonSum_forest'
    {f : X → ℂ} (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G \ G', ‖carlesonSum (⋃ u ∈ 𝔘₄ k n j l, 𝔗₂ k n j u) f x‖₊ ≤
    C2_0_4 a q n * 2 ^ (a + 5/2 : ℝ) * (volume G) ^ (1 - q⁻¹) * (volume F) ^ (q⁻¹) := by
  apply (lintegral_carlesonSum_forest hf h2f).trans
  simp only [mul_assoc]
  apply mul_le_mul_left'
  simp only [div_eq_mul_inv, one_mul, ENNReal.mul_rpow_of_nonneg _ _ (inv_q_sub_half_nonneg X),
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  calc
  2 ^ ((2 * a + 5 : ℕ) * (q⁻¹ - 2⁻¹)) * volume F ^ (q⁻¹ - 2⁻¹) * (volume G)⁻¹ ^ (q⁻¹ - 2⁻¹) *
    (volume F ^ (2⁻¹ : ℝ) * volume G ^ (2⁻¹ : ℝ))
  _ ≤ 2 ^ (a + 5/2 : ℝ) * volume F ^ (q⁻¹ - 2⁻¹) * (volume G)⁻¹ ^ (q⁻¹ - 2⁻¹) *
    ((volume F) ^ (2⁻¹ : ℝ) * volume G ^ (2⁻¹ : ℝ)) := by
    gcongr
    · exact one_le_two
    have : 1 ≤ q := (one_lt_q X).le
    have : (2 * a + 5 : ℕ) * (q⁻¹ - 2⁻¹) ≤ (2 * a + 5 : ℕ) * (1⁻¹ - 2⁻¹) := by gcongr
    apply this.trans_eq
    norm_num
    simp [add_mul, div_eq_mul_inv]
    ring
  _ = 2 ^ (a + 5/2 : ℝ) * (volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹) := by
    have IF : (volume F) ^ (q⁻¹) = (volume F) ^ ((q ⁻¹ - 2⁻¹) + 2⁻¹) := by congr; abel
    have IG : (volume G) ^ (1 - q⁻¹) = (volume G) ^ (2⁻¹ - (q⁻¹ - 2⁻¹)) := by
      congr 1
      simp only [sub_sub_eq_add_sub, sub_left_inj]
      norm_num
    rw [IF, IG, ENNReal.rpow_sub _ _ ProofData.volume_G_pos.ne' volume_G_ne_top,
      ENNReal.rpow_add_of_nonneg (x := volume F) _ _ (inv_q_sub_half_nonneg X) (by norm_num),
      ENNReal.div_eq_inv_mul, ENNReal.inv_rpow]
    ring

/-- Putting all the above decompositions together, one obtains a control of the integral of the
full Carleson sum over `𝔓₁`, as a sum over all the forests. -/
lemma forest_union_aux {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (h'f : Measurable f) :
    ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ f x‖₊ ≤ C2_0_4_base a * 2 ^ (a + 5/2 : ℝ) *
         (volume G) ^ (1 - q⁻¹) * (volume F) ^ (q⁻¹) *
        ∑ n ≤ maxℭ X, ∑ _k ≤ n, ∑ _j ≤ 2 * n + 3, ∑ _l < 4 * n + 12,
          (2 : ℝ≥0∞) ^ (- (q - 1) / q * n : ℝ) := calc
  ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ f x‖₊
  _ ≤ ∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3, ∫⁻ x in G \ G', ‖carlesonSum (ℭ₅ k n j) f x‖₊ := by
    simp only [Finset.sum_sigma']
    rw [← lintegral_finset_sum']; swap
    · exact fun b hb ↦ h'f.aestronglyMeasurable.carlesonSum.restrict.enorm
    apply lintegral_mono (fun x ↦ ?_)
    simp only [Finset.sum_sigma', carlesonSum_𝔓₁_eq_sum]
    exact (ENNReal.coe_le_coe.2 (nnnorm_sum_le _ _)).trans_eq (by simp)
  _ = ∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3, ∫⁻ x in G \ G', ‖carlesonSum (ℭ₆ k n j) f x‖₊ := by
    congr with n
    congr with k
    congr with j
    apply setLIntegral_congr_fun (measurableSet_G.diff measurable_G')
    exact Filter.Eventually.of_forall (fun x hx ↦ by rw [carlesonSum_ℭ₅_eq_ℭ₆ hx])
  _ ≤ ∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3,
        ∑ l < 4 * n + 12, ∫⁻ x in G \ G', ‖carlesonSum (⋃ u ∈ 𝔘₄ k n j l, 𝔗₂ k n j u) f x‖₊ := by
    gcongr with n hn k hk j hj
    rw [← lintegral_finset_sum']; swap
    · exact fun b hb ↦ h'f.aestronglyMeasurable.carlesonSum.restrict.enorm
    apply lintegral_mono (fun x ↦ ?_)
    simp only [Finset.mem_Iic] at hk
    rw [carlesonSum_ℭ₆_eq_sum hk]
    exact (ENNReal.coe_le_coe.2 (nnnorm_sum_le _ _)).trans_eq (by simp)
  _ ≤ ∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3,
        ∑ l < 4 * n + 12, C2_0_4 a q n * 2 ^ (a + 5/2 : ℝ) *
          (volume G) ^ (1 - q⁻¹) * (volume F) ^ (q⁻¹) := by
    gcongr with n hn k hk j hj l hl
    apply lintegral_carlesonSum_forest' h'f hf
  _ = C2_0_4_base a * 2 ^ (a + 5/2 : ℝ) * (volume G) ^ (1 - q⁻¹) * (volume F) ^ (q⁻¹) *
        ∑ n ≤ maxℭ X, ∑ k ≤ n, ∑ j ≤ 2 * n + 3, ∑ l < 4 * n + 12,
          (2 : ℝ≥0∞) ^ (- (q - 1) / q * n : ℝ) := by
    have A n : (C2_0_4 a q n : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (- (q - 1) / q * n : ℝ) * C2_0_4_base a := by
      simp only [C2_0_4, neg_sub, mul_comm, ENNReal.coe_mul,
        ENNReal.coe_rpow_of_ne_zero two_ne_zero]
      rfl
    simp only [A, ← Finset.sum_mul]
    ring

/- It remains to bound the sum above, by a sum/integral comparison over `ℝ` and then a cast from
`ℝ` to `ℝ≥0∞`. We do that in the next two lemmas. -/

open scoped Nat
open Real

lemma forest_union_sum_aux1 (M : ℕ) (q : ℝ) (hq : 1 < q) (h'q : q ≤ 2) :
    ∑ n ≤ M, ∑ _k ≤ n, ∑ _j ≤ 2 * n + 3, ∑ _l < 4 * n + 12,
      (2 : ℝ) ^ (- ((q - 1) / q * n)) ≤ 13009 / (q - 1) ^ 4 := by
  have A (x : ℝ) : (x + 1) * (2 * x + 3 + 1) * (4 * x + 12)
      = 8 * x ^ 3 + 48 * x ^ 2 + 88 * x + 48:= by ring
  simp only [Finset.sum_const, Nat.card_Iio, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.card_Iic, Nat.cast_one, ← mul_assoc, A, ge_iff_le]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  have : 0 ≤ q - 1 := by linarith
  have : q - 1 ≤ 1 := by linarith
  have : 0.6931471803 ≤ Real.log 2 := Real.log_two_gt_d9.le
  let c := (q - 1) / q
  have hc : 0 < c := div_pos (by linarith) (by linarith)
  calc
  8 * ∑ i ∈ Finset.Iic M, i ^ 3 * (2 : ℝ) ^ (-(c * i))
    + 48 * ∑ i ∈ Finset.Iic M, i ^ 2 * (2 : ℝ) ^ (-(c * i))
    + 88 * ∑ i ∈ Finset.Iic M, i * (2 : ℝ) ^ (-(c * i))
    + 48 * ∑ i ∈ Finset.Iic M, (2 : ℝ) ^ (-(c * i))
  _ = 8 * ∑ i ∈ Finset.Iic M, i ^ 3 * (2 : ℝ) ^ (-(c * i))
      + 48 * ∑ i ∈ Finset.Iic M, i ^ 2 * (2 : ℝ) ^ (-(c * i))
      + 88 * ∑ i ∈ Finset.Iic M, i ^ 1  * (2 : ℝ) ^ (-(c * i))
      + 48 * ∑ i ∈ Finset.Iic M, i ^ 0 * (2 : ℝ) ^ (-(c * i)) := by simp
  _ ≤ 8 * (2 ^ c * 3 ! / (Real.log 2 * c) ^ (3 + 1))
      + 48 * (2 ^ c * 2 ! / (Real.log 2 * c) ^ (2 + 1))
      + 88 * (2 ^ c * 1 ! / (Real.log 2 * c) ^ (1 + 1))
      + 48 * (2 ^ c * 0! / (Real.log 2 * c) ^ (0 + 1)) := by
    gcongr <;> exact sum_Iic_pow_mul_two_pow_neg_le hc
  _ = (2 ^ c * (48 * q ^ 4 / (Real.log 2) ^ 4 + 96 * q^3 * (q - 1) / (Real.log 2) ^ 3
      + 88 * q ^ 2 * (q - 1) ^ 2 / (Real.log 2) ^ 2
      + 48 * q * (q - 1) ^ 3/ (Real.log 2))) / (q - 1) ^ 4 := by
    simp only [Nat.factorial, Nat.succ_eq_add_one, Nat.reduceAdd, zero_add, mul_one, Nat.reduceMul,
      Nat.cast_ofNat, mul_pow, div_pow, Nat.cast_one, pow_one, c]
    have : q - 1 ≠ 0 := by linarith
    field_simp only
    ring
  _ ≤ (2 ^ (1 : ℝ) * (48 * 2 ^ 4 / (Real.log 2) ^ 4 + 96 * 2 ^ 3 * 1 / (Real.log 2) ^ 3
      + 88 * 2 ^ 2 * 1 ^ 2 / (Real.log 2) ^ 2 + 48 * 2 * 1 ^ 3 / (Real.log 2))) / (q - 1) ^ 4 := by
    gcongr
    · exact one_le_two
    · rw [div_le_one (by linarith)]
      linarith
  _ ≤ (2 ^ (1 : ℝ) * (48 * 2 ^ 4 / 0.6931471803 ^ 4 + 96 * 2 ^ 3 * 1 / 0.6931471803 ^ 3
      + 88 * 2 ^ 2 * 1 ^ 2 / 0.6931471803 ^ 2 + 48 * 2 * 1 ^ 3 / 0.6931471803)) / (q - 1) ^ 4 := by
    gcongr
  _ ≤ 13009 / (q - 1) ^ 4 := by
    gcongr
    norm_num

lemma forest_union_sum_aux2 (M : ℕ) (q : ℝ) (hq : 1 < q) (h'q : q ≤ 2) :
    (∑ n ≤ M, ∑ _k ≤ n, ∑ _j ≤ 2 * n + 3, ∑ _l < 4 * n + 12,
      (2 : ℝ≥0∞) ^ (- ((q - 1) / q * n))) ≤ 13009 / (ENNReal.ofReal (q - 1)) ^ 4 := by
  have : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by simp
  simp_rw [this, ENNReal.ofReal_rpow_of_pos zero_lt_two]
  simp only [Finset.sum_const, Nat.card_Iio, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.card_Iic, Nat.cast_one, ge_iff_le]
  calc
  ∑ x ∈ Finset.Iic M, (↑x + 1) * ((2 * ↑x + 3 + 1) * ((4 * ↑x + 12)
      * ENNReal.ofReal (2 ^ (-((q - 1) / q * ↑x)))))
  _ = ∑ x ∈ Finset.Iic M, ENNReal.ofReal
      ((↑x + 1) * ((2 * ↑x + 3 + 1) * ((4 * ↑x + 12) * 2 ^ (-((q - 1) / q * ↑x))))) := by
    congr with i
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
    congr <;> norm_cast
  _ = ENNReal.ofReal (∑ x ∈ Finset.Iic M,
      (↑x + 1) * ((2 * ↑x + 3 + 1) * ((4 * ↑x + 12) * 2 ^ (-((q - 1) / q * ↑x))))) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro i hi
    positivity
  _ = ENNReal.ofReal (∑ n ≤ M, ∑ _k ≤ n, ∑ _j ≤ 2 * n + 3, ∑ _l < 4 * n + 12,
      (2 : ℝ) ^ (- ((q - 1) / q * n))) := by simp
  _ ≤ ENNReal.ofReal (13009 / (q - 1) ^ 4) := by
    apply ENNReal.ofReal_le_ofReal
    exact forest_union_sum_aux1 M q hq h'q
  _ = 13009 / (ENNReal.ofReal (q - 1)) ^ 4 := by
    rw [ENNReal.ofReal_div_of_pos]; swap
    · have : 0 < q - 1 := by linarith
      positivity
    congr
    · norm_cast
    · rw [ENNReal.ofReal_pow]
      linarith

/-- An optimized constant for the forest union theorem. The constant from the blueprint,
defined as `C5_1_2` below, is slightly worse. -/
def C5_1_2_optimized (a : ℝ) (q : ℝ≥0) : ℝ≥0 :=
  C2_0_4_base a * 2 ^ (a + 5/2 : ℝ) * 13009 / (q - 1) ^ 4

/-- Version of the forest union result with a better constant. -/
lemma forest_union_optimized {f : X → ℂ} (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (h'f : Measurable f) :
    ∫⁻ x in G \ G', ‖carlesonSum 𝔓₁ f x‖₊ ≤
    C5_1_2_optimized a nnq * (volume G) ^ (1 - q⁻¹) * (volume F) ^ (q⁻¹) := by
  apply (forest_union_aux hf h'f).trans
  calc
  C2_0_4_base a * 2 ^ (a + 5 / 2 : ℝ) * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ *
    ∑ n ∈ Finset.Iic (maxℭ X),
      ∑ _k ∈ Finset.Iic n, ∑ _j ∈ Finset.Iic (2 * n + 3), ∑ _l ∈ Finset.Iio (4 * n + 12),
        2 ^ (-(q - 1) / q * ↑n)
  _ ≤ C2_0_4_base a * 2 ^ (a + 5 / 2 : ℝ) * volume G ^ (1 - q⁻¹) * volume F ^ q⁻¹ *
      (13009 / (ENNReal.ofReal (q - 1)) ^ 4) := by
    gcongr
    have A n : (2 : ℝ≥0∞) ^ (-(q - 1) / q * n) = 2 ^ (- ((q - 1) / q * n)) := by
      congr; ring
    simp_rw [A]
    exact forest_union_sum_aux2 (maxℭ X) q (one_lt_q X) (q_le_two X)
  _ = C5_1_2_optimized a nnq * (volume G) ^ (1 - q⁻¹) * (volume F) ^ (q⁻¹) := by
    have : ENNReal.ofReal (q - 1) = (nnq - 1 : ℝ≥0) := rfl
    rw [this]
    simp only [ENNReal.div_eq_inv_mul, C5_1_2_optimized, div_eq_inv_mul _ ((nnq - 1) ^ 4),
      ENNReal.coe_sub, ENNReal.coe_one, ENNReal.coe_mul, ENNReal.coe_ofNat]
    rw [ENNReal.coe_inv, ENNReal.coe_rpow_of_ne_zero two_ne_zero]; swap
    · have : 0 < nnq - 1 := tsub_pos_of_lt (one_lt_nnq X)
      apply ne_of_gt
      positivity
    simp only [ENNReal.coe_inv, ENNReal.coe_rpow_of_ne_zero two_ne_zero,
      ENNReal.coe_pow, ENNReal.coe_sub, ENNReal.coe_one, ENNReal.coe_ofNat]
    ring

/- Start of proof attempt -/
lemma round1_C5_1_2_optimized_le' {a : ℕ} {q : ℝ≥0} (ha : 4 ≤ a) :
    C5_1_2_optimized a q ≤ C2_0_4_base a * 2 ^ (a ^ 3) / (q - 1) ^ 4 := by
  have h16 : (2 : ℝ≥0) ^ ((a : ℝ) ^ 3) = (2 : ℝ≥0) ^ (a ^ 3) := by
    have h15 : (a : ℝ) ^ 3 = ((a ^ 3 : ℕ) : ℝ) := by
      simp [pow_succ]
      <;> ring
    have h161 : (2 : ℝ≥0) ^ ((a : ℝ) ^ 3) = (2 : ℝ≥0) ^ ((a ^ 3 : ℕ) : ℝ) := by
      rw [h15]
    have h162 : (2 : ℝ≥0) ^ ((a ^ 3 : ℕ) : ℝ) = (2 : ℝ≥0) ^ (a ^ 3) := by
      norm_cast
    rw [h161, h162]
  have h4 : (2 : ℝ) ^ ((a : ℝ) ^ 3) ≥ (2 : ℝ) ^ ((a : ℝ) + 5 / 2 + 14) := by
    have h41 : (a : ℝ) ^ 3 ≥ (a : ℝ) + 5 / 2 + 14 := by
      have h1 : (a : ℝ) ≥ 4 := by exact_mod_cast ha
      nlinarith [sq_nonneg ((a : ℝ) - 4), sq_nonneg ((a : ℝ))]
    have h42 : (2 : ℝ) ^ ((a : ℝ) ^ 3) ≥ (2 : ℝ) ^ ((a : ℝ) + 5 / 2 + 14) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · norm_num
      · linarith
    linarith
  have h5 : (2 : ℝ) ^ ((a : ℝ) + 5 / 2 + 14) = (2 : ℝ) ^ ((a : ℝ) + 5 / 2) * (2 : ℝ) ^ (14 : ℝ) := by
    have h52 : (2 : ℝ) ^ ((a : ℝ) + 5 / 2 + 14) = (2 : ℝ) ^ ((a : ℝ) + 5 / 2) * (2 : ℝ) ^ (14 : ℝ) := by
      rw [show (a : ℝ) + 5 / 2 + 14 = ((a : ℝ) + 5 / 2) + (14 : ℝ) by ring]
      rw [Real.rpow_add] <;> norm_num
    linarith
  have h6 : (2 : ℝ) ^ (14 : ℝ) > 13009 := by
    norm_num [Real.rpow_natCast]
  have h7 : (2 : ℝ) ^ ((a : ℝ) ^ 3) ≥ (2 : ℝ) ^ ((a : ℝ) + 5 / 2) * 13009 := by
    have h75 : (2 : ℝ) ^ ((a : ℝ) + 5 / 2) > 0 := by positivity
    have h76 : (2 : ℝ) ^ ((a : ℝ) + 5 / 2) * (2 : ℝ) ^ (14 : ℝ) > (2 : ℝ) ^ ((a : ℝ) + 5 / 2) * 13009 := by
      nlinarith
    have h43 : (2 : ℝ) ^ ((a : ℝ) ^ 3) ≥ (2 : ℝ) ^ ((a : ℝ) + 5 / 2) * (2 : ℝ) ^ (14 : ℝ) := by
      linarith [h4, h5]
    linarith
  have h11 : (C2_0_4_base a : ℝ≥0) * (2 : ℝ≥0) ^ ((a : ℝ) ^ 3) ≥ (C2_0_4_base a : ℝ≥0) * (2 : ℝ≥0) ^ ((a : ℝ) + 5 / 2) * 13009 := by
    have h111 : (2 : ℝ) ^ ((a : ℝ) ^ 3) ≥ (2 : ℝ) ^ ((a : ℝ) + 5 / 2) * 13009 := h7
    have h112 : (0 : ℝ) ≤ (C2_0_4_base a : ℝ) := by positivity
    have h113 : (C2_0_4_base a : ℝ) * (2 : ℝ) ^ ((a : ℝ) ^ 3) ≥ (C2_0_4_base a : ℝ) * ((2 : ℝ) ^ ((a : ℝ) + 5 / 2) * 13009) := by
      nlinarith
    have h114 : (C2_0_4_base a : ℝ) * ((2 : ℝ) ^ ((a : ℝ) + 5 / 2) * 13009) = (C2_0_4_base a : ℝ) * (2 : ℝ) ^ ((a : ℝ) + 5 / 2) * 13009 := by ring
    have h115 : (C2_0_4_base a : ℝ) * (2 : ℝ) ^ ((a : ℝ) ^ 3) ≥ (C2_0_4_base a : ℝ) * (2 : ℝ) ^ ((a : ℝ) + 5 / 2) * 13009 := by linarith
    exact_mod_cast h115
  have h12 : (C2_0_4_base a : ℝ≥0) * (2 : ℝ≥0) ^ ((a : ℝ) ^ 3) / (q - 1) ^ 4 ≥ (C2_0_4_base a : ℝ≥0) * (2 : ℝ≥0) ^ ((a : ℝ) + 5 / 2) * 13009 / (q - 1) ^ 4 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact h11
  have h13 : C5_1_2_optimized a q = (C2_0_4_base a : ℝ≥0) * (2 : ℝ≥0) ^ ((a : ℝ) + 5 / 2) * 13009 / (q - 1) ^ 4 := by
    simp [C5_1_2_optimized]
    <;> ring
  have h14 : (C2_0_4_base a : ℝ≥0) * (2 : ℝ≥0) ^ ((a : ℝ) ^ 3) / (q - 1) ^ 4 ≥ C5_1_2_optimized a q := by
    rw [h13]
    exact h12
  have h14' : (C2_0_4_base a : ℝ≥0) * (2 : ℝ≥0) ^ (a ^ 3) / (q - 1) ^ 4 ≥ C5_1_2_optimized a q := by
    have h141 : (C2_0_4_base a : ℝ≥0) * (2 : ℝ≥0) ^ ((a : ℝ) ^ 3) / (q - 1) ^ 4 ≥ C5_1_2_optimized a q := h14
    have h16' : (2 : ℝ≥0) ^ ((a : ℝ) ^ 3) = (2 : ℝ≥0) ^ (a ^ 3) := h16
    have h142 : (C2_0_4_base a : ℝ≥0) * (2 : ℝ≥0) ^ ((a : ℝ) ^ 3) / (q - 1) ^ 4 = (C2_0_4_base a : ℝ≥0) * (2 : ℝ≥0) ^ (a ^ 3) / (q - 1) ^ 4 := by
      rw [h16']
      <;> rfl
    rw [h142] at h141
    exact h141
  exact h14'.le

theorem C5_1_2_optimized_le' {a : ℕ} {q : ℝ≥0} (ha : 4 ≤ a) :
    C5_1_2_optimized a q ≤ C2_0_4_base a * 2 ^ (a ^ 3) / (q - 1) ^ 4  := by

  exact round1_C5_1_2_optimized_le' ha
