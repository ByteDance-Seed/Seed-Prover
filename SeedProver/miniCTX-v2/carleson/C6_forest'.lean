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

/- Start of proof attempt -/
lemma round1_h4 :
  (⋃ u ∈ (⋃ l ∈ Iio (4 * n + 12), 𝔘₄ (X := X) k n j l), 𝔗₂ k n j u) = 
  ⋃ l ∈ Iio (4 * n + 12), ⋃ u ∈ 𝔘₄ k n j l, 𝔗₂ k n j u := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · -- Proving the forward direction
    rintro ⟨u, hu, hxu⟩
    rcases hu with ⟨l, hl, hu'⟩
    refine ⟨l, hl, u, hu', hxu⟩
  · -- Proving the reverse direction
    rintro ⟨l, hl, u, hu', hxu⟩
    refine ⟨u, ?_, hxu⟩
    refine ⟨l, hl, hu'⟩

theorem C6_forest' (hkn : k ≤ n) :
    ℭ₆ (X := X) k n j = ⋃ l ∈ Iio (4 * n + 12), ⋃ u ∈ 𝔘₄ k n j l, 𝔗₂ k n j u  := by

  have h1 : ℭ₆ (X := X) k n j = ⋃ u ∈ 𝔘₃ k n j, 𝔗₂ k n j u := C6_forest
  have h2 : ⋃ l ∈ Iio (4 * n + 12), 𝔘₄ (X := X) k n j l = 𝔘₃ k n j := iUnion_𝔘₄ hkn
  have h3 : ℭ₆ (X := X) k n j = ⋃ u ∈ (⋃ l ∈ Iio (4 * n + 12), 𝔘₄ (X := X) k n j l), 𝔗₂ k n j u := by
    rw [h1, h2]
    <;> rfl
  have h4 : (⋃ u ∈ (⋃ l ∈ Iio (4 * n + 12), 𝔘₄ (X := X) k n j l), 𝔗₂ k n j u) = 
    ⋃ l ∈ Iio (4 * n + 12), ⋃ u ∈ 𝔘₄ k n j l, 𝔗₂ k n j u := round1_h4
  rw [h3, h4]
  <;> rfl
