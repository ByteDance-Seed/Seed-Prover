import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.NormNum.BigOperators
set_option linter.unusedVariables.analyzeTactics true
set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false

lemma round1_h_main (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (m n : ℕ)
  (h : n ≤ m):
  (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a n : ℝ) * (a (n + 1) : ℝ)) =
  (∏ i ∈ (Finset.range (m + 2) \ {n, n + 1}), (a i : ℝ)) := by
  let S := Finset.range (m + 2) \ {n, n + 1}
  have h3 : Disjoint ({n, n + 1} : Finset ℕ) S := by
    simp [S, Finset.disjoint_left]
  have h4 : ({n, n + 1} : Finset ℕ) ∪ S = Finset.range (m + 2) := by
    ext x
    simp [S] ; omega
  have h5 : ∏ i ∈ Finset.range (m + 2), (a i : ℝ) =
      (∏ i ∈ ({n, n + 1} : Finset ℕ), (a i : ℝ)) * (∏ i ∈ S, (a i : ℝ)) := by
    rw [← h4]
    rw [Finset.prod_union h3]
  have h6 : (∏ i ∈ ({n, n + 1} : Finset ℕ), (a i : ℝ)) = (a n : ℝ) * (a (n + 1) : ℝ) := by
    simp [Finset.prod_insert, Finset.prod_singleton]
  have h7 : (a n : ℝ) > 0 := by exact_mod_cast (h_pos n)
  have h8 : (a (n + 1) : ℝ) > 0 := by exact_mod_cast (h_pos (n + 1))
  have h9 : (a n : ℝ) * (a (n + 1) : ℝ) ≠ 0 := mul_ne_zero h7.ne' h8.ne'
  rw [h5, h6]
  have h10 : (( (a n : ℝ) * (a (n + 1) : ℝ) ) * (∏ i ∈ S, (a i : ℝ))) / ((a n : ℝ) * (a (n + 1) : ℝ)) = (∏ i ∈ S, (a i : ℝ)) := by
    field_simp [h9]
  exact h10

lemma round1_h1_90e6 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n):
  ∀ n : ℕ, 0 < (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ)) := by
  simp_all +decide

lemma round1_h2 (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n):
  ∀ n : ℕ, a n ≥ n + 1 := by
  intro n
  induction n with
  | zero =>
    linarith [h_pos 0]
  | succ n ih =>
    have h2₂ : a (n + 1) > a n := h_mono (by linarith)
    linarith

lemma round1_h_sum_telescoping :
  Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) - (1 : ℝ) / ((n : ℝ) + 2)) := by
  let f : ℕ → ℝ := fun n => (1 : ℝ) / ((n : ℝ) + 1) - (1 : ℝ) / ((n : ℝ) + 2)
  have h_nonneg : ∀ i : ℕ, 0 ≤ f i := by
    intro i
    have h₁ : (1 : ℝ) / ((i : ℝ) + 1) > (1 : ℝ) / ((i : ℝ) + 2) := by
      apply one_div_lt_one_div_of_lt
      <;> linarith
    have h₂ : (1 : ℝ) / ((i : ℝ) + 1) - (1 : ℝ) / ((i : ℝ) + 2) ≥ 0 := by linarith
    simpa [f] using h₂
  have h₁ : ∀ N : ℕ, (∑ k ∈ Finset.range N, f k) = 1 - 1 / ((N : ℝ) + 1) := by
    intro N
    induction N with
    | zero =>
      norm_num [f]
    | succ N ih =>
      have h₂ : (∑ k ∈ Finset.range (N + 1), f k) = (∑ k ∈ Finset.range N, f k) + f N := by
        rw [Finset.sum_range_succ]
      rw [h₂, ih]
      have h₃ : f N = (1 : ℝ) / ((N : ℝ) + 1) - (1 : ℝ) / (((N : ℝ) + 1) + 1) := by
        simp [f] ; ring
      rw [h₃] ; field_simp ; ring
  have h₃ : (fun N : ℕ => (∑ k ∈ Finset.range N, f k)) = fun N : ℕ => 1 - 1 / ((N : ℝ) + 1) := by
    funext N
    exact h₁ N
  have h₄ : Filter.Tendsto (fun N : ℕ => 1 - 1 / ((N : ℝ) + 1)) Filter.atTop (nhds 1) := by
    have h₅ : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) Filter.atTop (nhds 0) := by
      apply tendsto_one_div_add_atTop_nhds_zero_nat
    have h₆ : Filter.Tendsto (fun N : ℕ => 1 - 1 / ((N : ℝ) + 1)) Filter.atTop (nhds (1 - 0)) := by
      exact Filter.Tendsto.sub tendsto_const_nhds h₅
    simpa using h₆
  have h₅ : Filter.Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, f k)) Filter.atTop (nhds 1) := by
    rw [h₃] ; exact h₄
  have h₆ : HasSum f 1 := by
    rw [hasSum_iff_tendsto_nat_of_nonneg h_nonneg (1 : ℝ)]
    exact h₅
  exact h₆.summable

lemma round1_hS_pos (a : ℕ → ℕ)
  (h1 : ∀ n : ℕ, 0 < (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ)))
  (h_summable : Summable (fun n : ℕ => (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ)))):
  0 < (∑' n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
  let f : ℕ → ℝ := fun n => (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ))
  have h_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    exact le_of_lt (h1 n)
  have h_pos' : ∀ n : ℕ, 0 < f n := h1
  have h_sum : Summable f := h_summable
  let g : ℕ → NNReal := fun n => ⟨f n, h_nonneg n⟩
  have h1' : 0 < g 0 := by
    exact_mod_cast h_pos' 0
  have h2' : Summable g := by
    have h2₁ : (∀ n : ℕ, 0 ≤ f n) := h_nonneg
    have h2₂ : Summable (fun n : ℕ => (g n)) ↔ Summable f := NNReal.summable_mk h2₁
    exact h2₂.mpr h_sum
  have h3' : 0 < (∑' n : ℕ, (g n : ℝ)) := by
    have h4 : 0 < ∑' (n : ℕ), g n := NNReal.tsum_pos h2' (i := (0 : ℕ)) h1'
    exact_mod_cast h4
  have h4' : (∑' n : ℕ, (g n : ℝ)) = ∑' n : ℕ, f n := by
    simp [g]
  rw [h4'] at h3'
  exact h3'

lemma round1_h_main_7a50 (a : ℕ → ℕ)
  (k n : ℕ)
  (h1 : n < k)
  (h2 : n + 1 < k):
  a n * a (n + 1) ∣ ∏ i ∈ Finset.range k, a i := by
  let S := Finset.range k
  let T : Finset ℕ := {n, n + 1}
  have hT1 : T ⊆ S := by
    intro x hx
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [S, h1]
    · simp [S, h2]
  have h_disj : Disjoint T (S \ T) := Finset.disjoint_sdiff
  have h_prod : ∏ i ∈ S, a i = (∏ i ∈ T, a i) * ∏ i ∈ (S \ T), a i := by
    rw [← Finset.prod_union h_disj, Finset.union_sdiff_of_subset hT1]
  have h12 : ∏ i ∈ T, a i = a n * a (n + 1) := by
    simp [T, Finset.prod_insert, Finset.prod_singleton]
  rw [h_prod, h12]
  exact ⟨∏ i ∈ (S \ T), a i, by ring⟩

lemma round1_h_main_6aa1 (a : ℕ → ℕ)
  (m : ℕ)
  (sub_lemma2 : ∀ (m n : ℕ), n ≤ m → a n * a (n + 1) ∣ ∏ i ∈ Finset.range (m + 2), a i):
  ∃ (k : ℕ → ℕ), ∀ (n : ℕ), n ∈ Finset.range (m + 1) →
    (∏ i ∈ Finset.range (m + 2), a i) = (a n * a (n + 1)) * k n := by
  let k : ℕ → ℕ := fun n =>
    if h : n ≤ m then Nat.find (sub_lemma2 m n h) else 0
  use k
  intro n hn
  have h₃ : n ≤ m := by
    simp only [Finset.mem_range] at hn ; linarith
  have h₄ : a n * a (n + 1) ∣ ∏ i ∈ Finset.range (m + 2), a i := sub_lemma2 m n h₃
  have h₅ : (∏ i ∈ Finset.range (m + 2), a i) = (a n * a (n + 1)) * (k n) := by
    have h₆ : k n = Nat.find h₄ := by
      simp [k, h₃]
    rw [h₆]
    exact Nat.find_spec h₄
  exact h₅

lemma round1_h_final (a : ℕ → ℕ)
  (m : ℕ)
  (h_pos : ∀ n, 0 < a n)
  (k : ℕ → ℕ)
  (hk : ∀ (n : ℕ), n ∈ Finset.range (m + 1) →
    (∏ i ∈ Finset.range (m + 2), a i) = (a n * a (n + 1)) * k n):
  ∃ (Im : ℕ), (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (Im : ℝ) := by
  set P : ℕ := ∏ i ∈ Finset.range (m + 2), a i with hP
  have h₁ : ∀ (n : ℕ), n ∈ Finset.range (m + 1) →
    (P : ℝ) = ((a n : ℝ) * (a (n + 1) : ℝ)) * (k n : ℝ) := by
    intro n hn
    have h₂ : (∏ i ∈ Finset.range (m + 2), a i) = (a n * a (n + 1)) * k n := hk n hn
    exact_mod_cast h₂
  set Im : ℕ := ∑ n ∈ Finset.range (m + 1), k n with hIm
  have h₃ : (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) = (P : ℝ) := by
    simp [hP]
  have h₄ : ∀ (n : ℕ), n ∈ Finset.range (m + 1) →
    ((P : ℝ) * (1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) = (k n : ℝ) := by
    intro n hn
    have h₅ : (P : ℝ) = ((a n : ℝ) * (a (n + 1) : ℝ)) * (k n : ℝ) := h₁ n hn
    have h₆ : (a n : ℝ) > 0 := by exact_mod_cast (h_pos n)
    have h₇ : (a (n + 1) : ℝ) > 0 := by exact_mod_cast (h_pos (n + 1))
    have h₈ : ((a n : ℝ) * (a (n + 1) : ℝ)) ≠ 0 := by positivity
    rw [h₅]
    field_simp [h₈]
  have h₅ : (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) =
    ∑ n ∈ Finset.range (m + 1), ((P : ℝ) * (1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) := by
    rw [h₃]
    have h₅₁ : ((P : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) =
        ∑ n ∈ Finset.range (m + 1), ((P : ℝ) * (1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) := by
      rw [Finset.mul_sum]
    exact h₅₁
  rw [h₅]
  have h₆ : ∑ n ∈ Finset.range (m + 1), ((P : ℝ) * (1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) =
    ∑ n ∈ Finset.range (m + 1), (k n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact h₄ n hn
  rw [h₆]
  have h₇ : (∑ n ∈ Finset.range (m + 1), (k n : ℝ)) = ((∑ n ∈ Finset.range (m + 1), k n : ℕ) : ℝ) := by
    norm_cast
  rw [h₇]
  exact ⟨Im, by simp [hIm]⟩

lemma round1_h1_5a8f (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (m : ℕ):
  (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) > 0 := by
  exact_mod_cast Finset.prod_pos fun i _ => h_pos i

lemma round1_h_sum_split (a : ℕ → ℕ)
  (m : ℕ):
  (∑ n ∈ Finset.range (m + 1), (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ))) =
  (∑ n ∈ Finset.range m, (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ))) +
  (1 : ℝ) / ((a m : ℝ) * (a (m + 1) : ℝ)) := by
  have h1 : Finset.range (m + 1) = Finset.range m ∪ {m} := by
    ext x
    simp [Finset.mem_range]
    omega
  rw [h1]
  rw [Finset.sum_union]
  <;> simp [Finset.sum_singleton]

lemma round1_h_prod1 (a : ℕ → ℕ)
  (m : ℕ):
  (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) = (a (m + 1) : ℝ) * (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) := by
  have h1 : Finset.range (m + 2) = Finset.range (m + 1) ∪ {m + 1} := by
    ext x
    simp [Finset.mem_range]
    omega
  rw [h1]
  rw [Finset.prod_union]
  <;> simp
  ring

lemma round1_h_prod2 (a : ℕ → ℕ)
  (m : ℕ):
  (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) =
  (∏ i ∈ Finset.range m, (a i : ℝ)) * (a m : ℝ) * (a (m + 1) : ℝ) := by
  have h1 : Finset.range (m + 2) = Finset.range m ∪ ({m, m + 1} : Finset ℕ) := by
    ext x
    simp [Finset.mem_range, Finset.mem_insert]
    omega
  rw [h1]
  rw [Finset.prod_union]
  <;> simp [Finset.prod_insert, Finset.prod_singleton]
  ring_nf

lemma round1_h1' (a : ℕ → ℕ)
  (h_mono : StrictMono a):
  ∀ (n : ℕ), (a (n + 1) - a n) ≥ 1 := by
  intro n
  have h2 : a n < a (n + 1) := h_mono (by linarith)
  omega

lemma round1_h2' (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n):
  ∀ (n : ℕ), (1 : ℝ) / (a n : ℝ) - 1 / (a (n + 1) : ℝ) =
    ((a (n + 1) : ℝ) - (a n : ℝ)) / ((a n : ℝ) * (a (n + 1) : ℝ)) := by
  intro n
  have h_pos1 : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast (h_pos n)
  have h_pos2 : (0 : ℝ) < (a (n + 1) : ℝ) := by exact_mod_cast (h_pos (n + 1))
  have h_pos3 : (0 : ℝ) < (a n : ℝ) * (a (n + 1) : ℝ) := mul_pos h_pos1 h_pos2
  field_simp [h_pos1.ne', h_pos2.ne', h_pos3.ne']

lemma round1_h2_ac08 (x : ℕ → ℝ)
  (M : ℕ):
  ∑ n ∈ Finset.range M, (x n - x (n + 1)) = x 0 - x M := by
  induction M with
  | zero =>
    norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    ring

lemma round1_h_main_4c10 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (h_ineq1 : ∀ n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ)) ≤ 1 / (a n : ℝ) - 1 / (a (n + 1) : ℝ))
  (h_telescoping_sum : ∀ k M : ℕ, (∑ n ∈ Finset.range M, (1 / (a (n + k) : ℝ) - 1 / (a (n + k + 1) : ℝ))) = 1 / (a k : ℝ) - 1 / (a (k + M) : ℝ))
  (k : ℕ):
  (∑' n : ℕ, 1 / ((a (n + k) : ℝ) * (a (n + k + 1) : ℝ))) ≤ 1 / (a k : ℝ) := by
  apply Real.tsum_le_of_sum_range_le (fun _ ↦ by positivity) fun M ↦
    (Finset.sum_le_sum fun _ _ ↦ h_ineq1 _).trans_eq (h_telescoping_sum k M) |>.trans (sub_le_self _ (by positivity))

theorem round1_h_sum_split_fde7 (a : ℕ → ℕ)
  (P : ℕ)
  (Q : ℕ)
  (hQ_pos : Q > 0)
  (hP_pos : P > 0)
  (h_sum_eq : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ)):
  ∀ k : ℕ, (∑' n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range k, (1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) = (∑' n : ℕ, 1 / ((a (n + k) : ℝ) * (a (n + k + 1) : ℝ))) := by
  let f : ℕ → ℝ := fun n => 1 / ((a n : ℝ) * (a (n + 1) : ℝ))
  have h_summable : Summable f := by
    by_contra h
    have h₄ : (∑' n : ℕ, f n) = 0 := tsum_eq_zero_of_not_summable h
    rw [h₄] at h_sum_eq
    have h₆ : (P : ℝ) > 0 := by exact_mod_cast hP_pos
    have h₇ : (Q : ℝ) > 0 := by exact_mod_cast hQ_pos
    have h₈ : (P : ℝ) / (Q : ℝ) > 0 := div_pos h₆ h₇
    linarith
  intro k
  have h_main : (∑ n ∈ Finset.range k, f n) + (∑' n : ℕ, f (n + k)) = (∑' n : ℕ, f n) :=
    Summable.sum_add_tsum_nat_add k h_summable
  have h_final : (∑' n : ℕ, f n) - (∑ n ∈ Finset.range k, f n) = (∑' n : ℕ, f (n + k)) := by
    linarith
  have h_eq : (∑' n : ℕ, f (n + k)) = (∑' n : ℕ, 1 / ((a (n + k) : ℝ) * (a (n + k + 1) : ℝ))) := by
    congr with n
  rw [h_eq] at h_final
  exact h_final

theorem round1_h_prod_ge_one (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n):
  ∀ n : ℕ, (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) ≥ 1 := by
  intro n
  induction n with
  | zero =>
    simp
    exact_mod_cast h_pos 0
  | succ n ih =>
    rw [Finset.prod_range_succ]
    have : 1 ≤ (a (n + 1) : ℝ) := by exact_mod_cast h_pos (n + 1)
    nlinarith

lemma round1_h1_9221 (a : ℕ → ℕ)
  (n : ℕ):
  (∏ i ∈ Finset.range (n + 2), (a i : ℝ)) =
  (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) * (a (n + 1) : ℝ) := by
  have h1 : Finset.range (n + 2) = Finset.range (n + 1) ∪ {n + 1} := by
    ext x
    simp [Finset.mem_range]
    omega
  rw [h1]
  rw [Finset.prod_union]
  <;> simp [Finset.disjoint_left]
  omega

lemma round1_h2_f3dc (a : ℕ → ℕ)
  (n : ℕ)
  (h3_rec : ∀ n : ℕ, n ≥ 3 → (a n : ℝ) ≤ K * (∏ i ∈ Finset.range n, (a i : ℝ)))
  (h_n : n ≥ 2):
  (a (n + 1) : ℝ) ≤ K * (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) := by
  simp_all +decide

lemma round1_h_main_0295 (z : ℕ → ℝ)
  (N₀ : ℕ)
  (hN₀ : ∀ n : ℕ, n ≥ N₀ → z (n + 1) ≤ z n):
  ∀ (m N : ℕ), m ≥ N₀ → N ≥ m → z N ≤ z m := by
  intro m N hm hN
  have h₁ : ∀ n : ℕ, n ≥ m → z n ≤ z m := by
    intro n hn
    induction' hn with n hn ih
    ·
      simp
    ·
      have h₂ : n ≥ N₀ := by
        exact le_trans hm hn
      have h₃ : z (n + 1) ≤ z n := hN₀ n h₂
      have h₄ : z (n + 1) ≤ z m := by linarith
      exact h₄
  exact h₁ N hN

lemma round1_h_main_ineq (C : ℝ)
  (n : ℕ):
  |(C * (1 - (1 / 2 : ℝ) ^ n)) - C| = |C| / (2 : ℝ) ^ n := by
  have h₁ : (C * (1 - (1 / 2 : ℝ) ^ n)) - C = -C * ((1 / 2 : ℝ) ^ n) := by
    ring
  rw [h₁]
  have h₂ : |(-C * ((1 / 2 : ℝ) ^ n))| = |(-C)| * |((1 / 2 : ℝ) ^ n)| := by
    rw [abs_mul]
  rw [h₂]
  have h₃ : |(-C)| = |C| := by
    simp
  rw [h₃]
  have h₄ : |((1 / 2 : ℝ) ^ n)| = (1 : ℝ) / (2 : ℝ) ^ n := by
    have h₅ : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    rw [abs_of_pos h₅]
    field_simp
  rw [h₄]
  field_simp

lemma round1_h_pow_gt_id (n : ℕ):
  (2 : ℕ) ^ n > n := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    cases n with
    | zero =>
      norm_num
    | succ n =>
      simp [pow_succ] at *
      omega

theorem round1_lemma3 (u v : ℕ → ℝ)
  (U V : ℝ)
  (hu : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |u n - U| < ε)
  (hv : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |v n - V| < ε):
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(u n + v n) - (U + V)| < ε := by
  have h1 : Filter.Tendsto u Filter.atTop (nhds U) := by
    simpa [Metric.tendsto_atTop] using hu
  have h2 : Filter.Tendsto v Filter.atTop (nhds V) := by
    simpa [Metric.tendsto_atTop] using hv
  have h3 : Filter.Tendsto (fun n : ℕ ↦ u n + v n) Filter.atTop (nhds (U + V)) :=
    Filter.Tendsto.add h1 h2
  simpa [Metric.tendsto_atTop] using h3

lemma test_def (b : ℕ → ℝ):
  Filter.atTop.liminf b = sSup { a : ℝ | ∀ᶠ n in Filter.atTop, a ≤ b n } := by
  bound

lemma round1_h_main_ineq_9cca :
  ∀ (n : ℕ), (2 : ℝ) ^ n ≥ (n : ℝ) + 1 := by
  intro n
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    simp [pow_succ] at *
    linarith

lemma round1_main_goal (h_sub : ∀ (M : ℝ), M > 0 → ∃ N' : ℕ, ∀ n : ℕ, n ≥ N' → (2 : ℝ) ^ n > M)
  (K_0 : ℝ)
  (δ : ℝ)
  (hδ : δ > 0):
  ∃ N' : ℕ, ∀ n : ℕ, n ≥ N' → K_0 / (2 : ℝ) ^ n > -δ := by
  by_cases h1 : K_0 ≥ 0
  ·
    use 0
    intro n _
    have h3 : K_0 / (2 : ℝ) ^ n ≥ 0 := by
      apply div_nonneg
      · linarith
      · positivity
    linarith
  ·
    set M : ℝ := (-K_0) / δ with hM
    have hM_pos : M > 0 := by
      apply div_pos
      · linarith
      · linarith
    rcases h_sub M hM_pos with ⟨N', hN'⟩
    use N'
    intro n hn
    have h7 : (2 : ℝ) ^ n > M := hN' n hn
    have h8 : (2 : ℝ) ^ n > 0 := by positivity
    have h10 : δ * (2 : ℝ) ^ n > (-K_0) := by
      calc
        δ * (2 : ℝ) ^ n > δ * M := by gcongr
        _ = (-K_0) := by
          rw [hM]
          field_simp [hδ.ne'] ; ring
    have h12 : K_0 > - (δ * (2 : ℝ) ^ n) := by linarith
    calc
      K_0 / (2 : ℝ) ^ n > (-(δ * (2 : ℝ) ^ n)) / (2 : ℝ) ^ n := by gcongr
      _ = -δ := by
        field_simp [h8.ne']

lemma round1_prod_log :
  ∀ (k : ℕ) (x : ℕ → ℝ), (∀ i ∈ Finset.range (k + 1), x i ≠ 0) →
    Real.log (∏ i ∈ Finset.range (k + 1), x i) = ∑ i ∈ Finset.range (k + 1), Real.log (x i) := by
  exact fun k => Real.log_prod (Finset.range (k + 1))

lemma round1_h_main_a15a (N : ℕ):
  ∀ (n : ℕ), (n ≥ N → (∑ i ∈ Finset.Ico N (n + 1), (2 : ℝ) ^ i) = (2 : ℝ) ^ (n + 1) - (2 : ℝ) ^ N) := by
  intro n
  induction n with
  | zero =>
    intro h
    have hN : N = 0 := by linarith
    subst hN
    norm_num
  | succ n ih =>
    intro h
    have h₁ : (∑ i ∈ Finset.Ico N ((n + 1) + 1), (2 : ℝ) ^ i) = (∑ i ∈ Finset.Ico N (n + 2), (2 : ℝ) ^ i) := by
      rfl
    have h_goal : (∑ i ∈ Finset.Ico N (n + 2), (2 : ℝ) ^ i) = (2 : ℝ) ^ ((n + 1) + 1) - (2 : ℝ) ^ N := by
      have h₂ : (∑ i ∈ Finset.Ico N (n + 2), (2 : ℝ) ^ i) = (∑ i ∈ Finset.Ico N (n + 1), (2 : ℝ) ^ i) + (2 : ℝ) ^ (n + 1) := by
        have h₃ : Finset.Ico N (n + 2) = Finset.Ico N (n + 1) ∪ {n + 1} := by
          ext x
          simp [Finset.mem_Ico] ; omega
        rw [h₃]
        rw [Finset.sum_union] <;> simp [Finset.disjoint_left] ; omega
      rw [h₂]
      by_cases h4 : n ≥ N
      ·
        have h5 := ih h4
        rw [h5]
        simp [pow_succ] ; ring
      ·
        have h5 : n < N := by omega
        have h6 : n + 1 ≥ N := h
        have h7 : n = N - 1 := by omega
        have h8 : N > 0 := by omega
        have h9 : n + 1 = N := by omega
        have h10 : n + 2 = N + 1 := by omega
        have h11 : Finset.Ico N (n + 2) = Finset.Ico N (N + 1) := by
          apply congrArg (fun k : ℕ => Finset.Ico N k) h10
        have h12 : (∑ i ∈ Finset.Ico N (N + 1), (2 : ℝ) ^ i) = (2 : ℝ) ^ N := by
          have h13 : Finset.Ico N (N + 1) = {N} := by
            ext x
            simp
          rw [h13]
          simp
        have h14 : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ N := by
          rw [h9]
        have h15 : ((∑ i ∈ Finset.Ico N (n + 1), (2 : ℝ) ^ i) + (2 : ℝ) ^ (n + 1)) = (2 : ℝ) ^ ((n + 1) + 1) - (2 : ℝ) ^ N := by
          have h16 : n + 1 = N := h9
          rw [h16] at *
          simp [pow_succ] ; ring
        exact h15
    rw [h₁] ; exact h_goal

lemma round1_h_sum_split_7870 (a : ℕ → ℕ)
  (n : ℕ)
  (N : ℕ)
  (hN : n ≥ N):
  ∑ i ∈ Finset.range (n + 1), Real.log ((a i : ℝ)) =
    (∑ i ∈ Finset.range N, Real.log ((a i : ℝ))) + (∑ i ∈ Finset.Ico N (n + 1), Real.log ((a i : ℝ))) := by
  have h1 : Finset.range (n + 1) = Finset.range N ∪ Finset.Ico N (n + 1) := by
    ext x
    simp [Finset.mem_range, Finset.mem_Ico]
    omega
  have h2 : Disjoint (Finset.range N) (Finset.Ico N (n + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp [Finset.mem_range, Finset.mem_Ico] at hx1 hx2 ; omega
  rw [h1]
  rw [Finset.sum_union h2]

lemma round1_h_sum_lower_bound (a : ℕ → ℕ)
  (c : ℝ)
  (N : ℕ)
  (n : ℕ)
  (hN : n ≥ N)
  (h_ineq1 : ∀ n : ℕ, n ≥ N → Real.log (a n : ℝ) > c * (2 : ℝ) ^ n):
  ∑ i ∈ Finset.Ico N (n + 1), Real.log ((a i : ℝ)) > c * (∑ i ∈ Finset.Ico N (n + 1), (2 : ℝ) ^ i) := by
  have h1 : ∀ i ∈ Finset.Ico N (n + 1), Real.log ((a i : ℝ)) > c * (2 : ℝ) ^ i := by
    intro i hi
    have h2 : i ≥ N := by
      simp only [Finset.mem_Ico] at hi
      linarith
    exact h_ineq1 i h2
  have h3 : ∑ i ∈ Finset.Ico N (n + 1), Real.log ((a i : ℝ)) > ∑ i ∈ Finset.Ico N (n + 1), (c * (2 : ℝ) ^ i) := by
    apply Finset.sum_lt_sum_of_nonempty
    ·
      exact ⟨N, by
        simp ; omega⟩
    ·
      intro i hi
      exact h1 i hi
  have h4 : ∑ i ∈ Finset.Ico N (n + 1), (c * (2 : ℝ) ^ i) = c * (∑ i ∈ Finset.Ico N (n + 1), (2 : ℝ) ^ i) := by
    rw [Finset.mul_sum]
  rw [h4] at h3
  exact h3

lemma round1_h_main_5367 (x : ℕ → ℝ)
  (R : ℝ)
  (h_R_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |x n - R| < ε)
  (L : ℝ)
  (hL : ∃ N1 : ℕ, ∀ n : ℕ, n ≥ N1 → x n > L):
  R ≥ L := by
  by_contra h
  set ε : ℝ := (L - R) / 2 with hε
  have hε_pos : ε > 0 := by linarith
  have h₃ : ∃ N2 : ℕ, ∀ n : ℕ, n ≥ N2 → |x n - R| < ε := h_R_converges ε hε_pos
  rcases h₃ with ⟨N2, hN2⟩
  rcases hL with ⟨N1, hN1⟩
  let N := max N1 N2
  have hN1' : N ≥ N1 := le_max_left N1 N2
  have hN2' : N ≥ N2 := le_max_right N1 N2
  have h₄ : |x N - R| < ε := hN2 N hN2'
  have h₅ : x N < L := by
    have := abs_lt.mp h₄
    linarith
  have h₈ : x N > L := hN1 N hN1'
  linarith

lemma round1_h_prod_ge_one_nat (a : ℕ → ℕ):
  ∀ (s : Finset ℕ), (∀ (i : ℕ), i ∈ s → (a i : ℝ) ≥ 1) → (∏ i ∈ s, (a i : ℝ)) ≥ 1 := by
  intro s h
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.prod_insert hk]
    have h_k := h k (Finset.mem_insert_self k s)
    have h_ih := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    nlinarith

lemma round1_hR_nonneg (x : ℕ → ℝ)
  (R : ℝ)
  (h_x_nonneg : ∀ n : ℕ, x n ≥ 0)
  (h_R_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |x n - R| < ε):
  R ≥ 0 := by
  by_contra h
  have h₂ : -R > 0 := by linarith
  let ε : ℝ := -R
  rcases h_R_converges ε h₂ with ⟨N, hN⟩
  have h₅ : |x N - R| < ε := hN N (by linarith)
  have h₆ : x N < 0 := by
    have h₈ := abs_lt.mp h₅
    linarith
  have h₉ : x N ≥ 0 := h_x_nonneg N
  linarith

lemma round1_h_main_identity (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (n : ℕ)
  (hn : n ≥ 1):
  Real.log ((a n : ℝ)) / (2 : ℝ) ^ n =
    (Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) / (2 : ℝ) ^ n) -
    (1 / 2 : ℝ) * (Real.log (∏ i ∈ Finset.range n, (a i : ℝ)) / (2 : ℝ) ^ (n - 1)) := by
  have h1 : ∀ m : ℕ, 0 < (∏ i ∈ Finset.range m, (a i : ℝ)) := by
    intro m
    have h1₁ : ∀ i ∈ Finset.range m, (0 : ℝ) < (a i : ℝ) := by
      intro i _
      exact_mod_cast (h_pos i)
    have h1₂ : 0 < ∏ i ∈ Finset.range m, (a i : ℝ) := by
      apply Finset.prod_pos
      exact h1₁
    exact h1₂
  have h2 : (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) = (∏ i ∈ Finset.range n, (a i : ℝ)) * (a n : ℝ) := by
    rw [Finset.prod_range_succ]
  have h3 : (0 : ℝ) < (∏ i ∈ Finset.range n, (a i : ℝ)) := h1 n
  have h4 : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast (h_pos n)
  have h5 : Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) = Real.log (∏ i ∈ Finset.range n, (a i : ℝ)) + Real.log ((a n : ℝ)) := by
    rw [h2]
    rw [Real.log_mul (by positivity) (by positivity)]
  have h6 : Real.log ((a n : ℝ)) = Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) - Real.log (∏ i ∈ Finset.range n, (a i : ℝ)) := by linarith
  have h7 : n ≥ 1 := hn
  have h8 : (n - 1) + 1 = n := by omega
  have h9 : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ n' =>
      simp [pow_succ]
      ring
  rw [h6]
  rw [h9]
  field_simp [h3.ne']

lemma round1_h_sum_ico_pow (N m : ℕ)
  (h₁ : N ≤ m + 1):
  ∑ i ∈ Finset.Ico N (m + 1), (2 : ℝ) ^ i = (2 : ℝ) ^ (m + 1) - (2 : ℝ) ^ N := by
  rw [geom_sum_Ico (by norm_num) h₁]
  norm_num

lemma round1_h_prod_pos (a : ℕ → ℕ)
  (S : Finset ℕ)
  (h : ∀ i ∈ S, (a i : ℝ) > 0):
  (∏ i ∈ S, (a i : ℝ)) > 0 := by
  apply Finset.prod_pos
  exact h

lemma round1_h_main_ebf0 (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n)
  (m : ℕ):
  0 < (a (m + 1) : ℝ) / (a (m + 3) : ℝ) ∧ (a (m + 1) : ℝ) / (a (m + 3) : ℝ) < 1 := by
  have h1 : m + 1 < m + 3 := by
    omega
  have h2 : a (m + 1) < a (m + 3) := h_mono h1
  have h3 : 0 < a (m + 1) := h_pos (m + 1)
  have h4 : 0 < a (m + 3) := h_pos (m + 3)
  have h5 : (0 : ℝ) < (a (m + 1) : ℝ) := by exact_mod_cast h3
  have h6 : (0 : ℝ) < (a (m + 3) : ℝ) := by exact_mod_cast h4
  have h7 : (a (m + 1) : ℝ) < (a (m + 3) : ℝ) := by exact_mod_cast h2
  have h8 : 0 < ((a (m + 1) : ℝ) / (a (m + 3) : ℝ)) := by
    apply div_pos h5 h6
  have h9 : ((a (m + 1) : ℝ) / (a (m + 3) : ℝ)) < 1 := by
    rw [div_lt_one h6]
    linarith
  exact ⟨h8, h9⟩

theorem round1_h3_491b (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (m : ℕ):
  ((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + 2) : ℝ) * (a (m + 3) : ℝ))) =
  ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) * ((a (m + 1) : ℝ) / (a (m + 3) : ℝ)) := by
  have h1 : (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) = (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) * (a (m + 1) : ℝ) := by
    rw [Finset.prod_range_succ]
  have h2 : (a (m + 2) : ℝ) ≠ 0 := by
    have h2₁ : 0 < a (m + 2) := h_pos (m + 2)
    have h2₂ : (a (m + 2) : ℝ) > 0 := by exact_mod_cast h2₁
    linarith
  have h3 : (a (m + 3) : ℝ) ≠ 0 := by
    have h3₁ : 0 < a (m + 3) := h_pos (m + 3)
    have h3₂ : (a (m + 3) : ℝ) > 0 := by exact_mod_cast h3₁
    linarith
  rw [h1]
  field_simp [h2, h3]

lemma round1_h_aux :
  ∀ (k : ℕ), (2 : ℕ) ^ (k + 1) > k := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
    cases k with
    | zero => norm_num
    | succ k' =>
      simp [pow_succ] at * ; ring_nf at * ; omega

lemma round1_h_summable_9d78 (a : ℕ → ℕ)
  (P : ℕ)
  (Q : ℕ)
  (hQ_pos : Q > 0)
  (hP_pos : P > 0)
  (h_sum_eq : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ)):
  Summable (fun n : ℕ => 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
  let f : ℕ → ℝ := fun n => 1 / ((a n : ℝ) * (a (n + 1) : ℝ))
  by_contra h
  have h₃ : (∑' n : ℕ, f n) = 0 := tsum_eq_zero_of_not_summable h
  have h₇ : (P : ℝ) / (Q : ℝ) > 0 := by positivity
  linarith [h_sum_eq, h₃, h₇]

lemma round1_h_main_identity_a39d (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (k m : ℕ):
  let T := fun (k : ℕ) (m : ℕ) => (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + k) : ℝ) * (a (m + k + 1) : ℝ))
  (T (k + 1) m) = (T k m) * ((a (m + k) : ℝ) / (a (m + k + 2) : ℝ)) := by
  dsimp only
  have h1 : (a (m + k) : ℝ) > 0 := by exact_mod_cast (h_pos (m + k))
  have h2 : (a (m + k + 1) : ℝ) > 0 := by exact_mod_cast (h_pos (m + k + 1))
  have h3 : (a (m + k + 2) : ℝ) > 0 := by exact_mod_cast (h_pos (m + k + 2))
  have h4 : ((a (m + (k + 1)) : ℝ)) = (a (m + k + 1) : ℝ) := by
    have h5 : m + (k + 1) = m + k + 1 := by omega
    rw [h5]
  have h6 : ((a (m + (k + 1) + 1) : ℝ)) = (a (m + k + 2) : ℝ) := by
    have h7 : m + (k + 1) + 1 = m + k + 2 := by omega
    rw [h7]
  rw [h4, h6]
  field_simp [h1.ne', h2.ne', h3.ne']
  ring

lemma round1_h_main_ineq_5c86 (m : ℕ)
  (T : ℕ → ℕ → ℝ)
  (h_ineq : ∀ k : ℕ, k ≥ 1 → T (k + 1) m < (1 / 2) * (T k m)):
  ∀ (k : ℕ), T (k + 3) m < (1 / 2 : ℝ) ^ (k + 1) * T 2 m := by
  intro k
  induction k with
  | zero =>
    have h1 := h_ineq 2 (by norm_num)
    norm_num at h1 ⊢
    linarith
  | succ k ih =>
    have h2 : T (k + 4) m = T ((k + 3) + 1) m := by ring_nf
    rw [h2]
    have h3 : T ((k + 3) + 1) m < (1 / 2 : ℝ) * (T (k + 3) m) := by
      apply h_ineq
      linarith
    calc
      T ((k + 3) + 1) m < (1 / 2 : ℝ) * (T (k + 3) m) := h3
      _ < (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ (k + 1) * T 2 m) := by gcongr
      _ = (1 / 2 : ℝ) ^ (k + 2) * T 2 m := by
        ring

lemma round1_h_sum_geom :
  (∑' (k : ℕ), (1 / 2 : ℝ) ^ (k + 1)) = 1 := by
  have h₁ : ∀ (k : ℕ), (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k := by
    intro k
    ring
  have h₂ : (∑' (k : ℕ), (1 / 2 : ℝ) ^ (k + 1)) = (∑' (k : ℕ), (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k) := by
    congr 1
    funext k ; exact h₁ k
  rw [h₂]
  have h₃ : (∑' (k : ℕ), (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k) = (1 / 2 : ℝ) * (∑' (k : ℕ), (1 / 2 : ℝ) ^ k) := by
    rw [tsum_mul_left]
  rw [h₃]
  have h₄ : (∑' (k : ℕ), (1 / 2 : ℝ) ^ k) = 2 := by
    rw [tsum_geometric_of_lt_one] <;> norm_num
  rw [h₄] ; norm_num

lemma round1_h1_2d60 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (m k : ℕ):
  (0 : ℝ) < (a (m + k) : ℝ) := by
  simp_all +decide

lemma round1_h2_8c70 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (m k : ℕ):
  (0 : ℝ) < (a (m + k + 1) : ℝ) := by
  simp_all +decide

lemma round1_h3_c582 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (m k : ℕ):
  (0 : ℝ) < (a (m + k + 2) : ℝ) := by
  simp_all +decide

lemma round1_h1_988e (f : ℕ → ℝ)
  (K : ℕ)
  (h_ratio : ∀ n : ℕ, n ≥ K → f (n + 1) < (1 / 2) * f n):
  ∀ (m : ℕ), f (K + m) ≤ f K * (1 / 2 : ℝ) ^ m := by
  intro m
  induction m with
  | zero =>
    norm_num
  | succ m ih =>
    have h : f (K + m + 1) ≤ f K * (1 / 2 : ℝ) ^ (m + 1) := by
      calc
        f (K + m + 1) ≤ (1 / 2 : ℝ) * f (K + m) := le_of_lt (h_ratio (K + m) (by linarith))
        _ ≤ (1 / 2 : ℝ) * (f K * (1 / 2 : ℝ) ^ m) := by gcongr
        _ = f K * (1 / 2 : ℝ) ^ (m + 1) := by ring
    simpa [add_assoc] using h

theorem round1_lemma_tsum_relation (f : ℕ → ℝ)
  (h_summable : Summable f):
  (∑' k : ℕ, f k) = f 0 + (∑' k : ℕ, f (k + 1)) := by
  have h_main : (∑' k : ℕ, f k) = (∑ i ∈ Finset.range 1, f i) + (∑' k : ℕ, f (k + 1)) := by
    exact Eq.symm (Summable.sum_add_tsum_nat_add (1 : ℕ) h_summable)
  have h₁ : (∑ i ∈ Finset.range 1, f i) = f 0 := by
    norm_num
  rw [h₁] at h_main
  exact h_main

theorem round1_summable_shift (f : ℕ → ℝ)
  (hf : Summable f):
  Summable (fun (k : ℕ) => f (k + 1)) := by
  let φ : ℕ → ℕ := fun k => k + 1
  have h_inj : Function.Injective φ := by
    intro k m h
    simp [φ] at h ; omega
  have h_main : Summable (f ∘ φ) := Summable.comp_injective hf h_inj
  simpa [φ] using h_main

lemma round1_h_main_e2d5 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (m : ℕ)
  (T : ℕ → ℕ → ℝ)
  (hT_def : ∀ k : ℕ, T k m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + k) : ℝ) * (a (m + k + 1) : ℝ))):
  T 1 m = ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) := by
  have h1 : T 1 m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + 1) : ℝ) * (a (m + 2) : ℝ)) := by
    simp [hT_def]
  have h2 : (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) = (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) * (a (m + 1) : ℝ) := by
    rw [Finset.prod_range_succ]
  have h3 : (a (m + 1) : ℝ) ≠ 0 := by
    have h4 : 0 < a (m + 1) := h_pos (m + 1)
    exact_mod_cast (show (a (m + 1) : ℝ) ≠ 0 from by positivity)
  have h4 : (a (m + 2) : ℝ) ≠ 0 := by
    have h5 : 0 < a (m + 2) := h_pos (m + 2)
    exact_mod_cast (show (a (m + 2) : ℝ) ≠ 0 from by positivity)
  rw [h1, h2]
  have h5 : (((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) * (a (m + 1) : ℝ)) / ((a (m + 1) : ℝ) * (a (m + 2) : ℝ))) =
    ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) := by
    calc
      (((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) * (a (m + 1) : ℝ)) / ((a (m + 1) : ℝ) * (a (m + 2) : ℝ)))
        = (((∏ i ∈ Finset.range (m + 1), (a i : ℝ))) / (a (m + 2) : ℝ)) := by
          field_simp [h3, h4] ; ring
      _ = (((∏ i ∈ Finset.range (m + 1), (a i : ℝ))) / (a (m + 2) : ℝ)) := by rfl
  exact h5

theorem round1_T2_eq (a : ℕ → ℕ)
  (m : ℕ)
  (T : ℕ → ℕ → ℝ)
  (hT_def : ∀ k : ℕ, T k m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + k) : ℝ) * (a (m + k + 1) : ℝ))):
  T 2 m = ((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + 2) : ℝ) * (a (m + 3) : ℝ))) := by
  simp_all +decide

lemma round1_h1_d71c (Q : ℕ)
  (hQ_pos : Q > 0):
  (1 : ℝ) / (Q : ℝ) > 0 := by
  simp_all +decide

lemma round1_h_telescoping_summable :
  Summable (fun n : ℕ ↦ (1 / ((n : ℝ) + 1)) - (1 / ((n : ℝ) + 2))) := by
  let f : ℕ → ℝ := fun n ↦ (1 / ((n : ℝ) + 1)) - (1 / ((n : ℝ) + 2))
  have h_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    have h₄ : 1 / ((n : ℝ) + 1) > 1 / ((n : ℝ) + 2) := by
      apply one_div_lt_one_div_of_lt
      · positivity
      · linarith
    dsimp only [f]
    linarith
  have h_partial_sum : ∀ N : ℕ, ∑ n ∈ Finset.range N, f n = 1 - 1 / ((N : ℝ) + 1) := by
    intro N
    induction N with
    | zero =>
      norm_num [f]
    | succ N ih =>
      have h₁ : ∑ n ∈ Finset.range (N + 1), f n = (∑ n ∈ Finset.range N, f n) + f N := by
        rw [Finset.sum_range_succ]
      rw [h₁, ih]
      have h₂ : f N = (1 / ((N : ℝ) + 1)) - (1 / (((N : ℝ) + 1) + 1)) := by
        simp [f] ; ring
      rw [h₂]
      field_simp
      ring
  let g : ℕ → ℝ := fun N ↦ 1 - 1 / ((N : ℝ) + 1)
  have h₁ : ∀ N : ℕ, ∑ n ∈ Finset.range N, f n = g N := by
    intro N
    exact h_partial_sum N
  have h_eq : (fun n : ℕ ↦ ∑ i ∈ Finset.range n, f i) = g := by
    funext n
    exact h₁ n
  have h₃ : ¬ Filter.Tendsto g Filter.atTop Filter.atTop := by
    intro h
    have h₄ : ∀ (B : ℝ), ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ → g n ≥ B := by
      exact Filter.tendsto_atTop_atTop.mp h
    have h₅ := h₄ 2
    rcases h₅ with ⟨N₀, hN₀⟩
    have h₆ : g N₀ ≥ 2 := hN₀ N₀ (by linarith)
    have h₇ : g N₀ = 1 - 1 / ((N₀ : ℝ) + 1) := by rfl
    rw [h₇] at h₆
    have h₉ : (1 : ℝ) / ((N₀ : ℝ) + 1) > 0 := by positivity
    linarith
  have h₅ : ¬ Filter.Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n, f i) Filter.atTop Filter.atTop := by
    rw [h_eq] ; exact h₃
  have h_sum : Summable f := by
    rw [summable_iff_not_tendsto_nat_atTop_of_nonneg h_nonneg] ; exact h₅
  exact h_sum

lemma round1_h_main_75b9 (S : ℝ)
  (h_S_pos : S > 0)
  (h : ∃ (q : ℚ), (q : ℝ) = S):
  ∃ (P Q : ℕ), Q > 0 ∧ P > 0 ∧ S = (P : ℝ) / (Q : ℝ) := by
  rcases h with ⟨q, hq⟩
  have h1 : (q : ℝ) > 0 := by
    linarith [h_S_pos, hq]
  have hq_pos : 0 < q := by
    exact_mod_cast h1
  have h2 : q.num > 0 := by
    exact Rat.num_pos.mpr hq_pos
  let Q : ℕ := q.den
  have hQ_pos : 0 < Q := q.den_pos
  have h3 : (q : ℚ) = ( (q.num : ℚ) ) / ( (q.den : ℚ) ) := by
    exact Eq.symm (Rat.num_div_den q)
  have h4 : ((q : ℝ)) = (( (q.num : ℝ) ) / ( (q.den : ℝ) )) := by
    exact_mod_cast h3
  have h6 : 0 ≤ q.num := by linarith
  let P' : ℕ := (q.num).toNat
  have hP'_pos : 0 < P' := by
    have h8 : (P' : ℤ) = q.num := by
      simp [P', Int.toNat_of_nonneg h6]
    have h9 : (0 : ℤ) < (P' : ℤ) := by linarith
    exact_mod_cast h9
  have h8 : ((P' : ℤ)) = (q.num) := by
    simp [P', Int.toNat_of_nonneg h6]
  have h7 : (P' : ℝ) = ( (q.num : ℝ) ) := by
    exact_mod_cast h8
  have h9 : S = ((P' : ℝ) / (Q : ℝ)) := by
    have h10 : S = (q : ℝ) := by exact hq.symm
    rw [h10, h4, h7]
  refine' ⟨P', Q, hQ_pos, hP'_pos, h9⟩

theorem round1_sub_lemma2 (a : ℕ → ℕ)
  (sub_lemma1 : ∀ (k n : ℕ), n < k → n + 1 < k → a n * a (n + 1) ∣ ∏ i ∈ Finset.range k, a i):
  ∀ (m n : ℕ), n ≤ m → a n * a (n + 1) ∣ ∏ i ∈ Finset.range (m + 2), a i := by
  grind +ring

theorem round1_h_L_ge_0 (a : ℕ → ℕ)
  (h_prod_ge_one : ∀ n : ℕ, (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) ≥ 1):
  ∀ n : ℕ, Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) ≥ 0 := by
  bound

theorem round1_h1 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n):
  ∀ (m : ℕ), ∃ (K : ℤ), (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (K : ℝ) := by
  intro m
  let P_m := ∏ i ∈ Finset.range (m + 2), (a i : ℝ)
  let S_m := ∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))
  have h1 : P_m * S_m = ∑ n ∈ Finset.range (m + 1), (P_m * (1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) := by
    rw [Finset.mul_sum]
  rw [h1]
  have h2 : ∀ n ∈ Finset.range (m + 1),
      P_m * (1 / ((a n : ℝ) * (a (n + 1) : ℝ))) =
      (∏ i ∈ (Finset.range (m + 2) \ {n, n + 1}), (a i : ℝ)) := by
    intro n hn
    have h3 : n < m + 1 := Finset.mem_range.mp hn
    have h4 : n ≤ m := by omega
    have h5 : (a n : ℝ) > 0 := by exact_mod_cast (h_pos n)
    have h6 : (a (n + 1) : ℝ) > 0 := by exact_mod_cast (h_pos (n + 1))
    have h7 : (a n : ℝ) * (a (n + 1) : ℝ) ≠ 0 := mul_ne_zero h5.ne' h6.ne'
    have h8 := round1_h_main a h_pos m n h4
    have h9 : P_m * (1 / ((a n : ℝ) * (a (n + 1) : ℝ))) =
        P_m / ((a n : ℝ) * (a (n + 1) : ℝ)) := by
      field_simp [h7]
    rw [h9]
    exact h8
  have h3 : ∑ n ∈ Finset.range (m + 1), (P_m * (1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) =
      ∑ n ∈ Finset.range (m + 1), (∏ i ∈ (Finset.range (m + 2) \ {n, n + 1}), (a i : ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact h2 n hn
  rw [h3]
  let K_nat : ℕ := ∑ n ∈ Finset.range (m + 1), (∏ i ∈ (Finset.range (m + 2) \ {n, n + 1}), (a i))
  have h4 : (∑ n ∈ Finset.range (m + 1), (∏ i ∈ (Finset.range (m + 2) \ {n, n + 1}), (a i : ℝ))) = (K_nat : ℝ) := by
    norm_cast
  refine' ⟨(K_nat : ℤ), _⟩
  exact h4

lemma round1_h_summable (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (h2 : ∀ n : ℕ, a n ≥ n + 1):
  Summable (fun n : ℕ => (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
  have h3 : ∀ n : ℕ, 0 ≤ (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ)) := by
    intro n
    have h3₁ : (a n : ℝ) > 0 := by exact_mod_cast (h_pos n)
    have h3₂ : (a (n + 1) : ℝ) > 0 := by exact_mod_cast (h_pos (n + 1))
    positivity
  have h4 : ∀ n : ℕ, (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ)) ≤ (1 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    intro n
    have h4₁ : (a n : ℝ) ≥ ((n : ℝ) + 1) := by exact_mod_cast (h2 n)
    have h4₂ : (a (n + 1) : ℝ) ≥ ((n : ℝ) + 2) := by
      have h4₃ : a (n + 1) ≥ (n + 1) + 1 := by linarith [h2 (n + 1)]
      exact_mod_cast h4₃
    have h4₄ : (a n : ℝ) * (a (n + 1) : ℝ) ≥ (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
      nlinarith
    have h4₅ : 0 < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
    apply one_div_le_one_div_of_le h4₅ h4₄
  have h5 : Summable (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
    have h6 : ∀ n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) = (1 : ℝ) / ((n : ℝ) + 1) - (1 : ℝ) / ((n : ℝ) + 2) := by
      intro n
      field_simp
      ring
    rw [show (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2))) = fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) - (1 : ℝ) / ((n : ℝ) + 2) from by funext n; exact h6 n]
    exact round1_h_sum_telescoping
  exact Summable.of_nonneg_of_le h3 h4 h5

theorem round1_sub_lemma1 (a : ℕ → ℕ):
  ∀ (k n : ℕ), n < k → n + 1 < k → a n * a (n + 1) ∣ ∏ i ∈ Finset.range k, a i := by
  intro k n h1 h2
  exact round1_h_main_7a50 a k n h1 h2

theorem round1_sub_lemma3 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (sub_lemma2 : ∀ (m n : ℕ), n ≤ m → a n * a (n + 1) ∣ ∏ i ∈ Finset.range (m + 2), a i)
  (m : ℕ):
  ∃ Im : ℕ, (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (Im : ℝ) := by
  have h_main : ∃ (k : ℕ → ℕ), ∀ (n : ℕ), n ∈ Finset.range (m + 1) →
      (∏ i ∈ Finset.range (m + 2), a i) = (a n * a (n + 1)) * k n :=
    round1_h_main_6aa1 a m sub_lemma2
  rcases h_main with ⟨k, hk⟩
  exact round1_h_final a m h_pos k hk

theorem round1_sub_lemma4 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (P : ℕ)
  (Q : ℕ)
  (hQ_pos : Q > 0)
  (hP_pos : P > 0)
  (h_sum_eq : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ))
  (x : ℕ → ℝ)
  (hx_def : ∀ m : ℕ, x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))))):
  ∀ m : ℕ, x m > 0 := by
  set u : ℕ → ℝ := fun n => 1 / ((a n : ℝ) * (a (n + 1) : ℝ)) with hu
  have h_pos_u : ∀ n : ℕ, u n > 0 := by
    intro n
    have h1 : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast (h_pos n)
    have h2 : (0 : ℝ) < (a (n + 1) : ℝ) := by exact_mod_cast (h_pos (n + 1))
    positivity
  have h_nonneg : ∀ n : ℕ, 0 ≤ u n := by
    intro n
    have h4 : u n > 0 := h_pos_u n
    linarith
  have h_pos_sum : (0 : ℝ) < (P : ℝ) / (Q : ℝ) := by
    apply div_pos
    · exact_mod_cast hP_pos
    · exact_mod_cast hQ_pos
  have h_summable : Summable u := by
    by_contra h
    have h1 : (∑' n, u n) = 0 := by
      exact tsum_eq_zero_of_not_summable h
    rw [h1] at h_sum_eq
    linarith
  have h1 : ∀ (s : Finset ℕ), ∑ x ∈ s, u x ≤ ∑' x, u x := by
    intro s
    exact Summable.sum_le_tsum s (fun (i : ℕ) (_ : i ∉ s) => h_nonneg i) h_summable
  have h2 : ∀ (m : ℕ), (∑ n ∈ Finset.range (m + 1), u n) ≤ (∑' n, u n) := by
    intro m
    exact h1 (Finset.range (m + 1))
  have h3 : ∀ (m : ℕ), (∑ n ∈ Finset.range (m + 1), u n) < (∑' n, u n) := by
    intro m
    have h7 : (∑ n ∈ Finset.range (m + 1), u n) ≤ (∑' n, u n) := h2 m
    by_contra h
    have h8 : (∑ n ∈ Finset.range (m + 1), u n) = (∑' n, u n) := by linarith
    have h9 : (∑ n ∈ Finset.range (m + 2), u n) = (∑ n ∈ Finset.range (m + 1), u n) + u (m + 1) := by
      rw [Finset.sum_range_succ]
    have h11 : u (m + 1) > 0 := h_pos_u (m + 1)
    have h13 : (∑ n ∈ Finset.range (m + 2), u n) ≤ (∑' n, u n) := h1 (Finset.range (m + 2))
    linarith
  intro m
  have hPm_pos : (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) > 0 := round1_h1_5a8f a h_pos m
  have hTm_pos : ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) > 0 := by
    have h4 : (∑ n ∈ Finset.range (m + 1), u n) < (∑' n, u n) := h3 m
    linarith
  have h_main : x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) := by
    have h_eq1 : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = ∑' n, u n := by
      simp [hu]
    have h_eq2 : (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = ∑ n ∈ Finset.range (m + 1), u n := by
      simp [hu]
    rw [hx_def m, h_eq1, h_eq2]
  rw [h_main]
  exact mul_pos hPm_pos hTm_pos

theorem round1_h3_8ee9 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (x : ℕ → ℝ)
  (hx_def : ∀ m : ℕ, x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))))):
  ∀ m : ℕ, m ≥ 1 → x m = (a (m + 1) : ℝ) * x (m - 1) - (∏ i ∈ Finset.range m, (a i : ℝ)) := by
  intro m hm
  set S := (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) with hS
  set T : ℕ → ℝ := fun n => 1 / ((a n : ℝ) * (a (n + 1) : ℝ)) with hT
  have h_sum : (∑ n ∈ Finset.range (m + 1), T n) = (∑ n ∈ Finset.range m, T n) + T m :=
    round1_h_sum_split a m
  have h_prod1 : (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) = (a (m + 1) : ℝ) * (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) :=
    round1_h_prod1 a m
  have h_prod2 : (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) = (∏ i ∈ Finset.range m, (a i : ℝ)) * (a m : ℝ) * (a (m + 1) : ℝ) :=
    round1_h_prod2 a m
  have h2 : x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (S - (∑ n ∈ Finset.range (m + 1), T n)) := by
    simpa [hS, hT] using hx_def m
  have h_eq1 : (m - 1) + 2 = m + 1 := by omega
  have h_eq2 : (m - 1) + 1 = m := by omega
  have h3 : x (m - 1) = (∏ i ∈ Finset.range ((m - 1) + 2), (a i : ℝ)) * (S - (∑ n ∈ Finset.range ((m - 1) + 1), T n)) :=
    hx_def (m - 1)
  have h4 : (∏ i ∈ Finset.range ((m - 1) + 2), (a i : ℝ)) = (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) := by
    rw [h_eq1]
  have h5 : (∑ n ∈ Finset.range ((m - 1) + 1), T n) = (∑ n ∈ Finset.range m, T n) := by
    rw [h_eq2]
  have h6 : x (m - 1) = (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) * (S - (∑ n ∈ Finset.range m, T n)) := by
    rw [h3, h4, h5]
  let A := (∏ i ∈ Finset.range (m + 2), (a i : ℝ))
  let C := (∑ n ∈ Finset.range m, T n)
  let D := T m
  have h7 : (∑ n ∈ Finset.range (m + 1), T n) = C + D := h_sum
  have h9 : x m = A * (S - (C + D)) := by
    rw [h2, h7]
  have h10 : A * (S - (C + D)) = A * (S - C) - A * D := by
    ring
  have h11 : x m = A * (S - C) - A * D := by
    rw [h9, h10]
  have h12 : (a m : ℝ) > 0 := by exact_mod_cast (h_pos m)
  have h13 : (a (m + 1) : ℝ) > 0 := by exact_mod_cast (h_pos (m + 1))
  have h14 : (a m : ℝ) * (a (m + 1) : ℝ) ≠ 0 := by positivity
  have h15 : D = 1 / ((a m : ℝ) * (a (m + 1) : ℝ)) := by
    simp [hT, D]
  have h16 : A = (∏ i ∈ Finset.range m, (a i : ℝ)) * (a m : ℝ) * (a (m + 1) : ℝ) := h_prod2
  have h17 : A * D = (∏ i ∈ Finset.range m, (a i : ℝ)) := by
    rw [h16, h15]
    field_simp [h14] ; ring
  have h18 : A * (S - C) = (a (m + 1) : ℝ) * ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) * (S - C)) := by
    have h19 : A = (a (m + 1) : ℝ) * (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) := h_prod1
    rw [h19] ; ring
  calc
    x m
      = A * (S - C) - A * D := h11
    _ = (a (m + 1) : ℝ) * ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) * (S - C)) - A * D := by
        rw [h18]
    _ = (a (m + 1) : ℝ) * x (m - 1) - A * D := by rw [h6]
    _ = (a (m + 1) : ℝ) * x (m - 1) - (∏ i ∈ Finset.range m, (a i : ℝ)) := by rw [h17]

theorem round1_h_ineq1 (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n):
  ∀ n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ)) ≤ 1 / (a n : ℝ) - 1 / (a (n + 1) : ℝ) := by
  intro n
  rw [round1_h2' a h_pos n]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← Nat.cast_sub (h_mono.monotone n.le_succ)]
  exact_mod_cast round1_h1' a h_mono n

theorem round1_h_telescoping_sum (a : ℕ → ℕ):
  ∀ k M : ℕ, (∑ n ∈ Finset.range M, (1 / (a (n + k) : ℝ) - 1 / (a (n + k + 1) : ℝ))) = 1 / (a k : ℝ) - 1 / (a (k + M) : ℝ) := by
  intro k M
  let x : ℕ → ℝ := fun n => 1 / (a (n + k) : ℝ)
  have h_main : ∑ n ∈ Finset.range M, (x n - x (n + 1)) = x 0 - x M := round1_h2_ac08 x M
  have h1 : ∀ n : ℕ, x n - x (n + 1) = 1 / (a (n + k) : ℝ) - 1 / (a (n + k + 1) : ℝ) := by
    intro n
    simp only [x]
    ring_nf
  have h2 : ∑ n ∈ Finset.range M, (1 / (a (n + k) : ℝ) - 1 / (a (n + k + 1) : ℝ)) = ∑ n ∈ Finset.range M, (x n - x (n + 1)) := by
    simp_rw [← h1]
  have h3 : x 0 = 1 / (a k : ℝ) := by
    simp [x]
  have h4 : x M = 1 / (a (k + M) : ℝ) := by
    simp [x]
    ring_nf
  rw [h2, h_main, h3, h4]

theorem round1_h4 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (h_ineq1 : ∀ n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ)) ≤ 1 / (a n : ℝ) - 1 / (a ( n + 1) : ℝ))
  (h_telescoping_sum : ∀ k M : ℕ, (∑ n ∈ Finset.range M, (1 / (a (n + k) : ℝ) - 1 / (a (n + k + 1) : ℝ))) = 1 / (a k : ℝ) - 1 / (a (k + M) : ℝ)):
  ∀ k : ℕ, (∑' n : ℕ, 1 / ((a (n + k) : ℝ) * (a (n + k + 1) : ℝ))) ≤ 1 / (a k : ℝ) := by
  intro k
  exact round1_h_main_4c10 a h_pos h_ineq1 h_telescoping_sum k

theorem round1_h_upper_bound (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (K : ℝ)
  (hK_pos : K > 0)
  (h3_rec : ∀ n : ℕ, n ≥ 3 → (a n : ℝ) ≤ K * (∏ i ∈ Finset.range n, (a i : ℝ))):
  ∀ n : ℕ, n ≥ 2 → Real.log (∏ i ∈ Finset.range (n + 2), (a i : ℝ)) ≤ 2 * Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) + Real.log K := by
  intro n hn
  have h1 : (∏ i ∈ Finset.range (n + 2), (a i : ℝ)) =
    (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) * (a (n + 1) : ℝ) :=
    round1_h1_9221 a n
  have h2 : (a (n + 1) : ℝ) ≤ K * (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) :=
    round1_h2_f3dc a n h3_rec hn
  set S₁ := (∏ i ∈ Finset.range (n + 1), (a i : ℝ))
  have hS₁_pos : 0 < S₁ := by
    apply Finset.prod_pos
    intro i _hi
    exact_mod_cast (h_pos i)
  have h_a_pos : 0 < (a (n + 1) : ℝ) := by exact_mod_cast (h_pos (n + 1))
  have h3 : Real.log ((a (n + 1) : ℝ)) ≤ Real.log (K * S₁) := by
    apply Real.log_le_log
    · positivity
    · exact h2
  have h4 : Real.log (K * S₁) = Real.log K + Real.log S₁ := by
    rw [Real.log_mul (by positivity) (by positivity)]
  have h6 : Real.log (∏ i ∈ Finset.range (n + 2), (a i : ℝ)) =
      Real.log S₁ + Real.log ((a (n + 1) : ℝ)) := by
    rw [h1]
    rw [Real.log_mul (by positivity) (by positivity)]
  rw [h6]
  linarith

theorem round1_lemma1 (z : ℕ → ℝ)
  (h_eventually_non_increasing : ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → z (n + 1) ≤ z n)
  (h_bounded_below : ∃ B : ℝ, ∀ n : ℕ, B ≤ z n):
  ∃ R' : ℝ, ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |z n - R'| < ε := by
  rcases h_eventually_non_increasing with ⟨N₀, hN₀⟩
  rcases h_bounded_below with ⟨B, hB⟩
  let S : Set ℝ := Set.range (fun k : ℕ ↦ z (N₀ + k))
  have hS_nonempty : Set.Nonempty S := by
    refine' ⟨z (N₀ + 0), _⟩
    exact ⟨0, by simp⟩
  have hS_bounded_below : BddBelow S := by
    use B
    intro x hx
    rcases hx with ⟨k, rfl⟩
    exact hB (N₀ + k)
  let R' : ℝ := sInf S
  use R'
  intro ε hε
  have h1 : ∃ (x : ℝ), x ∈ S ∧ x < R' + ε := by
    exact exists_lt_of_csInf_lt hS_nonempty (by linarith)
  rcases h1 with ⟨x, hx, h2⟩
  rcases hx with ⟨k, rfl⟩
  let N : ℕ := N₀ + k
  have hN_ge_N₀ : N ≥ N₀ := by omega
  have h3 : z N < R' + ε := by simpa [N] using h2
  use N
  intro n hn
  have h4 : z n ∈ S := by
    refine' ⟨n - N₀, _⟩
    have h5 : n ≥ N₀ := by omega
    have h6 : n = N₀ + (n - N₀) := by omega
    rw [h6] ; simp
  have h5 : R' ≤ z n := csInf_le hS_bounded_below h4
  have h6 : z n ≤ z N := round1_h_main_0295 z N₀ hN₀ N n hN_ge_N₀ hn
  have h7 : z n < R' + ε := by linarith
  have h8 : |z n - R'| < ε := by
    rw [abs_lt]
    constructor <;> linarith
  exact h8

lemma round1_h_pow_gt_x (x : ℝ):
  ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → (2 : ℝ) ^ n > x := by
  rcases exists_nat_gt x with ⟨N, hN⟩
  use N
  intro n hn
  have h_pow : (2 ^ n : ℝ) > n := by exact_mod_cast round1_h_pow_gt_id n
  have h_le : (n : ℝ) ≥ N := by exact_mod_cast hn
  linarith

lemma round1_h_main_6371 (b : ℕ → ℝ)
  (h_b_pos : ∀ n, 0 < b n)
  (h : 1 < Filter.atTop.liminf b):
  ∃ (K : ℝ) (N : ℕ), K > 1 ∧ ∀ (n : ℕ), n ≥ N → b n ≥ K := by
  let T : Set ℝ := { a : ℝ | ∀ᶠ n in Filter.atTop, a ≤ b n }
  have h_def : Filter.atTop.liminf b = sSup T := test_def b
  have hS_nonempty : Set.Nonempty T := by
    refine' ⟨0, _⟩
    filter_upwards with n
    linarith [h_b_pos n]
  have h4 : ∃ (a : ℝ), a ∈ T ∧ 1 < a := by
    by_contra h5
    push_neg at h5
    have h6 : ∀ (x : ℝ), x ∈ T → x ≤ 1 := by simpa using h5
    have h7 : sSup T ≤ 1 := csSup_le hS_nonempty h6
    rw [h_def] at h
    linarith
  rcases h4 with ⟨a, ha_T, ha1⟩
  rcases Filter.eventually_atTop.mp ha_T with ⟨N, hN⟩
  exact ⟨a, N, ha1, hN⟩

theorem round1_h_sub :
  ∀ (M : ℝ), M > 0 → ∃ N' : ℕ, ∀ n : ℕ, n ≥ N' → (2 : ℝ) ^ n > M := by
  intro M _
  obtain ⟨N, hN⟩ := exists_nat_gt M
  use N
  intro n hn
  have : (n : ℝ) ≥ N := by exact_mod_cast hn
  linarith [round1_h_main_ineq_9cca n]

theorem round1_lemma3_limit_inequality (h_sub : ∀ (M : ℝ), M > 0 → ∃ N' : ℕ, ∀ n : ℕ, n ≥ N' → (2 : ℝ) ^ n > M):
  ∀ (K_0 : ℝ) (δ : ℝ), δ > 0 → ∃ N' : ℕ, ∀ n : ℕ, n ≥ N' → K_0 / (2 : ℝ) ^ n > -δ := by
  intro K_0 δ hδ
  exact round1_main_goal h_sub K_0 δ hδ

theorem round1_lemma1_sum_log (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n):
  ∀ n : ℕ, Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) = ∑ i ∈ Finset.range (n + 1), Real.log ((a i : ℝ)) := by
  intro n
  have h₁ : ∀ i ∈ Finset.range (n + 1), (a i : ℝ) ≠ 0 := fun i _ ↦
    ne_of_gt (by exact_mod_cast h_pos i)
  exact round1_prod_log n (fun i ↦ (a i : ℝ)) h₁

theorem round1_lemma2_geometric_sum (N : ℕ):
  ∀ n : ℕ, n ≥ N → (∑ i ∈ Finset.Ico N (n + 1), (2 : ℝ) ^ i) = (2 : ℝ) ^ (n + 1) - (2 : ℝ) ^ N := by
  have h_main : ∀ (n : ℕ), (n ≥ N → (∑ i ∈ Finset.Ico N (n + 1), (2 : ℝ) ^ i) = (2 : ℝ) ^ (n + 1) - (2 : ℝ) ^ N) :=
    round1_h_main_a15a N
  exact h_main

theorem round1_lemma2_sum_bound (a : ℕ → ℕ)
  (c : ℝ)
  (N : ℕ)
  (h_ineq1 : ∀ n : ℕ, n ≥ N → Real.log (a n : ℝ) > c * (2 : ℝ) ^ n)
  (lemma2_geometric_sum : ∀ n : ℕ, n ≥ N → (∑ i ∈ Finset.Ico N (n + 1), (2 : ℝ) ^ i) = (2 : ℝ) ^ (n + 1) - (2 : ℝ) ^ N):
  ∀ n : ℕ, n ≥ N → (∑ i ∈ Finset.range (n + 1), Real.log ((a i : ℝ))) > (∑ i ∈ Finset.range N, Real.log ((a i : ℝ))) - c * (2 : ℝ) ^ N + c * (2 : ℝ) ^ (n + 1) := by
  intro n hn
  have h_sum_split : ∑ i ∈ Finset.range (n + 1), Real.log ((a i : ℝ)) =
      (∑ i ∈ Finset.range N, Real.log ((a i : ℝ))) + (∑ i ∈ Finset.Ico N (n + 1), Real.log ((a i : ℝ))) :=
    round1_h_sum_split_7870 a n N hn
  have h_geom : (∑ i ∈ Finset.Ico N (n + 1), (2 : ℝ) ^ i) = (2 : ℝ) ^ (n + 1) - (2 : ℝ) ^ N :=
    lemma2_geometric_sum n hn
  have h_sum_lower_bound : ∑ i ∈ Finset.Ico N (n + 1), Real.log ((a i : ℝ)) > c * (∑ i ∈ Finset.Ico N (n + 1), (2 : ℝ) ^ i) :=
    round1_h_sum_lower_bound a c N n hn h_ineq1
  have h_ineq3 : ∑ i ∈ Finset.Ico N (n + 1), Real.log ((a i : ℝ)) > c * ((2 : ℝ) ^ (n + 1) - (2 : ℝ) ^ N) := by
    rw [h_geom] at h_sum_lower_bound
    exact h_sum_lower_bound
  rw [h_sum_split]
  linarith

lemma round1_h_xn_nonneg (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n):
  ∀ n : ℕ, (Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) / (2 : ℝ) ^ n) ≥ 0 := by
  intro n
  let s := Finset.range (n + 1)
  have h₁ : ∀ i ∈ s, (a i : ℝ) ≥ 1 := fun i _ => by exact_mod_cast Nat.succ_le_of_lt (h_pos i)
  have h₄ : (∏ i ∈ s, (a i : ℝ)) ≥ 1 := round1_h_prod_ge_one_nat a s h₁
  have h₅ : Real.log (∏ i ∈ s, (a i : ℝ)) ≥ 0 := Real.log_nonneg h₄
  have h₇ : (Real.log (∏ i ∈ s, (a i : ℝ)) / (2 : ℝ) ^ n) ≥ 0 := div_nonneg h₅ (by positivity)
  simpa [s] using h₇

theorem round1_log_a_n_div_2_pow_n_converges_to_R_div_2 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (R : ℝ)
  (h_R_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) / (2 : ℝ) ^ n) - R| < ε):
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (a n : ℝ) / (2 : ℝ) ^ n) - R / 2| < ε := by
  intro ε hε
  have hε' : 0 < (2 * ε) / 3 := by positivity
  have h1 : ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 → |(Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) / (2 : ℝ) ^ n) - R| < (2 * ε) / 3 :=
    h_R_converges ((2 * ε) / 3) hε'
  rcases h1 with ⟨N0, hN0⟩
  use N0 + 1
  intro n hn
  have h2 : n ≥ N0 + 1 := hn
  have h3 : n ≥ N0 := by linarith
  have h4 : n - 1 ≥ N0 := by omega
  set L_n := (Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) / (2 : ℝ) ^ n) with hL_n
  have h5 : (n - 1) + 1 = n := by omega
  have h6' : ∏ i ∈ Finset.range ((n - 1) + 1), (a i : ℝ) = ∏ i ∈ Finset.range n, (a i : ℝ) := by
    rw [h5]
  set L_n1 := (Real.log (∏ i ∈ Finset.range n, (a i : ℝ)) / (2 : ℝ) ^ (n - 1)) with hL_n1
  have h7 : |L_n - R| < (2 * ε) / 3 := hN0 n h3
  have h8 : |(Real.log (∏ i ∈ Finset.range ((n - 1) + 1), (a i : ℝ)) / (2 : ℝ) ^ (n - 1) - R)| < (2 * ε) / 3 :=
    hN0 (n - 1) h4
  have h9 : |L_n1 - R| < (2 * ε) / 3 := by
    rw [h6'] at h8
    exact h8
  have h10 : (Real.log (a n : ℝ) / (2 : ℝ) ^ n) = L_n - (1 / 2 : ℝ) * L_n1 :=
    round1_h_main_identity a h_pos n (by omega)
  rw [h10]
  have h11 : |(L_n - (1 / 2 : ℝ) * L_n1 - R / 2)| ≤ |L_n - R| + (1 / 2 : ℝ) * |L_n1 - R| := by
    calc
      |(L_n - (1 / 2 : ℝ) * L_n1 - R / 2)|
        = |( (L_n - R) - (1 / 2 : ℝ) * (L_n1 - R) )| := by ring_nf
      _ ≤ |L_n - R| + |(1 / 2 : ℝ) * (L_n1 - R)| := by apply abs_sub
      _ = |L_n - R| + (1 / 2 : ℝ) * |L_n1 - R| := by
        simp [abs_mul]
  have h12 : |(L_n - (1 / 2 : ℝ) * L_n1 - R / 2)| < ε := by
    linarith [abs_lt.mp h7, abs_lt.mp h9]
  exact h12

lemma round1_h_sum_upper_bound (a : ℕ → ℕ)
  (R : ℝ)
  (N : ℕ)
  (hN : ∀ n : ℕ, n ≥ N → Real.log (a n : ℝ) < (5 * R / 8) * (2 : ℝ) ^ n)
  (m : ℕ)
  (hm : m ≥ N):
  ∑ i ∈ Finset.range (m + 1), Real.log (a i : ℝ) <
    (∑ i ∈ Finset.range N, Real.log (a i : ℝ)) - (5 * R / 8) * (2 : ℝ) ^ N
    + (5 * R / 8) * (2 : ℝ) ^ (m + 1) := by
  have h₁ : m + 1 ≥ N := by linarith
  have h₂ : Finset.range (m + 1) = Finset.range N ∪ Finset.Ico N (m + 1) := by
    ext x
    simp [Finset.mem_range, Finset.mem_Ico] ; omega
  have h₃ : Disjoint (Finset.range N) (Finset.Ico N (m + 1)) := by
    rw [Finset.disjoint_left] ; intro x hx₁ hx₂ ; simp [Finset.mem_range, Finset.mem_Ico] at hx₁ hx₂ ; omega
  have h₄ : ∑ i ∈ Finset.range (m + 1), Real.log (a i : ℝ) =
      ∑ i ∈ Finset.range N, Real.log (a i : ℝ) + ∑ i ∈ Finset.Ico N (m + 1), Real.log (a i : ℝ) := by
    rw [h₂, Finset.sum_union h₃]
  rw [h₄]
  have h₅ : ∑ i ∈ Finset.Ico N (m + 1), Real.log (a i : ℝ) <
      ∑ i ∈ Finset.Ico N (m + 1), (5 * R / 8) * (2 : ℝ) ^ i := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨N, by simp ; omega⟩
    · intro i hi
      have h₆ : N ≤ i := (Finset.mem_Ico.mp hi).1
      exact hN i h₆
  have h₆ : ∑ i ∈ Finset.Ico N (m + 1), (5 * R / 8) * (2 : ℝ) ^ i =
      (5 * R / 8) * ∑ i ∈ Finset.Ico N (m + 1), (2 : ℝ) ^ i := by
    rw [Finset.mul_sum]
  rw [h₆] at h₅
  have h₇ : ∑ i ∈ Finset.Ico N (m + 1), (2 : ℝ) ^ i = (2 : ℝ) ^ (m + 1) - (2 : ℝ) ^ N :=
    round1_h_sum_ico_pow N m h₁
  rw [h₇] at h₅
  linarith

theorem round1_h1_d500 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n):
  ∀ m : ℕ, ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) > 0 := by
  intro m
  apply div_pos
  · apply round1_h_prod_pos
    exact fun i _ => by exact_mod_cast h_pos i
  · exact_mod_cast h_pos (m + 2)

theorem round1_h2_8d71 (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n):
  ∀ m : ℕ, 0 < (a (m + 1) : ℝ) / (a (m + 3) : ℝ) ∧ (a (m + 1) : ℝ) / (a (m + 3) : ℝ) < 1 := by
  intro m
  exact round1_h_main_ebf0 a h_mono h_pos m

lemma round1_h9 (R : ℝ)
  (hR_pos : R > 0):
  Filter.Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n * (-3 * R / 4)) Filter.atTop Filter.atBot := by
  have hC : (-3 * R / 4 : ℝ) < 0 := by linarith
  set C := (-3 * R / 4 : ℝ) with hC_def
  have hD_pos : 0 < -C := by
    dsimp only [C] ; linarith
  have h_main : ∀ (b : ℝ), ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → (2 : ℝ) ^ n * C ≤ b := by
    intro b
    set D := -C
    have hD_pos' : 0 < D := hD_pos
    set X : ℝ := (-b) / D with hX_def
    have h1 : ∃ (k : ℕ), (k : ℝ) > X := exists_nat_gt X
    rcases h1 with ⟨k, hk⟩
    let m := k + 1
    have h2 : (2 : ℕ) ^ m > k := round1_h_aux k
    have h3 : ((2 : ℕ) ^ m : ℝ) > (k : ℝ) := by exact_mod_cast h2
    use m
    intro n hn
    have h4 : (2 : ℝ) ^ n ≥ (2 : ℝ) ^ m := by
      have h_nat : (2 : ℕ) ^ m ≤ (2 : ℕ) ^ n := Nat.pow_le_pow_right (by norm_num) hn
      exact_mod_cast h_nat
    have h10 : (2 : ℝ) ^ n > X := by
      calc
        (2 : ℝ) ^ n ≥ (2 : ℝ) ^ m := h4
        _ > (k : ℝ) := h3
        _ > X := hk
    have h11 : (2 : ℝ) ^ n * D > (-b) := by
      have h13 : (2 : ℝ) ^ n * D > X * D := by gcongr
      have h14 : X * D = (-b) := by
        rw [hX_def] ; field_simp [hD_pos'.ne']
      linarith
    have h15 : (2 : ℝ) ^ n * C = - ((2 : ℝ) ^ n * D) := by
      dsimp only [C, D] ; ring
    rw [h15] ; linarith
  simpa [Filter.tendsto_atBot] using h_main

lemma round1_h_main_826e (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (P : ℕ)
  (Q : ℕ)
  (hQ_pos : Q > 0)
  (hP_pos : P > 0)
  (h_sum_eq : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ)):
  ∀ (m : ℕ),
    (∑' n : ℕ, (1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) -
    (∑ n ∈ Finset.range (m + 1), (1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) =
    ∑' k : ℕ, (1 / ((a ((m + 1) + k) : ℝ) * (a (((m + 1) + k) + 1) : ℝ))) := by
  intro m
  have hf := round1_h_summable_9d78 a P Q hQ_pos hP_pos h_sum_eq
  rw [← hf.sum_add_tsum_nat_add (m + 1), add_sub_cancel_left]
  congr; ext; rw [add_comm]

theorem round1_ratio_inequality (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (N0 : ℕ)
  (hN0 : ∀ n : ℕ, n ≥ N0 → ((a n : ℝ) / (a (n + 2) : ℝ)) < 1 / 2):
  ∀ (m : ℕ), m ≥ N0 → ∀ (k : ℕ), k ≥ 1 →
    let T := fun (k : ℕ) (m : ℕ) => (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + k) : ℝ) * (a (m + k + 1) : ℝ))
    (T (k + 1) m) < (1 / 2) * (T k m) := by
  intro m hm k hk T
  have hT_pos : 0 < T k m := by
    unfold T
    refine div_pos (Finset.prod_pos fun i _ => by exact_mod_cast h_pos i) (mul_pos ?_ ?_)
    all_goals exact_mod_cast h_pos _
  calc
    T (k + 1) m = T k m * ((a (m + k) : ℝ) / (a (m + k + 2) : ℝ)) := by
      simpa [T] using round1_h_main_identity_a39d a h_pos k m
    _ < T k m * (1 / 2) := (mul_lt_mul_left hT_pos).mpr (hN0 (m + k) (by omega))
    _ = (1 / 2) * T k m := by ring

theorem round1_tail_bound (m : ℕ)
  (T : ℕ → ℕ → ℝ)
  (h_ineq : ∀ k : ℕ, k ≥ 1 → T (k + 1) m < (1 / 2) * (T k m))
  (h_pos_T : ∀ k : ℕ, T k m > 0):
  (∑' k : ℕ, T (k + 3) m) ≤ T 2 m := by
  let f : ℕ → ℝ := fun k => T (k + 3) m
  let g : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (k + 1) * T 2 m
  have h_main_ineq : ∀ (k : ℕ), f k < g k :=
    round1_h_main_ineq_5c86 m T h_ineq
  have h0 : ∀ (k : ℕ), 0 ≤ f k := by
    intro k
    have h₅ : f k > 0 := h_pos_T (k + 3)
    linarith
  have h1 : ∀ (k : ℕ), f k ≤ g k := by
    intro k
    exact le_of_lt (h_main_ineq k)
  have h2 : ∃ (i : ℕ), f i < g i := ⟨0, h_main_ineq 0⟩
  rcases h2 with ⟨i, hi⟩
  have h_summable₁ : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) := by
    have h₅ : (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) = fun k : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k := by
      funext k
      ring
    rw [h₅]
    have h₆ : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) := by
      apply summable_geometric_of_lt_one
      <;> norm_num
    exact Summable.mul_left (1 / 2 : ℝ) h₆
  have h_summable_g : Summable g := by
    have h₇ : g = fun k : ℕ => (T 2 m) * ((1 / 2 : ℝ) ^ (k + 1)) := by
      funext k
      ring
    rw [h₇]
    exact Summable.mul_left (T 2 m) h_summable₁
  have h_tsum_lt : (∑' k : ℕ, f k) < (∑' k : ℕ, g k) := by
    exact Summable.tsum_lt_tsum_of_nonneg h0 h1 hi h_summable_g
  have h_tsum_eq : (∑' k : ℕ, g k) = T 2 m := by
    have h₃ : (∑' k : ℕ, g k) = (∑' k : ℕ, ((1 / 2 : ℝ) ^ (k + 1) * T 2 m)) := by rfl
    rw [h₃]
    have h₄ : (∑' k : ℕ, ((1 / 2 : ℝ) ^ (k + 1) * T 2 m)) = (∑' k : ℕ, (T 2 m) * ((1 / 2 : ℝ) ^ (k + 1))) := by
      congr 1 ; funext k ; ring
    rw [h₄]
    have h₅ : (∑' k : ℕ, (T 2 m) * ((1 / 2 : ℝ) ^ (k + 1))) = (T 2 m) * (∑' k : ℕ, (1 / 2 : ℝ) ^ (k + 1)) := by
      exact Summable.tsum_mul_left (T (2 : ℕ) m) h_summable₁
    rw [h₅]
    rw [round1_h_sum_geom] ; ring
  rw [h_tsum_eq] at h_tsum_lt
  linarith

theorem round1_lemma_T_identity (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (m : ℕ)
  (T : ℕ → ℕ → ℝ)
  (hT_def : ∀ k : ℕ, T k m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + k) : ℝ) * (a (m + k + 1) : ℝ))):
  ∀ k : ℕ, T (k + 1) m = T k m * ((a (m + k) : ℝ) / (a (m + k + 2) : ℝ)) := by
  intro k
  set P_m := (∏ i ∈ Finset.range (m + 2), (a i : ℝ))
  have h1 : (0 : ℝ) < (a (m + k) : ℝ) := round1_h1_2d60 a h_pos m k
  have h2 : (0 : ℝ) < (a (m + k + 1) : ℝ) := round1_h2_8c70 a h_pos m k
  have h3 : (0 : ℝ) < (a (m + k + 2) : ℝ) := round1_h3_c582 a h_pos m k
  have h4 : (a (m + (k + 1)) : ℝ) = (a (m + k + 1) : ℝ) := by
    congr 1
  have h5 : (a (m + (k + 1) + 1) : ℝ) = (a (m + k + 2) : ℝ) := by
    congr 1
  have hT1 : T (k + 1) m = P_m / ((a (m + (k + 1)) : ℝ) * (a (m + (k + 1) + 1) : ℝ)) := by
    simpa using hT_def (k + 1)
  have hT2 : T k m = P_m / ((a (m + k) : ℝ) * (a (m + k + 1) : ℝ)) := by
    simpa using hT_def k
  rw [hT1, hT2]
  rw [h4, h5]
  field_simp [h1.ne', h2.ne', h3.ne']
  ring

theorem round1_lemma_summable_from_ratio (f : ℕ → ℝ)
  (h_pos : ∀ n : ℕ, f n > 0)
  (h_ratio : ∃ K : ℕ, ∀ n : ℕ, n ≥ K → f (n + 1) < (1 / 2) * f n):
  Summable f := by
  rcases h_ratio with ⟨K, h_ratio⟩
  have h_f_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    have h1 : f n > 0 := h_pos n
    linarith
  have h1 : ∀ (m : ℕ), f (K + m) ≤ f K * (1 / 2 : ℝ) ^ m := round1_h1_988e f K h_ratio
  have h2 : ∀ (m : ℕ), 0 ≤ f (K + m) := by
    intro m
    have h21 : f (K + m) > 0 := h_pos (K + m)
    linarith
  let g : ℕ → ℝ := fun m => f K * (1 / 2 : ℝ) ^ m
  have h3 : Summable g := by
    have h4 : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ m) := by
      apply summable_geometric_of_lt_one
      <;> norm_num
    exact Summable.mul_left (f K) h4
  have h4 : Summable (fun m : ℕ => f (K + m)) := by
    apply Summable.of_nonneg_of_le h2 h1 h3
  let h : ℕ → ℝ := fun m => f (K + m)
  have h_sum : Summable h := h4
  have h_nonneg : ∀ (m : ℕ), 0 ≤ h m := by
    intro m
    exact h2 m
  let C : ℝ := ∑' (m : ℕ), h m
  have hC_nonneg : 0 ≤ C := by
    exact tsum_nonneg h_nonneg
  have h_hasSum : HasSum h C := h_sum.hasSum
  have h15 : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, h i) Filter.atTop (nhds C) := by
    exact (hasSum_iff_tendsto_nat_of_nonneg h2 C).mp h_hasSum
  have h19 : ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |(∑ i ∈ Finset.range n, h i) - C| < 1 := by
    exact Metric.tendsto_atTop.mp h15 1 (by norm_num)
  rcases h19 with ⟨N, hN⟩
  have h20 : ∀ (n : ℕ), n ≥ N → (∑ i ∈ Finset.range n, h i) ≤ C + 1 := by
    intro n hn
    have h21 : |(∑ i ∈ Finset.range n, h i) - C| < 1 := hN n hn
    have h22 : (∑ i ∈ Finset.range n, h i) - C < 1 := by
      linarith [abs_lt.mp h21]
    linarith
  let S := Finset.range N
  let A := Finset.image (fun (n : ℕ) ↦ ∑ i ∈ Finset.range n, h i) S
  have hA_bounded : ∃ (B1 : ℝ), ∀ (x : ℝ), x ∈ A → x ≤ B1 := by
    exact Finset.bddAbove A
  rcases hA_bounded with ⟨B1, hB1⟩
  let B := max B1 (C + 1)
  have h23 : C + 1 ≤ B := by
    exact le_max_right B1 (C + 1)
  have hB_nonneg : 0 ≤ B := by linarith
  have h_bounded : ∀ (n : ℕ), (∑ i ∈ Finset.range n, h i) ≤ B := by
    intro n
    by_cases h24 : n < N
    ·
      have h25 : n ∈ S := Finset.mem_range.mpr h24
      have h26 : (∑ i ∈ Finset.range n, h i) ∈ A := by
        exact Finset.mem_image.mpr ⟨n, h25, rfl⟩
      have h27 : (∑ i ∈ Finset.range n, h i) ≤ B1 := hB1 (∑ i ∈ Finset.range n, h i) h26
      have h28 : (∑ i ∈ Finset.range n, h i) ≤ B := by
        exact le_trans h27 (le_max_left B1 (C + 1))
      exact h28
    ·
      have h25 : n ≥ N := by omega
      have h26 : (∑ i ∈ Finset.range n, h i) ≤ C + 1 := h20 n h25
      have h27 : (∑ i ∈ Finset.range n, h i) ≤ B := by
        exact le_trans h26 (le_max_right B1 (C + 1))
      exact h27
  let B' : ℝ := (∑ i ∈ Finset.range K, f i) + B
  have h5 : ∀ (n : ℕ), ∑ i ∈ Finset.range n, f i ≤ B' := by
    intro n
    by_cases h6 : n < K
    ·
      have h7 : n ≤ K := by omega
      have h8 : ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range K, f i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_subset.mpr (by omega)
        · exact fun i _ _ => h_f_nonneg i
      have h10 : ∑ i ∈ Finset.range K, f i ≤ (∑ i ∈ Finset.range K, f i) + B := by
        linarith [hB_nonneg]
      linarith
    ·
      have h7 : n ≥ K := by omega
      have h8 : ∃ (M : ℕ), n = K + M := by
        refine' ⟨n - K, by omega⟩
      rcases h8 with ⟨M, rfl⟩
      have h9 : ∑ i ∈ Finset.range (K + M), f i = (∑ i ∈ Finset.range K, f i) + ∑ m ∈ Finset.range M, h m := by
        have h10 : Finset.range (K + M) = Finset.range K ∪ Finset.Ico K (K + M) := by
          ext x
          simp [Finset.mem_range, Finset.mem_Ico] ; omega
        have h11 : Disjoint (Finset.range K) (Finset.Ico K (K + M)) := by
          rw [Finset.disjoint_left] ; intro x hx1 hx2 ; simp [Finset.mem_range, Finset.mem_Ico] at hx1 hx2 ; omega
        rw [h10]
        rw [Finset.sum_union h11]
        have h12 : ∑ i ∈ Finset.Ico K (K + M), f i = ∑ m ∈ Finset.range M, h m := by
          rw [Finset.sum_Ico_eq_sum_range]
          simp [h]
        rw [h12]
      rw [h9]
      have h13 : ∑ m ∈ Finset.range M, h m ≤ B := h_bounded M
      linarith
  have h6 : Summable f := by
    apply summable_of_sum_range_le h_f_nonneg h5
  exact h6

theorem round1_T1_eq (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (m : ℕ)
  (T : ℕ → ℕ → ℝ)
  (hT_def : ∀ k : ℕ, T k m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + k) : ℝ) * (a (m + k + 1) : ℝ))):
  T 1 m = ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) := by
  exact round1_h_main_e2d5 a h_pos m T hT_def

theorem round1_contradiction_from_convergence (Q : ℕ)
  (hQ_pos : Q > 0)
  (x : ℕ → ℝ)
  (hx_ge : ∀ m : ℕ, x m ≥ 1 / (Q : ℝ))
  (h_xm_converges_to_0 : ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, m ≥ N → |x m - 0| < ε):
  False := by
  have h1 : (1 : ℝ) / (Q : ℝ) > 0 := round1_h1_d71c Q hQ_pos
  have h2 : ∃ (N : ℕ), ∀ (m : ℕ), m ≥ N → |x m - 0| < (1 : ℝ) / (Q : ℝ) :=
    h_xm_converges_to_0 ((1 : ℝ) / (Q : ℝ)) h1
  rcases h2 with ⟨N, hN⟩
  have h3 : ∀ (m : ℕ), m ≥ N → |x m| < (1 : ℝ) / (Q : ℝ) := by
    intro m hm
    have h4 : |x m - 0| < (1 : ℝ) / (Q : ℝ) := hN m hm
    simpa using h4
  have h5 : ∀ (m : ℕ), m ≥ N → x m < (1 : ℝ) / (Q : ℝ) := by
    intro m hm
    have h6 : |x m| < (1 : ℝ) / (Q : ℝ) := h3 m hm
    have h7 : -((1 : ℝ) / (Q : ℝ)) < x m ∧ x m < (1 : ℝ) / (Q : ℝ) := by
      exact abs_lt.mp h6
    exact h7.2
  have h8 : ∃ (m : ℕ), m ≥ N := ⟨N, by linarith⟩
  rcases h8 with ⟨m, hm⟩
  have h9 : x m < (1 : ℝ) / (Q : ℝ) := h5 m hm
  have h10 : x m ≥ (1 : ℝ) / (Q : ℝ) := hx_ge m
  linarith

lemma round1_h_summable_fbf3 (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n):
  Summable (fun n : ℕ ↦ 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
  have h1 : ∀ n : ℕ, (a n : ℝ) ≥ (n : ℝ) + 1 := by
    intro n
    induction n with
    | zero =>
      have h1 : 0 < a 0 := h_pos 0
      have h2 : (a 0 : ℝ) ≥ 1 := by exact_mod_cast (by linarith)
      norm_num at * ; linarith
    | succ n ih =>
      have h2 : a (n + 1) > a n := h_mono (by linarith)
      have h3 : a (n + 1) ≥ a n + 1 := by linarith
      have h4 : (a (n + 1) : ℝ) ≥ (a n : ℝ) + 1 := by exact_mod_cast h3
      have h5 : (a (n + 1) : ℝ) ≥ ((n : ℝ) + 1) + 1 := by linarith
      simp [Nat.cast_add] at * ; linarith
  have h2 : ∀ n : ℕ, 0 ≤ 1 / ((a n : ℝ) * (a (n + 1) : ℝ)) := by
    intro n
    have h_pos1 : 0 < (a n : ℝ) := by exact_mod_cast (h_pos n)
    have h_pos2 : 0 < (a (n + 1) : ℝ) := by exact_mod_cast (h_pos (n + 1))
    positivity
  have h3 : ∀ n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ)) ≤ 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    intro n
    have h4 : (a n : ℝ) ≥ (n : ℝ) + 1 := h1 n
    have h5 : (a (n + 1) : ℝ) ≥ ((n : ℝ) + 2) := by
      have h6 := h1 (n + 1)
      simp [Nat.cast_add] at h6 ⊢ ; linarith
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  have h4 : Summable (fun n : ℕ ↦ 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
    have h5 : (fun n : ℕ ↦ 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) = (fun n : ℕ ↦ (1 / ((n : ℝ) + 1)) - (1 / ((n : ℝ) + 2))) := by
      funext n
      field_simp ; ring
    rw [h5]
    exact round1_h_telescoping_summable
  exact Summable.of_nonneg_of_le h2 h3 h4

theorem round1_rational_implies_exists_P_Q (S : ℝ)
  (h_S_pos : S > 0)
  (h : ∃ (q : ℚ), (q : ℝ) = S):
  ∃ (P Q : ℕ), Q > 0 ∧ P > 0 ∧ S = (P : ℝ) / (Q : ℝ) := by
  exact round1_h_main_75b9 S h_S_pos h

theorem round1_h3 (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n):
  ∀ (m : ℕ), (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) > 0 := by
  have h1 : ∀ n : ℕ, 0 < (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ)) := round1_h1_90e6 a h_pos
  have h2 : ∀ n : ℕ, a n ≥ n + 1 := round1_h2 a h_mono h_pos
  have h_summable : Summable (fun n : ℕ => (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ))) :=
    round1_h_summable a h_pos h2
  have hS_pos : 0 < (∑' n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) :=
    round1_hS_pos a h1 h_summable
  intro m
  set S := (∑' n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) with hS
  set S_m := (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) with hS_m
  have h_pos_prod : 0 < (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) := by
    apply Finset.prod_pos
    intro i _
    exact_mod_cast (h_pos i)
  let f : ℕ → ℝ := fun n => (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ))
  have h_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    exact le_of_lt (h1 n)
  have h5 : ∀ n : ℕ, 0 < f n := h1
  let k : ℕ := m + 1
  let g : ℕ → ℝ := fun i => f (i + k)
  have h_inj : Function.Injective (fun (i : ℕ) => i + k) := by
    intro i₁ i₂ h
    simpa using h
  have h_sum_g : Summable g := by
    exact h_summable.comp_injective h_inj
  have h_pos_g : ∀ i : ℕ, 0 < g i := by
    intro i
    have h6 : 0 < f (i + k) := h5 (i + k)
    simpa [g] using h6
  have h_nonneg_g : ∀ i : ℕ, 0 ≤ g i := by
    intro i
    exact le_of_lt (h_pos_g i)
  let h : ℕ → NNReal := fun i => ⟨g i, h_nonneg_g i⟩
  have h2' : Summable h := by
    have h2₁ : (∀ n : ℕ, 0 ≤ g n) := h_nonneg_g
    have h2₂ : Summable (fun n : ℕ => (h n)) ↔ Summable g := NNReal.summable_mk h2₁
    exact h2₂.mpr h_sum_g
  have h14 : (0 : NNReal) < ∑' (i : ℕ), h i := NNReal.tsum_pos h2' (i := (0 : ℕ)) (by exact_mod_cast h_pos_g 0)
  have h11 : (0 : ℝ) < (∑' (i : ℕ), g i) := by
    have h15 : ((0 : NNReal) < ∑' (i : ℕ), h i) := h14
    have h16 : ((∑' (i : ℕ), h i : ℝ)) > (0 : ℝ) := by exact_mod_cast h15
    have h17 : (∑' (i : ℕ), (h i : ℝ)) = (∑' (i : ℕ), g i) := by
      simp [h]
    rw [h17] at h16
    exact h16
  have h14' : (∑' n : ℕ, f n) = (∑ n ∈ Finset.range k, f n) + (∑' i : ℕ, g i) := by
    have h15 : (∑' n : ℕ, f n) = (∑ n ∈ Finset.range k, f n) + (∑' i : ℕ, g i) := by
      exact Eq.symm (Summable.sum_add_tsum_nat_add' h_sum_g)
    exact h15
  have h16 : S_m = ∑ n ∈ Finset.range k, f n := by
    have h17 : k = m + 1 := by rfl
    rw [h17]
  have h_pos_diff : 0 < S - S_m := by
    have h17 : S = S_m + (∑' i : ℕ, g i) := by
      linarith [h14', h16]
    linarith [h11, h17]
  have h_main : 0 < (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (S - S_m) := by
    exact mul_pos h_pos_prod h_pos_diff
  simpa [hS, hS_m] using h_main

theorem round1_h1_251e (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (P : ℕ)
  (Q : ℕ)
  (hQ_pos : Q > 0)
  (hP_pos : P > 0)
  (h_sum_eq : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ))
  (x : ℕ → ℝ)
  (hx_def : ∀ m : ℕ, x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))))):
  ∀ m : ℕ, x m ≥ 1 / (Q : ℝ) := by
  have sub_lemma1 : ∀ (k n : ℕ), n < k → n + 1 < k → a n * a (n + 1) ∣ ∏ i ∈ Finset.range k, a i := by
    exact round1_sub_lemma1 a
  have sub_lemma2 : ∀ (m n : ℕ), n ≤ m → a n * a (n + 1) ∣ ∏ i ∈ Finset.range (m + 2), a i := by
    exact round1_sub_lemma2 a sub_lemma1
  have sub_lemma3 : ∀ (m : ℕ), ∃ Im : ℕ, (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (Im : ℝ) := by
    intro m
    exact round1_sub_lemma3 a h_pos sub_lemma2 m
  have sub_lemma4 : ∀ (m : ℕ), x m > 0 := by
    exact round1_sub_lemma4 a h_pos P Q hQ_pos hP_pos h_sum_eq x hx_def
  intro m
  obtain ⟨Im, h_Im⟩ := sub_lemma3 m
  have hx_pos : x m > 0 := sub_lemma4 m
  have h_eq1 : x m = ((P : ℝ) / (Q : ℝ)) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) - (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
    have h1 : x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range ( m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) := hx_def m
    have h2 : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ) := h_sum_eq
    rw [h1, h2]
    ring_nf
  have h_eq2 : x m = ((P : ℝ) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) - (Q : ℝ) * (Im : ℝ)) / (Q : ℝ) := by
    have h1 : x m = ((P : ℝ) / (Q : ℝ)) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) - (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := h_eq1
    have h2 : (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (Im : ℝ) := by linarith [h_Im]
    rw [h1]
    have h3 : (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (Im : ℝ) := h2
    have h4 : ((P : ℝ) / (Q : ℝ)) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) - (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = ((P : ℝ) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) - (Q : ℝ) * (Im : ℝ)) / (Q : ℝ) := by
      calc
        ((P : ℝ) / (Q : ℝ)) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) - (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ)))
          = ((P : ℝ) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ))) / (Q : ℝ) - (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
            field_simp [hQ_pos]
        _ = ((P : ℝ) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ))) / (Q : ℝ) - (Im : ℝ) := by
            rw [h3]
        _ = ((P : ℝ) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) - (Q : ℝ) * (Im : ℝ)) / (Q : ℝ) := by
            field_simp [hQ_pos]
    rw [h4]
  have h_pos1 : ((P : ℝ) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) - (Q : ℝ) * (Im : ℝ)) > 0 := by
    have hQ_pos' : (Q : ℝ) > 0 := by exact_mod_cast hQ_pos
    have h : x m > 0 := hx_pos
    rw [h_eq2] at h
    have h4 : ((P : ℝ) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) - (Q : ℝ) * (Im : ℝ)) > 0 := by
      by_contra h5
      have h5' : ((P : ℝ) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) - (Q : ℝ) * (Im : ℝ)) ≤ 0 := by linarith
      have h5'' : ((P : ℝ) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) - (Q : ℝ) * (Im : ℝ)) / (Q : ℝ) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg h5'
        linarith [hQ_pos']
      linarith
    linarith
  set A : ℕ := ∏ i ∈ Finset.range (m + 2), a i
  have h9 : (P : ℝ) * (A : ℝ) > (Q : ℝ) * (Im : ℝ) := by
    have h92 : (P : ℝ) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) > (Q : ℝ) * (Im : ℝ) := by linarith [h_pos1]
    have h93 : (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) = (A : ℝ) := by
      norm_cast
    rw [h93] at h92
    linarith
  have h10 : P * A > Q * Im := by
    norm_cast at h9 ⊢
  have h11 : P * A ≥ Q * Im + 1 := by
    omega
  set Nm : ℕ := P * A - Q * Im with hNm_def
  have h12 : Nm ≥ 1 := by
    omega
  have h13 : (Nm : ℝ) ≥ 1 := by exact_mod_cast h12
  have h14 : (Nm : ℝ) = (P : ℝ) * (A : ℝ) - (Q : ℝ) * (Im : ℝ) := by
    have h141 : P * A ≥ Q * Im := by omega
    have h142 : (Nm : ℝ) = ((P : ℝ) * (A : ℝ)) - ((Q : ℝ) * (Im : ℝ)) := by
      simp [hNm_def]
      norm_cast
    exact h142
  have h15 : x m = (Nm : ℝ) / (Q : ℝ) := by
    have h151 : (P : ℝ) * (A : ℝ) = (P : ℝ) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) := by
      have h152 : (A : ℝ) = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) := by
        norm_cast
      rw [h152]
    have h155 : x m = ((P : ℝ) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) - (Q : ℝ) * (Im : ℝ)) / (Q : ℝ) := by
      rw [h_eq2]
    have h156 : (Nm : ℝ) = (P : ℝ) * (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) - (Q : ℝ) * (Im : ℝ) := by
      linarith [h14, h151]
    rw [h155, h156]
  have h16 : (Nm : ℝ) / (Q : ℝ) ≥ 1 / (Q : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [h13]
  linarith [h15, h16]

theorem round1_h2_8af1 (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n)
  (P Q : ℕ)
  (hQ_pos : Q > 0)
  (hP_pos : P > 0)
  (h_sum_eq : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ))
  (x : ℕ → ℝ)
  (hx_def : ∀ m : ℕ, x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))))):
  ∀ m : ℕ, x m ≤ (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) := by
  have h_ineq1 : ∀ n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ)) ≤ 1 / (a n : ℝ) - 1 / (a (n + 1) : ℝ) :=
    round1_h_ineq1 a h_mono h_pos
  have h_telescoping_sum : ∀ k M : ℕ, (∑ n ∈ Finset.range M, (1 / (a (n + k) : ℝ) - 1 / (a (n + k + 1) : ℝ))) = 1 / (a k : ℝ) - 1 / (a (k + M) : ℝ) :=
    round1_h_telescoping_sum a
  have h4 : ∀ k : ℕ, (∑' n : ℕ, 1 / ((a (n + k) : ℝ) * (a (n + k + 1) : ℝ))) ≤ 1 / (a k : ℝ) :=
    round1_h4 a h_pos h_ineq1 h_telescoping_sum
  have h_sum_split : ∀ k : ℕ, (∑' n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range k, (1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) = (∑' n : ℕ, 1 / ((a (n + k) : ℝ) * (a (n + k + 1) : ℝ))) :=
    round1_h_sum_split_fde7 a P Q hQ_pos hP_pos h_sum_eq
  have h9 : ∀ m : ℕ, (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) = (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) * (a (m + 1) : ℝ) := by
    intro m
    rw [Finset.prod_range_succ]
  intro m
  have h52 : (∑' n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), (1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) = (∑' n : ℕ, 1 / ((a (n + (m + 1)) : ℝ) * (a (n + (m + 1) + 1) : ℝ))) := by
    simpa [add_assoc] using h_sum_split (m + 1)
  have h53 : x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑' n : ℕ, 1 / ((a (n + (m + 1)) : ℝ) * (a (n + (m + 1) + 1) : ℝ))) := by
    rw [hx_def m, h52]
  have h54 : (∑' n : ℕ, 1 / ((a (n + (m + 1)) : ℝ) * (a (n + (m + 1) + 1) : ℝ))) ≤ 1 / (a (m + 1) : ℝ) := by
    simpa [add_assoc] using h4 (m + 1)
  have h55 : x m ≤ (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (1 / (a (m + 1) : ℝ)) := by
    have h552 : (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) ≥ 0 :=
      Finset.prod_nonneg (fun i _hi => mod_cast (h_pos i).le)
    have h553 : (∑' n : ℕ, 1 / ((a (n + (m + 1)) : ℝ) * (a (n + (m + 1) + 1) : ℝ))) ≥ 0 :=
      tsum_nonneg (fun _n => by positivity)
    nlinarith [h53, h54, h552, h553]
  have h56 : (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (1 / (a (m + 1) : ℝ)) = (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) := by
    rw [h9 m]
    have : (a (m + 1) : ℝ) > 0 := by exact_mod_cast h_pos (m + 1)
    field_simp
  linarith [h55, h56]

theorem round1_lemma2 (C : ℝ):
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(C * (1 - (1 / 2 : ℝ) ^ n)) - C| < ε := by
  intro ε hε
  by_cases hC : C = 0
  ·
    use 0
    intros
    rw [hC]
    norm_num
    linarith
  ·
    set x : ℝ := |C| / ε with hx
    have h₁ : ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → (2 : ℝ) ^ n > x := round1_h_pow_gt_x x
    rcases h₁ with ⟨N, hN⟩
    use N
    intro n hn
    have h₂ : (2 : ℝ) ^ n > x := hN n hn
    have h₃ : (2 : ℝ) ^ n > 0 := by positivity
    have h₄ : (2 : ℝ) ^ n > |C| / ε := by
      simpa [hx] using h₂
    have h₅ : ε * (2 : ℝ) ^ n > |C| := by
      calc
        ε * (2 : ℝ) ^ n > ε * (|C| / ε) := by gcongr
        _ = |C| := by
          field_simp [hε.ne']
    have h₆ : |C| / (2 : ℝ) ^ n < ε := by
      calc
        |C| / (2 : ℝ) ^ n < (ε * (2 : ℝ) ^ n) / (2 : ℝ) ^ n := by gcongr
        _ = ε := by
          field_simp [h₃.ne']
    rw [round1_h_main_ineq C n]
    exact h₆

theorem round1_lemma1_9f53 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (h_liminf : 1 < Filter.atTop.liminf (fun n ↦ (a n : ℝ) ^ ((1 : ℝ) / 2 ^ n))):
  ∃ (c : ℝ), c > 0 ∧ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → Real.log (a n : ℝ) > c * (2 : ℝ) ^ n := by
  let b : ℕ → ℝ := fun n ↦ (a n : ℝ) ^ ((1 : ℝ) / 2 ^ n)
  have h_b_pos : ∀ n, 0 < b n := by
    intro n
    have h₁ : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast (h_pos n)
    positivity
  have h_main : ∃ (K' : ℝ) (N : ℕ), K' > 1 ∧ ∀ (n : ℕ), n ≥ N → b n ≥ K' :=
    round1_h_main_6371 b h_b_pos h_liminf
  rcases h_main with ⟨K', N, hK'_gt_one, h_ineq⟩
  have h_log_K'_pos : 0 < Real.log K' := Real.log_pos (by linarith)
  set c : ℝ := (1 / 2) * Real.log K' with hc
  have hc_pos : c > 0 := by positivity
  refine' ⟨c, hc_pos, N, _⟩
  intro n hn
  have h1 : b n ≥ K' := h_ineq n hn
  have h2 : (a n : ℝ) > 0 := by exact_mod_cast (h_pos n)
  have h3 : b n = (a n : ℝ) ^ ((1 : ℝ) / 2 ^ n) := by rfl
  rw [h3] at h1
  have h4 : Real.log (((a n : ℝ) ^ ((1 : ℝ) / 2 ^ n))) ≥ Real.log K' := Real.log_le_log (by positivity) h1
  have h5 : Real.log (((a n : ℝ) ^ ((1 : ℝ) / 2 ^ n))) = ((1 : ℝ) / 2 ^ n) * Real.log (a n : ℝ) := by
    rw [Real.log_rpow (by linarith)]
  rw [h5] at h4
  have h7 : (2 : ℝ) ^ n > 0 := by positivity
  have h8 : Real.log (a n : ℝ) ≥ Real.log K' * (2 : ℝ) ^ n := by
    calc
      Real.log (a n : ℝ)
        = ((1 : ℝ) / 2 ^ n) * Real.log (a n : ℝ) * (2 : ℝ) ^ n := by
          field_simp [h7.ne']
      _ ≥ (Real.log K') * (2 : ℝ) ^ n := by gcongr
  have h9 : Real.log (a n : ℝ) > c * (2 : ℝ) ^ n := by
    rw [hc]
    have h12 : Real.log K' * (2 : ℝ) ^ n > ((1 / 2) * Real.log K') * (2 : ℝ) ^ n := by
      nlinarith [h_log_K'_pos]
    linarith
  exact h9

theorem round1_lemma2_b154 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (c : ℝ)
  (N : ℕ)
  (h_ineq1 : ∀ n : ℕ, n ≥ N → Real.log (a n : ℝ) > c * (2 : ℝ) ^ n)
  (δ : ℝ)
  (hδ1 : 0 < δ):
  ∃ N1 : ℕ, ∀ n : ℕ, n ≥ N1 → Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) / (2 : ℝ) ^ n > 2 * c - δ := by
  have h_sub : ∀ (M : ℝ), M > 0 → ∃ N' : ℕ, ∀ n : ℕ, n ≥ N' → (2 : ℝ) ^ n > M := by
    exact round1_h_sub
  have lemma3_limit_inequality : ∀ (K_0 : ℝ) (δ : ℝ), δ > 0 → ∃ N' : ℕ, ∀ n : ℕ, n ≥ N' → K_0 / (2 : ℝ) ^ n > -δ := by
    exact round1_lemma3_limit_inequality h_sub
  have lemma1_sum_log : ∀ n : ℕ, Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) = ∑ i ∈ Finset.range (n + 1), Real.log ((a i : ℝ)) := by
    exact round1_lemma1_sum_log a h_pos
  have lemma2_geometric_sum : ∀ n : ℕ, n ≥ N → (∑ i ∈ Finset.Ico N (n + 1), (2 : ℝ) ^ i) = (2 : ℝ) ^ (n + 1) - (2 : ℝ) ^ N := by
    exact round1_lemma2_geometric_sum N
  have lemma2_sum_bound : ∀ n : ℕ, n ≥ N → (∑ i ∈ Finset.range (n + 1), Real.log ((a i : ℝ))) > (∑ i ∈ Finset.range N, Real.log ((a i : ℝ))) - c * (2 : ℝ) ^ N + c * (2 : ℝ) ^ (n + 1) := by
    exact round1_lemma2_sum_bound a c N h_ineq1 lemma2_geometric_sum
  set K_0 : ℝ := (∑ i ∈ Finset.range N, Real.log ((a i : ℝ))) - c * (2 : ℝ) ^ N with hK0_def
  rcases lemma3_limit_inequality K_0 δ hδ1 with ⟨N', hN'⟩
  let N1 : ℕ := max N N'
  use N1
  intro n hn
  have h_n_ge_N : n ≥ N := by
    have h1 : N1 ≥ N := by apply le_max_left
    linarith
  have h_n_ge_N' : n ≥ N' := by
    have h2 : N1 ≥ N' := by apply le_max_right
    linarith
  have h20 : (∑ i ∈ Finset.range (n + 1), Real.log ((a i : ℝ))) > K_0 + c * (2 : ℝ) ^ (n + 1) := by
    have h201 := lemma2_sum_bound n h_n_ge_N
    linarith [hK0_def]
  have h21 : c * (2 : ℝ) ^ (n + 1) = 2 * c * (2 : ℝ) ^ n := by
    calc
      c * (2 : ℝ) ^ (n + 1) = c * ((2 : ℝ) ^ n * 2) := by
        rw [pow_succ]
      _ = 2 * c * (2 : ℝ) ^ n := by ring
  have h22 : (∑ i ∈ Finset.range (n + 1), Real.log ((a i : ℝ))) > K_0 + 2 * c * (2 : ℝ) ^ n := by
    linarith [h20, h21]
  have h23 : ((∑ i ∈ Finset.range (n + 1), Real.log ((a i : ℝ))) / (2 : ℝ) ^ n) > (K_0 / (2 : ℝ) ^ n) + 2 * c := by
    have h231 : (2 : ℝ) ^ n > 0 := by positivity
    have h : ((∑ i ∈ Finset.range (n + 1), Real.log ((a i : ℝ))) / (2 : ℝ) ^ n) > ((K_0 + 2 * c * (2 : ℝ) ^ n) / (2 : ℝ) ^ n) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    have h233 : ((K_0 + 2 * c * (2 : ℝ) ^ n) / (2 : ℝ) ^ n) = (K_0 / (2 : ℝ) ^ n) + 2 * c := by
      field_simp
    linarith
  have h24 : K_0 / (2 : ℝ) ^ n > -δ := hN' n h_n_ge_N'
  have h25 : ((∑ i ∈ Finset.range (n + 1), Real.log ((a i : ℝ))) / (2 : ℝ) ^ n) > 2 * c - δ := by
    linarith [h23, h24]
  have h26 : Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) = (∑ i ∈ Finset.range (n + 1), Real.log ((a i : ℝ))) := by
    rw [lemma1_sum_log n]
  rw [h26]
  exact h25

theorem round1_lemma3_9883 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (c : ℝ)
  (hc_pos : c > 0)
  (h_ineq2 : ∀ (δ : ℝ), 0 < δ → δ < 2 * c → ∃ N1 : ℕ, ∀ n : ℕ, n ≥ N1 → Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) / (2 : ℝ) ^ n > 2 * c - δ)
  (R : ℝ)
  (h_R_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) / (2 : ℝ) ^ n) - R| < ε):
  R > 0 := by
  let x : ℕ → ℝ := fun n => Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) / (2 : ℝ) ^ n
  have h_xn_nonneg : ∀ n : ℕ, x n ≥ 0 := round1_h_xn_nonneg a h_pos
  have hR_nonneg : R ≥ 0 := round1_hR_nonneg x R h_xn_nonneg h_R_converges
  have h_main₁ : R ≥ 2 * c := by
    by_contra h
    set δ : ℝ := (2 * c - R) / 2 with hδ
    have hδ_pos : 0 < δ := by linarith
    have hδ_lt : δ < 2 * c := by linarith
    rcases h_ineq2 δ hδ_pos hδ_lt with ⟨N1, hN1⟩
    have h₄ : R ≥ 2 * c - δ := round1_h_main_5367 x R h_R_converges (2 * c - δ) ⟨N1, hN1⟩
    linarith
  linarith

theorem round1_lemma1_d8f2 (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (R : ℝ)
  (hR_pos : R > 0)
  (h_log_a_n_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (a n : ℝ) / (2 : ℝ) ^ n) - R / 2| < ε):
  ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, m ≥ N → |((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ))| < ε := by
  intro ε hε
  have h₂ : 0 < ε := hε
  set δ : ℝ := R / 8 with hδ
  have hδ_pos : 0 < δ := by positivity
  have h₃ : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (a n : ℝ) / (2 : ℝ) ^ n) - R / 2| < δ :=
    h_log_a_n_converges δ hδ_pos
  rcases h₃ with ⟨N, hN⟩
  have h₄ : ∀ n : ℕ, n ≥ N → Real.log (a n : ℝ) < (5 * R / 8) * (2 : ℝ) ^ n := by
    intro n hn
    have h₅ : |(Real.log (a n : ℝ) / (2 : ℝ) ^ n) - R / 2| < δ := hN n hn
    have h₆ : (2 : ℝ) ^ n > 0 := by positivity
    have h₇ : (Real.log (a n : ℝ) / (2 : ℝ) ^ n) - R / 2 < δ := by linarith [abs_lt.mp h₅]
    have h₈ : Real.log (a n : ℝ) / (2 : ℝ) ^ n < R / 2 + δ := by linarith [abs_lt.mp h₅]
    have h₉ : Real.log (a n : ℝ) < (R / 2 + δ) * (2 : ℝ) ^ n := by
      calc
        Real.log (a n : ℝ) = (Real.log (a n : ℝ) / (2 : ℝ) ^ n) * (2 : ℝ) ^ n := by field_simp [h₆.ne']
        _ < (R / 2 + δ) * (2 : ℝ) ^ n := by gcongr
    have h₁₀ : (R / 2 + δ) = (5 * R / 8) := by
      rw [hδ] ; ring
    rw [h₁₀] at h₉ ; exact h₉
  have h₅ : ∀ n : ℕ, n ≥ N → Real.log (a n : ℝ) > (3 * R / 8) * (2 : ℝ) ^ n := by
    intro n hn
    have h₆ : |(Real.log (a n : ℝ) / (2 : ℝ) ^ n) - R / 2| < δ := hN n hn
    have h₇ : (2 : ℝ) ^ n > 0 := by positivity
    have h₈ : (Real.log (a n : ℝ) / (2 : ℝ) ^ n) - R / 2 > -δ := by linarith [abs_lt.mp h₆]
    have h₉ : Real.log (a n : ℝ) / (2 : ℝ) ^ n > R / 2 - δ := by linarith
    have h₁₀ : Real.log (a n : ℝ) > (R / 2 - δ) * (2 : ℝ) ^ n := by
      calc
        Real.log (a n : ℝ) = (Real.log (a n : ℝ) / (2 : ℝ) ^ n) * (2 : ℝ) ^ n := by field_simp [h₇.ne']
        _ > (R / 2 - δ) * (2 : ℝ) ^ n := by gcongr
    have h₁₁ : (R / 2 - δ) = (3 * R / 8) := by
      rw [hδ] ; ring
    rw [h₁₁] at h₁₀ ; exact h₁₀
  let C' : ℝ := (∑ i ∈ Finset.range N, Real.log (a i : ℝ)) - (5 * R / 8) * (2 : ℝ) ^ N
  set B : ℝ := (C' - Real.log ε) / (R / 8) with hB
  have hB_pos : (R / 8 : ℝ) > 0 := by positivity
  have h₆ : ∃ (k : ℕ), (k : ℝ) > B := exists_nat_gt B
  rcases h₆ with ⟨k, hk⟩
  have h₇ : ∃ (N' : ℕ), ∀ (m : ℕ), m ≥ N' → (2 : ℝ) ^ (m + 1) ≥ (k : ℝ) := by
    have h₈ : ∃ (N'' : ℕ), (2 : ℝ) ^ N'' ≥ (k : ℝ) := by
      by_cases h₉ : (k : ℝ) ≤ 0
      · refine' ⟨0, _⟩
        norm_num at * ; linarith
      · have h₁₀ : 0 < (k : ℝ) := by linarith
        have h₁₁ : ∃ (n : ℕ), (n : ℝ) > Real.log (k) / Real.log 2 := exists_nat_gt (Real.log (k) / Real.log 2)
        rcases h₁₁ with ⟨n, hn⟩
        have h₁₂ : Real.log 2 > 0 := Real.log_pos (by norm_num)
        have h₁₃ : (n : ℝ) * Real.log 2 > Real.log (k) := by
          calc
            (n : ℝ) * Real.log 2 > (Real.log (k) / Real.log 2) * Real.log 2 := by gcongr
            _ = Real.log (k) := by
              field_simp [h₁₂.ne']
        have h₁₄ : Real.log ((2 : ℝ) ^ n) = (n : ℝ) * Real.log 2 := by
          rw [Real.log_pow]
        have h₁₈ : (2 : ℝ) ^ n > (k : ℝ) := by
          by_contra h₁₉
          have h₂₀ : (2 : ℝ) ^ n ≤ (k : ℝ) := by linarith
          have h₂₁ : Real.log ((2 : ℝ) ^ n) ≤ Real.log (k) := Real.log_le_log (by positivity) h₂₀
          linarith [h₁₄, h₁₃]
        refine' ⟨n, by linarith⟩
    rcases h₈ with ⟨N'', hN''⟩
    refine' ⟨N'', _⟩
    intro m hm
    have h₉ : m + 1 ≥ N'' := by linarith
    have h₁₀ : (2 : ℕ) ^ N'' ≤ (2 : ℕ) ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) h₉
    have h₁₁ : ( (2 : ℕ) ^ N'' : ℝ) ≤ ( (2 : ℕ) ^ (m + 1) : ℝ) := by exact_mod_cast h₁₀
    have h₁₂ : (2 : ℝ) ^ N'' ≤ (2 : ℝ) ^ (m + 1) := by simpa [pow_succ] using h₁₁
    have h₁₄ : (2 : ℝ) ^ (m + 1) ≥ (k : ℝ) := by
      linarith
    exact h₁₄
  rcases h₇ with ⟨N', hN'⟩
  use max N (N' + 2)
  intro m hm
  have h₉ : m ≥ N := by exact le_trans (le_max_left N (N' + 2)) hm
  have h₁₀ : m + 2 ≥ N := by linarith
  have h₁₁ : m ≥ N' := by linarith [le_max_right N (N' + 2)]
  have h₁₂ : (2 : ℝ) ^ (m + 1) ≥ (k : ℝ) := hN' m h₁₁
  have h₁₃ : (2 : ℝ) ^ (m + 1) > B := by linarith [hk]
  have h₁₄ : Real.log (a (m + 2) : ℝ) > (3 * R / 8) * (2 : ℝ) ^ (m + 2) := h₅ (m + 2) h₁₀
  have h₁₅ : ∑ i ∈ Finset.range (m + 1), Real.log (a i : ℝ) < C' + (5 * R / 8) * (2 : ℝ) ^ (m + 1) :=
    round1_h_sum_upper_bound a R N h₄ m h₉
  have h₁₆ : (0 : ℝ) < (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) := by
    exact Finset.prod_pos (fun i _hi => by exact_mod_cast (h_pos i))
  have h₁₇ : (0 : ℝ) < (a (m + 2) : ℝ) := by exact_mod_cast (h_pos (m + 2))
  have h₁₉ : (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) ≠ 0 := h₁₆.ne'
  have h₂₀ : Real.log ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) =
      Real.log (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) - Real.log (a (m + 2) : ℝ) := by
    rw [Real.log_div h₁₉ (by positivity)]
  have h₂₁ : Real.log (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) = ∑ i ∈ Finset.range (m + 1), Real.log (a i : ℝ) :=
    round1_lemma1_sum_log a h_pos m
  have h₂₂ : Real.log ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) =
      (∑ i ∈ Finset.range (m + 1), Real.log (a i : ℝ)) - Real.log (a (m + 2) : ℝ) := by
    rw [h₂₀, h₂₁]
  have h₂₃ : (∑ i ∈ Finset.range (m + 1), Real.log (a i : ℝ)) - Real.log (a (m + 2) : ℝ) < C' - (R / 8) * (2 : ℝ) ^ (m + 1) := by
    calc
      (∑ i ∈ Finset.range (m + 1), Real.log (a i : ℝ)) - Real.log (a (m + 2) : ℝ)
        < (C' + (5 * R / 8) * (2 : ℝ) ^ (m + 1)) - Real.log (a (m + 2) : ℝ) := by gcongr
      _ < (C' + (5 * R / 8) * (2 : ℝ) ^ (m + 1)) - ((3 * R / 8) * (2 : ℝ) ^ (m + 2)) := by gcongr
      _ = C' - (R / 8) * (2 : ℝ) ^ (m + 1) := by ring
  have h₂₄ : Real.log ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) < C' - (R / 8) * (2 : ℝ) ^ (m + 1) := by
    rw [h₂₂] ; exact h₂₃
  have h₂₅ : C' - (R / 8) * (2 : ℝ) ^ (m + 1) < Real.log ε := by
    have h₂₆ : (R / 8 : ℝ) > 0 := by positivity
    have h₂₇ : (R / 8) * (2 : ℝ) ^ (m + 1) > (R / 8) * B := by gcongr
    have h₂₈ : (R / 8) * B = C' - Real.log ε := by
      rw [hB] ; field_simp [h₂₆.ne'] ; ring
    rw [h₂₈] at h₂₇
    linarith
  have h₂₉ : Real.log ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) < Real.log ε := by
    linarith [h₂₄, h₂₅]
  have h₃₀ : 0 < (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ) := by
    apply div_pos
    · exact Finset.prod_pos (fun i _hi => by exact_mod_cast (h_pos i))
    · exact_mod_cast (h_pos (m + 2))
  have h₃₁ : |((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ))| =
      ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) := by
    rw [abs_of_pos h₃₀]
  rw [h₃₁]
  have h₃₂ : ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) < ε := by
    have h₃₃ : Real.log ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) < Real.log ε := h₂₉
    have h₃₄ : 0 < ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) := h₃₀
    have h₃₅ : 0 < ε := h₂
    exact (Real.log_lt_log_iff h₃₄ h₃₅).mp h₃₃
  exact h₃₂

theorem round1_key_lemma (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (R : ℝ)
  (hR_pos : R > 0)
  (h_log_a_n_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (a n : ℝ) / (2 : ℝ) ^ n) - R / 2| < ε):
  ∀ (ε : ℝ), ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ((a n : ℝ) / (a (n + 2) : ℝ)) < ε := by
  set x : ℕ → ℝ := fun n ↦ Real.log (a n : ℝ) / (2 : ℝ) ^ n
  have h1 : Filter.Tendsto x Filter.atTop (nhds (R / 2)) := by
    simpa [Metric.tendsto_atTop] using h_log_a_n_converges
  have h2₁ : Filter.Tendsto (fun k : ℕ ↦ k + 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_add_atTop_nat 2
  have h2 : Filter.Tendsto (fun n : ℕ ↦ x (n + 2)) Filter.atTop (nhds (R / 2)) :=
    Filter.Tendsto.comp h1 h2₁
  have h3₁ : Filter.Tendsto (fun n : ℕ ↦ x n) Filter.atTop (nhds (R / 2)) := h1
  have h3₂ : Filter.Tendsto (fun n : ℕ ↦ 4 * x (n + 2)) Filter.atTop (nhds (4 * (R / 2))) :=
    Filter.Tendsto.const_mul 4 h2
  have h3₃ : (4 * (R / 2) : ℝ) = 2 * R := by ring
  rw [h3₃] at h3₂
  have h3₄ : Filter.Tendsto (fun n : ℕ ↦ x n - 4 * x (n + 2)) Filter.atTop
      (nhds (R / 2 - (2 * R))) := Filter.Tendsto.sub h3₁ h3₂
  have h3₅ : (R / 2 - (2 * R) : ℝ) = -3 * R / 2 := by ring
  rw [h3₅] at h3₄
  set c : ℕ → ℝ := fun n ↦ x n - 4 * x (n + 2)
  have h4 : Filter.Tendsto c Filter.atTop (nhds (-3 * R / 2)) := h3₄
  have hε_pos : (3 * R / 4 : ℝ) > 0 := by positivity
  have h5 : ∃ N : ℕ, ∀ n ≥ N, |c n - (-3 * R / 2)| < (3 * R / 4 : ℝ) := by
    exact Metric.tendsto_atTop.mp h4 ((3 * R / 4 : ℝ)) hε_pos
  rcases h5 with ⟨N, hN⟩
  have h6 : ∀ n ≥ N, c n < -3 * R / 4 := by
    intro n hn
    have h7 : |c n - (-3 * R / 2)| < (3 * R / 4 : ℝ) := hN n hn
    have h8 : c n - (-3 * R / 2) < (3 * R / 4 : ℝ) := by
      linarith [abs_lt.mp h7]
    linarith
  set y : ℕ → ℝ := fun n ↦ Real.log (a n : ℝ) - Real.log (a (n + 2) : ℝ)
  have h7 : ∀ n : ℕ, y n = (2 : ℝ) ^ n * c n := by
    intro n
    have h9 : x n = Real.log (a n : ℝ) / (2 : ℝ) ^ n := by simp [x]
    have h10 : x (n + 2) = Real.log (a (n + 2) : ℝ) / (2 : ℝ) ^ (n + 2) := by simp [x]
    have h12 : (2 : ℝ) ^ n * c n
      = (2 : ℝ) ^ n * (x n - 4 * x (n + 2)) := by rfl
    rw [h12]
    have h13 : (2 : ℝ) ^ n * (x n - 4 * x (n + 2))
      = (2 : ℝ) ^ n * (x n) - 4 * ((2 : ℝ) ^ n * (x (n + 2))) := by ring
    rw [h13]
    have h14 : (2 : ℝ) ^ n * (x n) = Real.log (a n : ℝ) := by
      rw [h9]
      field_simp [show (2 : ℝ) ^ n ≠ 0 by positivity]
    have h15 : 4 * ((2 : ℝ) ^ n * (x (n + 2))) = Real.log (a (n + 2) : ℝ) := by
      rw [h10]
      have h16 : (2 : ℝ) ^ (n + 2) = 4 * (2 : ℝ) ^ n := by ring
      field_simp [h16, show (2 : ℝ) ^ n ≠ 0 by positivity] ; ring
    rw [h14, h15]
  have h8 : ∀ n ≥ N, y n < (2 : ℝ) ^ n * (-3 * R / 4) := by
    intro n hn
    have h9 : c n < -3 * R / 4 := h6 n hn
    have h10 : y n = (2 : ℝ) ^ n * c n := h7 n
    rw [h10]
    have h11 : (2 : ℝ) ^ n > 0 := by positivity
    nlinarith
  have h9 : Filter.Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n * (-3 * R / 4)) Filter.atTop Filter.atBot :=
    round1_h9 R hR_pos
  have h11 : ∀ (b : ℝ), ∃ (N₁ : ℕ), ∀ (n : ℕ), n ≥ N₁ → y n ≤ b := by
    intro b
    have h12 : ∀ᶠ (n : ℕ) in Filter.atTop, (2 : ℝ) ^ n * (-3 * R / 4) ≤ b :=
      h9.eventually_le_atBot b
    have h13 : ∃ (N₂ : ℕ), ∀ (n : ℕ), n ≥ N₂ → (2 : ℝ) ^ n * (-3 * R / 4) ≤ b := by
      simpa [Filter.eventually_atTop] using h12
    rcases h13 with ⟨N₂, hN₂⟩
    use max N N₂
    intro n hn
    have h14 : n ≥ N := by exact le_trans (le_max_left N N₂) hn
    have h15 : n ≥ N₂ := by exact le_trans (le_max_right N N₂) hn
    have h16 : y n ≤ (2 : ℝ) ^ n * (-3 * R / 4) := by
      have h17 : y n < (2 : ℝ) ^ n * (-3 * R / 4) := h8 n h14
      linarith
    have h18 : (2 : ℝ) ^ n * (-3 * R / 4) ≤ b := hN₂ n h15
    linarith
  have h10 : Filter.Tendsto y Filter.atTop Filter.atBot := by
    simpa [Filter.tendsto_atBot] using h11
  have h12 : Filter.Tendsto (fun n : ℕ ↦ Real.log ((a n : ℝ) / (a (n + 2) : ℝ))) Filter.atTop Filter.atBot := by
    have h13 : ∀ n : ℕ, Real.log ((a n : ℝ) / (a (n + 2) : ℝ)) = y n := by
      intro n
      have h14 : (a n : ℝ) > 0 := by exact_mod_cast (h_pos n)
      have h15 : (a (n + 2) : ℝ) > 0 := by exact_mod_cast (h_pos (n + 2))
      have h16 : Real.log ((a n : ℝ) / (a (n + 2) : ℝ)) = Real.log (a n : ℝ) - Real.log (a (n + 2) : ℝ) := by
        rw [Real.log_div (by positivity) (by positivity)]
      rw [h16]
    simpa [h13] using h10
  intro ε hε
  have h13 : ∃ N' : ℕ, ∀ n ≥ N', Real.log ((a n : ℝ) / (a (n + 2) : ℝ)) ≤ Real.log ε - 1 := by
    have h14 : Filter.Tendsto (fun n : ℕ ↦ Real.log ((a n : ℝ) / (a (n + 2) : ℝ))) Filter.atTop Filter.atBot := h12
    have h15 : ∀ (b : ℝ), ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → Real.log ((a n : ℝ) / (a (n + 2) : ℝ)) ≤ b := by
      simpa [Filter.tendsto_atBot] using h14
    exact h15 (Real.log ε - 1)
  rcases h13 with ⟨N', hN'⟩
  refine' ⟨N', _⟩
  intro n hn
  have h15 : Real.log ((a n : ℝ) / (a (n + 2) : ℝ)) ≤ Real.log ε - 1 := hN' n hn
  have h16 : (a n : ℝ) / (a (n + 2) : ℝ) > 0 := by
    have h17 : (a n : ℝ) > 0 := by exact_mod_cast (h_pos n)
    have h18 : (a (n + 2) : ℝ) > 0 := by exact_mod_cast (h_pos (n + 2))
    positivity
  have h19 : Real.log ((a n : ℝ) / (a (n + 2) : ℝ)) < Real.log ε := by linarith
  have h20 : (a n : ℝ) / (a (n + 2) : ℝ) < ε := by
    have h22 : Real.log ((a n : ℝ) / (a (n + 2) : ℝ)) < Real.log ε := h19
    have h23 : (a n : ℝ) / (a (n + 2) : ℝ) < ε := by
      exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp h22
    exact h23
  exact h20

theorem round1_sum_representation (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (P : ℕ)
  (Q : ℕ)
  (hQ_pos : Q > 0)
  (hP_pos : P > 0)
  (h_sum_eq : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ))
  (x : ℕ → ℝ)
  (hx_def : ∀ m : ℕ, x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))))):
  ∀ m : ℕ,
    let T := fun (k : ℕ) (m : ℕ) => (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + k) : ℝ) * (a (m + k + 1) : ℝ))
    x m = (∑' k : ℕ, T (k + 1) m) := by
  intro m
  dsimp only
  let f : ℕ → ℝ := fun n => 1 / ((a n : ℝ) * (a (n + 1) : ℝ))
  let C : ℝ := ∏ i ∈ Finset.range (m + 2), (a i : ℝ)
  have h_main1 : x m = C * ((∑' n, f n) - (∑ n ∈ Finset.range (m + 1), f n)) := by
    have h₁ := hx_def m
    simpa [f, C] using h₁
  have h₂ := round1_h_main_826e a h_pos P Q hQ_pos hP_pos h_sum_eq m
  have h₃ : (∑' n, f n) = (∑' n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
    congr
  have h₄ : (∑ n ∈ Finset.range (m + 1), f n) = (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
    congr
  have h₅ : (∑' k : ℕ, f (k + (m + 1))) = (∑' k : ℕ, (1 / ((a ((m + 1) + k) : ℝ) * (a (((m + 1) + k) + 1) : ℝ)))) := by
    apply tsum_congr
    intro k
    have h₅₁ : (k + (m + 1)) = (m + 1) + k := by omega
    rw [h₅₁]
  have h_main2' : (∑' n, f n) - (∑ n ∈ Finset.range (m + 1), f n) = ∑' k : ℕ, f (k + (m + 1)) := by
    rw [h₃, h₄]
    have h₆ : (∑' n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (∑' k : ℕ, (1 / ((a ((m + 1) + k) : ℝ) * (a (((m + 1) + k) + 1) : ℝ)))) := h₂
    rw [h₆]
    exact h₅.symm
  have h_main3 : x m = C * (∑' k : ℕ, f (k + (m + 1))) := by
    rw [h_main1, h_main2']
  have h_main4 : C * (∑' k : ℕ, f (k + (m + 1))) = ∑' k : ℕ, (C * f (k + (m + 1))) := by
    rw [tsum_mul_left]
  have h_main5 : ∀ (k : ℕ), C * f (k + (m + 1)) = ((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + (k + 1)) : ℝ) * (a (m + (k + 1) + 1) : ℝ))) := by
    intro k
    have h₃ : (k + (m + 1)) = (m + 1) + k := by omega
    have h₄ : C = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) := by rfl
    rw [h₄]
    rw [h₃]
    simp [f] ; field_simp ; ring_nf
  have h_main6 : ∑' k : ℕ, (C * f (k + (m + 1))) = ∑' k : ℕ, ((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + (k + 1)) : ℝ) * (a (m + (k + 1) + 1) : ℝ))) := by
    apply tsum_congr
    intro k
    exact h_main5 k
  have h_final : x m = ∑' k : ℕ, ((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + (k + 1)) : ℝ) * (a (m + (k + 1) + 1) : ℝ))) := by
    rw [h_main3, h_main4, h_main6]
  have h_goal : ∑' k : ℕ, ((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + (k + 1)) : ℝ) * (a (m + (k + 1) + 1) : ℝ))) = ∑' k : ℕ, ( (fun (k : ℕ) (m : ℕ) => (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + k) : ℝ) * (a (m + k + 1) : ℝ))) (k + 1) m ) := by
    apply tsum_congr
    intro k
    simp
  rw [h_goal] at h_final
  exact h_final

theorem round1_sum_pos (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (h_mono : StrictMono a):
  (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) > 0 := by
  have h_summable : Summable (fun n : ℕ ↦ 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) :=
    round1_h_summable_fbf3 a h_mono h_pos
  let f : ℕ → ℝ := fun n ↦ 1 / ((a n : ℝ) * (a (n + 1) : ℝ))
  have h_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    have h_pos1 : 0 < (a n : ℝ) := by exact_mod_cast (h_pos n)
    have h_pos2 : 0 < (a (n + 1) : ℝ) := by exact_mod_cast (h_pos (n + 1))
    positivity
  have h_pos0 : 0 < f 0 := by
    simp only [f]
    have h1 : 0 < (a 0 : ℝ) := by exact_mod_cast (h_pos 0)
    have h2 : 0 < (a 1 : ℝ) := by exact_mod_cast (h_pos 1)
    positivity
  have h_main : (∑' n : ℕ, f n) ≥ f 0 := by
    have h₁ : (∑ x ∈ ({0} : Finset ℕ), f x) = f 0 := by simp
    have h₂ : (∑ x ∈ ({0} : Finset ℕ), f x) ≤ ∑' n : ℕ, f n :=
      Summable.sum_le_tsum ({0} : Finset ℕ) (fun i _ ↦ h_nonneg i) h_summable
    linarith [h₁, h₂]
  have h_final : (∑' n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) > 0 := by
    simpa [f] using lt_of_lt_of_le h_pos0 h_main
  exact h_final

theorem round1_exists_x_and_lower_bound (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n)
  (P : ℕ)
  (Q : ℕ)
  (hQ_pos : Q > 0)
  (h_sum_eq : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ)):
  ∃ (x : ℕ → ℝ),
    (∀ m : ℕ, x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))))) ∧
    (∀ m : ℕ, x m ≥ 1 / (Q : ℝ)) := by
  have h1 : ∀ (m : ℕ), ∃ (K : ℤ), (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (K : ℝ) := by
    exact round1_h1 a h_pos
  have h3 : ∀ (m : ℕ), (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) > 0 := by
    exact round1_h3 a h_mono h_pos
  set x : ℕ → ℝ := fun m => (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) with hx_def
  have h21 : ∀ m : ℕ, x m ≥ 1 / (Q : ℝ) := by
    intro m
    rcases h1 m with ⟨K, hK⟩
    set D_m_nat : ℕ := (∏ i ∈ Finset.range (m + 2), a i) with hD_m_nat_def
    set I : ℤ := (D_m_nat : ℤ) * (P : ℤ) - K * (Q : ℤ) with hI_def
    have hI_eq : (I : ℝ) = ((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (P : ℝ)) - (K : ℝ) * (Q : ℝ) := by
      simp [hI_def, hD_m_nat_def]
    have h_x_eq : x m = ((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (P : ℝ)) / (Q : ℝ) - (K : ℝ) := by
      have h4 : x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) := by
        rw [hx_def]
      rw [h4]
      have h5 : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ) := h_sum_eq
      rw [h5]
      have h7 : (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (((P : ℝ) / (Q : ℝ)) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ)))) = ((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (P : ℝ)) / (Q : ℝ) - (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
        field_simp
        ring_nf
      rw [h7]
      have h8 : (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (K : ℝ) := by
        linarith
      rw [h8]
    have h_x_eq_I_div_Q : x m = (I : ℝ) / (Q : ℝ) := by
      have h9 : x m = ((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (P : ℝ)) / (Q : ℝ) - (K : ℝ) := h_x_eq
      have h10 : (I : ℝ) = ((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * (P : ℝ)) - (K : ℝ) * (Q : ℝ) := hI_eq
      have h11 : (Q : ℝ) > 0 := by exact_mod_cast hQ_pos
      rw [h9, h10]
      field_simp [h11]
      ring_nf
    have h_x_pos : x m > 0 := h3 m
    have hI_real_pos : (I : ℝ) > 0 := by
      have h14 : (Q : ℝ) > 0 := by exact_mod_cast hQ_pos
      have h16 : (I : ℝ) > 0 := by
        by_contra h16'
        have h17 : (I : ℝ) ≤ 0 := by linarith
        have h18 : (I : ℝ) / (Q : ℝ) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg h17
          linarith
        linarith [h_x_eq_I_div_Q, h_x_pos]
      linarith
    have hI_pos : I > 0 := by exact_mod_cast hI_real_pos
    have hI_ge_1 : I ≥ 1 := by
      omega
    have hI_real_ge_1 : (I : ℝ) ≥ 1 := by exact_mod_cast hI_ge_1
    have h12 : (I : ℝ) / (Q : ℝ) ≥ 1 / (Q : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    linarith [h_x_eq_I_div_Q, h12]
  refine' ⟨x, _ , _⟩
  · intro m
    rw [hx_def]
  · intro m
    exact h21 m

theorem round1_exists_K_recurrence (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n)
  (P Q : ℕ)
  (hQ_pos : Q > 0)
  (hP_pos : P > 0)
  (h_sum_eq : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ))
  (x : ℕ → ℝ)
  (hx_def : ∀ m : ℕ, x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))))):
  ∃ (K : ℝ), K > 0 ∧ ∀ n : ℕ, n ≥ 3 → (a n : ℝ) ≤ K * (∏ i ∈ Finset.range n, (a i : ℝ)) := by
  have h1 : ∀ m : ℕ, x m ≥ 1 / (Q : ℝ) := by
    exact round1_h1_251e a h_pos P Q hQ_pos hP_pos h_sum_eq x hx_def
  have h3 : ∀ m : ℕ, m ≥ 1 → x m = (a (m + 1) : ℝ) * x (m - 1) - (∏ i ∈ Finset.range m, (a i : ℝ)) := by
    exact round1_h3_8ee9 a h_pos x hx_def
  have h2 : ∀ m : ℕ, x m ≤ (∏ i ∈ Finset.range (m + 1), (a i : ℝ)) := by
    exact round1_h2_8af1 a h_mono h_pos P Q hQ_pos hP_pos h_sum_eq x hx_def
  use 2 * (Q : ℝ)
  constructor
  ·
    have hQ_pos1 : (Q : ℝ) > 0 := by exact_mod_cast hQ_pos
    linarith
  ·
    intro n hn
    have h4 : n ≥ 1 := by linarith
    have h5 : n - 1 ≥ 1 := by omega
    have h6 : x (n - 1) = (a n : ℝ) * x (n - 2) - (∏ i ∈ Finset.range (n - 1), (a i : ℝ)) := by
      have h61 := h3 (n - 1) (by bound)
      have h62 : (n - 1) + 1 = n := by field_simp
      simpa [h62] using h61
    have h61 : (a n : ℝ) * x (n - 2) = x (n - 1) + (∏ i ∈ Finset.range (n - 1), (a i : ℝ)) := by linarith
    have h71 : x (n - 1) ≤ (∏ i ∈ Finset.range n, (a i : ℝ)) := by
      have h7 : x (n - 1) ≤ (∏ i ∈ Finset.range ((n - 1) + 1), (a i : ℝ)) := h2 (n - 1)
      have h72 : (n - 1) + 1 = n := by field_simp
      rw [h72] at h7
      exact h7
    have h8 : x (n - 2) ≥ 1 / (Q : ℝ) := h1 (n - 2)
    have h9 : x (n - 2) > 0 := by
      have : (Q : ℝ) > 0 := by exact_mod_cast hQ_pos
      have h91 : (1 : ℝ) / (Q : ℝ) > 0 := by positivity
      linarith
    have h10 : (a n : ℝ) * x (n - 2) ≤ (∏ i ∈ Finset.range n, (a i : ℝ)) + (∏ i ∈ Finset.range (n - 1), (a i : ℝ)) := by linarith
    have h11 : (a n : ℝ) ≤ (Q : ℝ) * ((∏ i ∈ Finset.range n, (a i : ℝ)) + (∏ i ∈ Finset.range (n - 1), (a i : ℝ))) := by
      have hQ_pos1 : (Q : ℝ) > 0 := by exact_mod_cast hQ_pos
      have h81 : x (n - 2) ≥ 1 / (Q : ℝ) := h8
      have h101 : (a n : ℝ) * x (n - 2) ≤ (∏ i ∈ Finset.range n, (a i : ℝ)) + (∏ i ∈ Finset.range (n - 1), (a i : ℝ)) := h10
      have h102 : (Q : ℝ) * x (n - 2) ≥ 1 := by
        have h95 : (Q : ℝ) * x (n - 2) ≥ (Q : ℝ) * (1 / (Q : ℝ)) := by gcongr
        have h96 : (Q : ℝ) * (1 / (Q : ℝ)) = 1 := by
          field_simp
        linarith
      nlinarith [h101, h102, mul_nonneg (show 0 ≤ (Q : ℝ) by linarith) (show 0 ≤ (∏ i ∈ Finset.range n, (a i : ℝ)) + (∏ i ∈ Finset.range (n - 1), (a i : ℝ)) by
        have h103 : (∏ i ∈ Finset.range n, (a i : ℝ)) ≥ 0 := by
          apply Finset.prod_nonneg
          intro i _hi
          exact_mod_cast (le_of_lt (h_pos i))
        have h104 : (∏ i ∈ Finset.range (n - 1), (a i : ℝ)) ≥ 0 := by
          apply Finset.prod_nonneg
          intro i _hi
          exact_mod_cast (le_of_lt (h_pos i))
        linarith)]
    have h123 : (∏ i ∈ Finset.range n, (a i : ℝ)) + (∏ i ∈ Finset.range (n - 1), (a i : ℝ)) ≤ 2 * (∏ i ∈ Finset.range n, (a i : ℝ)) := by
      have h121 : (∏ i ∈ Finset.range n, (a i : ℝ)) = (∏ i ∈ Finset.range (n - 1), (a i : ℝ)) * (a (n - 1) : ℝ) := by
        cases n with
        | zero =>
          exfalso
          linarith
        | succ n1 =>
          cases n1 with
          | zero =>
            exfalso
            bound
          | succ n2 =>
            simp [Finset.prod_range_succ, mul_comm]
      have h122 : (a (n - 1) : ℝ) ≥ 1 := by
        have h1221 : a (n - 1) ≥ 1 := by
          have h1222 : 0 < a (n - 1) := h_pos (n - 1)
          bound
        exact_mod_cast h1221
      have h124 : (∏ i ∈ Finset.range (n - 1), (a i : ℝ)) > 0 := by
        apply Finset.prod_pos
        intro i _hi
        exact_mod_cast (h_pos i)
      nlinarith
    have h12 : (Q : ℝ) * ((∏ i ∈ Finset.range n, (a i : ℝ)) + (∏ i ∈ Finset.range (n - 1), (a i : ℝ))) ≤ 2 * (Q : ℝ) * (∏ i ∈ Finset.range n, (a i : ℝ)) := by
      have : (Q : ℝ) > 0 := by exact_mod_cast hQ_pos
      nlinarith [h123]
    have h13 : (a n : ℝ) ≤ 2 * (Q : ℝ) * (∏ i ∈ Finset.range n, (a i : ℝ)) := by
      linarith
    simpa [mul_assoc] using h13

theorem analysis_lemma (L : ℕ → ℝ)
  (h1 : ∃ N₀ : ℕ, ∃ C : ℝ, ∀ n : ℕ, n ≥ N₀ → L (n + 1) ≤ 2 * L n + C)
  (h2 : ∃ M : ℝ, ∀ n : ℕ, L n ≥ M):
  ∃ (R : ℝ), ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(L n / (2 : ℝ) ^ n) - R| < ε := by
  rcases h1 with ⟨N₀, C, h11⟩
  rcases h2 with ⟨M, h21⟩
  have h_x_bounded_below : ∃ B1 : ℝ, ∀ n : ℕ, B1 ≤ (L n / (2 : ℝ) ^ n) := by
    by_cases hM1 : M ≥ 0
    ·
      use 0
      intro n
      have h111 : L n ≥ M := h21 n
      have h113 : (2 : ℝ) ^ n > 0 := by positivity
      apply _root_.div_nonneg
      · linarith
      · linarith
    ·
      have hM2 : M < 0 := by linarith
      use M
      intro n
      have h13 : (2 : ℝ) ^ n ≥ 1 := by
        have h131 : (2 : ℝ) ^ n ≥ (2 : ℝ) ^ 0 := by
          apply pow_le_pow_right₀
          · norm_num
          · bound
        norm_num at h131 ⊢
        linarith
      have h14 : L n ≥ M := h21 n
      have h141 : (L n) / ((2 : ℝ) ^ n) ≥ M / ((2 : ℝ) ^ n) := by
        apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
        nlinarith
      have h142 : M / ((2 : ℝ) ^ n) ≥ M := by
        have h1421 : (2 : ℝ) ^ n ≥ 1 := h13
        have h : M / ((2 : ℝ) ^ n) - M ≥ 0 := by
          have h1424 : M / ((2 : ℝ) ^ n) - M = M * (1 / ((2 : ℝ) ^ n) - 1) := by
            field_simp
            ring_nf
          rw [h1424]
          have h1425 : 1 / ((2 : ℝ) ^ n) - 1 ≤ 0 := by
            have h1427 : 1 / ((2 : ℝ) ^ n) ≤ 1 := by
              apply (div_le_iff₀ (by positivity)).mpr
              nlinarith
            linarith
          nlinarith
        linarith
      linarith
  have h_S_bounded_above : ∃ B2 : ℝ, ∀ n : ℕ, (C * (1 - (1 / 2 : ℝ) ^ n)) ≤ B2 := by
    by_cases hC1 : C ≥ 0
    ·
      use C
      intro n
      have h1 : (1 : ℝ) - (1 / 2 : ℝ) ^ n ≤ 1 := by
        have h11 : (1 / 2 : ℝ) ^ n ≥ 0 := by positivity
        linarith
      nlinarith
    ·
      use 0
      intro n
      have h2 : (1 : ℝ) - (1 / 2 : ℝ) ^ n ≥ 0 := by
        have h21 : (1 / 2 : ℝ) ^ n ≤ 1 := by
          have h : (1 / 2 : ℝ) ^ n ≤ (1 : ℝ) ^ n := by
            apply pow_le_pow_left₀
            all_goals linarith
          have h213 : (1 : ℝ) ^ n = 1 := by simp
          linarith
        linarith
      nlinarith
  rcases h_x_bounded_below with ⟨B1, hB1⟩
  rcases h_S_bounded_above with ⟨B2, hB2⟩
  have h_y_bounded_below : ∃ B3 : ℝ, ∀ n : ℕ, B3 ≤ (L n / (2 : ℝ) ^ n) - (C * (1 - (1 / 2 : ℝ) ^ n)) := by
    refine' ⟨B1 - B2, _⟩
    intro n
    have h161 : B1 ≤ (L n / (2 : ℝ) ^ n) := hB1 n
    have h162 : (C * (1 - (1 / 2 : ℝ) ^ n)) ≤ B2 := hB2 n
    linarith
  have h_y_non_increasing : ∃ N₀' : ℕ, ∀ n : ℕ, n ≥ N₀' → ((L (n + 1) / (2 : ℝ) ^ (n + 1)) - (C * (1 - (1 / 2 : ℝ) ^ (n + 1)))) ≤ ((L n / (2 : ℝ) ^ n) - (C * (1 - (1 / 2 : ℝ) ^ n))) := by
    refine' ⟨N₀, _⟩
    intro n hn
    have h111 : L (n + 1) ≤ 2 * L n + C := h11 n hn
    have h_ineq1 : L (n + 1) / ((2 : ℝ) ^ (n + 1)) ≤ (L n / (2 : ℝ) ^ n) + C / ((2 : ℝ) ^ (n + 1)) := by
      have h_pos1 : (2 : ℝ) ^ (n + 1) > 0 := by positivity
      have h113 : L (n + 1) / ((2 : ℝ) ^ (n + 1)) ≤ (2 * L n + C) / ((2 : ℝ) ^ (n + 1)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith
      have h114 : (2 * L n + C) / ((2 : ℝ) ^ (n + 1)) = (L n / (2 : ℝ) ^ n) + C / ((2 : ℝ) ^ (n + 1)) := by
        field_simp [pow_succ]
        ring_nf
      linarith
    have h_eq2 : C * (1 - (1 / 2 : ℝ) ^ (n + 1)) = C * (1 - (1 / 2 : ℝ) ^ n) + C / ((2 : ℝ) ^ (n + 1)) := by
      field_simp [pow_succ]
      ring_nf
    linarith [h_ineq1, h_eq2]
  rcases h_y_non_increasing with ⟨N₀', h_y_non_increasing⟩
  have h_y_converges : ∃ R' : ℝ, ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |((L n / (2 : ℝ) ^ n) - (C * (1 - (1 / 2 : ℝ) ^ n))) - R'| < ε := by
    apply round1_lemma1 (fun n => (L n / (2 : ℝ) ^ n) - (C * (1 - (1 / 2 : ℝ) ^ n)))
    · refine' ⟨N₀', _⟩
      intro n hn
      simpa [sub_le_iff_le_add] using h_y_non_increasing n hn
    · rcases h_y_bounded_below with ⟨B3, hB3⟩
      refine' ⟨B3, _⟩
      intro n
      simpa using hB3 n
  rcases h_y_converges with ⟨R', hR'⟩
  have h_S_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(C * (1 - (1 / 2 : ℝ) ^ n)) - C| < ε := by
    exact round1_lemma2 C
  have h_x_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(L n / (2 : ℝ) ^ n) - (R' + C)| < ε := by
    have h := round1_lemma3 (fun n => (L n / (2 : ℝ) ^ n) - (C * (1 - (1 / 2 : ℝ) ^ n))) (fun n => (C * (1 - (1 / 2 : ℝ) ^ n))) R' C hR' h_S_converges
    intro ε hε
    rcases h ε hε with ⟨N, hN⟩
    refine' ⟨N, _⟩
    intro n hn
    have h50 := hN n hn
    have h51 : (( (L n / (2 : ℝ) ^ n) - (C * (1 - (1 / 2 : ℝ) ^ n))) + (C * (1 - (1 / 2 : ℝ) ^ n))) = (L n / (2 : ℝ) ^ n) := by
      ring_nf
    have h52 : |(( (L n / (2 : ℝ) ^ n) - (C * (1 - (1 / 2 : ℝ) ^ n))) + (C * (1 - (1 / 2 : ℝ) ^ n))) - (R' + C)| < ε := by simpa using h50
    have h53 : |(L n / (2 : ℝ) ^ n) - (R' + C)| < ε := by
      rw [h51] at h52
      exact h52
    exact h53
  exact ⟨R' + C, h_x_converges⟩

theorem round1_R_is_positive_79ab (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (R : ℝ)
  (h_R_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) / (2 : ℝ) ^ n) - R| < ε)
  (h_liminf : 1 < Filter.atTop.liminf (fun n ↦ (a n : ℝ) ^ ((1 : ℝ) / 2 ^ n))):
  R > 0 := by
  rcases round1_lemma1_9f53 a h_pos h_liminf with ⟨c, hc_pos, N, h_ineq1⟩
  exact round1_lemma3_9883 a h_pos c hc_pos (fun δ hδ1 _ ↦ round1_lemma2_b154 a h_pos c N h_ineq1 δ hδ1) R h_R_converges

theorem round1_lemma2_b9b4 (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n)
  (R : ℝ)
  (hR_pos : R > 0)
  (h_log_a_n_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (a n : ℝ) / (2 : ℝ) ^ n) - R / 2| < ε):
  ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, m ≥ N → |((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + 2) : ℝ) * (a (m + 3) : ℝ)))| < ε := by
  have h1 : ∀ m : ℕ, ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) > 0 := by
    exact round1_h1_d500 a h_pos
  have h2 : ∀ m : ℕ, 0 < (a (m + 1) : ℝ) / (a (m + 3) : ℝ) ∧ (a (m + 1) : ℝ) / (a (m + 3) : ℝ) < 1 := by
    exact round1_h2_8d71 a h_mono h_pos
  intro ε hε
  have h10 : ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, m ≥ N → |((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ))| < ε := by
    exact round1_lemma1_d8f2 a h_pos R hR_pos h_log_a_n_converges
  rcases h10 ε hε with ⟨N, hN⟩
  refine' ⟨N, _⟩
  intro m hm
  have h3 : ((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + 2) : ℝ) * (a (m + 3) : ℝ))) =
    ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) * ((a (m + 1) : ℝ) / (a (m + 3) : ℝ)) := by
    exact round1_h3_491b a h_pos m
  have hU_pos : ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) > 0 := h1 m
  have hV1 : 0 < (a (m + 1) : ℝ) / (a (m + 3) : ℝ) := (h2 m).1
  have hV2 : (a (m + 1) : ℝ) / (a (m + 3) : ℝ) < 1 := (h2 m).2
  have h4 : |((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ))| < ε := hN m hm
  have h41 : ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) < ε := by
    have h411 : |((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ))| = ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) := by
      rw [abs_of_pos]
      linarith [hU_pos]
    linarith
  have h5 : ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) * ((a (m + 1) : ℝ) / (a (m + 3) : ℝ)) < ε := by
    nlinarith [hU_pos, hV1, hV2, h41]
  have h6 : ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) * ((a (m + 1) : ℝ) / (a (m + 3) : ℝ)) > 0 := by
    exact mul_pos hU_pos hV1
  have h7 : |((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) * ((a (m + 1) : ℝ) / (a (m + 3) : ℝ))| = ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) * ((a (m + 1) : ℝ) / (a (m + 3) : ℝ)) := by
    rw [abs_of_pos]
    linarith
  rw [h3]
  linarith

theorem round1_sum_decomposition (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (R : ℝ)
  (hR_pos : R > 0)
  (h_log_a_n_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (a n : ℝ) / (2 : ℝ) ^ n) - R / 2| < ε)
  (m : ℕ)
  (T : ℕ → ℕ → ℝ)
  (hT_def : ∀ k : ℕ, T k m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + k) : ℝ) * (a (m + k + 1) : ℝ)))
  (h_pos_T : ∀ k : ℕ, T k m > 0):
  (∑' k : ℕ, T (k + 1) m) = T 1 m + T 2 m + (∑' k : ℕ, T (k + 3) m) := by
  have h_identity : ∀ k : ℕ, T (k + 1) m = T k m * ((a (m + k) : ℝ) / (a (m + k + 2) : ℝ)) := by
    exact round1_lemma_T_identity a h_pos m T hT_def
  have h_T_has_ratio : ∃ K : ℕ, ∀ n : ℕ, n ≥ K → T (n + 1) m < (1 / 2) * T n m := by
    have h2 : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ((a n : ℝ) / (a (n + 2) : ℝ)) < 1 / 2 := by
      exact round1_key_lemma a h_pos R hR_pos h_log_a_n_converges (1 / 2) (by norm_num)
    rcases h2 with ⟨N, hN⟩
    refine' ⟨N, _⟩
    intro n hn
    have h3 : m + n ≥ N := by linarith
    have h4 : ((a (m + n) : ℝ) / (a (m + n + 2) : ℝ)) < 1 / 2 := by
      have h41 := hN (m + n) h3
      simpa [add_assoc] using h41
    have h5 : T (n + 1) m = T n m * ((a (m + n) : ℝ) / (a (m + n + 2) : ℝ)) := by
      have h51 := h_identity n
      simpa [add_assoc] using h51
    have h6 : T n m > 0 := h_pos_T n
    have h7 : T (n + 1) m < (1 / 2) * T n m := by
      rw [h5]
      nlinarith
    linarith
  have h_summable_T : Summable (fun k : ℕ => T k m) := by
    exact round1_lemma_summable_from_ratio (fun k : ℕ => T k m) (fun n => h_pos_T n) h_T_has_ratio
  have h_summable_T1 : Summable (fun (k : ℕ) => T (k + 1) m) := by
    exact round1_summable_shift (fun k : ℕ => T k m) h_summable_T
  have h_summable_T2 : Summable (fun (k : ℕ) => T (k + 2) m) := by
    exact round1_summable_shift (fun k : ℕ => T (k + 1) m) h_summable_T1
  have h_eq2 : (∑' k : ℕ, T (k + 1) m) = (T 1 m) + (∑' k : ℕ, T (k + 2) m) := by
    exact round1_lemma_tsum_relation (fun k : ℕ => T (k + 1) m) h_summable_T1
  have h_eq3 : (∑' k : ℕ, T (k + 2) m) = (T 2 m) + (∑' k : ℕ, T (k + 3) m) := by
    exact round1_lemma_tsum_relation (fun k : ℕ => T (k + 2) m) h_summable_T2
  linarith

theorem round1_not_rational_implies_irrational (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n)
  (h_not_rational : ¬ ∃ (P Q : ℕ), Q > 0 ∧ P > 0 ∧ (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ)):
  Irrational (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
  set S := (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) with hS_def
  have h_S_pos : S > 0 := by
    exact round1_sum_pos a h_pos h_mono
  have h1 : (∃ (q : ℚ), (q : ℝ) = S) → (∃ (P Q : ℕ), Q > 0 ∧ P > 0 ∧ S = (P : ℝ) / (Q : ℝ)) := by
    intro h
    exact round1_rational_implies_exists_P_Q S h_S_pos h
  have h2 : ¬ ∃ (q : ℚ), (q : ℝ) = S := by
    intro h21
    have h22 : ∃ (P Q : ℕ), Q > 0 ∧ P > 0 ∧ S = (P : ℝ) / (Q : ℝ) := h1 h21
    rcases h22 with ⟨P, Q, hQ_pos, hP_pos, h_eq⟩
    have h23 : ∃ (P Q : ℕ), Q > 0 ∧ P > 0 ∧ (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ) := ⟨P, Q, hQ_pos, hP_pos, by
      simpa [hS_def] using h_eq⟩
    tauto
  exact h2

theorem round1_exists_R_converges_4eef (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (K : ℝ)
  (hK_pos : K > 0)
  (h3_rec : ∀ n : ℕ, n ≥ 3 → (a n : ℝ) ≤ K * (∏ i ∈ Finset.range n, (a i : ℝ))):
  ∃ (R : ℝ), ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) / (2 : ℝ) ^ n) - R| < ε := by
  set L : ℕ → ℝ := fun n => Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) with hL_def
  have h_prod_ge_one : ∀ n : ℕ, (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) ≥ 1 := by
    exact round1_h_prod_ge_one a h_pos
  have h_L_ge_0 : ∀ n : ℕ, L n ≥ 0 := by
    exact round1_h_L_ge_0 a h_prod_ge_one
  have h_upper_bound : ∀ n : ℕ, n ≥ 2 → L (n + 1) ≤ 2 * L n + Real.log K := by
    intro n hn
    have h : Real.log (∏ i ∈ Finset.range (n + 2), (a i : ℝ)) ≤ 2 * Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) + Real.log K := by
      exact round1_h_upper_bound a h_pos K hK_pos h3_rec n hn
    simpa [hL_def] using h
  have h1 : ∃ N₀ : ℕ, ∃ C : ℝ, ∀ n : ℕ, n ≥ N₀ → L (n + 1) ≤ 2 * L n + C := by
    refine ⟨2, Real.log K, fun n hn => h_upper_bound n hn⟩
  have h2 : ∃ M : ℝ, ∀ n : ℕ, L n ≥ M := by
    refine ⟨0, fun n => h_L_ge_0 n⟩
  have h_final : ∃ (R : ℝ), ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(L n / (2 : ℝ) ^ n) - R| < ε := by
    exact analysis_lemma L h1 h2
  simpa [hL_def] using h_final

theorem round1_lemma3_6abf (a : ℕ → ℕ)
  (h_pos : ∀ n, 0 < a n)
  (P : ℕ)
  (Q : ℕ)
  (hQ_pos : Q > 0)
  (hP_pos : P > 0)
  (h_sum_eq : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ))
  (x : ℕ → ℝ)
  (hx_def : ∀ m : ℕ, x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ)))))
  (R : ℝ)
  (hR_pos : R > 0)
  (h_log_a_n_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (a n : ℝ) / (2 : ℝ) ^ n) - R / 2| < ε):
  ∃ N₀ : ℕ, ∀ m : ℕ, m ≥ N₀ → x m ≤ ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) + 2 * (((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + 2) : ℝ) * (a (m + 3) : ℝ)))) := by
  have h_key_lemma := round1_key_lemma a h_pos R hR_pos h_log_a_n_converges
  have h1 := round1_sum_representation a h_pos P Q hQ_pos hP_pos h_sum_eq x hx_def
  have h2 := round1_ratio_inequality a h_pos
  have h_N0_exists : ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 → ((a n : ℝ) / (a (n + 2) : ℝ)) < 1 / 2 := by
    have h5 := h_key_lemma (1 / 2 : ℝ) (by norm_num)
    tauto
  rcases h_N0_exists with ⟨N0, hN0⟩
  refine' ⟨N0, _⟩
  intro m hm
  set T := fun (k : ℕ) (m : ℕ) => (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + k) : ℝ) * (a (m + k + 1) : ℝ))
  have h_sum_repr : x m = (∑' k : ℕ, T (k + 1) m) := by
    exact h1 m
  have h_ratio_ineq : ∀ k : ℕ, k ≥ 1 → T (k + 1) m < (1 / 2) * (T k m) := by
    intro k hk
    exact h2 N0 hN0 m hm k hk
  have h_pos_T : ∀ k : ℕ, T k m > 0 := by
    intro k
    have h_pos1 : ∀ n : ℕ, (a n : ℝ) > 0 := fun n => by exact_mod_cast (h_pos n)
    apply _root_.div_pos
    · exact Finset.prod_pos (fun i _ => h_pos1 i)
    · have h11 : (a (m + k) : ℝ) > 0 := h_pos1 (m + k)
      have h12 : (a (m + k + 1) : ℝ) > 0 := h_pos1 (m + k + 1)
      positivity
  have h_tail_bound : (∑' k : ℕ, T (k + 3) m) ≤ T 2 m := by
    exact round1_tail_bound m T (fun k hk => h_ratio_ineq k hk) h_pos_T
  have h6 : (∑' k : ℕ, T (k + 1) m) = T 1 m + T 2 m + (∑' k : ℕ, T (k + 3) m) := by
    exact round1_sum_decomposition a h_pos R hR_pos h_log_a_n_converges m T (fun k => rfl) h_pos_T
  have h7 : (∑' k : ℕ, T (k + 1) m) ≤ T 1 m + 2 * (T 2 m) := by
    linarith [h_tail_bound, h6]
  have h8 : x m ≤ T 1 m + 2 * (T 2 m) := by
    linarith [h_sum_repr, h7]
  have h9 : T 1 m = ((∏ i ∈ Finset.range (m + 1), (a i : ℝ)) / (a (m + 2) : ℝ)) := by
    exact round1_T1_eq a h_pos m T (fun k => rfl)
  have h10 : T 2 m = ((∏ i ∈ Finset.range (m + 2), (a i : ℝ)) / ((a (m + 2) : ℝ) * (a (m + 3) : ℝ))) := by
    exact round1_T2_eq a m T (fun k => rfl)
  rw [h9, h10] at h8
  exact h8

theorem round1_x_m_converges_to_0 (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n)
  (P : ℕ)
  (Q : ℕ)
  (hQ_pos : Q > 0)
  (hP_pos : P > 0)
  (h_sum_eq : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ))
  (x : ℕ → ℝ)
  (hx_def : ∀ m : ℕ, x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ)))))
  (hx_ge : ∀ m : ℕ, x m ≥ 1 / (Q : ℝ))
  (R : ℝ)
  (hR_pos : R > 0)
  (h_log_a_n_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (a n : ℝ) / (2 : ℝ) ^ n) - R / 2| < ε):
  ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, m ≥ N → |x m - 0| < ε := by
  have h_lemma1 := round1_lemma1_d8f2 a h_pos R hR_pos h_log_a_n_converges
  have h_lemma2 := round1_lemma2_b9b4 a h_mono h_pos R hR_pos h_log_a_n_converges
  have h_lemma3 := round1_lemma3_6abf a h_pos P Q hQ_pos hP_pos h_sum_eq x hx_def R hR_pos h_log_a_n_converges
  intro ε hε
  rcases h_lemma3 with ⟨N₀, hN₀⟩
  rcases h_lemma1 (ε / 3) (by linarith) with ⟨N1, hN1⟩
  rcases h_lemma2 (ε / 3) (by linarith) with ⟨N2, hN2⟩
  set N := max N₀ (max N1 N2) with hN_def
  use N
  intro m hm
  have hN₀' : m ≥ N₀ := by linarith [hN_def, le_max_left N₀ (max N1 N2)]
  have hN1' : m ≥ N1 := by linarith [hN_def, le_max_right N₀ (max N1 N2), le_max_left N1 N2]
  have hN2' : m ≥ N2 := by linarith [hN_def, le_max_right N₀ (max N1 N2), le_max_right N1 N2]
  have h41 := hN1 m hN1'
  have h42 := hN2 m hN2'
  have h5 := hN₀ m hN₀'
  have h7 : x m > 0 := by
    have h71 := hx_ge m
    have h72 : (1 : ℝ) / (Q : ℝ) > 0 := by positivity
    linarith
  have h8 : |x m - 0| = x m := by
    rw [sub_zero, abs_of_pos h7]
  rw [h8]
  linarith [abs_lt.mp h41, abs_lt.mp h42]

theorem round1_get_contradiction_3f85 (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n)
  (P : ℕ)
  (Q : ℕ)
  (hQ_pos : Q > 0)
  (hP_pos : P > 0)
  (h_sum_eq : (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ))
  (x : ℕ → ℝ)
  (hx_def : ∀ m : ℕ, x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ)))))
  (hx_ge : ∀ m : ℕ, x m ≥ 1 / (Q : ℝ))
  (R : ℝ)
  (h_R_converges : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) / (2 : ℝ) ^ n) - R| < ε)
  (h_liminf : 1 < Filter.atTop.liminf (fun n ↦ (a n : ℝ) ^ ((1 : ℝ) / 2 ^ n))):
  False := by
  have h1 : R > 0 := by
    exact round1_R_is_positive_79ab a h_pos R h_R_converges h_liminf
  have h2 : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (a n : ℝ) / (2 : ℝ) ^ n) - R / 2| < ε := by
    exact round1_log_a_n_div_2_pow_n_converges_to_R_div_2 a h_pos R h_R_converges
  have h3 : ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, m ≥ N → |x m - 0| < ε := by
    exact round1_x_m_converges_to_0 a h_mono h_pos P Q hQ_pos hP_pos h_sum_eq x hx_def hx_ge R h1 h2
  have h4 : False := by
    exact round1_contradiction_from_convergence Q hQ_pos x hx_ge h3
  exact h4

theorem erdos_1051_irrational (a : ℕ → ℕ)
  (h_mono : StrictMono a)
  (h_pos : ∀ n, 0 < a n)
  (h_liminf : 1 < Filter.atTop.liminf (fun n ↦ (a n : ℝ) ^ ((1 : ℝ) / 2 ^ n))):
  Irrational (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
  by_cases h : ∃ (P Q : ℕ), Q > 0 ∧ P > 0 ∧ (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ)
  ·
    rcases h with ⟨P, Q, hQ_pos, hP_pos, h_sum_eq⟩
    have h1 : ∃ (x : ℕ → ℝ),
        (∀ m : ℕ, x m = (∏ i ∈ Finset.range (m + 2), (a i : ℝ)) * ((∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) - (∑ n ∈ Finset.range (m + 1), 1 / ((a n : ℝ) * (a (n + 1) : ℝ))))) ∧
        (∀ m : ℕ, x m ≥ 1 / (Q : ℝ)) := by
      exact round1_exists_x_and_lower_bound a h_mono h_pos P Q hQ_pos h_sum_eq
    rcases h1 with ⟨x, hx_def, hx_ge⟩
    have h2 : ∃ (K : ℝ), K > 0 ∧ ∀ n : ℕ, n ≥ 3 → (a n : ℝ) ≤ K * (∏ i ∈ Finset.range n, (a i : ℝ)) := by
      exact round1_exists_K_recurrence a h_mono h_pos P Q hQ_pos hP_pos h_sum_eq x hx_def
    rcases h2 with ⟨K, hK_pos, h3_rec⟩
    have h3 : ∃ (R : ℝ), ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(Real.log (∏ i ∈ Finset.range (n + 1), (a i : ℝ)) / (2 : ℝ) ^ n) - R| < ε := by
      exact round1_exists_R_converges_4eef a h_pos K hK_pos h3_rec
    rcases h3 with ⟨R, h_R_converges⟩
    have h4 : False := by
      exact round1_get_contradiction_3f85 a h_mono h_pos P Q hQ_pos hP_pos h_sum_eq x hx_def hx_ge R h_R_converges h_liminf
    exact False.elim h4
  ·
    have h5 : ¬ ∃ (P Q : ℕ), Q > 0 ∧ P > 0 ∧ (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) = (P : ℝ) / (Q : ℝ) := by simpa using h
    have h6 : Irrational (∑' n, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))) := by
      exact round1_not_rational_implies_irrational a h_mono h_pos h5
    exact h6

#print axioms erdos_1051_irrational
