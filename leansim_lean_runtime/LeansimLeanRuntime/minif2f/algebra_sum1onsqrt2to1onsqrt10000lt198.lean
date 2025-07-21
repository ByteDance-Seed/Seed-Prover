import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
  ∑ k in (Finset.Icc (2 : ℕ) 10000), (1 / Real.sqrt k) < 198 := by 

-- The original code had 'bylet' on one line. The 'let' tactic should be on a new line after 'by'.
let f := fun (x : ℝ) => 1 / Real.sqrt x
-- Define the summation bounds
let a : ℕ := 2
let b : ℕ := 10000

-- Define the finset for the sum and the real interval for the integral
-- Removed the let s_finset definition here, will use Finset.Icc a b directly.
-- let s_finset := Finset.Icc a b -- s_finset : Finset ℕ
let s_real := Set.Icc (a : ℝ) (b : ℝ) -- s_real : Set ℝ

-- Prove the interval is subset of [0, ∞). This is needed for Real.sqrt properties.
have h_s_real_subset_Ici_zero : s_real ⊆ Set.Ici 0 := by
  intro x hx -- x ∈ [a, b] (reals)
  -- Goal: x ∈ Set.Ici 0, i.e., 0 ≤ x
  -- hx : x ∈ Set.Icc (a : ℝ) (b : ℝ) which means (a : ℝ) ≤ x and x ≤ (b : ℝ).
  -- We have (a : ℝ) ≤ x (from hx.left).
  -- We know a = 2, so (a : ℝ) = 2. We need to show 0 ≤ (a : ℝ).
  have ha_ge_zero : (a : ℝ) ≥ 0 := by norm_num -- 2 ≥ 0, true.
  -- We need to prove 0 ≤ x from ha_ge_zero : 0 ≤ (a : ℝ) and hx.left : (a : ℝ) ≤ x.
  -- By transitivity (le_trans), 0 ≤ (a : ℝ) and (a : ℝ) ≤ x implies 0 ≤ x.
  exact le_trans ha_ge_zero hx.left

-- Prove Real.sqrt is continuous on s_real. This is needed for continuity of f and F.
have h_sqrt_continuous_on_s_real : ContinuousOn Real.sqrt s_real :=
  -- `continuous_sqrt` proves continuity on Set.univ. `Continuous.continuousOn` applies this to any subset s_real.
  Continuous.continuousOn continuous_sqrt

-- Step 1: Show f(x) = 1/√x is antitonic (decreasing) on the interval [a, b].
-- This uses the real interval s_real.
have hf_antitone : AntitoneOn f s_real := by
  -- We need to show that for any x, y in [a, b] with x ≤ y, f x ≥ f y.
  intro x hx y hy hxy
  -- Since x, y are in [a, b] = [2, 10000], we have x ≥ 2 and y ≥ 2.
  -- This implies x > 0 and y > 0.
  have hx_ge_two : (a : ℝ) ≤ x := hx.left
  have hx_pos : 0 < x := by
    have h0_lt_a : 0 < (a : ℝ) := by norm_num
    -- We have 0 < a and a ≤ x. Use lt_of_lt_of_le.
    exact lt_of_lt_of_le h0_lt_a hx_ge_two

  have hy_ge_two : (a : ℝ) ≤ y := hy.left
  have hy_pos : 0 < y := by
    have h0_lt_a : 0 < (a : ℝ) := by norm_num
    -- We have 0 < a and a ≤ y. Use lt_of_lt_of_le.
    exact lt_of_lt_of_le h0_lt_a hy_ge_two

  -- The square root function `Real.sqrt` is strictly increasing on [0, ∞).
  -- Thus, x ≤ y implies Real.sqrt x ≤ Real.sqrt y, provided x, y ≥ 0.
  have hsqrt_xy : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  -- Since x ≥ 2 and y ≥ 2, Real.sqrt x > 0 and Real.sqrt y > 0.
  have hsqrt_x_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hsqrt_y_pos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy_pos
  -- For positive numbers, taking the reciprocal reverses the inequality.
  -- Use `one_div_le_one_div_of_le`: $u \le v \implies 1/v \le 1/u$ for $0 < u \le v$.
  -- We have `Real.sqrt x ≤ Real.sqrt y` with `0 < Real.sqrt x`.
  -- The target is `1 / Real.sqrt y ≤ 1 / Real.sqrt x`.
  -- The theorem needs `0 < Real.sqrt x` and `Real.sqrt x ≤ Real.sqrt y`.
  -- We have `hsqrt_x_pos` and `hsqrt_xy`.
  apply one_div_le_one_div_of_le hsqrt_x_pos hsqrt_xy

-- Step 2: Apply the sum-integral comparison theorem.
-- We want to show ∑ k in Icc a b, f(k) <= f(a) + integral_a_b f(x) dx
-- Split the sum: ∑ k in Icc a b, f(k) = f(a) + ∑ k in Icc (a+1) b, f(k)
-- Use the theorem AntitoneOn.sum_le_integral_Ico: ∑ i in Ico a b, f(i+1) <= integral_a^b f(x) dx
-- The sum ∑ k in Icc (a+1) b, f(k) is equal to ∑ i in Ico a b, f(i+1).

-- Prove a ≤ b (nats).
have hab_nat : a ≤ b := by norm_num

-- Prove the sum can be split into f(a) + sum over Icc (a+1) b.
-- Replace s_finset with Finset.Icc a b in the goal and the theorem application.
have h_sum_split : (∑ k in Finset.Icc a b, f (↑k : ℝ)) = f (↑a : ℝ) + (∑ k in Finset.Icc (a + 1) b, f (↑k : ℝ)) := by
  -- Use Finset.add_sum_Ioc_eq_sum_Icc. Requires a ≤ b.
  -- The theorem states f a + ∑ x ∈ Ioc a b, f x = ∑ x ∈ Icc a b, f x.
  -- We apply the symmetric version of this theorem to match the goal.
  apply Eq.symm
  -- Goal is now f (↑a : ℝ) + ∑ k ∈ Finset.Icc (a + 1) b, f (↑k : ℝ) = ∑ k ∈ Finset.Icc a b, f (↑k : ℝ)

  -- The theorem `Finset.add_sum_Ioc_eq_sum_Icc` uses `Finset.Ioc a b`.
  -- For natural numbers, `Finset.Icc (a + 1) b` is the same as `Finset.Ioc a b` when `a ≤ b`.
  -- We prove this equality and rewrite the goal before applying the theorem.
  have h_Icc_eq_Ioc : Finset.Icc (a + 1) b = Finset.Ioc a b := by
    -- Prove set equality using extensionality.
    ext k
    -- Goal: k ∈ Finset.Icc (a + 1) b ↔ k ∈ Finset.Ioc a b
    -- Expand definitions of Finset.mem_Icc and Finset.mem_Ioc.
    simp only [Finset.mem_Icc, Finset.Ico, Finset.mem_Ioc]
    -- Goal: (a + 1 ≤ k ∧ k ≤ b) ↔ (a < k ∧ k ≤ b) -- Correct
    constructor -- Splits ↔ into → and ←
    . -- Proof (→): Assume a + 1 ≤ k ∧ k ≤ b.
      intro h_left
      constructor
      . -- Goal: a < k. We have a + 1 ≤ k. Nat.lt_of_succ_le proves a < k from a + 1 ≤ k.
        exact Nat.lt_of_succ_le h_left.left
      . -- Goal: k ≤ b. This is the second part of the hypothesis.
        exact h_left.right
    . -- Proof (←): Assume a < k ∧ k ≤ b.
      intro h_right
      constructor
      . -- Goal: a + 1 ≤ k. We have a < k. Nat.succ_le_of_lt proves a + 1 ≤ k from a < k.
        exact Nat.succ_le_of_lt h_right.left
      . -- Goal: k ≤ b. This is the second part of the hypothesis.
        exact h_right.right

  -- Rewrite `Finset.Icc (a + 1) b` to `Finset.Ioc a b` in the goal.
  rw [h_Icc_eq_Ioc]
  -- Goal: f (↑a : ℝ) + ∑ k ∈ Finset.Ioc a b, f (↑k : ℝ) = ∑ k ∈ Finset.Icc a b, f (↑k : ℝ)

  -- Define the function g : ℕ → ℝ to match the domain of the sum index.
  -- This function is definitionally equal to `f (↑k : ℝ)` for each k.
  -- By defining it explicitly and hinting Lean to use it in the theorem application,
  -- we help the unifier match the goal terms.
  let g := fun k : ℕ => f (↑k : ℝ)

  -- Now apply the theorem Finset.add_sum_Ioc_eq_sum_Icc.
  -- The theorem requires a function `f'` from the index type (ℕ) to the sum type (ℝ).
  -- We use the explicitly defined function `g` for `f'`.
  -- The goal `f (↑a : ℝ) + ∑ k ∈ Finset.Ioc a b, f (↑k : ℝ) = ∑ k ∈ Finset.Icc a b, f (↑k : ℝ)`
  -- is definitionally equal to `g a + ∑ k ∈ Finset.Ioc a b, g k = ∑ k ∈ Finset.Icc a b, g k`.
  -- Applying the theorem with `f := g` and the hypothesis `hab_nat` proves this equality.
  -- The previous error was due to Lean failing to unify the function automatically.
  apply Finset.add_sum_Ioc_eq_sum_Icc (f := g) hab_nat

-- Define the mapping function and the domain finset for the index shift.
-- Moved these definitions and the following proofs outside the `h_sum_shift` proof
-- block to ensure they are available in the main context when `h_sum_shift` is proven.
let map_fn := fun i : ℕ => i + 1
let dom_set := Finset.Ico a b -- The set {a, a+1, ..., b-1}
-- Define the function to be summed over the image set.
-- Moved the definition of sum_fn outside the proof block, as it is used
-- in the `apply` tactic which should refer to terms in the current context.
let sum_fn := fun k : ℕ => f (↑k : ℝ)

-- Prove that the image of the domain set under the mapping function is the target finset.
-- We need Finset.image map_fn dom_set = Finset.Icc (a + 1) b.
-- The previous proof using extensionality and manually constructing the existential
-- witness caused an error message (`unsolved goals case a.mpr`).
-- We replace the manual proof with `simp` and a manual proof for the resulting equivalence.
have h_finset_image_eq : Finset.image map_fn dom_set = Finset.Icc (a + 1) b := by
  -- Prove set equality using extensionality.
  ext k
  -- The goal is now k ∈ Finset.image map_fn dom_set ↔ k ∈ Finset.Icc (a + 1) b.
  -- Expand definitions of Finset.mem_image, Finset.Icc. Keep Finset.mem_Ico as y ∈ dom_set for now.
  simp only [Finset.mem_image, Finset.mem_Icc]
  -- The goal is now (∃ (y : ℕ), y ∈ dom_set ∧ y + 1 = k) ↔ (a + 1 ≤ k ∧ k ≤ b).
  constructor -- Splits ↔ into → and ←
  . -- Proof (→): Assume ∃ y : ℕ, y ∈ dom_set ∧ y + 1 = k
    intro h_exists
    rcases h_exists with ⟨y, hy_in_dom_set, hy_succ_eq_k⟩
    -- Goal: a + 1 ≤ k ∧ k ≤ b
    -- Expand hy_in_dom_set: y ∈ dom_set, which is definitionally y ∈ Finset.Ico a b.
    -- The lemma Finset.mem_Ico states this is equivalent to a ≤ y ∧ y < b.
    -- We need the hypothesis in the form of a conjunction to use `.left` and `.right` later.
    -- The previous use of `simp only [Finset.mem_Ico] at hy_in_dom_set` reported "no progress".
    -- Replacing it with `rw [Finset.mem_Ico]` explicitly applies the equivalence to rewrite the hypothesis.
    rw [Finset.mem_Ico] at hy_in_dom_set -- -- Use rw to explicitly rewrite the hypothesis using the iff lemma.
    -- hy_in_dom_set is now a ≤ y ∧ y < b.
    have hy_ge_a : a ≤ y := hy_in_dom_set.left
    have hy_lt_b : y < b := hy_in_dom_set.right
    constructor
    . -- Goal: a + 1 ≤ k. We have hy_ge_a : a ≤ y and hy_succ_eq_k : y + 1 = k.
      -- From a ≤ y, we get a + 1 ≤ y + 1.
      have h_a_succ_le_y_succ : a + 1 ≤ y + 1 := Nat.add_le_add_right hy_ge_a 1
      -- By transitivity, a + 1 ≤ y + 1 and y + 1 = k implies a + 1 ≤ k.
      -- The previous error was on the line `rw [hy_succ_eq_k] at h_a_succ_le_y_succ`.
      -- We replace the rewrite and the following exact with an explicit le_trans.
      exact le_trans h_a_succ_le_y_succ (le_of_eq hy_succ_eq_k) -- Corrected: Used le_trans instead of rewrite
    . -- Goal: k ≤ b
      -- We have hy_lt_b : y < b and hy_succ_eq_k : y + 1 = k.
      -- k = y + 1. We need y + 1 ≤ b.
      -- We have y < b, which is equivalent to y + 1 ≤ b (for natural numbers) by Nat.succ_le_of_lt.
      have hy_succ_le_b : y + 1 ≤ b := Nat.succ_le_of_lt hy_lt_b
      -- We have y + 1 = k (hy_succ_eq_k) and y + 1 ≤ b (hy_succ_le_b).
      -- We want to show k ≤ b.
      -- Use `le_of_eq_trans` with `k = y + 1` and `y + 1 ≤ b`.
      -- The theorem `le_of_eq_trans` proves `a = b → b ≤ c → a ≤ c`.
      -- Here `a` is `k`, `b` is `y + 1`, `c` is `b`.
      -- The equality is `k = y + 1`, which is `Eq.symm hy_succ_eq_k`.
      -- The inequality is `y + 1 ≤ b`, which is `hy_succ_le_b`.
      -- The theorem le_of_eq_trans does not exist. We use le_trans combined with le_of_eq.
      exact le_trans (le_of_eq (Eq.symm hy_succ_eq_k)) hy_succ_le_b -- Corrected: Used le_trans (le_of_eq ..) instead of le_of_eq_trans
  . -- Proof (←): Assume a + 1 ≤ k ∧ k ≤ b
    intro h_a_succ_le_k_and_k_le_b
    -- Goal: ∃ y : ℕ, y ∈ dom_set ∧ y + 1 = k
    -- We know a = 2, so a + 1 = 3. The assumption is 3 ≤ k ∧ k ≤ b.
    -- Since 3 ≤ k, k is at least 3, so k ≠ 0.
    have hk_ne_zero : k ≠ 0 := by omega
    -- Since k ≠ 0, there exists a natural number y such that k = y + 1.
    obtain ⟨y, hy_succ_eq_k⟩ := Nat.exists_eq_succ_of_ne_zero hk_ne_zero
    -- We need to show y ∈ dom_set and y + 1 = k.
    -- We already have hy_succ_eq_k : y + 1 = k. This is the second part.
    -- We need to prove y ∈ dom_set.
    -- From a + 1 ≤ k (from hypothesis) and k = y + 1 (by definition of y), we get a + 1 ≤ y + 1.
    have ha_succ_le_y_succ : a + 1 ≤ y + 1 := by
      -- We have h_a_succ_le_k_and_k_le_b.left : a + 1 ≤ k.
      -- We have hy_succ_eq_k : k = y + 1.
      -- Use `rw` to substitute `k` with `y + 1` in `h_a_succ_le_k_and_k_le_b.left`.
      rw [hy_succ_eq_k] at h_a_succ_le_k_and_k_le_b -- This rewrite modifies the hypothesis
      exact h_a_succ_le_k_and_k_le_b.left
    -- Apply `Nat.le_of_succ_le_succ` to `ha_succ_le_y_succ` to get `a ≤ y`.
    have ha_le_y : a ≤ y := Nat.le_of_succ_le_succ ha_succ_le_y_succ
    -- From k ≤ b (from hypothesis) and k = y + 1 (by definition of y), we get y + 1 ≤ b.
    -- By Nat.lt_of_succ_le, this implies y < b.
    have hy_succ_le_b : y + 1 ≤ b := by
      -- We have h_a_succ_le_k_and_k_le_b.right : k ≤ b.
      -- We have hy_succ_eq_k : k = y + 1.
      -- Use `rw` to substitute `k` with `y + 1` in `h_a_succ_le_k_and_k_le_b.right`.
      rw [hy_succ_eq_k] at h_a_succ_le_k_and_k_le_b -- This rewrite modifies the hypothesis again
      exact h_a_succ_le_k_and_k_le_b.right
    -- Apply `Nat.lt_of_succ_le` to `hy_succ_le_b` to get `y < b`.
    have hy_lt_b : y < b := Nat.lt_of_succ_le hy_succ_le_b
    -- We have found a witness y and proven y ∈ dom_set (i.e. a <= y and y < b) and y + 1 = k.
    -- Goal: ∃ y : ℕ, y ∈ dom_set ∧ y + 1 = k
    -- Use `exists_intro` with the witness `y`.
    use y
    -- Goal: y ∈ dom_set ∧ y + 1 = k
    -- Rewrite the first part `y ∈ dom_set` using its definition via Finset.mem_Ico.
    -- This makes the goal explicitly `(a ≤ y ∧ y < b) ∧ y + 1 = k`.
    rw [Finset.mem_Ico]
    -- Goal: (a ≤ y ∧ y < b) ∧ y + 1 = k
    -- Apply constructor to split into `a ≤ y ∧ y < b` and `y + 1 = k`.
    constructor
    . -- Goal: a ≤ y ∧ y < b
      -- Apply constructor again to split into `a ≤ y` and `y < b`.
      constructor
      . -- Goal: a ≤ y. We have proven ha_le_y.
        exact ha_le_y
      . -- Goal: y < b. We have proven hy_lt_b.
        exact hy_lt_b
    . -- Goal: y + 1 = k. We have proven hy_succ_eq_k : k = y + 1. The goal is y + 1 = k.
      -- We need to prove map_fn y = k which is y + 1 = k.
      -- Our hypothesis is k = y + 1. We use symmetry.
      exact Eq.symm hy_succ_eq_k -- Corrected: Use Eq.symm to match the goal orientation.

-- Prove the sum over Icc (a+1) b is equal to sum over Ico a b with shifted index.
-- The original proof of this `have` block had `let` and `have` statements
-- defined *inside* the `by` block, which likely caused scoping issues,
-- leading to the "unsolved goals" error. We have moved those definitions and
-- proofs to the main proof context above.
have h_sum_shift : (∑ k in Finset.Icc (a + 1) b, f (↑k : ℝ)) = (∑ i in Finset.Ico a b, f (↑(i + 1) : ℝ)) := by
  -- Rewrite the goal's LHS using `h_finset_image_eq` which was proven above.
  -- This changes the goal from sum over Icc to sum over Image.
  rw [← h_finset_image_eq]
  -- Goal: ∑ k ∈ Finset.image map_fn dom_set, f (↑k : ℝ) = ∑ i ∈ Finset.Ico a b, f (↑(i + 1) : ℝ)

  -- Use `change` tactics to make the goal terms match the structure of `Finset.sum_image`.
  -- The theorem `Finset.sum_image` proves `∑ x ∈ image g s, f' x = ∑ x ∈ s, f' (g x)`
  -- given `hg : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y`.
  -- We want s = dom_set, g = map_fn, f' = sum_fn.
  -- The goal is currently ∑ k ∈ Finset.image map_fn dom_set, f (↑k : ℝ) = ∑ i ∈ Finset.Ico a b, f (↑(i + 1) : ℝ).
  -- Change the LHS using `sum_fn k = f (↑k : ℝ)`.
  change ∑ k in Finset.image map_fn dom_set, sum_fn k = ∑ i in Finset.Ico a b, f (↑(i + 1) : ℝ)
  -- Change the RHS by replacing `Finset.Ico a b` with `dom_set`.
  change ∑ k in Finset.image map_fn dom_set, sum_fn k = ∑ i in dom_set, f (↑(i + 1) : ℝ)
  -- Change the RHS by replacing `i + 1` with `map_fn i`.
  change ∑ k in Finset.image map_fn dom_set, sum_fn k = ∑ i in dom_set, f (↑(map_fn i) : ℝ)
  -- Change the RHS by replacing `f (↑(map_fn i) : ℝ)` with `sum_fn (map_fn i)`.
  change ∑ k in Finset.image map_fn dom_set, sum_fn k = ∑ i in dom_set, sum_fn (map_fn i)

  -- Apply the theorem `Finset.sum_image` which requires the injectivity proof `hg` as a premise.
  -- -- The previous error was "application type mismatch" because the pre-proven hypothesis `h_inj`
  -- -- had a type signature that Lean's unifier couldn't match exactly with the expected argument
  -- -- type of `Finset.sum_image`.
  -- -- We fix this by providing the injectivity proof inline as the argument to `Finset.sum_image`.
  apply Finset.sum_image
  -- The goal is now the injectivity hypothesis required by `Finset.sum_image`:
  -- ∀ (x : ℕ), x ∈ dom_set → ∀ (y : ℕ), y ∈ dom_set → map_fn x = map_fn y → x = y
  intro x hx y hy h_eq_succ -- Introduce universal quantifiers and implications
  -- Goal: x = y
  -- We have h_eq_succ : map_fn x = map_fn y, i.e., x + 1 = y + 1
  -- Use Nat.succ_inj which proves x + 1 = y + 1 ↔ x = y. We need the forward direction.
  exact Nat.succ_inj.mp h_eq_succ


-- Apply AntitoneOn.sum_le_integral_Ico to the shifted sum.
have h_shifted_sum_le_integral : (∑ i in Finset.Ico a b, f (↑(i + 1) : ℝ)) ≤ ∫ (x : ℝ) in (a : ℝ)..(b : ℝ), f x := by
  -- Requires AntitoneOn f (Set.Icc (a : ℝ) (b : ℝ)) and a ≤ b (nats).
  -- The original attempt used the wrong theorem name `Finset.AntitoneOn.sum_le_integral_Icc`.
  -- Based on the hint and the structure of the sum, `AntitoneOn.sum_le_integral_Ico` is the correct theorem to bound `∑_{i=a}^{b-1} f(i+1)` by `∫_a^b f(x) dx`.
  -- The theorem requires the `a ≤ b` proof before the `AntitoneOn` proof.
  apply AntitoneOn.sum_le_integral_Ico hab_nat hf_antitone
  -- Note: This theorem does NOT require interval integrability of f.

-- Combine the results to get the desired sum-integral inequality.
-- Replace s_finset with Finset.Icc a b in the goal and the inequality.
have h_sum_le_integral : (∑ k in Finset.Icc a b, f (↑k : ℝ)) ≤ f (↑a : ℝ) + ∫ (x : ℝ) in (a : ℝ)..(b : ℝ), f x := by
  -- Rewrite the sum using the split and the index shift.
  rw [h_sum_split, h_sum_shift]
  -- Goal: f (↑a : ℝ) + ∑ i in Finset.Ico a b, f (↑(i + 1) : ℝ) ≤ f (↑a : ℝ) + ∫ (x : ℝ) in (a : ℝ)..(b : ℝ), f x
  -- Apply add_le_add_left using the inequality for the shifted sum.
  apply add_le_add_left h_shifted_sum_le_integral


-- Need to show the integrand is interval integrable for the Fundamental Theorem of Calculus later.
-- A continuous function on a closed interval is interval integrable.
have h_integrand_integrable : IntervalIntegrable (fun x => 1 / Real.sqrt x) MeasureTheory.volume (a : ℝ) (b : ℝ) := by
  -- We need to show the integrand is continuous on [a, b] = s_real.
  have h_integrand_continuous_on_s_real : ContinuousOn (fun x => 1 / Real.sqrt x) s_real := by
    -- Show Real.sqrt x is non-zero on the set s_real.
    have h_sqrt_nonzero_on_s_real : ∀ x ∈ s_real, Real.sqrt x ≠ 0 := by
      intro x hx; simp [Set.mem_Icc] at hx
      -- Proving 0 < x from (a : ℝ) < x and 0 < (a : ℝ)
      -- can be done using transitivity. We know (a : ℝ) = 2, and 0 < 2 is true.
      have hx_pos : 0 < x := by
        have h0_lt_a : 0 < (a : ℝ) := by norm_num
        -- We have 0 < a and a ≤ x. Use lt_of_lt_of_le.
        exact lt_of_lt_of_le h0_lt_a hx.left
      -- We need to show Real.sqrt x ≠ 0. We have hx_pos : 0 < x.
      -- The theorem Real.sqrt_ne_zero'.mpr gives Real.sqrt x ≠ 0 ↔ 0 < x.
      -- We need to apply the backward direction (mpr) to the hypothesis hx_pos.
      apply Real.sqrt_ne_zero'.mpr
      exact hx_pos

    -- Define g(x) = (Real.sqrt x)⁻¹
    let g := fun (x : ℝ) => (Real.sqrt x)⁻¹

    -- Show g is continuous on the set s_real using ContinuousOn.inv₀.
    have hg_continuous_on_s_real : ContinuousOn g s_real := by
      -- Apply the theorem `ContinuousOn.inv₀` which requires continuity and non-zero on the set.
      apply ContinuousOn.inv₀
      -- The first argument is `ContinuousOn f s`, where `f = Real.sqrt`. We use the hypothesis proven earlier.
      exact h_sqrt_continuous_on_s_real
      -- The second argument is `∀ x ∈ s, f x ≠ 0`. We use the hypothesis proven just above.
      exact h_sqrt_nonzero_on_s_real

    -- Show `fun x => 1 * g x` is continuous on the set s_real.
    have h_product_form_continuous_on_s_real : ContinuousOn (fun x => (1 : ℝ) * (Real.sqrt x)⁻¹) s_real := by
      -- We need to show the function `fun x => (1 : ℝ) * (Real.sqrt x)⁻¹` is continuous on s_real.
      -- This is the product of the constant function `fun x => (1 : ℝ)` and the function `fun x => (Real.sqrt x)⁻¹`.
      -- We know `hg_continuous_on_s_real` is `ContinuousOn (fun x => (Real.sqrt x)⁻¹) s_real`.
      -- We know the constant function fun x => 1 is continuous everywhere, and hence continuous on s_real.
      -- We ensure the constant 1 is treated as a Real number.
      have h_const_continuous_on_s_real : ContinuousOn (fun x : ℝ => (1 : ℝ)) s_real := by
        -- We use `Continuous.continuousOn` which proves continuity on a subset from global continuity.
        -- We break it down into applying the theorem and providing its argument.
        apply Continuous.continuousOn
        -- Use the continuity tactic to prove the continuity of the constant function.
        -- The tactic `continuity` can prove the continuity of `fun x => 1`.
        continuity -- Proves Continuous (fun x : ℝ => 1)
      -- Apply the theorem `ContinuousOn.mul` to show the product is continuous.
      -- `ContinuousOn.mul h_f h_g` proves `ContinuousOn (fun x => f x * g x) s`.
      -- Here f = `fun x => (1 : ℝ)`, g = `fun x => (Real.sqrt x)⁻¹`, h_f = `h_const_continuous_on_s_real`, h_g = `hg_continuous_on_s_real`.
      apply ContinuousOn.mul h_const_continuous_on_s_real hg_continuous_on_s_real

    -- Now prove that `integrand x` is definitionally equal to `1 * g x` for all `x ∈ s_real`.
    -- integrand x is `1 / Real.sqrt x`. 1 * g x is `1 * (Real.sqrt x)⁻¹`.
    have h_integrand_eq_product_form : ∀ x ∈ s_real, (1 / Real.sqrt x) = ((1 : ℝ) * (Real.sqrt x)⁻¹) := by
      intro x hx
      -- 1 / Real.sqrt x = 1 * (Real.sqrt x)⁻¹ holds by definition in a field.
      -- The goal is (1 : ℝ) / Real.sqrt x = (1 : ℝ) * (Real.sqrt x)⁻¹.
      -- This is a definitional equality in a field. Let's use `dsimp` to unfold definitions, then `rfl`.
      -- We remove dsimp as it made no progress and rfl is sufficient for definitional equality.
      rfl

    -- Finally, use `ContinuousOn.congr` to show `ContinuousOn integrand s_real` from `ContinuousOn product_form s_real` and the equality.
    -- The integrand function is `fun x => 1 / Real.sqrt x`.
    -- The function `h_product_form_continuous_on_s_real` is `ContinuousOn (fun x => (1 : ℝ) * (Real.sqrt x)⁻¹) s_real`.
    -- We have `h_integrand_eq_product_form : ∀ x ∈ s_real, (fun x => 1 / Real.sqrt x) x = (fun x => (1 : ℝ) * (Real.sqrt x)⁻¹) x`.
    -- We use `exact` for a perfect match.
    exact ContinuousOn.congr h_product_form_continuous_on_s_real h_integrand_eq_product_form

  -- Now apply the theorem `ContinuousOn.intervalIntegrable_of_Icc` with the necessary hypotheses.
  -- This theorem requires (a : ℝ) ≤ (b : ℝ) and ContinuousOn f (Set.Icc (a : ℝ) (b : ℝ)).
  -- We provide these in the required order.
  apply ContinuousOn.intervalIntegrable_of_Icc
  . -- Proof for (a : ℝ) ≤ (b : ℝ).
    norm_num
  . -- Proof for ContinuousOn f (Set.Icc (a : ℝ) (b : ℝ)).
    -- This is exactly the hypothesis h_integrand_continuous_on_s_real.
    exact h_integrand_continuous_on_s_real

-- Step 3: Calculate the definite integral ∫ (x : ℝ) in a..b, f x.
-- We use the Fundamental Theorem of Calculus. Let F(x) be an antiderivative of f(x).
-- f(x) = x^(-1/2). An antiderivative is F(x) = 2 * x^(1/2) = 2 * Real.sqrt x.
let F_integral := fun (x : ℝ) => 2 * Real.sqrt x

-- F_integral is differentiable on (0, ∞). (a, b) = (2, 10000) is a subset of (0, ∞).
-- We need to show `HasDerivAt F_integral (f x) x` for `x ∈ Set.Ioo (a : ℝ) (b : ℝ)`.
have hF_deriv : ∀ x ∈ Set.Ioo (a : ℝ) (b : ℝ), HasDerivAt F_integral (1 / Real.sqrt x) x := by
  intro x hx
  simp at hx
  -- 2 < x ∧ x < 10000
  -- Proving 0 < x from (a : ℝ) < x and 0 < (a : ℝ)
  -- can be done using transitivity. We know (a : ℝ) = 2, and 0 < 2 is true.
  have hx_pos : 0 < x := by
    have h0_lt_a : 0 < (a : ℝ) := by norm_num
    -- We have 0 < a and a < x. Use lt_trans.
    exact lt_trans h0_lt_a hx.left
  -- The derivative of `Real.sqrt x` is `1 / (2 * Real.sqrt x)`.
  have h_sqrt_deriv : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := by
    apply Real.hasDerivAt_sqrt hx_pos.ne'
  -- The derivative of `2 * g(x)` is `2 * g'(x)`.
  convert HasDerivAt.const_mul 2 h_sqrt_deriv using 1
  -- Simplify `2 * (1 / (2 * Real.sqrt x))` to `1 / Real.sqrt x`.
  field_simp [hx_pos.ne'] -- Requires x ≠ 0, which is true.

-- Need to show the antiderivative `F_integral = fun x => 2 * Real.sqrt x` is continuous on `[a, b]` for the FTC.
have hF_continuous_on_s_real : ContinuousOn F_integral s_real := by
  -- F_integral(x) = 2 * Real.sqrt x
  -- Real.sqrt is continuous on [0, ∞). s_real = Set.Icc (a : ℝ) (b : ℝ) is a subset of [0, ∞) as a = 2 >= 0.
  -- We use the hypothesis h_sqrt_continuous_on_s_real which proves ContinuousOn Real.sqrt on s_real.
  -- The constant function fun x => 2 is continuous everywhere.
  -- We ensure the constant 2 is treated as a Real number.
  -- Prove the constant function is continuous on s_real.
  have h_const_continuous_on_s_real : ContinuousOn (fun x : ℝ => (2 : ℝ)) s_real := by
    -- We use `Continuous.continuousOn` which proves continuity on a subset from global continuity.
    -- We break it down into applying the theorem and providing its argument.
    apply Continuous.continuousOn
    -- Use the continuity tactic to prove the continuity of the constant function.
    -- The tactic `continuity` can prove the continuity of `fun x => 2`.
    continuity -- Proves Continuous (fun x : ℝ => 2)

  -- We need to show that the function F_integral(x) = 2 * Real.sqrt x is continuous on s_real.
  -- This is a multiplication of two functions.
  -- We use the theorem `ContinuousOn.mul`.
  -- We have `h_const_continuous_on_s_real` (continuity of `fun x => (2 : ℝ)`) and `h_sqrt_continuous_on_s_real` (continuity of `Real.sqrt`).
  -- Apply the theorem `ContinuousOn.mul`.
  -- Use `ContinuousOn.mul` for multiplication of functions with codomain ℝ.
  apply ContinuousOn.mul h_const_continuous_on_s_real h_sqrt_continuous_on_s_real

-- The correct theorem for the Fundamental Theorem of Calculus is `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`.
have h_integral_value : ∫ (x : ℝ) in (a : ℝ)..(b : ℝ), f x = F_integral (b : ℝ) - F_integral (a : ℝ) := by
  -- Apply the Fundamental Theorem of Calculus.
  -- This theorem requires a ≤ b, F_integral continuous on [a, b], F_integral has deriv f on (a, b), and f is integrable on [a, b).
  -- The theorem actually requires `IntervalIntegrable f volume a b` and `∀ x ∈ Set.Ioo a b, HasDerivAt F_integral (f x) x` and `ContinuousOn F_integral (Set.Icc a b)`.
  -- We have already proven these. The order in the apply matters.
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
  · -- a ≤ b (reals)
    norm_num
  · -- F_integral is continuous on s_real = [a, b].
    exact hF_continuous_on_s_real
  · -- F_integral has derivative f x for x ∈ Set.Ioo a b.
    exact hF_deriv
  · -- f is interval integrable on [a, b].
    exact h_integrand_integrable

-- Calculate Real.sqrt(10000) = 100.
have h_sqrt_b_val : Real.sqrt (10000 : ℝ) = 100 := by
  -- Use `Real.sqrt_eq_iff_sq_eq` which requires non-negativity of both terms.
  have h_10000_nonneg : (10000 : ℝ) ≥ 0 := by norm_num
  have h_100_nonneg : (100 : ℝ) ≥ 0 := by norm_num
  rw [Real.sqrt_eq_iff_sq_eq h_10000_nonneg h_100_nonneg]
  -- The goal is now (100 : ℝ) ^ 2 = (10000 : ℝ).
  norm_num

-- Calculate the value of the integral using the FTC and numerical results.
have h_integral_value_simp : ∫ (x : ℝ) in (↑a : ℝ)..(↑b : ℝ), f x = (2 : ℝ) * (100 : ℝ) - (2 : ℝ) * Real.sqrt (2 : ℝ) := by
  -- Rewrite the integral term using the FTC result.
  rw [h_integral_value]
  -- Expand the definitions of f and F_integral.
  dsimp [f, F_integral]
  -- Goal is now (2 * Real.sqrt 10000) - (2 * Real.sqrt 2) = (2 * 100) - (2 * Real.sqrt 2).
  -- Use h_sqrt_b_val to simplify Real.sqrt 10000 to 100.
  rw [h_sqrt_b_val]
  -- Goal is now (2 * 100) - (2 * Real.sqrt 2) = 200 - (2 * Real.sqrt 2).
  -- This is definitionally true.

-- Substitute the integral value into the sum inequality from Step 2.
-- Replace s_finset with Finset.Icc a b in the goal and the inequality.
have h_sum_le_subst_integral : (∑ k in Finset.Icc a b, f (↑k : ℝ)) ≤ f (↑a : ℝ) + ((2 : ℝ) * (100 : ℝ) - (2 : ℝ) * Real.sqrt (2 : ℝ)) := by
  -- Rewrite the integral term using the calculated value from `h_integral_value_simp`.
  rw [h_integral_value_simp] at h_sum_le_integral
  exact h_sum_le_integral

-- Calculate f (↑a : ℝ) = 1 / Real.sqrt (2 : ℝ).
have h_fa_value : f (↑a : ℝ) = 1 / Real.sqrt (2 : ℝ) := by
  -- Expand definition of f and cast a=2 to a real.
  dsimp [f]
  -- The goal is now 1 / Real.sqrt (↑a : ℝ) = 1 / Real.sqrt (2 : ℝ).
  -- Since a = 2, ↑a = 2, so this is 1 / Real.sqrt (2 : ℝ) = 1 / Real.sqrt (2 : ℝ).
  -- This is definitionally true.

-- Substitute the value of f (↑a : ℝ) into the sum inequality.
have h_sum_le_value : (∑ k in Finset.Icc a b, f (↑k : ℝ)) ≤ (1 : ℝ) / Real.sqrt (2 : ℝ) + ((2 : ℝ) * (100 : ℝ) - (2 : ℝ) * Real.sqrt (2 : ℝ)) := by
  -- Rewrite the f(a) term using `h_fa_value`.
  rw [h_fa_value] at h_sum_le_subst_integral
  exact h_sum_le_subst_integral

-- Simplify the upper bound: 1/√2 + 200 - 2√2 = 200 - 3/√2.
-- Note that (2 : ℝ) * (100 : ℝ) is definitionally 200.
have h_upper_bound_simp : (1 : ℝ) / Real.sqrt (2 : ℝ) + ((2 : ℝ) * (100 : ℝ) - (2 : ℝ) * Real.sqrt (2 : ℝ)) = (200 : ℝ) - (3 : ℝ) / Real.sqrt (2 : ℝ) := by
  -- We need to show this equality. Use field_simp and ring.
  -- Ensure Real.sqrt(2) is non-zero for field operations.
  have h_sqrt2_nz : (Real.sqrt (2 : ℝ)) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  -- Clear the denominator by multiplying by sqrt(2).
  field_simp [h_sqrt2_nz]
  -- Goal: (1 : ℝ) + ((2 : ℝ) * (100 : ℝ) - (2 : ℝ) * √(2 : ℝ)) * √(2 : ℝ) = (200 : ℝ) * √(2 : ℝ) - (3 : ℝ)

  -- Apply (a-b)*c = ac - bc
  rw [sub_mul]
  -- Goal: (1 : ℝ) + (2 : ℝ) * (100 : ℝ) * √(2 : ℝ) - ((2 : ℝ) * √(2 : ℝ)) * √(2 : ℝ) = (200 : ℝ) * √(2 : ℝ) - (3 : ℝ)

  -- We want to simplify ((2 : ℝ) * √(2 : ℝ)) * √(2 : ℝ) to 8.
  -- This uses (a*b)*c = a*(b*c) with a=2, b=sqrt(2), c=sqrt(2)
  rw [mul_assoc (2 : ℝ) (Real.sqrt (2 : ℝ)) (Real.sqrt (2 : ℝ))]
  -- Goal: (1 : ℝ) + (2 : ℝ) * (100 : ℝ) * √(2 : ℝ) - (2 : ℝ) * (√(2 : ℝ) * √(2 : ℝ)) = (200 : ℝ) * √(2 : ℝ) - (3 : ℝ)
  rw [Real.mul_self_sqrt (by norm_num)]
  -- Goal: (1 : ℝ) + (2 : ℝ) * (100 : ℝ) * √(2 : ℝ) - (2 : ℝ) * (2 : ℝ) = (200 : ℝ) * √(2 : ℝ) - (3 : ℝ)
  -- norm_num simplifies 2*100 to 200 and 2*2 to 4.
  norm_num
  -- Goal: (1 : ℝ) + (200 : ℝ) * Real.sqrt (2 : ℝ) - (4 : ℝ) = (200 : ℝ) * Real.sqrt (2 : ℝ) - (3 : ℝ)
  -- The previous sequence of rw and norm_num was complicated and had an error.
  -- The goal is now a polynomial equality in terms of `Real.sqrt (2 : ℝ)`.
  -- The `ring` tactic should be able to prove this.
  -- We use `ring` to simplify the algebraic expression involving addition, subtraction, and multiplication.
  -- The term `(200 : ℝ) * Real.sqrt (2 : ℝ)` is treated as an atomic variable by `ring`.
  ring -- Replaces the sequence of manual rewrites and norm_num


-- The sum is less than or equal to 200 - 3 / Real.sqrt 2.
-- The sum term is (∑ k in Finset.Icc a b, f (↑k : ℝ)).
-- The goal sum term is ∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k).
-- These are definitionally equal.
-- Replace s_finset with Finset.Icc a b in the goal and the inequality.
have h_sum_le_final : (∑ k in Finset.Icc a b, f (↑k : ℝ)) ≤ (200 : ℝ) - (3 : ℝ) / Real.sqrt (2 : ℝ) := by
  -- We have h_sum_le_value: sum ≤ (1/√2 + (2 * 100 - 2√2)).
  -- We want to show sum ≤ (200 - 3/√2).
  -- We have h_upper_bound_simp: (1/√2 + (200 - 2√2)) = (200 - 3/√2).
  -- The term (2 * 100) is definitionally equal to 200.
  -- So the RHS of h_sum_le_value is definitionally equal to the LHS of h_upper_bound_simp.
  -- We have `h_sum_le_value : Sum ≤ RHS_of_h_sum_le_value`.
  -- We have `h_upper_bound_simp : RHS_of_h_sum_le_value = RHS_of_goal`.
  -- By transitivity, Sum ≤ RHS_of_goal.
  exact le_trans h_sum_le_value (le_of_eq h_upper_bound_simp)


-- Step 5: Show the upper bound 200 - 3 / Real.sqrt 2 is less than 198.
have h_upper_bound_lt_198 : (200 : ℝ) - (3 : ℝ) / Real.sqrt (2 : ℝ) < (198 : ℝ) := by
  -- Start with the goal: (200 - 3/√2) < 198
  -- Add 3/√2 to both sides: 200 < 198 + 3/√2
  -- Use `sub_lt_iff_lt_add` equivalence: `a - c < b ↔ a < b + c`.
  -- Here `a = 200`, `b = 198`, `c = 3/√2`.
  -- Goal: `(200 : ℝ) - (3 : ℝ) / Real.sqrt (2 : ℝ) < (198 : ℝ)` which is `a - c < b`.
  -- We want to rewrite this to `a < b + c`, which is `(200 : ℝ) < (198 : ℝ) + (3 : ℝ) / Real.sqrt (2 : ℝ)`.
  rw [sub_lt_iff_lt_add]
  -- Goal: (200 : ℝ) < (198 : ℝ) + (3 : ℝ) / Real.sqrt (2 : ℝ)

  -- Subtract 198 from both sides: 200 - 198 < (198 + 3/√2) - 198
  -- Use the equivalence `a < b ↔ a - c < b - c`. Apply it with c = 198.
  -- This is the reverse direction of the equivalence.
  rw [← sub_lt_sub_iff_right (198 : ℝ)]
  -- Goal: (200 : ℝ) - (198 : ℝ) < ((198 : ℝ) + (3 : ℝ) / Real.sqrt (2 : ℝ)) - (198 : ℝ)

  -- Simplify the numerical subtraction 200 - 198 = 2 on the LHS and the expression on the RHS.
  norm_num
  -- Goal: (2 : ℝ) < (3 : ℝ) / Real.sqrt (2 : ℝ)

  -- Apply the division equivalence: a < b/c ↔ a*c < b, for c > 0.
  -- Since Real.sqrt 2 is positive, we can multiply by it.
  have h_sqrt2_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  -- Use `lt_div_iff` equivalence: `a < b / c ↔ a * c < b`.
  -- Here `a = 2`, `b = 3`, `c = Real.sqrt 2`.
  rw [lt_div_iff h_sqrt2_pos]
  -- Goal: (2 : ℝ) * Real.sqrt (2 : ℝ) < (3 : ℝ)

  -- Since both sides are positive, this is equivalent to squaring both sides.
  have h_lhs_pos : 0 < (2 : ℝ) * Real.sqrt (2 : ℝ) := by positivity
  have h_rhs_pos : 0 < (3 : ℝ) := by norm_num
  -- Use `mul_self_lt_mul_self_iff`: `a < b ↔ a * a < b * b` for `0 ≤ a, b`.
  -- We have `a = (2 : ℝ) * Real.sqrt (2 : ℝ)` and `b = (3 : ℝ)`.
  -- We want to replace the goal `a < b` with `a*a < b*b`.
  -- The theorem is `(a < b) ↔ (a*a < b*b)`.
  -- We use `exact (mul_self_lt_mul_self_iff h_lhs_pos.le h_rhs_pos.le).mp this` or `rw` with the iff.
  rw [mul_self_lt_mul_self_iff h_lhs_pos.le h_rhs_pos.le]
  -- Goal: ((2 : ℝ) * Real.sqrt (2 : ℝ)) * ((2 : ℝ) * Real.sqrt (2 : ℝ)) < (3 : ℝ) * (3 : ℝ)

  -- Calculate the squares and simplify the inequality.
  -- The target is `(2*√2)*(2*√2) < 3*3`.
  -- Simplify LHS: (2*√2)*(2*√2) = (2*2)*(√2*√2) = 4 * 2 = 8.
  -- Simplify RHS: 3*3 = 9.
  -- Goal: (8 : ℝ) < (9 : ℝ).
  -- Use a sequence of rw and arithmetic laws to simplify the LHS expression step-by-step.
  -- -- The previous sequence of `rw` tactics was incorrect.
  -- -- We use `mul_mul_mul_comm` to rearrange the terms (a*b)*(c*d) = (a*c)*(b*d).
  rw [mul_mul_mul_comm]
  -- Goal: (2 : ℝ) * (2 : ℝ) * (√(2 : ℝ) * √(2 : ℝ)) < (3 : ℝ) * (3 : ℝ)
  -- The `norm_num` tactic simplifies the numerical parts including `sqrt 2 * sqrt 2` and the multiplication/comparison.
  norm_num
  -- -- The previous line `rw [Real.mul_self_sqrt (by norm_num)]` is redundant because `norm_num` already simplified `sqrt 2 * sqrt 2`.
  -- -- The message "no goals to be solved" appears here because the goal was already closed by the preceding `norm_num`.
  -- -- Remove the redundant tactic and the following comment/tactic.


-- Step 6: Combine the results.
-- We have ∑ k in Finset.Icc a b, f (↑k : ℝ) ≤ 200 - 3 / Real.sqrt 2 (from Step 4).
-- We have 200 - 3 / Real.sqrt 2 < 198 (from Step 5).
-- By transitivity of <, the sum is less than 198.
exact lt_of_le_of_lt h_sum_le_final h_upper_bound_lt_198


#print axioms algebra_sum1onsqrt2to1onsqrt10000lt198