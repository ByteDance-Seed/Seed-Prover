import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem amc12_2001_p21
  (a b c d : ℕ)
  (h₀ : a * b * c * d = Nat.factorial 8)
  (h₁ : a * b + a + b = 524)
  (h₂ : b * c + b + c = 146)
  (h₃ : c * d + c + d = 104) :
  ↑a - ↑d = (10 : ℤ) := by 

  -- The given equations involve terms like `xy + x + y`.
  -- We rewrite `xy + x + y` as `(x+1)(y+1) - 1`.
  -- This identity is `x*y + x + y + 1 - 1 = (x+1)(y+1) - 1`.
  -- We apply this transformation to h₁, h₂, h₃.
  -- We need to prove `(x+1)(y+1) = xy + x + y + 1`.
  -- First prove `(x+1)(y+1) = xy + x + y + 1` using `ring`.
  -- Then use `Nat.add_one_sub_one` for `(Z + 1) - 1 = Z`.

  have h₁' : (a + 1) * (b + 1) - 1 = 524 := by
    -- Prove the identity (a+1)(b+1) = ab + a + b + 1
    have identity_add_one : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
    -- Rewrite the goal using the identity
    -- -- The previous tactic `rw [identity_add_one]` had a typo in the lemma name.
    -- -- The previous tactic `rw [Nat.add_sub_cancel (a * b + a + b)]` used the wrong theorem and arguments.
    -- -- We use Nat.add_one_sub_one (n + 1 - 1 = n).
    rw [identity_add_one, Nat.add_one_sub_one (a * b + a + b)]
    -- The goal is now `a*b + a + b = 524`, which is h₁.
    exact h₁

  have h₂' : (b + 1) * (c + 1) - 1 = 146 := by
    -- Prove the identity (b+1)(c+1) = bc + b + c + 1
    have identity_add_one : (b + 1) * (c + 1) = b * c + b + c + 1 := by ring
    -- Rewrite the goal using the identity
    -- -- The previous tactic `rw [identity_add_add_one]` had a typo in the lemma name.
    -- The previous tactic `rw [Nat.add_sub_cancel (b * c + b + c)]` used the wrong theorem and arguments.
    rw [identity_add_one, Nat.add_one_sub_one (b * c + b + c)]
    -- The goal is now `b*c + b + c = 146`, which is h₂.
    exact h₂

  have h₃' : (c + 1) * (d + 1) - 1 = 104 := by
    -- Prove the identity (c+1)(d+1) = cd + c + d + 1
    have identity_add_one : (c + 1) * (d + 1) = c * d + c + d + 1 := by ring
    -- Rewrite the goal using the identity
    -- The previous tactic `rw [Nat.add_sub_cancel (c * d + c + d)]` used the wrong theorem and arguments.
    rw [identity_add_one, Nat.add_one_sub_one (c * d + c + d)]
    -- The goal is now `c*d + c + d = 104`, which is h₃.
    exact h₃

  -- Add 1 to both sides of the rewritten equations to isolate the product terms.
  -- We use `Nat.sub_add_cancel (N - 1) + 1 = N` if `1 <= N`.
  have h₁'' : (a + 1) * (b + 1) = 525 := by
    -- Start with h₁'
    have h_add_one_sides : ((a + 1) * (b + 1) - 1) + 1 = 524 + 1 := by rw [h₁']
    -- Simplify the right side
    rw [show 524 + 1 = 525 by norm_num] at h_add_one_sides
    -- The term (a+1)*(b+1) is the product of two natural numbers >= 1, so it is >= 1.
    -- Use Nat.le_add_left to show 1 <= a+1 and 1 <= b+1, then Left.one_le_mul.
    have one_le_aplus1 : 1 ≤ a + 1 := Nat.le_add_left 1 a
    have one_le_bplus1 : 1 ≤ b + 1 := Nat.le_add_left 1 b
    -- The theorem `Left.one_le_mul` proves `1 ≤ x * y` from `1 ≤ x` and `1 ≤ y`.
    have prod_ge_one : 1 ≤ (a + 1) * (b + 1) := Left.one_le_mul one_le_aplus1 one_le_bplus1
    -- Use Nat.sub_add_cancel to simplify the left side: ((a+1)*(b+1) - 1) + 1 = (a+1)*(b+1)
    rw [Nat.sub_add_cancel prod_ge_one] at h_add_one_sides
    -- The goal is now `(a + 1) * (b + 1) = 525`, which is exactly `h_add_one_sides`.
    exact h_add_one_sides

  have h₂'' : (b + 1) * (c + 1) = 147 := by
    -- Start with h₂'
    have h_add_one_sides : ((b + 1) * (c + 1) - 1) + 1 = 146 + 1 := by rw [h₂']
    -- Simplify the right side
    rw [show 146 + 1 = 147 by norm_num] at h_add_one_sides
    -- The term (b+1)*(c+1) is the product of two natural numbers >= 1, so it is >= 1.
    -- Use Nat.le_add_left to show 1 <= b+1 and 1 <= c+1, then Left.one_le_mul.
    have one_le_bplus1 : 1 ≤ b + 1 := Nat.le_add_left 1 b
    have one_le_cplus1 : 1 ≤ c + 1 := Nat.le_add_left 1 c
    -- The theorem `Left.one_le_mul` proves `1 ≤ x * y` from `1 ≤ x` and `1 ≤ y`.
    have prod_ge_one : 1 ≤ (b + 1) * (c + 1) := Left.one_le_mul one_le_bplus1 one_le_cplus1
    -- Use Nat.sub_add_cancel to simplify the left side
    rw [Nat.sub_add_cancel prod_ge_one] at h_add_one_sides
    -- The goal is now `(b + 1) * (c + 1) = 147`, which is exactly `h_add_one_sides`.
    exact h_add_one_sides

  have h₃'' : (c + 1) * (d + 1) = 105 := by
    -- Start with h₃'
    have h_add_one_sides : ((c + 1) * (d + 1) - 1) + 1 = 104 + 1 := by rw [h₃']
    -- Simplify the right side
    rw [show 104 + 1 = 105 by norm_num] at h_add_one_sides
    -- The term (c+1)*(d+1) is the product of two natural numbers >= 1, so it is >= 1.
    -- Use Nat.le_add_left to show 1 <= c+1 and 1 <= d+1, then Left.one_le_mul.
    have one_le_cplus1 : 1 ≤ c + 1 := Nat.le_add_left 1 c
    have one_le_dplus1 : 1 ≤ d + 1 := Nat.le_add_left 1 d
    -- The theorem `Left.one_le_mul` proves `1 ≤ x * y` from `1 ≤ x` and `1 ≤ y`.
    have prod_ge_one : 1 ≤ (c + 1) * (d + 1) := Left.one_le_mul one_le_cplus1 one_le_dplus1
    -- Use Nat.sub_add_cancel to simplify the left side
    rw [Nat.sub_add_cancel prod_ge_one] at h_add_one_sides
    -- The goal is now `(c + 1) * (d + 1) = 105`, which is exactly `h_add_one_sides`.
    exact h_add_one_sides

  -- Let A = a+1, B = b+1, C = c+1, D = d+1. These are positive natural numbers.
  -- Using `let` instead of `have` for A, B, C, D makes them definitionally equal.
  let A : ℕ := a + 1
  let B : ℕ := b + 1
  let C : ℕ := c + 1
  let D : ℕ := d + 1

  -- A, B, C, D are positive since a,b,c,d are natural numbers (>= 0).
  -- The proof Nat.succ_pos n gives 0 < succ n.
  -- Since A = succ a, we need to prove 0 < A.
  -- With `let`, A is definitionally `a + 1`.
  have A_pos : A > 0 := Nat.succ_pos a
  have B_pos : B > 0 := Nat.succ_pos b
  have C_pos : C > 0 := Nat.succ_pos c
  have D_pos : D > 0 := Nat.succ_pos d

  -- Substitute A, B, C, D into the equations.
  -- With `let`, A and B are definitionally `a+1` and `b+1`.
  have h_AB : A * B = 525 := by
    -- The goal is `(a + 1) * (b + 1) = 525`.
    exact h₁''

  have h_BC : B * C = 147 := by
    -- The goal is `(b + 1) * (c + 1) = 147`.
    exact h₂''

  have h_CD : C * D = 105 := by
    -- The goal is `(c + 1) * (d + 1) = 105`.
    exact h₃''

  -- From h_AB and h_BC, B must be a common divisor of 525 and 147.
  -- A * B = 525 implies B | 525 if A > 0 (which A_pos provides).
  -- We use the definition of divisibility (∃ k, m = n * k).
  -- We need A > 0 to ensure the existence of A = 525 / B.
  -- Since A is definitionally a+1, and A_pos proves a+1 > 0, A != 0.
  have A_ne_zero : A ≠ 0 := Nat.pos_iff_ne_zero.mp A_pos
  have B_dvd_525 : B ∣ 525 := by
    -- We have A * B = 525 and A > 0. We need to show there exists k such that 525 = B * k.
    -- Since A * B = 525, we can let k = A.
    exists A
    -- The goal is 525 = B * A. We have h_AB : A * B = 525.
    -- We need to prove 525 = B * A.
    -- We know 525 = A * B (from Eq.symm h_AB)
    -- And we know A * B = B * A (from Nat.mul_comm).
    -- By transitivity, 525 = B * A.
    -- Use Eq.trans to compose the symmetry and the commutativity to prove the goal 525 = B * A.
    exact Eq.trans (Eq.symm h_AB) (Nat.mul_comm A B)

  -- B * C = 147 implies B | 147 if C > 0 (which C_pos provides).
  -- We need C > 0 to ensure the existence of C = 147 / B.
  -- Since C is definitionally c+1, and C_pos proves c+1 > 0, C != 0.
  have C_ne_zero : C ≠ 0 := Nat.pos_iff_ne_zero.mp C_pos
  have B_dvd_147 : B ∣ 147 := by
    -- We have B * C = 147 and C > 0. We need to show there exists k such that 147 = B * k.
    -- Since B * C = 147, we can let k = C.
    exists C
    -- The goal is 147 = B * C. We have h_BC : B * C = 147.
    -- We need to prove 147 = B * C.
    -- The symmetry of h_BC, Eq.symm h_BC, directly proves this.
    exact Eq.symm h_BC

  -- B divides both 525 and 147, so B divides their greatest common divisor.
  have B_dvd_gcd : B ∣ Nat.gcd 525 147 := Nat.dvd_gcd B_dvd_525 B_dvd_147

  -- Calculate the gcd of 525 and 147.
  have gcd_val : Nat.gcd 525 147 = 21 := by norm_num

  -- Substitute the gcd value into the divisibility statement.
  have B_dvd_21 : B ∣ 21 := by rw [gcd_val] at B_dvd_gcd; exact B_dvd_gcd

  -- From B * C = 147 and B > 0, we can deduce C = 147 / B.
  -- Nat.eq_div_of_mul_eq_left requires the divisor (B) to be non-zero. B_pos gives B > 0, which implies B ≠ 0.
  -- Since B is definitionally b+1, and B_pos proves b+1 > 0, B != 0.
  have B_ne_zero : B ≠ 0 := Nat.pos_iff_ne_zero.mp B_pos
  -- We have the equation B * C = 147. To get C = 147 / B, we need to use the theorem for multiplication on the right side.
  have C_eq_div : C = 147 / B := Nat.eq_div_of_mul_eq_right B_ne_zero h_BC

  -- Substitute C = 147 / B into the equation h_CD: C * D = 105.
  have h_div_mul_D : (147 / B) * D = 105 := by
    rw [C_eq_div] at h_CD
    exact h_CD

  -- Multiply h_div_mul_D by B on both sides. This is valid since B > 0 (B_ne_zero).
  -- The previous tactic `by exact Eq.mul_right h_div_mul_D B` failed with "invalid field notation".
  -- We prove the equality by rewriting one side using the hypothesis h_div_mul_D.
  have h_mult_B : ((147 / B) * D) * B = 105 * B := by
    rw [h_div_mul_D]
    -- The goal became 105 * B = 105 * B, which is definitionally true and solved automatically.
    -- -- rfl is sufficient here -- The goal was definitionally equal after the rewrite, so rfl is not needed.

  -- Rearrange the left side ((147 / B) * D) * B and apply Nat.div_mul_cancel.
  -- ((147 / B) * D) * B = (147 / B) * (D * B)  (associativity)
  --                     = (147 / B) * (B * D)  (commutativity)
  --                     = (147 / B * B) * D  (associativity)
  --                     = 147 * D (since B | 147, using Nat.div_mul_cancel)
  rw [Nat.mul_assoc (147 / B) D B, Nat.mul_comm D B, ← Nat.mul_assoc (147 / B) B D] at h_mult_B
  -- We need to show that B divides 147 for `Nat.div_mul_cancel (147 / B) B` to simplify to 147.
  -- We have B_dvd_147.
  rw [Nat.div_mul_cancel B_dvd_147] at h_mult_B

  -- Now h_mult_B is: 147 * D = 105 * B.
  -- Rename this hypothesis for clarity as in the original proof structure.
  have h_147D_eq_105B : 147 * D = 105 * B := h_mult_B

  -- Simplify the equation 147 * D = 105 * B by dividing by gcd(147, 105) = 21.
  -- 147 = 21 * 7, 105 = 21 * 5.
  -- (21 * 7) * D = (21 * 5) * B
  -- 21 * (7 * D) = 21 * (5 * B)
  -- Since 21 > 0, we can cancel 21 using Nat.mul_eq_mul_right_cancel_of_pos.
  have h_7D_eq_5B : 7 * D = 5 * B := by
    -- Start with the equation 147 * D = 105 * B
    rw [show 147 = 21 * 7 by norm_num, show 105 = 21 * 5 by norm_num] at h_147D_eq_105B
    -- The hypothesis h_147D_eq_105B is now (21 * 7) * D = (21 * 5) * B
    -- Rearrange using associativity
    rw [Nat.mul_assoc 21 7 D, Nat.mul_assoc 21 5 B] at h_147D_eq_105B
    -- The equation is now 21 * (7 * D) = 21 * (5 * B)
    -- We need to provide the equality for cancellation.
    have h_cancel_form : 21 * (7 * D) = 21 * (5 * B) := h_147D_eq_105B
    -- Apply the cancellation theorem since 21 > 0
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 21 > 0) h_cancel_form

  -- From 7 * D = 5 * B, since 7 and 5 are coprime, 7 must divide B (by Euclid's Lemma).
  -- Need to prove Nat.coprime 7 5. norm_num cannot directly prove this by itself,
  -- but it works after unfolding the definition of coprime using simp.
  -- We prove `Nat.Coprime 7 5`.
  -- Use the theorem Nat.coprime_iff_gcd_eq_one.mpr which proves Coprime from gcd = 1.
  have seven_coprime_five : Nat.Coprime 7 5 := Nat.coprime_iff_gcd_eq_one.mpr (by norm_num) -- Proof: Nat.gcd 7 5 = 1 is proven by norm_num.
  -- 7 * D = 5 * B implies 7 | 5 * B.
  have seven_dvd_5B : 7 ∣ 5 * B := Exists.intro D (Eq.symm h_7D_eq_5B)
  -- Since 7 and 5 are coprime and 7 | 5 * B, by Nat.coprime.dvd_mul_left, 7 | B.
  -- Now use Nat.Coprime.dvd_mul_left with 7 coprime 5.
  -- 7 | 5 * B and 7.coprime 5 implies 7 | B.
  -- We use the forward implication (.mp) of the equivalence provided by Nat.Coprime.dvd_mul_left.
  have seven_dvd_B : 7 ∣ B := (Nat.Coprime.dvd_mul_left seven_coprime_five).mp seven_dvd_5B

  -- We know B | 21 (B_dvd_21) and 7 | B (seven_dvd_B).
  -- Since B is positive (B_pos), B must be a divisor of 21 that is also a multiple of 7.
  -- The positive divisors of 21 are 1, 3, 7, 21.
  -- The positive multiples of 7 are 7, 14, 21, 28, ...
  -- The common values are 7 and 21.
  -- So B must be 7 or 21.
  have B_is_7_or_21 : B = 7 ∨ B = 21 := by
    -- Since 7 | B (seven_dvd_B), B = 7 * j for some j.
    rcases seven_dvd_B with ⟨j, hj⟩ -- hj : B = 7 * j
    -- Since B | 21 (B_dvd_21), 21 = B * k for some k.
    rcases B_dvd_21 with ⟨k, hk⟩ -- hk : 21 = B * k
    -- Substitute B = 7 * j into 21 = B * k: 21 = (7 * j) * k.
    rw [hj] at hk
    -- By associativity, 7 * (j * k) = 21.
    rw [Nat.mul_assoc 7 j k] at hk
    -- We have 7 * (j * k) = 21 and we know 7 * 3 = 21.
    -- Since 7 > 0, we can conclude j * k = 3 by cancelling 7 from 7 * (j * k) = 7 * 3.
    have jk_eq_3 : j * k = 3 := by
      -- Construct the equality 7 * (j * k) = 7 * 3
      have h_cancel_form : 7 * (j * k) = 7 * 3 := by
        -- From hk, we have 7 * (j * k) = 21 (by symmetry)
        -- We also know 21 = 7 * 3 (by norm_num)
        -- By transitivity, 7 * (j * k) = 7 * 3
        exact Eq.trans (Eq.symm hk) (by norm_num : 21 = 7 * 3)
      -- Apply the cancellation theorem since 7 > 0
      apply Nat.eq_of_mul_eq_mul_left (by norm_num : 7 > 0) h_cancel_form

    -- Since B > 0 (B_pos) and B = 7 * j (hj), and 7 > 0, j must be > 0.
    -- We prove j > 0 by cases on j.
    have j_pos : j > 0 := by
      -- The goal is j > 0.
      cases j
      . -- Case j = 0
        -- The goal is 0 > 0, which is false.
        -- Substitute j = 0 into hj: B = 7 * 0 = 0.
        rw [mul_zero] at hj -- hj is now B = 0
        -- Substitute hj into B_pos: B > 0 becomes 0 > 0, which is False.
        rw [hj] at B_pos
        -- We have B_pos : 0 > 0, which is a contradiction.
        -- Use contradiction to solve the goal.
        -- -- The previous tactic `simp at B_pos` removed the B_pos hypothesis.
        -- -- The previous comment "The goal is automatically solved..." was based on the false B_pos.
        contradiction -- Explicitly prove from contradiction.
      . -- Case j = Nat.succ k
        -- The goal is Nat.succ k > 0. This is true by definition.
        apply Nat.succ_pos

    -- Since j > 0 (j_pos) and j * k = 3 (jk_eq_3), k must be > 0.
    -- We prove k > 0 by cases on k.
    have k_pos : k > 0 := by
      -- The goal is k > 0.
      cases k
      . -- Case k = 0
        -- The goal is 0 > 0, which is false.
        -- Substitute k = 0 into jk_eq_3: j * 0 = 3.
        rw [mul_zero] at jk_eq_3 -- jk_eq_3 is now 0 = 3.
        -- We have jk_eq_3 : 0 = 3 in the context, which is a contradiction.
        -- The goal is 0 > 0.
        -- Use contradiction to solve the goal from the contradictory hypothesis.
        -- The error message "no goals to be solved" here might indicate that `jk_eq_3 : 0 = 3` already made the goal provable by contradiction implicitly. However, explicitly using `contradiction` is clearer.
        contradiction -- Add contradiction tactic here.
      . -- Case k = Nat.succ m
        -- The goal is Nat.succ m > 0. This is true by definition.
        apply Nat.succ_pos


    -- j and k are positive natural numbers and j * k = 3.
    -- The positive natural number divisors of 3 are 1 and 3.
    -- Since j | 3 (from j * k = 3), j must be 1 or 3.
    -- We know `j ∣ 3` (j_dvd_3).
    have j_dvd_3 : j ∣ 3 := dvd_of_mul_right_eq k jk_eq_3
    -- We also know `j ≠ 0` from `j_pos` (since j > 0).
    have j_ne_zero : j ≠ 0 := Nat.ne_of_gt j_pos
    -- A positive divisor of 3 must be in the set of divisors of 3.
    -- We want to prove j ∈ Nat.divisors 3.
    have j_in_divisors : j ∈ Nat.divisors 3 := by
      -- The theorem `Nat.mem_divisors` states that `d ∈ n.divisors ↔ d ∣ n ∧ n ≠ 0`.
      -- We apply the reverse direction (`.mpr`) of this equivalence to the goal `j ∈ Nat.divisors 3`.
      -- This changes the goal to the premise of the implication, which is `j ∣ 3 ∧ 3 ≠ 0`.
      apply (Nat.mem_divisors).mpr
      -- The goal is now `j ∣ 3 ∧ 3 ≠ 0`.
      -- We split the goal into two using `constructor`.
      constructor
      -- The first subgoal is `j ∣ 3`. We have this as hypothesis `j_dvd_3`.
      exact j_dvd_3
      -- The second subgoal is `3 ≠ 0`. We can prove this with `norm_num`.
      norm_num

    -- The set of divisors of 3 is {1, 3}.
    -- We use the theorem `Nat.Prime.divisors` which states that the divisors of a prime number `p` are `{1, p}`.
    -- First, we prove that 3 is a prime number.
    have three_is_prime : Nat.Prime 3 := by norm_num -- `norm_num` can prove primality for small numbers.
    -- Now, apply `Nat.Prime.divisors` with `p = 3` and the primality proof.
    have divisors_3_eq : Nat.divisors 3 = {1, 3} := Nat.Prime.divisors three_is_prime
    -- Substitute the value of Nat.divisors 3 into the set membership.
    rw [divisors_3_eq] at j_in_divisors
    -- j_in_divisors is now `j ∈ {(1 : ℕ), (3 : ℕ)}`.
    -- We rewrite this membership statement into a disjunction using Finset theorems.
    -- j ∈ {1, 3} is definitionally j ∈ insert 1 {3}.
    -- Apply Finset.mem_insert to convert set membership to disjunction
    -- Apply Finset.mem_singleton to convert singleton set membership to equality
    simp [Finset.mem_insert, Finset.mem_singleton] at j_in_divisors
    -- j_in_divisors is now `j = 1 ∨ j = 3`.
    -- The hypothesis `j_in_divisors` now has the desired disjunction type.
    -- Case analysis on the possible values of j.
    cases j_in_divisors with -- Use the rewritten hypothesis
    | inl h_j_1 => -- Case 1: j = 1
      -- Substitute j = 1 into B = 7 * j.
      left -- Prove B = 7
      -- Apply hj to rewrite B as 7 * j in the goal. Goal becomes `7 * j = 7`.
      -- Apply h_j_1 to rewrite j as 1 in the goal. Goal becomes `7 * 1 = 7`.
      rw [hj, h_j_1]
      -- The goal is now `7 * 1 = 7`, which is definitionally true.
      -- -- The previous tactic `norm_num` was redundant.
    | inr h_j_3 => -- Case 2: j = 3
      -- Substitute j = 3 into B = 7 * j.
      right -- Prove B = 21
      -- Apply hj to rewrite B as 7 * j in the goal. Goal becomes `7 * j = 21`.
      -- Apply h_j_3 to rewrite j as 3 in the goal. Goal becomes `7 * 3 = 21`.
      rw [hj, h_j_3]
      -- The goal is now `7 * 3 = 21`, which is definitionally true.
      -- -- The previous tactic `norm_num` was redundant.

  -- Now we split the main goal into two subgoals based on the possible values of B.
  -- The "unsolved goals" message indicates that the proof is currently at this state,
  -- with the main goal `↑a - ↑d = (10 : ℤ)` pending, and the hypothesis `B_is_7_or_21 : B = 7 ∨ B = 21` available.
  -- The tactic `apply Or.elim B_is_7_or_21` is used to perform case analysis on this disjunction.
  -- It will generate two subgoals: one assuming B = 7, and one assuming B = 21.
  apply Or.elim B_is_7_or_21

  -- Subgoal 1: Assume B = 7.
  . -- Add explicit . to structure the cases from Or.elim
    intro hB7
    -- Calculate A, C, D, a, d based on B = 7.
    have B_7_pos : (7 : ℕ) > 0 := by norm_num
    have B_7_ne_zero : (7 : ℕ) ≠ (0 : ℕ) := Nat.pos_iff_ne_zero.mp B_7_pos

    -- A * B = 525, so A * 7 = 525. A = 525 / 7 = 75.
    rw [hB7] at h_AB -- h_AB is now A * 7 = 525
    have A_val : A = 75 := by exact Nat.eq_div_of_mul_eq_left B_7_ne_zero h_AB

    -- B * C = 147, so 7 * C = 147. C = 147 / 7 = 21.
    rw [hB7] at h_BC -- h_BC is now 7 * C = 147
    have C_val : C = 21 := by exact Nat.eq_div_of_mul_eq_right B_7_ne_zero h_BC

    -- C * D = 105, so 21 * D = 105. D = 105 / 21 = 5.
    -- We have C_val : C = 21.
    rw [C_val] at h_CD -- h_CD is now 21 * D = 105
    have C_21_pos : (21 : ℕ) > 0 := by norm_num
    have C_21_ne_zero : (21 : ℕ) ≠ (0 : ℕ) := Nat.pos_iff_ne_zero.mp C_21_pos
    have D_val : D = 5 := by exact Nat.eq_div_of_mul_eq_right C_21_ne_zero h_CD

    -- A = a + 1, so 75 = a + 1. a = 74.
    have a_plus_one_eq_75 : a + 1 = 75 := A_val
    have a_val : a = 74 := by
      -- Goal: a = 74
      -- Have: a + 1 = 75
      -- Rewrite 74 as 75 - 1 using norm_num.
      rw [show 74 = 75 - 1 by norm_num]
      -- Goal: a = 75 - 1
      -- Rewrite 75 as a + 1 using the hypothesis a_plus_one_eq_75.
      rw [← a_plus_one_eq_75]
      -- Goal: a = (a + 1) - 1
      -- Use Nat.add_one_sub_one to simplify (a + 1) - 1 to a.
      -- Removed the redundant hypothesis `have one_le_aplus1 : 1 ≤ a + 1 := Nat.le_add_left 1 a`.
      rw [Nat.add_one_sub_one a]
      -- Goal: a = a (solved by rfl implicitly)

    -- D = d + 1, so 5 = d + 1. d = 4.
    have d_plus_one_eq_5 : d + 1 = 5 := D_val
    have d_val : d = 4 := by
      -- Goal: d = 4
      -- Have: d + 1 = 5
      -- Rewrite 4 as 5 - 1 using norm_num.
      rw [show 4 = 5 - 1 by norm_num]
      -- Goal: d = 5 - 1
      -- Rewrite 5 as d + 1 using the hypothesis d_plus_one_eq_5.
      rw [← d_plus_one_eq_5]
      -- Goal: d = (d + 1) - 1
      -- Use Nat.add_one_sub_one to simplify (d + 1) - 1 to d.
      -- Removed the redundant hypothesis `have one_le_dplus1 : 1 ≤ d + 1 := Nat.le_add_left 1 d`.
      rw [Nat.add_one_sub_one d]
      -- Goal: d = d (solved by rfl implicitly)

    -- B = b + 1, so 7 = b + 1. b = 6.
    have b_plus_one_eq_7 : b + 1 = 7 := hB7
    have b_val : b = 6 := by
      -- Goal: b = 6
      -- Have: b + 1 = 7
      -- Rewrite 6 as 7 - 1 using norm_num.
      rw [show 6 = 7 - 1 by norm_num]
      -- Goal: b = 7 - 1
      -- Rewrite 7 as b + 1 using the hypothesis b_plus_one_eq_7.
      rw [← b_plus_one_eq_7]
      -- Goal: b = (b + 1) - 1
      -- Use Nat.add_one_sub_one to simplify (b + 1) - 1 to b.
      -- Removed the redundant hypothesis `have one_le_bplus1 : 1 ≤ b + 1 := Nat.le_add_left 1 b`.
      rw [Nat.add_one_sub_one b]
      -- Goal: b = b (solved by rfl implicitly)

    -- C = c + 1, so 21 = c + 1. c = 20.
    have c_plus_one_eq_21 : c + 1 = 21 := C_val
    have c_val : c = 20 := by
      -- Goal: c = 20
      -- Have: c + 1 = 21
      -- Rewrite 20 as 21 - 1 using norm_num.
      rw [show 20 = 21 - 1 by norm_num]
      -- Goal: c = 21 - 1
      -- Rewrite 21 as c + 1 using the hypothesis c_plus_one_eq_21.
      rw [← c_plus_one_eq_21]
      -- Goal: c = (c + 1) - 1
      -- Use Nat.add_one_sub_one to simplify (c + 1) - 1 to c.
      -- Removed the redundant hypothesis `have one_le_cplus1 : 1 ≤ c + 1 := Nat.le_add_one_sub_one c`.
      rw [Nat.add_one_sub_one c]
      -- Goal: c = c (solved by rfl implicitly)

    -- Check if the product a * b * c * d matches 8!.
    -- h₀ : a * b * c * d = Nat.factorial 8
    -- Substitute the calculated values of a, b, c, d into h₀.
    rw [a_val, b_val, c_val, d_val] at h₀
    -- The hypothesis h₀ is now `74 * 6 * 20 * 4 = Nat.factorial 8`.

    -- Evaluate Nat.factorial 8
    -- The previous proof `simp [Nat.factorial]; norm_num` worked,
    -- but the `norm_num` step was reported with "no goals to be solved".
    -- Replacing with `decide` to prove this concrete numerical equality.
    have factorial8_val : Nat.factorial 8 = 40320 := by decide
    -- Substitute the factorial value into h₀
    rw [factorial8_val] at h₀
    -- h₀ is now `74 * 6 * 20 * 4 = 40320`.
    -- Evaluate the multiplication on the left side using simp, as simp can handle this numerical product.
    simp at h₀ -- Simplify the product to 35520. h₀ is now `35520 = 40320`.
    -- The hypothesis h₀ is now `False` because 35520 and 40320 are different.
    -- The goal is implicitly solved by the presence of the contradictory hypothesis h₀.
    -- As simp at h₀ results in h₀ : False, the goal is already closed by contradiction.
    -- Any further tactic like norm_num or contradiction would be redundant.
    -- -- The previous tactic `norm_num at h₀` was redundant as the goal was already closed.
    -- -- The error message "no goals to be solved" pointed to the redundant tactic here.
    -- The goal is closed by the contradiction `h₀ : False`.
    -- We remove the redundant tactic `norm_num at h₀`.


  -- Subgoal 2: Assume B = 21.
  . -- Add explicit . to structure the cases from Or.elim
    intro hB21
    -- Calculate A, C, D, a, d based on B = 21.
    have B_21_pos : (21 : ℕ) > 0 := by norm_num
    have B_21_ne_zero : (21 : ℕ) ≠ (0 : ℕ) := Nat.pos_iff_ne_zero.mp B_21_pos

    -- A * B = 525, so A * 21 = 525. A = 525 / 21 = 25.
    rw [hB21] at h_AB -- h_AB is now A * 21 = 525
    have A_val : A = 25 := by exact Nat.eq_div_of_mul_eq_left B_21_ne_zero h_AB

    -- B * C = 147, so 21 * C = 147. C = 147 / 21 = 7.
    rw [hB21] at h_BC -- h_BC is now 21 * C = 147
    have C_val : C = 7 := by
      exact Nat.eq_div_of_mul_eq_right B_21_ne_zero h_BC

    -- C * D = 105, so 7 * D = 105. D = 105 / 7 = 15.
    -- We have C_val : C = 7.
    rw [C_val] at h_CD -- h_CD is now 7 * D = 105
    have C_7_pos : (7 : ℕ) > 0 := by norm_num
    have C_7_ne_zero : (7 : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp C_7_pos
    have D_val : D = 15 := by exact Nat.eq_div_of_mul_eq_right C_7_ne_zero h_CD

    -- A = a + 1, so 25 = a + 1. a = 24.
    have a_plus_one_eq_25 : a + 1 = 25 := A_val
    have a_val : a = 24 := by
      -- Goal: a = 24
      -- Have: a + 1 = 25
      -- Rewrite 24 as 25 - 1 using norm_num.
      rw [show 24 = 25 - 1 by norm_num]
      -- Goal: a = 25 - 1
      -- Rewrite 25 as a + 1 using the hypothesis a_plus_one_eq_25.
      rw [← a_plus_one_eq_25]
      -- Goal: a = (a + 1) - 1
      -- Use Nat.add_one_sub_one to simplify (a + 1) - 1 to a.
      -- Removed the redundant hypothesis `have one_le_aplus1 : 1 ≤ a + 1 := Nat.le_add_left 1 a`.
      rw [Nat.add_one_sub_one a]
      -- Goal: a = a (solved by rfl implicitly)

    -- D = d + 1, so 15 = d + 1. d = 14.
    have d_plus_one_eq_15 : d + 1 = 15 := D_val
    have d_val : d = 14 := by
      -- Goal: d = 14
      -- Have: d + 1 = 15
      -- Rewrite 14 as 15 - 1 using norm_num.
      rw [show 14 = 15 - 1 by norm_num]
      -- Goal: d = 15 - 1
      -- Rewrite 15 as d + 1 using the hypothesis d_plus_one_eq_15.
      rw [← d_plus_one_eq_15]
      -- Goal: d = (d + 1) - 1
      -- Use Nat.add_one_sub_one to simplify (d + 1) - 1 to d.
      -- Removed the redundant hypothesis `have one_le_dplus1 : 1 ≤ d + 1 := Nat.le_add_left 1 d`.
      rw [Nat.add_one_sub_one d]
      -- Goal: d = d (solved by rfl implicitly)

    -- B = b + 1, so 21 = b + 1. b = 20.
    have b_plus_one_eq_21 : b + 1 = 21 := hB21
    have b_val : b = 20 := by
      -- Goal: b = 20
      -- Have: b + 1 = 21
      -- Rewrite 20 as 21 - 1 using norm_num.
      rw [show 20 = 21 - 1 by norm_num]
      -- Goal: b = 21 - 1
      -- Rewrite 21 as b + 1 using the hypothesis b_plus_one_eq_21.
      rw [← b_plus_one_eq_21]
      -- Goal: b = (b + 1) - 1
      -- Use Nat.add_one_sub_one to simplify (b + 1) - 1 to b.
      -- Removed the redundant hypothesis `have one_le_bplus1 : 1 ≤ b + 1 := Nat.le_add_left 1 b`.
      rw [Nat.add_one_sub_one b]
      -- Goal: b = b (solved by rfl implicitly)

    -- C = c + 1, so 7 = c + 1. c = 6.
    have c_plus_one_eq_7 : c + 1 = 7 := C_val
    have c_val : c = 6 := by
      -- Goal: c = 6
      -- Have: c + 1 = 7
      -- Rewrite 6 as 7 - 1 using norm_num.
      rw [show 6 = 7 - 1 by norm_num]
      -- Goal: c = 7 - 1
      -- Rewrite 7 as c + 1 using the hypothesis c_plus_one_eq_7.
      rw [← c_plus_one_eq_7]
      -- Goal: c = (c + 1) - 1
      -- Use Nat.add_one_sub_one to simplify (c + 1) - 1 to c.
      -- Removed the redundant hypothesis `have one_le_cplus1 : 1 ≤ c + 1 := Nat.le_add_one_sub_one c`.
      rw [Nat.add_one_sub_one c]
      -- Goal: c = c (solved by rfl implicitly)

    -- Check if the product a * b * c * d matches 8!.
    -- h₀ : a * b * c * d = Nat.factorial 8
    -- Substitute the calculated values of a, b, c, d into h₀.
    rw [a_val, b_val, c_val, d_val] at h₀
    -- The hypothesis h₀ is now `24 * 20 * 6 * 14 = Nat.factorial 8`.

    -- Evaluate Nat.factorial 8
    -- The previous proof `simp [Nat.factorial]; norm_num` worked,
    -- but the `norm_num` step was reported with "no goals to be solved".
    -- Replacing with `decide` to prove this concrete numerical equality.
    have factorial8_val : Nat.factorial 8 = 40320 := by decide
    -- Substitute the factorial value into h₀
    rw [factorial8_val] at h₀
    -- h₀ is now `24 * 20 * 6 * 14 = 40320`.
    -- Evaluate the multiplication on the left side using simp, as simp can handle this numerical product.
    simp at h₀ -- Simplify the product to 40320
    -- h₀ is now `40320 = 40320`, which is true.
    -- -- The message "no goals to be solved" also pointed to a redundant tactic here.
    -- -- As simp at h₀ results in a definitionally true equality, any further tactic like norm_num is redundant.
    -- -- We remove the redundant tactic `norm_num`.

    -- The goal is ↑a - ↑d = (10 : ℤ).
    -- Substitute the calculated values of a and d.
    rw [a_val, d_val]
    -- The goal is now `↑24 - ↑14 = (10 : ℤ)`.
    -- Rewrite using Nat.cast_sub, provided the subtraction is valid.
    have h_sub_le : 14 ≤ 24 := by norm_num
    rw [← Nat.cast_sub h_sub_le]
    -- The goal is now `↑(24 - 14) = (10 : ℤ)`.
    -- Evaluate the subtraction 24 - 14 and cast to integer.
    -- The goal is now `↑10 = (10 : ℤ)`, which is definitionally true.
    -- -- The message "no goals to be solved" also pointed to a redundant tactic here.
    -- -- The previous `norm_num` tactic previously here was redundant as the goal was definitionally equal.
    -- We remove the redundant tactic `norm_num`.
    -- Close goal by reflexivity.
    rfl


#print axioms amc12_2001_p21