import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat Polynomial

theorem imo1959_p1_numbertheory (n : ℕ) (h₀ : 0 < n) :
  Nat.gcd (21*n + 4) (14*n + 3) = 1 := by sorry
theorem imo1959_p2a_algebra (x : ℝ) :
  (Real.sqrt (x + Real.sqrt (2*x - 1)) + Real.sqrt (x - Real.sqrt (2*x - 1)) = Real.sqrt 2 ∧
   0 ≤ 2*x - 1 ∧ 0 ≤ x + Real.sqrt (2*x - 1) ∧ 0 ≤ x - Real.sqrt (2*x - 1))
  ↔ x ∈ Set.Icc (1/2) 1 := by sorry
theorem imo1959_p2b_algebra (x : ℝ) :
  (Real.sqrt (x + Real.sqrt (2*x - 1)) + Real.sqrt (x - Real.sqrt (2*x - 1)) = 1 ∧
   0 ≤ 2*x - 1 ∧ 0 ≤ x + Real.sqrt (2*x - 1) ∧ 0 ≤ x - Real.sqrt (2*x - 1))
  → False := by sorry
theorem imo1959_p2c_algebra (x : ℝ) :
  (Real.sqrt (x + Real.sqrt (2*x - 1)) + Real.sqrt (x - Real.sqrt (2*x - 1)) = 2 ∧
   0 ≤ 2*x - 1 ∧ 0 ≤ x + Real.sqrt (2*x - 1) ∧ 0 ≤ x - Real.sqrt (2*x - 1))
  ↔ x = 3 / 2 := by sorry
theorem imo1960_p1_numbertheory (n : ℕ) :
  ((Nat.digits 10 n).length = 3 ∧
   11 ∣ n ∧
   n / 11 = ((Nat.digits 10 n).map fun x => x * x).sum)
  ↔
  n = 550 ∨ n = 803 := by sorry
theorem imo1960_p2_algebra (x : ℝ) :
  (4 * x^2 / (1 - Real.sqrt (2*x + 1) )^2 < 2*x + 9 ∧
   0 ≤ 2*x + 1 ∧
   (1 - Real.sqrt (2*x + 1))^2 ≠ 0)
  ↔
  x ∈ Set.Ico (-1/2) (45/8) \ {0} := by sorry
theorem imo1961_p1_algebra (x y z a b : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (h₁ : x ≠ y) (h₂ : y ≠ z)
  (h₃ : z ≠ x) (h₄ : x + y + z = a) (h₅ : x ^ 2 + y ^ 2 + z ^ 2 = b ^ 2) (h₆ : x * y = z ^ 2) :
  0 < a ∧ b ^ 2 < a ^ 2 ∧ a ^ 2 < 3 * b ^ 2 := by
  sorry
theorem imo1961_p2_geometry
    (a b c S s : ℝ)
    (h_triangle : 0 < a ∧ 0 < b ∧ 0 < c ∧ a < b + c ∧ b < c + a ∧ c < a + b)
    (h_heron_formula : s = (a + b + c) / 2 ∧ S = √ (s * (s - a) * (s - b) * (s - c))) :
    (a ^ 2 + b ^ 2 + c ^ 2 ≥ 4 * S * √ 3) ∧
    (a ^ 2 + b ^ 2 + c ^ 2 = 4 * S * √ 3 ↔ a = b ∧ a = c) := by sorry
theorem imo1961_p3_algebra {n : ℕ} {x : ℝ} (npos : 0 < n) :
  ((∃ k : ℤ, k * Real.pi = x) ∧ Even n ∨
   (∃ k : ℤ, k * (2 * Real.pi) = x) ∧ Odd n ∨
   (∃ k : ℤ, -(Real.pi/2) + k * (2 * Real.pi) = x) ∧ Odd n)
  ↔
  (cos x)^n - (sin x)^n = 1 := by sorry
theorem imo1962_p1_numbertheory :
  IsLeast {n | ((Nat.digits 10 n).headI = 6 ∧ Nat.ofDigits 10 ((Nat.digits 10 n).tail.concat 6) = 4 * n)} 153846 := by sorry
theorem imo1962_p2_algebra (x : ℝ) :
  (Real.sqrt (3 - x) - Real.sqrt (x + 1) > 1/2 ∧ 3 - x ≥ 0 ∧ x + 1 ≥ 0)
  ↔ x ∈ Set.Ico (-1) (1 - Real.sqrt 31/8) := by sorry
theorem imo1962_p4_algebra (x : ℝ) :
  cos (x)^2 + cos (2*x)^2 + cos (3*x)^2 = 1
  ↔
  ∃ k : ℤ, x = (2*k + 1) * Real.pi/4 ∨ x = (2*k + 1)* Real.pi/6 := by sorry
theorem imo1963_p1_algebra (p x : ℝ) :
  let f (p : ℝ) : Set ℝ :=
    if p ≥ 0 ∧ p ≤ 4/3
    then { (4 - p)/(2 * Real.sqrt (4 - 2*p)) }
    else ∅
  (x^2 - p ≥ 0 ∧
   x^2 - 1 ≥ 0)
  →
  (Real.sqrt (x^2 - p) + 2 * Real.sqrt (x^2 - 1) = x
   ↔
   x ∈ f p) := by
  sorry
theorem imo1963_p5_algebra : Real.cos (Real.pi/7) - Real.cos (2*Real.pi/7) + Real.cos (3*Real.pi/7) = 1/2 := by sorry
theorem imo1964_p1a_numbertheory (n : ℕ) (h₀ : 7 ∣ 2 ^ n - 1) : 3 ∣ n := by sorry
theorem imo1964_p1b_numbertheory (n : ℕ) : ¬7 ∣ 2 ^ n + 1 := by sorry
theorem imo1964_p2_algebra
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := by sorry
theorem imo1964_p4_comb
    (Person Topic : Type)
    [Fintype Person] [DecidableEq Person]
    [Fintype Topic] [DecidableEq Topic]
    (card_person : Fintype.card Person = 17)
    (card_topic : Fintype.card Topic = 3)
    (discusses : Person → Person → Topic)
    (discussion_sym : ∀ p1 p2 : Person, discusses p1 p2 = discusses p2 p1) :
    ∃ t : Topic, ∃ s : Finset Person,
      2 < s.card ∧
        ∀ p1 ∈ s, ∀ p2 ∈ s, p1 ≠ p2 → discusses p1 p2 = t := by sorry
theorem imo1965_p1_algebra :
  {x ∈ Set.Icc 0 (2*Real.pi) | |√(1 + sin (2*x)) - √(1 - sin (2*x))| ∈ Set.Icc (2 * cos x) √2} = Set.Icc (Real.pi/4) (7*Real.pi/4) := by sorry
theorem imo1965_p2_algebra (x : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ)
    (heqs : ∀ i, ∑ j : Fin 3, (a i j * x j) = 0)
    (hab : ∀ i j, if i = j then 0 < a i j else a i j < 0)
    (hc : ∀ i, 0 < ∑ j : Fin 3, a i j)
    : ∀ i, x i = 0 := by sorry
theorem imo1965_p4_algebra (x1 x2 x3 x4: ℝ):
  ((x1 + x2*x3*x4 = 2) ∧ (x2 + x1*x3*x4 = 2) ∧
  (x3 + x1*x2*x4 = 2) ∧ (x4 + x1*x2*x3 = 2)) ↔
  ((x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨
  (x1 = 3 ∧ x2 = -1 ∧ x3 = -1 ∧ x4 = -1) ∨
  (x1 = -1 ∧ x2 = 3 ∧ x3 = -1 ∧ x4 = -1) ∨
  (x1 = -1 ∧ x2 = -1 ∧ x3 = 3 ∧ x4 = -1) ∨
  (x1 = -1 ∧ x2 = -1 ∧ x3 = -1 ∧ x4 = 3)) := by sorry
theorem imo1966_p1_comb (n : ℕ)
    (A B C : Finset (Fin n))
    (h0 : (A ∪ B ∪ C).card = 25)
    (h1 : (Aᶜ ∩ B).card = 2 * (Aᶜ ∩ C).card)
    (h2 : (A ∩ Bᶜ ∩ Cᶜ).card = (A ∩ (B ∪ C)).card + 1)
    (h3 : ((A ∩ Bᶜ ∩ Cᶜ) ∪ (Aᶜ ∩ B ∩ Cᶜ) ∪ (Aᶜ ∩ Bᶜ ∩ C)).card = 2 * ((Aᶜ ∩ B ∩ Cᶜ) ∪ (Aᶜ ∩ Bᶜ ∩ C)).card) :
    (Aᶜ ∩ B ∩ Cᶜ).card = 6 := by sorry
theorem imo1966_p4_algebra (n : ℕ) (x : ℝ)
    (hx : ∀ t : ℕ, ∀ k : ℤ, x ≠ k * Real.pi / 2^t) :
    ∑ i ∈ Finset.range n, 1 / Real.sin (2^(i + 1) * x) =
    1 / Real.tan x - 1 / Real.tan (2^n * x) := by
  sorry
theorem imo1966_p5_algebra {a x: Fin 4 → ℝ}
  (distinct_a: ∀(i j: Fin 4), i ≠ j → a i ≠ a j):
  ( (|a 0-a 1|)*(x 1) + (|a 0-a 2|)*(x 2) + (|a 0-a 3|)*(x 3) = 1 ∧
  (|a 1-a 0|)*(x 0) + (|a 1-a 2|)*(x 2) + (|a 1-a 3|)*(x 3) = 1 ∧
  (|a 2-a 0|)*(x 0) + (|a 2-a 1|)*(x 1) + (|a 2-a 3|)*(x 3) = 1 ∧
  (|a 3-a 0|)*(x 0) + (|a 3-a 1|)*(x 1) + (|a 3-a 2|)*(x 2) = 1) ↔
  (∀ i j, (∀ k, a i ≥ a k ∧ a j ≤ a k) →
  ( (x i = 1 / (a i - a j) ∧ x j = 1 / (a i - a j)) ∧
  ∀ k, k ≠ i ∧ k ≠ j → x k = 0) ) := by sorry
theorem imo1967_p3_numbertheory (k m n : ℕ) (pr : (m + k + 1).Prime) (pgt : n + 1 < m + k + 1) :
  let c : ℕ → ℕ := fun s => s * (s + 1); ∏ i ∈ Finset.range n, (c (i + 1) : ℤ) ∣ ∏ i ∈ Finset.range n, ((c (m + i + 1):ℤ) - (c k):ℤ) := by sorry
theorem imo1967_p6_comb {m n: ℕ}
  {awarded_medals_day: ℕ → ℕ}
  {medal_left: ℕ → ℕ}
  (ngt1: n > 1)
  (day0: awarded_medals_day 0 = 0)
  (dayn: awarded_medals_day n = n)
  (dayi_left: ∀i:ℕ, medal_left i =
    m - ∑ j ∈ Finset.range i, awarded_medals_day j)
  (dayi_award: ∀i:ℕ, 0 < i → i < n → awarded_medals_day i =
    i + (medal_left i - i)/(7:ℚ))
  (total_n_day: ∑ j ∈ Finset.range (n+1), awarded_medals_day j = m):
  n=6 ∧ m=36 := by sorry
theorem imo1968_p2_numbertheory (x : ℕ) :
  x = 12 ↔ x^2 = 10 * x + 22 + (Nat.digits 10 x).prod := by sorry
theorem imo1968_p3_algebra (n : ℕ) [NeZero n] (a b c Δ : ℝ) (ha : a ≠ 0) (hdelta : Δ = (b - 1) ^ 2 - 4 * a * c)
    (s : Set (Fin n → ℝ)) (hs : s = {x | ∀ i, a * x i ^ 2 + b * x i + c = x (i + 1)}) :
    (Δ < 0 → s.encard = 0) ∧
    (Δ = 0 → s.encard = 1) ∧
    (Δ > 0 → s.encard > 1) := by sorry
theorem imo1968_p5a_algebra (f : ℝ → ℝ) (a : ℝ) (ha : a > 0)
  (hf : ∀ x, (f x)^2 ≤ f x ∧ f (x + a) = 1/2 + √(f x - (f x)^2)) :
  ∃ b > 0, Function.Periodic f b := by sorry
theorem imo1968_p5b_algebra :
  ∃ f : ℝ → ℝ, (∀ x, (f x)^2 ≤ f x ∧ f (x + 1) = 1/2 + √(f x - (f x)^2)):= by sorry
theorem imo1968_p6_numbertheory {n : ℕ} :
    ∑' k : ℕ, ⌊(n + 2 ^ k) / (2 ^ (k + 1) : ℝ)⌋ = ⌊(n : ℝ)⌋ := by sorry
theorem imo1969_p1_numbertheory : Set.Infinite {a : ℕ | ∀ n : ℕ, ¬Nat.Prime (n ^ 4 + a)} := by sorry
theorem imo1969_p2_algebra {n : ℕ} {a : ℕ → ℝ} {f : ℝ → ℝ} (hf : ∀ x, f x = ∑ i ∈ Finset.range (n + 1),
    (1 / 2) ^ i * cos (a i + x))
    {x1 x2 : ℝ} (hx1x2 : f x1 = 0 ∧ f x2 = 0) : ∃ m : ℤ, x2 - x1 = m * Real.pi := by sorry
  theorem imo1971_p1_algebra {n : ℕ}
    (Eterm : ℕ → (ℕ → ℝ) → ℝ)
    (E : (ℕ → ℝ) → ℝ)
    (h_Eterm : ∀ i a, Eterm i a = ∏ j ∈ (Finset.range n \ {i}), (a i - a j))
    (h_def_E : ∀ a, E a = ∑ i ∈ Finset.range n, Eterm i a) :
    ((n = 3 ∨ n = 5) → (∀ a : ℕ → ℝ, Monotone a → 0 ≤ E a)) ∧
    ((n > 2 ∧ (n ≠ 3 ∧ n ≠ 5)) → ¬ (∀ a : ℕ → ℝ, Monotone a → 0 ≤ E a)) := by sorry
theorem imo1971_p3_numbertheory : ∃ (S : Set ℕ), Set.Infinite S ∧ (∀ n m, n ∈ S ∧ m ∈ S ∧ n ≠ m → Nat.Coprime (2 ^ n - 3) (2 ^ m - 3)) := by sorry
theorem imo1972_p1_numbertheory (S : Finset ℕ)
    (Scard : S.card = 10)
    (Sdigits : ∀ n ∈ S, (Nat.digits 10 n).length = 2) :
    ∃ S1 S2 : Finset ℕ, S1 ⊆ S ∧ S2 ⊆ S ∧ S1.card ≥ 1 ∧ S2.card ≥ 1 ∧
       Disjoint S1 S2 ∧ ∑ n ∈ S1, n = ∑ n ∈ S2, n := by sorry
theorem imo1972_p3_numbertheory (m n : ℕ) :
    Nat.factorial m * Nat.factorial n * Nat.factorial (m + n) ∣ Nat.factorial (2 * m) * Nat.factorial (2 * n) := by sorry
theorem imo1972_p4_algebra (a b c d e : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e):
    (a^2 - c * e) * (b^2 - c * e) ≤ 0 ∧
    (b^2 - d * a) * (c^2 - d * a) ≤ 0 ∧
    (c^2 - e * b) * (d^2 - e * b) ≤ 0 ∧
    (d^2 - a * c) * (e^2 - a * c) ≤ 0 ∧
    (e^2 - b * d) * (a^2 - b * d) ≤ 0 ↔
      a = b ∧ b = c ∧ c = d ∧ d = e := by sorry
theorem imo1972_p5_algebra (f g : ℝ → ℝ) (hf1 : ∀ x, ∀ y, f (x + y) + f (x - y) = 2 * f x * g y)
    (hf2 : BddAbove (Set.range fun x => ‖f x‖)) (hf3 : ∃ x, f x ≠ 0) (y : ℝ) : ‖g y‖ ≤ 1 := by sorry
theorem imo1973_p3_algebra : IsLeast {m : ℝ | ∃ a b, m = a ^ 2 + b ^ 2 ∧
∃ x, x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1 = 0} 0.8 := by sorry
theorem imo1973_p5_algebra {G : Set (ℝ → ℝ)}
    (hf: ∀ f ∈ G, ∃ a b : ℝ, a ≠ 0 ∧ ∀ x : ℝ, f x = a * x + b)
    (hG : ∀ f ∈ G, ∀ g ∈ G, g ∘ f ∈ G)
    (hinv : ∀ f ∈ G, f⁻¹ ∈ G)
    (hfix : ∀ f ∈ G, ∃ x, f x = x) :
    ∃ k : ℝ, ∀ f ∈ G, f k = k := by sorry
theorem imo1973_p6_algebra
    {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ} (ha : ∀ k, 0 < a k)
    {q : ℝ} (hq : 0 < q ∧ q < 1) :
    ∃ b : Fin n → ℝ,
      (∀ k, a k < b k) ∧
      (∀ k : Fin n, (h : k + 1 < n) → b ⟨k + 1, h⟩ / b k ∈ Set.Ioo q (1 / q)) ∧
      (∑ k, b k < (1 + q) / (1 - q) * ∑ k, a k) := by sorry
theorem imo1974_p1_comb
    {n p q r : ℕ}
    {A B C : ℕ → ℕ}
    (hn : 2 ≤ n) (hp : 0 < p) (hq : p < q) (hr : q < r)
    (h_A_v : ∀ i ∈ Finset.range n, A i = p ∨ A i = q ∨ A i = r)
    (h_B_v : ∀ i ∈ Finset.range n, B i = p ∨ B i = q ∨ B i = r)
    (h_C_v : ∀ i ∈ Finset.range n, C i = p ∨ C i = q ∨ C i = r)
    (h_ABC_disj : ∀ i ∈ Finset.range n, A i ≠ B i ∧ A i ≠ C i ∧ B i ≠ C i)
    (hA : ∑ i ∈ Finset.range n, A i = 20)
    (hB : ∑ i ∈ Finset.range n, B i = 10)
    (hC : ∑ i ∈ Finset.range n, C i = 9)
    (hlstB : B (n - 1) = r) :
    C 0 = q := by sorry
theorem imo1974_p3_numbertheory (n : ℕ) :
  ¬ 5∣∑ k in Finset.range (n + 1), (Nat.choose (2 * n + 1) (2 * k + 1)) * (2^(3 * k)) := by sorry
theorem imo1974_p5_algebra (a b c d s : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : s = a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)) :
  1 < s ∧ s < 2 := by
  sorry
theorem imo1975_p1_algebra (n : ℕ) (σ : Equiv.Perm ℕ) (x y : ℕ → ℝ)
    (hx : AntitoneOn x (Finset.Icc 1 n)) (hy : AntitoneOn y (Finset.Icc 1 n))
    (hσ : {x | σ x ≠ x} ⊆ Finset.Icc 1 n) :
    ∑ i ∈ Finset.Icc 1 n, (x i - y i) ^ 2 ≤ ∑ i ∈ Finset.Icc 1 n, (x i - y (σ i)) ^ 2 := by sorry
theorem imo1975_p2_algebra (a : ℕ → ℤ)
  (apos : ∀ i : ℕ, 0 < a i)
  (ha : ∀ i : ℕ, a i < a (i + 1)) :
    ( ∀ i n0 : ℕ ,
      ∃ n, n0 ≤ n ∧
      ∃ r s : ℕ,
      ∃ j : ℕ,
        a n = r * a i + s * a j ∧
        i < j ∧
        0 < r ∧
        0 < s ):= by sorry
theorem imo1975_p4_numbertheory (A B : ℕ) (hA : A = (Nat.digits 10 (4444 ^ 4444)).sum)
  (hB : B = (Nat.digits 10 A).sum): (Nat.digits 10 B).sum = 7 := by sorry
theorem imo1976_p2_algebra (p : ℕ → ℝ[X]) (hp0 : p 0 = X ^ 2 + C (-2))
    (hpn : ∀ n, p (n + 1) = (p 0).comp (p n)) :
    ∀ n, ∃ r : Fin (2 ^ (n + 1)) ↪ ℝ, (p n - X).roots.toFinset = Finset.univ.map r := by sorry
theorem imo1976_p5_algebra (p q : ℕ) (hq : q = 2 * p) (hp : 0 < p) (a : Fin p → Fin q → ℤ)
    (ha : ∀ i j, a i j ∈ Finset.Icc (-1) 1) :
    ∃ x : Fin q → ℤ, (∃ j, x j ≠ 0) ∧
    (∀ i, ∑ j, a i j * x j = 0) ∧
    (∀ j, |x j| ≤ q) := by sorry
theorem imo1976_p6_algebra (u : ℕ → ℝ)
  (h₀ : u 0 = 2)
  (h₁ : u 1 = 5 / 2)
  (h₂ : ∀ n, u (n + 2) = u (n + 1) * ((u n)^2 - 2) - u 1) :
    ∀ n > 0, ⌊u n⌋  = (2:ℝ) ^((2^n - (-1 : ℝ)^n) / 3):= by sorry
theorem imo1977_p2_comb : IsGreatest {n:ℕ | ∃(x: ℕ → ℝ),
  (∀m: ℕ, m+7 ≤ n → ∑ i ∈ Finset.range 7, (x (m+i)) < 0)  ∧
  (∀m: ℕ, m+11 ≤ n → ∑ i ∈ Finset.range 11, (x (m+i)) > 0)} 16 := by sorry
theorem imo1977_p3_comb (n : ℕ) (ngt2 : 2 < n) : let V := {x | ∃ k, 1 ≤ k ∧ x = 1 + k * n};
  let indecomposable : ℕ → Prop := fun m => ¬ ∃ p ∈ V, ∃ q ∈ V, m = p * q;
  ∃ m ∈ V, ∃ p ∈ V, ∃ q ∈ V, ∃ p' ∈ V, ∃ q' ∈ V,
  indecomposable p ∧ indecomposable q ∧ indecomposable p' ∧ indecomposable q' ∧
  m = p * q ∧ m = p' * q' ∧ p ≠ p' ∧ p ≠ q' := by sorry
theorem imo1977_p4_algebra (f : ℝ → ℝ) (a b A B : ℝ)
  (h₀ : ∀ x, f x =
             1 - a * Real.cos x - b * Real.sin x - A * Real.cos (2 * x) - B * Real.sin (2 * x))
  (h₁ : ∀ x, f x ≥ 0) :
    a ^ 2 + b ^ 2 ≤ 2 ∧ A ^ 2 + B ^ 2 ≤ 1 := by sorry
theorem imo1977_p6_algebra (f : ℕ+ → ℕ+) (h : ∀ n, f (f n) < f (n + 1)) : ∀ n, f n = n := by sorry
theorem imo1978_p1_numbertheory : IsLeast { s | ∃ m n : ℕ, 1 ≤ m ∧ m < n ∧ (1978^m) % 1000 = (1978^n) % 1000 ∧ s = m + n } 106 := by sorry
theorem imo1978_p5_algebra (f : ℕ → ℕ) (finj : f.Injective) : ∀ n,
  ∑ k ∈ Finset.range n, (1:ℚ) / (k + 1) ≤ ∑ k ∈ Finset.range n, ((f k + 1):ℚ) / (k + 1) ^ 2 := by sorry
theorem imo1978_p6_comb (n : ℕ) (hn : n = 1978) (C : Fin n → Fin 6) :
  ∃ j : Fin n, ∃ i : Fin n, ∃ k : Fin n,
    C i = C j ∧
    C j = C k ∧
    (i:ℕ) + 1 + (k:ℕ) + 1 = (j:ℕ) + 1 := by sorry
theorem imo1979_p1_numbertheory (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (h : (p : ℚ) / q = ∑ i ∈ Finset.range 1319, (-1 : ℚ)^i / (i + 1)) :
    1979 ∣ p := by sorry
theorem imo1979_p5_algebra (a : ℝ) :
  (∃ x1 x2 x3 x4 x5 : ℝ,
    x1 ≥ 0 ∧ x2 ≥ 0 ∧ x3 ≥ 0 ∧ x4 ≥ 0 ∧ x5 ≥ 0 ∧
    x1 + 2*x2 + 3*x3 + 4*x4 + 5*x5 = a ∧
    x1 + 2^3*x2 + 3^3*x3 + 4^3*x4 + 5^3*x5 = a^2 ∧
    x1 + 2^5*x2 + 3^5*x3 + 4^5*x4 + 5^5*x5 = a^3 ) ↔ a = 0 ∨ a = 1 ∨ a = 4 ∨ a = 9 ∨ a = 16 ∨ a = 25:= by sorry
theorem imo1981_p6_algebra (f : ℕ → ℕ → ℕ) :
  (∀ y, f 0 y = y + 1) →
  (∀ x, f (x + 1) 0 = f x 1) →
  (∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y)) →
  f 4 1981 = (pow2^[1984]) 1 - 3 := by sorry
theorem imo1982_p1_algebra (f : ℕ → ℕ)
    (h2 : f 2 = 0)
    (h3 : 0 < f 3)
    (h9999 : f 9999 = 3333)
    (hf : ∀ m n, 0 < m → 0 < n → f (m + n) = f m + f n ∨ f (m + n) = f m + f n + 1) :
    f 1982 = 660 := by sorry
theorem imo1982_p3a_algebra {x : ℕ → ℝ} (hx : Antitone x) (h0 : x 0 = 1) (hp : ∀ k, 0 < x k) :
    ∃ n : ℕ, 3.999 ≤ ∑ k ∈ Finset.range n, (x k) ^ 2 / x (k + 1) := by sorry
theorem imo1982_p3b_algebra : ∃ x : ℕ → ℝ, (Antitone x ∧ x 0 = 1 ∧ ∀ k, 0 < x k) ∧ ∀ n : ℕ, ∑ k ∈ Finset.range n, (x k) ^ 2 / x (k + 1) < 4 := by sorry
theorem imo1982_p4_numbertheory (n : ℕ)
  (hn : 0 < n)
  (hxy : ∃ x y : ℤ, x^3 - 3 * x * y^2 + y^3 = n) :
    (n ≠ 2891) ∧
    ∃ x1 x2 x3 y1 y2 y3 : ℤ, (x1^3 - 3 * x1 * y1^2 + y1^3 = n ∧
      x2^3 - 3 * x2 * y2^2 + y2^3 = n ∧
      x3^3 - 3 * x3 * y3^2 + y3^3 = n ∧
      (x1 ≠ x2 ∨ y1 ≠ y2) ∧
      (x1 ≠ x3 ∨ y1 ≠ y3) ∧
      (x2 ≠ x3 ∨ y2 ≠ y3)) := by sorry
theorem imo1983_p1_algebra (f : ℝ → ℝ) (hf : ∀ x, f x > 0) :
    (∀ a > 0, f a = 1 / a) ↔
    ((∀ x y, x > 0 → y > 0 → f (x * f y) = y * f x) ∧
     (∀ ε > 0, ∃ x > 0, ∀ y > 0, x < y → f y < ε)) := by sorry
theorem imo1983_p3_numbertheory {a b c : ℤ}
    (a_pos : 0 < a) (b_pos : 0 < b) (c_pos : 0 < c)
    (coab : IsCoprime a b) (cobc : IsCoprime b c) (coca : IsCoprime c a) :
  IsGreatest
    {t : ℤ | ¬∃ x y z, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x * b * c + y * c * a + z * a * b = t}
    (2 * a * b * c - a * b - b * c - c * a) := by sorry
theorem imo1983_p5_numbertheory :
  ∃ S : Finset ℕ, S.card = 1983 ∧
  (∀ x ∈ S, x ≤ 10^5 ∧ x ≥ 1) ∧
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y ∧ y < z → x + z ≠ 2 * y := by sorry
theorem imo1983_p6_algebra
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by sorry
theorem imo1984_p1_algebra (x y z : ℝ)
  (h₀ : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z)
  (h₁ : x + y + z = 1) :
    0 ≤ x * y + y * z + z * x - 2 * x * y * z ∧ x * y + y * z + z * x - 2 * x * y * z ≤
      (7:ℝ) / 27 := by sorry
theorem imo1984_p2_numbertheory (a b : ℤ) (h₀ : 0 < a ∧ 0 < b) (h₁ : ¬7 ∣ a) (h₂ : ¬7 ∣ b) (h₃ : ¬7 ∣ a + b)
  (h₄ : 7 ^ 7 ∣ (a + b) ^ 7 - a ^ 7 - b ^ 7) : 19 ≤ a + b := by
  sorry
theorem imo1984_p6_numbertheory
  (a b c d k m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h₂ : a < b ∧ b < c ∧ c < d)
  (h₃ : a * d = b * c)
  (h₄ : a + d = 2^k)
  (h₅ : b + c = 2^m) :
  a = 1 := by sorry
theorem imo1985_p4_numbertheory (M : Finset ℕ) (hM_card : M.card = 1985) (Mpos : ∀ m ∈ M, 0 < m)
    (Mdivisors : ∀ m ∈ M, ∀ n, m.Prime ∧ n ∣ m → m ≤ 23)
    : ∃ M' : Finset ℕ, M'.card = 4 ∧ M' ⊆ M ∧ ∃ k, M'.prod id = k^4 := by
  sorry
theorem imo1985_p6_algebra
   (f : ℕ → ℝ → ℝ)
   (h₀ : ∀ x, f 1 x = x)
   (h₁ : ∀ n x, 0 < n → f (n + 1) x = f n x * (f n x + 1 / n)) :
   ∃! a, ∀ n, 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by sorry
theorem imo1986_p1_numbertheory (d : ℤ) (_hdpos : 1 ≤ d) (h2 : d ≠ 2) (h5 : d ≠ 5) (h13 : d ≠ 13) :
    ∃ a b :({2, 5, 13, d} : Finset ℤ), (a ≠ b) ∧ ¬ ∃ z, z^2 = (a * (b : ℤ) - 1) := by sorry
theorem imo1986_p5_algebra (f : ℝ → ℝ) (hf : ∀ x ≥ 0, f x ≥ 0)
  (h1 : ∀ x y, (x ≥ 0 ∧ y ≥ 0) → f (x * f y) * f y = f (x + y))
  (h2 : f 2 = 0)
  (h3 : ∀ x, (x ≥ 0 ∧ x < 2) → f x ≠ 0) :
  ∀ x ≥ 2, f x = 0 ∧
  ∀ x, (x ≥ 0 ∧ x < 2) → f x = 2 / (2 - x) := by sorry
theorem imo1987_p4_algebra : ¬∃ f : ℕ → ℕ, ∀ n, f (f n) = n + 1987 := by sorry
theorem imo1987_p6_numbertheory (n : ℕ) (nge : 2 ≤ n) (hpr : ∀ k : ℕ, k ≤ Real.sqrt ((n:ℝ)/3) → (k ^ 2 + k + n).Prime) :
  ∀ k : ℕ, k ≤ n - 2 → (k ^ 2 + k + n).Prime := by sorry
theorem imo1988_p3_algebra (f : ℕ → ℕ)
  (h₀ : f 1 = 1)
  (h₁ : f 3 = 3)
  (h₂ : ∀ n, n > 0 → f (2 * n) = f n)
  (h₃ : ∀ n, n > 0 → f (4 * n + 1) + f n = 2 * f (2 * n + 1))
  (h₄ : ∀ n, n > 0 → f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1))
  (A: Finset {n | 0 < n ∧ n ≤ 1988 ∧ f n = n}) :
    A.card = 92 := by sorry
theorem imo1988_p6_numbertheory {a b : ℕ} (h : a * b + 1 ∣ a ^ 2 + b ^ 2) :
    ∃ d, d ^ 2 = (a ^ 2 + b ^ 2) / (a * b + 1) := by sorry
theorem imo1989_p5_numbertheory (n : ℕ) : ∃ m, ∀ j < n, ¬IsPrimePow (m + j) := by sorry
theorem imo1990_p3_numbertheory (n : ℕ) (hn : 1 < n) : n = 3 ↔ n^2 ∣ 2^n + 1 := by sorry
theorem imo1991_p2_numbertheory (n k : ℕ) (ngt : 6 < n) (a : ℕ → ℕ) (copr : a '' (Finset.range k) = {t | t < n ∧ n.Coprime t})
(diff : ∀ i < k - 1, a (i + 1) - a i = a 1 - a 0 ∧ 0 < a (i + 1) - a i) : n.Prime ∨ ∃ m, n = 2 ^ m := by sorry
theorem imo1992_p1_numbertheory (a b c : ℤ) (ha : 1 < a) (hb : a < b) (hc : b < c) :
    (a, b, c) ∈ ({(2, 4, 8), (3, 5, 15)} : Set (ℤ × ℤ × ℤ)) ↔
    (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1 := by sorry
theorem imo1992_p2_algebra (f : ℝ → ℝ) :
    (∀ x, f x = x) ↔
    ∀ x y, f (x^2 + f y) = y + f x ^ 2 := by sorry
theorem imo1993_p1_algebra (n : ℕ) (ngt : 1 < n) (f : Polynomial ℤ)
  (hf : f = X ^ n + 5 * X ^ (n - 1) + 3) : Irreducible f := by sorry
theorem imo1993_p5_algebra :
    ∃ f : ℕ+ → ℕ+, f 1 = 2 ∧ ∀ n, f (f n) = f n + n ∧ ∀ n, f n < f (n + 1) := by sorry
theorem imo1994_p1_comb (n : ℕ) (m : ℕ) (A : Finset ℕ) (hm : A.card = m + 1)
    (hrange : ∀ a ∈ A, 0 < a ∧ a ≤ n)
    (hadd : ∀ a ∈ A, ∀ b ∈ A, a + b ≤ n → a + b ∈ A) :
    (m + 1) * (n + 1) ≤ 2 * ∑ x ∈ A, x := by sorry
theorem imo1994_p3_numbertheory {m : ℕ} (m_pos : 0 < m) :
    let b k := (Nat.digits 2 k).count 1
    let f k := ((Finset.Ioc k (2 * k)).filter (b · = 3)).card
    ∃ k, 0 < k ∧ f k = m := by sorry
theorem imo1995_p2_algebra (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 / 2 ≤ 1 / (a^3 * (b + c)) + 1 / (b^3 * (c + a)) + 1 / (c^3 * (a + b)) := by sorry
theorem imo1995_p4_algebra
  (x : ℕ → ℝ)
  (h : x 0 = x 1995)
  (h1 : ∀ i : ℕ, 0 < i ∧ i ≤ 1995 → x (i - 1) + (2 / x (i - 1)) = 2 * x i + (1 / x i)) :
  x 0 ≤ 2^997 ∧
  (∃ x : ℕ → ℝ, x 0 = 2^997 ∧
    x 0 = x 1995 ∧
    ∀ i : ℕ, 0 < i ∧ i ≤ 1995 → x (i - 1) + (2 / x (i - 1)) = 2 * x i + (1 / x i)) := by sorry
theorem imo1997_p5_numbertheory
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x^(y^2) = y^x) :
  (x, y) = (1, 1) ∨ (x, y) = (16, 2) ∨ (x, y) = (27, 3) := by sorry
theorem imo1998_p3_numbertheory (k : ℕ) (hk : k > 0) :
    Odd k ↔
    ∃ n : ℕ,
     (Finset.card (Nat.divisors (n ^ 2))) = k * Finset.card (Nat.divisors n) := by sorry
theorem imo1998_p4_numbertheory (a b : ℕ) :
    (0 < a ∧ 0 < b ∧ a * b^2 + b + 7 ∣ a^2 * b + a + b) ↔
    (a, b) ∈ {(11, 1), (49, 1)} ∪ {(x,y) | ∃ k : ℕ , (k > 0) ∧ (x = 7 * k^2 ∧ y = 7 * k)} := by sorry
theorem imo1998_p6_algebra
    (f : ℕ → ℕ) (hf : ∀ x, f x > 0)
    (h : ∀ s t, s > 0 → t > 0 → f (t^2 * f s) = s * (f t)^2) :
    IsLeast {n : ℕ | n = f 1998} 120 := by sorry
theorem imo1999_p2_algebra
    (n : ℕ) (hn : 2 ≤ n) :
    IsLeast {c : ℝ | ∀ x : ℕ → ℝ, ((∀ i, 0 ≤ x i) →
      ∑ j ∈ Finset.range n, (∑ i ∈ Finset.range j, (x i) * (x j) * (x i ^ 2 + x j ^ 2)) ≤
      c * (∑ i ∈ Finset.range n, x i) ^ 4 ) } 8⁻¹ := by sorry
theorem imo1999_p6_algebra (f : ℝ → ℝ) :
    (∀ x, f x = 1 - x^2 / 2) ↔
    ∀ x y, f (x - f y) = f (f y) + x * f y + f x - 1 := by sorry
theorem imo2000_p2_algebra (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 := by sorry
theorem imo2001_p2_algebra (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 ≤
    a / Real.sqrt (a ^ 2 + 8 * b * c) + b / Real.sqrt (b ^ 2 + 8 * c * a) +
    c / Real.sqrt (c ^ 2 + 8 * a * b) := by sorry
theorem imo2001_p3_comb {Girl Boy Problem : Type}
    [Finite Girl] [Finite Boy] [Finite Problem]
    (girl_card : Nat.card Girl = 21)
    (boy_card : Nat.card Boy = 21)
    (girl_solved : Girl → Problem → Prop)
    (boy_solved : Boy → Problem → Prop)
    (hG : ∀ g : Girl, Set.ncard {p | girl_solved g p} ≤ 6)
    (hB : ∀ b : Boy, Set.ncard {p | boy_solved b p} ≤ 6)
    (hp : ∀ g : Girl, ∀ b : Boy, Set.ncard {p | girl_solved g p ∧ boy_solved b p} ≤ 1)
    : ∃ p : Problem, 3 ≤ Set.ncard {g | girl_solved g p} ∧
                     3 ≤ Set.ncard {g | boy_solved g p} := by sorry
theorem imo2001_p6_numbertheory (a b c d : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) (h₁ : d < c) (h₂ : c < b)
    (h₃ : b < a) (h₄ : a * c + b * d = (b + d + a - c) * (b + d + c - a)) :
    ¬Nat.Prime (a * b + c * d) := by sorry
theorem imo2002_p5_algebra (f : ℝ → ℝ) :
    ((∀ x, f x = 0) ∨ (∀ x, f x = 1 / 2 ∨ ∀ x, f x = x ^ 2)) ↔
    ∀ x y z t, (f x + f z) * (f y + f t) =
               f (x * y - z * t) + f (x * t + y * z) := by sorry
theorem imo2003_p1_comb (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 (10^6)) (hAcard : A.card = 101) :
    ∃ t : Fin 100 → ℕ, ∀ i, t i ≥ 1 ∧ t i ≤ 10^6 ∧
      ∀ i j, i ≠ j → Disjoint {x + t i | x ∈ A} {x + t j | x ∈ A} := by sorry
theorem imo2003_p6_numbertheory (p : ℕ) (hp : p.Prime) :
    ∃ q : ℕ, q.Prime ∧ ∀ n, ¬((q : ℤ) ∣ (n : ℤ)^p - (p : ℤ)) := by sorry
theorem imo2004_p4_algebra {n: ℕ}{t: ℕ → ℝ}(nge3: n ≥ 3)
  (tpos: ∀ i, t i > 0)
  (h₀: n^2 + 1 > (∑ i ∈ Finset.range n, t i) * (∑ i ∈ Finset.range n, (1/(t i)))):
  ∀(i j k: Fin n), i < j → j < k →
  (t i + t j > t k ∧ t j + t k > t i ∧ t k + t i > t j) := by sorry
theorem imo2005_p2_algebra (a : ℕ → ℤ) (ha : ∀ n, 0 < n → Set.InjOn (fun i => a i % n) (Finset.range n.natAbs))
  (neginfi : ({x | x < 0 ∧ ∃ i, x = a i}).Infinite) (posinfi : ({x | 0 < x ∧ ∃ i, x = a i}).Infinite):
  ∀ k, ∃! j, a j = k := by sorry
theorem imo2005_p3_algebra (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x * y * z ≥ 1) :
    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) + (y ^ 5 - y ^ 2) / (y ^ 5 + z ^ 2 + x ^ 2) +
        (z ^ 5 - z ^ 2) / (z ^ 5 + x ^ 2 + y ^ 2) ≥ 0 := by sorry
theorem imo2005_p4_numbertheory {k : ℕ} (hk : 0 < k) :
    (∀ n : ℕ, 1 ≤ n → Nat.Coprime (2 ^ n + 3 ^ n + 6 ^ n - 1) k) ↔ k = 1 := by sorry
theorem imo2006_p3_algebra :
    IsLeast
      { M | (∀ a b c : ℝ,
              |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤
              M * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) } (9 * Real.sqrt 2 / 32) := by sorry
theorem imo2006_p5_numbertheory {P : Polynomial ℤ} (hP : 1 < P.natDegree) {k : ℕ} (hk : 0 < k) :
    (P.comp^[k] X - X).roots.toFinset.card ≤ P.natDegree := by sorry
theorem imo2007_p5_numbertheory (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b - 1 ∣ (4 * a^2 - 1)^2) : a = b := by sorry
theorem imo2008_p2a_algebra (x y z : ℝ) (h : x * y * z = 1) (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) :
    x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 ≥ 1 := by sorry
theorem imo2008_p2b_algebra : Set.Infinite {s : ℚ × ℚ × ℚ | ∃ x y z : ℚ, s = (x, y, z) ∧ x ≠ 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧ x * y * z = 1 ∧
    x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 = 1} := by sorry
theorem imo2008_p3_numbertheory : ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ^ 2 + 1 ∧ (p : ℝ) > 2 * n + Real.sqrt (2 * n) := by sorry
theorem imo2008_p4_algebra (f : ℝ → ℝ) (hpos : ∀ x > 0, f x > 0) :
    ((∀ x > 0, f x = x) ∨ (∀ x > 0, f x = 1 / x)) ↔
      ∀ w x y z, w > 0 ∧ x > 0 ∧ y > 0 ∧ z > 0 ∧ w * x = y * z →
       ((f w)^2 + (f x)^2) * (y^2 + z^2) = (w^2 + x^2) * (f (y^2) + f (z^2)) := by sorry
theorem imo2009_p1_numbertheory
    (n k : ℕ) (hk : 2 ≤ k) (hn : 2 ≤ n) [NeZero k]
    (a : (Fin k) → ℕ)
    (h_a_range : ∀ i : Fin k, (1 ≤ a i ∧ a i ≤ n))
    (h_a_dist : ∀ i j : Fin k, i ≠ j → a i ≠ a j)
    (h_dvd : ∀ i : (Fin k), i ≠ (k - 1) → n ∣ a i * (a (i + 1) - 1)) :
    ¬ n ∣ a (k - 1) * (a 0 - 1) := by sorry
theorem imo2009_p5_algebra (f : ℕ+ → ℕ+) :
    f x = x ↔
    ∀ a b, (f (b + f a - 1) < f b + a ∧
            a < f b + f (b + f a - 1) ∧
            f b < f (b + f a - 1) + a) := by sorry
theorem imo2009_p6_comb (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℤ)
    (ainj : a.Injective)
    (apos : ∀ i, 0 < a i)
    (M : Finset ℤ)
    (Mpos : ∀ m ∈ M, 0 < m)
    (Mcard : M.card = n - 1)
    (hM : ∑ i, a i ∉ M)
    : ∃ p : Equiv.Perm (Fin n),
        ∀ i : Fin n,
          ∑ j ∈ Finset.univ.filter (· ≤ i), a (p j) ∉ M := by sorry
theorem imo2010_p1_algebra (f : ℝ → ℝ) :
    f ∈ { f | (∃ C, ⌊C⌋ = 1 ∧ f = Function.const _ C) ∨ f = Function.const _ 0 } ↔ ∀ x y, f (⌊x⌋ * y) = f x * ⌊f y⌋ := by sorry
theorem imo2010_p3_algebra (g : ℤ → ℤ) :
    (∃ c, c ≥ 0 ∧ ∀ x, g x = x + c) ↔ ∀ m n, m > 0 → n > 0 → IsSquare ((g m + n) * (g n + m)) := by sorry
theorem imo2011_p3_algebra (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) ≤ y * f x + f (f x)) :
    ∀ x ≤ 0, f x = 0 := by sorry
theorem imo2011_p5_numbertheory (f : ℤ → ℤ)
    (fpos : ∀ n, 0 < f n)
    (fpos : ∀ m n, f (m - n) ∣ f m - f n)
    : ∀ m n, f m ≤ f n → f m ∣ f n := by
  sorry
theorem imo2012_p2_algebra (n : ℕ) (hn : 3 ≤ n) (a : Finset.Icc 2 n → ℝ)
    (apos : ∀ i, 0 < a i) (aprod : ∏ i, a i = 1) :
    (n:ℝ)^n < ∏ i, (1 + a i)^i.val := by sorry
theorem imo2012_p4_algebra (f : ℤ → ℤ) :
    ((∃ c : ℤ, ∀ x : ℤ, f x = x ^ 2 * c) ∨
    (∃ c : ℤ, ∀ x : ℤ, (Odd x → f x = c) ∧ (Even x → f x = 0)) ∨
    (∃ c : ℤ, ∀ x : ℤ, (x % 4 = 0 → f x = 0) ∧ (x % 4 = 2 → f x = 4 * c) ∧ (Odd x → f x = c))) ↔
    ∀ a b c : ℤ, a + b + c = 0 →
      (f a)^2 + (f b)^2 + (f c)^2 =
        2 * f a * f b + 2 * f b * f c + 2 * f c * f a := by sorry
theorem imo2013_p1_numbertheory (n : ℕ) (k : ℕ) (hn : n > 0) (hk : k > 0) :
    ∃ m : ℕ → ℕ,
      (1 : ℚ) + (2 ^ k - 1) / n = ∏ i ∈ Finset.range k, (1 + 1 / (m i : ℚ)) ∧ ∀ i, m i > 0 := by sorry
theorem imo2013_p5_algebra
    (f : ℚ → ℝ)
    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
    (H2 : ∀ x y, 0 < x → 0 < y → f x + f y ≤ f (x + y))
    (H_fixed_point : ∃ a, 1 < a ∧ f a = a) :
    ∀ x, 0 < x → f x = x := by sorry
theorem imo2014_p1_algebra (a : ℕ → ℤ) (apos : ∀ i, 0 < a i) (ha : ∀ i, a i < a (i + 1)) :
    ∃! n : ℕ, 0 < n ∧
              n * a n < (∑ i in Finset.range (n + 1), a i) ∧
              (∑ i in Finset.range (n + 1), a i) ≤ n * a (n + 1) := by sorry
theorem imo2015_p5_algebra (f : ℝ → ℝ) :
    ((∀ x, f x = x) ∨ (∀ x, f x = 2 - x)) ↔
    ∀ x y, f (x + f (x + y)) + f (x * y) = x + f (x + y) + y * f x := by sorry
theorem imo2016_p5_algebra :
    IsLeast { k | ∃ L R : Finset ℕ,
                  L ⊂ Finset.Icc 1 2016 ∧
                  R ⊂ Finset.Icc 1 2016 ∧
                  L.card + R.card = k ∧
                  ¬∃ x : ℝ,
                   ∏ i ∈ Finset.Icc 1 2016 \ L, (x - (i : ℝ)) =
                   ∏ i ∈ Finset.Icc 1 2016 \ R, (x - (i : ℝ)) } 2016 := by sorry
theorem imo2017_p1_numbertheory (a : ℕ → ℕ) (h0 : a 0 > 1) (ha : ∀ n, a (n + 1) = if (Nat.sqrt (a n))^2 = a n then Nat.sqrt (a n) else a n + 3) : Nat.mod (a 0) 3 = 0 ↔ (∃ A : ℕ, ∀ M : ℕ, ∃ N > M, a N = A) := by sorry
theorem imo2017_p2_algebra (f : ℝ → ℝ) :
    ((∀ x, f x = 0) ∨ (∀ x, f x = x - 1) ∨ (∀ x, f x = 1 - x)) ↔ ∀ x y, f (f x * f y) + f (x + y) = f (x * y) := by sorry
theorem imo2017_p6_numbertheory (S : Finset (ℤ × ℤ)) (hS : ∀ s ∈ S, gcd s.1 s.2 = 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : ℕ → ℤ,
      ∀ s ∈ S, ∑ i ∈ Finset.range n, a i * s.1 ^ i * s.2 ^ (n - i) = 1 := by sorry
theorem imo2018_p2_algebra (n : ℕ) (hn : n ≥ 3) :
    3 ∣ n ↔ ∃ a : ZMod n → ℝ, ∀ i, a i * a (i + 1) + 1 = a (i + 2) := by sorry
theorem imo2018_p5_numbertheory
    (a : ℕ → ℤ)
    (apos : ∀ n, 0 < a n)
    (N : ℕ)
    (hN : 0 < N)
    (h : ∀ n, N ≤ n →
      ∃ z : ℤ,
        z = ∑ i in Finset.range n, (a i : ℚ) / a ((i + 1) % n))
    : ∃ M, ∀ m, M ≤ m → a m = a (m + 1) := by  sorry
theorem imo2019_p1_algebra (f : ℤ → ℤ) :
    (∀ a b, f (2 * a) + 2 * (f b) = f (f (a + b))) ↔ f ∈ { f | (∀ z, f z = 0) ∨ ∃ c, ∀ z, f z = 2 * z + c } := by sorry
theorem imo2019_p4_numbertheory (n k : ℕ) :
    ((n = 1 ∧ k = 1) ∨ (n = 2 ∧ k = 3)) ↔
    0 < n ∧ 0 < k ∧
    (Nat.factorial k : ℤ) = ∏ i ∈ Finset.range n, ((2:ℤ)^n - (2:ℤ)^i) := by sorry
theorem imo2020_p2_algebra (a b c d : ℝ) (hd0 : 0 < d) (hdc : d ≤ c) (hcb : c ≤ b) (hba : b ≤ a)
    (h1 : a + b + c + d = 1) : (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d < 1 := by sorry
theorem imo2020_p3_comb {n : ℕ} {c : Fin (4 * n) → Fin n} (h : ∀ i, {j | c j = i}.ncard = 4) :
     ∃ S : Finset (Fin (4 * n)), ∑ i ∈ S, ((i : ℕ) + 1) = ∑ i ∈ Sᶜ, ((i : ℕ) + 1) ∧
       ∀ i, {j ∈ S | c j = i}.ncard = 2 := by sorry
theorem imo2020_p4_comb {n : ℕ} (hn : 1 < n) :
    let S := Finset.Icc 1 (n^2)
    let P (k : ℕ) :=
      0 < k ∧
      ∀ (A B : Finset (ℕ × ℕ)),
        A.card = k → B.card = k →
        (∀ p ∈ A, p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2) →
        (∀ p ∈ B, p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2) →
        (A.image Prod.fst).card = k → (A.image Prod.snd).card = k →
        (B.image Prod.fst).card = k → (B.image Prod.snd).card = k →
        (∀ p1 ∈ A, ∀ p2 ∈ A, p1.1 < p2.1 → p1.2 < p2.2) →
        (∀ p1 ∈ B, ∀ p2 ∈ B, p1.1 < p2.1 → p1.2 < p2.2) →
        (let R_A (u v : ℕ) := (u, v) ∈ A
        let R_B (u v : ℕ) := (u, v) ∈ B
        ∃ u v, u ∈ S ∧ v ∈ S ∧ u < v ∧
        Relation.TransGen R_A u v ∧ Relation.TransGen R_B u v)
    IsLeast {k | P k} (n^2 - n + 1) := by sorry
theorem imo2020_p5_numbertheory (n : ℕ) (hn : n > 1) (a : Fin n → ℕ)
  (h : ∀ i j : Fin n, ∃ S : Finset (Fin n), S.card ≥ 1 ∧ (a i + a j) / (2:ℚ) = (∏ s ∈ S, (a s:ℝ))^((1:ℝ) / S.card)) :
    ∀ i j : Fin n, a i = a j := by sorry
theorem imo2021_p1_numbertheory :
    ∀ n : ℕ, 100 ≤ n → ∀ A ⊆ Finset.Icc n (2 * n),
    (∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ IsSquare (a + b)) ∨
    ∃ a ∈ Finset.Icc n (2 * n) \ A, ∃ b ∈ Finset.Icc n (2 * n) \ A, a ≠ b ∧ IsSquare (a + b) := by sorry
theorem imo2021_p2_algebra (n : ℕ) (x : Fin n → ℝ) :
    ∑ i, ∑ j, √|x i - x j| ≤ ∑ i, ∑ j, √|x i + x j| := by sorry
theorem imo2021_p6_algebra (m : ℕ) (hm : 2 ≤ m) (A : Finset ℤ)
    (B : Fin m → Finset ℤ) (hB : ∀ k, B k ⊆ A)
    (hs : ∀ k, ∑ b ∈ B k, b = (m : ℤ) ^ (k.val + 1))
    : m ≤ 2 * A.card := by sorry
theorem imo2022_p2_algebra (f : ℝ → ℝ) :
    (∀ x > 0, f x = 1 / x) ↔
    ∀ x > 0, ∃! y > 0, x * f y + y * f x ≤ 2 := by sorry
theorem imo2022_p5_numbertheory (a b p : ℕ) (ha : 0 < a) (hb : 0 < b) (hp : p.Prime) :
    ((a = 2 ∧ b = 2 ∧ p = 2) ∨ (a = 3 ∧ b = 4 ∧ p = 3)) ↔ a^p = Nat.factorial b + p := by sorry
theorem imo2023_p1_numbertheory (n : ℕ) (hn : n > 1) (hncom : ¬n.Prime)
  (Dividable : ℕ → Prop)
  (Dividable_def : ∀ n, Dividable n ↔ ∀ a b c : ℕ, a ∣ n ∧ b ∣ n ∧ c ∣ n ∧ a < b ∧ b < c ∧ (∀ i, ((a < i) ∧ (i < b)) ∨ ((b < i) ∧ (i < c)) → ¬ i ∣ n) → (a ∣ b + c)) :
  IsPrimePow n ↔ Dividable n := by sorry
theorem imo2023_p1_numbertheory_v2 (n : ℕ) : ¬IsPrimePow n ↔ (n ≤ 1) ∨ (∃ a b c : ℕ, a ∣ n ∧ b ∣ n ∧ c ∣ n ∧ a < b ∧ b < c ∧ (∀ i, (i ∣ n → (i < a ∨ i > c ∨ i = a ∨ i = b ∨ i = c))) ∧ ¬(a ∣ b + c)) := by sorry
theorem imo2023_p1_numbertheory_v3_left
  (n a b c : ℕ)
  (hn : n > 1)
  (hncom : ¬n.Prime)
  (hpp : IsPrimePow n)
  (h_abc_factor : a ∣ n ∧ b ∣ n ∧ c ∣ n)
  (h_diff : a < b ∧ b < c)
  (h_no_factor_in_a_b : ∀ x : ℕ, a < x ∧ x < b → ¬ x ∣ n)
  (h_no_factor_in_b_c : ∀ x : ℕ, b < x ∧ x < c → ¬ x ∣ n) :
  a ∣ b + c := by sorry
theorem imo2023_p1_numbertheory_v3_right
  (n : ℕ)
  (hn : n > 1)
  (hncom : ¬n.Prime)
  (hmain : ∀ a b c : ℕ, (1 ≤ a) ∧ (a < b) ∧ (b < c) ∧ (a ∣ n ∧ b ∣ n ∧ c ∣ n) ∧ (¬∃ x, (x ∣ n ∧ a < x ∧ x < b)) ∧ (¬∃ x, (x ∣ n ∧ b < x ∧ x < c)) → a ∣ b + c) :
  IsPrimePow n := by sorry
theorem imo2023_p3_algebra {k : ℕ} (hk : 2 ≤ k) (a : ℕ → ℤ) (h_dummy : a 0 = 1) (ha : ∀ i, a i > 0) :
    (∃ d : ℤ, (d ≥ 0) ∧ (∀ i ≥ 1, a i + d = a (i + 1))) ↔
    (∃ P : Polynomial ℤ, P.Monic ∧ P.degree = k ∧ (∀ m : ℕ, m ≤ k → 0 ≤ P.coeff m) ∧
    ∀ n ≥ 1, P.eval ((a n) : ℤ) = ∏ i ∈ Finset.range k, a (n + i + 1)) := by sorry
theorem imo2023_p4_algebra
    (x a : ℕ → ℝ)
    (hxp : ∀ i, 0 < x i)
    (hxi : x.Injective)
    (ha : ∀ i : ℕ, a i = Real.sqrt ((∑ i in Finset.Icc 1 i, x i) * (∑ i in Finset.Icc 1 i, 1 / x i)))
    (hxa : ∀ i : ℕ, ∃ k : ℤ, a i = k) :
    3034 ≤ a 2023 := by sorry
theorem imo2024_p1_numbertheory :
    {(α : ℝ) | ∀ (n : ℕ), 0 < n → (n : ℤ) ∣ (∑ i in Finset.Icc 1 n, ⌊i * α⌋)}
    = {α : ℝ | ∃ k : ℤ, Even k ∧ α = k} := by sorry
theorem imo2024_p2_numbertheory :
    {(a, b) | 0 < a ∧ 0 < b ∧ ∃ g N, 0 < g ∧ 0 < N ∧ ∀ n ≥ N, Nat.gcd (a ^ n + b) (b ^ n + a) = g}
    = {(1, 1)} := by sorry
theorem imo2024_p3_comb (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
  (N : ℕ) (hN : 0 < N) (h : ∀ n, N < n → a n = {i | i ∈ Finset.Icc 1 (n - 1) ∧ a (n - 1) = a i}.ncard) :
  (∃ p > 0, ∃ M > 0, ∀ m ≥ M, a (2 * (m + p) + 1) = a (2 * m + 1)) ∨
  (∃ p > 0, ∃ M > 0, ∀ m ≥ M, a (2 * (m + p) + 2) = a (2 * m + 2)) := by sorry
theorem imo2024_p6_algebra
    (IsAquaesulian : (ℚ → ℚ) → Prop)
    (IsAquaesulian_def : ∀ f, IsAquaesulian f ↔
      ∀ x y, f (x + f y) = f x + y ∨ f (f x + y) = x + f y) :
    IsLeast {(c : ℤ) | ∀ f, IsAquaesulian f → {(f r + f (-r)) | (r : ℚ)}.Finite ∧
      {(f r + f (-r)) | (r : ℚ)}.ncard ≤ c} 2 := by sorry
