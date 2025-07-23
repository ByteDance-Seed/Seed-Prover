-- In FLT/FLT/Mathlib/Algebra/Algebra/Hom.lean

import Mathlib.Algebra.Algebra.Hom

section semialghom

/-- Let `φ : R →+* S` be a ring homomorphism, let `A` be an `R`-algebra and let `B` be
an `S`-algebra. Then `SemialgHom φ A B` or `A →ₛₐ[φ] B` is the ring homomorphisms `ψ : A →+* B`
making lying above `φ` (i.e. such that `ψ (r • a) = φ r • ψ a`).
-/
structure SemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*)  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends A →ₛₗ[φ] B, RingHom A B

@[inherit_doc SemialgHom]
infixr:25 " →ₛₐ " => SemialgHom _

@[inherit_doc]
notation:25 A " →ₛₐ[" φ:25 "] " B:0 => SemialgHom φ A B

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*)  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

instance instFunLike : FunLike (A →ₛₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective' h

variable {φ} {A} {B} in

/- Start of proof attempt -/
lemma round1_h1 (φ : R →+* S)
  (A B : Type*)
  [Semiring A]
  [Semiring B]
  [Algebra R A]
  [Algebra S B]
  (ψ : A →ₛₐ[φ] B)
  (m : R)
  (x : A):
  ψ.toSemilinearMap (m • x) = φ m • ψ.toSemilinearMap x := by
  simp

lemma round1_h2 (φ : R →+* S)
  (A B : Type*)
  [Semiring A]
  [Semiring B]
  [Algebra R A]
  [Algebra S B]
  (ψ : A →ₛₐ[φ] B)
  (m : R)
  (x : A)
  (h1 : ψ.toSemilinearMap (m • x) = φ m • ψ.toSemilinearMap x):
  ∀ (y : A), ψ y = ψ.toSemilinearMap y := by
  intro y
  rfl

lemma round1_h21 (φ : R →+* S)
  (A B : Type*)
  [Semiring A]
  [Semiring B]
  [Algebra R A]
  [Algebra S B]
  (ψ : A →ₛₐ[φ] B)
  (m : R)
  (x : A)
  (h1 : ψ.toSemilinearMap (m • x) = φ m • ψ.toSemilinearMap x)
  (h2 : ∀ (y : A), ψ y = ψ.toSemilinearMap y):
  ψ (m • x) = ψ.toSemilinearMap (m • x) := by
  exact h2 (m • x)

lemma round1_h22 (φ : R →+* S)
  (A B : Type*)
  [Semiring A]
  [Semiring B]
  [Algebra R A]
  [Algebra S B]
  (ψ : A →ₛₐ[φ] B)
  (m : R)
  (x : A)
  (h1 : ψ.toSemilinearMap (m • x) = φ m • ψ.toSemilinearMap x)
  (h2 : ∀ (y : A), ψ y = ψ.toSemilinearMap y)
  (h21 : ψ (m • x) = ψ.toSemilinearMap (m • x)):
  ψ x = ψ.toSemilinearMap x := by
  exact h2 x

theorem SemialgHom.map_smul (ψ : A →ₛₐ[φ] B) (m : R) (x : A) : ψ (m • x) = φ m • ψ x  := by

  have h1 : ψ.toSemilinearMap (m • x) = φ m • ψ.toSemilinearMap x := by
    exact round1_h1 φ A B ψ m x
  have h2 : ∀ (y : A), ψ y = ψ.toSemilinearMap y := by
    exact round1_h2 φ A B ψ m x h1
  have h21 : ψ (m • x) = ψ.toSemilinearMap (m • x) := by
    exact round1_h21 φ A B ψ m x h1 h2
  have h22 : ψ x = ψ.toSemilinearMap x := by
    exact round1_h22 φ A B ψ m x h1 h2 h21
  have h3 : ψ (m • x) = φ m • ψ.toSemilinearMap x := by
    rw [h21]
    exact h1
  have h4 : φ m • ψ.toSemilinearMap x = φ m • ψ x := by
    rw [h22]
    <;> simp
  rw [h3]
  rw [h4]
