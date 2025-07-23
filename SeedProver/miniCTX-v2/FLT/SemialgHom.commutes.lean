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
lemma SemialgHom.map_smul (ψ : A →ₛₐ[φ] B) (m : R) (x : A) : ψ (m • x) = φ m • ψ x :=
  LinearMap.map_smul' ψ.toLinearMap m x

end semialghom

section semialghomclass

class SemialgHomClass (F : Type*) {R S : outParam Type*}
  [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] extends SemilinearMapClass F φ A B, RingHomClass F A B

variable (F : Type*) {R S : Type*}
  [CommSemiring R] [CommSemiring S] (φ : R →+* S) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [SemialgHomClass F φ A B]

instance SemialgHomClass.instSemialgHom : SemialgHomClass (A →ₛₐ[φ] B) φ A B where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero

end semialghomclass

section semialghom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*}  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

/- Start of proof attempt -/
lemma round1_h1 (R : Type*) (S : Type*) [CommSemiring R] [CommSemiring S]
  (A : Type*) [Semiring A] [Algebra R A]
  (r : R):
  algebraMap R A r = r • (1 : A) := by
  simp [Algebra.algebraMap_eq_smul_one]

lemma round1_h2 (R : Type*) (S : Type*) [CommSemiring R] [CommSemiring S]
  (φ : R →+* S)
  (A : Type*) [Semiring A] [Algebra R A]
  (B : Type*) [Semiring B] [Algebra S B]
  (ψ : A →ₛₐ[φ] B)
  (r : R)
  (h1 : algebraMap R A r = r • (1 : A)):
  ψ (algebraMap R A r) = ψ (r • (1 : A)) := by
  rw [h1]

lemma round1_h3 (R : Type*) (S : Type*) [CommSemiring R] [CommSemiring S]
  (φ : R →+* S)
  (A : Type*) [Semiring A] [Algebra R A]
  (B : Type*) [Semiring B] [Algebra S B]
  (ψ : A →ₛₐ[φ] B)
  (r : R):
  ψ (r • (1 : A)) = φ r • ψ (1 : A) := by
  exact ψ.map_smul r (1 : A)

lemma round1_h4 (R : Type*) (S : Type*) [CommSemiring R] [CommSemiring S]
  (φ : R →+* S)
  (A : Type*) [Semiring A] [Algebra R A]
  (B : Type*) [Semiring B] [Algebra S B]
  (ψ : A →ₛₐ[φ] B):
  ψ (1 : A) = (1 : B) := by
  exact ψ.map_one

lemma round1_h5 (R : Type*) (S : Type*) [CommSemiring R] [CommSemiring S]
  (φ : R →+* S)
  (A : Type*) [Semiring A] [Algebra R A]
  (B : Type*) [Semiring B] [Algebra S B]
  (ψ : A →ₛₐ[φ] B)
  (r : R)
  (h4 : ψ (1 : A) = (1 : B)):
  φ r • ψ (1 : A) = φ r • (1 : B) := by
  rw [h4]

lemma round1_h6 (R : Type*) (S : Type*) [CommSemiring R] [CommSemiring S]
  (φ : R →+* S)
  (A : Type*) [Semiring A] [Algebra R A]
  (B : Type*) [Semiring B] [Algebra S B]
  (r : R):
  algebraMap S B (φ r) = (φ r) • (1 : B) := by
  simp [Algebra.algebraMap_eq_smul_one]

theorem SemialgHom.commutes (ψ : A →ₛₐ[φ] B) (r : R) :
    ψ (algebraMap R A r) = algebraMap S B (φ r)  := by

  have h1 : algebraMap R A r = r • (1 : A) := by
    exact round1_h1 R S A r
  have h2 : ψ (algebraMap R A r) = ψ (r • (1 : A)) := by
    exact round1_h2 R S φ A B ψ r h1
  have h3 : ψ (r • (1 : A)) = φ r • ψ (1 : A) := by
    exact round1_h3 R S φ A B ψ r
  have h4 : ψ (1 : A) = (1 : B) := by
    exact round1_h4 R S φ A B ψ
  have h5 : φ r • ψ (1 : A) = φ r • (1 : B) := by
    exact round1_h5 R S φ A B ψ r h4
  have h6 : algebraMap S B (φ r) = (φ r) • (1 : B) := by
    exact round1_h6 R S φ A B r
  rw [h2, h3, h5]
  rw [h6]
  <;> simp
