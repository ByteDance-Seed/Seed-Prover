-- In FLT/FLT/Mathlib/Algebra/Algebra/Pi.lean

import Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Algebra.Hom

def Pi.semialgHom  {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A]  [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) :
  A →ₛₐ[φ] (i : I) → f i where
  __ := Pi.ringHom fun i ↦ (g i).toRingHom
  map_smul' r a := by ext; simp

/- Start of proof attempt -/
lemma round1_Pi.semialgHom_apply (I : Type*) (R S : Type*) (f : I → Type*) [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A] [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) (a : A) (i : I) :
  (Pi.semialgHom _ φ g) a i = g i a := by
  rfl

theorem Pi.semialgHom_apply {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A] [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) (a : A) (i : I) :
  (Pi.semialgHom _ φ g) a i = g i a  := by

  exact round1_Pi.semialgHom_apply I R S f φ g a i
