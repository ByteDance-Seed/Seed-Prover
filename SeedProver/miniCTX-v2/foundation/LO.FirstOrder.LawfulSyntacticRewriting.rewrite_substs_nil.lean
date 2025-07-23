-- In foundation/Foundation/Logic/Predicate/Rew.lean

import Foundation.Logic.Predicate.Term
import Foundation.Logic.Predicate.Quantifier

/-!
# Rewriting System

term/formula morphisms such as Rewritings, substitutions, and embeddings are handled by the structure `LO.FirstOrder.Rew`.
- `LO.FirstOrder.Rew.rewrite f` is a Rewriting of the free variables occurring in the term by `f : ξ₁ → Semiterm L ξ₂ n`.
- `LO.FirstOrder.Rew.substs v` is a substitution of the bounded variables occurring in the term by `v : Fin n → Semiterm L ξ n'`.
- `LO.FirstOrder.Rew.bShift` is a transformation of the bounded variables occurring in the term by `#x ↦ #(Fin.succ x)`.
- `LO.FirstOrder.Rew.shift` is a transformation of the free variables occurring in the term by `&x ↦ &(x + 1)`.
- `LO.FirstOrder.Rew.emb` is a embedding of the term with no free variables.

Rewritings `LO.FirstOrder.Rew` is naturally converted to formula Rewritings by `LO.FirstOrder.Rew.hom`.

-/

namespace LO

namespace FirstOrder

structure Rew (L : Language) (ξ₁ : Type*) (n₁ : ℕ) (ξ₂ : Type*) (n₂ : ℕ) where
  toFun : Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂
  func' : ∀ {k} (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁), toFun (Semiterm.func f v) = Semiterm.func f (fun i => toFun (v i))

abbrev SyntacticRew (L : Language) (n₁ n₂ : ℕ) := Rew L ℕ n₁ ℕ n₂

namespace Rew

open Semiterm
variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}
variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

instance : FunLike (Rew L ξ₁ n₁ ξ₂ n₂) (Semiterm L ξ₁ n₁) (Semiterm L ξ₂ n₂) where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by rcases f; rcases g; simpa using h

instance : CoeFun (Rew L ξ₁ n₁ ξ₂ n₂) (fun _ => Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂) := DFunLike.hasCoeToFun

protected lemma func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (func f v) = func f (fun i => ω (v i)) := ω.func' f v

lemma func'' {k} (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (func f v) = func f (ω ∘ v) := ω.func' f v

@[simp] lemma func0 (f : L.Func 0) (v : Fin 0 → Semiterm L ξ₁ n₁) :
    ω (func f v) = func f ![] := by simp[Rew.func, Matrix.empty_eq]

@[simp] lemma func1 (f : L.Func 1) (t : Semiterm L ξ₁ n₁) :
    ω (func f ![t]) = func f ![ω t] := by simp[Matrix.constant_eq_singleton, Rew.func]

@[simp] lemma func2 (f : L.Func 2) (t₁ t₂ : Semiterm L ξ₁ n₁) :
    ω (func f ![t₁, t₂]) = func f ![ω t₁, ω t₂] := by
  simp only [Rew.func, func.injEq, heq_eq_eq, true_and]
  funext i
  induction i using Fin.induction <;> simp

@[simp] lemma func3 (f : L.Func 3) (t₁ t₂ t₃ : Semiterm L ξ₁ n₁) :
    ω (func f ![t₁, t₂, t₃]) = func f ![ω t₁, ω t₂, ω t₃] := by
  simp only [Rew.func, func.injEq, heq_eq_eq, true_and]
  funext i; induction' i using Fin.induction with i
  · simp
  · induction' i using Fin.induction with i <;> simp

@[ext] lemma ext (ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂) (hb : ∀ x, ω₁ #x = ω₂ #x) (hf : ∀ x, ω₁ &x = ω₂ &x) : ω₁ = ω₂ := by
  apply DFunLike.ext ω₁ ω₂; intro t
  induction t <;> simp[*, ω₁.func, ω₂.func]

lemma ext' {ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂} (h : ω₁ = ω₂) (t) : ω₁ t = ω₂ t := by simp[h]

protected def id : Rew L ξ n ξ n where
  toFun := id
  func' := fun _ _ => rfl

@[simp] lemma id_app (t : Semiterm L ξ n) : Rew.id t = t := rfl

protected def comp (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) : Rew L ξ₁ n₁ ξ₃ n₃ where
  toFun := fun t => ω₂ (ω₁ t)
  func' := fun f v => by simp[func'']; rfl

lemma comp_app (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) :
    (ω₂.comp ω₁) t = ω₂ (ω₁ t) := rfl

@[simp] lemma id_comp (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Rew.id.comp ω = ω := by ext <;> simp[comp_app]

@[simp] lemma comp_id (ω : Rew L ξ₁ n₁ ξ₂ n₂) : ω.comp Rew.id = ω := by ext <;> simp[comp_app]

def bindAux (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) : Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂
  | (#x)       => b x
  | (&x)       => e x
  | (func f v) => func f (fun i => bindAux b e (v i))

def bind (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) : Rew L ξ₁ n₁ ξ₂ n₂ where
  toFun := bindAux b e
  func' := fun _ _ => rfl

def rewrite (f : ξ₁ → Semiterm L ξ₂ n) : Rew L ξ₁ n ξ₂ n := bind Semiterm.bvar f

def rewriteMap (e : ξ₁ → ξ₂) : Rew L ξ₁ n ξ₂ n := rewrite (fun m => &(e m))

def map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) : Rew L ξ₁ n₁ ξ₂ n₂ :=
  bind (fun n => #(b n)) (fun m => &(e m))

def substs {n'} (v : Fin n → Semiterm L ξ n') : Rew L ξ n ξ n' :=
  bind v fvar

def emb {o : Type v₁} [h : IsEmpty o] {ξ : Type v₂} {n} : Rew L o n ξ n := map id h.elim

abbrev embs {o : Type v₁} [IsEmpty o] {n} : Rew L o n ℕ n := emb

def empty {o : Type v₁} [h : IsEmpty o] {ξ : Type v₂} {n} : Rew L o 0 ξ n := map Fin.elim0 h.elim

def bShift : Rew L ξ n ξ (n + 1) :=
  map Fin.succ id

def bShiftAdd (m : ℕ) : Rew L ξ n ξ (n + m) :=
  map (Fin.addNat · m) id

def cast {n n' : ℕ} (h : n = n') : Rew L ξ n ξ n' :=
  map (Fin.cast h) id

def castLE {n n' : ℕ} (h : n ≤ n') : Rew L ξ n ξ n' :=
  map (Fin.castLE h) id

def toS : Rew L (Fin n) 0 Empty n := Rew.bind ![] (#·)

def toF : Rew L Empty n (Fin n) 0 := Rew.bind (&·) Empty.elim

def embSubsts (v : Fin k → Semiterm L ξ n) : Rew L Empty k ξ n := Rew.bind v Empty.elim

protected def q (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Rew L ξ₁ (n₁ + 1) ξ₂ (n₂ + 1) :=
  bind (#0 :> bShift ∘ ω ∘ bvar) (bShift ∘ ω ∘ fvar)

lemma eq_id_of_eq {ω : Rew L ξ n ξ n} (hb : ∀ x, ω #x = #x) (he : ∀ x, ω &x = &x) (t) : ω t = t := by
  have : ω = Rew.id := by ext <;> simp[*]
  simp[this]

def qpow (ω : Rew L ξ₁ n₁ ξ₂ n₂) : (k : ℕ) → Rew L ξ₁ (n₁ + k) ξ₂ (n₂ + k)
  | 0     => ω
  | k + 1 => (ω.qpow k).q

@[simp] lemma qpow_zero (ω : Rew L ξ₁ n₁ ξ₂ n₂) : qpow ω 0 = ω := rfl

@[simp] lemma qpow_succ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (k : ℕ) : qpow ω (k + 1) = (ω.qpow k).q := rfl

section bind

variable (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂)

@[simp] lemma bind_fvar (m : ξ₁) : bind b e (&m : Semiterm L ξ₁ n₁) = e m := rfl

@[simp] lemma bind_bvar (n : Fin n₁) : bind b e (#n : Semiterm L ξ₁ n₁) = b n := rfl

lemma eq_bind (ω : Rew L ξ₁ n₁ ξ₂ n₂) : ω = bind (ω ∘ bvar) (ω ∘ fvar) := by
  ext t; induction t ;simp [Rew.func'']; simp [*]

@[simp] lemma bind_eq_id_of_zero (f : Fin 0 → Semiterm L ξ₂ 0) : bind f fvar = Rew.id := by
  ext x <;> simp only [bind_bvar, bind_fvar, id_app]; exact Fin.elim0 x

end bind

section map

variable (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂)

@[simp] lemma map_fvar (m : ξ₁) : map b e (&m : Semiterm L ξ₁ n₁) = &(e m) := rfl

@[simp] lemma map_bvar (n : Fin n₁) : map b e (#n : Semiterm L ξ₁ n₁) = #(b n) := rfl

@[simp] lemma map_id : map (L := L) (id : Fin n → Fin n) (id : ξ → ξ) = Rew.id := by ext <;> simp

lemma map_inj {b : Fin n₁ → Fin n₂} {e : ξ₁ → ξ₂} (hb : Function.Injective b) (he : Function.Injective e) :
    Function.Injective $ map (L := L) b e
  | #x,                    #y                    => by simpa using @hb _ _
  | #x,                    &y                    => by simp
  | #x,                    func f w              => by simp [Rew.func]
  | &x,                    #y                    => by simp
  | &x,                    &y                    => by simpa using @he _ _
  | &x,                    func f w              => by simp [Rew.func]
  | func f v,              #y                    => by simp [Rew.func]
  | func f v,              &y                    => by simp [Rew.func]
  | func (arity := k) f v, func (arity := l) g w => fun h ↦ by
    have : k = l := by simp [Rew.func] at h; simp_all
    rcases this
    have : f = g := by simp [Rew.func] at h; simp_all
    rcases this
    have : v = w := by
      have : (fun i ↦ (map b e) (v i)) = (fun i ↦ (map b e) (w i)) := by simpa [Rew.func] using h
      funext i; exact map_inj hb he (congrFun this i)
    simp_all

end map

section rewrite

variable (f : ξ₁ → Semiterm L ξ₂ n)

@[simp] lemma rewrite_fvar (x : ξ₁) : rewrite f &x = f x := rfl

@[simp] lemma rewrite_bvar (x : Fin n) : rewrite e (#x : Semiterm L ξ₁ n) = #x := rfl

lemma rewrite_comp_rewrite (v : ξ₂ → Semiterm L ξ₃ n) (w : ξ₁ → Semiterm L ξ₂ n) :
    (rewrite v).comp (rewrite w) = rewrite (rewrite v ∘ w) :=
  by ext <;> simp[comp_app]

@[simp] lemma rewrite_eq_id : (rewrite Semiterm.fvar : Rew L ξ n ξ n) = Rew.id := by ext <;> simp

end rewrite

section rewriteMap

variable (e : ξ₁ → ξ₂)

@[simp] lemma rewriteMap_fvar (x : ξ₁) : rewriteMap e (&x : Semiterm L ξ₁ n) = &(e x) := rfl

@[simp] lemma rewriteMap_bvar (x : Fin n) : rewriteMap e (#x : Semiterm L ξ₁ n) = #x := rfl

@[simp] lemma rewriteMap_id : rewriteMap (L := L) (n := n) (id : ξ → ξ) = Rew.id := by ext <;> simp

lemma eq_rewriteMap_of_funEqOn_fv [DecidableEq ξ₁] (t : Semiterm L ξ₁ n₁) (f g : ξ₁ → Semiterm L ξ₂ n₂) (h : Function.funEqOn t.FVar? f g) :
    Rew.rewriteMap f t = Rew.rewriteMap g t := by
  induction t
  case bvar => simp
  case fvar x => simpa using h x (by simp)
  case func f v ih =>
    simp only [Rew.func, func.injEq, heq_eq_eq, true_and]
    funext i
    exact ih i (fun x hx ↦ h x (by simpa [Semiterm.fvar?_func] using ⟨i, hx⟩))

end rewriteMap

section emb

variable {o : Type v₂} [IsEmpty o]

@[simp] lemma emb_bvar (x : Fin n) : emb (ξ := ξ) (#x : Semiterm L o n) = #x := rfl

@[simp] lemma emb_eq_id : (emb : Rew L o n o n) = Rew.id := by
  ext x <;> simp only [emb_bvar, id_app]; exact isEmptyElim x

lemma eq_empty [h : IsEmpty ξ₁] (ω : Rew L ξ₁ 0 ξ₂ n) :
  ω = empty := by ext x; { exact x.elim0 }; { exact h.elim' x }

end emb

section bShift

@[simp] lemma bShift_bvar (x : Fin n) : bShift (#x : Semiterm L ξ n) = #(Fin.succ x) := rfl

@[simp] lemma bShift_fvar (x : ξ) : bShift (&x : Semiterm L ξ n) = &x := rfl

@[simp] lemma bShift_ne_zero (t : Semiterm L ξ n) : bShift t ≠ #0 := by
  cases t <;> simp[Rew.func, Fin.succ_ne_zero]

@[simp] lemma bShift_positive (t : Semiterm L ξ n) : (bShift t).Positive := by
  induction t <;> simp [Rew.func, *]

lemma positive_iff {t : Semiterm L ξ (n + 1)} : t.Positive ↔ ∃ t', t = bShift t' :=
  ⟨by induction t <;> simp
      case bvar x =>
        intro hx; exact ⟨#(x.pred (Fin.pos_iff_ne_zero.mp hx)), by simp⟩
      case fvar x => exact ⟨&x, by simp⟩
      case func k f v ih =>
        intro h
        have : ∀ i, ∃ t', v i = bShift t' := fun i => ih i (h i)
        choose w hw using this
        exact ⟨func f w, by simp [Rew.func]; funext i; exact hw i⟩,
   by rintro ⟨t', rfl⟩; simp⟩

@[simp] lemma leftConcat_bShift_comp_bvar :
    (#0 :> bShift ∘ bvar : Fin (n + 1) → Semiterm L ξ (n + 1)) = bvar :=
  funext (Fin.cases (by simp) (by simp))

@[simp] lemma bShift_comp_fvar :
    (bShift ∘ fvar : ξ → Semiterm L ξ (n + 1)) = fvar :=
  funext (by simp)

end bShift

section bShiftAdd

@[simp] lemma bShiftAdd_bvar (m) (x : Fin n) : bShiftAdd m (#x : Semiterm L ξ n) = #(Fin.addNat x m) := rfl

@[simp] lemma bShiftAdd_fvar (m) (x : ξ) : bShiftAdd m (&x : Semiterm L ξ n) = &x := rfl

end bShiftAdd

section substs

variable {n'} (w : Fin n → Semiterm L ξ n')

@[simp] lemma substs_bvar (x : Fin n) : substs w #x = w x :=
  by simp[substs]

@[simp] lemma substs_fvar (x : ξ) : substs w &x = &x :=
  by simp[substs]

@[simp] lemma substs_zero (w : Fin 0 → Term L ξ) : substs w = Rew.id :=
  by ext x <;> simp; { exact Fin.elim0 x }

lemma substs_comp_substs (v : Fin l → Semiterm L ξ k) (w : Fin k → Semiterm L ξ n) :
    (substs w).comp (substs v) = substs (substs w ∘ v) :=
  by ext <;> simp[comp_app]

@[simp] lemma substs_eq_id : (substs Semiterm.bvar : Rew L ξ n ξ n) = Rew.id := by ext <;> simp

end substs

section cast

variable {n'} (h : n = n')

@[simp] lemma cast_bvar (x : Fin n) : cast h (#x : Semiterm L ξ n) = #(Fin.cast h x) := rfl

@[simp] lemma cast_fvar (x : ξ) : cast h (&x : Semiterm L ξ n) = &x := rfl

@[simp] lemma cast_eq_id {h} : (cast h : Rew L ξ n ξ n) = Rew.id := by ext <;> simp

end cast

section castLE

@[simp] lemma castLe_bvar {n'} (h : n ≤ n') (x : Fin n) : castLE h (#x : Semiterm L ξ n) = #(Fin.castLE h x) := rfl

@[simp] lemma castLe_fvar {n'} (h : n ≤ n') (x : ξ) : castLE h (&x : Semiterm L ξ n) = &x := rfl

@[simp] lemma castLe_eq_id {h} : (castLE h : Rew L ξ n ξ n) = Rew.id := by ext <;> simp

end castLE

section toS

@[simp] lemma toS_fvar {n} (x : Fin n) : toS (&x : Term L (Fin n)) = #x := rfl

end toS

section embSubsts

variable {k} (w : Fin k → Semiterm L ξ n)

@[simp] lemma embSubsts_bvar (x : Fin k) : embSubsts w #x = w x :=
  by simp[embSubsts]

@[simp] lemma embSubsts_zero (w : Fin 0 → Term L ξ) : embSubsts w = Rew.emb := by
  ext x <;> try simp
  · exact Fin.elim0 x
  · exact Empty.elim x

lemma substs_comp_embSubsts (v : Fin l → Semiterm L ξ k) (w : Fin k → Semiterm L ξ n) :
    (substs w).comp (embSubsts v) = embSubsts (substs w ∘ v) := by
  ext x <;> simp[comp_app]
  exact Empty.elim x

@[simp] lemma embSubsts_eq_id : (embSubsts Semiterm.bvar : Rew L Empty n ξ n) = Rew.emb := by
  ext x <;> try simp
  · exact Empty.elim x

end embSubsts

section ψ

variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

@[simp] lemma q_bvar_zero : ω.q #0 = #0 := by simp[Rew.q]

@[simp] lemma q_bvar_succ (i : Fin n₁) : ω.q #(i.succ) = bShift (ω #i) := by simp[Rew.q]

@[simp] lemma q_fvar (x : ξ₁) : ω.q &x = bShift (ω &x) := by simp[Rew.q]

@[simp] lemma q_comp_bShift : ω.q.comp bShift = bShift.comp ω := by
  ext x <;> simp[comp_app]

@[simp] lemma q_comp_bShift_app (t : Semiterm L ξ₁ n₁) : ω.q (bShift t) = bShift (ω t) := by
  have := ext' (ω.q_comp_bShift) t; simpa only [comp_app] using this

@[simp] lemma q_id : (Rew.id : Rew L ξ n ξ n).q = Rew.id := by ext x; { cases x using Fin.cases <;> simp }; { simp }

@[simp] lemma q_eq_zero_iff : ω.q t = #0 ↔ t = #0 := by
  cases t <;> simp [Rew.func]
  case bvar i =>
    cases i using Fin.cases <;> simp [Fin.succ_ne_zero]

@[simp] lemma q_positive_iff : (ω.q t).Positive ↔ t.Positive := by
  induction t <;> simp [Rew.func, *]
  case bvar x =>
    cases x using Fin.cases <;> simp

@[simp] lemma qpow_id {k} : (Rew.id : Rew L ξ n ξ n).qpow k = Rew.id := by induction k <;> simp[*]

lemma q_comp (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) :
    (Rew.comp ω₂ ω₁).q = ω₂.q.comp ω₁.q := by ext x; { cases x using Fin.cases <;> simp[comp_app] }; { simp[comp_app] }

lemma qpow_comp (k) (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) :
    (Rew.comp ω₂ ω₁).qpow k = (ω₂.qpow k).comp (ω₁.qpow k) := by induction k <;> simp[*, q_comp]

lemma q_bind (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) :
    (bind b e).q = bind (#0 :> bShift ∘ b) (bShift ∘ e) := by ext x; { cases x using Fin.cases <;> simp }; { simp }

lemma q_map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) :
    (map (L := L) b e).q = map (0 :> Fin.succ ∘ b) e := by ext x; { cases x using Fin.cases <;> simp }; { simp }

lemma q_rewrite (f : ξ₁ → Semiterm L ξ₂ n) :
    (rewrite f).q = rewrite (bShift ∘ f) := by ext x; { cases x using Fin.cases <;> simp[rewriteMap] }; { simp }

@[simp] lemma q_rewriteMap (e : ξ₁ → ξ₂) :
    (rewriteMap (L := L) (n := n) e).q = rewriteMap e := by ext x; { cases x using Fin.cases <;> simp[rewriteMap] }; { simp }

@[simp] lemma q_emb {o : Type v₁} [e : IsEmpty o] {n} :
    (emb (L := L) (o := o) (ξ := ξ₂) (n := n)).q = emb := by ext x; { cases x using Fin.cases <;> simp }; { exact e.elim x }

@[simp] lemma qpow_emb {o : Type v₁} [e : IsEmpty o] {n k} :
    (emb (L := L) (o := o) (ξ := ξ₂) (n := n)).qpow k = emb := by induction k <;> simp[*]

@[simp] lemma q_cast {n n'} (h : n = n') :
    (cast h : Rew L ξ n ξ n').q = cast (congrFun (congrArg HAdd.hAdd h) 1) := by
  ext x <;> simp; cases x using Fin.cases <;> simp

@[simp] lemma q_castLE {n n'} (h : n ≤ n') :
    (castLE h : Rew L ξ n ξ n').q = castLE (Nat.add_le_add_right h 1) := by
  ext x <;> simp; cases x using Fin.cases <;> simp

lemma q_toS :
    (toS : Rew L (Fin n) 0 Empty n).q = bind ![#0] (#·.succ) := by
  ext x <;> simp; cases x using Fin.cases <;> try simp
  · exact Fin.elim0 (by assumption)

@[simp] lemma qpow_castLE {n n'} (h : n ≤ n') :
    (castLE h : Rew L ξ n ξ n').qpow k = castLE (Nat.add_le_add_right h k) := by
  induction k <;> simp[*]

lemma q_substs (w : Fin n → Semiterm L ξ n') :
    (substs w).q = substs (#0 :> bShift ∘ w) := by ext x; { cases x using Fin.cases <;> simp }; { simp }

lemma q_embSubsts (w : Fin k → Semiterm L ξ n) :
    (embSubsts w).q = embSubsts (#0 :> bShift ∘ w) := by ext x; { cases x using Fin.cases <;> simp }; { simp; exact Empty.elim x }

end ψ

section Syntactic

/-
  #0 #1 ... #(n - 1) &0 &1 ...
   ↓shift
  #0 #1 ... #(n - 1) &1 &2 &3 ...
-/

def shift : SyntacticRew L n n := map id Nat.succ

/-
  #0 #1 ... #(n - 1) #n &0 &1 ...
   ↓free           ↑fix
  #0 #1 ... #(n - 1) &0 &1 &2 ...
 -/

def free : SyntacticRew L (n + 1) n := bind (bvar <: &0) (fun m => &(Nat.succ m))

def fix : SyntacticRew L n (n + 1) := bind (fun x => #(Fin.castSucc x)) (#(Fin.last n) :>ₙ fvar)

abbrev rewrite1 (t : SyntacticSemiterm L n) : SyntacticRew L n n := bind Semiterm.bvar (t :>ₙ fvar)

section shift

@[simp] lemma shift_bvar (x : Fin n) : shift (#x : SyntacticSemiterm L n) = #x := rfl

@[simp] lemma shift_fvar (x : ℕ) : shift (&x : SyntacticSemiterm L n) = &(x + 1) := rfl

lemma shift_func {k} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    shift (func f v) = func f (fun i => shift (v i)) := rfl

lemma shift_Injective : Function.Injective (@shift L n) :=
  Function.LeftInverse.injective (g := map id Nat.pred)
    (by intros φ; simp[←comp_app]; apply eq_id_of_eq <;> simp[comp_app])

end shift

section free

@[simp] lemma free_bvar_castSucc (x : Fin n) : free (#(Fin.castSucc x) : SyntacticSemiterm L (n + 1)) = #x := by simp[free]

@[simp] lemma free_bvar_castSucc_zero : free (#0 : SyntacticSemiterm L (n + 1 + 1)) = #0 := free_bvar_castSucc 0

@[simp] lemma free_bvar_last : free (#(Fin.last n) : SyntacticSemiterm L (n + 1)) = &0 := by simp[free]

@[simp] lemma free_bvar_last_zero : free (#0 : SyntacticSemiterm L 1) = &0 := free_bvar_last

@[simp] lemma free_fvar (x : ℕ) : free (&x : SyntacticSemiterm L (n + 1)) = &(x + 1) := by simp[free]

end free

section fix

@[simp] lemma fix_bvar (x : Fin n) : fix (#x : SyntacticSemiterm L n) = #(Fin.castSucc x) := by simp[fix]

@[simp] lemma fix_fvar_zero : fix (&0 : SyntacticSemiterm L n) = #(Fin.last n) := by simp[fix]

@[simp] lemma fix_fvar_succ (x : ℕ) : fix (&(x + 1) : SyntacticSemiterm L n) = &x := by simp[fix]

end fix

@[simp] lemma free_comp_fix : (free (L := L) (n := n)).comp fix = Rew.id := by
  ext x <;> simp[comp_app]; { cases x <;> simp }

@[simp] lemma fix_comp_free : (fix (L := L) (n := n)).comp free = Rew.id := by
  ext x <;> simp[comp_app]; { cases x using Fin.lastCases <;> simp }

@[simp] lemma bShift_free_eq_shift : (free (L := L) (n := 0)).comp bShift = shift := by
  ext x <;> simp[comp_app]; { exact Fin.elim0 x }

lemma bShift_comp_substs (v : Fin n₁ → Semiterm L ξ₂ n₂) :
  bShift.comp (substs v) = substs (bShift ∘ v) := by ext x <;> simp[comp_app]

lemma shift_comp_substs (v : Fin n₁ → SyntacticSemiterm L n₂) :
  shift.comp (substs v) = (substs (shift ∘ v)).comp shift := by ext x <;> simp[comp_app]

lemma shift_comp_substs1 (t : SyntacticSemiterm L n₂) :
  shift.comp (substs ![t]) = (substs ![shift t]).comp shift := by ext x <;> simp[comp_app]

@[simp] lemma rewrite_comp_emb {o : Type v₁} [e : IsEmpty o] (f : ξ₂ → Semiterm L ξ₃ n) :
  (rewrite f).comp emb = (emb : Rew L o n ξ₃ n) := by ext x <;> simp[comp_app]; { exact IsEmpty.elim e x }

@[simp] lemma shift_comp_emb {o : Type v₁} [e : IsEmpty o] :
  shift.comp emb = (emb : Rew L o n ℕ n) := by ext x <;> simp[comp_app]; { exact IsEmpty.elim e x }

lemma rewrite_comp_free_eq_substs (t : SyntacticTerm L) :
    (rewrite (t :>ₙ Semiterm.fvar)).comp free = substs ![t] := by ext x <;> simp[comp_app, Fin.eq_zero]

lemma rewrite_comp_shift_eq_id (t : SyntacticTerm L) :
    (rewrite (t :>ₙ Semiterm.fvar)).comp shift = Rew.id := by ext x <;> simp[comp_app]

@[simp] lemma substs_mbar_zero_comp_shift_eq_free :
    (substs (L := L) ![&0]).comp shift = free := by ext x <;> simp[comp_app, Fin.eq_zero]

@[simp] lemma substs_comp_bShift_eq_id (v : Fin 1 → Semiterm L ξ 0) :
    (substs (L := L) v).comp bShift = Rew.id := by ext x <;> simp[comp_app]; exact Fin.elim0 x

lemma free_comp_substs_eq_substs_comp_shift {n'} (w : Fin n' → SyntacticSemiterm Lf (n + 1)) :
    free.comp (substs w) = (substs (free ∘ w)).comp shift :=
  by ext x <;> simp[comp_app]

@[simp] lemma rewriteMap_comp_rewriteMap (f : ξ₁ → ξ₂) (g : ξ₂ → ξ₃) :
  (rewriteMap (L := L) (n := n) g).comp (rewriteMap f) = rewriteMap (g ∘ f) := by ext x <;> simp [comp_app]

@[simp] lemma fix_free_app (t : SyntacticSemiterm L (n + 1)) : fix (free t) = t := by simp[←comp_app]

@[simp] lemma free_fix_app (t : SyntacticSemiterm L n) : free (fix t) = t := by simp[←comp_app]

@[simp] lemma free_bShift_app (t : SyntacticSemiterm L 0) : free (bShift t) = shift t := by simp[←comp_app]

@[simp] lemma substs_bShift_app (v : Fin 1 → Semiterm L ξ 0) : substs v (bShift t) = t := by simp[←comp_app]

lemma rewrite_comp_fix_eq_substs (t) :
    ((rewrite (t :>ₙ (&·))).comp free : SyntacticRew L 1 0) = substs ![t] := by
  ext x <;> simp[comp_app, Fin.eq_zero]

lemma bShift_eq_rewrite :
    (Rew.bShift : SyntacticRew L 0 1) = Rew.substs ![] := by
  ext x
  · exact x.elim0
  · simp

section ψ

variable (ω : SyntacticRew L n₁ n₂)

@[simp] lemma q_shift : (shift (L := L) (n := n)).q = shift := by ext x; { cases x using Fin.cases <;> simp }; { simp }

@[simp] lemma q_free : (free (L := L) (n := n)).q = free := by
  ext x; { cases' x using Fin.cases with x <;> simp; { cases x using Fin.lastCases <;> simp[Fin.succ_castSucc] } }; { simp }

@[simp] lemma q_fix : (fix (L := L) (n := n)).q = fix := by
  ext x; { cases x using Fin.cases <;> simp[Fin.succ_castSucc] }; { cases x <;> simp }

--@[simp] lemma qpow_fix (k : ℕ) : (fix (L := L) (n := n)).qpow k = fix := by

end ψ

def fixitr (n : ℕ) : (m : ℕ) → SyntacticRew L n (n + m)
  | 0     => Rew.id
  | m + 1 => Rew.fix.comp (fixitr n m)

@[simp] lemma fixitr_zero :
    fixitr (L := L) n 0 = Rew.id := by simp [fixitr]

lemma fixitr_succ (m) :
    fixitr (L := L) n (m + 1) = Rew.fix.comp (fixitr n m) := by
  simp [fixitr]

@[simp] lemma fixitr_bvar (n m) (x : Fin n) : fixitr n m (#x : SyntacticSemiterm L n) = #(x.castAdd m) := by
  induction m <;> simp [*, comp_app, fixitr_succ]
  case succ m ih =>
    simpa [ih] using comp_app fix (fixitr (L := L) n m) #x

lemma fixitr_fvar (n m) (x : ℕ) :
    fixitr n m (&x : SyntacticSemiterm L n) = if h : x < m then #(Fin.natAdd n ⟨x, h⟩) else &(x - m) := by
  induction m <;> simp [*, comp_app]
  case succ m ih =>
    suffices fix (fixitr n m &x) = if h : x < m + 1 then #⟨n + x, _⟩ else &(x - (m + 1)) from Eq.trans (comp_app _ _ _) this
    simp [ih]
    by_cases hx : x < m
    · simp [hx, Nat.lt_add_right 1 hx]
    by_cases hx2 : x < m + 1
    · have : x = m := Nat.le_antisymm (by { simpa [Nat.lt_succ] using hx2 }) (by simpa using hx)
      simp [this, hx, hx2]; ext; simp
    · simp [hx, hx2]
      have : x - m = x - (m + 1) + 1 := by omega
      simp [this]

end Syntactic

lemma substs_bv (t : Semiterm L ξ n) (v : Fin n → Semiterm L ξ m) :
    (Rew.substs v t).bv = t.bv.biUnion (fun i ↦ (v i).bv) := by
  induction t <;> simp [Rew.func, Semiterm.bv_func, Finset.biUnion_biUnion, *]

@[simp] lemma substs_positive (t : Semiterm L ξ n) (v : Fin n → Semiterm L ξ (m + 1)) :
    (Rew.substs v t).Positive ↔ ∀ i ∈ t.bv, (v i).Positive := by
  simp [Semiterm.Positive, substs_bv]
  exact ⟨fun H i hi x hx ↦ H x i hi hx, fun H x i hi hx ↦ H i hi x hx⟩

lemma embSubsts_bv (t : Semiterm L Empty n) (v : Fin n → Semiterm L ξ m) :
    (Rew.embSubsts v t).bv = t.bv.biUnion (fun i ↦ (v i).bv) := by
  induction t <;> simp [Rew.func, Semiterm.bv_func, Finset.biUnion_biUnion, *]
  · contradiction

@[simp] lemma embSubsts_positive (t : Semiterm L Empty n) (v : Fin n → Semiterm L ξ (m + 1)) :
    (Rew.embSubsts v t).Positive ↔ ∀ i ∈ t.bv, (v i).Positive := by
  simp [Semiterm.Positive, embSubsts_bv]
  exact ⟨fun H i hi x hx ↦ H x i hi hx, fun H x i hi hx ↦ H i hi x hx⟩

@[simp] lemma bshift_positive (t : Semiterm L ξ n) : Positive (Rew.bShift t) := by
  induction t <;> simp

lemma emb_comp_bShift_comm {o : Type v₁} [IsEmpty o] :
    Rew.bShift.comp (Rew.emb : Rew L o n ξ n) = Rew.emb.comp Rew.bShift := by
  ext x; simp [comp_app]
  exact IsEmpty.elim (by assumption) x

lemma emb_bShift_term {o : Type v₁} [IsEmpty o] (t : Semiterm L o n) :
    Rew.bShift (Rew.emb t : Semiterm L ξ n) = Rew.emb (Rew.bShift t) := by
  simp [←comp_app, emb_comp_bShift_comm]

end Rew

/-!
### Rewriting system of terms

-/
namespace Semiterm

variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}

instance : Coe (Semiterm L Empty n) (SyntacticSemiterm L n) := ⟨Rew.emb⟩

@[simp] lemma freeVariables_emb {ο : Type*} [IsEmpty ο] [DecidableEq ξ] {t : Semiterm L ο n} :
    (Rew.emb t : Semiterm L ξ n).freeVariables = ∅ := by
  induction t
  case bvar => simp
  case fvar x => exact IsEmpty.elim inferInstance x
  case func k f v ih =>
    ext x; simp [Rew.func, freeVariables_func, ih]

lemma rew_eq_of_funEqOn [DecidableEq ξ₁] (ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁)
  (hb : ∀ x, ω₁ #x = ω₂ #x)
  (he : Function.funEqOn t.FVar? (ω₁ ∘ Semiterm.fvar) (ω₂ ∘ Semiterm.fvar)) :
    ω₁ t = ω₂ t := by
  induction t <;> try simp[Rew.func, hb]
  case fvar => simpa [FVar?, Function.funEqOn] using he
  case func k f v ih =>
    funext i
    exact ih i (he.of_subset $ by simp[FVar?]; intro x hx; exact ⟨i, hx⟩)

section lMap

variable (Φ : L₁ →ᵥ L₂)
open Rew

lemma lMap_bind (b : Fin n₁ → Semiterm L₁ ξ₂ n₂) (e : ξ₁ → Semiterm L₁ ξ₂ n₂) (t) :
    lMap Φ (bind b e t) = bind (lMap Φ ∘ b) (lMap Φ ∘ e) (t.lMap Φ) :=
  by induction t <;> simp[*, lMap_func, Rew.func]

lemma lMap_map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) (t) :
    (map b e t).lMap Φ = map b e (t.lMap Φ) := by
  simp [map, lMap_bind, Function.comp_def]

lemma lMap_bShift (t : Semiterm L₁ ξ₁ n) : (bShift t).lMap Φ = bShift (t.lMap Φ) :=
  by simp[bShift, lMap_map]

lemma lMap_shift (t : SyntacticSemiterm L₁ n) : (shift t).lMap Φ = shift (t.lMap Φ) :=
  by simp[shift, lMap_map]

lemma lMap_free (t : SyntacticSemiterm L₁ (n + 1)) : (free t).lMap Φ = free (t.lMap Φ) :=
  by simp[free, lMap_bind]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

lemma lMap_fix (t : SyntacticSemiterm L₁ n) : (fix t).lMap Φ = fix (t.lMap Φ) :=
  by simp[fix, lMap_bind]; congr; funext x; cases x <;> simp

end lMap

lemma fvar?_rew [DecidableEq ξ₁] [DecidableEq ξ₂]
    {ω : Rew L ξ₁ n₁ ξ₂ n₂}
    {t : Semiterm L ξ₁ n₁} {x} :
    (ω t).FVar? x → (∃ i : Fin n₁, (ω #i).FVar? x) ∨ (∃ z : ξ₁, t.FVar? z ∧ (ω &z).FVar? x) := by
  induction t
  case bvar z =>
    intro h; left; exact ⟨z, h⟩
  case fvar z =>
    intro h; right; exact ⟨z, by simp [h]⟩
  case func k F v ih =>
    simp only [Rew.func, fvar?_func, forall_exists_index]
    intro i hx
    rcases ih i hx with (h | ⟨z, hi, hz⟩)
    · left; exact h
    · right; exact ⟨z, ⟨i, hi⟩, hz⟩

@[simp] lemma fvar?_bShift [DecidableEq ξ] {t : Semiterm L ξ n} {x} :
    (Rew.bShift t).FVar? x ↔ t.FVar? x := by
  induction t <;> simp [Rew.func, *]

def toEmpty [DecidableEq ξ] {n : ℕ} : (t : Semiterm L ξ n) → t.freeVariables = ∅ → Semiterm L Empty n
  | #x,        _ => #x
  | &x,        h => by simp at h
  | func f v, h =>
    have : ∀ i, (v i).freeVariables = ∅ := by
      intro i; ext x
      have := by simpa using Eq.to_iff (congrFun (congrArg Membership.mem h) x)
      simpa using this i
    func f fun i ↦ toEmpty (v i) (this i)

@[simp] lemma emb_toEmpty [DecidableEq ξ] (t : Semiterm L ξ n) (ht : t.freeVariables = ∅) : Rew.emb (t.toEmpty ht) = t := by
  induction t <;> try simp [toEmpty, Rew.func, *]
  case fvar => simp at ht

end Semiterm

/-!
### Rewriting system of formulae

-/

class FreeVar (ξ : outParam Type*) (F : ℕ → Type*) where

class Rewriting (L : outParam Language) (ξ : outParam Type*) (F : ℕ → Type*) (ζ : Type*) (G : outParam (ℕ → Type*))
    [LCWQ F] [LCWQ G] where
  app {n₁ n₂} : Rew L ξ n₁ ζ n₂ → F n₁ →ˡᶜ G n₂
  app_all (ω₁₂ : Rew L ξ n₁ ζ n₂) (φ) : app ω₁₂ (∀' φ) = ∀' (app ω₁₂.q φ)
  app_ex (ω₁₂ : Rew L ξ n₁ ζ n₂) (φ) : app ω₁₂ (∃' φ) = ∃' (app ω₁₂.q φ)

abbrev SyntacticRewriting (L : outParam Language) (F : ℕ → Type*) (G : outParam (ℕ → Type*)) [LCWQ F] [LCWQ G] :=
  Rewriting L ℕ F ℕ G

namespace Rewriting

variable [LCWQ F] [LCWQ G] [Rewriting L ξ F ζ G]

attribute [simp] app_all app_ex

infixr:73 " ▹ " => app

lemma smul_ext' {ω₁ ω₂ : Rew L ξ n₁ ζ n₂} (h : ω₁ = ω₂) {φ : F n₁} : ω₁ ▹ φ = ω₂ ▹ φ := by rw [h]

@[simp] lemma smul_ball (ω : Rew L ξ n₁ ζ n₂) (φ ψ : F (n₁ + 1)) : ω ▹ (∀[φ] ψ) = ∀[ω.q ▹ φ] (ω.q ▹ ψ) := by simp [ball]

@[simp] lemma smul_bex (ω : Rew L ξ n₁ ζ n₂) (φ ψ : F (n₁ + 1)) : ω ▹ (∃[φ] ψ) = ∃[ω.q ▹ φ] (ω.q ▹ ψ) := by simp [bex]

abbrev substitute [Rewriting L ξ F ξ F] (φ : F n₁) (w : Fin n₁ → Semiterm L ξ n₂) : F n₂ := Rew.substs w ▹ φ

infix:90 " ⇜ " => LO.FirstOrder.Rewriting.substitute

abbrev shift [Rewriting L ℕ F ℕ F] (φ : F n) : F n := @Rew.shift L n ▹ φ

abbrev free [Rewriting L ℕ F ℕ F] (φ : F (n + 1)) : F n := @Rew.free L n ▹ φ

abbrev fix [Rewriting L ℕ F ℕ F] (φ : F n) : F (n + 1) := @Rew.fix L n ▹ φ

def shifts [Rewriting L ℕ F ℕ F] (Γ : List (F n)) : List (F n) := Γ.map Rewriting.shift

scoped[LO.FirstOrder] postfix:max "⁺" => FirstOrder.Rewriting.shifts

@[coe] abbrev embedding {ο ξ} [IsEmpty ο] {O F : ℕ → Type*} [LCWQ O] [LCWQ F] [Rewriting L ο O ξ F] (φ : O n) : F n := @Rew.emb L ο _ ξ n ▹ φ

end Rewriting

section Notation

open Lean PrettyPrinter Delaborator

syntax (name := substituteNotation) term:max "/[" term,* "]" : term

macro_rules (kind := substituteNotation)
  | `($φ:term /[$terms:term,*]) => `($φ ⇜ ![$terms,*])

@[app_unexpander Rewriting.substitute]
def _root_.unexpsnderSubstitute : Unexpander
  | `($_ $φ:term ![$ts:term,*]) => `($φ /[ $ts,* ])
  | _                           => throw ()

end Notation

class ReflectiveRewriting (L : outParam Language) (ξ : outParam Type*) (F : ℕ → Type*)
    [LCWQ F] [Rewriting L ξ F ξ F] where
  id_app (φ : F n) : @Rew.id L ξ n ▹ φ = φ

class TransitiveRewriting (L : outParam Language)
    (ξ₁ : outParam Type*) (F₁ : ℕ → Type*) (ξ₂ : Type*) (F₂ : outParam (ℕ → Type*)) (ξ₃ : Type*) (F₃ : outParam (ℕ → Type*))
    [LCWQ F₁] [LCWQ F₂] [LCWQ F₃]
    [Rewriting L ξ₁ F₁ ξ₂ F₂] [Rewriting L ξ₂ F₂ ξ₃ F₃] [Rewriting L ξ₁ F₁ ξ₃ F₃] where
  comp_app (ω₁₂ : Rew L ξ₁ n₁ ξ₂ n₂) (ω₂₃ : Rew L ξ₂ n₂ ξ₃ n₃) (φ : F₁ n₁) : (ω₂₃.comp ω₁₂) ▹ φ = ω₂₃ ▹ ω₁₂ ▹ φ

class InjMapRewriting (L : outParam Language) (ξ : outParam Type*) (F : ℕ → Type*) (ζ : Type*) (G : outParam (ℕ → Type*))
    [LCWQ F] [LCWQ G] [Rewriting L ξ F ζ G] where
  smul_map_injective {b : Fin n₁ → Fin n₂} {f : ξ → ζ} :
    (hb : Function.Injective b) → (hf : Function.Injective f) → Function.Injective fun φ : F n₁ ↦ Rew.map (L := L) b f ▹ φ

class LawfulSyntacticRewriting (L : outParam Language) (S : ℕ → Type*) [LCWQ S] [SyntacticRewriting L S S] extends
  ReflectiveRewriting L ℕ S, TransitiveRewriting L ℕ S ℕ S ℕ S, InjMapRewriting L ℕ S ℕ S

attribute [simp] ReflectiveRewriting.id_app

namespace LawfulSyntacticRewriting

variable {S : ℕ → Type*} [LCWQ S] [SyntacticRewriting L S S]

open Rewriting ReflectiveRewriting TransitiveRewriting InjMapRewriting

lemma fix_allClosure (φ : S n) :
    ∀' fix (∀* φ) = ∀* fix φ := by
  induction n
  case zero => simp [univClosure_succ]
  case succ n ih => simp [univClosure_succ, ih]

@[simp] lemma shifts_cons (φ : S n) (Γ : List (S n)) :
    (φ :: Γ)⁺ = Rewriting.shift φ :: Γ⁺ := by simp [shifts]

@[simp] lemma shifts_nil : ([] : List (S n))⁺ = [] := by rfl

lemma shifts_union (Γ Δ : List (S n)) :
    (Γ ++ Δ)⁺ = Γ⁺ ++ Δ⁺ := by simp [shifts]

lemma shifts_neg (Γ : List (S n)) :
    (Γ.map (∼·))⁺ = (Γ⁺).map (∼·) := by simp [shifts]

lemma shift_conj₂ (Γ : List (S n)) : shift (⋀Γ) = ⋀Γ⁺ := by
  induction Γ using List.induction_with_singleton
  case hnil => simp
  case hsingle => simp
  case hcons φ Γ hΓ ih =>
    have : Γ⁺ ≠ [] := by intro H; have : Γ = [] := List.map_eq_nil_iff.mp H; contradiction
    simp [hΓ, this, ih]

variable [LawfulSyntacticRewriting L S]

lemma shift_injective : Function.Injective fun φ : S n ↦ shift φ :=
  smul_map_injective Function.injective_id Nat.succ_injective

@[simp] lemma fix_free (φ : S (n + 1)) :
    fix (free φ) = φ := by simp [←comp_app]

@[simp] lemma free_fix (φ : S n) :
    free (fix φ) = φ := by simp [←comp_app]

@[simp] lemma substitute_empty (φ : S 0) (v : Fin 0 → Semiterm L ℕ  0) : (φ ⇜ v) = φ := by simp [substitute]

/-- `hom_substs_mbar_zero_comp_shift_eq_free` -/
@[simp] lemma app_substs_fbar_zero_comp_shift_eq_free (φ : S 1) :
    (shift φ)/[&0] = free φ := by simp [← comp_app, Rew.substs_mbar_zero_comp_shift_eq_free]

lemma free_rewrite_eq (f : ℕ → SyntacticTerm L) (φ : S 1) :
    free ((Rew.rewrite fun x ↦ Rew.bShift (f x)) ▹ φ) =
    Rew.rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x)) ▹ free φ := by
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app, Fin.eq_zero]

lemma shift_rewrite_eq (f : ℕ → SyntacticTerm L) (φ : S 0) :
    shift (Rew.rewrite f ▹ φ) = (Rew.rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x))) ▹ shift φ := by
  simpa [←comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]

lemma rewrite_subst_eq (f : ℕ → SyntacticTerm L) (t) (φ : S 1) :
    Rew.rewrite f ▹ φ/[t] = (Rew.rewrite (Rew.bShift ∘ f) ▹ φ)/[Rew.rewrite f t] := by
  simpa [←comp_app] using smul_ext' <| by ext x <;> simp[Rew.comp_app]

@[simp] lemma free_substs_nil (φ : S 0) : free (Rewriting.substitute (ξ := ℕ) φ ![]) = shift φ := by
  simpa [←comp_app] using smul_ext' <| by
    ext x <;> simp only [Rew.comp_app, Rew.substs_fvar, Rew.free_fvar, Rew.shift_fvar]; { exact Fin.elim0 x }

/- Start of proof attempt -/
lemma round1_rewrite_substs_nil (f : ℕ → SyntacticTerm L) (φ : S 0) :
    Rew.rewrite (Rew.bShift ∘ f) ▹ (Rewriting.substitute (ξ := ℕ) φ ![]) =
    Rewriting.substitute (ξ := ℕ) (Rew.rewrite f ▹ φ) ![] := by
  have h1 : (Rew.rewrite (Rew.bShift ∘ f)).comp (Rew.bShift : SyntacticRew L 0 1) = (Rew.bShift : SyntacticRew L 0 1).comp (Rew.rewrite f) := by
    have h11 : (Rew.rewrite f).q = Rew.rewrite (Rew.bShift ∘ f) := by simp [Rew.q_rewrite]
    have h12 : (Rew.rewrite f).q.comp (Rew.bShift : SyntacticRew L 0 1) = (Rew.bShift : SyntacticRew L 0 1).comp (Rew.rewrite f) := by
      simp [Rew.q_comp_bShift]
    rw [h11] at h12
    exact h12
  have h2 : ((Rew.rewrite (Rew.bShift ∘ f)).comp (Rew.bShift : SyntacticRew L 0 1)) ▹ φ = (Rew.rewrite (Rew.bShift ∘ f)) ▹ ((Rew.bShift : SyntacticRew L 0 1) ▹ φ) := by
    apply TransitiveRewriting.comp_app
  have h3 : ((Rew.bShift : SyntacticRew L 0 1).comp (Rew.rewrite f)) ▹ φ = (Rew.bShift : SyntacticRew L 0 1) ▹ (Rew.rewrite f ▹ φ) := by
    apply TransitiveRewriting.comp_app
  have h4 : ((Rew.rewrite (Rew.bShift ∘ f)).comp (Rew.bShift : SyntacticRew L 0 1)) ▹ φ = ((Rew.bShift : SyntacticRew L 0 1).comp (Rew.rewrite f)) ▹ φ := by
    rw [h1]
  have h5 : (Rew.rewrite (Rew.bShift ∘ f)) ▹ ((Rew.bShift : SyntacticRew L 0 1) ▹ φ) = (Rew.bShift : SyntacticRew L 0 1) ▹ (Rew.rewrite f ▹ φ) := by
    calc
      (Rew.rewrite (Rew.bShift ∘ f)) ▹ ((Rew.bShift : SyntacticRew L 0 1) ▹ φ) = ((Rew.rewrite (Rew.bShift ∘ f)).comp (Rew.bShift : SyntacticRew L 0 1)) ▹ φ := by
        rw [h2]
      _ = ((Rew.bShift : SyntacticRew L 0 1).comp (Rew.rewrite f)) ▹ φ := by
        rw [h4]
      _ = (Rew.bShift : SyntacticRew L 0 1) ▹ (Rew.rewrite f ▹ φ) := by
        rw [h3]
  have h6 : (Rew.substs ![] : SyntacticRew L 0 1) = (Rew.bShift : SyntacticRew L 0 1) := by
    rw [Rew.bShift_eq_rewrite]
    <;> aesop
  have h7 : Rewriting.substitute (ξ := ℕ) φ ![] = (Rew.bShift : SyntacticRew L 0 1) ▹ φ := by
    simp only [Rewriting.substitute]
    have h71 : (Rew.substs ![] : SyntacticRew L 0 1) = (Rew.bShift : SyntacticRew L 0 1) := h6
    have h72 : (Rew.substs ![] : SyntacticRew L 0 1) ▹ φ = (Rew.bShift : SyntacticRew L 0 1) ▹ φ := by
      rw [h71]
    simpa using h72
  have h8 : Rewriting.substitute (ξ := ℕ) (Rew.rewrite f ▹ φ) ![] = (Rew.bShift : SyntacticRew L 0 1) ▹ (Rew.rewrite f ▹ φ) := by
    simp only [Rewriting.substitute]
    have h81 : (Rew.substs ![] : SyntacticRew L 0 1) = (Rew.bShift : SyntacticRew L 0 1) := h6
    have h82 : (Rew.substs ![] : SyntacticRew L 0 1) ▹ (Rew.rewrite f ▹ φ) = (Rew.bShift : SyntacticRew L 0 1) ▹ (Rew.rewrite f ▹ φ) := by
      rw [h81]
    simpa using h82
  rw [h7, h8]
  exact h5

theorem rewrite_substs_nil (f : ℕ → SyntacticTerm L) (φ : S 0) :
    Rew.rewrite (Rew.bShift ∘ f) ▹ (Rewriting.substitute (ξ := ℕ) φ ![]) =
    Rewriting.substitute (ξ := ℕ) (Rew.rewrite f ▹ φ) ![]  := by

  exact round1_rewrite_substs_nil f φ
