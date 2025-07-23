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

/- Start of proof attempt -/
lemma round1_bShift_eq_rewrite :
    (Rew.bShift : SyntacticRew L 0 1) = Rew.substs ![]  := by
  apply Rew.ext
  · -- Proof for bounded variables
    intro x
    exfalso
    exact Fin.elim0 x
  · -- Proof for free variables
    intro x
    simp [Rew.substs_fvar]

theorem bShift_eq_rewrite :
    (Rew.bShift : SyntacticRew L 0 1) = Rew.substs ![]  := by

  exact round1_bShift_eq_rewrite
