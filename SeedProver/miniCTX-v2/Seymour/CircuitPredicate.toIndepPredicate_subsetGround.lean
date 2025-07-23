-- In Seymour/Seymour/Matroid/Notions/CircuitAxioms.lean

import Mathlib.Order.RelClasses
import Mathlib.Data.Matroid.Basic

import Seymour.Basic
import Seymour.Matroid.Notions.IndepAxioms

/-- Circuit predicate, defines which sets are circuits. -/
abbrev CircuitPredicate (α : Type) := Set α → Prop

variable {α : Type}

section ValidFamily

/-- Family of circuits satisfying assumptions of circuit axiom (C3) from Bruhn et al. -/
structure ValidFamily (P : CircuitPredicate α) (X : Set α) where
  F : X.Elem → Set α
  hPF : ∀ x : X.Elem, P (F x)
  hF : ∀ x y : X.Elem, x.val ∈ F y ↔ x = y -- `F y` may nevertheless contain multiple elements of `Xᶜ`

/-- Shorthand for union of sets in `ValidFamily` -/
abbrev ValidFamily.union {P : CircuitPredicate α} {X : Set α} (F : ValidFamily P X) : Set α :=
  Set.iUnion F.F

-- question: unused API?
lemma ValidFamily.mem_of_elem {P : CircuitPredicate α} {X : Set α} (F : ValidFamily P X) (x : X.Elem) :
    x.val ∈ F.F x := by
  rw [F.hF]

-- question: unused API?
lemma ValidFamily.outside {P : CircuitPredicate α} {C X : Set α} {F : ValidFamily P X} {z : α} (hzCF : z ∈ C \ F.union) :
    z ∉ X := by
  intro hz
  have := F.hF ⟨z, hz⟩ ⟨z, hz⟩
  simp_all

end ValidFamily

section CircuitAxioms

/-- Circuit predicate `P` defines independence predicate: independent sets are all non-circuits. -/
def CircuitPredicate.toIndepPredicate (P : CircuitPredicate α) (E : Set α) : IndepPredicate α :=
  fun I : Set α => I ⊆ E ∧ ∀ C : Set α, C ⊆ I → ¬(P C)

/-- Axiom (C1): empty set is not a circuit. -/
def CircuitPredicate.NotCircuitEmpty (P : CircuitPredicate α) : Prop :=
  ¬(P ∅)
alias CircuitPredicate.BruhnC1 := CircuitPredicate.NotCircuitEmpty

/-- Axiom (C2): no circuit is a subset of another circuit. -/
def CircuitPredicate.CircuitNotSsubset (P : CircuitPredicate α) : Prop :=
  ∀ C C' : Set α, P C → P C' → ¬(C' ⊂ C)  -- todo: swap to ¬C ⊂ C'
alias CircuitPredicate.BruhnC2 := CircuitPredicate.CircuitNotSsubset

/-- Axiom (C3) from Bruhn et al. -/
def CircuitPredicate.BruhnC3 (P : CircuitPredicate α) : Prop :=
  ∀ X C : Set α, ∀ F : ValidFamily P X, ∀ z ∈ C \ F.union, ∃ C' : Set α, P C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ F.union) \ X

/-- Axiom (CM) from Bruhn et al.: set of all independent sets has the maximal subset property. -/
def CircuitPredicate.CircuitMaximal (P : CircuitPredicate α) (E : Set α) : Prop :=
  ∀ X : Set α, X ⊆ E → Matroid.ExistsMaximalSubsetProperty (P.toIndepPredicate E) X
alias CircuitPredicate.BruhnCM := CircuitPredicate.CircuitMaximal

/-- Every circuit is a subset of the ground set. -/
def CircuitPredicate.SubsetGround (P : CircuitPredicate α) (E : Set α) : Prop :=
  ∀ C : Set α, P C → C ⊆ E
alias CircuitPredicate.BruhnCE := CircuitPredicate.SubsetGround

/-- Strong circuit elimination axiom: if `C₁` and `C₂` are circuits with `e ∈ C₁ ∩ C₂` and `f ∈ C₁ \ C₂`,
    then there is circuit `C₃` such that `f ∈ C₃ ⊆ C₁ ∪ C₂ \ {e}`. -/
def CircuitPredicate.StrongCircuitElim (P : CircuitPredicate α) : Prop :=
  ∀ C₁ C₂ : Set α, ∀ e f, P C₁ ∧ P C₂ ∧ e ∈ C₁ ∩ C₂ ∧ f ∈ C₁ \ C₂ → ∃ C₃, P C₃ ∧ f ∈ C₃ ∧ C₃ ⊆ (C₁ ∪ C₂) \ {e}

/-- Weak circuit elimination axiom: if `C₁` and `C₂` are distinct circuits and `e ∈ C₁ ∩ C₂`,
    then there is circuit `C₃` such that `C₃ ⊆ C₁ ∪ C₂ \ {e}`. -/
def CircuitPredicate.WeakCircuitElim (P : CircuitPredicate α) : Prop :=
  ∀ C₁ C₂ : Set α, C₁ ≠ C₂ → P C₁ → P C₂ → ∀ e ∈ C₁ ∩ C₂, ∃ C₃, P C₃ ∧ C₃ ⊆ (C₁ ∪ C₂) \ {e}

end CircuitAxioms

section CircuitAxiomRelations

/-- Alternative formulation of axiom (C2). -/
lemma CircuitPredicate.circuit_not_ssubset_iff (P : CircuitPredicate α) :
    P.CircuitNotSsubset ↔ ∀ C C' : Set α, P C → P C' → C' ⊆ C → C ⊆ C' := by
  constructor
  · intro hP C C' hC hC' hCC'
    apply hP C C' hC at hC'
    rw [ssubset_iff_subset_ne] at hC'
    push_neg at hC'
    exact (hC' hCC').symm.subset
  · intro hP C C' hC hC' hCC'
    apply hP C C' hC at hC'
    rw [ssubset_iff_subset_ne] at hCC'
    exact hCC'.right.symm (Set.Subset.antisymm (hC' hCC'.left) hCC'.left)

/-- Axiom (C3) implies strong circuit elimination. -/
lemma CircuitPredicate.C3_strong_circuit_elim (P : CircuitPredicate α) :
    P.BruhnC3 → P.StrongCircuitElim := by
  intro hPC3 C₁ C₂ x z hxz
  obtain ⟨_hC₁, hC₂, hx, hz⟩ := hxz
  let F : ValidFamily P {x} :=
  ⟨
    (fun _ => C₂),
    (fun _ => hC₂),
    (by simpa using Set.mem_of_mem_inter_right hx)
  ⟩
  specialize hPC3 {x} C₁ F
  simp only [ValidFamily.union, Set.iUnion_coe_set, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left] at hPC3
  specialize hPC3 z hz
  exact hPC3

/-- Strong circuit elimination implies weak circuit elimination. -/
lemma CircuitPredicate.strong_circuit_elim_weak_circuit_elim (P : CircuitPredicate α) :
    P.StrongCircuitElim → P.WeakCircuitElim := by
  intro hP C₁ C₂ hCC hC₁ hC₂ e he
  if hf : ∃ f : α, f ∈ C₁ \ C₂ then
    obtain ⟨f, hf⟩ := hf
    specialize hP C₁ C₂ e f (And.intro hC₁ (And.intro hC₂ (And.intro he hf)))
    obtain ⟨C₃, ⟨hC₃, ⟨-, _⟩⟩⟩ := hP
    use C₃
  else
    push_neg at hf
    simp only [Set.mem_diff, not_and, not_not] at hf
    have C₁_sub_C₂ : C₁ ⊆ C₂ := hf
    obtain ⟨f, hff⟩ : (C₂ \ C₁).Nonempty
    · rw [Set.diff_nonempty]
      by_contra C₂_sub_C₁
      exact hCC (C₁_sub_C₂.antisymm C₂_sub_C₁)
    specialize hP C₂ C₁ e f (And.intro hC₂ (And.intro hC₁ (And.intro he.symm hff)))
    obtain ⟨C₃, ⟨hC₃, ⟨-, hCCCe⟩⟩⟩ := hP
    rw [Set.union_comm] at hCCCe
    use C₃

/-- todo: desc -/
def CircuitPredicate.support (P : CircuitPredicate α) : Set α :=
  { C : Set α | P C }.sUnion

/-- todo: desc -/
lemma CircuitPredicate.support_eq (P : CircuitPredicate α) :
    Minimal (fun S : Set α => ∀ C : Set α, P C → C ⊆ S) P.support := by
  sorry

/-- Condition for circuit predicate to have finite support. -/
lemma CircuitPredicate.finite_support_iff (P : CircuitPredicate α) :
    P.support.Finite ↔ ∃ S : Set α, S.Finite ∧ ∀ C : Set α, P C → C ⊆ S := by
  sorry

/-- If `P` is finitely supported and `P` satisfies weak circuit elimination, then `P` satisfies (C3). -/
lemma CircuitPredicate.finSup_weakCircuitElim_bruhnC3 {P : CircuitPredicate α} (hP_fin : P.support.Finite) :
    P.WeakCircuitElim → P.BruhnC3 := by
  sorry

end CircuitAxiomRelations

section PredicateRelations

/-- Independence predicate defines following circuit predicate: circuits are minimal dependent sets. -/
def IndepPredicate.ToCircuitPredicate (P : IndepPredicate α) (E : Set α) : CircuitPredicate α :=
  fun C : Set α => Minimal (fun D : Set α => ¬(P D) ∧ D ⊆ E) C

/-- Converting circuit predicate to independence predicate and then to circuit predicate
    yields original independence predicate.-/
lemma CircuitPredicate.toIndep_toCircuit (P : CircuitPredicate α) (E C : Set α) :
    (P.toIndepPredicate E).ToCircuitPredicate E C → C ⊆ E ∧ P C := by
  intro ⟨⟨C_dep, hCE⟩, C_min⟩
  constructor
  · exact hCE
  · unfold CircuitPredicate.toIndepPredicate at C_dep C_min
    push_neg at C_dep
    obtain ⟨D, hDC, hD⟩ := C_dep hCE
    have D_ok : ¬(D ⊆ E ∧ ∀ C ⊆ D, ¬P C) ∧ D ⊆ E := ⟨(by push_neg; intro; use D), hDC.trans hCE⟩
    exact Set.eq_of_subset_of_subset (C_min D_ok hDC) hDC ▸ hD

/-- todo: desc-/
lemma CircuitPredicate.toIndep_toCircuit_iff {P : CircuitPredicate α} (hP : P.CircuitNotSsubset) (E C : Set α) :
    (P.toIndepPredicate E).ToCircuitPredicate E C ↔ C ⊆ E ∧ P C := by
  constructor
  · exact P.toIndep_toCircuit E C
  · intro ⟨hCE, hC⟩
    constructor
    · exact ⟨fun ⟨_, C_subset_E⟩ => (C_subset_E C Set.Subset.rfl) hC, hCE⟩
    · intro D ⟨D_notIndep, hDE⟩ hDC
      unfold CircuitPredicate.toIndepPredicate at D_notIndep
      push_neg at D_notIndep
      obtain ⟨D', hDD, hD'⟩ := D_notIndep hDE
      rw [CircuitPredicate.circuit_not_ssubset_iff] at hP
      exact (hP C D' hC hD' (hDD.trans hDC)).trans hDD

/-- Converting independence predicate to circuit predicate and then to independence predicate
    yields original independence predicate.-/
lemma IndepPredicate.toCircuit_toIndep_iff (P : IndepPredicate α) (E I : Set α) :
    (P.ToCircuitPredicate E).toIndepPredicate E I ↔ P I ∧ I ⊆ E := by
  constructor
  · intro ⟨hIE, hI⟩
    constructor
    · sorry
    · exact hIE
  · intro ⟨hPI, hIE⟩
    constructor
    · exact hIE
    · sorry

/-- Converting independence predicate of matroid to circuit predicate and then to independence predicate
    yields original independence predicate. -/
lemma IndepPredicate.matroid_toCircuit_toIndep_iff (M : Matroid α) (I : Set α) :
    (M.IndepPredicate.ToCircuitPredicate M.E).toIndepPredicate M.E I ↔ I ⊆ M.E ∧ M.Indep I := by
  constructor
  · intro ⟨hIE, hI⟩
    constructor
    · exact hIE
    · -- hI : I contains no circuit
      let hIE' := hIE
      apply M.maximality at hIE
      specialize hIE ∅ M.empty_indep I.empty_subset
      obtain ⟨J, -, ⟨J_indep, hJI⟩, hJ⟩ := hIE
      simp at hJ
      have J_eq_I : J = I
      · by_contra hJneqI
        have haIJ : ∃ a : α, a ∈ I \ J := Set.nonempty_of_ssubset (HasSubset.Subset.ssubset_of_ne hJI hJneqI)
        obtain ⟨a, ha⟩ := haIJ
        have notIndep_J_a : ¬M.Indep (J ∪ {a}) := sorry
        have hC : ∃ C : Set α, C ⊆ J ∪ {a} ∧ ¬M.Indep C ∧ ∀ C' ⊂ C, M.Indep C' := sorry
        obtain ⟨C, hCJa, C_notIndep, indep_ssub_C⟩ := hC
        have hJE : J ⊆ M.E := fun ⦃a⦄ a_1 => hIE (hJI a_1)
        have haE : {a} ⊆ M.E := Set.singleton_subset_iff.← (hIE (Set.mem_of_mem_diff ha))
        have hCE : C ⊆ M.E := fun _ a_1 => (Set.union_subset hJE haE) (hCJa a_1)
        have haI : {a} ⊆ I := (Set.singleton_subset_iff.← (Set.mem_of_mem_diff ha))
        have hJaI : J ∪ {a} ⊆ I := Set.union_subset hJI haI
        have hCI : C ⊆ I := hCJa.trans hJaI
        unfold IndepPredicate.ToCircuitPredicate Minimal at hI
        push_neg at hI
        specialize hI C hCI ⟨C_notIndep, hCE⟩
        obtain ⟨D, ⟨hDdep, hDE⟩, ⟨hDC, hCD⟩⟩ := hI
        sorry -- todo: finish
      exact J_eq_I ▸ J_indep
  · intro ⟨hIE, I_indep⟩
    constructor
    · exact hIE
    · intro C hCI ⟨⟨C_dep, hCE⟩, hCmin⟩
      exact C_dep (Matroid.Indep.subset I_indep hCI)

end PredicateRelations

section CircuitToIndepAxioms

/-- Independence predicate constructed from circuit predicate satisfies (I1): empty set is independent. -/
lemma CircuitPredicate.toIndepPredicate_indepEmpty {P : CircuitPredicate α}
    (hP : P.NotCircuitEmpty) (E : Set α) :
    (P.toIndepPredicate E).IndepEmpty :=
  ⟨E.empty_subset, fun _ C_empty hC => hP (Set.subset_eq_empty C_empty rfl ▸ hC)⟩

/-- Independence predicate constructed from circuit predicate satisfies (I2): subsets of independent sets are independent. -/
lemma CircuitPredicate.toIndepPredicate_indepSubset (P : CircuitPredicate α) (E : Set α) :
    (P.toIndepPredicate E).IndepSubset := by
  unfold IndepPredicate.IndepSubset
  exact fun I J hJ hIJ => ⟨hIJ.trans hJ.left, fun C hCI hPC => hJ.right C (hCI.trans hIJ) hPC⟩

/-- Independence predicate constructed from circuit predicate satisfies (I3): independent sets have augmentation property. -/
lemma CircuitPredicate.toIndepPredicate_indepAug {P : CircuitPredicate α} {E : Set α}
    (hPCM : P.CircuitMaximal E) (hPC3 : P.BruhnC3) :
    (P.toIndepPredicate E).IndepAug := by
  -- Proof adapted from Bruhn et al., Theorem 4.2 (ii), backward direction
  intro I B hI hInmax hBmax
  sorry -- todo : fix

    -- (hI : P.toIndepPredicate E I)
    -- (hPI : ¬Maximal (P.toIndepPredicate E) I)
    -- (hPI' : Maximal (P.toIndepPredicate E) I')

  -- have hB := hI
  -- apply hPCM at hB
  -- specialize hB hI.1
  -- obtain ⟨B, hIB, hBmax⟩ := hB
  -- simp only [Maximal, Set.le_eq_subset, and_imp] at hBmax
  -- obtain ⟨⟨hBindep, hBground⟩, hBmax⟩ := hBmax

  -- have hIBstrict : I ⊂ B
  -- · rw [Set.ssubset_def]
  --   by_contra! hBI
  --   unfold Maximal at hInmax
  --   push_neg at hInmax
  --   obtain ⟨J, hJindep, hIJ, hnJI⟩ := hInmax hI
  --   have hIJneq : I ≠ J := (ne_of_not_le hnJI).symm
  --   have hBJ : B ⊆ J := (hBI hIB).trans hIJ
  --   rw [hIB.antisymm (hBI hIB), hBJ.antisymm (hBmax hJindep hJindep.1 hBJ)] at hIJneq
  --   exact hIJneq rfl

  -- obtain ⟨z, hzB, hzI⟩ := Set.exists_of_ssubset hIBstrict

  -- if hzI' : z ∈ I' then
  --   exact ⟨z, Set.mem_diff_of_mem hzI' hzI, indep_subset hBindep (Set.insert_subset hzB hIB)⟩
  -- else
  --   have J' := z ᕃ I'
  --   have hJ'ground : J' ⊆ E := Set.insert_subset (hBground hzB) hPI'.1.1
  --   have hJ' : ¬P.toIndepPredicate E J'
  --   · intro hJ'indep
  --     obtain ⟨hI'indep, hI'max⟩ := hPI'
  --     exact hzI' (hI'max hJ'indep (Set.subset_insert z I') (Or.inl rfl))

  --   unfold CircuitPredicate.toIndepPredicate at hJ'
  --   push_neg at hJ'
  --   specialize hJ' hJ'ground
  --   obtain ⟨C, ⟨hCcirc, hCJ'⟩⟩ := hJ'

  --   have X := C \ B
  --   have hXJ' : X ⊆ J' := fun _ x => hCJ' (Set.diff_subset x)
  --   have hzX : z ∉ X := Set.not_mem_diff_of_mem hzB
  --   have hXI' : X ⊆ I' := (Set.subset_insert_iff_of_not_mem hzX).→ hXJ'
  --   have hBX : B ∩ X = ∅ := Set.inter_diff_self B C
  --   have tmp : I ∩ X ⊆ B ∩ X := Set.inter_subset_inter hIB Set.Subset.rfl
  --   have hIX : I ∩ X = ∅ := Set.subset_eq_empty tmp hBX
  --   have hIXsubnone : I ∩ X ⊆ ∅ := Set.subset_empty_iff.← hIX
  --   have hIXdisj : Disjoint I X := Set.disjoint_iff.← hIXsubnone
  --   have hXII' : X ⊆ I' \ I := Set.subset_diff.← ⟨hXI', hIXdisj.symm⟩

  --   by_contra hx
  --   unfold CircuitPredicate.toIndepPredicate at hx
  --   push_neg at hx

  --   have hIxground : ∀ x ∈ E, x ᕃ I ⊆ E := fun x a => Set.insert_subset a (fun _ hxI => hBground (hIB hxI))
  --   have hI'mIground : I' \ I ⊆ E := fun _ hII' => hPI'.1.1 (Set.diff_subset hII')
  --   have hI'mIxground : ∀ x ∈ I' \ I, x ᕃ I ⊆ E := fun x a => hIxground x (hI'mIground a)

  --   have hz : ∀ x ∈ X, z ∉ x ᕃ I
  --   · intro x hxx
  --     have hxI'mI : x ∈ I' \ I := hXII' hxx
  --     have hxIground : x ᕃ I ⊆ E := hIxground x (hJ'ground (hXJ' hxx))
  --     obtain ⟨Cx, ⟨hCx, hCxI⟩⟩ := hx x hxI'mI hxIground
  --     have hzx : z ≠ x := (ne_of_mem_of_not_mem (hXI' hxx) hzI').symm
  --     exact nmem_insert hzx hzI

  --   -- for every `x ∈ X`, take corresponding `C` from `hx` and put it into `F`
  --   have F : ValidFamily P C X := sorry -- todo: construction
  --   have hzxF : ∀ x, F.F x ⊆ (x : α) ᕃ I := sorry -- holds by constructoin
  --   have hzF : z ∈ C \ F.union := sorry -- holds by construction
  --   apply hPC3 at hzF
  --   obtain ⟨C', hC', hzC', hCC'FX⟩ := hzF

  --   have hCxI : ∀ x, F.F x \ X ⊆ I := sorry -- follows from `hzxF`
  --   have hCxB : ∀ x, F.F x \ X ⊆ B := fun x _ hFFxX => hIB (hCxI x hFFxX)
  --   have hCalt : C' ⊆ (C \ X) ∪ Set.iUnion (F.F · \ X) := sorry -- holds by construction of `C'`
  --   have hUB : Set.iUnion (F.F · \ X) ⊆ B := Set.iUnion_subset hCxB
  --   have hCXB : C \ X ⊆ B := Set.diff_subset_comm.→ (fun _ => id)
  --   have hC'exprB : (C \ X) ∪ Set.iUnion (F.F · \ X) ⊆ B := Set.union_subset hCXB hUB
  --   have hC'B : C' ⊆ B := hCalt.trans hC'exprB

  --   -- contradiction: `C'` is a cycle and a subset of an independent set
  --   obtain ⟨hC'ground, hC'nosubcircuit⟩ := indep_subset hBindep hC'B
  --   exact hC'nosubcircuit C' hC' (fun _ => id)

  -- rfl

/-- Independence predicate constructed from circuit predicate satisfies (IM): independent sets have maximal property. -/
lemma CircuitPredicate.toIndepPredicate_indepMaximal (P : CircuitPredicate α) (E : Set α) :
    (P.toIndepPredicate E).IndepMaximal E :=
  sorry

/- Start of proof attempt -/
lemma round1_toIndepPredicate_subsetGround (P : CircuitPredicate α) (E : Set α) :
    (P.toIndepPredicate E).SubsetGround E := by
  intro I hI
  exact hI.1

/-- Independence predicate constructed from circuit predicate satisfies (IE): independent sets are subsets of ground set. -/
theorem CircuitPredicate.toIndepPredicate_subsetGround (P : CircuitPredicate α) (E : Set α) :
    (P.toIndepPredicate E).SubsetGround E  := by

  exact round1_toIndepPredicate_subsetGround P E
