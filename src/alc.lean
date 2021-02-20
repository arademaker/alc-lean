import data.set 
open set

/-!

# Goal

We want to proof that the SC defined in the thesis is sound and
complete. In this file, ACL syntax and semantics are defined.

# References

- DL Prime: https://arxiv.org/abs/1201.4089v3
- http://arademaker.github.io/bibliography/phdthesis-4.html

-/

namespace ALC

inductive Role (AtomicRole : Type) : Type
  | Atomic : AtomicRole → Role

inductive Concept (AtomicConcept AtomicRole : Type) : Type 
  | TopConcept    : Concept
  | BottomConcept : Concept
  | Atomic        : AtomicConcept → Concept
  | Negation      : Concept → Concept
  | Intersection  : Concept → Concept → Concept
  | Union         : Concept → Concept → Concept
  | Some          : (Role AtomicRole) → Concept → Concept
  | Every         : (Role AtomicRole) → Concept → Concept

open Concept Role

-- notation        `⊤` := Concept.TopConcept    -- \top
-- notation        `⊥` := Concept.BottomConcept -- \bot
-- prefix          `¬` := Concept.Negation      -- \neg
-- infix       `⊓` :51 := Concept.Intersection  -- \sqcap
-- infix       `⊔` :51 := Concept.Union         -- \sqcup
-- notation `Some` R . C := Concept.Ex R C -- (it would be nice to use `∃ R. C`)
-- notation `Only` R . C := Concept.Al R C -- (it would be nice to use `∀ R. C`)
-- infix `⊑` : 50 := subsumption -- \sqsubseteq
-- infix `≡` : 50 := equivalence -- \==


-- interpretation structure 
structure Interpretation (AtomicConcept AtomicRole : Type) := 
mk :: (δ : Type) 
      [nonempty : nonempty δ]
      (atom_C   : AtomicConcept → set δ)
      (atom_R   : AtomicRole → set (δ × δ))

variables {AtomicConcept AtomicRole : Type}

-- role interpretation
definition r_interp (I : Interpretation AtomicConcept AtomicRole) : Role AtomicRole → set (I.δ × I.δ)  
  | (Role.Atomic R) := I.atom_R R

-- concept interpretation
definition interp (I : Interpretation AtomicConcept AtomicRole) : Concept AtomicConcept AtomicRole → set I.δ 
 | TopConcept           := univ
 | BottomConcept        := ∅ 
 | (Atomic C)           := I.atom_C C
 | (Negation C)         := compl (interp C)
 | (Intersection C1 C2) := (interp C1) ∩ (interp C2)
 | (Union C1 C2)        := (interp C1) ∪ (interp C2)
 | (Some R C)           := { a: I.δ | ∃ b : I.δ, 
                            (a, b) ∈ (r_interp I R) ∧ b ∈ (interp C) }
 | (Every R C)          := { a: I.δ | ∀ b : I.δ,
                            (a, b) ∈ (r_interp I R) → b ∈ (interp C) }


-- more general properties of 'interp' should also be provable:

lemma interp_inter_neg_empty (a b : Type) (i : Interpretation a b) (c : Concept a b) : 
 interp i (Intersection c (Negation c)) = ∅ := 
begin
  dsimp [interp],
  --rw inter_comm,
  finish,
  --exact set.compl_inter_self (interp i c),
end


lemma interp_union_neq_univ (a b : Type) (i : Interpretation a b) (c : Concept a b) : 
 interp i (Union c (Negation c)) = univ := 
begin
  dsimp [interp],
  exact set.union_compl_self (interp i c),
end


def satisfiable (C : Concept AtomicConcept AtomicRole) : Prop :=
  ∃ I : Interpretation AtomicConcept AtomicRole, interp I C ≠ ∅

def subsumption (C D: Concept AtomicConcept AtomicRole) : Prop :=
  ∀ I : Interpretation AtomicConcept AtomicRole, interp I C ⊆ interp I D

def equivalence (C D: Concept AtomicConcept AtomicRole) : Prop := 
  subsumption C D ∧ subsumption D C


-- see https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/non.20empty.20set.20in.20a.20structure

lemma sat_union_neq (a b : Type) (C : Concept a b) : satisfiable (Union (Negation C) C) :=
begin
  dsimp [satisfiable, interp],
  let i : Interpretation a b := { Interpretation . 
    δ := ℕ, 
    nonempty :=  ⟨0⟩, 
    atom_C := (λ x : a, ∅), 
    atom_R := (λ x : b, ∅) },
  existsi i,
  rw set.union_comm,
  rw set.union_compl_self,
  
  -- option 1
  -- exact empty_ne_univ.symm,
  
  -- option 2
  -- simp at *, 
  
  -- option 3
  -- apply empty_ne_univ.symm, exact i.nonempty,
  
  rw set.univ_eq_empty_iff,
  rw not_not,
  exact i.nonempty,
end


lemma not_sat_inter_neg (a b : Type) (C : Concept a b) : ¬ satisfiable (Intersection (Negation C) C) := 
begin
  dsimp [satisfiable,interp],
  -- don't even need to instatiate
  -- goal accomplished with only norm_num
  let i : Interpretation a b := { Interpretation . 
    δ := ℕ, 
    nonempty :=  ⟨0⟩, 
    atom_C := (λ x : a, ∅), 
    atom_R := (λ x : b, ∅) },
  intro hk0,
  cases hk0 with hk1 hk2,
  simp at hk2,
  exact hk2,
end


lemma inter_subsum_left (C D: Concept AtomicConcept AtomicRole) : subsumption (Intersection C D) C  :=
begin
  dsimp [subsumption, interp],
  intro h,
  exact inter_subset_left (interp h C) (interp h D),
end


lemma inter_subsum_right (C D: Concept AtomicConcept AtomicRole) : subsumption (Intersection C D) D  :=
begin
  dsimp [subsumption, interp],
  intro h,
  exact inter_subset_right (interp h C) (interp h D),
end


lemma subsum_union_left (C D : Concept AtomicConcept AtomicRole) : subsumption C (Union C D) :=
begin
  dsimp [subsumption, interp],
  intro h,
  exact subset_union_left (interp h C) (interp h D),
end


lemma subsum_union_right (C D : Concept AtomicConcept AtomicRole) : subsumption D (Union C D) :=
begin
  dsimp [subsumption, interp],
  intro h,
  exact subset_union_right (interp h C) (interp h D),
end


lemma subsum_trans (C D E: Concept AtomicConcept AtomicRole) (cd : (subsumption C D)) (de : subsumption D E) : 
  subsumption C E :=
begin
  dsimp [subsumption, interp] at *,
  intro h,
  have h1 : interp h C ⊆ interp h D, from cd h,
  have h2 : interp h D ⊆ interp h E, from de h,
  exact (subset.trans h1 h2),
end 

/- 
1. all concepts C is equivalent to itself
2. all concepts C \sqsubseteq (subsubmise) ifself
-/

end ALC
