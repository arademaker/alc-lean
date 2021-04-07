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

@[reducible]
definition VarConcept := nat

@[reducible]
definition VarRole := nat

meta def print {α} [has_reflect α] (e : α) : tactic unit :=
 tactic.pp (reflect e) >>= tactic.trace

@[derive has_reflect]
inductive Role : Type
  | Atomic  : VarRole → Role
  | Compose : Role → Role → Role
  | Inverse : Role → Role

@[derive has_reflect]
inductive Concept : Type 
  | Top           : Concept
  | Bot           : Concept
  | Atomic        : VarConcept → Concept
  | Negation      : Concept → Concept
  | Intersection  : Concept → Concept → Concept
  | Union         : Concept → Concept → Concept
  | Some          : Role → Concept → Concept
  | Every         : Role → Concept → Concept

notation `R#`:max P:max := Role.Atomic P
notation `C#`:max P:max := Concept.Atomic P

open Concept Role

attribute [pattern] has_inf.inf has_sup.sup has_top.top has_bot.bot

instance concept_has_top: 
 has_top Concept := ⟨ Concept.Top ⟩ 

instance concept_has_bot : 
 has_bot Concept := ⟨ Concept.Bot ⟩ 

instance concept_has_inf : 
 has_inf Concept := ⟨ Concept.Intersection ⟩

instance concept_has_sup : 
 has_sup Concept := ⟨ Concept.Union ⟩


-- local infix     `⊓` : 55 := Concept.Intersection  -- \sqcap
-- local infix     `⊔` : 55 := Concept.Union         -- \sqcup
-- notation        `⊤` := Concept.TopConcept    -- \top
-- notation        `⊥` := Concept.BottomConcept -- \bot
prefix          `¬ₐ` : 55 := Concept.Negation
notation `Ex` R `:` C := Concept.Some R C  -- (it would be nice to use `∃ R. C`)
notation `Ax` R `:` C := Concept.Every R C -- (it would be nice to use `∀ R. C`)


-- I am not sure about this. We are mapping VarConcept to a set. This
-- is because we don't have a type for atomic roles?

structure Interpretation := 
mk :: (δ : Type) 
      [nonempty : nonempty δ]
      (atom_C   : VarConcept → set δ)
      (atom_R   : VarRole → set (δ × δ))

variables {AtomicConcept AtomicRole : Type}


-- role interpretation
def r_interp (I : Interpretation) : Role → set (I.δ × I.δ)  
  | (Role.Atomic R)    := I.atom_R R
  | (Role.Inverse R)   := { d | ∀ x: I.δ × I.δ, x ∈ (r_interp R) → d.1 = x.2 ∧ d.2 = x.1 }
  | (Role.Compose R S) := { d | ∀ x y : I.δ × I.δ, x ∈ (r_interp R) ∧ y ∈ (r_interp R) ∧ 
                                  x.2 = y.1 → d.1 =  x.1 ∧ d.2 = y.2 }

-- concept interpretation
def interp (I : Interpretation) : Concept → set I.δ 
 | ⊤            := univ
 | ⊥            := ∅ 
 | (Atomic C)   := I.atom_C C
 | (¬ₐ C)       := compl (interp C)
 | (C1 ⊓ C2)    := (interp C1) ∩ (interp C2) 
 | (C1 ⊔ C2)    := (interp C1) ∪ (interp C2)
 | Ex R : C     := { a: I.δ | ∃ b : I.δ, 
                     (a, b) ∈ (r_interp I R) ∧ b ∈ (interp C) }
 | Ax R : C     := { a: I.δ | ∀ b : I.δ,
                     (a, b) ∈ (r_interp I R) → b ∈ (interp C) }
 

-- more general properties of 'interp' should also be provable:

lemma interp_inter_neg_empty (i : Interpretation) (c : Concept) : 
 interp i (c ⊓ (¬ₐ c)) = ∅ := 
begin
  dsimp [interp],
  --rw inter_comm,
  finish,
  --exact set.compl_inter_self (interp i c),
end

lemma interp_union_neq_univ (i : Interpretation) (c : Concept) : 
 interp i (c ⊔ (¬ₐ c)) = univ := 
begin
  dsimp [interp],
  exact set.union_compl_self (interp i c),
end

def satisfiable (C : Concept) : Prop :=
  ∃ I : Interpretation, interp I C ≠ ∅

def subsumption (C D: Concept) : Prop :=
  ∀ I : Interpretation, interp I C ⊆ interp I D

def equivalence (C D: Concept) : Prop := 
  subsumption C D ∧ subsumption D C


local infix ` ⊑  ` : 50 := subsumption
local infix ` ≡  ` : 50 := equivalence

inductive Statement : Type
  | Subsumption : Concept → Concept → Statement
  | Equivalence : Concept → Concept → Statement

-- Created another operator with a different syntax as the polymorphic instance would not be able
-- to differentiate beetween the two. Both take Concept AC AR in two instances.


local infix ` ⊑ₛ ` : 50 := Statement.Subsumption -- \sqsubseteq
local infix ` ≡ₛ ` : 50 := Statement.Equivalence -- \==


definition interp_stmt (I : Interpretation) : Statement → Prop
  | (Statement.Subsumption C D) := interp I C ⊆ interp I D
  | (Statement.Equivalence C D) := interp I C = interp I D


def satisfies (I : Interpretation) (tbox : list Statement) : Prop :=
    (∀ c ∈ tbox, (interp_stmt I c)) 

def models (tbox : list Statement) (a : Statement) : Prop :=
  ∀ I : Interpretation, satisfies I tbox → (interp_stmt I a)


example (A B C : Concept) : models [A ⊑ₛ B, B ⊑ₛ C] (A ⊑ₛ C) := 
begin
 unfold models,
 intro h1,
 unfold interp_stmt,
 unfold satisfies,
 intro S, simp at S,
 unfold interp_stmt at S, exact subset.trans S.1 S.2,
end

-- see https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/non.20empty.20set.20in.20a.20structure

lemma sat_union_neq (C : Concept) : satisfiable ((¬ₐ C) ⊔ C) :=
begin
  dsimp [satisfiable, interp],
  let i : Interpretation  := { Interpretation . 
    δ := ℕ, 
    nonempty :=  ⟨0⟩, 
    atom_C := (λ x : VarConcept, ∅), 
    atom_R := (λ x : VarRole, ∅) },
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


lemma not_sat_inter_neg (C : Concept) : ¬ satisfiable ((¬ₐ C) ⊓ C) := 
begin
  dsimp [satisfiable,interp],
  -- don't even need to instatiate
  -- goal accomplished with only norm_num
  let i : Interpretation := { Interpretation . 
    δ := ℕ, 
    nonempty :=  ⟨0⟩, 
    atom_C := (λ x : VarConcept, ∅), 
    atom_R := (λ x : VarRole, ∅) },
  intro hk0,
  cases hk0 with hk1 hk2,
  simp at hk2,
  exact hk2,
end


lemma inter_subsum_left (C D: Concept) : (C ⊓ D) ⊑ C  :=
begin
  dsimp [subsumption, interp],
  intro h,
  exact inter_subset_left (interp h C) (interp h D),
end


lemma inter_subsum_right (C D: Concept) : (C ⊓ D) ⊑ D  :=
begin
  dsimp [subsumption, interp],
  intro h,
  exact inter_subset_right (interp h C) (interp h D),
end


lemma subsum_union_left (C D : Concept) : C ⊑ (C ⊔ D) :=
begin
  dsimp [subsumption, interp],
  intro h,
  exact subset_union_left (interp h C) (interp h D),
end


lemma subsum_union_right (C D : Concept) : D ⊑ (C ⊔ D) :=
begin
  dsimp [subsumption, interp],
  intro h,
  exact subset_union_right (interp h C) (interp h D),
end

lemma subsum_refl (C : Concept) : C ⊑ C :=
begin
  dsimp [subsumption, interp],
  intro h,
  exact subset.refl (interp h C), 
end

lemma subsum_trans {C D E: Concept} (cd : C ⊑ D) (de : D ⊑ E) : 
   C ⊑ E :=
begin
  dsimp [subsumption, interp] at *,
  intro h,
  have h1 : interp h C ⊆ interp h D, from cd h,
  have h2 : interp h D ⊆ interp h E, from de h,
  exact (subset.trans h1 h2),
end 

lemma subsum_antisymm {C D : Concept} (cd : C ⊑  D) (dc : D ⊑  C) : C ≡ D :=
begin
  dsimp[subsumption,equivalence,interp] at *,
  split,
  intro h, exact cd h,
  intro h, exact dc h,
end 

lemma equiv_refl (C : Concept) : C ≡ C :=
begin
  dsimp [equivalence, interp],
  split,
  exact subsum_refl C, exact subsum_refl C,
end

-- Statement lemmas

lemma equiv_stat_refl (I : Interpretation) (C : Concept) : interp_stmt I (C ≡ₛ C) :=
begin
  unfold interp_stmt,
end

lemma subsum_stat_refl (I : Interpretation) (C : Concept) : interp_stmt I (C ⊑ₛ C) :=
begin
  unfold interp_stmt,
end

lemma subsum_stat_trans {I : Interpretation} {C D E: Concept} (cd : interp_stmt I (C ⊑ₛ D)) 
   (de : interp_stmt I (D ⊑ₛ E)) : 
   interp_stmt I (C ⊑ₛ E) :=
begin
  unfold interp_stmt at *,
  exact subset.trans cd de,
end 

lemma subsum_stat_antisym {AC AR : Type} {I: Interpretation} {C D: Concept} 
  (cd : interp_stmt I (C ⊑ₛ D)) (dc : interp_stmt I (D ⊑ₛ C)) :
  interp_stmt I (C ≡ₛ D) :=
begin
  unfold interp_stmt at *,
  rw subset.antisymm_iff,
  exact ⟨cd,dc⟩,
end

end ALC
