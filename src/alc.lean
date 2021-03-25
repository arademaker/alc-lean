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
  | Atomic  : AtomicRole → Role
  | Compose : Role → Role → Role
  | Inverse : Role → Role

inductive Concept (AtomicConcept AtomicRole : Type) : Type 
  | Top           : Concept
  | Bot           : Concept
  | Atomic        : AtomicConcept → Concept
  | Negation      : Concept → Concept
  | Intersection  : Concept → Concept → Concept
  | Union         : Concept → Concept → Concept
  | Some          : (Role AtomicRole) → Concept → Concept
  | Every         : (Role AtomicRole) → Concept → Concept

open Concept Role

attribute [pattern] has_inf.inf has_sup.sup has_top.top has_bot.bot

instance concept_has_top (AtomicConcept AtomicRole : Type) : 
 has_top (Concept AtomicConcept AtomicRole) := ⟨ Concept.Top ⟩ 

instance concept_has_bot (AtomicConcept AtomicRole : Type) : 
 has_bot (Concept AtomicConcept AtomicRole) := ⟨ Concept.Bot ⟩ 

instance concept_has_inf (AtomicConcept AtomicRole : Type) : 
 has_inf (Concept AtomicConcept AtomicRole) := ⟨ Concept.Intersection ⟩

instance concept_has_sup (AtomicConcept AtomicRole : Type) : 
 has_sup (Concept AtomicConcept AtomicRole) := ⟨ Concept.Union ⟩


-- local infix     `⊓` : 55 := Concept.Intersection  -- \sqcap
-- local infix     `⊔` : 55 := Concept.Union         -- \sqcup
-- notation        `⊤` := Concept.TopConcept    -- \top
-- notation        `⊥` := Concept.BottomConcept -- \bot
prefix          `¬ₐ` : 55 := Concept.Negation
notation `Ex` R `:` C := Concept.Some R C  -- (it would be nice to use `∃ R. C`)
notation `Ax` R `:` C := Concept.Every R C -- (it would be nice to use `∀ R. C`)


structure Interpretation (AtomicConcept AtomicRole : Type) := 
mk :: (δ : Type) 
      [nonempty : nonempty δ]
      (atom_C   : AtomicConcept → set δ)
      (atom_R   : AtomicRole → set (δ × δ))

variables {AtomicConcept AtomicRole : Type}


-- role interpretation
def r_interp (I : Interpretation AtomicConcept AtomicRole) : Role AtomicRole → set (I.δ × I.δ)  
  | (Role.Atomic R)    := I.atom_R R
  | (Role.Inverse R)   := { d | ∀ x: I.δ × I.δ, x ∈ (r_interp R) → d.1 = x.2 ∧ d.2 = x.1 }
  | (Role.Compose R S) := { d | ∀ x y : I.δ × I.δ, x ∈ (r_interp R) ∧ y ∈ (r_interp R) ∧ 
                                  x.2 = y.1 → d.1 =  x.1 ∧ d.2 = y.2 }

-- concept interpretation
def interp (I : Interpretation AtomicConcept AtomicRole) : Concept AtomicConcept AtomicRole → set I.δ 
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

lemma interp_inter_neg_empty (a b : Type) (i : Interpretation a b) (c : Concept a b) : 
 interp i (c ⊓ (¬ₐ c)) = ∅ := 
begin
  dsimp [interp],
  --rw inter_comm,
  finish,
  --exact set.compl_inter_self (interp i c),
end

lemma interp_union_neq_univ (a b : Type) (i : Interpretation a b) (c : Concept a b) : 
 interp i (c ⊔ (¬ₐ c)) = univ := 
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


local infix ` ⊑  ` : 50 := subsumption
local infix ` ≡  ` : 50 := equivalence

inductive Statement {AC AR : Type} : Type
  | Subsumption : Concept AC AR → Concept AC AR → Statement
  | Equivalence : Concept AC AR → Concept AC AR → Statement

-- Created another operator with a different syntax as the polymorphic instance would not be able
-- to differentiate beetween the two. Both take Concept AC AR in two instances.


local infix ` ⊑ₛ ` : 50 := Statement.Subsumption -- \sqsubseteq
local infix ` ≡ₛ ` : 50 := Statement.Equivalence -- \==


definition interp_stmt {AC AR : Type} (I : Interpretation AC AR) : @Statement AC AR → Prop
  | (Statement.Subsumption C D) := interp I C ⊆ interp I D
  | (Statement.Equivalence C D) := interp I C = interp I D


def sat_concept_tbox {AC AR : Type} (tbox : set (@Statement AC AR)) (a : @Statement AC AR) : Prop :=
  ∃ I : Interpretation AC AR,
    (∀ c ∈ tbox, (interp_stmt I c)) → (interp_stmt I a)

example (ac ar : Type) (A B C : Concept ac ar) : sat_concept_tbox { A ⊑ₛ B , B ⊑ₛ C } (A ⊑ₛ C) := 
begin
 unfold sat_concept_tbox,
 let i : Interpretation ac ar := { Interpretation . 
    δ := ℕ, 
    nonempty :=  ⟨0⟩, 
    atom_C := (λ x : ac, ∅), 
    atom_R := (λ x : ar, ∅) },
 existsi i,
 intro h1,
 have ha := h1 (A ⊑ₛ B),simp at ha,
 have hb := h1 (B ⊑ₛ C), simp at hb,
 unfold interp_stmt at *,
 exact (subset.trans ha hb),
end

-- see https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/non.20empty.20set.20in.20a.20structure

lemma sat_union_neq {a b : Type} (C : Concept a b) : satisfiable ((¬ₐ C) ⊔ C) :=
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


lemma not_sat_inter_neg {a b : Type} (C : Concept a b) : ¬ satisfiable ((¬ₐ C) ⊓ C) := 
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


lemma inter_subsum_left (C D: Concept AtomicConcept AtomicRole) : (C ⊓ D) ⊑ C  :=
begin
  dsimp [subsumption, interp],
  intro h,
  exact inter_subset_left (interp h C) (interp h D),
end


lemma inter_subsum_right (C D: Concept AtomicConcept AtomicRole) : (C ⊓ D) ⊑ D  :=
begin
  dsimp [subsumption, interp],
  intro h,
  exact inter_subset_right (interp h C) (interp h D),
end


lemma subsum_union_left (C D : Concept AtomicConcept AtomicRole) : C ⊑ (C ⊔ D) :=
begin
  dsimp [subsumption, interp],
  intro h,
  exact subset_union_left (interp h C) (interp h D),
end


lemma subsum_union_right (C D : Concept AtomicConcept AtomicRole) : D ⊑ (C ⊔ D) :=
begin
  dsimp [subsumption, interp],
  intro h,
  exact subset_union_right (interp h C) (interp h D),
end

lemma subsum_refl (C : Concept AtomicConcept AtomicRole) : C ⊑ C :=
begin
  dsimp [subsumption, interp],
  intro h,
  exact subset.refl (interp h C), 
end

lemma subsum_trans {C D E: Concept AtomicConcept AtomicRole} (cd : C ⊑ D) (de : D ⊑ E) : 
   C ⊑ E :=
begin
  dsimp [subsumption, interp] at *,
  intro h,
  have h1 : interp h C ⊆ interp h D, from cd h,
  have h2 : interp h D ⊆ interp h E, from de h,
  exact (subset.trans h1 h2),
end 

lemma subsum_antisymm {C D : Concept AtomicConcept AtomicRole} (cd : C ⊑  D) (dc : D ⊑  C) : C ≡ D :=
begin
  dsimp[subsumption,equivalence,interp] at *,
  split,
  intro h, exact cd h,
  intro h, exact dc h,
end 

lemma equiv_refl (C : Concept AtomicConcept AtomicRole) : C ≡ C :=
begin
  dsimp [equivalence, interp],
  split,
  exact subsum_refl C, exact subsum_refl C,
end

-- Statement lemmas

lemma equiv_stat_refl {AC AR : Type} (I : Interpretation AC AR) (C : Concept AC AR) : interp_stmt I (C ≡ₛ C) :=
begin
  unfold interp_stmt,
end

lemma subsum_stat_refl {AC AR : Type} (I : Interpretation AC AR) (C : Concept AC AR) : interp_stmt I (C ⊑ₛ C) :=
begin
  unfold interp_stmt,
end

lemma subsum_stat_trans {AC AR : Type} {I : Interpretation AC AR} {C D E: Concept AC AR} (cd : interp_stmt I (C ⊑ₛ D)) (de : interp_stmt I (D ⊑ₛ E)) : 
   interp_stmt I (C ⊑ₛ E) :=
begin
  unfold interp_stmt at *,
  exact subset.trans cd de,
end 

lemma subsum_stat_antisym {AC AR : Type} {I: Interpretation AC AR} {C D: Concept AC AR} (cd : interp_stmt I (C ⊑ₛ D)) (dc : interp_stmt I (D ⊑ₛ C)) :
  interp_stmt I (C ≡ₛ D) :=
begin
  unfold interp_stmt at *,
  rw subset.antisymm_iff,
  exact ⟨cd,dc⟩,
end



end ALC
