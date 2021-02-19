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
-- notation `Some` R . C := Concept.Ex R C
-- notation `Only` R . C := Concept.Al R C 

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

definition satisfiable (C : Concept AtomicConcept AtomicRole) : Prop :=
  ∃ I : Interpretation AtomicConcept AtomicRole, interp I C ≠ ∅

definition subsumption (C D: Concept AtomicConcept AtomicRole) : Prop :=
  ∀ I : Interpretation AtomicConcept AtomicRole, interp I C ⊆ interp I D

definition equivalence (C D: Concept AtomicConcept AtomicRole) : Prop := 
  subsumption C D ∧ subsumption D C

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

lemma subsum_trans (C D E: Concept AtomicConcept AtomicRole) (cd : (subsumption C D)) (de : subsumption D E) : subsumption C E :=
begin
  dsimp [subsumption, interp] at *,
  intro h,
  -- how to work with forall in hypothesis
  -- hello
  sorry,
end 

end ALC


namespace test

open ALC
open ALC.Concept


inductive ac : Type
 | man : ac
 | woman : ac

inductive ar : Type
 | hasChild : ar

@[reducible]
def ic : ac → set ℕ  
 | ac.man   := ({2,4} : set ℕ)
 | ac.woman := ({1,3} : set ℕ)     

@[reducible]
def ir : ar → set (ℕ × ℕ)
 | ar.hasChild := ({(1,2),(4,3)} : set (ℕ × ℕ))

@[reducible]
def i := Interpretation.mk ℕ ic ir

-- below, the concept is not reduced to {2,4} but to a equivalent λ-term.

#reduce interp i (Concept.Atomic ac.woman)

#reduce interp i (Some (Role.Atomic ar.hasChild) (Concept.Atomic ac.man))


-- instead of 'compute' concepts, let us proof things about the interpretation

example : 
 interp i (Some (Role.Atomic ar.hasChild) (Concept.Atomic ac.man)) = ({1} : set ℕ) :=
begin
 dsimp [interp,r_interp,i],
 rw [ic,ir],
 ext n,  
 apply iff.intro,
 { intro h1, 
   simp at *, 
   apply (exists.elim h1),
   simp, intros a ha hb,
   finish,
 },
 { intros h1,
   norm_num at h1,
   rw h1,
   apply exists.intro 2,
   finish,
 } 
end

-- Mario's proof
example :
  interp i (Every (Role.Atomic ar.hasChild) (Concept.Atomic ac.man)) = ({4}ᶜ : set ℕ) :=
begin
  ext n,
  simp [interp, r_interp, ir, ic],
  split,
  { rintro h rfl,
    have := h 3, revert this,
    norm_num, 
  },
  { rintro h _ (⟨rfl, rfl⟩|⟨rfl, rfl⟩), {norm_num},
    cases h rfl },
end

-- if i, ic and ir were not 'reducible'
example :
  interp i (Every (Role.Atomic ar.hasChild) (Concept.Atomic ac.man)) = ({4}ᶜ : set ℕ) :=
begin
  dsimp [i, interp],
  ext n,
  simp [r_interp, ir],
  split,
  { rintro H rfl,
    have := H 3, revert this,
    norm_num },
  { rintro h _ (⟨rfl, rfl⟩|⟨rfl, rfl⟩), {norm_num},
    cases h rfl },
end

-- a detailed proof
example :
  interp i (Every (Role.Atomic ar.hasChild) (Concept.Atomic ac.man)) = ({4}ᶜ : set ℕ) :=
begin
  ext n,
  simp [interp, r_interp, ir, ic],
  split,
  { rintro h rfl,
    have := h 3, revert this,
    norm_num, 
  },
  { intros h1 a h2,
    cases h2 with h2a h2b,
    exact or.inl h2a.2,
    exfalso, exact h1 h2b.left,
  },
end


-- more general properties of 'interp' should also be provable:

example (a b : Type) (i : Interpretation a b) (c : Concept a b) : interp i (Intersection c (Negation c)) = ∅ := 
begin
  dsimp [interp],
  --rw inter_comm,
  finish,
  --exact set.compl_inter_self (interp i c),
end


example (a b : Type) (i : Interpretation a b) (c : Concept a b) : interp i (Union c (Negation c)) = univ := 
begin
  dsimp [interp],
  exact set.union_compl_self (interp i c),
end

-- see https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/non.20empty.20set.20in.20a.20structure

example (a b : Type) (C : Concept a b) : satisfiable (Union (Negation C) C) :=
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

example (a b : Type) (C : Concept a b) : ¬ satisfiable (Intersection (Negation C) C) := 
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



-- detailed proofs for the steps closed with 'finish' above.

example (h : 1 = 4) : false := 
begin
 -- if succ 0 = succ 3 then 0 = 3 because succ is injective
 have h1 := (nat.succ_injective h),
 apply nat.succ_ne_zero _ h1.symm, 
end


example (n a : ℕ) (ha : n = 1 ∧ a = 2 ∨ n = 4 ∧ a = 3)
  (hb : a = 2 ∨ a = 4) : n = 1 := 
begin
 by_contradiction,
 cases hb with hb1 hb2,
 cases ha with ha1 ha2,
 exact h ha1.1, 
 have hx := and.intro ha2.2 hb1,
 finish,
 finish,
end

end test
