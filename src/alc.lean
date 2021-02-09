import data.set 
open set


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
  | Some          : Role AtomicRole → Concept → Concept
  | Every         : Role AtomicRole → Concept → Concept

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
      (atom_C : AtomicConcept → set δ)
      (atom_R : AtomicRole → set (δ × δ))

variables {AtomicConcept AtomicRole : Type}

-- role interpretation
definition r_interp {I : Interpretation AtomicConcept AtomicRole} : 
 Role AtomicRole → set (I.δ × I.δ)  
  | (Role.Atomic R) := I.atom_R R

-- concept interpretation
definition interp {I : Interpretation AtomicConcept AtomicRole} : 
  Concept AtomicConcept AtomicRole → set I.δ 
 | TopConcept           := univ
 | BottomConcept        := ∅ 
 | (Atomic C)           := I.atom_C C
 | (Negation C)         := compl (interp C)
 | (Intersection C1 C2) := (interp C1) ∩ (interp C2)
 | (Union C1 C2)        := (interp C1) ∪ (interp C2)
 | (Some R C)           := { a: I.δ | ∃ b : I.δ, 
                            (a, b) ∈ (@r_interp _ _ I R) ∧ b ∈ (interp C) }
 | (Every R C)          := { a: I.δ | ∀ b : I.δ,
                            (a, b) ∈ (@r_interp _ _ I R) → b ∈ (interp C) }

end ALC


namespace test

open ALC
open ALC.Concept

inductive ac : Type
 | man : ac
 | woman : ac

inductive ar : Type
 | hasChild : ar

open ac 
open ar

def ic : ac → set ℕ  
 | man   := ({2,4} : set ℕ)
 | woman := ({1,3} : set ℕ)     

def ir : ar → set (ℕ × ℕ)
 | hasChild := ({(1,2),(4,3)} : set (ℕ × ℕ))

def i := Interpretation.mk ℕ ic ir


#check Concept.Atomic man 


-- ∀ hasChild.man (the concept of all things such that all its fillers
-- for the role 'hasChild' are of type 'man')

#reduce @interp ac ar i (Every (Role.Atomic hasChild) (Concept.Atomic man))

#reduce interp (Every (Role.Atomic hasChild) (Concept.Atomic man))

end test

/- References:

- DL Prime: https://arxiv.org/abs/1201.4089v3
-/

