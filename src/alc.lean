
import data.set 
open set

namespace ALC

structure AtomicRole :=
 (id : string)

structure AtomicConcept := 
 (id : string)

#check { AtomicRole . id := "hasChild"}

#check ({ id := "hasChild" } : AtomicRole)

inductive Role : Type
  | Atomic : AtomicRole → Role

inductive Concept : Type 
  | TopConcept    : Concept
  | BottomConcept : Concept
  | Atomic        : AtomicConcept → Concept
  | Negation      : Concept → Concept
  | Intersection  : Concept → Concept → Concept
  | Union         : Concept → Concept → Concept
  | Some          : Role → Concept → Concept
  | Every         : Role → Concept → Concept

open Concept Role

-- notation        `⊤` := Concept.TopConcept    -- \top
-- notation        `⊥` := Concept.BottomConcept -- \bot
-- prefix          `¬` := Concept.Negation      -- \neg
-- infix       `⊓` :51 := Concept.Intersection  -- \sqcap
-- infix       `⊔` :51 := Concept.Union         -- \sqcup
-- notation `Some` R . C := Concept.Ex R C
-- notation `Only` R . C := Concept.Al R C 

-- interpretation structure 
structure Interpretation := 
mk :: (δ : Type) 
      (atom_C : AtomicConcept → set δ)
      (atom_R : AtomicRole → set (δ × δ))

variables {AtomicConcept AtomicRole : Type}

-- role interpretation
definition r_interp (I : Interpretation) : Role → set (I.δ × I.δ)  
  | (Role.Atomic R) := I.atom_R R

-- concept interpretation
definition interp (I : Interpretation) : Concept → set I.δ 
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

end ALC


namespace test

open ALC
open ALC.Concept


@[reducible]
def ic : AtomicConcept → set ℕ  
 | { id := "man" }   := ({2,4} : set ℕ)
 | { id := "woman" } := ({1,3} : set ℕ)     
 | _ := ∅ 

@[reducible]
def ir : AtomicRole → set (ℕ × ℕ)
 | { id := "hasChild" } := ({(1,2),(4,3)} : set (ℕ × ℕ))
 | _ := ∅ 

@[reducible]
def i := Interpretation.mk ℕ ic ir

#check Concept.Atomic { id := "man" }

#reduce interp i (Concept.Atomic { id := "man"})

-- ∀ hasChild.man (the concept of all things such that all its fillers
-- for the role 'hasChild' are of type 'man')


#reduce interp i (Every (Role.Atomic { id := "hasChild"}) (Concept.Atomic { id := "man"}))


example : 
 interp i (Every (Role.Atomic {id := "hasChild"}) (Concept.Atomic {id := "man"})) = ({1} : set ℕ) :=
begin
 ext n,  
 apply iff.intro,
 intro h1, 
 dsimp [interp,r_interp,i] at h1, 
 have h2 := h1 1,
 
end


end test


/- References:

DL Prime: https://arxiv.org/abs/1201.4089v3

-/

