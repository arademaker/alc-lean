
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
      (atom_C : AtomicConcept → set δ)
      (atom_R : AtomicRole → set (δ × δ))


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

#check @Concept.Atomic _ ar ac.man

#reduce interp i (Concept.Atomic ac.man)

-- ∀ hasChild.man (the concept of all things such that all its fillers
-- for the role 'hasChild' are of type 'man')

#reduce interp i (Every (Role.Atomic ar.hasChild) (Concept.Atomic ac.man))


example : 
 interp i (Every (Role.Atomic ar.hasChild) (Concept.Atomic ac.man)) = ({1} : set ℕ) :=
begin
 ext n,  
 apply iff.intro,
 { intro h1, 
   dsimp [interp,r_interp,i] at h1, 
   -- have h2 := h1 2,
   -- norm_num, dsimp at *,
   rw [ic,ir] at h1, 
   dsimp at *, norm_num, 
   have h2 := h1 2,
   sorry, },

 { intros h1 n2,
   dsimp [interp,r_interp,i],
   rw [ic,ir],
   norm_num at h1,
   intro h3,
   rw h1 at h3,  
   simp at *, left, 
   cases h3 with ha hb, exact ha, exfalso,   
   have hb1 := hb.1,
   finish, -- what?
 }
end

end test


/- References:

DL Prime: https://arxiv.org/abs/1201.4089v3

-/
