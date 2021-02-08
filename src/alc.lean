import data.set data.finset
open set


namespace ALC

constants AtomicConcept AtomicRole : Type

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

-- role interpretation
definition r_interp {I : Interpretation} : Role → set (I.δ × I.δ)  
  | (Role.Atomic R) := I.atom_R R

-- concept interpretation
definition interp {I : Interpretation} : Concept → set I.δ 
 | TopConcept           := univ
 | BottomConcept        := ∅ 
 | (Atomic C)           := I.atom_C C
 | (Negation C)         := compl (interp C)
 | (Intersection C1 C2) := (interp C1) ∩ (interp C2)
 | (Union C1 C2)        := (interp C1) ∪ (interp C2)
 | (Some R C)           := { a: I.δ | ∃ b : I.δ, 
                            (a, b) ∈ (@r_interp I R) ∧ b ∈ (interp C) }
 | (Every R C)          := { a: I.δ | ∀ b : I.δ,
                            (a, b) ∈ (@r_interp I R) → b ∈ (interp C) }

end ALC


namespace test
open ALC

inductive AtomicConcept : Type
 | man : AtomicConcept
 | woman : AtomicConcept

def iconcept : AtomicConcept → set ℕ  
 | man   := ({2,4} : finset ℕ)
 | woman := ({1,3} : finset ℕ)

def irole : AtomicRole → set ℕ × ℕ
 | hasChild := ({(1,2),(2,4)} : finset ℕ × ℕ)

def i := Interpretation ℕ iconcept irole

#check i

end test

/- TODO:
1. verificar erro acima (e.g. https://www.youtube.com/watch?v=qlJrCtYiEkI&t=800s)
2. um exemplo! Criar termos para um exemplo
-/

