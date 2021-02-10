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


-- Berlow, the concept is not reduced to {2,4} but to a equivalent term.

#reduce interp i (Concept.Atomic ac.man)

#reduce interp i (Every (Role.Atomic ar.hasChild) (Concept.Atomic ac.man))


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

-- if i, ic and ir are not 'reducible'
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


example : 
 interp i (Every (Role.Atomic ar.hasChild) (Concept.Atomic ac.man)) = ({1,2,3} : set ℕ)  
  := sorry

-- more general properties of 'interp' should also be provable:

example (a b : Type) (i : Interpretation a b) (c : Concept a b) : 
  interp i (Intersection c (Negation c)) = ∅ := sorry


example (a b : Type) (i : Interpretation a b) (c : Concept a b) : 
  interp i (Union c (Negation c)) = univ := sorry


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
 sorry,  
end

end test

