import alc

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


example (α : Type*) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
begin
 intros h x,
 exact (h x).1,
end

end test
