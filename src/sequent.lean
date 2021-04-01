import alc
import data.multiset

open ALC
open ALC.Concept

-- the labeled concepts 

inductive Label : Type
  | Forall : Role  → Label
  | Exists : Role  → Label

structure LConcept : Type :=
mk :: (roles : list Label)
      (concept : Concept)

open LConcept
open Label

def isAx : Label → Prop
 | (Forall _) := true
 | (Exists _) := false

def isEx : Label → Prop
 | (Forall _) := false
 | (Exists _) := true

def every {a : Type} : (a → Prop) → (list a) → Prop 
 | f []      := true
 | f (x::xs) := (f x) ∧ (every f xs) 

def negLabel : list Label → list Label
  | [] := []
  | ((Forall a)::L) := Exists a :: negLabel L
  | ((Exists a)::L) := Forall a :: negLabel L
 

#check (⟨[Forall R#0, Exists R#1], (Concept.Bot)⟩ : LConcept)


open LConcept
open Label

def sigma_aux : list Label -> Concept -> Concept 
 | []                 c := c
 | ((Forall r) :: ls) c := Every r (sigma_aux ls c)
 | ((Exists r) :: ls) c := Some r (sigma_aux ls c)

def sigma' : LConcept -> Concept
 | ⟨ roles , concept ⟩ := sigma_aux roles concept

#reduce sigma' (⟨[Forall R#0, Exists R#1], (Concept.Bot)⟩)


-- sequent calculus for ALC 

structure Sequent : Type :=
mk :: (lhs : list LConcept)
      (rhs : list LConcept)

local infix ` ⇒ `:51 := Sequent.mk -- \=> 

#check [LConcept.mk [Forall R#0] (Concept.Bot)] ⇒ [LConcept.mk [Forall R#0, Exists R#1] (Concept.Bot)]


#check list.map (λ x, LConcept.mk (Forall R#1 :: LConcept.roles x) (x.concept)) [LConcept.mk [Forall R#0] (Concept.Bot)]


inductive proof : list Sequent → Sequent → Type 
  infix ` ⊢ ` : 25 := proof
  | ax : ∀ Ω α,                 Ω ⊢ [α] ⇒ [α] 
  | ax_falsum : ∀ Ω α,          Ω ⊢  [] ⇒ [α] 

  | weak_l : ∀ {Ω Δ Γ} δ,         Ω ⊢ (Δ ⇒ Γ) → Ω ⊢ (δ::Δ) ⇒ Γ
  | weak_r : ∀ Ω Δ Γ γ,         Ω ⊢ (Δ ⇒ Γ) → Ω ⊢ Δ ⇒ (γ::Γ)

  | contraction_l : ∀ Ω Δ Γ δ,  Ω ⊢ (δ::δ::Δ) ⇒ Γ → Ω ⊢ (δ::Δ) ⇒ Γ
  | contraction_r : ∀ Ω Δ Γ γ,  Ω ⊢ Δ ⇒ (γ::γ::Γ) → Ω ⊢ Δ ⇒ (γ::Γ)

  | perm_l : ∀ Ω Δ₁ Δ₂ Γ δ₁ δ₂,  Ω ⊢ Δ₁ ++ (δ₁ :: δ₂ :: Δ₂) ⇒ Γ →  Ω ⊢ Δ₁ ++ (δ₂::δ₁::Δ₂) ⇒ Γ
  | perm_r : ∀ Ω Δ Γ₁ Γ₂ γ₁ γ₂,  Ω ⊢ Δ ⇒ Γ₁ ++ (γ₁::γ₂::Γ₂) → Ω ⊢ Δ ⇒ Γ₁ ++ (γ₂::γ₁::Γ₂)

  | cut : ∀ Ω Δ₁ Δ₂ Γ₁ Γ₂ α,     Ω ⊢ Δ₁ ⇒ α :: Γ₁ → Ω ⊢ α :: Δ₂ ⇒ Γ₂ → Ω ⊢ Δ₁ ++ Δ₂ ⇒ Γ₁ ++ Γ₂

  | and_l : ∀ Ω Δ Γ α β L, (every isAx L) → 
            Ω ⊢ (⟨L, α⟩ :: ⟨L,β⟩ :: Δ) ⇒ Γ →  
            Ω ⊢ (⟨ L, α ⊓ β⟩ :: Δ) ⇒ Γ

  | and_r : ∀ Ω₁ Ω₂ Δ Γ α β L, (every isAx L) → 
            Ω₁ ⊢ Δ ⇒ (⟨L, α⟩ :: Γ) →  
            Ω₂ ⊢ Δ ⇒ (⟨L, β⟩ :: Γ) →  
            Ω₁ ++ Ω₂ ⊢ Δ ⇒ (⟨L, α ⊓ β⟩ :: Γ) 

  | all_r : ∀ Ω Δ Γ L α R,  Ω ⊢ Δ ⇒ ⟨ L ++ [Forall R], α⟩ :: Γ →
                            Ω ⊢ Δ ⇒ ⟨ L, Ax R : α⟩ :: Γ
  
  | all_l : ∀ Ω Δ Γ L α R,  Ω ⊢ ⟨ L ++ [Forall R], α⟩ :: Δ ⇒ Γ →
                            Ω ⊢ ⟨ L, Ax R : α ⟩ :: Δ ⇒ Γ
                        
  | exists_r : ∀ {Ω Δ Γ L α R},  Ω ⊢ Δ ⇒ ⟨ L ++ [Exists R], α⟩ :: Γ →
                               Ω ⊢ Δ ⇒ ⟨ L, Ex R : α⟩ :: Γ

  | or_l : ∀ Ω Δ Γ α β L, (every isEx L) → 
            Ω ⊢ Δ ⇒ (⟨L, α⟩ :: Γ) →  
            Ω ⊢ Δ ⇒ (⟨L, β⟩ :: Γ) →  
            Ω ⊢ Δ ⇒ (⟨L, α ⊔ β⟩ :: Γ) 

  | or_r : ∀ Ω Δ Γ α β L, (every isEx L) → 
            Ω ⊢ Δ ⇒ ⟨L, α⟩ :: ⟨L,β⟩ :: Γ →  
            Ω ⊢ Δ ⇒ ⟨L, α ⊓ β⟩ :: Γ

  | neg_l : ∀ Ω Δ Γ α L, Ω ⊢ Δ ⇒ ⟨L,α⟩::Γ → 
              Ω ⊢ ⟨negLabel L, ¬ₐα⟩::Δ ⇒ Γ

  | neg_r : ∀ {Ω} Δ {Γ α L}, Ω ⊢ (Δ++[⟨L,α⟩]) ⇒ Γ → 
              Ω ⊢ Δ ⇒ ⟨negLabel L, ¬ₐα⟩::Γ
  
  | prom_ex : ∀ {Ω δ Γ} R, Ω ⊢ [δ] ⇒ Γ → 
                Ω ⊢ [⟨ Exists R :: LConcept.roles δ, LConcept.concept δ⟩] ⇒ (list.map (λ x, ⟨ (Exists R) :: LConcept.roles x, LConcept.concept x⟩) Γ)

  | prom_ax : ∀ {Ω γ Δ} R, Ω ⊢ Δ ⇒ [γ] → 
                Ω ⊢ (list.map (λ x, ⟨ Forall R :: LConcept.roles x, LConcept.concept x ⟩) Δ) ⇒ [⟨ Forall R :: LConcept.roles γ, LConcept.concept γ⟩]
infix ` ⊢ ` := proof -- \vdash

example : proof [] ([] ⇒ [LConcept.mk [] C#1]) :=
begin
  exact proof.ax_falsum [] (LConcept.mk [] C#1),
end

example : proof [] ([LConcept.mk [Forall R#1] C#1] ⇒ [LConcept.mk [Forall R#1] C#1]) :=
begin
  have S := proof.ax [] ⟨ [] , C#1 ⟩,
  have S₁ := proof.weak_l ⟨[],C#1⟩ S,
  exact proof.prom_ax R#1 S,
end

example : proof [] ([⟨[], ⊤⟩, LConcept.mk [Forall R#1] C#1] ⇒ [LConcept.mk [Forall R#1] C#1]) :=
begin
  have S := proof.ax [] ⟨ [] , C#1 ⟩,
  have S₂ := proof.prom_ax R#1 S, simp at S₂,
  exact proof.weak_l ⟨[],⊤⟩ S₂,
end

example : proof [] ([⟨[], ⊤⟩, LConcept.mk [Forall R#1] C#1] ⇒ [LConcept.mk [Forall R#1] C#1]) :=
begin
  have S := proof.ax [] ⟨ [] , C#1 ⟩,
  have S₂ := proof.prom_ax R#1 S, simp at S₂,
  exact proof.weak_l ⟨[],⊤⟩ S₂,
end


example : proof [] ([⟨[], ⊤⟩] ⇒ [LConcept.mk [Exists R#1] (Concept.Negation C#1), LConcept.mk [Forall R#1] C#1]) :=
begin
  have S₁ := proof.ax [] ⟨ [] , C#1 ⟩,
  have S₂ := proof.prom_ax R#1 S₁, simp at S₂,
  have J₁ := proof.weak_l ⟨[],⊤⟩ S₂,
  exact proof.neg_r [LConcept.mk [] ⊤ ] J₁,
end

example : proof [] ([⟨[], ⊤⟩] ⇒ 
  [LConcept.mk [] (Concept.Some R#1 (Concept.Negation C#1)), LConcept.mk [Forall R#1] C#1]) :=
begin
  have S₁ := proof.ax [] ⟨ [] , C#1 ⟩,
  have S₂ := proof.prom_ax R#1 S₁, simp at S₂,
  have J₁ := proof.weak_l ⟨[],⊤⟩ S₂,
  have J₂ := proof.neg_r [LConcept.mk [] ⊤ ] J₁,
  exact proof.exists_r J₂,
end

example : proof [] ([⟨[Exists R#1], ⊤⟩] ⇒ 
  [LConcept.mk [Exists R#1] (Concept.Some R#1 (Concept.Negation C#1)), LConcept.mk [Exists R#1,Forall R#1] C#1]) :=
begin
  have S₁ := proof.ax [] ⟨ [] , C#1 ⟩,
  have S₂ := proof.prom_ax R#1 S₁, simp at S₂,
  have J₁ := proof.weak_l ⟨[],⊤⟩ S₂,
  have J₂ := proof.neg_r [LConcept.mk [] ⊤ ] J₁, dsimp [negLabel] at J₂,
  have K₁ := proof.exists_r J₂,
end

example 




/-
reserve infix ` ⊢ `:26


inductive Sequent : list LConcept → list LConcept → Type
infix ⊢ := Sequent
  | One : ∀ L, L ⊢ L
  | Neg : ∀ L, [LConcept.mk [] Concept.Bot] ⊢ L
  | Ins : ∀ L₁ A, A ∈ L₁ → L₁ ⊢ [A]
  | WeL : ∀ L₁ L₂ A, A ∈ L₁ → L₁ ⊢ L₂ → A::L₁ ⊢ L₂
  | WeR : ∀ L₁ L₂ B, B ∈ L₂ → L₁ ⊢ L₂ → L₁ ⊢ B::L₂
  | CoL : ∀ L₁ L₂ A, A::A::L₁ ⊢ L₂ → (A::L₁) ⊢ L₂ 
  | CoR : ∀ L₁ L₂ B, L₁ ⊢ (B::L₂) → L₁ ⊢ (B::L₂)
  | PeL : ∀ AL₁ A₁ B₁ BL₁ L₂, AL₁ ++ [A₁,B₁] ++ BL₁ ⊢ L₂ →  AL₁ ++ [B₁,A₁] ++ BL₁ ⊢ L₂
  | PeR : ∀ AL₂ A₂ B₂ BL₂ L₁, L₁ ⊢ AL₂ ++ [A₂,B₂] ++ BL₂ →  L₁ ⊢ AL₂ ++ [B₂,A₂] ++ BL₂
  | CuT : ∀ AL₁ BL₁ B AL₂ CL₂, AL₁ ⊢ BL₁ ++ [B] → B::AL₂ ⊢ CL₂ → AL₁ ++ AL₂ ⊢ BL₁ ++ CL₂  


#check Sequent

instance Concept_Intersection_is_commutative {AC AR : Type}:
  @is_commutative (Concept AC AR) Concept.Intersection := ⟨λ a b, by⟩

this is the idea for the implementation, we can use folds in multiset, but I still have to prove commutative to
use it, but I am having trouble as it is...

def inter_LConcepts {AC AR : Type} (as : list (qLConcept AC AR)) :=
  list.foldl (Concept.Intersection) (sigma_exhaust (list.head as)) (list.map sigma_exhaust (list.tail as))

def union_LConcepts {AC AR : Type} (as : list (LConcept AC AR)) :=
  list.foldl (Concept.Union) (sigma_exhaust (list.head as)) (list.map sigma_exhaust (list.tail as))

def sequent {AC AR : Type} (as : list (LConcept AC AR)) (bs : list (LConcept AC AR)) :=
  subsumption (inter_LConcepts as) (union_LConcepts bs)

#reduce list.foldl (λ x y, Concept.Intersection x y) (Concept.Top) [Concept.Bot]


lemma weak_l_srule {AC AR : Type} {as bs : list (LConcept AC AR)} 
  (a : LConcept AC AR) (h1 : list.mem a as) (h : subsequent as bs) : subsequent (a::as) bs :=
begin
  unfold subsequent at *,
  unfold subsumption at *,
  intro I,
  have hn : interp I (inter_LConcepts as) ⊆ interp I (union_LConcepts bs), from h I,
  
end 

pure logic! Sequent Calculus:

Man |- Person     Person |- Casado
---------------------------------- cut
        Man |- Casado


dependent types:

h1 : Man |- Person
h2 : Person |- Casado
cut h1 h2 : Man |- Casado

-/
