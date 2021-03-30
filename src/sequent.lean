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
 

#check (⟨[Forall R#0, Exists R#1], (Concept.Bot)⟩ : LConcept)


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


inductive proof : list Sequent → Sequent → Type 
  infix ` ⊢ ` : 25 := proof
  | ax : ∀ Ω α,                 Ω ⊢ [α] ⇒ [α] 
  | ax_falsum : ∀ Ω α,          Ω ⊢  [] ⇒ [α] 

  | weak_l : ∀ Ω Δ Γ δ,         Ω ⊢ (Δ ⇒ Γ) → Ω ⊢ (δ::Δ) ⇒ Γ
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

infix ` ⊢ ` : 25 := proof -- \vdash


/--

--instance Concept_Intersection_is_commutative {AC AR : Type}:
--  @is_commutative (Concept AC AR) Concept.Intersection := ⟨λ a b, by⟩

--this is the idea for the implementation, we can use folds in multiset, but I still have to prove commutative to
--use it, but I am having trouble as it is...

def inter_LConcepts {AC AR : Type} (as : list (qLConcept AC AR)) :=
  list.foldl (Concept.Intersection) (sigma_exhaust (list.head as)) (list.map sigma_exhaust (list.tail as))

def union_LConcepts {AC AR : Type} (as : list (LConcept AC AR)) :=
  list.foldl (Concept.Union) (sigma_exhaust (list.head as)) (list.map sigma_exhaust (list.tail as))

def sequent {AC AR : Type} (as : list (LConcept AC AR)) (bs : list (LConcept AC AR)) :=
  subsumption (inter_LConcepts as) (union_LConcepts bs)

#reduce list.foldl (λ x y, Concept.Intersection x y) (Concept.Top) [Concept.Bot]


#reduce 4 ∈ [1,2,3]

#check 4 ∈ [1,2,3]

lemma l1 : 2 ∈ [1,2,3] :=
begin
 simp,
end

#check l1


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

--/

