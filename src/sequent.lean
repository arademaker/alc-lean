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
  | ax_theory : ∀ Ω s,  (s ∈ Ω) → Ω ⊢ s          -- the only real use of Ω
  | ax_falsum : ∀ Ω α,          Ω ⊢  [⟨ [], ⊥ ⟩] ⇒ [α] 

  | weak_l : ∀ Ω Δ Γ δ,       Ω ⊢ (Δ ⇒ Γ) → Ω ⊢ (δ::Δ) ⇒ Γ
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
                        
  | exists_r : ∀ Ω Δ Γ L α R,  Ω ⊢ Δ ⇒ ⟨ (Exists R) :: L, α⟩ :: Γ →
                               Ω ⊢ Δ ⇒ ⟨ L, Ex R : α⟩ :: Γ

  | or_l : ∀ Ω Δ Γ α β L, (every isEx L) → 
            Ω ⊢ Δ ⇒ (⟨L, α⟩ :: Γ) →  
            Ω ⊢ Δ ⇒ (⟨L, β⟩ :: Γ) →  
            Ω ⊢ Δ ⇒ (⟨L, α ⊔ β⟩ :: Γ) 

  | or_r : ∀ Ω Δ Γ α β L, (every isEx L) → 
            Ω ⊢ Δ ⇒ ⟨L, α⟩ :: ⟨L,β⟩ :: Γ →  
            Ω ⊢ Δ ⇒ ⟨L, α ⊓ β⟩ :: Γ

  | neg_l : ∀ Ω Δ Γ α L L1, L1 = negLabel L →  Ω ⊢ Δ ⇒ ⟨L,α⟩ :: Γ → Ω ⊢ ⟨L1, ¬ₐα⟩ :: Δ ⇒ Γ

  | neg_r : ∀ Ω Δ Γ α L L1, L1 = negLabel L →  Ω ⊢ Δ ++ [⟨L,α⟩]  ⇒ Γ → Ω ⊢ Δ ⇒ ⟨L1, ¬ₐα⟩ :: Γ
  
  | prom_ex : ∀ Ω δ Γ R, Ω ⊢ [δ] ⇒ Γ → 
                Ω ⊢ [⟨ Exists R :: LConcept.roles δ, LConcept.concept δ⟩] ⇒ 
                    (list.map (λ x, ⟨ (Exists R) :: LConcept.roles x, LConcept.concept x⟩) Γ)

  | prom_ax : ∀ Ω γ Δ R, Ω ⊢ Δ ⇒ [γ] → 
                Ω ⊢ (list.map (λ x, ⟨ Forall R :: LConcept.roles x, LConcept.concept x ⟩) Δ) ⇒ 
                    [⟨ Forall R :: LConcept.roles γ, LConcept.concept γ⟩]
infix ` ⊢ ` := proof -- \vdash


def doctor := C#1
def child  := R#1

lemma l1 : proof [] ([LConcept.mk [Forall child] doctor] ⇒ [LConcept.mk [Forall child] doctor]) :=
begin
  have S := proof.ax [] ⟨[] , doctor⟩,
  exact proof.prom_ax [] _ _ child S,
end

lemma l2 : proof [] ([⟨[], ⊤⟩, LConcept.mk [Forall child] doctor] ⇒ [LConcept.mk [Forall child] doctor]) :=
begin
  apply proof.weak_l,
  exact l1,  
end


example : proof [] ([⟨[], ⊤⟩] ⇒ 
  [LConcept.mk [] (Concept.Some R#1 (Concept.Negation C#1)), LConcept.mk [Forall R#1] C#1]) :=
begin
  have S₁ := proof.ax [] ⟨ [] , C#1 ⟩,
  have S₂ := proof.prom_ax _ _ _ R#1 S₁, simp at S₂,
  have J₁ := proof.weak_l [] [{roles := [Forall R#1], concept := C#1}] [{roles := [Forall R#1], concept := C#1}] ⟨[],⊤⟩ S₂,
  have J₂ := proof.neg_r [] [{roles := ([] : list Label), concept := ⊤}] [{roles := [Forall R#1], concept := C#1}] C#1 [Forall R#1] [Exists R#1] _ J₁,
  clear S₁ S₂ J₁,
  exact proof.exists_r [] [⟨[], ⊤⟩] [{roles := [Forall R#1], concept := C#1}] [] (¬ₐ C#1) R#1 J₂,
  tauto,
end

example : proof [] 
   ([LConcept.mk ([] : list Label) (Ex R#1 : ⊤)] ⇒ 
   [(LConcept.mk [Exists R#1] ¬ₐ C#1), (LConcept.mk [Exists R#1,Forall R#1] C#1)]) := 
begin
 apply proof.neg_r [] 
  [{roles := ([] : list Label), concept := Ex R#1:⊤}] 
  [{roles := [Exists R#1, Forall R#1], concept := C#1}] C#1 [Forall R#1] [Exists R#1],
 rw [negLabel, negLabel],

 sorry
  
end

lemma in_map {α β} {x : α} {A : list α} (x ∈ A) (f : α → β) : (f x) ∈ (list.map f A) :=
begin
  finish,
end

lemma head_out_map {α β} {a : α } {A : list α} {f : α → β} : list.map f (a::A) = (f a) :: list.map f A :=
begin
  finish,
end

def subseteq_imp_inter_subseteq {α} {A C : set α} {B : set α} : A ⊆ C → (A ∩ B) ⊆ C :=
begin
  intro h, have h1 : A ∩ B ⊆ A, exact set.inter_subset_left A B, exact set.subset.trans h1 h,
end

def subseteq_imp_union_subseteq {α} {A C : set α} {B : set α} : A ⊆ C → A ⊆ B ∪ C :=
begin
  intro h, have h1 : C ⊆ B ∪ C, exact set.subset_union_right B C, exact set.subset.trans h h1,
end


def foldl_inter : list LConcept → Concept
  | [] := ⊤
  | [a] := sigma' a
  | (a::ls) := sigma' a ⊓ (foldl_inter ls)

def foldl_union : list LConcept → Concept
  | [] := ⊥
  | [a] := sigma' a
  | (a::ls) := sigma' a ⊔ (foldl_union ls) 


def seq_to_stmt : Sequent → Statement
  | (Δ ⇒ Γ) := Statement.Subsumption (foldl_inter Δ) (foldl_union Γ)

lemma interp_foldl_inter_append {xs a I}: interp I (foldl_inter (xs ++ [a])) = interp I (foldl_inter (a::xs)) :=
begin
  sorry,
end

lemma interp_foldl_union_reverse {xs I} : interp I (foldl_inter xs) = interp I (foldl_inter (list.reverse xs)) :=
begin
  sorry,
end

lemma interp_stmt_weak_l {Δ Γ I} ( δ : LConcept) : (interp_stmt I (seq_to_stmt(Δ ⇒ Γ))) →  (interp_stmt I (seq_to_stmt(δ::Δ ⇒ Γ))) :=
begin
  intro a,
  induction Δ with δ₁ Δ₂ Δh, 
  
  induction Γ with γ₁ Γ₂ Γh,

  unfold seq_to_stmt interp_stmt foldl_union interp at *,
  rw ← set.eq_empty_of_subset_empty a, exact set.subset_univ (interp I (foldl_inter [δ])),

  unfold seq_to_stmt interp_stmt interp at *, 
  rw (set.eq_univ_of_univ_subset a), exact (interp I (foldl_inter [δ])).subset_univ,

  induction Γ with γ₁ Γ₂ Γh,

  unfold seq_to_stmt interp_stmt interp foldl_inter at *, rw set.inter_comm, exact subseteq_imp_inter_subseteq a,
  
  unfold seq_to_stmt interp_stmt foldl_union foldl_inter at *,
  unfold1 interp, rw set.inter_comm, exact subseteq_imp_inter_subseteq a,
end

lemma gen_interp_stmt_weak_l {Δ₁ Δ₂ Γ I} : (interp_stmt I (seq_to_stmt(Δ₂ ⇒ Γ))) →  (interp_stmt I (seq_to_stmt(Δ₁++Δ₂ ⇒ Γ))) :=
begin
  intro h,
  induction Δ₁ with Δ₁0 Δ₁1 Δ₁h, simp, exact h, exact interp_stmt_weak_l Δ₁0 Δ₁h,
end

lemma interp_stmt_weak_r {Δ Γ I} ( γ : LConcept) : (interp_stmt I (seq_to_stmt(Δ ⇒ Γ))) →  (interp_stmt I (seq_to_stmt(Δ ⇒ γ::Γ))) :=
begin
  intro a,
  induction Δ with δ₁ Δ₂ Δh, 
  
  induction Γ with γ₁ Γ₂ Γh,

  unfold seq_to_stmt interp_stmt foldl_union interp at *,
  rw set.eq_empty_of_subset_empty a, exact (interp I (sigma' γ)).empty_subset,

  unfold seq_to_stmt interp_stmt interp foldl_union at *, exact subseteq_imp_union_subseteq a,

  induction Γ with γ₁ Γ₂ Γh,

  unfold seq_to_stmt interp_stmt interp foldl_union at *, rw set.eq_empty_of_subset_empty a,
  exact set.empty_subset (interp I (sigma' γ)),

  unfold seq_to_stmt interp_stmt foldl_union foldl_inter at *, unfold interp, exact subseteq_imp_union_subseteq a,
end

lemma gen_interp_stmt_weak_r {Δ Γ₁ Γ₂ I} : (interp_stmt I (seq_to_stmt(Δ ⇒ Γ₂))) →  (interp_stmt I (seq_to_stmt(Δ ⇒ Γ₁++Γ₂))) :=
begin
  intro h,
  induction Γ₁ with Γ₁0 Γ₁1 Γ₁h, simp, exact h, exact interp_stmt_weak_r Γ₁0 Γ₁h,
end

#check is_commutative

lemma interp_stmt_contract_l {Δ Γ I} {δ : LConcept} : (interp_stmt I (seq_to_stmt(δ::δ::Δ ⇒ Γ))) →  (interp_stmt I (seq_to_stmt(δ::Δ ⇒ Γ))) :=
begin
  intro h,
  unfold seq_to_stmt foldl_inter interp at *, 
  induction Δ with Δ0 Δ1, 
  
  unfold foldl_inter interp_stmt interp at *, rw set.inter_self at h, exact h,
  unfold foldl_inter interp_stmt interp at *, rw ← set.inter_assoc at h , rw set.inter_self at h, exact h,
end

lemma interp_stmt_contract_r {Δ Γ I} {γ : LConcept} : (interp_stmt I (seq_to_stmt(Δ ⇒ γ::γ::Γ))) →  (interp_stmt I (seq_to_stmt(Δ ⇒ γ::Γ))) :=
begin
  intro h,
  unfold seq_to_stmt foldl_inter interp at *, 
  induction Γ with Γ0 Γ1, 
  
  unfold foldl_union interp_stmt interp at *, rw set.union_self at h, exact h,
  unfold foldl_union interp_stmt interp at *, rw ← set.union_assoc at h , rw set.union_self at h, exact h,
end

lemma interp_stmt_perm_l {Δ₁ Δ₂ Γ I δ₁ δ₂} : interp_stmt I (seq_to_stmt (Δ₁ ++ δ₁ :: δ₂ :: Δ₂ ⇒ Γ)) → interp_stmt I (seq_to_stmt (Δ₁ ++ δ₂ :: δ₁ :: Δ₂ ⇒ Γ)) :=
begin
  intro h,
  unfold seq_to_stmt at *, 
  
  induction Δ₁ with Δ₁0 Δ₁1, 
  
  simp at *, unfold foldl_inter interp_stmt interp at *, 
  
  induction Δ₂ with Δ₂0 Δ₂1, 
  
  unfold foldl_inter at *, rw set.inter_comm at h, exact h,
  
  unfold foldl_inter interp at *, rw ← set.inter_assoc at h, nth_rewrite 1 set.inter_comm at h, rw set.inter_assoc at h, exact h,

  sorry
end


theorem soundness {Ω : list Sequent} : ∀ {Δ Γ}, (proof Ω (Δ ⇒ Γ)) →  models (list.map seq_to_stmt Ω) (seq_to_stmt (Δ ⇒ Γ))
  | _ _ (proof.ax Ω₁ α₁) := 
    by {unfold models, intros h1 h2, 
      unfold seq_to_stmt foldl_inter foldl_union interp_stmt,
    }
  | _ _ (proof.ax_theory Ω₁ (lhs ⇒ rhs) S) :=
    by {unfold models, intros h1 h2, unfold satisfies at h2,
     have h3 := h2 (seq_to_stmt(lhs ⇒ rhs )), 
     have h4 := in_map (lhs ⇒ rhs) S seq_to_stmt, 
     exact h2 (seq_to_stmt(lhs ⇒ rhs )) h4, exact (lhs ⇒ rhs),
     }
  | _ _ (proof.ax_falsum Ω₁ α₁) :=
    by {unfold models, intros h1 h2, 
      unfold seq_to_stmt foldl_inter foldl_union interp_stmt sigma' sigma_aux interp at *, exact set.empty_subset (interp h1 (sigma' α₁)),
    }
  | _ _ (proof.weak_l Ω₁ Δ Γ δ h) :=
    by { unfold models, intros I h2, unfold satisfies at h2,
      have h4 := soundness h, unfold models at h4, have h5 := h4 I, unfold satisfies at h5, have h6 := h5 h2,
      exact interp_stmt_weak_l δ h6,
    }
  | _ _ (proof.weak_r Ω₁ Δ Γ γ h) :=
    by { unfold models, intros I h2, unfold satisfies at h2,
      have h4 := soundness h, unfold models at h4, have h5 := h4 I, unfold satisfies at h5, have h6 := h5 h2,
      exact interp_stmt_weak_r γ h6,
    }
  | _ _ (proof.contraction_l Ω₁ Δ Γ δ h) :=
    by { unfold models, intros I h1, unfold satisfies at h1,
      have h2 := soundness h, unfold models at h2, have h3 := h2 I, unfold satisfies at h3, have h4:= h3 h1,
      exact interp_stmt_contract_l h4,
    }
  | _ _ (proof.contraction_r Ω₁ Δ Γ δ h) :=
    by { unfold models, intros I h1, unfold satisfies at h1,
      have h2 := soundness h, unfold models at h2, have h3 := h2 I, unfold satisfies at h3, have h4:= h3 h1,
      exact interp_stmt_contract_r h4,
    }
  | _ _ (proof.perm_l Ω Δ₁ Δ₂ Γ δ₁ δ₂ h) :=
    by { unfold models, intros I h1, unfold satisfies at h1,
      have h2 := soundness h, unfold models at h2, have h3 := h2 I, unfold satisfies at h3, have h4:= h3 h1,
      sorry,
    }

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
