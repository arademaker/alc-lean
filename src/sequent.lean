import alc
import data.multiset

open ALC
open ALC.Concept

variables {α β : Type }

inductive Label (AC AR : Type) : Type
  | Empty : Label
  | Negation : Label
  | Forall : (Role AR) → Concept AC AR → Label
  | Exist : (Role AR) → Concept AC AR → Label

-- to use with lists, we need an instance for inhabited, that is
-- to say that we have at leasts one element of the type

instance Label_inhabited {AC AR : Type} : 
  inhabited (Label AC AR) := inhabited.mk Label.Empty

instance Concept_inhabited {AC AR : Type} :
  inhabited (Concept AC AR) := inhabited.mk Concept.Top

structure LConcept (AC AR: Type) :=
mk :: (roles : list (Label AC AR))
      (concept : Concept AC AR)

instance LConcept_inhabited {AC AR : Type} :
  inhabited (LConcept AC AR) := inhabited.mk (LConcept.mk [Label.Empty] Concept.Top)

#check (LConcept.mk [@Label.Negation α β] (@Concept.Bot α β )).roles.head

def sigma_line {AC AR : Type} : LConcept AC AR → Label AC AR →  LConcept AC AR
  | a Label.Empty           := a
  | a Label.Negation        := LConcept.mk (a.roles.tail) (Concept.Negation a.concept)
  | a (Label.Forall RO CO)  := LConcept.mk (a.roles.tail) (Concept.Every RO a.concept)
  | a (Label.Exist RO CO)   := LConcept.mk (a.roles.tail) (Concept.Some RO a.concept)


def sigma_apply {AC AR : Type} (lc : @LConcept AC AR) :=
  sigma_line lc (lc.roles.head)

def sigma_line2 {AC AR : Type} : list (Label AC AR) → LConcept AC AR → LConcept AC AR
  | [] a := a
  | (_::ls) a := sigma_line2 (ls) (sigma_apply a)

def sigma_exhaust {AC AR : Type} (lb : LConcept AC AR) :=
  LConcept.concept (sigma_line2 (LConcept.roles lb) lb)

#reduce LConcept.concept (sigma_apply (LConcept.mk [@Label.Negation α β] (@Concept.Bot α β )))

#reduce sigma_exhaust (LConcept.mk [@Label.Negation α β] (@Concept.Bot α β ))

#check multiset.fold (Concept.Intersection) Concept.Top {Concept.Top}

--#check Concept.rec
--instance Concept_Intersection_is_commutative {AC AR : Type}:
--  @is_commutative (Concept AC AR) Concept.Intersection := ⟨λ a b, by⟩

--this is the idea for the implementation, we can use folds in multiset, but I still have to prove commutative to
--use it, but I am having trouble as it is...

def inter_LConcepts {AC AR : Type} (as : list (LConcept AC AR)) :=
  list.foldl (Concept.Intersection) (sigma_exhaust (list.head as)) (list.map sigma_exhaust (list.tail as))

def union_LConcepts {AC AR : Type} (as : list (LConcept AC AR)) :=
  list.foldl (Concept.Union) (sigma_exhaust (list.head as)) (list.map sigma_exhaust (list.tail as))

def subsequent {AC AR : Type} (as : list (LConcept AC AR)) (bs : list (LConcept AC AR)) :=
  subsumption (inter_LConcepts as) (union_LConcepts bs)

#reduce list.foldl (λ x y, Concept.Intersection x y) (Concept.Top) [Concept.Bot]


#reduce 1 ∈ [1,2,3]

lemma weak_l_srule {AC AR : Type} {as bs : list (LConcept AC AR)} 
  (a : LConcept AC AR) (h1 : list.mem a as) (h : subsequent as bs) : subsequent (a::as) bs :=
begin
  unfold subsequent at *,
  unfold subsumption at *,
  intro I,
  have hn : interp I (inter_LConcepts as) ⊆ interp I (union_LConcepts bs), from h I,
  
end 