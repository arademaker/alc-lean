import alc
import data.multiset

open ALC
open ALC.Concept

inductive Label : Type
  | Forall : Role  → Label
  | Exists : Role  → Label


-- to use with lists, we need an instance for inhabited, that is
-- to say that we have at leasts one element of the type

/--
instance Label_inhabited {AC AR : Type} : 
  inhabited (Label AC AR) := inhabited.mk Label.Empty

instance Concept_inhabited {AC AR : Type} :
  inhabited (Concept AC AR) := inhabited.mk Concept.Top

instance LConcept_inhabited {AC AR : Type} :
  inhabited (LConcept AC AR) := inhabited.mk (LConcept.mk [Label.Empty] Concept.Top)
--/

structure LConcept :=
mk :: (roles : list Label)
      (concept : Concept)

open LConcept
open Label

def sigma_aux : list Label -> Concept -> Concept 
 | []                 c := c
 | ((Forall r) :: ls) c := Every r (sigma_aux ls c)
 | ((Exists r) :: ls) c := Some r (sigma_aux ls c)

def sigma' : LConcept -> Concept
 | ⟨ roles , concept ⟩ := sigma_aux roles concept

#reduce sigma' (LConcept.mk [Forall R#0, Exists R#1] (Concept.Bot))


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

