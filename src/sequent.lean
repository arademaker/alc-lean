import alc
import data.multiset

open ALC
open ALC.Concept

variables {α β : Type }

inductive upper_Label (AC AR : Type) : Type
  | Empty : upper_Label
  | Negation : upper_Label
  | Forall : (Role AR) → Concept AC AR → upper_Label
  | Exist : (Role AR) → Concept AC AR → upper_Label

-- to use with lists, we need an instance for inhabited, that is
-- to say that we have at leasts one element of the type

instance upper_Label_inhabited {AC AR : Type} : 
  inhabited (upper_Label AC AR) := inhabited.mk upper_Label.Empty

structure lab_Concept (AC AR: Type) :=
mk :: (roles : list (upper_Label AC AR))
      (concept : Concept AC AR)

#check (lab_Concept.mk [@upper_Label.Negation α β] (@Concept.Bot α β )).roles.head

def sigma_line {AC AR : Type} : lab_Concept AC AR → upper_Label AC AR →  lab_Concept AC AR
  | a upper_Label.Empty           := a
  | a upper_Label.Negation        := lab_Concept.mk (a.roles.tail) (Concept.Negation a.concept)
  | a (upper_Label.Forall RO CO)  := lab_Concept.mk (a.roles.tail) (Concept.Every RO a.concept)
  | a (upper_Label.Exist RO CO)   := lab_Concept.mk (a.roles.tail) (Concept.Some RO a.concept)


def sigma_apply {AC AR : Type} (lc : @lab_Concept AC AR) :=
  sigma_line lc (lc.roles.head)

def sigma_line2 {AC AR : Type} : list (upper_Label AC AR) → lab_Concept AC AR → lab_Concept AC AR
  | [] a := a
  | (_::ls) a := sigma_line2 (ls) (sigma_apply a)

def sigma_exhaust {AC AR : Type} (lb : lab_Concept AC AR) :=
  lab_Concept.concept (sigma_line2 (lab_Concept.roles lb) lb)

#reduce lab_Concept.concept (sigma_apply (lab_Concept.mk [@upper_Label.Negation α β] (@Concept.Bot α β )))

#reduce sigma_exhaust (lab_Concept.mk [@upper_Label.Negation α β] (@Concept.Bot α β ))

#check multiset.fold (Concept.Intersection) Concept.Top {Concept.Top}

def subsequent {AC AR : Type} (as : multiset (lab_Concept AC AR)) (bs : multiset (Concept AC AR)) :=
  multiset.fold (@Concept.Intersection AC AR) (@Concept.Top AC AR) (multiset.map sigma_exhaust as)

#check and.comm