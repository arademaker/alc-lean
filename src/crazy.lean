
open nat bool list decidable

@[reducible]
definition VarConcept := nat

@[reducible]
definition VarRole := nat

inductive Role : Type
  | Atomic  : VarRole → Role
  | Compose : Role → Role → Role
  | Inverse : Role → Role

inductive Concept : Type 
  | Top           : Concept
  | Bot           : Concept
  | Atomic        : VarConcept → Concept
  | Negation      : Concept → Concept
  | Intersection  : Concept → Concept → Concept
  | Union         : Concept → Concept → Concept
  | Some          : Role → Concept → Concept
  | Every         : Role → Concept → Concept


notation `R#`:max P:max := Role.Atomic P
notation `C#`:max P:max := Concept.Atomic P

#check Concept.Union C#1 C#2

def man := C#1

#check (Concept.Some R#1 man)
