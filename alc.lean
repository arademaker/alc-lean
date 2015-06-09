import logic.identities logic.axioms.classical data.list
open bool list
 

section SetTheory

 

--print instances decidable

 

-- some necessary logic theorems

 

-- [Leo]: The file logic.identities has many useful theorems for "classical" users.

-- Remark: when we import logic.axioms.classical, all propositions are treated as decidable.

-- See file: library/logic/axioms/prop_decidable.lean

theorem neg_conj {p: Prop} {q: Prop} (h: ¬(p ∧ q)) : ¬p ∨ ¬q :=

iff.mp not_and_iff_not_or_not h



theorem double_neg {p : Prop} (h: ¬¬p) : p :=

iff.mp not_not_iff h


/-theorem iff_neg {p q : Prop} (h:p↔q) : ¬p↔¬q :=
iff.intro
    (assume h2:¬p,
     assume h3:q,
     have l:p, from (iff.mp' h) h3,
     show false, from absurd l h2)
    (assume h2:¬q,
     assume h3:p,
     have l:q, from (iff.mp h) h3,
     show false, from absurd l h2)-/

theorem contraposition {p q : Prop} (h: p→q) : ¬q→¬p :=
assume h2: ¬q,
assume h3: p,
have l1: q, from h h3,
show false, from absurd l1 h2

 

-- [Leo]: In the long-term, I think it would be easier for you if {A : Type} is an explicit

-- parameter.

inductive Set {A : Type} : Type :=

spec: (A → Prop) → Set -- specification, or every set represents and is represented by a Property (a proposition)

 

definition Property {A : Type} (S : Set) : A → Prop := (Set.rec (λ(P: A → Prop), P)) S


definition member {A : Type} (S: @Set A) (a : A) : Prop := Property S a


 
notation a `∈` S := member S a

notation a `∉` S := ¬ a∈S

 

definition UnivSet {A : Type} : Set := Set.spec (λx:A, x=x) -- Universal Set

definition EmptySet {A : Type} : Set := Set.spec (λx: A, ¬x=x)

definition Union {A : Type} (S : Set) (T : Set) : Set := Set.spec (λ(x: A), x∈S∨x∈T)

definition Compl {A : Type} (S : Set) : Set := Set.spec (λ(x: A), x∉S) -- complementar

 

notation `U` := UnivSet

notation `∅` := EmptySet

notation S `∪` T := Union S T

prefix `∁`:71 := Compl

 

definition Inters {A : Type} (S : @Set A) (T : @Set A) : @Set A :=

∁(∁S ∪ ∁T)

 

notation S `∩` T := Inters S T

 

definition Diff {A : Type} (S : Set) (T : Set) : @Set A :=

S∩(∁T)

 

infix `∖`:51 := Diff

 

theorem UnivMember {A : Type} : ∀(x: A), x∈UnivSet :=

take x: A,

have h: x=x, from rfl,

show x∈UnivSet, from h

 

theorem EmptyMember {A: Type} : ∀(x: A), x∉EmptySet :=

take x: A,

assume h2: x∈EmptySet,

have l: x=x, from rfl,

have l2: x≠x, from h2,

show false, from absurd l l2

 

theorem UnionMember {A: Type} {S: Set} {T: Set} : ∀(x: A), x∈(S∪T)↔(x∈S ∨ x∈T) :=

take x: A,

iff.intro

    (assume h: x∈(S∪T),

     have l1: x∈S∨x∈T, from h,

     or.elim l1

        (assume l2: x∈S,

         show x∈S∨x∈T, from or.intro_left (x∈T) l2)

         (assume l2: x∈T,

         show x∈S∨x∈T, from or.intro_right (x∈S) l2))

    (assume h: x∈S∨x∈T,

     show x∈(S∪T), from h)

 

theorem ComplMember {A: Type} {S: Set} : ∀(x: A), x∉S ↔ x∈∁S :=

take x: A,

iff.intro

    (assume h: x∉S,

     show x∈∁S, from h)

    (assume h: x∈∁S,

     show x∉S, from h)

theorem IntersMember {A: Type} {S: Set} {T: Set} : ∀(x:A), x∈(S∩T)↔(x∈S ∧ x∈T) :=
take x: A,
iff.intro
    (assume h: x∈(S∩T),
     have l1: x∉(∁S∪∁T), from h,
     have l2: ¬(x∈∁S ∨ x∈∁T), from l1,
     have l3: x∉∁S ∧ x∉∁T, from iff.mp not_or_iff_not_and_not l2,
     have l4: x∉∁S, from and.elim_left l3,
     have l5: x∉∁T, from and.elim_right l3,
     have l6: x∈S, from not_not_elim (contraposition (iff.mp (ComplMember x)) l4),
     have l7: x∈T, from not_not_elim (contraposition (iff.mp (ComplMember x)) l5),
     show x∈S ∧ x∈T, from and.intro l6 l7)
    (assume h: x∈S∧x∈T,
     have l1: x∈S, from and.elim_left h,
     have l2: x∈T, from and.elim_right h,
     have l3: x∉∁S, from (contraposition (iff.mp' (ComplMember x)) (iff.mp' not_not_iff l1)),
     have l4: x∉∁T, from (contraposition (iff.mp' (ComplMember x)) (iff.mp' not_not_iff l2)),
     have l5: x∉∁S∧x∉∁T, from and.intro l3 l4,
     have l6: ¬(x∈∁S ∨ x∈∁T), from iff.mp' not_or_iff_not_and_not l5,
     have l7: x∉(∁S∪∁T), from l6,
     show x∈S∩T, from l7)

theorem DiffMember {A: Type} {S: Set} {T: Set} : ∀(x: A), x∈(S∖T)↔(x∈S ∧ x∉T) :=
take x:A,
iff.intro
    (assume h: x∈(S∖T),
     have l: x∈S∩∁T, from h,
     have l2: x∈S∧x∈∁T, from iff.mp (IntersMember x) l,
     have l3: x∈S, from and.elim_left l2,
     have l4: x∈∁T, from and.elim_right l2,
     have l5: x∉T, from iff.mp' (ComplMember x) l4,
     show x∈S∧x∉T, from and.intro l3 l5)
    (assume h:x∈S∧x∉T,
     have l: x∈S, from and.elim_left h,
     have l2: x∉T, from and.elim_right h,
     have l3: x∈∁T, from iff.mp (ComplMember x) l2,
     have l4: x∈S∧x∈∁T, from and.intro l l3,
     have l5: x∈S∩∁T, from iff.mp' (IntersMember x) l4,
     show x∈(S∖T), from l5)

	 
definition subset {A: Type} (S: Set) (T: Set) : Prop := ∀x:A, x∈S → x∈T

infix `⊂`:52 := subset

axiom SetEqual {A: Type} {S T : @Set A} : S⊂T∧T⊂S ↔ S=T
   
theorem IntersUniv {A: Type} {S: @Set A} : S∩U = S :=
iff.mp SetEqual (and.intro
       (assume x:A,
        assume h:x∈S∩U,
        have l:x∈S∧x∈U, from iff.mp (IntersMember x) h,
        show x∈S, from and.elim_left l)
       (assume x:A,
        assume h:x∈S,
        have l:x∈U, from UnivMember x,
        have l2:x∈S∧x∈U, from and.intro h l,
        show x∈S∩U, from iff.mp' (IntersMember x) l2))

theorem Inters_commu {A: Type} (B C: @Set A) : B∩C = C∩B :=
iff.mp SetEqual (and.intro
       (assume x:A,
        assume h:x∈B∩C,
        have l:x∈B∧x∈C, from iff.mp (IntersMember x) h,
        have l2:x∈B, from and.elim_left l,
        have l3:x∈C, from and.elim_right l,
        have l4:x∈C∧x∈B, from and.intro l3 l2,
        show x∈C∩B, from iff.mp' (IntersMember x) l4)
       (assume x:A,
        assume h:x∈C∩B,
        have l:x∈C∧x∈B, from iff.mp (IntersMember x) h,
        have l2:x∈C, from and.elim_left l,
        have l3:x∈B, from and.elim_right l,
        have l4:x∈B∧x∈C, from and.intro l3 l2,
        show x∈B∩C, from iff.mp' (IntersMember x) l4))

theorem Inters_assoc {A: Type} {B C D: @Set A} : B∩(C∩D) = (B∩C)∩D :=
iff.mp SetEqual (and.intro
       (assume x:A,
        assume h:x∈B∩(C∩D),
        have l: x∈B∧x∈(C∩D), from iff.mp (IntersMember x) h,
        have l2: x∈B, from and.elim_left l,
        have l3: x∈(C∩D), from and.elim_right l,
        have l4: x∈C∧x∈D, from iff.mp (IntersMember x) l3,
        have l5: x∈C, from and.elim_left l4,
        have l6: x∈D, from and.elim_right l4,
        have l7: x∈B∧x∈C, from and.intro l2 l5,
        have l8: x∈B∩C, from iff.mp' (IntersMember x) l7,
        have l9: x∈B∩C∧x∈D, from and.intro l8 l6,
        show x∈(B∩C)∩D, from iff.mp' (IntersMember x) l9)
       (assume x:A,
        assume h:x∈(B∩C)∩D,
        have l: x∈B∩C∧x∈D, from iff.mp (IntersMember x) h,
        have l2: x∈B∩C, from and.elim_left l,
        have l3: x∈D, from and.elim_right l,
        have l4: x∈B∧x∈C, from iff.mp (IntersMember x) l2,
        have l5: x∈B, from and.elim_left l4,
        have l6: x∈C, from and.elim_right l4,
        have l7: x∈C∧x∈D, from and.intro l6 l3,
        have l8: x∈C∩D, from iff.mp' (IntersMember x) l7,
        have l9: x∈B∧x∈C∩D, from and.intro l5 l8,
        show x∈B∩(C∩D), from iff.mp' (IntersMember x) l9))

theorem subset_inters {A: Type} {B C D: @Set A} : B⊂C → (D∩B⊂D∩C) :=
  assume h: B⊂C,
  take x: A,
  assume h2:x∈D∩B,
  have l: x∈D∧x∈B, from iff.mp (IntersMember x) h2,
  have l2: x∈B, from and.elim_right l,
  have l3: x∈D, from and.elim_left l,
  have l4: x∈C, from h x l2,
  have l5: x∈D∧x∈C, from and.intro l3 l4,
  show x∈(D∩C), from iff.mp' (IntersMember x) l5

theorem subset_trans {A: Type} {B C D: @Set A} : B⊂C → C⊂D → B⊂D :=
  assume h:B⊂C,
  assume h2:C⊂D,
  take x:A,
  assume h3: x∈B,
  have l: x∈C, from h x h3,
  show x∈D, from h2 x l

theorem UnionEmpty {A: Type} {S: @Set A}: S∪∅ = S :=
iff.mp SetEqual (and.intro
  (assume x: A,
   assume h: x∈S∪∅,
   have l: x∈S∨x∈∅, from iff.mp (UnionMember x) h,
   show x∈S, from or.elim l
                  (assume h2: x∈S,
                   h2)
                  (assume h2: x∈∅,
                   absurd h2 (EmptyMember x)))
  (assume x:A,
   assume h:x∈S,
   have l:x∈S∨x∈∅, from or.intro_left (x∈∅) h,
   show x∈S∪∅, from iff.mp' (UnionMember x) l))

theorem Union_commu {A: Type} (S T: @Set A): S∪T = T∪S :=
 iff.mp SetEqual (and.intro
   (assume x:A,
    assume h:x∈S∪T,
    have l:x∈S∨x∈T, from iff.mp (UnionMember x) h,
    have l2: x∈T∨x∈S, from iff.mp or.comm l,
    show x∈T∪S, from iff.mp' (UnionMember x) l2)
   (assume x:A,
    assume h:x∈T∪S,
    have l:x∈T∨x∈S, from iff.mp (UnionMember x) h,
    have l2: x∈S∨x∈T, from iff.mp or.comm l,
    show x∈S∪T, from iff.mp' (UnionMember x) l2))

theorem Union_assoc {A: Type} {R S T: @Set A} : R∪(S∪T) = (R∪S)∪T :=
iff.mp SetEqual (and.intro
  (assume x:A,
   assume h:x∈(R∪(S∪T)),
   have l:x∈R∨x∈S∪T, from iff.mp (UnionMember x) h,
   or.elim l
     (assume h2:x∈R,
      have l2:x∈R∨x∈S, from !or.intro_left h2,
      have l3:x∈R∪S, from iff.mp' (UnionMember x) l2,
      have l4:x∈(R∪S)∨x∈T, from !or.intro_left l3,
      show x∈(R∪S)∪T, from iff.mp' (UnionMember x) l4)
     (assume h2:x∈S∪T,
      have l2:x∈S∨x∈T, from iff.mp (UnionMember x) h2,
      show x∈(R∪S)∪T, from or.elim l2
        (assume h3:x∈S,
         have l3:x∈R∨x∈S, from !or.intro_right h3,
         have l4:x∈R∪S, from iff.mp' (UnionMember x) l3,
         have l5:x∈R∪S∨x∈T, from or.intro_left (x∈T) l4,
         show x∈(R∪S)∪T, from iff.mp' (UnionMember x) l5)
        (assume h3:x∈T,
         have l5:x∈R∪S∨x∈T, from or.intro_right (x∈R∪S) h3,
         show x∈(R∪S)∪T, from iff.mp' (UnionMember x) l5)))
   (assume x:A,
    assume h:x∈(R∪S)∪T,
    have l:x∈R∪S∨x∈T, from iff.mp (UnionMember x) h,
    show x∈R∪(S∪T), from or.elim l
      (assume h2: x∈R∪S,
       have l2:x∈R∨x∈S, from iff.mp (UnionMember x) h2,
       show x∈R∪(S∪T), from or.elim l2
            (assume h3:x∈R,
             have l3: x∈R∨x∈S∪T, from or.intro_left (x∈S∪T) h3,
             show x∈R∪(S∪T), from iff.mp' (UnionMember x) l3)
            (assume h3:x∈S,
             have l3: x∈S∨x∈T, from or.intro_left (x∈T) h3,
             have l4:x∈S∪T, from iff.mp' (UnionMember x) l3,
             have l5:x∈R∨x∈S∪T, from or.intro_right (x∈R) l4,
             show x∈R∪(S∪T), from iff.mp' (UnionMember x) l5))
       (assume h2:x∈T,
        have l2:x∈S∨x∈T, from or.intro_right (x∈S) h2,
        have l3:x∈S∪T, from iff.mp' (UnionMember x) l2,
        have l4:x∈R∨x∈S∪T, from or.intro_right (x∈R) l3,
        show x∈R∪(S∪T), from iff.mp' (UnionMember x) l4)))

-- I've copied this incomplete proof of this theorem because in this last step, LEAN says it couldn't
-- unify x ∈ α∩C with false. However, (iff.mp' (IntersMember x)) produces x∈ ?S ∧ x∈?T → x∈?S∪?T
-- What's wrong here?

/-theorem SetCut {A: Type} {B C α X Y: @Set A} (h: B⊂α∪X) (h2: α∩C⊂Y): B∩C ⊂ X∪Y :=
begin
  intro x,
  intro h3,
  have l:x∈B∧x∈C, from iff.mp (IntersMember x) h3,
  have l2:x∈B, from and.elim_left l,
  have l3:x∈C, from and.elim_right l,
  have l4:x∈α∨x∈X, from (iff.mp (UnionMember x) (h x l2)),
  apply (iff.mp' (UnionMember x)),
  apply (or.elim l4),
    intro x_α, apply !or.intro_right, apply (h2 x), apply (iff.mp' (IntersMember x)),

end-/

  
theorem SetCut {A: Type} {B C α X Y: @Set A} (h: B⊂α∪X) (h2: α∩C⊂Y): B∩C ⊂ X∪Y :=
begin
  intro x,
  intro h3,
  have l:x∈B∧x∈C, from iff.mp (IntersMember x) h3,
  have l2:x∈B, from and.elim_left l,
  have l3:x∈C, from and.elim_right l,
  have l4:x∈α∨x∈X, from (iff.mp (UnionMember x) (h x l2)),
  apply (iff.mp' (UnionMember x)),
  apply (or.elim l4),
    intro x_α, apply !or.intro_right, apply (h2 x), have l5: x∈α∧x∈C, from (and.intro x_α l3), exact (iff.mp' (IntersMember x) l5),
    intro x_X, exact (!or.intro_left x_X)
end

/-take x: A,
assume h3: x∈B∩C,
have l:x∈B∧x∈C, from iff.mp (IntersMember x) h3,
have l2:x∈B, from and.elim_left l,
have l3:x∈C, from and.elim_right l,
show x∈X∪Y, from
  begin
  apply (or.elim h l2),

  end-/



end SetTheory


namespace ALC

universe UNI

constants AtomicConcept AtomicRole : Type.{UNI}

inductive Role : Type :=
| Atomic : AtomicRole → Role

inductive Concept : Type :=
| TopConcept : Concept
| BottomConcept : Concept
| Atomic :  AtomicConcept → Concept
| Negation : Concept → Concept
| Intersection : Concept → Concept → Concept
| Union : Concept → Concept → Concept
| ExistQuant : Role → Concept → Concept  
| ValueRestr : Role → Concept → Concept  


--attribute Concept.Atomic [coercion]

--attribute Role.Atomic [coercion]

open Concept
open Role

notation `⊤` := TopConcept --\top
notation `⊥` := BottomConcept --\bot
prefix `¬` := Negation --\neg
infix `⊓` :51 := Intersection --sqcap
infix `⊔` :51 := Union -- \sqcup
notation ∃; R . C := ExistQuant R C
notation `∀;` R . C := ValueRestr R C -- overload not working for: `∀` R . C


structure Interp := -- interpretation structure
mk :: (δ : Type.{UNI}) -- δ is the Universe
      (atom_C : AtomicConcept → @Set δ)
      (atom_R : AtomicRole → @Set (δ×δ))

definition r_interp {I : Interp} : Role → @Set(Interp.δ I × Interp.δ I)  -- Role interpretation
| r_interp (Atomic R) := !Interp.atom_R R

definition interp {I: Interp} : Concept → Set -- Concept Interpretation
| interp ⊤ := U
| interp ⊥ := ∅
| interp (Atomic C) := !Interp.atom_C C
| interp ¬C := ∁(interp C)
| interp (C1⊓C2) := (interp C1)∩(interp C2)
| interp (C1⊔C2) := (interp C1)∪(interp C2)
| interp (∃;R. C) := Set.spec (λa:Interp.δ I, exists b : Interp.δ I, (a, b)∈(!r_interp R) ∧ b∈(interp C) )
| interp (ValueRestr R C) := Set.spec (λa:Interp.δ I, forall b : Interp.δ I, ((a, b)∈(!r_interp R)) → b∈(interp C))


definition satisfiable (C : Concept) : Prop :=
exists I : Interp, @interp I C ≠ ∅

definition subsumption (C D: Concept) : Prop :=
forall I : Interp, @interp I C ⊂ @interp I D
infix `⊑` : 50 := subsumption -- \sqsubseteq

definition equivalence (C D: Concept) : Prop := C⊑D∧D⊑C
infix `≡` : 50 := equivalence -- \==

definition TBOX_subsumption (D : @Set Prop) (α : Prop) : Prop :=
(forall p: Prop, (p∈D → p)) → α
infix `⊧` : 1 := TBOX_subsumption --\models

definition models_proof (Ω: @Set Prop) (α: Prop) (h: (∀p: Prop, (p∈ Ω → p)) → α): Ω⊧α :=
h

example (C D : Concept) : C⊓D ⊑ C :=
take (I : Interp),
take x : Interp.δ I,
assume h : x ∈ interp (C⊓D),
have l: x ∈ (interp C)∩(interp D), from h,
have l2: x∈(interp C)∧x∈(interp D), from (iff.elim_left (IntersMember x)) l,
show x∈(interp C), from and.elim_left l2

example (C D E : Concept) : (Set.spec (λp: Prop, p = C⊑D ∨ p = D⊑E)) ⊧ C⊑E :=
assume h: forall (p: Prop), (p∈(Set.spec (λp: Prop, p = C⊑D ∨ p = D⊑E)) → p),
have l1: C⊑D = C⊑D, from rfl,
have l2: C⊑D = C⊑D ∨ C⊑D = D⊑E, from or.intro_left (C⊑D = D⊑E) l1,
have l3: C⊑D ∈ (Set.spec (λp: Prop, p = C⊑D ∨ p = D⊑E)), from l2,
have l4: D⊑E = D⊑E, from rfl,
have l5: D⊑E = C⊑D ∨ D⊑E = D⊑E, from or.intro_right (D⊑E = C⊑D) l4,
have l6: D⊑E ∈ (Set.spec (λp: Prop, p = C⊑D ∨ p = D⊑E)), from l5,
have l7: C⊑D, from h (C⊑D) l3,
have l8: D⊑E, from h (D⊑E) l6,
assume I : Interp,
take x : Interp.δ I,
assume h2: x∈ interp C,
have l9: x∈ interp D, from l7 I x h2,
show x ∈ interp E, from l8 I x l9
 
--- Sequent Calculus


inductive Label : Type :=
| all : Role → Label
| ex : Role → Label

notation `∀;` R := Label.all R

inductive LabelConc : Type := -- labeled concept
| mk : list Label → Concept → LabelConc

notation L `[` C `]` := LabelConc.mk L C

definition LabelToPrefix [reducible] : list Label → (Concept → Concept) -- label to prefix
| LabelToPrefix nil C := C
| LabelToPrefix ((Label.all R)::L) C := ∀;R . (LabelToPrefix L C)
| LabelToPrefix ((Label.ex R)::L) C := ∃;R .(LabelToPrefix L C)

definition getLabelList : LabelConc → list Label
| getLabelList (LabelConc.mk L C) := L

definition σ [reducible] : LabelConc → Concept
| σ (LabelConc.mk L C) := (LabelToPrefix L) C

definition negLabel: list Label → list Label  -- negation of a list of labels
| negLabel nil := nil
| negLabel ((Label.all R)::L) := (Label.ex R)::(negLabel L)
| negLabel ((Label.ex R)::L) := (Label.all R)::(negLabel L)

definition AppendLabelList (L: list Label) (α: LabelConc) : LabelConc :=
LabelConc.rec_on α (λ(R: list Label) (C: Concept), (L++R)[C])

definition isNullLabelList : list Label → bool
| isNullLabelList nil := tt
| isNullLabelList (L::R) := ff

definition isAllLabel : Label → bool
| isAllLabel (Label.all R) := tt
| isAllLabel (Label.ex R) := ff

definition isExLabel : Label → bool
| isExLabel (Label.all R) := ff
| isExLabel (Label.ex R) := tt

definition internalLabel : list Label → list Label
| internalLabel nil := nil
| internalLabel (R::L) :=
            cond (isNullLabelList L) (R::nil)
                                     (internalLabel L)

definition remainderLabel : list Label → list Label
| remainderLabel nil := nil
| remainderLabel (R::L) :=
    cond (isNullLabelList L) nil
                         (R::(remainderLabel L))

                        
definition downLabelConc : LabelConc → Concept
| downLabelConc (LabelConc.mk L C) := LabelToPrefix L C

definition downInternalLabel : LabelConc → LabelConc
| downInternalLabel (LabelConc.mk L C) := LabelConc.mk (remainderLabel L) ((LabelToPrefix (internalLabel L)) C)

definition isOnlyAllLabel : list Label → bool
| isOnlyAllLabel nil := tt
| isOnlyAllLabel ((Label.all R)::L) := isOnlyAllLabel L
| isOnlyAllLabel ((Label.ex R)::L) := ff

definition isOnlyExLabel : list Label → bool
| isOnlyExLabel nil := tt
| isOnlyExLabel ((Label.all R)::L) := ff
| isOnlyExLabel ((Label.ex R)::L) := (isOnlyExLabel L)

definition is_true [reducible] (b : bool) := b = tt

/-
namespace tests -- tests
    constant C: Concept
    constants R1 R2 R3 : Role
    eval internalLabel (Label.ex R3 (Label.ex R1 (Label.all R2 (Label.null))))
    eval remainderLabel (Label.ex R3 (Label.ex R1 (Label.all R2 (Label.null))))
    definition test := LabelConc.mk (Label.ex R3 (Label.ex R1 (Label.all R2 (Label.null)))) C
    eval downInternalLabel test
end tests-/

  -- Structural Rules
  

definition isNil {A: Type} : list A → bool
| isNil nil := tt
| isNil (a :: l) := ff

definition AntecedentWrap : list LabelConc → Concept -- Não está sendo utilizado
| AntecedentWrap nil := ⊤
| AntecedentWrap (α :: L) :=
        list.rec_on L (σ α)
                      (λα2 L2 C2, (σ α)⊓(AntecedentWrap L))
                       
definition ConsequentWrap : list LabelConc → Concept
| ConsequentWrap nil := ⊥
| ConsequentWrap (α :: L) :=
        list.rec_on L (σ α)
                      (λα2 L2 C2, (σ α)⊔(ConsequentWrap L))

definition AInterp [reducible] {I: Interp} : list LabelConc → @Set (Interp.δ I) -- Antecedent Interpretation
| AInterp nil := U
| AInterp (α :: L) := (interp (σ α))∩(AInterp L)

definition CInterp [reducible] {I: Interp} : list LabelConc → @Set (Interp.δ I) -- Consequent Interpretation
| CInterp nil := ∅
| CInterp (α::L) := (interp (σ α))∪(CInterp L)

set_option pp.universes true
set_option unifier.max_steps 1000000

definition AInterp_append {I: Interp} (Δ1 Δ2: list LabelConc) : @AInterp I ((Δ1)++Δ2) = (AInterp Δ1)∩(AInterp Δ2) :=
begin
apply (list.induction_on Δ1),
  apply eq.trans,
    rewrite (eq.refl (nil++Δ2)), apply (eq.refl (AInterp Δ2)),
    rewrite (Inters_commu (AInterp nil) (AInterp Δ2)), apply (eq.symm IntersUniv),
  intro a, intro Δ, intro IndHyp, rewrite (append_cons a Δ Δ2), rewrite {AInterp (a::Δ)}(eq.refl ((interp (σ a))∩(AInterp Δ))), rewrite -(!Inters_assoc), rewrite -IndHyp, 
end

definition CInterp_append {I: Interp} (Δ1 Δ2: list LabelConc) : @CInterp I ((Δ1)++Δ2) = (CInterp Δ1)∪(CInterp Δ2) :=
begin
apply (list.induction_on Δ1),
  apply eq.trans,
    rewrite (eq.refl (nil++Δ2)), apply (eq.refl (CInterp Δ2)),
    rewrite (Union_commu (CInterp nil) (CInterp Δ2)), rewrite {CInterp nil}(eq.refl ∅), rewrite -(eq.symm UnionEmpty),
  intro a, intro Δ, intro IndHyp, rewrite (append_cons a Δ Δ2), rewrite {CInterp (a::Δ)}(eq.refl ((interp (σ a))∪(CInterp Δ))), rewrite -(!Union_assoc), rewrite -IndHyp,
end

inductive sequent (Δ : list LabelConc) (Γ: list LabelConc) : Prop :=
infix `⇒`:51 := sequent
| intro : (∀I: Interp, (@AInterp I Δ) ⊂ CInterp Γ) → Δ⇒Γ
infix `⇒`:51 := sequent

-- Duas definições apenas para conseguir usar a notação {a,b} para as listas de LabelConc e somente para elas
definition label_conc_append (a: list LabelConc) (b: list LabelConc): list LabelConc := append a b
local notation `{` a `,` b`}` := label_conc_append a b

definition label_conc_cons (a: list LabelConc) (b: LabelConc): list LabelConc := b::a
local notation `{` b `,` a`}` := label_conc_cons a b -- notation overload

definition label.to_labellist [coercion] (l: Label) : list Label := l::nil
definition Concept.to_LabelConc [coercion] (C: Concept) : LabelConc := nil[C]
definition LabelConc.to_ListLabelConc [coercion] (a: LabelConc) : list LabelConc := a::nil

namespace test
constant R : Role
constant C: Concept
constant L: Label
constant M: list Label
check ∀;R
check ∀; R . C
check { M[C] , M[C] }
eval { ((∀;R)::L)[C] , C}
check M[C]
check L[C]
check (∀;R : list Label)[C]
end test

namnespace test2
  constant a: list LabelConc
  constant b: list LabelConc
  constant c: LabelConc
  constant d: Label
  constant e: Concept
  constant d2: Label
  check a++b
  check {a,b}
  check {c,a}
  check {(d::nil)[e],a}
  check {d[e],a}
  check {(d2::d2::d)[e],a}
  -- Seria interessante conseguir utilizar a notação {a, b, b}...
end test2

namespace sequent

definition meaning {Δ : list LabelConc} {Γ: list LabelConc} (h: Δ⇒Γ) : ∀I: Interp, (@AInterp I Δ) ⊂ CInterp Γ := -- elimination rule for sequents
sequent.rec_on h (assume h2: ∀I: Interp, (@AInterp I Δ) ⊂ CInterp Γ, take I: Interp, h2 I)
end sequent

open Label

inductive SCALCproof (Ω: @Set Prop) : Prop → Prop :=
infix `⊢` : 25 := SCALCproof -- \vdash
| hypo : Π{α: Concept}, Ω⊢(nil[α]::nil)⇒(nil[α]::nil) -- fazer uma coercion concept -> labeled concept
| ex_falsum : Π(α: Concept), Ω⊢(nil[⊥]::nil) ⇒ (nil[α]::nil)
| weak_l : Π(Δ Γ: list LabelConc) (δ: LabelConc), Ω⊢(Δ⇒Γ) → Ω⊢(δ::Δ)⇒Γ
| weak_r : Π(Δ Γ: list LabelConc) (γ: LabelConc), Ω⊢Δ⇒Γ → Ω⊢Δ⇒(γ::Γ)
| contraction_l : Π(Δ Γ: list LabelConc) (δ: LabelConc), Ω⊢(δ::δ::Δ)⇒Γ → Ω⊢(δ::Δ)⇒Γ
| contraction_r : Π(Δ Γ: list LabelConc) (γ: LabelConc), Ω⊢Δ⇒(γ::γ::Γ) → Ω⊢Δ⇒(γ::Γ)
| perm_l : Π(Δ1 Δ2 Γ: list LabelConc) (δ1 δ2: LabelConc), Ω⊢Δ1++(δ1::δ2::Δ2)⇒Γ → Ω⊢(Δ1++(δ2::δ1::Δ2))⇒Γ
| perm_r : Π(Δ Γ1 Γ2: list LabelConc) (γ1 γ2: LabelConc), Ω⊢Δ⇒Γ1++(γ1::γ2::Γ2) → Ω⊢Δ⇒Γ1++(γ2::γ1::Γ2)
| cut : Π(Δ1 Δ2 Γ1 Γ2: list LabelConc) (α: LabelConc), Ω⊢Δ1⇒α::Γ1 → Ω⊢α::Δ2⇒Γ2 → Ω⊢Δ1++Δ2⇒Γ1++Γ2
| and_l : Π(Δ Γ : list LabelConc) (L: list Label) (α β : Concept) (p: is_true (isOnlyAllLabel L)),  Ω⊢(L[α]::L[β]::Δ)⇒Γ → Ω⊢(L[α⊓β]::Δ)⇒Γ
| all_r : Π(Δ Γ: list LabelConc) (L: list Label) (α: Concept) (R: Role), Ω⊢ Δ⇒{ (L++(∀;R))[α], Γ}  → Ω⊢ Δ⇒{ (L[∀;R .α]), Γ}
infix `⊢` : 25 := SCALCproof

definition cut_soundness (Ω: @Set Prop) (Δ1 Δ2 Γ1 Γ2: list LabelConc) (α: LabelConc) : (Ω⊧ Δ1⇒α::Γ1) → (Ω⊧ α::Δ2⇒Γ2) → (Ω⊧ Δ1++Δ2⇒Γ1++Γ2) :=
  assume h: Ω⊧Δ1⇒α::Γ1,
  assume h2: Ω⊧α::Δ2⇒Γ2,
  assume h3: ∀p: Prop, (p∈ Ω → p),
  have l1: Δ1⇒α::Γ1, from h h3,
  have l2: α::Δ2⇒Γ2, from h2 h3,
  have l3: ∀I: Interp, AInterp Δ1 ⊂ CInterp (α::Γ1), from sequent.meaning l1,
  have l4: ∀I: Interp, AInterp (α::Δ2) ⊂ CInterp Γ2, from sequent.meaning l2,
  assert l5: (∀I: Interp, AInterp Δ1 ⊂ (interp (σ α)∪(CInterp Γ1))), from
    take I: Interp,
    eq.subst rfl (l3 I),
  assert l6: (∀I: Interp, (@interp I (σ α)) ∩ (AInterp Δ2) ⊂ (CInterp Γ2)), from
    take I: Interp,
    eq.subst rfl (l4 I),
  show Δ1++Δ2⇒(Γ1++Γ2), from
    begin
      apply sequent.intro, intro I, rewrite [(AInterp_append Δ1 Δ2), (CInterp_append Γ1 Γ2)], exact (SetCut (l5 I) (l6 I)),
    end

definition drop_last_all_label {L: list Label} {α: Concept} {R: Role} : σ ((L++(∀;R))[α]) = σ(L[∀;R . α]) := sorry

definition all_r_soundness (Ω: @Set Prop) (Δ Γ: list LabelConc) (L: list Label) (α: Concept) (R: Role):
(Ω⊧ (Δ⇒{ (L++(∀;R))[α], Γ}))  →  (Ω⊧ Δ⇒{ L[∀;R .α], Γ}) :=
assume h: Ω⊧( Δ⇒{ (L++(∀;R))[α], Γ}),
assume h2: ∀p: Prop, (p∈Ω → p),
have l1: Δ⇒{ (L++(∀;R))[α], Γ}, from h h2,
assert l2: ∀I: Interp, AInterp Δ ⊂ CInterp { (L++(∀;R))[α], Γ}, from sequent.meaning l1,
assert l3: (σ ((L++(∀;R))[α])) = (σ (L[∀;R . α])), from drop_last_all_label,
have l4: (CInterp {(L++(∀;R))[α], Γ}) = (CInterp {L[∀;R. α], Γ}), from
  begin
    esimp, rewrite l3,
  end,
--have l3: (CInterp {(L++(∀;R))[α], Γ}) = (CInterp {L[∀;R. α], Γ}), from sorry,
show Δ ⇒ {(L[∀;R .α]), Γ}, from
  begin
    apply sequent.intro, intro I,
  end

section hide
constants (Δ Γ: list LabelConc) (L: list Label) (α: Concept) (R: Role)
check (eq.refl (CInterp { (L++(∀;R))[α], Γ}))
end hide

axiom Axiom2_1 (R: Role) (α β: Concept) : ValueRestr R α⊓β ≡ (ValueRestr R α) ⊓ (ValueRestr R β)

/-
definition and_l_soundness (Ω: @Set Prop) (Δ Γ: list LabelConc) (L: list Label) (α β: Concept) (p: is_true (isOnlyAllLabel L)) : (Ω⊧ (L[α]::L[β]::Δ)⇒Γ) → (Ω⊧ (L[α⊓β]::Δ)⇒Γ) :=
  assume h:  Ω⊧ (L[α]::L[β]::Δ)⇒Γ,
  assume h2: ∀q: Prop, (q∈ Ω → q),
  assert l1: (L[α]::L[β]::Δ)⇒Γ, from h h2,
  begin
    apply sequent.meaning,
  end
-/
end ALC
