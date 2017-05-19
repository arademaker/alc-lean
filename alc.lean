-- import logic.identities logic.axioms.classical data.list
import init.logic init.data.set
open bool list


namespace ALC

constants AtomicConcept AtomicRole : Type

inductive Role : Type
  | Atomic : AtomicRole → Role

inductive Concept : Type 
  | TopConcept : Concept
  | BottomConcept : Concept
  | Atomic :  AtomicConcept → Concept
  | Negation : Concept → Concept
  | Intersection : Concept → Concept → Concept
  | Union : Concept → Concept → Concept
  | Ex : Role → Concept → Concept
  | Al : Role → Concept → Concept

-- open Concept Role

notation      `⊤` := Concept.TopConcept    -- \top
notation      `⊥` := Concept.BottomConcept -- \bot
prefix        `¬` := Concept.Negation      -- \neg
infix     `⊓` :51 := Concept.Intersection  -- \sqcap
infix     `⊔` :51 := Concept.Union         -- \sqcup
notation `E` R . C := Concept.Ex R C
notation `A` R . C := Concept.Al R C 


-- interpretation structure δ is the Universe
structure Interp := 
mk :: (δ : Type)   
      (atom_C : AtomicConcept → set δ)
      (atom_R : AtomicRole → set (δ × δ))


-- Role interpretation
definition r_interp {I : Interp} : Role → set (Interp.δ I × Interp.δ I)  
  | r_interp (Role.Atomic R) := Interp.atom_R I R


definition interp {I: Interp} : Concept → Set -- Concept Interpretation
  | interp ⊤ := U
  | interp ⊥ := ∅
  | interp (Atomic C) := !Interp.atom_C C
  | interp ¬C := ∁(interp C)
  | interp (C1⊓C2) := (interp C1)∩(interp C2)
  | interp (C1⊔C2) := (interp C1)∪(interp C2)
  | interp (∃;R. C) := Set.spec (λa:Interp.δ I, exists b :
                                   Interp.δ I, (a, b)∈(!r_interp R) ∧ b∈(interp C) )
  | interp (ValueRestr R C) := Set.spec (λa:Interp.δ I, forall b :
                                   Interp.δ I, ((a, b)∈(!r_interp R)) → b∈(interp C))

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

definition models_proof (Ω: @Set Prop) (α: Prop) (h: (∀p: Prop, (p∈ Ω → p)) → α) : Ω⊧α
           := h

example (C D : Concept) : C⊓D ⊑ C :=
take (I : Interp),
take x : Interp.δ I,
assume h : x ∈ interp (C⊓D),
have l: x ∈ (interp C)∩(interp D), from h,
have l2: x∈(interp C)∧x∈(interp D), from (iff.elim_left (IntersMember x)) l,
show x∈(interp C), from and.elim_left l2


example (A B : Concept) : A ⊓ B ⊑ A ⊔ B :=  sorry 



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


inductive Label : Type :=
| all : Role → Label
| ex : Role → Label

notation `∀;` R := Label.all R

inductive LabelConc : Type := -- labeled concept
| mk : list Label → Concept → LabelConc

notation L `[` C `]` := LabelConc.mk L C

-- label to prefix
definition LabelToPrefix [reducible] : list Label → (Concept → Concept)
| LabelToPrefix nil C := C
| LabelToPrefix ((Label.all R)::L) C := ∀;R . (LabelToPrefix L C)
| LabelToPrefix ((Label.ex R)::L) C := ∃;R .(LabelToPrefix L C)

definition getLabelList : LabelConc → list Label
| getLabelList (LabelConc.mk L C) := L

definition σ [reducible] : LabelConc → Concept
| σ (LabelConc.mk L C) := (LabelToPrefix L) C

-- negation of a list of labels
definition negLabel: list Label → list Label
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
constants X R : Role
constant C: Concept
constant L: Label
constant M: list Label
check ∃;R
check (L::L)[C]
check ((∀;R) ++ (∀;R))[C]
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
  | and_l : Π(Δ Γ : list LabelConc) (L: list Label) (α β : Concept) (p: is_true (isOnlyAllLabel L)),
    Ω⊢(L[α]::L[β]::Δ)⇒Γ → Ω⊢(L[α⊓β]::Δ)⇒Γ
  | all_r : Π(Δ Γ: list LabelConc) (L: list Label) (α: Concept) (R: Role), Ω⊢ Δ⇒{ (L++(∀;R))[α], Γ} →
    Ω⊢ Δ⇒{ (L[∀;R .α]), Γ}
infix `⊢` : 25 := SCALCproof

definition cut_soundness (Ω: @Set Prop) (Δ1 Δ2 Γ1 Γ2: list LabelConc) (α: LabelConc) :
           (Ω⊧ Δ1⇒α::Γ1) → (Ω⊧ α::Δ2⇒Γ2) → (Ω⊧ Δ1++Δ2⇒Γ1++Γ2) :=
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
      apply sequent.intro, intro I, rewrite [(AInterp_append Δ1 Δ2), (CInterp_append Γ1 Γ2)],
        exact (SetCut (l5 I) (l6 I)),
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
