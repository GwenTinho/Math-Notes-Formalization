Require Import Ensembles.
Require Import Classical_Prop.
Require Import PropExtensionality.
Require Import FunctionalExtensionality.
Require Import FinFun.

Require Export Ensembles.

Local Notation "x 'in' X" := (In _ X x)
(at level 69).
Local Notation "A 'sub' B" := (Included _ A B)
(at level 69).
Local Notation "A 'inter' B" := (Intersection _ A B)
(at level 67, right associativity).
Local Notation "A 'union' B" := (Union _ A B)
(at level 68, right associativity).
Local Notation "¬ A" := (Complement _ A)
(at level 66).

Local Arguments Empty_set {U}.
Local Arguments Full_set {U}.


Inductive FamilyUnion {X I} (F : I -> Ensemble X): Ensemble X :=
| Union_intro : forall x:X, forall i:I, x in (F i) -> x in (FamilyUnion F).

Theorem intersection_char {X} (A B : Ensemble X) x :
    (x in A inter B) = (x in A /\ x in B).
Proof.
    apply propositional_extensionality.
    split.
    intros p.
    destruct p.
    split.
    exact H.
    exact H0.
    intros [a b].
    auto with sets.
Qed.

Theorem union_char {X} (A B : Ensemble X) x :
    (x in A union B) = (x in A \/ x in B).
Proof.
    apply propositional_extensionality.
    split.
    intros p.
    destruct p; auto.
    intros []; auto with sets.
Qed.


Theorem empty_char {X}  (x : X) :
    x in Empty_set = False.
Proof.
    apply propositional_extensionality.
    split.
    intros [].
    intros [].
Qed.
