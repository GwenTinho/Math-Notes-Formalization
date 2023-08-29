Lemma double_neg_intro: forall a : Prop, a -> ~~a.
Proof.
    intros.
    unfold not.
    intros.
    apply H0 in H.
    apply H.
Qed.

Lemma contrapositive: forall a b : Prop, (a -> b) -> (~b -> ~a).
Proof.
    intros.
    unfold not in H0.
    unfold not.
    intros.
    apply H in H1.
    apply H0 in H1.
    apply H1.
Qed.

Lemma curry : forall a b c : Prop, (a /\ b -> c) <-> (a -> b -> c).
Proof.
    split.
    intros H s t.
    apply H.
    split.
    exact s.
    exact t.
    intros.
    destruct H0 as [p q].
    apply H.
    exact p.
    exact q.
Qed.




Lemma neg_intro: forall a b : Prop, ((a -> b) /\ (a -> ~b)) -> ~a.
Proof.
    intros.
    unfold not in *.
    intros.
    destruct H as [f nf].
    apply nf.
    exact H0.
    apply f.
    exact H0.
Qed.

Theorem abcd_c : forall (A:Set)(a b c d:A), a=c \/ b= c \/ c=c \/ d=c.
Proof.
    intros.
    right.
    right.
    left.
    reflexivity.
Qed.

Lemma and_assoc : forall A B C:Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
    intros A B C [a [b c]].
    repeat split.
    exact a.
    exact b.
    exact c.
Qed.


Lemma and_imp_dist : forall A B C D:Prop,
   (A -> B) /\ (C -> D) -> A /\ C -> B /\ D.
Proof.
    intros A B C D [f g] [a c].
    split.
    apply f.
    exact a.
    apply g.
    exact c.
Qed.


Lemma not_contrad : forall A : Prop, ~(A /\ ~A).
Proof.
    unfold not.
    intros A [a na].
    apply na.
    exact a.
Qed.

Lemma absurd : forall A : Prop, False -> A.
Proof.
    intro A.
    assert (False -> A -> False).
    intros.
    exact H.
    apply neg_intro.


Lemma or_and_not : forall A B : Prop, (A\/B)/\~A -> B.
Proof.
    unfold not.
    intros A B [aob na].
    destruct aob as [p | q].
    assert (False -> B).
    intros.


Qed.






