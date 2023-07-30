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







