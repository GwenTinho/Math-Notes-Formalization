Section Group.

Variable G:Set.
(* G is not an empty set. At least one element exists. *)
Variable e:G.
Variable inv:G->G.
Variable mult:G->G->G.
Notation "a * b" := (mult a b).
Notation "!" := inv.
Variable assoc: forall a b c, a*(b*c) = (a*b)*c.
Variable idenr: forall a, a * e = a.
Variable idenl: forall a, e * a = a.
Variable invl: forall a, !a * a = e.
Variable invr: forall a, a * !a = e.


Lemma move_inv1 : forall a b, a = b -> a * !b = e.
Proof.
    intros.
    rewrite H.
    rewrite invr.
    reflexivity.
Qed.

Lemma move_inv2 : forall a b c, a = b * c -> a * !c = b.
Proof.
    intros.
    rewrite H.
    replace (b * c * !c) with (b * (c * !c)).
    rewrite invr.
    rewrite idenr.
    reflexivity.
    rewrite assoc.
    reflexivity.
Qed.

Lemma move_inv3 : forall a b c, a * c = b * c -> a = b.
Proof.
    intros.
    specialize (move_inv2 (a*c) b c).
    intros.
    apply H0 in H.
    replace (a * c * !c) with (a * (c * !c)) in H.
    rewrite invr in H.
    rewrite idenr in H.
    apply H.
    rewrite assoc.
    reflexivity.
Qed.

Lemma inv_involutive: forall a, !(!a) = a.
Proof.
    intros.
    specialize (move_inv3 (a) (!(!a)) (!a)).
    rewrite invr.
    rewrite invl.
    intro.
    assert (e = e). reflexivity.
    apply H in H0.
    symmetry.
    apply H0.
Qed.

Lemma mult_eq : forall a b c, a = b -> a * c = b * c.
Proof.
    intros.
    specialize (move_inv2 a (b * c) (!c)).
    intros.
    replace (b) with (b * c * !c) in H.
    apply H0 in H.
    replace (a* !(!c)) with (a * c) in H.
    apply H.
    rewrite inv_involutive.
    reflexivity.
    replace (b* c * !c) with (b * (c * !c)).
    rewrite invr.
    rewrite idenr.
    reflexivity.
    rewrite assoc.
    reflexivity.
Qed.



Theorem inv_mult: forall a b, !(a*b) = !b * !a.
Proof.
    intros.
    assert (!(a * b) * (a * b) = e).
    rewrite invl.
    reflexivity.
    specialize (mult_eq (!(a * b) * (a * b)) (e) (!b)).
    intros.
    apply H0 in H.
    rewrite idenl in H.
    rewrite assoc in H.
    replace (!(a * b) * a * b * !b) with (!(a * b) * a) in H.
    specialize (mult_eq (!(a * b) * a) (!b) (!a)).
    intros.
    apply H1 in H.
    replace (!(a * b) * a * !a) with (!(a * b)) in H.
    apply H.
    replace (!(a * b) * a * !a) with (!(a * b) * (a * !a)).
    rewrite invr.
    rewrite idenr.
    reflexivity.
    rewrite assoc.
    reflexivity.
    replace (!(a * b) * a * b * !b) with (!(a * b) * a * (b * !b)).
    rewrite invr.
    rewrite idenr.
    reflexivity.
    rewrite assoc.
    reflexivity.
Qed.



