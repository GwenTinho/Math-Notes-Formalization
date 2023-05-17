Section Vector_Space.

Require Import Field.
Require Import Ring.


Variable V:Type.

(* G is not an empty set. At least one element exists. *)
Variable
    (F: Type)
    (f0: F)
    (f1: F)
    (fadd : F -> F -> F)
    (fmul : F -> F -> F)
    (fainv: F -> F)
    (fminv: F -> F)
    (afield: field_theory f0 f1 fadd fmul (fun x y => fadd x (fainv y)) fainv (fun x y => fmul x (fminv y)) fminv eq)
    .

Variable e:V.
Variable inv:V->V.
Variable add:V->V->V.
Variable mult: F->V->V.
Notation "a * b" := (mult a b).
Notation "a + b" := (add a b).
Notation "!" := inv.
Variable assoc: forall a b c, a+(b+c) = (a+b)+c.
Variable comm: forall a b, a+b = b+a.
Variable idenr: forall a, a + e = a.
Variable invr: forall a, !a + a = e.
Variable distv: forall a u v, a * (u + v) = (a * u) + (a * v).
Variable distf: forall (a b: F) (v: V), (fadd a b) * v = (a * v) + (b * v).

Lemma idenl: forall a, e + a = a.
Proof.
    intro.
    rewrite comm.
    rewrite idenr.
    reflexivity.
Qed.

Lemma invl: forall a, a + !a = e.
Proof.
    intro.
    rewrite comm.
    rewrite invr.
    reflexivity.
Qed.

Lemma f0_not_f1: f0 <> f1.
Proof.
    intro.

Qed.


Lemma zero_times: forall u: V, f0 * u = e.
Proof.
    intro.

Qed.
