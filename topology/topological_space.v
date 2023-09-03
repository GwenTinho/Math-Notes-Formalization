Definition P (A : Type) := A -> Prop.

Notation "{ x : A | P }" := (fun x : A => P).

Definition singleton {A : Type} (x : A) := { y : A | x = y }.

Definition subset {A : Type} (u v : P A) :=
  forall x : A, u x -> v x.

Notation "u <= v" := (subset u v).

Definition disjoint {A : Type} (u v : P A) :=
  forall x, ~ (u x /\ v x).

Notation "'all' x : U , P" := (forall x, U x -> P) (at level 20, x at level 99).

Notation "'some' x : U , P" := (exists x, U x /\ P) (at level 20, x at level 99).

Definition union_family {A : Type} (S : P (P A)) :=
  { x : A | some U : S , U x }.

Definition union {A: Type} (u v : P A) := {x : A | u x \/ v x}.

Definition inter {A : Type} (u v : P A) :=
  { x : A | u x /\ v x }.

Notation "u * v" := (inter u v).
Notation "u + v" := (union u v).


Definition empty {A : Type} := { x : A | False }.

Definition full {A : Type} := { x : A | True }.

Structure topology (A : Type) := {
  open :> P A -> Prop ;
  empty_open : open empty ;
  full_open : open full ;
  inter_open : all u : open, all v : open, open (u * v) ;
  union_open : forall S, S <= open -> open (union_family S)
}.

Definition discrete (A : Type) : topology A.
Proof.
  exists full ; firstorder.
Defined.

Definition indiscrete (A : Type) : topology A.
Proof.
  exists { u : P A | forall x : A, u x -> (forall y : A, u y) } ; firstorder.
Defined.

Definition T1 {A : Type} (T : topology A) :=
  forall x y : A,
    x <> y ->
      some u : T, (u x /\ ~ (u y)).

Definition hausdorff {A: Type} (T : topology A) :=
  forall x y : A,
  x <> y ->
  some u : T, some v: T, (u x /\ v y /\ disjoint u v).


Lemma discrete_hausdorff {A : Type} : hausdorff (discrete A).
Proof.
  intros x y N.
  exists { z : A | x = z } ; split ; [exact I | idtac].
  exists { z : A | y = z } ; split ; [exact I | idtac].
  repeat split ; auto.
  intros z [? ?].
  absurd (x = y); auto.
  transitivity z; auto.
Qed.

Lemma hausdorff_is_T1 {A : Type} (T : topology A) :
  hausdorff T -> T1 T.
Proof.
  intros H x y N.
  destruct (H x y N) as [u [? [v [? [? [? G]]]]]].
  exists u ; repeat split ; auto.
  intro.
  absurd (u y /\ v y).
  auto.
  split.
  apply H4.
  apply H3.
Qed.

Definition image {X Y : Type} (f : X -> Y) (A : P X) := {y : Y | some x: A, (f x = y) }.

Definition inverse_image {X Y : Type} (f : X -> Y) (A : P Y) := {x : X | some y: A, (f x = y)}.

Definition continuous {X Y: Type} (f : X -> Y) :=
  topology X /\ topology Y /\


