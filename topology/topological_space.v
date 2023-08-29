Require Import ClassicalEnsembles.

Arguments Intersection {X} U V : rename.
Arguments Full_set {X} : rename.



Record TopOn {X : Type} := mkTopOn
{
  open : Ensemble (Ensemble X)
  ; intersection_open : forall U V, open U -> open V -> open (Intersection U V)
  ; full_open : open Full_set
  ;
}


