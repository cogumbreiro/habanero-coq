Require Import Lists.List.
Require Import Coq.Relations.Relations.

Section REL_DEC.

Variable A: Type.

Variable R: A -> A -> Prop.

Variable pairs : list (A * A) % type.

Lemma clos_trans_dec (rel_spec: forall x y,
  R x y <-> In (x, y) pairs):
  forall x y,
  { clos_trans A R x y } + { ~ clos_trans A R x y }.
Proof.
  intros.
  destruct pairs.
  - 
  assert (Hx := rel_spec x y).
Admitted.

End REL_DEC.
