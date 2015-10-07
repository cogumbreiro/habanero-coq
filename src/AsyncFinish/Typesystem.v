Require Import Coq.Lists.SetoidList.

Require Import HJ.Vars.
Require Import HJ.AsyncFinish.Lang.

Definition IsMap := (NoDupA (Map_TID.eq_key (elt:=task))).

Inductive Valid: finish -> Prop :=
  | valid_nil:
    Valid (Node nil)
  | valid_cons_ready:
    forall t l,
    Valid (Node l) ->
    ~ In t (Node l) ->
    Valid (Node ((t,Ready)::l))
  | valid_cons_blocked:
    forall t f l,
    Valid f ->
    Valid (Node l) ->
    ~ In t (Node l) ->
    Valid (Node ((t,Blocked f)::l)).

Module SubjectReduction.
Import Semantics.
(*
Lemma is_map_cons:
  forall t l a,
  IsMap l -> 
  ~ In t (Node l) ->
  IsMap ((t,a) :: l).
Proof.
  intros.
  unfold IsMap in *.
  apply NoDupA_cons.
*)

Lemma remove_notin:
  forall t l,
  ~ In t (Node l) ->
  remove_child l t = l.
Proof.
  intros.
  simpl.
  induction l.
  - auto.
  - simpl.
    destruct a as (t', a).
    destruct (TID.eq_dec t t').
    + subst.
      contradiction H.
      apply in_eq.
    + assert (Heq: (remove_child l t) = l). {
        apply IHl.
        intuition.
        auto using in_cons_rhs.
      }
      repeat rewrite Heq.
      trivial.
Qed.

Require Import HJ.AsyncFinish.LangExtra.

Lemma notin_remove:
  forall t l t' ,
  ~ In t (Node l) ->
  ~ In t (Node (remove_child l t')).
Proof.
  intros.
  rewrite notin_spec in *.
  induction l.
  - auto.
  - destruct a as (t'', a).
    simpl remove_child.
    apply notin_inv in H.
    destruct H as (?, (?, ?)).
    destruct (TID.eq_dec t' t'').
    + subst.
      auto.
    + auto using notin_cons.
Qed.

Theorem subject_reduction:
  forall f t,
  Valid f ->
  Valid (remove f t).
Proof.
  intros.
  unfold remove.
  destruct f.
  induction l.
  - auto.
  - destruct a as (t', a).
    simpl.
    destruct (TID.eq_dec t t').
    + subst.
      inversion H; auto.
    + assert (Valid (Node (remove_child l t))). { inversion H; auto. }
      clear IHl.
      inversion H.
      * subst.
        auto using valid_cons_ready, notin_remove.
      * subst.
        auto using valid_cons_blocked, notin_remove.
Qed.

Theorem subject_reduction:
  forall f t o f',
  Valid f ->
  Reduce f t o f' ->
  Valid f'.
Proof.
  intros.
  inversion H0.
  - subst.
Admitted.
End SubjectReduction.