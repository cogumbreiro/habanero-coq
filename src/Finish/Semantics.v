Require Import HJ.Finish.Syntax.
Require Import HJ.Finish.Rel.
Require Import HJ.Vars.
Require Import Coq.Lists.List.

Import Rel.
Import Rel.Notations.
Open Scope finish_scope.

Inductive In (t:tid) (f:finish) : Prop :=
  in_def:
    forall f',
    Registered t f' ->
    f' <= f ->
    In t f.

Lemma in_trans:
  forall t f f',
  In t f' ->
  f' < f ->
  In t f.
Proof.
  intros.
  inversion H.
  inversion H1.
  eauto using in_def, lt_to_le, le_trans.
Qed.

Lemma notin_le:
  forall t x y,
  ~ In t x ->
  y <= x ->
  ~ In t y.
Proof.
  intros.
  unfold not; intros.
  destruct H1.
  assert (Le f' x) by eauto using le_trans.
  contradiction H.
  eauto using in_def.
Qed.

Lemma in_eq:
  forall t f l,
  In t (Node ((t, f) :: l)).
Proof.
  intros.
  eauto using in_def, le_refl, registered_eq.
Qed.

Lemma in_cons:
  forall t p l,
  In t (Node l) ->
  In t (Node (p :: l)).
Proof.
  intros.
  destruct H.
  apply le_inv in H0; destruct H0.
  - eauto using lt_to_le, in_def, lt_cons.
  - subst.
    eauto using in_def, le_refl, registered_cons.
Qed.

Lemma in_absurd_nil:
  forall t,
  ~ In t (Node nil).
Proof.
  intros.
  intuition.
  inversion H.
  apply le_inv_nil in H1.
  subst.
  apply registered_absurd_nil in H0.
  assumption.
Qed.

Lemma in_inv_cons:
  forall t t' a l,
  In t (Node ((t',a) :: l)) ->
  t = t' \/ (exists f, a = Blocked f /\ In t f) \/ In t (Node l).
Proof.
  intros.
  destruct H.
  apply le_inv in H0.
  destruct H0.
  - apply lt_inv_cons in H0.
    destruct H0 as [?|[(f1, (?, ?))|?]].
    + subst.
      right; left.
      exists f'.
      intuition.
      eauto using in_def, le_refl.
    + subst.
      right; left.
      exists f1.
      split; eauto using in_def, lt_to_le.
    + right; right.
      eauto using in_def, lt_to_le.
  - subst.
    inversion H.
    destruct H0.
    destruct H0.
    + inversion H0.
      subst; intuition.
    + right; right.
      apply in_def with (Node l); auto.
      eauto using registered_def, child_def.
      auto using le_refl.
Qed.

(** Add task [t] to finish [f]. *)

Fixpoint remove_child (l:list l_task) (t:tid) :=
  match l with
  | (t', f) :: l => 
    if TID.eq_dec t t'
    then remove_child l t
    else (t',f) :: remove_child l t
  | nil => nil
  end.

Definition remove (f:finish) (t:tid) :=
  match f with
  | Node l => Node (remove_child l t)
  end.

Definition put (f:finish) (p:l_task) : finish :=
  Node (p::(get_tasks (remove f (fst p) ))).


Lemma remove_1:
  forall t f,
  ~ Registered t (remove f t).
Proof.
  intros.
  intuition.
  destruct H.
  unfold remove in *.
  destruct f.
  induction l.
  - inversion H.
    simpl in *.
    assumption.
  - simpl in H.
    destruct a0.
    destruct (TID.eq_dec t t0).
    + subst.
      auto.
    + destruct H.
      destruct H.
      * inversion H; subst.
        contradiction n.
        trivial.
      * contradiction IHl.
        auto using child_def.
Qed.

Lemma remove_2:
  forall x y e f,
  x <> y ->
  Child (y, e) f ->
  Child (y, e) (remove f x).
Proof.
  intros.
  unfold remove.
  destruct f.
  induction l.
  - apply child_absurd_nil in H0.
    inversion H0.
  - simpl.
    destruct a.
    destruct (TID.eq_dec x t).
    + subst.
      apply child_inv_cons in H0.
      destruct H0.
      * inversion H0.
        subst.
        contradiction H.
        trivial.
      * auto.
    + apply child_inv_cons in H0.
      destruct H0.
      * inversion H0.
        subst.
        auto using child_eq.
      * apply child_cons.
        auto.
Qed.

Lemma remove_3:
  forall x y e f,
  Child (y, e) (remove f x) ->
  Child (y, e) f.
Proof.
  intros.
  unfold remove in *.
  destruct f.
  induction l; auto.
  simpl in *.
  destruct a.
  destruct (TID.eq_dec x t).
  - subst.
    auto using child_cons.
  - apply child_inv_cons in H.
    destruct H.
    + inversion H.
      subst.
      auto using child_eq.
    + auto using child_cons.
Qed.

Module Notations.
  Infix " |+ " :=  (put) (at level 60, right associativity)  :  finish_scope.
  Infix " |- " :=  (remove) (at level 60, right associativity)  :  finish_scope.
End Notations.


Lemma put_1 :
  forall x e f,
  Child (x, e) (put f (x, e)).
Proof.
  intros.
  apply child_def.
  simpl.
  intuition.
Qed.

Lemma put_2:
  forall x y e e' f,
  x <> y ->
  Child (y, e) f ->
  Child (y, e) (put f (x, e') ).
Proof.
  intros.
  unfold put.
  simpl.
  apply child_cons.
  rewrite get_tasks_rw in *.
  auto using remove_2.
Qed.

Lemma put_3:
  forall x y e e' f,
  x <> y ->
  Child (y, e) (put f (x, e')) ->
  Child (y, e) f.
Proof.
  intros.
  unfold put in *.
  simpl in *.
  apply child_inv_cons in H0.
  destruct H0.
  - inversion H0; subst; clear H0.
    contradiction H.
    trivial.
  - rewrite get_tasks_rw in *.
    eauto using remove_3.
Qed.

(**
  In async/finish all operations are blocking, because a task
  might be stuck in a finish. *)

Inductive op :=
  | BEGIN_ASYNC : tid -> op
  | END_ASYNC
  | BEGIN_FINISH
  | END_FINISH.

Definition is_begin_async (o:op) : bool :=
match o with
  | BEGIN_ASYNC _ => true
  |  _ => false
end.

Inductive Disjoint (f:finish) : op -> Prop :=
  | disjoint_ok:
    forall t,
    ~ In t f ->
    Disjoint f (BEGIN_ASYNC t)
  | disjoint_skip:
    forall o,
    is_begin_async o = false ->
    Disjoint f o.

Lemma disjoint_inv_begin_async:
  forall f t,
  Disjoint f (BEGIN_ASYNC t) ->
  ~ In t f.
Proof.
  intros.
  inversion H.
  - assumption.
  - simpl in H0.
    inversion H0.
Qed.

Lemma disjoint_inv_cons_rhs:
  forall p l o,
  Disjoint (Node ((p :: l))) o ->
  Disjoint (Node l) o.
Proof.
  intros.
  inversion H.
  + apply disjoint_ok.
    intuition.
    contradiction H0.
    apply in_cons.
    assumption.
  + apply disjoint_skip.
    assumption.
Qed.

Lemma disjoint_inv_cons_lhs:
  forall t f l o,
  Disjoint (Node (((t, Blocked f) :: l))) o ->
  Disjoint f o.
Proof.
  intros.
  inversion H.
  + apply disjoint_ok.
    intuition.
    contradiction H0.
    subst.
    eauto using in_trans, lt_eq.
  + apply disjoint_skip.
    assumption.
Qed.

Lemma disjoint_le:
  forall o x y,
  Disjoint x o ->
  y <= x ->
  Disjoint y o.
Proof.
  intros.
  destruct H.
  - eauto using disjoint_ok, notin_le.
  - auto using disjoint_skip. 
Qed.

Import Notations.
Import Syntax.Notations.
Inductive Reduce (f:finish) (t:tid) : op -> finish -> Prop :=
  | begin_async:
    forall t',
    Child (!t) f ->
    ~ In t' f ->
    Reduce f t (BEGIN_ASYNC t') (f |+ ! t')
  | end_async:
    Child (!t) f ->
    Reduce f t END_ASYNC (f |- t)
  | begin_finish:
    Child (!t) f ->
    Reduce f t BEGIN_FINISH (f |+ t <| [!t])
  | end_finish:
    Child (t <| []) f ->
    Reduce f t END_FINISH (f |+ !t)
  | reduce_nested:
    forall t' o f' f'',
    Disjoint f o ->
    Child (t' <| f') f ->
    Reduce f' t o f'' ->
    Reduce f t o (f |+ t' <| f'').

