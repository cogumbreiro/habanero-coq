Require Import Coq.Lists.SetoidList.

Require Import HJ.Vars.
Require Import HJ.Finish.Lang.

Inductive IsMap : finish -> Prop :=
  is_map_def:
    forall l,
    NoDupA (Map_TID.eq_key (elt:=task)) l ->
    IsMap (Node l).

Lemma is_map_nil:
  IsMap (Node nil).
Proof.
  auto using NoDupA_nil, is_map_def.
Qed.

Lemma is_map_inv_cons:
  forall p l,
  IsMap (Node (p :: l)) ->
  IsMap (Node l).
Proof.
  intros.
  inversion H; subst.
  inversion H1; subst.
  auto using is_map_def.
Qed.

Import Syntax.Notations.

Inductive Valid: finish -> Prop :=
  | valid_nil:
    Valid []
  | valid_cons_ready:
    forall t l,
    Valid (Node l) ->
    ~ In t (Node l) ->
    Valid (Node ((!t)::l))
  | valid_cons_blocked:
    forall t f l,
    Valid f ->
    Valid (Node l) ->
    ~ In t (Node l) ->
    Valid (Node ((t <| f)::l)).


Lemma child_fun:
  forall t f a a',
  IsMap f ->
  Child (t, a) f ->
  Child (t, a') f ->
  a = a'.
Proof.
  intros.
  inversion H.
  subst.
  destruct H0, H1.
  simpl in *.
  induction l.
  { inversion H0. }
  destruct H0, H1.
  - destruct a0; inversion H0; inversion H1; subst; auto.
  - destruct a0; inversion H0; subst; clear H0.
    inversion H2.
    subst.
    contradiction H4.
    apply Map_TID_Extra.eq_key_in_to_ina with (t) (a'); auto.
  - destruct a0; inversion H1; subst; clear H1.
    inversion H2.
    subst.
    contradiction H4.
    apply Map_TID_Extra.eq_key_in_to_ina with (t) (a); auto.
  - inversion H2; subst.
    apply is_map_inv_cons in H.
    auto.
Qed.

Require Import HJ.Finish.LangExtra.

Lemma in_to_ina:
  forall t a l, 
  ~ In t (Node l) ->
  ~ InA (Map_TID.eq_key (elt:=task)) (t, a) l.
Proof.
  intros.
  apply notin_spec in H.
  induction l.
  - intuition.
    inversion H0.
  - apply notin_inv in H.
    destruct a0 as (t', a').
    destruct H as  (?, (?, ?)).
    simpl in H0, H.
    unfold not.
    intros.
    inversion H2.
    + subst.
      apply Map_TID_Extra.eq_key_unfold in H4; auto.
    + subst.
      intuition.
Qed.

Lemma valid_impl_is_map:
  forall f,
  Valid f ->
  IsMap f.
Proof.
  intros f.
  induction f using finish_ind_strong.
  - intros.
    auto using is_map_nil.
  - intros.
    inversion H.
    subst.
    apply is_map_def.
    apply NoDupA_cons.
    + auto using in_to_ina.
    + apply IHf in H2.
      inversion H2.
      assumption.
  - intros.
    inversion H.
    subst.
    apply is_map_def.
    apply NoDupA_cons.
    + auto using in_to_ina.
    + apply IHf0 in H4.
      inversion H4.
      assumption.
Qed.

Inductive CheckLeaf (f:finish) (t:tid) : op -> Prop :=
  | check_begin_async:
    forall t',
    Child (!t) f ->
    ~ In t' f ->
    CheckLeaf f t (BEGIN_ASYNC t')
  | check_end_async:
    Child (!t) f ->
    CheckLeaf f t END_ASYNC
  | check_begin_finish:
    Child (!t) f ->
    CheckLeaf f t BEGIN_FINISH
  | check_end_finish:
    forall f',
    ~ Registered t f' -> (* the task executed its body *)
    Child (t <| f') f ->
    CheckLeaf f t END_FINISH.

Import FinishNotations.

Inductive Check (f:finish) (t:tid) (o:op): Prop :=
  check_def:
    forall f',
    CheckLeaf f' t o ->
    f' <= f ->
    Disjoint f o ->
    Check f t o.
