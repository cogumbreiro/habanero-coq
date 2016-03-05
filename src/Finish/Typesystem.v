Require Import Coq.Lists.SetoidList.

Require Import HJ.Vars.
Require Import HJ.Finish.Lang.

Section Defs.

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

Lemma is_map_nil_cons:
  forall t a,
  IsMap (Node ((t, a) :: nil)).
Proof.
  intros.
  apply is_map_def.
  apply NoDupA_cons.
  - intuition.
    inversion H.
  - auto using NoDupA_nil.
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


  Lemma is_map_inv_cons_alt:
    forall t t' a a' l,
    IsMap (Node ((t', a') :: l)) ->
    Child (t, a) (Node ((t', a') :: l)) ->
    (t' = t /\ a' = a /\ ~ Registered t (Node l)) \/ (t <> t' /\ ~ Registered t' (Node l) /\ Child (t, a) (Node l)).
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H2; clear H2; subst.
    destruct H0.
    simpl in *.
    destruct H.
    - left.
      inversion H; subst.
      try (repeat split; auto).
      eauto using not_in_a_to_not_registered.
    - right.
      destruct (TID.eq_dec t t').
      + subst.
        contradiction H3.
        rewrite InA_alt.
        exists (t', a).
        split; auto.
        apply Map_TID_Extra.eq_key_unfold; auto.
      + split; auto.
        split; eauto using child_def, not_in_a_to_not_registered.
  Qed.

  Lemma in_a_remove:
    forall t a x,
    ~ InA (Map_TID.eq_key (elt:=task)) (t, a) (get_tasks (remove x t)).
  Proof.
    intros.
    intuition.
    apply ina_to_registered in H.
    rewrite get_tasks_rw in *.
    apply remove_1 in H.
    assumption.
  Qed.

  Let in_a_remove_child:
    forall t t' a l,
    InA (Map_TID.eq_key (elt:=task)) (t', a) (remove_child l t) ->
    InA (Map_TID.eq_key (elt:=task)) (t', a) l.
  Proof.
    intros.
    induction l; auto.
    inversion H; clear H.
    - destruct a0 as (t'', a').
      destruct y as (ty, ay).
      destruct (TID.eq_dec t t'').
      + subst.
        rewrite  <- H0 in *.
        auto using InA_cons_hd.
      + inversion H0; subst.
        apply Map_TID_Extra.eq_key_unfold in H1; auto.
    - destruct a0 as (t'', a').
      destruct y as (ty, ay).
      apply InA_cons_tl.
      destruct (TID.eq_dec t t'').
      + subst.
        assert (InA (Map_TID.eq_key (elt:=task)) (t', a) (remove_child l t'')). {
          assert (InA (Map_TID.eq_key (elt:=task)) (t', a) ((ty,ay)::l0)). {
            eauto using InA_cons_tl.
          }
          rewrite <- H0.
          assumption.
        }
        auto.
      + inversion H0.
        subst.
        auto.
  Qed.

  Let no_dup_a_remove_child:
    forall l t,
    NoDupA (Map_TID.eq_key (elt:=task)) l ->
    NoDupA (Map_TID.eq_key (elt:=task)) (remove_child l t).
  Proof.
    intros.
    induction l; auto.
    simpl.
    destruct a as (t', a).
    inversion H; subst.
    destruct (TID.eq_dec t t').
    - subst.
      auto.
    - apply NoDupA_cons; auto.
      unfold not; intros.
      contradiction H2.
      eauto using in_a_remove_child.
  Qed.

  Lemma is_map_remove:
    forall t f,
    IsMap f ->
    IsMap (remove f t).
  Proof.
    intros.
    destruct f.
    apply is_map_def; intros.
    inversion H; subst.
    auto.
  Qed.

  Lemma is_map_put:
    forall t a x,
    IsMap x ->
    IsMap (put x (t, a)).
  Proof.
    intros.
    apply is_map_def; intros.
    apply NoDupA_cons.
    - simpl.
      auto using in_a_remove.
    - apply is_map_remove with (t:=t) in H.
      inversion H; subst; simpl.
      rewrite <- H0.
      simpl.
      auto.
  Qed.

  Lemma reduces_preserves_is_map:
    forall x t o y,
    IsMap x ->
    Reduce x t o y ->
    IsMap y.
  Proof.
    intros.
    inversion H0; subst; auto using is_map_put.
    auto using is_map_remove.
  Qed.
End Defs.

Import Syntax.Notations.
Import FinishNotations.

(** Well-formed tasks. *)

Inductive WFTasks (f:finish) : Prop :=
  wf_tasks_def:
    (forall x, x <= f -> IsMap x) ->
    WFTasks f.


Lemma wf_tasks_le:
  forall x y,
  WFTasks y ->
  x <= y ->
  WFTasks x.
Proof.
  intros.
  apply wf_tasks_def.
  intros f; intros.
  assert (f <= y) by eauto using le_trans.
  inversion H; eauto.
Qed.

Lemma wf_tasks_child_fun:
  forall t f a a',
  WFTasks f ->
  Child (t, a) f ->
  Child (t, a') f ->
  a = a'.
Proof.
  intros.
  assert (f <= f) by eauto using le_refl.
  assert (IsMap f) by (destruct H; eauto).
  eauto using child_fun.
Qed.

Lemma wf_tasks_to_is_map:
  forall f,
  WFTasks f ->
  IsMap f.
Proof.
  intros.
  inversion H.
  eauto using le_refl.
Qed.

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


Inductive Check (f:finish) (t:tid) (o:op): Prop :=
  check_def:
    forall f',
    CheckLeaf f' t o ->
    f' <= f ->
    Disjoint f o ->
    Check f t o.
