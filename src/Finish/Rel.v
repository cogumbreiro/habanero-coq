Require Import HJ.Finish.Syntax.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import HJ.Vars.

Inductive Lt (f:finish) (f':finish) : Prop :=
  lt_def:
    clos_trans finish Sub f f' ->
    Lt f f'.

Inductive Gt (f:finish) (f':finish) : Prop :=
  gt_def:
    clos_trans finish (fun (f1:finish) (f2:finish) => Sub f2 f1) f f' ->
    Gt f f'.

Inductive Le (f:finish) (f':finish) : Prop :=
  le_def:
    clos_refl_trans finish Sub f f' ->
    Le f f'.

Inductive Ge (f:finish) (f':finish) : Prop :=
  ge_def:
    clos_refl_trans finish (fun (f1:finish) (f2:finish) => Sub f2 f1) f f' ->
    Ge f f'.

Module Notations.
  Notation "f < f'" := (Lt f f') : finish_scope.

  Notation "f > f'" := (Gt f f') : finish_scope.

  Notation "f <= f'" := (Le f f') : finish_scope.

  Notation "f >= f'" := (Ge f f') : finish_scope.
End Notations.

Import Notations.
Local Open Scope finish_scope.

Lemma lt_to_gt:
  forall f f',
  f < f' ->
  f' > f.
Proof.
  intros.
  inversion H; clear H.
  induction H0.
  - auto using gt_def, t_step.
  - inversion IHclos_trans1; inversion IHclos_trans2.
    eauto using gt_def, t_trans.
Qed.

Lemma gt_to_lt:
  forall f f',
  f > f' ->
  f' < f.
Proof.
  intros.
  destruct H.
  induction H.
  - auto using lt_def, t_step.
  - inversion IHclos_trans1; inversion IHclos_trans2.
    eauto using lt_def, t_trans.
Qed.

Lemma gt_lt_spec:
  forall f f',
  f < f' <-> f' > f.
Proof.
  intros.
  split; auto using gt_to_lt, lt_to_gt.
Qed.

Lemma le_to_ge:
  forall f f',
  f <= f' ->
  f' >= f.
Proof.
  intros.
  intuition.
  induction H0.
  - auto using rt_step.
  - auto using rt_refl.
  - eauto using rt_trans.
Qed.

Lemma lt_sub:
  forall x y,
  Sub x y ->
  x < y.
Proof.
  intros.
  intuition.
Qed.

Lemma lt_to_le:
  forall f f',
  f < f' ->
  f <= f'.
Proof.
  intros.
  intuition.
  induction H0.
  - auto using rt_step.
  - eauto using rt_trans.
Qed.

Lemma le_sub:
  forall x y,
  Sub x y ->
  x <= y.
Proof.
  intros; auto using lt_sub, lt_to_le.
Qed.

Lemma gt_to_ge:
  forall f f',
  f > f' ->
  f >= f'.
Proof.
  intros.
  intuition.
  induction H0.
  - auto using rt_step.
  - eauto using rt_trans.
Qed.

Lemma ge_to_le:
  forall f f',
  f >= f' ->
  f' <= f.
Proof.
  intros.
  intuition.
  induction H0.
  - auto using rt_step.
  - auto using rt_refl.
  - eauto using rt_trans.
Qed.

Lemma ge_le_spec:
  forall f f',
  f <= f' <-> f' >= f.
Proof.
  intros; split; auto using ge_to_le, le_to_ge.
Qed.

Lemma le_inv:
  forall f f',
  f <= f' ->
  f < f' \/ f = f'.
Proof.
  intros.
  intuition.
  induction H0.
  - intuition.
  - intuition.
  - destruct IHclos_refl_trans1, IHclos_refl_trans2.
    + left; intuition.
      eauto using t_trans.
    + subst.
      intuition.
    + subst; intuition.
    + subst; intuition.
Qed.

Lemma le_trans:
  forall f1 f2 f3,
  f1 <= f2 ->
  f2 <= f3 ->
  f1 <= f3.
Proof.
  intros.
  intuition.
  eauto using rt_trans.
Qed.

Lemma le_refl:
  forall f,
  f <= f.
Proof.
  intros.
  intuition.
Qed.

Lemma ge_inv:
  forall f f',
  f >= f' ->
  f > f' \/ f = f'.
Proof.
  intros.
  intuition.
  induction H0.
  - intuition.
  - intuition.
  - destruct IHclos_refl_trans1, IHclos_refl_trans2.
    + left; intuition.
      eauto using t_trans.
    + subst.
      intuition.
    + subst; intuition.
    + subst; intuition.
Qed.

Lemma sub_inv_cons_ready:
  forall f t l,
  Sub f (Node ((t, Ready) :: l)) ->
  Sub f (Node l).
Proof.
  intros.
  inversion H.
  assert ((t,Ready) <> (t0, Blocked f)). {
    intuition.
    inversion H1.
  }
  eauto using sub_def, child_neq.
Qed.

Lemma sub_eq:
  forall f t l,
  Sub f (Node ((t, Blocked f) :: l)).
Proof.
  intros.
  eauto using sub_def, child_eq.
Qed.

Lemma lt_child:
  forall t x y,
  Child (t, Blocked x) y ->
  x < y.
Proof.
  intros.
  apply sub_def in H.
  intuition.
Qed.

Lemma lt_eq:
  forall (f:finish) (t:tid) (l:list l_task),
  f < (Node ((t,Blocked f)::l)).
Proof.
  intros.
  auto using lt_def, t_step, sub_eq.
Qed.

Lemma lt_trans:
  forall f1 f2 f3,
  f1 < f2 ->
  f2 < f3 ->
  f1 < f3.
Proof.
  intros; intuition.
  eauto using t_trans.
Qed.

Lemma lt_inv_cons_ready:
  forall f t l,
  f < (Node ((t, Ready) :: l)) ->
  f < (Node l).
Proof.
  intros.
  rewrite gt_lt_spec in *.
  destruct H.
  rewrite clos_trans_t1n_iff in H.
  inversion H.
  - subst.
    eauto using sub_inv_cons_ready, gt_def, t_step.
  - subst.
    apply gt_def.
    apply t_trans with (y).
    + eauto using sub_inv_cons_ready, t_step.
    + auto using clos_t1n_trans.
Qed.

Lemma le_inv_cons_ready:
  forall f t l,
  f <= (Node ((t, Ready) :: l)) ->
  f < (Node l) \/ f = (Node ((t, Ready) :: l)).
Proof.
  intros.
  apply le_inv in H.
  destruct H.
  - left.
    eauto using lt_inv_cons_ready.
  - intuition.
Qed.

Lemma sub_absurd_nil:
  forall f,
  ~ Sub f (Node nil).
Proof.
  intros.
  intuition.
  inversion H.
  apply child_absurd_nil in H0.
  assumption.
Qed.

Lemma lt_absurd_nil:
  forall f,
  ~ f < (Node nil).
Proof.
  intros.
  rewrite gt_lt_spec.
  intuition.
  rewrite clos_trans_tn1_iff in H0.
  induction H0.
  - apply sub_absurd_nil in H; assumption.
  - assumption.
Qed.

Lemma le_inv_nil:
  forall f,
  f <= Node nil ->
  f = Node nil.
Proof.
  intros.
  apply le_inv in H.
  destruct H.
  - apply lt_absurd_nil in H.
    inversion H.
  - assumption.
Qed.

  Lemma le_inv_node_ready:
    forall t y,
    y <= Node ((t, Ready) :: nil) ->
    y = Node ((t, Ready) :: nil).
  Proof.
    intros.
    apply le_inv_cons_ready in H.
    destruct H.
    * apply lt_absurd_nil in H.
      inversion H.
    * subst.
      trivial.
  Qed.

Lemma sub_cons:
  forall f l p,
  Sub f (Node l) ->
  Sub f (Node (p :: l)).
Proof.
  intros.
  inversion H.
  eauto using sub_def, child_cons.
Qed.

Lemma gt_cons:
  forall f l p,
  Node l > f  ->
  Node (p :: l) > f.
Proof.
  intros.
  inversion H; clear H.
  rewrite clos_trans_tn1_iff in H0.
  apply gt_def.
  induction H0.
  - auto using sub_cons, t_step.
  - eauto using t_trans, t_step.
Qed.

Lemma lt_cons:
  forall f l p,
  f < Node l ->
  f < Node (p :: l).
Proof.
  intros.
  rewrite gt_lt_spec in *.
  auto using gt_cons.
Qed.

Lemma sub_inv_cons:
  forall f p l,
  Sub f (Node (p :: l)) ->
  (snd p = Blocked f) \/ Sub f (Node l).
Proof.
  intros.
  inversion H.
  destruct p as  (t', a).
  destruct H0.
  destruct H0.
  * inversion H0.
    intuition.
  * right.
    apply sub_def with (t).
    apply child_def.
    simpl.
    auto.
Qed.

Lemma gt_inv_cons:
  forall t a l f,
  Node ((t, a) :: l) > f ->
  a = Blocked f \/ (exists f', a = Blocked f' /\ f' > f) \/ Node l > f.
Proof.
  intros.
  intuition.
  apply clos_trans_t1n in H0.
  inversion H0.
  - subst.
    apply sub_inv_cons in H.
    destruct H.
    + left; auto.
    + right; right. auto using gt_def, t_step.
  - subst.
    apply sub_inv_cons in H.
    destruct H.
    + simpl in H.
      subst.
      right; left.
      exists y.
      intuition.
      eauto using clos_t1n_trans.
    + right; right.
      eauto using gt_def, t_step, t_trans, clos_t1n_trans.
Qed.

Lemma lt_inv_cons:
  forall t a l f,
  f < Node ((t, a) :: l) ->
  a = Blocked f \/ (exists f', a = Blocked f' /\ f < f') \/ f < Node l.
Proof.
  intros.
  rewrite gt_lt_spec in *.
  apply gt_inv_cons in H.
  destruct H as [?| [(f',(?,?))| ?]]; intuition.
  right; left.
  exists f'.
  rewrite gt_lt_spec.
  intuition.
Qed.

Inductive Any (P: finish -> Prop) (f:finish) : Prop :=
  any_def:
    forall f',
    f' <= f ->
    P f' ->
    Any P f.

Lemma any_cons:
  forall P f t l,
  Any P f ->
  Any P (Node ((t,(Blocked f))::l)).
Proof.
  intros.
  inversion H.
  apply any_def with (f').
  - apply le_inv in H0.
    destruct H0.
    + apply lt_to_le.
      remember (Node _) as y.
      assert (f <  y). {
        subst.
        eauto using lt_eq.
      }
      eauto using lt_trans.
    + subst.
      apply lt_to_le.
      auto using lt_eq.
  - assumption.
Qed.

Lemma any_cons_rhs:
  forall (P:finish->Prop) p l,
  Any P (Node l) ->
  ( (P (Node l)) ->  P (Node (p::l))) ->
  Any P (Node (p::l)).
Proof.
  intros.
  inversion H.
  apply le_inv in H1.
  destruct H1.
  - eauto using any_def, lt_to_le, lt_cons.
  - subst.
    apply any_def with (Node (p :: l)); auto.
    intuition.
Qed.

Lemma any_cons_lt:
  forall (P:finish->Prop) f p l,
  P f ->
  f < Node l ->
  Any P (Node (p :: l)).
Proof.
  intros.
  eauto using any_def, lt_to_le, lt_cons.
Qed.

Lemma any_eq:
  forall (P:finish->Prop) f,
  P f ->
  Any P f.
Proof.
  intros.
  eauto using any_def, le_refl.
Qed.

Lemma any_inv_nil:
  forall P,
  Any P (Node nil) ->
  P (Node nil).
Proof.
  intros.
  inversion H.
  apply le_inv_nil in H0.
  subst; assumption.
Qed.
