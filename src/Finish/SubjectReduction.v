Require Import Coq.Lists.SetoidList.

Require Import HJ.Vars.

Require Import HJ.Finish.Syntax.
Require Import HJ.Finish.Semantics.
Require Import HJ.Finish.IEF.
Require Import HJ.Finish.Rel.
Require Import HJ.Finish.LangExtra.

Import Rel.Notations.



Section Props.

  Require Import HJ.Finish.Typesystem.

  Lemma wf_tasks_child_absurd_neq:
    forall f t a,
    WFTasks (put f (t, Blocked a)) ->
    ~ Child (t, Ready) (put f (t, Blocked a)).
  Proof.
    intros.
    unfold not.
    intros.
    assert (Child (t, Blocked a) (put f (t, Blocked a)))
    by eauto using put_1.
    assert (A: Ready = Blocked a) by eauto using wf_tasks_child_fun.
    inversion A.
  Qed.

  Lemma wf_tasks_put_ready:
    forall f t,
    WFTasks f ->
    WFTasks (put f (t, Ready)).
  Proof.
    intros.
    apply wf_tasks_def; intros z ?.
    apply le_inv_put_ready in H0.
    destruct H0.
    - inversion H.
      eauto using lt_to_le.
    - subst.
      auto using is_map_put, wf_tasks_to_is_map.
  Qed.

  Lemma wf_tasks_remove:
    forall f t,
    WFTasks f ->
    WFTasks (remove f t).
  Proof.
    intros.
    apply wf_tasks_def; intros z ?.
    apply le_inv in H0.
    destruct H0.
    - apply lt_remove_1 in H0.
      apply lt_to_le in H0.
      inversion H; eauto.
    - subst.
      auto using is_map_remove, wf_tasks_to_is_map.
  Qed.

  Lemma wf_tasks_put_blocked:
    forall x y t,
    WFTasks x ->
    WFTasks y ->
    WFTasks (put x (t, Blocked y)).
  Proof.
    intros.
    apply wf_tasks_def; intros z ?.
    apply le_inv_put_blocked in H1.
    destruct H1 as [?|[?|?]].
    - subst.
      auto using is_map_put, wf_tasks_to_is_map.
    - apply lt_to_le in H1.
      inversion H; eauto.
    - inversion H0; eauto.
  Qed.

  Lemma wf_tasks_begin_finish:
    forall f t t',
    WFTasks f ->
    WFTasks (put f (t, Blocked (Node ((t', Ready) :: nil)))).
  Proof.
    intros.
    apply wf_tasks_put_blocked; eauto.
    apply wf_tasks_def; intros z ?.
    apply le_inv_node_ready in H0.
    subst.
    auto using is_map_nil_cons.
  Qed.

  Lemma wf_tasks_le:
    forall x y,
    WFTasks x ->
    y <= x ->
    WFTasks y.
  Proof.
    intros.
    apply wf_tasks_def; intros z ?.
    assert (z <= x) by eauto using le_trans.
    inversion H; eauto.
  Qed.

  Lemma sr_wf_task:
    forall x t o y,
    WFTasks x ->
    Reduce x t o y ->
    WFTasks y.
  Proof.
    intros.
    induction H0; subst.
    - auto using wf_tasks_put_ready.
    - auto using wf_tasks_remove.
    - auto using wf_tasks_begin_finish.
    - auto using wf_tasks_put_ready.
    - apply wf_tasks_put_blocked; auto.
      eauto using lt_child, lt_to_le, wf_tasks_le.
  Qed.

  Lemma ief_put:
    forall x y f a,
    IEF x (put f (y, a)) ->
    x = y \/ (x <> y /\ IEF x f).
  Proof.
    intros.
    destruct (TID.eq_dec y x). {
        subst.
        intuition.
    }
    right.
    inversion H.
    - eauto using put_3, ief_ready.
    - eauto using put_3, ief_blocked.
  Qed.

  Lemma child_inv_put:
    forall t f a b,
    WFTasks (put f (t, b)) ->
    Child (t, a) (put f (t, b)) ->
    a = b.
  Proof.
    intros.
    assert (Child (t, b) (put f (t, b))) by eauto using put_1.
    eauto using wf_tasks_child_fun.
  Qed.

  Lemma ief_put_inv_blocked:
    forall t t' x y,
    WFTasks (put x (t, Blocked y)) ->
    IEF t' (put x (t, Blocked y)) ->
    (t' = t /\ ~ Registered t y) \/ (t' <> t /\ IEF t' x).
  Proof.
    intros.
    assert (Hx := H0).
    apply ief_put in H0.
    destruct H0 as [?|(?,?)].
    - subst.
      inversion Hx.
      + apply child_inv_put in H0; auto.
        inversion H0.
      + apply child_inv_put in H0; auto.
        inversion H0; subst.
        intuition.
    - intuition.
  Qed.

  Variable f:finish.
  Variable WF2: WFTasks f.
  Variable WF3: UniqueIEF f.
  Variable WF4: IEFFun f.

  Lemma unique_ief_begin_async:
    forall t,
    ~ In t f ->
    UniqueIEF (put f (t, Ready)).
  Proof.
    intros.
    apply unique_child_def.
    intros x t'; intros.
    apply le_inv_put_ready in H0.
    destruct H0.
    - destruct WF3 as (Hx).
      eauto using lt_to_le.
    - subst.
      apply ief_put in H1.
      destruct H1 as [?|(_,?)].
      + subst.
        eauto using notin_lt, lt_put_1.
      + apply lt_put_1 in H2.
        destruct WF3 as (Hx).
        eauto using le_refl.
  Qed.

  Let ief_in_ex:
    forall x y t,
    x < y ->
    IEF t x ->
    In t x.
  Proof.
    eauto using in_trans, ief_in.
  Qed.

  Lemma ief_to_in:
    forall y t,
    y < f ->
    IEF t y ->
    In t f.
  Proof.
    eauto using in_trans, ief_in.
  Qed.

  Lemma ief_notin_sub:
    forall x t,
    x < f ->
    IEF t f ->
    ~ In t x.
  Proof.
    intros.
    destruct WF3 as (Hx).
    eauto using le_refl.
  Qed.

  Lemma ief_dup:
    forall x t t1,
    x < f ->
    IEF t1 x ->
    IEF t1 (put f (t, Ready)) ->
    In t f.
  Proof.
    intros.
    eauto.
    apply ief_put in H1.
    destruct H1 as [?|(_,?)].
    + subst.
      eauto using ief_to_in.
    + assert (i: ~ In t1 x) by eauto using ief_notin_sub.
      contradiction i.
      eauto using ief_in.
  Qed.

  Lemma lt_ief_in:
    forall x t,
    x < f ->
    IEF t x ->
    In t f.
  Proof.
    eauto using ief_dup, ief_to_in.
  Qed.

  Lemma ief_fun_begin_async:
    forall t,
    ~ In t f ->
    IEFFun (put f (t, Ready)).
  Proof.
    intros.
    apply ief_fun_def.
    intros x y t1; intros.
    apply le_inv_put_ready in H0.
    apply le_inv_put_ready in H2.
    destruct H0, H2; subst; auto.
    - destruct WF4; eauto using lt_to_le.
    - contradiction H; eauto using ief_dup.
    - contradiction H; eauto using ief_dup.
  Qed.

  Lemma unique_ief_fun_begin_async:
    forall t,
    ~ In t f ->
    UniqueIEF (put f (t, Ready)) /\ IEFFun (put f (t, Ready)).
  Proof.
    intros.
    split; auto using ief_fun_begin_async, unique_ief_begin_async.
  Qed.

  Lemma ief_child_put_ready:
    forall t y,
    Child (t, Blocked (Node nil)) f ->
    y < put f (t, Ready) ->
    ~ In t y.
  Proof.
    destruct WF3 as (Hx).
    eauto using lt_put_1, le_refl, ief_blocked, registered_absurd_nil.
  Qed.

  Lemma unique_ief_end_finish:
    forall t,
    Child (t, Blocked (Node nil)) f ->
    UniqueIEF (put f (t, Ready)).
  Proof.
    intros.
    apply unique_child_def.
    intros x t'; intros.
    apply le_inv_put_ready in H0.
    destruct H0.
    - destruct WF3 as (Hx).
      eauto using lt_to_le.
    - subst.
      apply ief_put in H1.
      destruct H1 as [?|(_,?)].
      + subst.
        eauto using ief_child_put_ready.
      + destruct WF3 as (Hx).
        eauto using lt_put_1, le_refl.
  Qed.

  Lemma abs_ief_1:
    forall t y,
    y < f ->
    IEF t y ->
    IEF t f ->
    False.
  Proof.
    intros.
    assert (Hi: ~ In t y) by (eapply ief_notin_sub; eauto).
    contradiction Hi.
    auto using ief_in.
  Qed.

  Lemma abs_ief_2:
    forall t x,
    Child (t, Blocked (Node nil)) f ->
    x < f ->
    IEF t x ->
    False.
  Proof.
    eauto using ief_blocked, registered_absurd_nil, abs_ief_1.
  Qed.

  Lemma abs_ief_3:
    forall t x t1,
    Child (t, Blocked (Node nil)) f ->
    x < f ->
    IEF t1 x ->
    IEF t1 (put f (t, Ready)) ->
    False.
  Proof.
    intros.
    apply ief_put in H2.
    destruct H2; subst.
    + eauto using abs_ief_2.
    + destruct H2 as (_,?).
      eauto using abs_ief_1.
  Qed.

  Lemma ief_fun_end_finish:
    forall t,
    Child (t, Blocked (Node nil)) f ->
    IEFFun (put f (t, Ready)).
  Proof.
    intros.
    apply ief_fun_def.
    intros x y t1; intros.
    apply le_inv_put_ready in H0;
    apply le_inv_put_ready in H2.
    destruct H0, H2; subst; auto.
    - destruct WF4; eauto using lt_to_le.
    - assert (X: False) by eauto using abs_ief_3; inversion X.
    - assert (X: False) by eauto using abs_ief_3; inversion X.
  Qed.

  Lemma unique_ief_fun_end_finish:
    forall t,
    Child (t, Blocked (Node nil)) f ->
    UniqueIEF (put f (t, Ready)) /\ IEFFun (put f (t, Ready)).
  Proof.
    eauto using ief_fun_end_finish, unique_ief_end_finish.
  Qed.

  Lemma unique_ief_end_async:
    forall t,
    UniqueIEF (remove f t).
  Proof.
    intros.
    apply unique_child_def.
    intros x t'; intros.
    apply le_inv in H.
    destruct H.
    - apply lt_remove_1 in H.
      destruct WF3 as (Hx).
      eauto using lt_to_le.
    - subst.
      apply ief_remove_3 in H0.
      apply lt_remove_1 in H1.
      destruct WF3 as (Hx).
      eauto using lt_to_le, le_refl.
  Qed.

  Lemma ief_fun_end_async:
    forall t,
    IEFFun (remove f t).
  Proof.
    intros.
    apply ief_fun_def.
    intros.
    apply le_inv in H.
    apply le_inv in H1.
    destruct H, H1; (try apply lt_remove_1 in H); (try apply lt_remove_1 in H1).
    - destruct WF4 as (Hx).
      eauto using lt_to_le.
    - subst.
      apply ief_remove_3 in H2.
      assert (Hi: ~ In t0 x) by eauto using ief_notin_sub.
      contradiction Hi; eauto.
    - subst.
      apply ief_remove_3 in H0.
      assert (Hi: ~ In t0 y) by eauto using ief_notin_sub.
      contradiction Hi; eauto.
    - subst; trivial.
  Qed.

  Lemma unique_ief_fun_end_async:
    forall t,
    UniqueIEF (remove f t) /\ IEFFun (remove f t).
  Proof.
    eauto using unique_ief_end_async, ief_fun_end_async.
  Qed.

  Lemma unique_ief_begin_finish:
    forall t,
    UniqueIEF (put f (t, Blocked (Node ((t, Ready) :: nil)))).
  Proof.
    intros.
    apply unique_child_def.
    intros x t'; intros.
    apply le_inv in H.
    destruct H.
    - apply lt_inv_put_blocked in H.
      destruct H.
      + destruct WF3 as (Hx).
        eauto using lt_to_le.
      + apply le_inv_cons_ready in H.
        destruct H.
        * apply lt_absurd_nil in H.
          inversion H.
        * subst.
          apply lt_inv_cons_ready in H1.
          apply lt_absurd_nil in H1.
          inversion H1.
    - subst.
      assert (IEF t' f /\ t' <> t). {
        destruct (TID.eq_dec t' t). {
          subst.
          assert (Hx: ~ IEF t (put f (t, Blocked (Node ((t, Ready) :: nil))))). {
            eauto using ief_put_absurd_1,
              wf_tasks_begin_finish, 
              ief_ready, child_eq.
          }
          contradiction Hx; trivial.
        }
        eauto using ief_put_3.
      }
      destruct H.
      apply lt_inv_put_blocked in H1.
      destruct H1.
      + destruct WF3.
        assert (f <= f) by eauto using le_refl.
        apply (H3 f t' y); eauto using lt_remove_1.
      + apply le_inv_node_ready in H1; subst.
        unfold not.
        intros.
        apply in_inv_cons in H1.
        destruct H1 as [?|[(?,(?,?))|?]].
        * contradiction.
        * inversion H1.
        * apply in_absurd_nil in H1.
          assumption.
  Qed.


Ltac resolve_log :=
  subst; auto;
  repeat (match goal with
           | [ H : False |- _ ] => destruct H (* resolve absurd cases *)
           | [ H : _ /\ _ |- _ ] => destruct H (* break conjuctions *)
           | [ H : _ \/ _ |- _ ] => destruct H (* break disjunctions *)
           | [ H : ?x <> ?x |- _ ] => contradiction H; trivial
         end; subst; auto).


  Ltac break_ief_put_blocked :=
  try match goal with
  | [ H: IEF _ (put f (_, Blocked _)) |- _ ] => (apply ief_put_inv_blocked in H; auto); resolve_log
  end.

  Ltac abs_registered_eq :=
  match goal with
  | [ H: ~ Registered ?t (Node ((?t, _) :: _)) |- _ ] =>
    contradiction H;
    apply registered_eq
  end.

  Ltac simpl_le_cons_ready :=
  match goal with
  | [ H: _ <= Node ((_, Ready) :: nil) |- _ ] =>
    apply le_inv_node_ready in H; subst
  end.

  Ltac simpl_ief_cons_ready :=
   match goal with
   | [ H: IEF ?t1 (Node ((?t2, _) :: nil)) |- _ ] =>
     apply ief_inv_cons_nil in H; subst
   end.
    

  Lemma ief_fun_begin_finish:
    forall t,
    Child (t, Ready) f ->
    IEFFun (put f (t, Blocked (Node ((t, Ready) :: nil)))).
  Proof.
    intros.
    apply ief_fun_def.
    intros.
    assert (WFTasks (put f (t, Blocked (Node ((t, Ready) :: nil))))). {
      eauto using wf_tasks_begin_finish, wf_tasks_put_blocked.
    }
    apply le_inv_put_blocked in H0.
    apply le_inv_put_blocked in H2.
    destruct H0, H2; resolve_log; break_ief_put_blocked;
      try abs_registered_eq; try simpl_le_cons_ready; try simpl_ief_cons_ready; resolve_log.
    - destruct H1; assert (X: False) by eauto using abs_ief_1; inversion X.
    - destruct H2; assert (X: False) by eauto using abs_ief_1; inversion X.
    - destruct WF4; eauto using lt_to_le.
    - assert (X: False) by eauto using abs_ief_1, ief_ready; inversion X.
    - assert (X: False) by eauto using abs_ief_1, ief_ready; inversion X.
    - simpl_le_cons_ready.
      trivial.
  Qed.

  Lemma unique_ief_fun_begin_finish:
    forall t,
    Child (t, Ready) f ->
    UniqueIEF (put f (t, Blocked (Node ((t, Ready) :: nil)))) /\
    IEFFun (put f (t, Blocked (Node ((t, Ready) :: nil)))).
  Proof.
    eauto using unique_ief_begin_finish, ief_fun_begin_finish.
  Qed.

  Variable unique_ief_le:
    forall x y, UniqueIEF y -> x <= y -> UniqueIEF x.

  Variable ief_fun_le:
    forall x y, IEFFun y -> x <= y -> IEFFun x.

  Lemma sr_unique_ief:
    forall t o f',
    Reduce f t o f' ->
    UniqueIEF f' /\ IEFFun f'.
  Proof.
    intros.
    induction H;
    eauto using
      unique_ief_fun_begin_async, unique_ief_fun_end_async,
      unique_ief_fun_begin_finish, unique_ief_fun_end_finish.
    assert (f' <= f) by eauto using lt_child, lt_to_le.
    assert (WFTasks f')  by eauto using wf_tasks_le.
    assert (UniqueIEF f')  by eauto using unique_ief_le.
    assert (IEFFun f')  by eauto using unique_ief_le.
    assert (X: UniqueIEF f'' /\ IEFFun f'') by eauto.
    destruct X as (X, Y).
    split.
    - 
  Qed.

End Props.