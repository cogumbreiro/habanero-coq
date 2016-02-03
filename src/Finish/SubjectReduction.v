Require Import Coq.Lists.SetoidList.

Require Import HJ.Vars.

Require Import HJ.Finish.Syntax.
Require Import HJ.Finish.Semantics.
Require Import HJ.Finish.IEF.
Require Import HJ.Finish.Rel.

Import Rel.Notations.

Section Sem.

  Lemma lt_remove_1:
    forall x y t,
    x < remove y t ->
    x < y.
  Proof.
    intros.
    unfold remove in *.
    destruct y.
    induction l; auto.
    destruct a as (t', a).
    simpl in *.
    destruct (TID.eq_dec t t').
    - auto using lt_cons.
    - apply lt_inv_cons in H.
      destruct H as [?|[(f',(?,?))|?]]; subst.
      + auto using lt_eq.
      + assert (f' < Node ((t', Blocked f') :: l))
        by auto using lt_eq.
        eauto using lt_trans.
      + auto using lt_cons.
  Qed.

  Lemma lt_put_1:
    forall x y t,
    x < put y (t, Ready) ->
    x < y.
  Proof.
    intros.
    unfold put in *.
    simpl in *.
    apply lt_inv_cons_ready in H.
    rewrite get_tasks_rw in *.
    eauto using lt_remove_1.
  Qed.

  Lemma le_inv_put_ready:
    forall x y t,
    x <= put y (t, Ready) ->
    x < y \/ x = put y (t, Ready).
  Proof.
    intros.
    unfold put in *.
    apply le_inv_cons_ready in H.
    destruct H.
    - simpl in *.
      left.
      rewrite get_tasks_rw in *.
      eauto using lt_remove_1.
    - simpl in *.
      subst.
      intuition.
  Qed.

  Lemma lt_inv_put_blocked:
    forall x y z t,
    x < put y (t, Blocked z) ->
    x < y \/ x <= z.
  Proof.
    intros.
    unfold put in *.
    apply lt_inv_cons in H.
    destruct H as [?|[(f',(?,?))|?]].
    + inversion H; subst.
      simpl in *; intuition.
    + inversion H; subst.
      assert (x <= f') by auto using lt_to_le.
      intuition.
    + simpl in *.
      rewrite get_tasks_rw in *.
      eauto using lt_remove_1.
  Qed.

  Lemma le_inv_put_blocked:
    forall x y z t,
    x <= put y (t, Blocked z) ->
    x = put y (t, Blocked z) \/ x < y \/ x <= z.
  Proof.
    intros.
    unfold put in *.
    apply le_inv in H.
    destruct H.
    - eauto using lt_inv_put_blocked.
    - intuition.
  Qed.

  Lemma ief_inv_cons_nil:
    forall t t' a,
    IEF t (Node ((t', a) :: nil)) ->
    t' = t.
  Proof.
    intros.
    inversion H.
    - apply child_inv_cons_nil in H0.
      inversion H0; trivial.
    - apply child_inv_cons_nil in H0.
      inversion H0; trivial.
  Qed.

  Lemma ief_put_3:
    forall t f t' a,
    IEF t (put f (t', a)) ->
    t <> t' ->
    IEF t f.
  Proof.
    intros.
    inversion H.
    - apply put_3 in H1; auto.
      eauto using ief_ready.
    - apply put_3 in H1; auto.
      eauto using ief_blocked.
  Qed.

  Lemma ief_remove_3:
    forall t f t',
    IEF t (remove f t') ->
    IEF t f.
  Proof.
    intros.
    inversion H.
    - apply remove_3 in H0.
      auto using ief_ready.
    - apply remove_3 in H0; auto.
      eauto using ief_blocked.
  Qed.

  Require Import HJ.Finish.Typesystem.

  Lemma ief_inv_registered:
    forall t f,
    IEF t f ->
    Registered t f.
  Proof.
    intros.
    inversion H;
    eauto using registered_def.
  Qed.

  Lemma ief_put_absurd_1:
   forall t x y,
     WFTasks (put y (t, Blocked x)) ->
     IEF t x ->
     ~ IEF t (put y (t, Blocked x)).
  Proof.
    intros.
    assert (Hc: Child (t, Blocked x) (put y (t, Blocked x))). {
      eauto using child_eq.
    }
    assert (Hlt: x < put y (t, Blocked x)). {
      eauto using lt_child.
    }
    unfold not; intros.
    inversion H1.
    - assert (Ha : Ready = Blocked x) by eauto using wf_tasks_child_fun.
      inversion Ha.
    - assert (Ha : Blocked x0 = Blocked x) by eauto using wf_tasks_child_fun.
      inversion Ha; subst; clear Ha.
      contradiction H3.
      eauto using ief_inv_registered.
  Qed.

(*
  Lemma ief_put_neq:
    forall 
    IEF t1 
    IEF t1 (put x (t2, Blocked y))
*)
End Sem.

Section Props.

  Require Import HJ.Finish.Typesystem.

(*
  Variable le_strengthen_2:
    forall x y t,
    x <= (remove y t) ->
    Rel.Le x y.

  Variable le_inv_put:
    forall x y z t,
    Rel.Le x (put y (t, Blocked z)) ->
    Rel.Le x y \/ Rel.Le x z.

  Variable le_inv_singleton:
    forall x t l,
    Rel.Le x (Node ((t, Ready) :: l)) ->
    x = (Node ((t, Ready) :: l)) \/ Rel.Le x (Node l).
*)

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
    

  Variable sr_wf_task:
    forall x t o y,
    WFTasks x ->
    Reduce x t o y ->
    WFTasks y.
    

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

  Lemma unique_ief_put_ready_1:
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

  Lemma ief_fun_put_ready_1:
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

  Lemma unique_ief_fun_put_ready_1:
    forall t,
    ~ In t f ->
    IEFFun (put f (t, Ready)) /\ UniqueIEF (put f (t, Ready)).
  Proof.
    intros.
    split; auto using ief_fun_put_ready_1, unique_ief_put_ready_1.
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

  Lemma unique_ief_begin_finish:
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
    assert (Hi: ~ In t0 y) by (eapply ief_notin_sub; eauto).
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

  Lemma ief_fun_begin_finish:
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

  Lemma unique_ief_remove:
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

  Lemma ief_fun_remove:
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

  Variable wf_task_put_blocked:
    forall x y t,
    WFTasks x ->
    WFTasks y ->
    WFTasks (put x (t, Blocked y)).

  Lemma wf_tasks_begin_finish:
    forall t,
    WFTasks (Node ((t, Ready) :: nil)).
  Proof.
    intros.
    apply wf_tasks_def.
    intros.
    apply le_inv_cons_ready in H.
    destruct H.
    * apply lt_absurd_nil in H.
      inversion H.
    * subst.
      apply is_map_def.
      apply NoDupA_cons. {
        unfold not.
        intros.
        inversion H.
      }
      apply NoDupA_nil.
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

  Lemma unique_ief_put_child:
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
              wf_tasks_begin_finish, wf_task_put_blocked,
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
    

  Lemma ief_fun_put_child:
    forall t,
    Child (t, Ready) f ->
    IEFFun (put f (t, Blocked (Node ((t, Ready) :: nil)))).
  Proof.
    intros.
    apply ief_fun_def.
    intros.
    assert (WFTasks (put f (t, Blocked (Node ((t, Ready) :: nil))))). {
      eauto using wf_tasks_begin_finish, wf_task_put_blocked.
    }
    apply le_inv_put_blocked in H0.
    apply le_inv_put_blocked in H2.
    destruct H0, H2; resolve_log; break_ief_put_blocked;
      try abs_registered_eq; try simpl_le_cons_ready; try simpl_ief_cons_ready.
    - eapply ief_notin_sub in H2; eauto.
      inversion H2.
    - contradiction H1; trivial.
    - eapply abs_ief_both in H3; eauto.
      inversion H3.
    - contradiction H2.
      trivial.
    - apply lt_remove_1 in H0.
      apply lt_remove_1 in H2.
      destruct WF4; eauto using lt_to_le.
    - assert (IEF t0 f) by eauto using ief_ready.
      eapply abs_ief_both in H3; eauto.
      inversion H3.
    - assert (Hi: IEF t0 f) by eauto using ief_ready.
      eapply abs_ief_both in Hi; eauto.
      inversion Hi.
    - simpl_le_cons_ready.
      trivial.
  Qed.

  Variable unique_ief_le:
    forall x y, UniqueIEF y -> x <= y -> UniqueIEF x.

  Lemma sr_unique_ief:
    forall t o f',
    Reduce f t o f' ->
    UniqueIEF f'.
  Proof.
    intros.
    induction H; eauto using unique_ief_put_ready_1, unique_ief_begin_finish, unique_ief_remove, unique_ief_put_child.
    assert (f' <= f) by eauto using lt_child, lt_to_le.
    assert (WFTasks f')  by eauto using wf_tasks_le.
    assert (UniqueIEF f')  by eauto using unique_ief_le.
    assert (UniqueIEF f'') by eauto.
  Qed.

(*
  Let sr_ief_sub_red:
    forall x t t' o y,
    Disjoint f o ->
    Child (t', Blocked x) f ->
    Reduce x t o y ->
    UniqueIEF y ->
    WFTasks (put f (t', Blocked y)) ->
    UniqueIEF (put f (t', Blocked y)).
  Proof.
    intros.
    apply unique_child_def; intros f1 b f2; intros.
    apply le_inv_put_blocked in H4.
    destruct H4.
    - subst.
      apply ief_put in H5; eauto.
      apply lt_inv_put_blocked in H6.
      destruct H5, H6.
      + subst.
        
        
        destruct H6.
        * 
          assert 
          Check (Hx).
        assert (y <= put f (t', Blocked y)) by eauto using put_le.
        Check (Hx y).
      apply ief_put_ready in H4.
    destruct H2 as (Hx).
  Qed.
    
    

  Let sr_ief_fun_begin_async:
    forall t t' f',
    Reduce f t (BEGIN_ASYNC t') f' ->
    UniqueIEF f'.
  Proof.
    intros.
    apply unique_child_def.
    intros ? t1; intros.
    inversion H; subst.
    - apply le_inv_put_ready in H0.
      destruct H0.
      + assert (y < f) by eauto using lt_trans.
        destruct WF3 as (Hx).
        assert (Hy: x <= f) by eauto using lt_to_le.
        eauto.
      + subst.
        apply lt_put_1 in H2.
        destruct WF3 as (Hx).
        apply ief_put_ready in H1; eauto.
        destruct H1.
        * subst.
          assert (y <= f) by eauto using lt_to_le.
          eauto using notin_le.
        * eauto using le_refl.
    - subst.
      apply le_inv_put_blocked in H0.
      destruct H0 as [?|[?|?]].
      + subst.
        destruct WF3 as (Hx).
        Check (Hx (put f (t'0, Blocked f'')) t1).

        apply lt_inv_put_blocked in H2.
        destruct H2.
        * destruct WF3 as (Hx).
          Check (Hx (put f (t'0, Blocked f''))).
          eauto using lt_to_le.
      + subst.
        apply lt_inv in H2.
        destruct WF3 as (Hx).
  Qed.

  Variable WF1: IEFFun f.

  Let sr_ief_fun_begin_async:
    forall t t' f',
    Reduce f t (BEGIN_ASYNC t') f' ->
    IEFFun f'.
  Proof.
    intros.
    inversion H.
    - subst.
      apply ief_fun_def.
      intros x y t''; intros.
      apply le_inv_put_ready in H0.
      apply le_inv_put_ready in H4.
      destruct H0, H4.
      + assert (x <= f) by auto using lt_to_le.
        assert (y <= f) by auto using lt_to_le.
        destruct WF1; eauto.
      + subst.
        destruct (TID.eq_dec t'' t'). {
          subst.
          contradiction H2.
          assert (In t' x) by eauto using ief_in.
          eauto using in_lt.
        }
        apply ief_put_3 in H5; auto.
        assert (X: t'' = t' \/ IEF t'' f). {
          assert (WFTasks (put f (t', Ready))) by eauto using sr_wf_task.
          apply ief_put_ready; auto.
        }
        destruct X.
        * subst.
          assert (x <= f) by auto using lt_to_le; clear H1.
        eauto.
        
  Qed.

  Lemma sr_ief_fun:
    forall f t o f',
    IEFFun f ->
    Reduce f t o f' ->
    IEFFun f'.
  Proof.
    intros.
    inversion H0; subst.
    - destruct H.
      apply le_inv_cons_ready in H1.
      apply le_inv_cons_ready in H3.
      destruct H1, H3.
      + 
    apply 
      eauto.
    - destruct H; eauto.
    - destruct (TID.eq_dec t t1). {
        subst.
        apply le_inv_put in H1.
        apply le_inv_put in H3.
        destruct H1, H3.
        - destruct H; eauto.
        - 
      }
      destruct H.
      
  Qed.
