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
    x = y \/ IEF x f.
  Proof.
    intros.
    inversion H.
    - destruct (TID.eq_dec y x). {
        subst.
        intuition.
      }
      eauto using put_3, ief_ready.
    - rename x0 into f'.
      destruct (TID.eq_dec x y). {
        intuition.
      }
      eauto using ief_blocked, put_3.
  Qed.

  Variable f:finish.
  Variable WF2: WFTasks f.
  Variable WF3: UniqueIEF f.

  Let unique_ief_put_ready_1:
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
      destruct H1.
      + subst.
        eauto using notin_lt, lt_put_1.
      + apply lt_put_1 in H2.
        destruct WF3 as (Hx).
        eauto using le_refl.
  Qed.

  Let unique_ief_begin_finish:
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
      destruct H1.
      + subst.
        assert (IEF t f). {
          eauto using ief_blocked, registered_absurd_nil.
        }
        destruct WF3 as (Hx).
        eauto using lt_put_1, le_refl.
      + apply lt_put_1 in H2.
        destruct WF3 as (Hx).
        eauto using le_refl.
  Qed.

  Let unique_ief_remove:
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
  Variable wf_task_put_blocked:
    forall x y t,
    WFTasks x ->
    WFTasks y ->
    WFTasks (put x (t, Blocked y)).

  Let unique_ief_put_child:
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
          assert (Hx: WFTasks (Node ((t, Ready) :: nil))). {
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
          }
          inversion H0.
          - apply wf_tasks_child_absurd_neq in H.
            + inversion H.
            + apply wf_task_put_blocked; auto.
          - assert (x = Node ((t,Ready)::nil)). {
              assert (Child (t, Blocked (Node ((t,Ready)::nil))) (put f (t, Blocked (Node ((t, Ready) :: nil)))))
              by eauto using put_1.
              apply wf_tasks_child_fun with (a:=Blocked x) in H3; auto.
              inversion H3.
              trivial.
            }
            subst.
            contradiction H2.
            apply registered_eq.
        }
        eauto using ief_put_3.
      }
      destruct H.
      apply lt_inv_put_blocked in H1.
      destruct H1.
      + destruct WF3.
        assert (f <= f) by eauto using le_refl.
        apply (H3 f t' y); auto.
      + apply le_inv_cons_ready in H1.
        destruct H1.
        * apply lt_absurd_nil in H1.
          inversion H1.
        * subst.
          unfold not.
          intros.
          apply in_inv_cons in H1.
          destruct H1 as [?|[(?,(?,?))|?]]. {
            contradiction.
          }
          {
            inversion H1.
          }
          apply in_absurd_nil in H1.
          assumption.
  Qed.

  Let sr_ief_fun_begin_async:
    forall t o f',
    Reduce f t o f' ->
    UniqueIEF f'.
  Proof.
    intros.
    induction H; eauto.
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
