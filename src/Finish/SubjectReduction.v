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

End Sem.

Section Props.

  Variable le_strengthen_2:
    forall x y t,
    Rel.Le x (remove y t) ->
    Rel.Le x y.

  Variable le_inv_put:
    forall x y z t,
    Rel.Le x (put y (t, Blocked z)) ->
    Rel.Le x y \/ Rel.Le x z.

  Variable le_inv_singleton:
    forall x t l,
    Rel.Le x (Node ((t, Ready) :: l)) ->
    x = (Node ((t, Ready) :: l)) \/ Rel.Le x (Node l).

  Let ief_put_ready:
    forall x y f,
    IEF x (put f (y, Ready)) ->
    x = y \/ IEF x f.
  Proof.
    intros.
    inversion H.
    - destruct (TID.eq_dec y x). {
        subst.
        intuition.
      }
      apply put_3 with (x:=y) (e':=Ready) in H0; auto using ief_ready.
    - rename x0 into f'.
      right.
      apply ief_blocked.
  Qed.

  Let sr_ief_fun_begin_async:
    forall f t t' f',
    IEFFun f ->
    Reduce f t (BEGIN_ASYNC t') f' ->
    IEFFun f'.
  Proof.
    intros.
    inversion H0.
    - subst.
      apply ief_fun_def.
      intros x y t''; intros.
      apply le_inv_put_ready in H1.
      apply le_inv_put_ready in H5.
      destruct H1, H5.
      + assert (x <= f) by auto using lt_to_le.
        assert (y <= f) by auto using lt_to_le.
        destruct H; eauto.
      + subst. 
        assert (x <= f) by auto using lt_to_le; clear H1.
        
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
