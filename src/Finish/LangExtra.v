Require Import Coq.Lists.List.

Require Import HJ.Vars.
Require Import HJ.Finish.Lang.

Fixpoint NotIn (t:tid) (f:finish) : Prop :=
  match f with
   | Node l =>
     (fix aux (l:list l_task) : Prop :=
       match l with
       | (t',a) :: l =>
         t <> t' /\ aux l /\
         (match a with
         | Ready => True
         | Blocked f => NotIn t f
         end)
       | nil => True
       end
     ) l
  end.

Lemma notin_cons:
  forall t l p,
  t <> fst p ->
  match snd p with
  | Ready => True
  | Blocked f => NotIn t f
  end ->
  NotIn t (Node l) ->
  NotIn t (Node (p :: l)).
Proof.
  intros.
  simpl.
  destruct p as (t', a).
  split.
  { simpl; auto. }
  split.
  - assumption.
  - assumption.
Qed.

Lemma notin_inv:
  forall t l p,
  NotIn t (Node (p :: l)) ->
  t <> fst p /\
  match snd p with
  | Ready => True
  | Blocked f => NotIn t f
  end /\
  NotIn t (Node l).
Proof.
  intros.
  destruct p.
  simpl in H.
  intuition.
Qed.

Lemma notin_cons_ready:
  forall t t' l,
  t <> t' ->
  NotIn t (Node l) ->
  NotIn t (Node ((t',Ready) :: l)).
Proof.
  intros.
  apply notin_cons; (simpl in *; auto with *).
Qed.

Lemma notin_cons_blocked:
  forall t t' f l,
  t <> t' ->
  NotIn t f ->
  NotIn t (Node l) ->
  NotIn t (Node ((t', Blocked f) :: l)).
Proof.
  intros.
  apply notin_cons; (simpl in *; auto with *).
Qed.

Lemma notin_spec_1:
  forall f t,
  NotIn t f ->
  ~ In t f.
Proof.
  intros.
  induction f using finish_ind_strong.
  - eauto using in_absurd_nil.
  - simpl in H.
    destruct H as (?, (?, _)).
    intuition.
    apply in_inv_cons in H1.
    destruct H1 as [?|[(f,(?,?))|?]].
    + contradiction H.
    + inversion H1.
    + contradiction H2.
  - simpl in H.
    destruct H as (?, (?, ?)).
    intuition.
    apply in_inv_cons in H2.
    destruct H2 as [?|[(f',(?,?))|?]].
    + contradiction H.
    + inversion H2; subst; rename f' into  f; clear H2.
      contradiction H5.
    + contradiction H2.
Qed.

Lemma notin_spec_2:
  forall f t,
  ~ In t f ->
  NotIn t f.
Proof.
  intros.
  induction f using finish_ind_strong.
  - simpl. trivial.
  - assert (Hneq : t <> t0). {
      destruct (TID.eq_dec t t0).
      subst.
      contradiction H.
      apply in_eq.
      assumption.
    }
    apply notin_cons_ready;  auto.
    apply IHf.
    intuition.
    contradiction H.
    auto using in_cons.
  - assert (Hneq : t <> t0). {
      destruct (TID.eq_dec t t0).
      subst.
      contradiction H.
      apply in_eq.
      assumption.
    }
    apply notin_cons_blocked; auto.
    + apply IHf.
      intuition.
      contradiction H.
      eauto using in_trans, lt_eq.
    + apply IHf0.
      intuition.
      contradiction H.
      auto using in_cons.
Qed.

Theorem notin_spec:
  forall t f,
  ~ In t f <-> NotIn t f.
Proof.
  split; auto using notin_spec_1, notin_spec_2.
Qed.

Lemma disjoint_inv_cons_name:
  forall t t' a l,
  Semantics.Disjoint (Node (((t, a) :: l))) (Semantics.BEGIN_ASYNC t') ->
  t <> t'.
Proof.
  intros.
  inversion H.
  + subst.
    apply notin_spec in H1.
    simpl in H1.
    intuition.
  + simpl in H0.
    inversion H0.
Qed.


Section Sem.
  Require Import Finish.Lang.
  Import Rel.Notations.

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

End Sem.