Require Import Coq.Lists.List.

Require Import HJ.Vars.
Require Import HJ.AsyncFinish.Lang.

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
  - eauto using in_leaf_absurd.
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
    auto using in_cons_rhs.
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
      auto using in_cons.
    + apply IHf0.
      intuition.
      contradiction H.
      auto using in_cons_rhs.
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

(*
Fixpoint disjoint (t:tid) (f:finish) : bool :=
  match f with
    | Node l =>
      (fix disjoint_alt (l:list (tid*finish)) : bool :=
       match l with
       | (t',f) :: l =>
         if TID.eq_dec t t then false
         else andb (disjoint t f) (disjoint_alt l)
       | nil => true
       end
     ) l 
   | Running => true
  end.
*)
