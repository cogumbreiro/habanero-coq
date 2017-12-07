Set Implicit Arguments.

Require Import Coq.Lists.SetoidList.

Require Import HJ.Vars.
Require Import HJ.Finish.Lang.

Import FinishNotations.

Open Scope finish_scope.

Inductive Nonempty : finish -> Prop :=
  nonempty_def:
    forall t f,
    In t f ->
    Nonempty f.

Lemma nonempty_leaf_absurd:
  Nonempty (Node nil) -> False.
Proof.
  intros.
  inversion H; subst; clear H.
  apply in_absurd_nil in H0; trivial.
Qed.

Lemma nonempty_cons:
  forall p l,
  Nonempty (Node (p :: l)).
Proof.
  intros.
  destruct p as (t, f).
  apply nonempty_def with (t:=t).
  eapply in_eq.
Qed.

Inductive Enabled: task -> Prop :=
  | enabled_ready:
    Enabled Ready
  | enabled_leaf:
    Enabled (Blocked (Node nil)).

Inductive Flat (f:finish) : Prop :=
  flat_def:
    (forall t a, Child (t, a) f -> Enabled a) ->
    Nonempty f ->
    Flat f.

Lemma flat_cons:
  forall t l,
  Flat (Node l) ->
  forall a,
  Enabled a ->
  Flat (Node ((t, a) :: l)).
Proof.
  intros.
  inversion H.
  apply flat_def.
  intros.
  destruct (TID.eq_dec t0 t).
  - subst.
    apply child_inv_cons in H3.
    destruct H3 as [?|?].
    + inversion H3; subst; assumption.
    + eauto using H1.
  - assert ((t0, a0) <> (t, a)). {
      intuition.
      inversion H4; subst; contradiction n; trivial.
    }
    eauto using child_neq.
  - auto using nonempty_cons.
Qed.

Lemma flat_eq:
  forall t a,
  Enabled a ->
  Flat [(t,a)].
Proof.
  intros.
  apply flat_def.
  - intros.
    apply child_inv_cons_nil in H0; inversion H0; subst.
    assumption.
  - auto using nonempty_cons.
Qed.

Lemma nonempty_dec:
  forall f,
  { Nonempty f } + {f = Node nil }.
Proof.
  intros.
  destruct f.
  destruct l.
  - right; trivial.
  - left.
    apply nonempty_cons.
Qed.

Lemma find_flat_alt:
  forall (f:finish),
  Nonempty f ->
  Any Flat f.
Proof.
  intros.
  induction f using finish_ind_strong.
  - apply nonempty_leaf_absurd in H.
    inversion H.
  - clear H.
    destruct (nonempty_dec (Node l)).
    + apply IHf in n; clear IHf.
      auto using any_cons_rhs, flat_cons, enabled_ready.
    + inversion e; subst; clear e.
      eauto using any_cons_rhs, any_def, le_refl, flat_eq, flat_cons, enabled_ready.
  - destruct (nonempty_dec f).
    { auto using any_cons. }
    subst.
    destruct (nonempty_dec (Node l)).
    { apply IHf0 in n.
      inversion n.
      apply le_inv in H0.
      destruct H0.
      - eauto using any_cons_lt.
      - subst.
        eauto using any_eq, flat_cons, enabled_leaf.
     }
     inversion e; subst; clear e.
     eauto using any_eq, flat_eq, enabled_leaf.
Qed.

(**
 If [f] is nonempty, then we can find a smaller-or-equal finish [f'] 
 such that [f'] is flat. *)
Theorem find_flat:
  forall (f:finish),
  Nonempty f ->
  exists f',
  Flat f' /\ f' <= f.
Proof.
  intros.
  assert (F: Any Flat f) by auto using find_flat_alt.
  inversion F.
  eauto.
Qed.


Require Import HJ.Finish.Semantics.
Require Import HJ.Finish.Typesystem.
Require Import HJ.Finish.LangExtra.

Lemma sub_notin:
  forall x y t,
  Sub x y ->
  ~ In t y ->
  ~ In t x.
Proof.
  intros.
  rewrite notin_spec in *.
  destruct H.
  destruct H.
  destruct y.
  assert (RW : get_tasks (Node l) = l) by (simpl; auto).
  rewrite RW in *; clear RW.
  induction l.
  { inversion H. }
  apply notin_inv in H0.
  destruct H0 as (?, (?, ?)).
  inversion H.
  - subst.
    simpl in H0, H1.
    assumption.
  - auto.
Qed.

Lemma le_notin:
  forall f f',
  f' <= f ->
  forall t,
  ~ In t f ->
  ~ In t f'.
Proof.
  intros f f' Hle.
  destruct Hle as (Hle).
  induction Hle; intros; eauto using sub_notin.
Qed.

Lemma le_disjoint:
  forall o f f',
  Disjoint f o ->
  f' <= f ->
  Disjoint f' o.
Proof.
  intros.
  inversion H; subst;
  eauto using disjoint_ok, le_notin, disjoint_skip.
Qed.


(**
  If finish [f1] reduces and [f1] is is smaller-or-equal than a finish [f3],
  then [f3] also reduces.
*)  

Theorem reduce_le:
  forall f1 f3,
  f1 <= f3 ->
  forall f2 t o,
  Reduce f1 t o f2 ->
  Disjoint f3 o ->
  exists f4, Reduce f3 t o f4.
Proof.
  intros f1 f2 Hf.
  inversion Hf as (Hf').
  induction Hf'; intros.
  - inversion H as (t', ?).
    exists (y |+ t' <| f2).
    eauto using reduce_nested.
  - eauto.
  - apply IHHf'1 in H.
    + destruct H as (y', R1).
      eauto using Relation_Operators.rt_trans, le_def.
    + eauto using Relation_Operators.rt_trans, le_def.
    + apply le_disjoint with (z); auto.
      eauto using Relation_Operators.rt_trans, le_def.
Qed.

Lemma flat_le:
  forall f f',
  Flat f ->
  f' <= f ->
  (f' = f \/ f' = []).
Proof.
  intros.
  destruct H0.
  induction H0.
  - inversion H0.
    inversion H.
    apply H2 in H1.
    inversion H1.
    intuition.
  - intuition.
  - intuition.
    + subst.
      auto.
    + subst.
      assert (Hle : x <= []). {
        eauto using Relation_Operators.rt_trans, le_def.
      }
      apply le_inv_nil in  Hle.
      intuition.
Qed.

Lemma check_leaf_absurd_nil:
  forall t o,
  ~ Leaf.Valid [] t o.
Proof.
  intros.
  intuition.
  inversion H; try (apply child_absurd_nil in H0; inversion H0).
  apply child_absurd_nil in H1; inversion H1.
Qed.

Lemma flat_le_rw:
  forall f f' t o,
  Flat f ->
  Leaf.Valid f' t o ->
  f' <= f ->
  f' = f.
Proof.
  intros.
  apply flat_le in H1; auto.
  destruct H1; subst; auto.
  apply check_leaf_absurd_nil in H0.
  inversion H0.
Qed.

(**
  Any flat finish reduces. 
  *)
Theorem flat_reduces:
  forall f,
  Flat f ->
  forall t o,
  Op.Valid f t o ->
  exists f', Reduce f t o f'.
Proof.
  intros.
  destruct H0.
  assert (RW : f' = f) by eauto using flat_le_rw.
  subst; clear H1.
  inversion H0; subst.
  - eauto using begin_async.
  - eauto using end_async.
  - eauto using begin_finish.
  - exists (f |+ !t).
    apply end_finish.
    inversion H.
    assert (Hx := H3).
    apply H4 in Hx.
    inversion Hx.
    subst.
    assumption.
Qed.


Lemma in_to_registered:
  forall t f,
  Flat f ->
  In t f ->
  Registered t f.
Proof.
  intros ? ? Hf Hin.
  inversion Hf as (He, Hn).
  destruct Hin.
  apply flat_le in H0; auto.
  destruct H0.
  - subst.
    eauto using registered_def.
  - subst.
    inversion H.
    inversion H0.
    inversion H1.
Qed.

(*
(**
  Any flat finish reduces. 
  *)
Corollary flat_reduces_simpl:
  forall f,
  Flat f ->
  exists f' t o, Reduce f t o f'.
Proof.
  intros.
  inversion H.
  inversion H1; subst; clear H1.
  apply in_to_registered in H2; auto.
  inversion H2.
  exists f.
  exists t.
  
Qed.
*)
(*
Lemma check_translate:
  forall f t o f',
  Check f t o ->
  f' <= f ->
  In t f' ->
  Check f t o.
Proof.
  intros.
  inversion H as (f'',?).
  apply check_def with (f'); auto.
  inversion H2; subst.
  - apply check_begin_async.
Qed.
*)