Require Import Coq.Lists.SetoidList.

Require Import HJ.Vars.
Require Import HJ.AsyncFinish.Lang.

Import FinishNotations.

Open Local Scope finish_scope.

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

(*
Lemma progress_easy:
  forall (f:finish),
  Nonempty f ->
  exists t,
  In t f /\
  CanReduce (Semantics.Reduce f) t Semantics.END_ASYNC.
Proof.
  intros.
  induction f using finish_ind_weak.
  - apply nonempty_leaf_absurd in H.
    inversion H.
  - destruct f as [l'].
    destruct l' as [l'|].
    + exists t.
      split; auto using in_eq.
      apply can_reduce_def with (s':= remove t (Node ((t, leaf) :: l))).
      apply Semantics.end_async.
      apply leaf_def.
      apply child_eq.
    + assert (Hn : Nonempty (Node (p :: l'))). {
        eauto using nonempty_cons.
      }
      apply IHf in Hn; clear IHf.
      destruct Hn as (t', (Hin, Hc)).
      exists t'.
      split.
      { (* left *)
        eauto using in_cons.
      }
      (* right *)
      inversion Hc; clear Hc; subst.
      remember (Node ((t, Node (p :: l')) :: l)) as s.
      apply can_reduce_def with (put t s' s).
      apply Semantics.reduce_nested with (f':=(Node (p :: l'))).
      * apply Semantics.disjoint_skip.
        simpl.
        trivial.
      * subst; apply child_eq.
      * assumption.
Qed.
*)

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

Require Import HJ.AsyncFinish.Semantics.
Require Import HJ.AsyncFinish.Typesystem.
Require Import HJ.AsyncFinish.LangExtra.

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
    + clear IHHf'1.
      destruct H as (y', R1).
      apply IHHf'2 with (y'); auto.
      intuition.
    + intuition.
    + apply le_disjoint with (z); auto.
      intuition.
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
      assert (Hle : x <= []) by intuition.
      apply le_inv_nil in  Hle.
      intuition.
Qed.

Lemma check_leaf_absurd_nil:
  forall t o,
  ~ CheckLeaf [] t o.
Proof.
  intros.
  intuition.
  inversion H; try (apply child_absurd_nil in H0; inversion H0).
  apply child_absurd_nil in H1; inversion H1.
Qed.

Lemma flat_le_rw:
  forall f f' t o,
  Flat f ->
  CheckLeaf f' t o ->
  f' <= f ->
  f' = f.
Proof.
  intros.
  apply flat_le in H1; auto.
  destruct H1; subst; auto.
  apply check_leaf_absurd_nil in H0.
  inversion H0.
Qed.

Lemma flat_reduces:
  forall f t o,
  Flat f ->
  Check f t o ->
  exists f', Reduce f t o f'.
Proof.
  intros.
  destruct H0.
  assert (RW : f' = f) by eauto using flat_le_rw.
  subst; clear H1.
  inversion H0; subst.
  - exists (f |+ !t').
    auto using begin_async.
  - exists (f |- t).
    auto using end_async.
  - exists (f |+ t <| [!t]).
    auto using begin_finish.
  - exists (f |+ !t).
    apply end_finish.
    inversion H.
    assert (Hx := H3).
    apply H4 in Hx.
    inversion Hx.
    subst.
    assumption.
Qed.

Require HJ.AsyncFinish.LangExtra.
Module E := LangExtra.

Lemma reduce_cons:
  forall l t o f p,
  Disjoint (Node (p::l)) o ->
  Reduce (Node l) t o f ->
  exists f', Reduce (Node (p :: l)) t o f'.
Proof.
  intros.
  inversion H0; subst.
  - exists (Node (p :: l) |+ !t').
    apply begin_async.
    + auto using child_cons.
    + apply disjoint_inv_begin_async in H.
      rewrite E.notin_spec in *.
      assumption.
  - exists (Node (p::l) |- t).
    auto using end_async, child_cons.
  - exists (Node (p::l) |+ t <| [!t]).
    auto using begin_finish, child_cons.
  - exists (Node (p::l) |+ !t).
    auto using end_finish, child_cons.
  - exists (put (Node (p::l)) (t', Blocked f'')).
    eauto using reduce_nested, child_cons.
Qed.
(*
Lemma flat_inv_cons:
  forall p p' l,
  Flat (Node (p :: p' :: l)) ->
  Flat (Node (p' :: l)).
Admitted.
*)
Lemma flat_inv_blocked:
  forall t f f',
  Flat f' ->
  Child (t <| f) f' ->
  f = [].
Proof.
  intros.
  inversion H.
  assert (Hx: Enabled (Blocked f)). {
    compute in *;
    eauto.
  }
  inversion Hx.
  trivial.
Qed.
(*
Lemma flat_reduce:
  forall f,
  Nonempty f ->
  Flat f ->
  (exists t, Child (t <| []) f) \/ (forall t, Registered t f -> Child (!t) f).
Proof.
  intros.
  induction f using finish_ind_strong.
  - inversion H.
    apply in_absurd_nil in H1.
    inversion H1.
  - destruct l.
    + right.
      intros.
      inversion H1.
      assert (Hx := H2).
      apply child_inv_cons_nil in H2.
      inversion H2; subst.
      assumption.
    + assert (Hx : Flat (Node (p :: l))) by eauto using flat_inv_cons.
      assert (Hy : Nonempty (Node (p :: l)) ) by auto using nonempty_cons.
      apply IHf in Hy; auto.
      clear IHf Hx.
      destruct Hy  as  [(t',?)|?].
      * left; exists t'.
        auto using child_cons.
      * right.
        intros.
        apply registered_inv_cons in H2.
        destruct H2.
        {
          subst.
          auto using child_eq.
        }
        auto using child_cons.
  - clear IHf.
    assert (f = []). {
      remember (Node (_::_)) as f'.
      assert (Child (t <| f) f'). {
        subst.
        auto using child_eq.
      }
      eauto using flat_inv_blocked.
    }
    subst.
    left.
    exists t.
    auto using child_eq.
Qed.
*)

(*
Let child_impl_nleaf:
  forall t f,
  Valid f ->
  Child (t <| []) f ->
  ~ Child (!t) f.
Proof.
  intros.
  unfold not; intros Hx.  
  apply child_fun with (a:=Ready) in H0; auto.
  inversion H0.
Qed.
*)
(*
Lemma blocked_nil_impl_end_finish:
  forall f t o,
  Valid  f ->
  Child (t <| []) f ->
  Check f t o ->
  o = END_FINISH.
Proof.
  intros.
  inversion H1.
  inversion H2; (try (apply child_impl_nleaf in H4; auto; tauto)).
  trivial.
Qed.
*)
(*
Lemma blocked_nil_impl_redex:
  forall f t,
  Valid  f ->
  Child (t <| []) f ->
  exists f', Reduce f t END_FINISH f'.
Proof.
  intros.
  exists (f |+ !t).
  auto using end_finish.
Qed.
*)
(* XXXXXXXXXXXXXXXXXXXXXXXXXXX
Lemma reduce_any:
  forall (f f':finish) (t:tid) (o:op),
  Disjoint f o ->
  Any (fun (f':finish) => exists f'', Reduce f' t o f'') f ->
  exists f', Reduce f t o f'.
Proof.
  intros.
  remember (fun f'0 : finish => exists f'' : finish, Reduce f'0 t o f'') as F.
  induction f using finish_ind_strong.
  - apply any_inv_nil in H0.
    subst; assumption.
  - apply any_inv_cons in H0.
    destruct H0 as [?|[(f'',(?,?))|?]].
    + rewrite HeqF in H0.
      assumption.
    + simpl in H0; inversion H0.
    + assert (Hx := H).
      apply disjoint_inv_cons_rhs in H.
      assert (Hy := IHf H H0); clear IHf.
      destruct Hy as (f'', Hy).
      destruct f''.
      eauto using reduce_cons.
  - apply any_inv_cons in H0.
    destruct H0 as [?|[(f'',(?,?))|?]].
    + rewrite HeqF in H0.
      assumption.
    + simpl in H0; inversion H0.
      rewrite <- H3 in *; clear H3 f''.
      clear IHf0.
      assert (Hx := H).
      apply disjoint_inv_cons_lhs in H.
      apply (IHf H) in H1.
      destruct H1 as  (f'', ?).
      exists (put (Node ((t0, Blocked f) :: l)) (t0, Blocked f'')).
      eauto using reduce_nested, child_eq.
    + assert (Hx := H).
      apply disjoint_inv_cons_rhs in H.
      assert (Hy := IHf0 H H0).
      destruct Hy as (f'', Hy).
      destruct f''.
      eauto using reduce_cons.
Qed.
*)

