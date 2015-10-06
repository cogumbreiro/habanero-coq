Require Import Coq.Lists.SetoidList.

Require Import HJ.Vars.
Require Import HJ.AsyncFinish.Lang.

(*
Inductive ParentOf (t:tid) (t':tid) (f:finish) : Prop :=
  | parent_of_def:
    forall f' a,
    Child t' a f' ->
    Child t (Blocked f') f ->
    ParentOf t t' f.

Inductive AncestorOf (t:tid) (t':tid) (f:finish) : Prop :=
  | ancestor_of_eq:
    ParentOf t t' f ->
    AncestorOf t t' f

  | ancestor_of_cons:
    forall t'' f',
    AncestorOf t'' t' f' ->
    Child t (Blocked f') f ->
    AncestorOf t t' f.
*)
(*

Module Progress.

(**
  Any unblocked 
  The proof for this lemma is trivial, by inversion of proposition [Check].
  *)

Require Import HJ.Progress.
*)

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
  eauto using in_leaf_absurd.
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
    (forall t a, Child t a f -> Enabled a) ->
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
    apply child_inv_cons in H2.
    destruct H2 as  [(?,?)|?].
    + subst; assumption.
    + eauto using H1.
  - apply child_neq in H2; auto.
    eauto using H0.
Qed.

Lemma flat_nil:
  Flat (Node nil).
Proof.
  apply flat_def.
  intros.
  apply child_leaf_absurd in H.
  inversion H.
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

Lemma find_flat:
  forall (f:finish),
  Nonempty f ->
  Some Flat f.
Proof.
  intros.
  induction f using finish_ind_strong.
  - apply nonempty_leaf_absurd in H.
    inversion H.
  - clear H.
    destruct (nonempty_dec (Node l)).
    + apply IHf in n; clear IHf.
      auto using some_cons_rhs, flat_cons, some_ok, enabled_ready.
    + inversion e.
      subst.
      auto using some_ok, flat_cons, flat_nil, enabled_ready.
  - destruct f  as (l').
    destruct l'.
    + auto using some_cons, some_ok, flat_nil, enabled_leaf.
    + assert (Hx : Nonempty (Node (p :: l'))). {
        apply nonempty_cons.
      }
      auto using some_cons, some_ok.
Qed.

Require HJ.AsyncFinish.Lang. 
Import Semantics.

Inductive Registered (t:tid) (f:finish) : Prop :=
  | registered_def:
    forall a,
    Child t a f ->
    Registered t f.

Inductive Typesystem (f:finish) (t:tid) : op -> Prop :=
  | check_begin_async:
    forall t',
    Leaf t f ->
    ~ In t' f ->
    Typesystem f t (BEGIN_ASYNC t')
  | check_end_async:
    Leaf t f ->
    Typesystem f t END_ASYNC
  | check_begin_finish:
    Leaf t f ->
    Typesystem f t BEGIN_FINISH
  | check_end_finish:
    forall f',
    ~ Registered t f' -> (* the task executed its body *)
    Child t (Blocked f') f ->
    Typesystem f t END_FINISH.

Inductive Valid (f:finish) (t:tid) (o:op): Prop :=
  valid_def:
    Typesystem f t o ->
    Disjoint f o ->
    Valid  f t o.

Lemma flat_reduces:
  forall f t o,
  Valid f t o ->
  Flat f ->
  exists f', Reduce f t o f'.
Proof.
  intros.
  inversion H.
  inversion H1.
  - subst.
    exists (put f (t', Ready)).
    apply begin_async; auto.
  - exists (remove f t).
    apply end_async; auto.
  - subst.
    exists (put f (t, Blocked (mk_finish t))).
    auto using begin_finish.
  - subst.
    exists (put f (t, Ready)).
    apply end_finish.
    inversion H0.
    assert (Hx := H4).
    apply H5 in H4.
    inversion H4.
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
  inversion H0.
  - subst.
    exists (put (Node (p::l)) (t', Ready)).
    apply begin_async.
    + auto using leaf_cons.
    + apply disjoint_inv_begin_async in H.
      rewrite E.notin_spec in *.
      assumption.
  - subst.
    exists (remove (Node (p::l)) t).
    auto using end_async, leaf_cons.
  - subst.
    exists (put (Node (p::l)) (t, Blocked (mk_finish t))).
    auto using begin_finish, leaf_cons.
  - subst.
    exists ((put (Node (p::l)) (t, Ready))).
    auto using end_finish, child_cons.
  - subst.
    exists (put (Node (p::l)) (t', Blocked f'')).
    eauto using reduce_nested, child_cons.
Qed.

Lemma reduce_some:
  forall (f f':finish) (t:tid) (o:op),
  Disjoint f o ->
  Some (fun (f':finish) => exists f'', Reduce f' t o f'') f ->
  exists f', Reduce f t o f'.
Proof.
  intros.
  remember (fun f'0 : finish => exists f'' : finish, Reduce f'0 t o f'') as F.
  induction f using finish_ind_strong.
  - apply some_inv_nil in H0.
    subst; assumption.
  - apply some_inv_cons in H0.
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
  - apply some_inv_cons in H0.
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

Inductive EnclosingFinish (t:tid) (f:finish) : Prop :=
  | enclosing_finish_ready:
    Child t Ready f ->
    EnclosingFinish t f
  | enclosing_finish_blocked:
    forall f',
    ~ Registered t f' ->
    Child t (Blocked f') f ->
    EnclosingFinish t f.

Definition GlobalValid (t:tid) (o:op) : finish -> Prop :=
  Some (fun (f:finish) => EnclosingFinish t f -> Valid f t o).

(*
Inductive MapsTo: list tid -> finish -> finish -> Prop :=
  | maps_to_child:
    forall t f f',
    Child t f f' ->
    MapsTo (t::nil) f f'
  | maps_to_ancestor:
    forall l f fc t f',
    MapsTo l f fc ->
    Child t fc f' ->
    MapsTo (t::l) f f'.

Lemma maps_to_eq:
  forall t f l,
  MapsTo (t::nil) f (Node ((t, f) :: l)).
Proof.
  intros.
  auto using maps_to_child, child_eq.
Qed.

Lemma maps_to_leaf_absurd:
  forall l f,
  MapsTo l f leaf -> False.
Proof.
  intros.
  inversion H; (
    subst;
    eauto using child_leaf_absurd).
Qed.

Lemma maps_to_cons:
  forall t f f' l l',
  MapsTo l' f' f ->
  MapsTo (cons t l') f' (Node ((t, f) :: l)).
Proof.
  intros.
  eauto using maps_to_ancestor, child_eq.
Qed.

Lemma maps_to_cons_perm:
  forall l' f p l,
  MapsTo l' f (Node l) ->
  MapsTo l' f (Node (p :: l)%list).
Proof.
  intros.
  inversion H.
  - subst.
    auto using maps_to_child, child_cons_perm.
  - subst.
    eauto using maps_to_ancestor, child_cons_perm.
Qed.

Lemma maps_to_inv_child:
  forall t f f',
  MapsTo (t :: nil) f f' ->
  Child t f f'.
Proof.
  intros.
  inversion H.
  - subst.
    assumption.
  - subst.
    inversion H2.
Qed.

Lemma maps_to_inv_cons_nil:
  forall t t' f f',
  MapsTo (t::nil) f (Node ((t', f') :: nil)) ->
  t' = t /\ f' = f.
Proof.
  intros.
  inversion H.
  - subst.
    apply child_inv_cons_nil in H1.
    destruct H1.
    subst.
    intuition.
  - subst.
    inversion H2.
Qed.

Lemma maps_to_inv_leaf:
  forall l f t,
  MapsTo l f (Node ((t, leaf):: nil))%list ->
  l = (t::nil)%list /\ f = leaf.
Proof.
  intros.
  inversion H.
  - subst.
    apply child_inv_cons_nil in H0.
    destruct H0.
    subst.
    intuition.
  - subst.
    apply child_inv_cons_nil in H1.
    destruct H1; subst.
    apply maps_to_leaf_absurd in H0.
    inversion H0.
Qed.

Inductive First : tid -> list tid -> Prop :=
  | first_eq:
    forall t,
    First t (t :: nil)
  | first_cons:
    forall t l t',
    First t l ->
    First t (t' :: l)%list.

Lemma first_inv_eq:
  forall t t',
  First t (t' :: nil) ->
  t =  t'.
Proof.
  intros.
  inversion H.
  - auto.
  - inversion H2.
Qed.

(*
Lemma maps_to_inv_cons_nodupa:
  forall t f l l' f',
  NoDupA (Map_TID.eq_key (elt:=finish)) ((t, f) :: l) ->
  MapsTo l' f' (Node ((t, f) :: l)) ->
  First t l' ->
  f = f' /\ l' = (t::nil).
Proof.
  intros.
  inversion H.
  subst.
  inversion H0.
  - subst.
    apply first_inv_eq in H1.
    subst.
    apply child_inv_cons_nodupa in H2; auto.
  - subst.
    destruct l0.
    { inversion H2. }
    inversion H1.
    subst.
Qed.
*)
*)