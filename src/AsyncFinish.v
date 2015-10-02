Require Import HJ.Phasers.Lang.
Require Import HJ.Vars.

Inductive finish :=
  | Node : list (tid * finish) -> finish.

Definition get_tasks f :=
match f with
  | Node l => l
end.

Notation leaf := (Node nil).

Section IND.

Hypothesis P : finish -> Prop.
Hypothesis Hnil: P (Node nil).
Hypothesis Hcons: forall f, P f ->  forall t l, P (Node ((t, f) :: l)).

Fixpoint finish_ind_weak (f:finish) : P f :=
match f as x return P x with
| Node l =>
    match l as x return P (Node x) with
    | nil => Hnil
    | cons (t,f') l' => Hcons f' (finish_ind_weak f') t l'
    end
end.

End IND.

Section STRONG_IND.

Hypothesis P : finish -> Prop.
Hypothesis Hnil: P (Node nil).
Hypothesis Hcons: forall f l, P f -> P (Node l) -> forall t, P (Node ((t, f) :: l)).

Fixpoint length f :=
match f with
  | Node l =>
    S (List.fold_left (fun (a:nat) (p:tid*finish) => a + length (snd p)) l 0) 
end.

Let fold_left_simpl:
  forall l x,
  List.fold_left (fun (a:nat) (p:tid*finish) => a + length (snd p)) l x =
  (List.fold_left (fun (a:nat) (p:tid*finish) => a + length (snd p)) l 0) + x.
Proof.
  intros l.
  induction l.
  - auto.
  - intros.
    simpl.
    remember (length (snd a)) as n.
    assert (Hx := IHl n).
    rewrite Hx.
    assert (Hy := IHl (x + n)).
    rewrite Hy.
    omega.
Qed.

Lemma length_leaf:
  length leaf = S 0.
Proof.
  auto.
Qed.

Lemma length_node_leaf:
  forall t f n,
  length f = n ->
  length (Node ((t, f) :: nil)) = S n.
Proof.
  intros.
  simpl.
  auto.
Qed.

Lemma length_cons:
  forall  t f l,
  length (Node ((t, f) :: l)) = (length f + length (Node l)).
Proof.
  intros.
  simpl.
  remember (List.fold_left (fun (a : nat) (p : tid * finish) => a + length (snd p)) l
     (length f)) as n.
  rewrite fold_left_simpl in Heqn.
  remember (List.fold_left
         (fun (a : nat) (p : tid * finish) => a + length (snd p)) l 0) as m.
  rewrite Heqn.
  auto with *.
Qed.

Lemma length_pos:
  forall f,
  length f > 0.
Proof.
  intros.
  destruct f.
  simpl.
  auto with *.
Qed.

Function finish_ind_strong (f:finish) { measure length } : P f :=
match f as x return P x with
| Node l =>
    match l as x return P (Node x) with
    | nil => Hnil
    | cons (t,f') l' => Hcons f' l' (finish_ind_strong f') (finish_ind_strong (Node l')) t
    end
end.
Proof.
 - intros.
   subst.
   rewrite length_cons.
   assert (length f' > 0). {
     auto using length_pos.
   }
   auto with *.
 - intros.
   rewrite length_cons.
   assert (length (Node l') > 0). {
     auto using length_pos.
   }
   omega.
Qed.
End STRONG_IND.

Inductive Child (t:tid) (f:finish) (f':finish) : Prop := 
  child_def:
    List.In (t, f) (get_tasks f') ->
    Child t f f'.

Lemma child_eq:
  forall t f l,
  Child t f (Node ((t, f) :: l)).
Proof.
  intros.
  eapply child_def.
  simpl.
  intuition.
Qed.

Lemma child_leaf_absurd:
  forall t f,
  Child t f leaf -> False.
Proof.
  intros.
  inversion H.
  simpl in *.
  inversion H0.
Qed.

Lemma child_inv_cons_nil:
  forall t f t' f',
  Child t' f' (Node ((t, f) :: nil)) ->
  t' = t /\ f' = f.
Proof.
  intros.
  inversion H.
  simpl in *.
  destruct H0; (inversion H0; intuition).
Qed.

Lemma child_inv_cons:
  forall t f f' l,
  Child t f' (Node ((t, f) :: l)) ->
  f' = f \/ Child t f' (Node l).
Proof.
  intros.
  inversion H; subst; clear H.
  simpl in *.
  destruct H0.
  - left.
    inversion H.
    trivial.
  - right.
    apply child_def.
    auto.
Qed.

Lemma child_neq:
  forall t f t' f' l,
  t <> t' ->
  Child t f (Node ((t', f') :: l)) ->
  Child t f (Node l).
Proof.
  intros.
  inversion H0.
  destruct H1.
  - (* absurd *)
    inversion H1; contradiction H.
    auto.
  - auto using child_def.
Qed.

Lemma child_cons_perm:
  forall l t f p,
  Child t f (Node l) ->
  Child t f (Node (p :: l)).
Proof.
  intros.
  apply child_def.
  simpl.
  right.
  inversion H.
  auto.
Qed.

Inductive Leaf (t:tid) (f:finish) : Prop :=
  leaf_def:
    Child t leaf f ->
    Leaf t f.

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

Inductive First : tid -> list tid -> Prop :=
  | first_eq:
    forall t,
    First t (t :: nil)
  | first_cons:
    forall t l t',
    First t l ->
    First t (t' :: l)%list.

Inductive Lookup (t:tid) (f':finish) (f:finish) : Prop :=
  lookup_def:
    forall l,
    MapsTo l f' f ->
    First t l ->
    Lookup t f' f.

Lemma lookup_leaf_absurd:
  forall t f,
  Lookup t f leaf -> False.
Proof.
  intros.
  inversion H; subst.
  eauto using maps_to_leaf_absurd.
Qed.

Lemma lookup_cons:
  forall t t' f f' l,
  Lookup t f' f ->
  Lookup t f' (Node ((t', f) :: l)).
Proof.
  intros.
  inversion H.
  eauto using lookup_def, maps_to_cons, first_cons.
Qed.

Inductive In (t:tid) (f:finish) : Prop :=
  in_def:
    forall f',
    Lookup t f' f ->
    In t f.

Lemma in_eq:
  forall t f l,
  In t (Node ((t, f) :: l)).
Proof.
  intros.
  eauto using in_def, lookup_def, maps_to_eq, first_eq.
Qed.

Lemma in_cons:
  forall t f t' l,
  In t f ->
  In t (Node ((t', f) :: l)).
Proof.
  intros.
  inversion H.
  eauto using in_def, lookup_cons.
Qed.

(** Add task [t] to finish [f]. *)

Definition as_map (f:finish) : Map_TID.t finish :=
  Map_TID_Props.of_list (get_tasks f).

Definition from_map (m:Map_TID.t finish) : finish :=
  Node (Map_TID.elements m).

Definition add t f f' :=
    from_map (Map_TID.add t f (as_map f')).

Definition remove t f :=
  from_map (Map_TID.remove t (as_map f)).

Module Semantics.

(**
  In async/finish all operations are blocking, because a task
  might be stuck in a finish. *)

Inductive op :=
  | BEGIN_ASYNC : tid -> op
  | END_ASYNC
  | BEGIN_FINISH
  | END_FINISH.

Definition is_begin_async (o:op) : bool :=
match o with
  | BEGIN_ASYNC _ => true
  |  _ => false
end.

Inductive Disjoint (f:finish) : op -> Prop :=
  | disjoint_ok:
    forall t,
    ~ In t f ->
    Disjoint f (BEGIN_ASYNC t)
  | disjoint_skip:
    forall o,
    is_begin_async o = false ->
    Disjoint f o.

Inductive Reduce (f:finish) (t:tid) : op -> finish -> Prop :=
  | begin_async:
    forall t',
    Leaf t f ->
    ~ In t' f ->
    Reduce f t (BEGIN_ASYNC t') (add t' leaf f)
  | end_async:
    Leaf t f ->
    Reduce f t END_ASYNC (remove t f)
  | begin_finish:
    Reduce f t BEGIN_FINISH (add t (add t leaf leaf) f)
  | end_finish:
    Child t leaf f ->
    Reduce f t END_FINISH (add t leaf f)
  | reduce_nested:
    forall o f' f'' t',
    Disjoint f o ->
    Child t' f' f ->
    Reduce f' t o f'' ->
    Reduce f t o (add t' f'' f).

End Semantics.


Module Progress.

(**
  Any unblocked 
  The proof for this lemma is trivial, by inversion of proposition [Check].
  *)

Require Import HJ.Progress.

Inductive Nonempty : finish -> Prop :=
  nonempty_def:
    forall t f,
    In t f ->
    Nonempty f.

Lemma in_leaf_absurd:
  forall t,
  In t leaf -> False.
Proof.
  intros.
  inversion H.
  eauto using lookup_leaf_absurd.
Qed.

Lemma nonempty_leaf_absurd:
  Nonempty leaf -> False.
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
      apply can_reduce_def with (add t s' s).
      apply Semantics.reduce_nested with (f':=(Node (p :: l'))).
      * apply Semantics.disjoint_skip.
        simpl.
        trivial.
      * subst; apply child_eq.
      * assumption.
Qed.

Inductive Flat (f:finish) : Prop :=
  flat_def:
    (forall t f', Child t f' f -> f' = leaf) ->
    Flat f.

Lemma flat_cons:
  forall t l,
  Flat (Node l) ->
  Flat (Node ((t, leaf) :: l)).
Proof.
  intros.
  inversion H.
  apply flat_def.
  intros.
  destruct (TID.eq_dec t0 t).
  - subst.
    apply child_inv_cons in H1.
    destruct H1.
    + assumption.
    + eauto using H0.
  - apply child_neq in H1; auto.
    eauto using H0.
Qed.

Lemma nonempty_dec:
  forall f,
  { Nonempty f } + {f = leaf }.
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
  Flat f \/ (exists l f', MapsTo l f' f /\ Flat f').
Proof.
  intros.
  induction f using finish_ind_strong.
  - apply nonempty_leaf_absurd in H.
    inversion H.
  - clear H.
    destruct (nonempty_dec f).
    + apply IHf in n; clear IHf.
      destruct n as [?|(l', (f', (Hmt, Hf)))].
      * right.
        exists (t::nil)%list.
        exists f.
        intuition.
        apply maps_to_eq.
      * right.
        exists (t::l')%list.
        exists f'.
        intuition.
        auto using maps_to_cons.
    + subst.
      clear IHf.
      destruct l.
      * left.
        apply flat_def.
        intros.
        apply child_inv_cons_nil in H.
        destruct H; auto.
      * assert (Hn : Nonempty (Node (p :: l))). {
          auto using nonempty_cons.
        }
        apply IHf0 in Hn; clear IHf0.
        destruct Hn.
        (* left *)
        {
          left.
          auto using flat_cons.
        }
        right.
        destruct H as (l', (f, (?, ?))).
        exists l'.
        exists f.
        intuition.
        auto using maps_to_cons_perm.
Qed.

End Progress.

(*
Module Examples.
(**
Original FX10 example:

              (t1: "finish { async S3 f() } S2") -> (t1, begin_finish)
                (t1: "async S3 f()"> |> t1: "S2" -> (t1, begin_async t2)
           (t2: "S3") || (t1: "f()") |> t1: "S2" -> (... evaluates function)
      (t2: "S3") || (t1: "async S5") |> t1: "S2" -> (t2, begin_async t3) 
(t2: "S3") || (t1: "") || (t3: "S5") |> t1: "S2" -> (t1, end_async)
            (t2: "S3") || (t3: "S5") |> t1: "S2" -> (t2, end_async)
                          (t3: "S5") |> t1: "S2" -> (t3, end_async)
                                Idle |> t1: "S2" -> (t3, end_finish)
                                      (t1: "S2") -> (t1, end_async)
                                            Idle

*)
Let t1:= 1.
(*
(t1: "finish { async S3 f() } S2") -> (t1, begin_finish)
(t1: "async S3 f()"> |> t1: "S2"
*)
Goal Reduce (Task t1) t1 BEGIN_FINISH (Finish (Task t1) t1).
Proof.
  auto using begin_finish.
Qed.

Let t2 := 2.
(*
(t1: "async S3 f()"> |> t1: "S2" -> (t1, begin_async t2)
(t2: "S3") || (t1: "f()") |> t1: "S2"
*)
Goal Reduce (Finish (Task t1) t1) t1 (BEGIN_ASYNC t2)
  (Finish (Par (Task t1) (Task t2)) t1).
Proof.
  eapply run_finish.
  - eapply disjoint_ok.
    intuition.
    inversion H.
  - eapply begin_async.
Qed.

(*
(t2: "S3") || (t1: "async S5") |> t1: "S2"
-> (t2, begin_async t3) 
(t2: "S3") || (t1: "") || (t3: "S5") |> t1: "S2"
*)

Let t3 := 3.

Goal Reduce
  (Finish (Par (Task t1) (Task t2)) t1)
  t1 (BEGIN_ASYNC t3)
  (Finish
    (Par (Par (Task t1) (Task t3)) (Task t2)) t1).
Proof.
  eapply run_finish.
  + eapply disjoint_ok; intuition; inversion H.
  + eapply run_par_left.
    - eapply disjoint_ok.
      intuition.
      inversion H.
    - eapply begin_async.
Qed.

(*
(t2: "S3") || (t1: "") || (t3: "S5") |> t1: "S2" -> (t1, end_async)
(t2: "S3") || Idle || (t3: "S5") |> t1: "S2"
*)
Goal Reduce
  (Finish
    (Par (Par (Task t1) (Task t3)) (Task t2)) t1)
  t1 END_ASYNC
  (Finish
    (Par (Par Idle (Task t3)) (Task t2)) t1).
Proof.
  eapply run_finish.
  { eapply disjoint_skip. auto. }
  eapply run_par_left.
  - eauto using disjoint_skip.
  - eapply run_par_left.
    + eauto using disjoint_skip.
    + eapply end_async.
Qed.

(*
(t2: "S3") || Idle || (t3: "S5") |> t1: "S2"
-> (t2, end_async)
(t3: "S5") || Idle || Idle |> t1: "S2"
*)
Goal Reduce
  (Finish
    (Par (Par Idle (Task t3)) (Task t2)) t1)
  t2 END_ASYNC
  (Finish
    (Par (Par Idle (Task t3)) Idle) t1).
Proof.
  eapply run_finish.
  { eapply disjoint_skip. auto. }
  eapply run_par_right.
  - eauto using disjoint_skip.
  - eapply end_async.
Qed.

(*
(t3: "S5") || Idle || Idle |> t1: "S2"
-> (t3, end_async)
Idle |> t1: "S2"
*)
Goal Reduce
  (Finish
    (Par (Par Idle (Task t3)) Idle) t1)
  t3 END_ASYNC
  (Finish
    (Par (Par Idle Idle) Idle) t1).
Proof.
  eapply run_finish.
  { apply disjoint_skip. auto. }
  eapply run_par_left.
  - eauto using disjoint_skip.
  - eapply run_par_right.
    + eauto using disjoint_skip.
    + eapply end_async.
Qed.

(*
Idle  || Idle  || Idle |> t1: "S2"
-> (t3, end_async)
(t1: "S2")
*)
Goal Reduce
  (Finish
    (Par (Par Idle Idle) Idle) t1)
  t1 END_FINISH
  (Task t1).
Proof.
  eapply run_congruence.
  simpl.
  eapply end_finish.
Qed.

(*
(t1: "S2")
->
Idle
*)
Goal Reduce
  (Task t1)
  t1 END_ASYNC
  Idle.
Proof.
  eapply end_async.
Qed.

End Examples.
*)
