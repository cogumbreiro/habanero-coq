Require Import HJ.Phasers.Lang.
Require Import HJ.Vars.

Require Import Coq.Lists.SetoidList.

Inductive finish :=
  | Node : list (tid * finish) -> finish.

Definition get_tasks f :=
match f with
  | Node l => l
end.

Notation leaf := (Node nil).

Definition singleton (t:tid) : finish :=
  Node (  (t,leaf)  :: nil).

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
    S (List.fold_left (fun (a:nat) (p:(tid*finish)%type) => a + length (snd p)) l 0) 
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

Lemma child_cons:
  forall t f l t' f',
  Child t f (Node l) ->
  Child t f (Node ((t', f') :: l)).
Proof.
  intros.
  eapply child_def.
  destruct H.
  simpl in *.
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

Lemma child_inv_cons:
  forall t t' f f' l,
  Child t f (Node ((t', f') :: l)) ->
  (t' = t /\ f' = f) \/ Child t f (Node l).
Proof.
  intros.
  inversion H.
  inversion H0.
  - inversion H1; intuition.
  - right.
    apply child_def; simpl; assumption.
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
(*
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
*)
Lemma child_to_ina:
  forall  t f l,
  Child t f (Node l) -> 
  InA (Map_TID.eq_key (elt:=finish)) (t, f) l.
Proof.
  intros.
  destruct H.
  apply InA_alt.
  exists (t,f).
  intuition.
Qed.

Lemma ina_eq_key_subst:
  forall t f f' l, 
  InA (Map_TID.eq_key (elt:=finish)) (t, f) l ->
  InA (Map_TID.eq_key (elt:=finish)) (t, f') l.
Proof.
  intros.
  apply InA_alt.
  apply InA_alt  in H.
  destruct H as ((t',f''), (?,?)).
  apply Map_TID_Extra.eq_key_unfold in H.
  subst.
  exists (t', f'').
  rewrite Map_TID_Extra.eq_key_unfold.
  intuition.
Qed.
(*
Lemma child_inv_cons_nodupa:
  forall t f f' l,
  NoDupA (Map_TID.eq_key (elt:=finish)) ((t,f') :: l) ->
  Child t f (Node ((t, f') :: l)) ->
  f' = f.
Proof.
  intros.
  apply child_inv_cons in H0.
  destruct H0; auto.
  inversion H.
  subst.
  contradiction H3.
  eauto using child_to_ina, ina_eq_key_subst.
Qed.
*)
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

Inductive Lt (f:finish) (f':finish) : Prop :=
  lt_def:
    forall t,
    Child t f f' ->
    Lt f f'
where "f < f'" := (Lt f f') : finish_scope.

Local Open Scope finish_scope.

Lemma lt_leaf_absurd:
  forall f,
  f < leaf -> False.
Proof.
  intros.
  intuition.
  inversion H.
  apply child_leaf_absurd in H0.
  assumption.
Qed.

Inductive Some (P: finish -> Prop) (f:finish) : Prop :=
  | some_ok:
    P f ->
    Some P f
  | some_parent:
    forall f',
    Some P f' ->
    f' < f ->
    Some P f.

Lemma some_cons:
  forall P f t l,
  Some P f ->
  Some P (Node ((t,f)::l)).
Proof.
  intros.
  eauto using some_parent, lt_def, child_eq.
Qed.

Inductive Lookup (t:tid) (f':finish) (f:finish) : Prop :=
  lookup_def:
    Some (fun (f'':finish) => Child t f' f'') f -> 
    Lookup t f' f.

Lemma lookup_leaf_absurd:
  forall t f,
  Lookup t f leaf -> False.
Proof.
  intros.
  inversion H; subst.
  inversion H0.
  - eauto using child_leaf_absurd.
  - eauto using lt_leaf_absurd.
Qed.

Lemma lookup_cons:
  forall t t' f f' l,
  Lookup t f' f ->
  Lookup t f' (Node ((t', f) :: l)).
Proof.
  intros.
  inversion H.
  eauto using lookup_def, some_cons, lt_def.
Qed.

Lemma lookup_eq:
  forall t f l,
  Lookup t f (Node ((t, f) :: l)).
Proof.
  intros.
  eauto using lookup_def, some_ok, child_eq.
Qed.

Lemma lookup_inv:
  forall l f t f' t',
  Lookup t f (Node ((t', f') :: l)) ->
  (t' = t /\ f' = f) \/ Lookup t f f' \/ Lookup t f (Node l).
Proof.
  intros.
  destruct H.
  inversion H.
  - destruct H0.
    inversion H0.
    + inversion H1.
      left.
      intuition.
    + assert (Child t f (Node l)). {
        assert (In (t, f) (get_tasks (Node l))). {
          auto.
        }
        auto using child_def.
      }
      right.
      right.
      eauto using lookup_def, some_ok.
  - inversion H1.
    apply child_inv_cons in H2.
    destruct H2.
    + destruct H2; subst.
      right.
      left.
      auto using lookup_def.
    + right; right.
      assert (f'0 < (Node l)). {
        eauto using lt_def.
      }
      eauto using lookup_def, some_parent.
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
  eauto using in_def, lookup_eq.
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

Lemma in_leaf_absurd:
  forall t,
  In t leaf -> False.
Proof.
  intros.
  inversion H.
  eauto using lookup_leaf_absurd.
Qed.

Lemma in_inv_leaf:
  forall t t',
  In t (Node ((t',leaf)::nil)) ->
  t = t'.
Proof.
  intros.
  inversion H.
  apply lookup_inv in H0.
  destruct H0.
  - intuition.
  - destruct H0; (apply lookup_leaf_absurd in H0; inversion H0).
Qed.

Lemma in_inv_cons:
  forall t t' f l,
  In t (Node ((t',f) :: l)) ->
  t = t' \/ In t f \/ In t (Node l).
Proof.
  intros.
  inversion H.
  apply lookup_inv in H0.
  destruct H0 as [(?,?)|[?|?]].
  - intuition.
  - right.
    left.
    eauto using in_def.
  - right.
    right.
    eauto using in_def.
Qed.

(*
Lemma lookup_impl_some_child:
  forall f' t f,
  Lookup t f f' -> Some (fun (f'':finish) => Child t f f'') f'.
Proof.
  intros f'.
  induction f' using finish_ind_strong.
  - intros.
    apply lookup_leaf_absurd in H.
    inversion H.
  - intros.
      
Qed.*)
(*
Lemma lookup_alt:
  forall t f f',
  Lookup t f f' <-> Some (fun (f'':finish) => Child t f f'') f'.
Qed.
*)
Inductive ParentOf (t:tid) (t':tid) (f:finish) : Prop :=
  | parent_of_def:
    forall f' f'',
    Child t' f'' f' ->
    Child t f' f ->
    ParentOf t t' f.

Inductive AncestorOf (t:tid) (t':tid) (f:finish) : Prop :=
  | ancestor_of_eq:
    ParentOf t t' f ->
    AncestorOf t t' f

  | ancestor_of_cons:
    forall t'' f',
    AncestorOf t'' t' f' ->
    Child t f' f ->
    AncestorOf t t' f.

(** Add task [t] to finish [f]. *)

Definition as_map (f:finish) : Map_TID.t finish :=
  Map_TID_Props.of_list (get_tasks f).

Definition from_map (m:Map_TID.t finish) : finish :=
  Node (Map_TID.elements m).

Definition put t f f' :=
  from_map (Map_TID.add t f (as_map f')).

Definition put_leaf t f :=
  put t leaf f.

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

Lemma disjoint_inv_begin_async:
  forall f t,
  Disjoint f (BEGIN_ASYNC t) ->
  ~ In t f.
Proof.
  intros.
  inversion H.
  - assumption.
  - simpl in H0.
    inversion H0.
Qed.

Fixpoint NotIn (t:tid) (f:finish) : Prop :=
  match f with
   Node l =>
     (fix disjoint_alt (l:list (tid*finish)) : Prop :=
       match l with
       | (t',f) :: l => t <> t' /\ NotIn t f /\ disjoint_alt l
       | nil => True
       end
     ) l
  end.

Lemma disjoint_alt_spec_1:
  forall t f,
  NotIn t f ->
  ~ In t f.
Proof.
  intros.
  induction f using finish_ind_strong.
  - eauto using in_leaf_absurd.
  - simpl in  H.
    destruct H as (?, (?, ?)).
    intuition.
    apply in_inv_cons in H2.
    destruct H2 as [?|[?|?]].
    + subst.
      apply H; trivial.
    + contradiction H3.
    + contradiction H4.
Qed.

(*
Lemma disjoint_alt_spec_2:
  forall t f,
  Disjoint f (BEGIN_ASYNC t) ->
  DisjointAlt t f.
Proof.
  intros.
  induction f using finish_ind_strong.
  - simpl. trivial.
  - simpl.
    
    inversion H.
    + subst; clear H.
      assert (
Qed.
*)
Fixpoint disjoint (t:tid) (f:finish) : bool :=
  match f with
    Node l =>
      (fix disjoint_alt (l:list (tid*finish)) : bool :=
       match l with
       | (t',f) :: l =>
         if TID.eq_dec t t then false
         else andb (disjoint t f) (disjoint_alt l)
       | nil => true
       end
     ) l 
  end.

(*
Fixpoint names (f:finish) : list tid :=
match f with
  | Node l =>
    (fix lnames (l':list (tid *finish)) : list tid :=
    match l' with
      | ((t,f) :: l'') =>
        t :: (names f) ++ (lnames l'')
      | nil => nil
    end) l
end.

Lemma names_spec_1:
  forall f t,
  In t f ->
  List.In t (names f).
Proof.
  intros f.
  induction f using finish_ind_strong.
  - intros; apply in_leaf_absurd in H.
    inversion H.
  - intros.
    inversion H.
Qed.

Lemma names_spec:
  forall f,
  (forall t, In t f <-> List.In t (names f)).
*)
Inductive Reduce (f:finish) (t:tid) : op -> finish -> Prop :=
  | begin_async:
    forall t',
    Leaf t f ->
    ~ In t' f ->
    Reduce f t (BEGIN_ASYNC t') (put_leaf t' f)
  | end_async:
    Leaf t f ->
    Reduce f t END_ASYNC (remove t f)
  | begin_finish:
    Reduce f t BEGIN_FINISH (put t (singleton t) f)
  | end_finish:
    Child t leaf f ->
    Reduce f t END_FINISH f
  | reduce_nested:
    forall o f' f'' t',
    Disjoint f o ->
    Child t' f' f ->
    Reduce f' t o f'' ->
    Reduce f t o (put t' f'' f).

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
      apply can_reduce_def with (put t s' s).
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
    + intuition.
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

Module Examples.
Module FX10.
Import Semantics.

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
Goal Reduce (singleton t1) t1 BEGIN_FINISH (put t1 (singleton t1) (singleton t1)).
Proof.
  auto using begin_finish.
Qed.

(* Making singleton works as expected. *)
Goal singleton t1 = Node ((t1,leaf) :: nil).
Proof.
  auto.
Qed.

Notation "[]" := leaf : finish_scope.
(* Notation "*" := (Node nil) : finish_scope. *)
Notation "[ p ]" :=  (Node ( (p  :: nil ) ))   :  finish_scope.
Infix " <| " :=  (@pair tid finish) (at level 60, right associativity)  :  finish_scope.
Notation "! t" :=  (@pair tid finish t (Node nil)) (at level 60)   :  finish_scope.
Notation " [ x | .. | y ] " := (Node ((cons x .. (cons y nil) ..) )) : finish_scope.

Ltac solve_notin :=
  (apply disjoint_alt_spec_1;
    simpl;
    intuition; inversion H).

Ltac solve_disjoint :=
  (apply disjoint_ok; solve_notin) ||
  (apply disjoint_skip; auto).

Goal put t1 (singleton t1) (singleton t1) = [ t1 <| [ ! t1 ] ] .
Proof.
  auto.
Qed.

Let t2 := 2.
(*
(t1: "async S3 f()"> |> t1: "S2" -> (t1, begin_async t2)
[(t2: "S3") || (t1: "f()") |> t1: "S2"]
*)
Goal Reduce
  [ t1 <| [ ! t1 ] ]
  t1 (BEGIN_ASYNC t2)
  (put t1 [ ! t1 | ! t2 ]  [ t1 <| [ ! t1 ] ]).
Proof.
  apply reduce_nested with (f':=[!t1]).
  - solve_disjoint.
  - eapply child_eq.
  - eapply begin_async.
    eapply leaf_def, child_eq.
    intuition.
    apply in_inv_leaf in H.
    inversion H.
Qed.

(*
(t2: "S3") || (t1: "async S5") |> t1: "S2"
-> (t2, begin_async t3) 
(t2: "S3") || (t1: "") || (t3: "S5") |> t1: "S2"
*)

Let t3 := 3.

Goal Reduce
  [ t1 <| [ !t2 | !t1 ] ]
  t1 (BEGIN_ASYNC t3)
  (put t1 (put t3 leaf [ !t2 | !t1 ]) [ t1 <| [ !t2 | !t1 ] ]).
Proof.
  apply reduce_nested with ([ !t2 | !t1 ]).
  + solve_disjoint.
  + eapply child_eq.
  + eapply begin_async.
    eapply leaf_def.
    eapply child_cons.
    eapply child_eq.
    apply disjoint_alt_spec_1.
    simpl.
    intuition; inversion H.
Qed.

(** Test the output of test. *)
Goal
  (put t3 leaf [ !t2 | !t1 ]) = 
  [ !t1 | !t2 | !t3 ].
auto.
Qed.


(** Test the simplification of this expression. *)
Goal 
  (put t1 (put t3 leaf [ !t2 | !t1 ]) [ t1 <| [ !t2 | !t1 ] ])
  = 
  [ t1 <| [  !t1 | !t2 | !t3 ] ].
auto.
Qed.

(*
(t2: "S3") || (t1: "") || (t3: "S5") |> t1: "S2" -> (t1, end_async)
(t2: "S3") || Idle || (t3: "S5") |> t1: "S2"
*)
Goal Reduce
  [ t1 <| [  !t1 | !t2 | !t3 ] ]
  t1 END_ASYNC
  (put t1 (remove t1 [ !t1 | !t2 | !t3 ]) [ t1 <| [ !t1 | !t2 | !t3 ] ])
  .
Proof.
  apply reduce_nested with ([  !t1 | !t2 | !t3 ]).
  - solve_disjoint.
  - apply child_eq.
  - apply end_async.
    apply leaf_def.
    apply child_eq.
Qed.

Goal
  (put t1 (remove t1 [ !t1 | !t2 | !t3 ]) [ t1 <| [ !t1 | !t2 | !t3 ] ])
  = 
  [ t1 <| [ !t2 | !t3 ] ].
auto.
Qed.

(*
(t2: "S3") || Idle || (t3: "S5") |> t1: "S2"
-> (t2, end_async)
(t3: "S5") || Idle || Idle |> t1: "S2"
*)
Goal Reduce
  [ t1 <| [ !t2 | !t3 ] ]
  t2 END_ASYNC
  (put t1 (remove t2 [ !t2 | !t3 ]) [ t1 <| [ !t2 | !t3 ] ])
  .
Proof.
  apply reduce_nested with ([ !t2 | !t3 ]).
  - solve_disjoint.
  - apply child_eq.
  - apply end_async.
    apply leaf_def.
    apply child_eq.
Qed.

Goal (put t1 (remove t2 [ !t2 | !t3 ]) [ t1 <| [ !t2 | !t3 ] ])
 = 
 [ t1 <| [ !t3 ] ].
auto.
Qed.

(*
(t3: "S5") || Idle || Idle |> t1: "S2"
-> (t3, end_async)
Idle |> t1: "S2"
*)
Goal Reduce
  [ t1 <| [ !t3 ] ]
  t3 END_ASYNC
  (put t1 (remove t3 [ !t3 ]) [ t1 <| [ !t3 ] ])
  .
Proof.
  apply reduce_nested with ([ !t3 ]).
  - solve_disjoint.
  - apply child_eq.
  - apply end_async.
    apply leaf_def.
    apply child_eq.
Qed.

Goal
  (put t1 (remove t3 [ !t3 ]) [ t1 <| [ !t3 ] ])
  = 
  [!t1].
auto.
Qed.

(*
Idle  || Idle  || Idle |> t1: "S2"
-> (t3, end_async)
(t1: "S2")
*)
Goal Reduce
  [!t1]
  t1 END_FINISH
  [!t1].
Proof.
  apply end_finish.
  unfold singleton.
  apply child_eq.
Qed.

(*
(t1: "S2")
->
Idle
*)
Goal Reduce
  [!t1]
  t1 END_ASYNC
  [].
Proof.
  eapply end_async.
  apply leaf_def.
  apply child_eq.
Qed.
End FX10.
End Examples.

