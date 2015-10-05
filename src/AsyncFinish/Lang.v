Require Import HJ.Vars.

Require Import Coq.Lists.SetoidList.


Inductive task :=
  | Ready
  | Blocked : finish -> task
with finish :=
  | Node : list (tid * task) -> finish.

Definition get_tasks f :=
match f with
  | Node l => l
end.

(** Labeled task  *)
Definition l_task := (tid * task) % type.

Scheme task_finish_rec := Induction for task Sort Set
  with finish_task_rec := Induction for finish Sort Set.

Definition mk_finish (t:tid) : finish := Node ((t,Ready) :: nil).

Section IND.

Hypothesis P : finish -> Prop.
Hypothesis Hnil: P (Node nil).
Hypothesis HconsR: forall t l, P (Node ((t, Ready) :: l)).
Hypothesis HconsB: forall f, P f ->  forall t l, P (Node ((t, Blocked f) :: l)).

Fixpoint finish_ind_weak (f:finish) : P f :=
match f as x return P x with
| Node l =>
    match l as x return P (Node x) with
    | nil => Hnil
    | cons (t,a) l =>
      match a with
      | Ready => HconsR t l
      | Blocked f => HconsB _ (finish_ind_weak f) t l
      end
    end
end.

End IND.

Section STRONG_IND.

Hypothesis P : finish -> Prop.
Hypothesis Hnil: P (Node nil).
Hypothesis HconsR: forall t l, P (Node l) -> P (Node ((t, Ready) :: l)).
Hypothesis HconsB: forall f l, P f -> P (Node l) -> forall t, P (Node ((t, Blocked f) :: l)).

Fixpoint finish_ind_strong (f:finish) : P f :=
match f with
| Node l =>
    (fix aux (l:list l_task) : P (Node l) :=
    match l with
    | nil => Hnil
    | cons (t,a) l =>
      match a with
      | Ready => HconsR t l (aux l)
      | Blocked f => HconsB f l (finish_ind_strong f) (aux l) t
      end
    end) l
end.

End STRONG_IND.

Inductive Child (t:tid) (a:task) (f:finish) : Prop := 
  child_def:
    List.In (t, a) (get_tasks f) ->
    Child t a f.

Lemma child_eq:
  forall t a l,
  Child t a (Node ((t, a) :: l)).
Proof.
  intros.
  eapply child_def.
  simpl.
  intuition.
Qed.

Lemma child_cons:
  forall t f l p,
  Child t f (Node l) ->
  Child t f (Node (p :: l)).
Proof.
  intros.
  eapply child_def.
  destruct H.
  simpl in *.
  intuition.
Qed.

Lemma child_leaf_absurd:
  forall t f,
  Child t f (Node nil) -> False.
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

Lemma child_to_ina:
  forall  t f l,
  Child t f (Node l) -> 
  InA (Map_TID.eq_key (elt:=task)) (t, f) l.
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
    Child t Ready f ->
    Leaf t f.

Inductive Lt (f:finish) (f':finish) : Prop :=
  lt_def:
    forall t,
    Child t (Blocked f) f' ->
    Lt f f'
where "f < f'" := (Lt f f') : finish_scope.

Local Open Scope finish_scope.

Lemma lt_leaf_absurd:
  forall f,
  f < (Node nil) -> False.
Proof.
  intros.
  intuition.
  inversion H.
  apply child_leaf_absurd in H0.
  assumption.
Qed.

Lemma lt_cons:
  forall f l p,
  f < Node l ->
  f < Node (p :: l).
Proof.
  intros.
  inversion H.
  eauto using lt_def, child_cons_perm.
Qed.

Lemma lt_inv_cons:
  forall f p l,
  f < Node (p :: l) ->
  (snd p = Blocked f) \/ f < (Node l).
Proof.
  intros.
  inversion H.
  destruct p as  (t', a).
  destruct H0.
  destruct H0.
  * inversion H0.
    intuition.
  * right.
    apply lt_def with (t).
    apply child_def.
    simpl.
    auto.
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
  Some P (Node ((t,(Blocked f))::l)).
Proof.
  intros.
  eauto using some_parent, lt_def, child_eq.
Qed.

Lemma some_cons_rhs:
  forall (P:finish->Prop) p l,
  Some P (Node l) ->
  ( (P (Node l)) ->  P (Node (p::l))) ->
  Some P (Node (p::l)).
Proof.
  intros.
  inversion H.
  - apply some_ok.
    auto.
  - eauto using some_parent, lt_cons.
Qed.

Lemma some_inv_nil:
  forall P,
  Some P (Node nil) ->
  P (Node nil).
Proof.
  intros.
  inversion H.
  - assumption.
  - apply lt_leaf_absurd in H1.
    inversion H1.
Qed.

Lemma some_inv_cons:
  forall P p l,
  Some P (Node (p :: l)) ->
  (P (Node (p::l))) \/
  (exists f, snd p = Blocked f /\ Some P f) \/ Some P (Node l).
Proof.
  intros.
  inversion H.
  - intuition.
  - right.
    apply lt_inv_cons  in H1.
    destruct H1.
    + left.
      exists f'.
      intuition.
    + right.
      eauto using some_parent.
Qed.

Inductive Lookup (t:tid) (a:task) (f:finish) : Prop :=
  lookup_def:
    Some (fun (f':finish) => Child t a f') f -> 
    Lookup t a f.

Lemma lookup_leaf_absurd:
  forall t f,
  Lookup t f (Node nil) -> False.
Proof.
  intros.
  inversion H; subst.
  inversion H0.
  - eauto using child_leaf_absurd.
  - eauto using lt_leaf_absurd.
Qed.

Lemma lookup_cons:
  forall t t' f a l,
  Lookup t a f ->
  Lookup t a (Node ((t', (Blocked f)) :: l)).
Proof.
  intros.
  inversion H.
  eauto using lookup_def, some_cons, lt_def.
Qed.

Lemma lookup_cons_rhs:
  forall t a p l,
  Lookup t a (Node l) ->
  Lookup t a (Node (p :: l)).
Proof.
  intros.
  inversion H; clear H.
  auto using lookup_def, some_cons_rhs, child_cons.
Qed.

Lemma lookup_eq:
  forall t a l,
  Lookup t a (Node ((t, a) :: l)).
Proof.
  intros.
  eauto using lookup_def, some_ok, child_eq.
Qed.

Lemma lookup_inv:
  forall l a t a' t',
  Lookup t a (Node ((t', a') :: l)) ->
  (t' = t /\ a' = a) \/ (exists f', a' = Blocked f' /\ Lookup t a f') \/ Lookup t a (Node l).
Proof.
  intros.
  destruct H.
  inversion H.
  - destruct H0.
    inversion H0.
    + inversion H1.
      left.
      intuition.
    + right.
      right.
      eauto using child_def, lookup_def, some_ok.
  - inversion H1.
    apply child_inv_cons in H2.
    destruct H2 as [(?,?)|?].
    + subst.
      right.
      left.
      exists f'.
      intuition.
      auto using lookup_def.
    + right; right.
      assert (f' < (Node l)). {
        eauto using lt_def.
      }
      eauto using lookup_def, some_parent.
Qed.

Inductive In (t:tid) (f:finish) : Prop :=
  in_def:
    forall a,
    Lookup t a f ->
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
  In t (Node ((t', (Blocked f)) :: l)).
Proof.
  intros.
  inversion H.
  eauto using in_def, lookup_cons.
Qed.

Lemma in_cons_rhs:
  forall t p l,
  In t (Node l) ->
  In t (Node (p :: l)).
Proof.
  intros.
  destruct H.
  eauto using in_def, lookup_cons_rhs.
Qed.

Lemma in_leaf_absurd:
  forall t,
  In t (Node nil) -> False.
Proof.
  intros.
  inversion H.
  eauto using lookup_leaf_absurd.
Qed.

Lemma in_inv_leaf:
  forall t t',
  In t (Node ((t',Blocked (Node nil))::nil)) ->
  t = t'.
Proof.
  intros.
  inversion H.
  apply lookup_inv in H0.
  destruct H0.
  - intuition.
  - destruct H0 as  [(?,(?,?))|?].
    + inversion H0.
      subst.
      apply lookup_leaf_absurd in H1; inversion H1.
    + apply lookup_leaf_absurd in H0; inversion H0.
Qed.

Lemma in_inv_cons:
  forall t t' a l,
  In t (Node ((t',a) :: l)) ->
  t = t' \/ (exists f, a = Blocked f /\ In t f) \/ In t (Node l).
Proof.
  intros.
  inversion H.
  apply lookup_inv in H0.
  destruct H0 as [(?,?)|[(f,(?,?))|?]].
  - intuition.
  - right.
    left.
    subst.
    exists f.
    intuition.
    eauto using in_def.
  - right.
    right.
    eauto using in_def.
Qed.

(** Add task [t] to finish [f]. *)

Definition as_map (f:finish) : Map_TID.t task :=
  Map_TID_Props.of_list (get_tasks f).

Definition from_map (m:Map_TID.t task) : finish :=
  Node (Map_TID.elements m).

Definition put (f:finish) (p:l_task) : finish :=
  from_map (Map_TID.add (fst p) (snd p) (as_map f)).

Definition remove (f:finish) (t:tid) :=
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

Lemma disjoint_inv_cons_rhs:
  forall p l o,
  Disjoint (Node ((p :: l))) o ->
  Disjoint (Node l) o.
Proof.
  intros.
  inversion H.
  + apply disjoint_ok.
    intuition.
    contradiction H0.
    apply in_cons_rhs.
    assumption.
  + apply disjoint_skip.
    assumption.
Qed.

Lemma disjoint_inv_cons_lhs:
  forall t f l o,
  Disjoint (Node (((t, Blocked f) :: l))) o ->
  Disjoint f o.
Proof.
  intros.
  inversion H.
  + apply disjoint_ok.
    intuition.
    contradiction H0.
    apply in_cons.
    assumption.
  + apply disjoint_skip.
    assumption.
Qed.

Inductive Reduce (f:finish) (t:tid) : op -> finish -> Prop :=
  | begin_async:
    forall t',
    Leaf t f ->
    ~ In t' f ->
    Reduce f t (BEGIN_ASYNC t') (put f (t', Ready))
  | end_async:
    Leaf t f ->
    Reduce f t END_ASYNC (remove f t)
  | begin_finish:
    Leaf t f ->
    Reduce f t BEGIN_FINISH (put f (t, Blocked (mk_finish t)))
  | end_finish:
    Child t (Blocked (Node nil)) f ->
    Reduce f t END_FINISH (put f (t, Ready))
  | reduce_nested:
    forall t' o f' f'',
    Disjoint f o ->
    Child t' (Blocked f') f ->
    Reduce f' t o f'' ->
    Reduce f t o (put f (t', Blocked f'')).

End Semantics.

Module FinishNotations.
Notation "[]" := (Node nil) : finish_scope.
Notation "[ p ]" :=  (Node ( (p  :: nil ) )) :  finish_scope.
Infix " <| " :=  (fun (t:tid) (f:finish) => (t, Blocked f)) (at level 50, left associativity)  :  finish_scope.
Notation "! t" :=  (t, Ready) (at level 60)   :  finish_scope.
Notation " [ x | .. | y ] " := (Node ((cons x .. (cons y nil) ..) )) : finish_scope.
Infix " |+ " :=  (put) (at level 60, right associativity)  :  finish_scope.
Infix " |- " :=  (remove) (at level 60, right associativity)  :  finish_scope.

End FinishNotations.