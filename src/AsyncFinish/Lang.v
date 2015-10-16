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
    | (t, Ready) :: l => HconsR t l
    | (t, Blocked f) :: l => HconsB _ (finish_ind_weak f) t l
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
    | (t,Ready) :: l => HconsR t l (aux l)
    | (t, Blocked f) :: l => HconsB f l (finish_ind_strong f) (aux l) t
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

Lemma child_inv_cons_blocked_ready:
  forall t f t' l,
  Child t (Blocked f) (Node ((t', Ready) :: l)) ->
  Child t (Blocked f) (Node l).
Proof.
  intros.
  inversion H.
  apply child_def.
  simpl in *.
  destruct H0.
  - inversion H0.
  - assumption.
Qed.

Lemma child_inv_cons_ready_blocked:
  forall t f t' l,
  Child t Ready (Node ((t', Blocked f) :: l)) ->
  Child t Ready (Node l).
Proof.
  intros.
  inversion H.
  apply child_def.
  simpl in *.
  destruct H0.
  - inversion H0.
  - assumption.
Qed.

Inductive Leaf (t:tid) (f:finish) : Prop :=
  leaf_def:
    Child t Ready f ->
    Leaf t f.

Lemma leaf_cons:
  forall t l p,
  Leaf t (Node l) ->
  Leaf t (Node (p :: l)).
Proof.
  intros.
  apply leaf_def.
  inversion H.
  auto using child_cons.
Qed.

Inductive Sub (f:finish) (f':finish) : Prop :=
  sub_def:
    forall t,
    Child t (Blocked f) f' ->
    Sub f f'.

Require Import Coq.Relations.Relation_Operators.

Inductive Lt (f:finish) (f':finish) : Prop :=
  lt_def:
    clos_trans finish Sub f f' ->
    Lt f f'.

Inductive Gt (f:finish) (f':finish) : Prop :=
  gt_def:
    clos_trans finish (fun (f1:finish) (f2:finish) => Sub f2 f1) f f' ->
    Gt f f'.

Inductive Le (f:finish) (f':finish) : Prop :=
  le_def:
    clos_refl_trans finish Sub f f' ->
    Le f f'.

Inductive Ge (f:finish) (f':finish) : Prop :=
  ge_def:
    clos_refl_trans finish (fun (f1:finish) (f2:finish) => Sub f2 f1) f f' ->
    Ge f f'.

Notation "f < f'" := (Lt f f') : finish_scope.

Notation "f > f'" := (Gt f f') : finish_scope.

Notation "f <= f'" := (Le f f') : finish_scope.

Notation "f >= f'" := (Ge f f') : finish_scope.

Local Open Scope finish_scope.

Lemma lt_to_gt:
  forall f f',
  f < f' ->
  f' > f.
Proof.
  intros.
  inversion H; clear H.
  induction H0.
  - auto using gt_def, t_step.
  - inversion IHclos_trans1; inversion IHclos_trans2.
    eauto using gt_def, t_trans.
Qed.

Lemma gt_to_lt:
  forall f f',
  f > f' ->
  f' < f.
Proof.
  intros.
  destruct H.
  induction H.
  - auto using lt_def, t_step.
  - inversion IHclos_trans1; inversion IHclos_trans2.
    eauto using lt_def, t_trans.
Qed.

Lemma gt_lt_spec:
  forall f f',
  f < f' <-> f' > f.
Proof.
  intros.
  split; auto using gt_to_lt, lt_to_gt.
Qed.

Lemma le_to_ge:
  forall f f',
  f <= f' ->
  f' >= f.
Proof.
  intros.
  intuition.
  induction H0.
  - auto using rt_step.
  - auto using rt_refl.
  - eauto using rt_trans.
Qed.

Lemma lt_to_le:
  forall f f',
  f < f' ->
  f <= f'.
Proof.
  intros.
  intuition.
  induction H0.
  - auto using rt_step.
  - eauto using rt_trans.
Qed.

Lemma gt_to_ge:
  forall f f',
  f > f' ->
  f >= f'.
Proof.
  intros.
  intuition.
  induction H0.
  - auto using rt_step.
  - eauto using rt_trans.
Qed.

Lemma ge_to_le:
  forall f f',
  f >= f' ->
  f' <= f.
Proof.
  intros.
  intuition.
  induction H0.
  - auto using rt_step.
  - auto using rt_refl.
  - eauto using rt_trans.
Qed.

Lemma ge_le_spec:
  forall f f',
  f <= f' <-> f' >= f.
Proof.
  intros; split; auto using ge_to_le, le_to_ge.
Qed.

Lemma le_inv:
  forall f f',
  f <= f' ->
  f < f' \/ f = f'.
Proof.
  intros.
  intuition.
  induction H0.
  - intuition.
  - intuition.
  - destruct IHclos_refl_trans1, IHclos_refl_trans2.
    + left; intuition.
      eauto using t_trans.
    + subst.
      intuition.
    + subst; intuition.
    + subst; intuition.
Qed.

Lemma le_trans:
  forall f1 f2 f3,
  f1 <= f2 ->
  f2 <= f3 ->
  f1 <= f3.
Proof.
  intros.
  intuition.
  eauto using rt_trans.
Qed.

Lemma ge_inv:
  forall f f',
  f >= f' ->
  f > f' \/ f = f'.
Proof.
  intros.
  intuition.
  induction H0.
  - intuition.
  - intuition.
  - destruct IHclos_refl_trans1, IHclos_refl_trans2.
    + left; intuition.
      eauto using t_trans.
    + subst.
      intuition.
    + subst; intuition.
    + subst; intuition.
Qed.

Lemma sub_inv_cons_ready:
  forall f t l,
  Sub f (Node ((t, Ready) :: l)) ->
  Sub f (Node l).
Proof.
  intros.
  inversion H.
  eauto using sub_def, child_inv_cons_blocked_ready.
Qed.

Lemma sub_eq:
  forall f t l,
  Sub f (Node ((t, Blocked f) :: l)).
Proof.
  intros.
  eauto using sub_def, child_eq.
Qed.


Lemma lt_eq:
  forall (f:finish) (t:tid) (l:list l_task),
  f < (Node ((t,Blocked f)::l)).
Proof.
  intros.
  auto using lt_def, t_step, sub_eq.
Qed.

Lemma lt_trans:
  forall f1 f2 f3,
  f1 < f2 ->
  f2 < f3 ->
  f1 < f3.
Proof.
  intros; intuition.
  eauto using t_trans.
Qed.

(*
Lemma le_cons:
  forall f f' t l,
  f <= f' ->
  f <= Node ((t, Blocked f') :: l).
Proof.
  intros.
  intuition.
  inversion H0.
  - subst.
  apply rt_step.
  apply sub_def with (t).
  
    eauto using rt_step, rt_trans.
Qed.
*)
Require Import Coq.Relations.Operators_Properties.

Lemma lt_inv_cons_ready:
  forall f t l,
  f < (Node ((t, Ready) :: l)) ->
  f < (Node l).
Proof.
  intros.
  rewrite gt_lt_spec in *.
  destruct H.
  rewrite clos_trans_t1n_iff in H.
  inversion H.
  - subst.
    eauto using sub_inv_cons_ready, gt_def, t_step.
  - subst.
    apply gt_def.
    apply t_trans with (y).
    + eauto using sub_inv_cons_ready, t_step.
    + auto using clos_t1n_trans.
Qed.
(*
Section LT_IND.

Hypothesis P : finish -> Prop.
Hypothesis Hnil: P (Node nil).
Hypothesis Hcons: forall t l, P (Node l) -> P (Node ((t, Ready)::l)).
Hypothesis Htrans: forall f f', P f -> f < f' -> P f'.

Fixpoint lt_ind (f:finish) : P f :=
match f with
| Node l =>
    (fix aux (l:list l_task) : P (Node l) :=
    match l as x return P (Node x) with 
    | nil => Hnil
    | (t,Ready) :: l => Hcons t l (aux l)
    | (t, Blocked f') :: l => Htrans f' (Node ((t, Blocked f')::l)) (lt_ind f') (lt_eq f' t l)
    end) l
end.

End LT_IND.
*)

Lemma sub_absurd_nil:
  forall f,
  ~ Sub f (Node nil).
Proof.
  intros.
  intuition.
  inversion H.
  apply child_leaf_absurd in H0.
  assumption.
Qed.

Lemma lt_absurd_nil:
  forall f,
  ~ f < (Node nil).
Proof.
  intros.
  rewrite gt_lt_spec.
  intuition.
  rewrite clos_trans_tn1_iff in H0.
  induction H0.
  - apply sub_absurd_nil in H; assumption.
  - assumption.
Qed.

Lemma le_inv_nil:
  forall f,
  f <= Node nil ->
  f = Node nil.
Proof.
  intros.
  apply le_inv in H.
  destruct H.
  - apply lt_absurd_nil in H.
    inversion H.
  - assumption.
Qed.

Lemma sub_cons:
  forall f l p,
  Sub f (Node l) ->
  Sub f (Node (p :: l)).
Proof.
  intros.
  inversion H.
  eauto using sub_def, child_cons_perm.
Qed.

Lemma gt_cons:
  forall f l p,
  Node l > f  ->
  Node (p :: l) > f.
Proof.
  intros.
  inversion H; clear H.
  rewrite clos_trans_tn1_iff in H0.
  apply gt_def.
  induction H0.
  - auto using sub_cons, t_step.
  - eauto using t_trans, t_step.
Qed.

Lemma lt_cons:
  forall f l p,
  f < Node l ->
  f < Node (p :: l).
Proof.
  intros.
  rewrite gt_lt_spec in *.
  auto using gt_cons.
Qed.

Lemma sub_inv_cons:
  forall f p l,
  Sub f (Node (p :: l)) ->
  (snd p = Blocked f) \/ Sub f (Node l).
Proof.
  intros.
  inversion H.
  destruct p as  (t', a).
  destruct H0.
  destruct H0.
  * inversion H0.
    intuition.
  * right.
    apply sub_def with (t).
    apply child_def.
    simpl.
    auto.
Qed.
(*
Lemma gt_inv_cons:
  forall f p l,
  Node (p :: l) > f  ->
  (snd p = Blocked f) \/ (Node l) > f.
Proof.
  intros.
  inversion H.
  rewrite clos_trans_tn1_iff in H0.
  induction H0.
  - apply sub_inv_cons in H0.
    destruct H0.
    + intuition.
    + right.
      auto using gt_def, t_step.
  - assert (Hx : Node (p::l) > y). {
      auto using gt_def, clos_tn1_trans.
    }
    apply IHclos_trans_n1 in Hx; clear H1 IHclos_trans_n1.
    destruct Hx.
    + intuition.
    + 
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
*)

Inductive Any (P: finish -> Prop) (f:finish) : Prop :=
  any_def:
    forall f',
    f' <= f ->
    P f' ->
    Any P f.

Lemma any_cons:
  forall P f t l,
  Any P f ->
  Any P (Node ((t,(Blocked f))::l)).
Proof.
  intros.
  inversion H.
  apply any_def with (f').
  - apply le_inv in H0.
    destruct H0.
    + apply lt_to_le.
      remember (Node _) as y.
      assert (f <  y). {
        subst.
        eauto using lt_eq.
      }
      eauto using lt_trans.
    + subst.
      apply lt_to_le.
      auto using lt_eq.
  - assumption.
Qed.

Lemma any_cons_rhs:
  forall (P:finish->Prop) p l,
  Any P (Node l) ->
  ( (P (Node l)) ->  P (Node (p::l))) ->
  Any P (Node (p::l)).
Proof.
  intros.
  inversion H.
  apply le_inv in H1.
  destruct H1.
  - eauto using any_def, lt_to_le, lt_cons.
  - subst.
    apply any_def with (Node (p :: l)); auto.
    intuition.
Qed.

Lemma any_inv_nil:
  forall P,
  Any P (Node nil) ->
  P (Node nil).
Proof.
  intros.
  inversion H.
  apply le_inv_nil in H0.
  subst; assumption.
Qed.
(*
Lemma any_inv_cons:
  forall P p l,
  Any P (Node (p :: l)) ->
  (exists f',  f' < Node (p :: l) /\ P f') \/ False.
(*  (P (Node (p::l))) \/
  (exists f, snd p = Blocked f /\ Any P f) \/ Any P (Node l).*)
Proof.
  intros.
  inversion H.
  apply le_inv in H0.
  destruct H0.
  - left; exists f'; intuition.
  - subst.
    right.
  - intuition.
  - right.
    apply lt_inv_cons  in H1.
    destruct H1.
    + left.
      exists f'.
      intuition.
    + right.
      eauto using any_parent.
Qed.
*)
Inductive Lookup (t:tid) (a:task) (f:finish) : Prop :=
  lookup_def:
    forall f',
    Child t a f' ->
    f' <= f ->
    Lookup t a f.

Lemma lookup_leaf_absurd:
  forall t f,
  Lookup t f (Node nil) -> False.
Proof.
  intros.
  inversion H; subst.
  inversion H0.
  apply le_inv_nil in H1; subst.
  eauto using child_leaf_absurd.
Qed.

Lemma lookup_le:
  forall t a f f',
  Lookup t a f ->
  f <= f' ->
  Lookup t a f'.
Proof.
  intros.
  inversion H.
  eauto using lookup_def, le_trans.
Qed.
(*
Lemma lookup_cons_rhs:
  forall t a p l,
  Lookup t a (Node l) ->
  Lookup t a (Node (p :: l)).
Proof.
  intros.
  inversion H; clear H.
  auto using lookup_def, any_cons_rhs, child_cons.
Qed.

Lemma lookup_eq:
  forall t a l,
  Lookup t a (Node ((t, a) :: l)).
Proof.
  intros.
  eauto using lookup_def, any_ok, child_eq.
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
      eauto using child_def, lookup_def, any_ok.
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
      eauto using lookup_def, any_parent.
Qed.
*)

Inductive Registered (t:tid) (f:finish) : Prop :=
  registered_def:
    forall a,
    Child t a f ->
    Registered t f.

Inductive In (t:tid) (f:finish) : Prop :=
  in_def:
    forall f',
    Registered t f' ->
    f' <= f ->
    In t f.

(*
Lemma in_child:
  forall t a f,
  Child t a f ->
  In t f.
Proof.
  intros.
  eauto using in_def, lookup_def, any_ok.
Qed.
*)
(*
Lemma in_trans:
  forall t f f',
  In t f' ->
  f' < f ->
  In t f.
Proof.
  intros.
  inversion H.
  inversion H1.
  eauto using in_def, lookup_def, any_parent.
Qed.

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
*)
Module Semantics.

(** Add task [t] to finish [f]. *)

Fixpoint remove_child (l:list l_task) (t:tid) :=
  match l with
  | (t', f) :: l => 
    if TID.eq_dec t t'
    then remove_child l t
    else (t',f) :: remove_child l t
  | nil => nil
  end.

Definition remove (f:finish) (t:tid) :=
  match f with
  | Node l => Node (remove_child l t)
  end.

Definition put (f:finish) (p:l_task) : finish :=
  Node (p::(get_tasks (remove f (fst p) ))).

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
Import Semantics.
Notation "[]" := (Node nil) : finish_scope.
Notation "[ p ]" :=  (Node ( (p  :: nil ) )) :  finish_scope.
Infix " <| " :=  (fun (t:tid) (f:finish) => (t, Blocked f)) (at level 50, left associativity)  :  finish_scope.
Notation "! t" :=  (t, Ready) (at level 60)   :  finish_scope.
Notation " [ x | .. | y ] " := (Node ((cons x .. (cons y nil) ..) )) : finish_scope.
Infix " |+ " :=  (put) (at level 60, right associativity)  :  finish_scope.
Infix " |- " :=  (remove) (at level 60, right associativity)  :  finish_scope.

End FinishNotations.