Require Import HJ.Vars.

Require Import Coq.Lists.SetoidList.
Require Import Coq.Relations.Operators_Properties.

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

Inductive Child (p:l_task) (f:finish) : Prop := 
  child_def:
    List.In p (get_tasks f) ->
    Child p f.

Lemma child_eq:
  forall p l,
  Child p (Node (p :: l)).
Proof.
  intros.
  eapply child_def.
  simpl.
  intuition.
Qed.

Lemma child_cons:
  forall p l p',
  Child p (Node l) ->
  Child p (Node (p' :: l)).
Proof.
  intros.
  eapply child_def.
  destruct H.
  simpl in *.
  intuition.
Qed.

Lemma child_absurd_nil:
  forall p,
  ~ Child p (Node nil).
Proof.
  intros.
  intuition.
Qed.

Lemma child_inv_cons:
  forall p p' l,
  Child p (Node (p' :: l)) ->
  p' = p \/ Child p (Node l).
Proof.
  intros.
  inversion H.
  inversion H0.
  - inversion H1; intuition.
  - right.
    apply child_def; simpl; assumption.
Qed.

Lemma child_inv_cons_nil:
  forall p p',
  Child p (Node (p' :: nil)) ->
  p' = p.
Proof.
  intros.
  inversion H.
  simpl in *.
  destruct H0; (inversion H0; intuition).
Qed.

Lemma child_to_ina:
  forall p l,
  Child p (Node l) -> 
  InA (Map_TID.eq_key (elt:=task)) p l.
Proof.
  intros.
  destruct H.
  apply InA_alt.
  exists p.
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
  forall p p' l,
  p <> p' ->
  Child p (Node (p' :: l)) ->
  Child p (Node l).
Proof.
  intros.
  inversion H0.
  destruct H1.
  - (* absurd *)
    subst.
    contradiction H; trivial.
  - auto using child_def.
Qed.

Lemma child_inv_cons_neq:
  forall p p' l,
  p' <> p ->
  Child p (Node (p' :: l)) ->
  Child p (Node l).
Proof.
  intros.
  inversion H0.
  apply child_def.
  simpl in *.
  destruct H1.
  - contradiction H; assumption.
  - assumption.
Qed.

Inductive Leaf (t:tid) (f:finish) : Prop :=
  leaf_def:
    Child (t, Ready) f ->
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

Lemma leaf_eq:
  forall t l,
  Leaf t (Node ((t,Ready)::l)).
Proof.
  intros.
  auto using leaf_def, child_eq.
Qed.

Inductive Sub (f:finish) (f':finish) : Prop :=
  sub_def:
    forall t,
    Child (t, (Blocked f)) f' ->
    Sub f f'.

Module Notations.
  Notation "[]" := (Node nil) : finish_scope.
  Notation "[ p ]" :=  (Node ( (p  :: nil ) )) :  finish_scope.
  Notation " t <| f" :=  ((t, Blocked f)) (at level 50, left associativity)  :  finish_scope.
  Notation "! t" :=  (t, Ready) (at level 60)   :  finish_scope.
  Notation " [ x | .. | y ] " := (Node ((cons x .. (cons y nil) ..) )) : finish_scope.
End Notations.