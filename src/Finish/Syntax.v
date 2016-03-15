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

Lemma get_tasks_rw:
  forall f,
  Node (get_tasks f) = f.
Proof.
  intros.
  destruct f.
  simpl.
  trivial.
Qed.

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

Inductive Registered (t:tid) (f:finish) : Prop :=
  registered_def:
    forall a,
    Child (t, a) f ->
    Registered t f.

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

Lemma registered_cons:
  forall t l p,
  Registered t (Node l) ->
  Registered t (Node (p::l)).
Proof.
  intros.
  inversion H.
  eauto using child_cons, registered_def.
Qed.

Lemma registered_eq:
  forall t l a,
  Registered t (Node ((t,a)::l)).
Proof.
  intros.
  eauto using registered_def, child_eq.
Qed.

Lemma registered_absurd_nil:
  forall t,
  ~ Registered t (Node nil).
Proof.
  intros.
  intuition.
  inversion H.
  apply child_absurd_nil in H0.
  assumption.
Qed.

Lemma registered_inv_cons:
  forall t t' a l,
  Registered t (Node ((t', a) :: l)) ->
  t = t' \/ Registered t (Node l).
Proof.
  intros.
  inversion H.
  apply child_inv_cons in H0.
  destruct H0 as [Hx|?].
  - inversion Hx; subst; clear Hx.
    intuition.
  - eauto using registered_def.
Qed.

Lemma ina_eq_key_subst {T}:
  forall t f f' l, 
  InA (Map_TID.eq_key (elt:=T)) (t, f) l ->
  InA (Map_TID.eq_key (elt:=T)) (t, f') l.
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

Lemma ina_to_registered:
  forall t a l,
  InA (Map_TID.eq_key (elt:=task)) (t,a) l ->
  Registered t (Node l).
Proof.
  intros.
  apply InA_alt in H.
  destruct H as ((t', a'), (He, Hi)).
  apply Map_TID_Extra.eq_key_unfold in He; auto.
  subst.
  eauto using registered_def, child_def.
Qed.

  Lemma not_in_a_to_not_registered:
    forall t a l,
    ~ InA (Map_TID.eq_key (elt:=task)) (t, a) l ->
    ~ Registered t (Node l).
  Proof.
    intros.
    unfold not; intros.
    inversion H0.
    apply child_to_ina in H1.
    contradiction H.
    eauto using ina_eq_key_subst.
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

Let eq_key_dec:
  forall x y,
  { Map_TID.eq_key (elt:=task) x y } + { ~ Map_TID.eq_key (elt:=task) x y}.
Proof.
  intros.
  destruct (TID.eq_dec (fst x) (fst y)). {
    left.
    destruct x, y.
    simpl in *; subst.
    apply Map_TID_Extra.eq_key_unfold.
    trivial.
  }
  destruct x as (x1,x2).
  destruct y as (y1,y2).
  simpl in *.
  right.
  intuition.
Qed.

Lemma registered_dec:
  forall t f,
  { Registered t f } + {~ Registered t f}.
Proof.
  intros.
  destruct (InA_dec eq_key_dec (t,Ready) (get_tasks f)).
  - apply InA_alt in i.
    left.
    destruct i as ((k,v), (?,?)).
    apply Map_TID_Extra.eq_key_unfold in H.
    subst.
    eauto using registered_def, child_def.
  - right.
    apply not_in_a_to_not_registered in n.
    rewrite get_tasks_rw in *.
    trivial.
Qed.

Section FINDA.
  Variable A B : Type.
(*
  Variable eqA : A -> A -> Prop.
  Hypothesis eqA_equiv : Equivalence eqA.
  Hypothesis eqA_dec : forall x y : A, {eqA x y}+{~(eqA x y)}.
*)
(*
  Variable f: A -> A -> bool.
  Hypothesis f_spec:
    forall x y,
    f x y = true ->
    eqA x y.
*)
  Lemma find_a_some:
    forall (f:A->bool) l e,
    @findA A B f l = Some e ->
    exists k, f k = true /\ List.In (k, e) l.
  Proof.
    intros.
    induction l.
    - inversion H.
    - simpl in *.
      destruct a as (x,y).
      remember (f x).
      symmetry in Heqb.
      destruct b.
      + inversion H.
        subst.
        exists x.
        intuition.
      + apply IHl in H; clear IHl.
        destruct H as  (k, (He, Hi)).
        exists k.
        intuition.
  Qed.

  Lemma find_a_none:
    forall (f:A->bool) l e,
    @findA A B f l = None ->
    forall k,
    List.In (k, e) l ->
    f k = false.
  Proof.
    intros.
    induction l. {
      inversion H0.
    }
    inversion H0.
    - subst.
      simpl in *.
      remember (f k).
      destruct b; auto.
      inversion H.
    - destruct a as (k', e').
      simpl in H.
      remember (f k').
      destruct b. {
       inversion H.
      }
      eauto.
  Qed.

End FINDA.

Require Import Aniceto.EqDec.

  Let tid_eqb x y := if TID.eq_dec x y then true else false.

  Let tid_eqb_true:
    forall t t',
    tid_eqb t t' = true ->
    t = t'.
  Proof.
    intros.
    unfold tid_eqb in *.
    destruct TID.eq_dec; auto.
    inversion H.
  Qed.

  Let tid_eqb_false:
    forall t t',
    tid_eqb t t' = false ->
    t <> t'.
  Proof.
    intros.
    unfold tid_eqb in *.
    destruct TID.eq_dec; auto.
    inversion H.
  Qed.

  Require Import Coq.Lists.SetoidList.

  Definition lookup t f : option task :=
    match f with
    Node l =>
      match findA (tid_eqb t) l with
      | Some a => Some a
      | None => None
      end
    end.

  Lemma lookup_to_child:
    forall t f a,
    lookup t f = Some a ->
    Child (t,a) f.
  Proof.
    intros.
    destruct f.
    simpl in *.
    remember (findA _ _).
    symmetry in Heqo.
    destruct o.
    - inversion H.
      subst.
      apply find_a_some in Heqo.
      destruct Heqo as (t', (Hf, Hin)).
      apply tid_eqb_true in Hf.
      subst.
      auto using child_def.
    - inversion H.
  Qed.

  Lemma registered_to_lookup:
    forall t f,
    Registered t f ->
    exists a, lookup t f = Some a.
  Proof.
    intros.
    remember (lookup t f).
    destruct o; eauto.
    destruct f.
    simpl in *.
    remember (findA _ _).
    destruct o; eauto.
    symmetry in Heqo0.
    inversion H.
    apply find_a_none with (k:=t) (e:=a) in Heqo0.
    - apply tid_eqb_false in Heqo0.
      contradiction Heqo0.
      trivial.
    - inversion H0.
      auto.
  Qed.

  Lemma lookup_none_to_not_registered:
    forall t f,
    lookup t f = None ->
    ~ Registered t f.
  Proof.
    unfold not; intros.
    inversion H0.
    apply registered_to_lookup in H0.
    destruct H0 as (a', Hl).
    rewrite H in Hl.
    inversion Hl.
  Qed.

  Definition ChildOf t f := { a : task | Child (t,a) f }.

  Definition Unregistered t f := { _:unit | ~ Registered t f }.

  (** Dependently-typed lookup *)

  Definition lookup_ex:
    forall t f,
    (ChildOf t f) + (Unregistered t f).
  Proof.
    intros.
    remember (lookup t f).
    symmetry in Heqo.
    destruct o as [a|].
    - apply lookup_to_child in Heqo.
      left.
      apply exist with (x:=a); auto.
    - right.
      apply lookup_none_to_not_registered in Heqo.
      unfold Unregistered.
      eapply exist.
      refine tt.
      auto.
  Defined.

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