Set Implicit Arguments.

Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.Arith.Peano_dec.

Require Import Aniceto.Map.

Require Coq.FSets.FMapFacts.

Inductive node := make : nat -> node.

Definition node_id r := match r with | make n => n end.

Definition node_first := make 0.

Definition node_next m := make (S (node_id m)).

Module NODE <: UsualOrderedType.
  Definition t := node.
  Definition eq := @eq node.
  Definition lt x y := lt (node_id x) (node_id y).
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Lemma lt_trans: forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros.
    unfold lt in *.
    destruct x, y, z.
    simpl in *.
    omega.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt in *.
    intros.
    destruct x, y.
    simpl in *.
    unfold not; intros.
    inversion H0.
    subst.
    apply Lt.lt_irrefl in H.
    inversion H.
  Qed.

  Require Import Coq.Arith.Compare_dec.
  Lemma compare:
    forall x y, Compare lt eq x y.
  Proof.
    intros.
    destruct x, y.
    destruct (Nat_as_OT.compare n n0);
    eauto using LT, GT.
    apply EQ.
    unfold Nat_as_OT.eq in *.
    subst.
    intuition.
  Defined.

  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros.
    unfold eq.
    destruct x, y.
    destruct (eq_nat_dec n n0).
    - subst; eauto.
    - right.
      unfold not.
      intros.
      contradiction n1.
      inversion H; auto.
  Defined.
End NODE.


Module MN := FMapAVL.Make NODE.
Module MN_Facts := FMapFacts.Facts MN.
Module MN_Props := FMapFacts.Properties MN.
Module MN_Extra := MapUtil MN.
Module SN := FSetAVL.Make NODE.
Definition set_node := SN.t.

Lemma node_eq_rw:
  forall (k k':node), NODE.eq k k' <-> k = k'.
Proof.
  intros.
  auto with *.
Qed.

Lemma node_eq_dec:
  forall x y : node, {x = y} + {x <> y}.
Proof.
  auto using node_eq_rw, NODE.eq_dec.
Qed.

Section NotIn.
  Variable elt:Type.

  Lemma node_lt_irrefl:
    forall x : node, ~ NODE.lt x x.
  Proof.
    unfold not; intros.
    apply NODE.lt_not_eq in H.
    contradiction H.
    apply NODE.eq_refl.
  Qed.

  Let lt_next:
    forall x, NODE.lt x (node_next x).
  Proof.
    intros.
    destruct x.
    unfold node_next, node_id, NODE.lt.
    simpl.
    auto.
  Qed.

  Let node_impl_eq:
    forall k k' : node, k = k' -> k = k'.
  Proof.
    auto.
  Qed.

  Definition supremum {elt:Type} := @MN_Extra.supremum elt node_first node_next NODE.lt NODE.compare.

  Theorem find_not_in:
    forall (m: MN.t elt),
    ~ MN.In (supremum m) m.
  Proof.
    intros.
    eauto using MN_Extra.find_not_in, NODE.lt_trans, node_lt_irrefl.
  Qed.

End NotIn.

Section Props.
  Require Bijection.

  Variable A:Type.

  Definition MapsTo (x:A) (n:node) (vs:list A) := Bijection.MapsTo x (node_id n) vs.

  Definition fresh (vs:list A) := make (length vs).

  Definition Node x (vs:list A) := Bijection.Index (node_id x) vs.

  Definition TaskOf (n:node) (x:A) (vs:list A) := Bijection.IndexOf x (node_id n) vs.

  Lemma maps_to_fun_1:
    forall x y n (vs:list A),
    MapsTo x n vs ->
    MapsTo y n vs ->
    y = x.
  Proof.
    unfold MapsTo; eauto using Bijection.maps_to_fun_1.
  Qed.

  Lemma maps_to_fun_2:
    forall vs (x:A) n n',
    MapsTo x n vs ->
    MapsTo x n' vs ->
    n' = n.
  Proof.
    intros.
    unfold MapsTo in *.
    destruct n as (n), n' as (n').
    simpl in *.
    eauto using Bijection.maps_to_fun_2.
  Qed.

  Lemma task_of_fun_2:
    forall vs (x y:A) n,
    TaskOf n x vs ->
    TaskOf n y vs ->
    x = y.
  Proof.
    unfold TaskOf; intros.
    eauto using Bijection.index_of_fun_2.
  Qed.

  Lemma maps_to_inv_eq:
    forall (x:A) n vs,
    MapsTo x n (x :: vs) ->
    n = fresh vs.
  Proof.
    intros.
    unfold MapsTo, fresh in *.
    destruct n as (n).
    simpl in *.
    eauto using Bijection.maps_to_inv_eq.
  Qed.

  Lemma task_of_inv_key:
    forall (x:A) y vs,
    TaskOf (fresh vs) x (y :: vs) ->
    x = y.
  Proof.
    intros.
    unfold TaskOf, fresh in *; simpl in *.
    eauto using Bijection.index_of_inv_key.
  Qed.

  Lemma maps_to_neq:
    forall (x:A) y vs n,
    x <> y ->
    MapsTo y n (x :: vs) ->
    MapsTo y n vs.
  Proof.
    intros.
    destruct n as (n).
    unfold MapsTo in *; simpl in *.
    eauto using Bijection.maps_to_neq.
  Qed.

  Lemma node_eq:
    forall x vs,
    Node (fresh vs) (x::vs).
  Proof.
    intros.
    unfold Node, fresh in *.
    eauto using Bijection.index_eq.
  Qed.

  Lemma maps_to_eq:
    forall x vs,
    MapsTo x (fresh vs) (x::vs).
  Proof.
    intros.
    unfold MapsTo, fresh.
    simpl.
    auto using Bijection.maps_to_eq.
  Qed.

  Lemma maps_to_cons:
    forall x vs y n,
    x <> y ->
    MapsTo x n vs ->
    MapsTo x n (y :: vs).
  Proof.
    unfold MapsTo, fresh.
    auto using Bijection.maps_to_cons.
  Qed.

  Lemma maps_to_lt:
    forall (x:A) n vs,
    MapsTo x n vs ->
    NODE.lt n (fresh vs).
  Proof.
    intros.
    unfold NODE.lt, fresh, MapsTo in *.
    destruct n; simpl in *.
    eauto using Bijection.maps_to_lt.
  Qed.

  Lemma node_lt:
    forall n vs,
    Node n vs ->
    NODE.lt n (fresh vs).
  Proof.
    intros.
    destruct n.
    unfold Node, fresh, NODE.lt in *.
    eauto using Bijection.index_lt.
  Qed.

  Lemma lt_to_node:
    forall n vs,
    NODE.lt n (fresh vs) ->
    Node n vs.
  Proof.
    unfold NODE.lt, Node, fresh.
    auto using Bijection.lt_to_index.
  Qed.

  Lemma node_cons:
    forall n vs x,
    Node n vs ->
    Node n (x::vs).
  Proof.
    unfold NODE.lt, Node, fresh.
    auto using Bijection.index_cons.
  Qed.

  Lemma maps_to_absurd_fresh:
    forall (x:A) vs,
    ~ MapsTo x (fresh vs) vs.
  Proof.
    unfold fresh, MapsTo.
    eauto using Bijection.maps_to_absurd_length.
  Qed.

  Lemma task_of_absurd_fresh:
    forall (x:A) vs,
    ~ TaskOf (fresh vs) x vs.
  Proof.
    unfold fresh, TaskOf.
    eauto using Bijection.index_of_absurd_length.
  Qed.

  Lemma node_absurd_fresh:
    forall vs,
    ~ Node (fresh vs) vs.
  Proof.
    intros.
    unfold Node.
    simpl.
    apply Bijection.index_absurd_length.
  Qed.

  Lemma maps_to_to_node:
    forall (x:A) n vs,
    MapsTo x n vs ->
    Node n vs.
  Proof.
    unfold MapsTo, Node.
    intros.
    eauto using Bijection.maps_to_to_index.
  Qed.

  Lemma maps_to_to_task_of:
    forall (x:A) n vs,
    MapsTo x n vs ->
    TaskOf n x vs.
  Proof.
    unfold MapsTo, TaskOf.
    eauto using Bijection.maps_to_to_index_of.
  Qed.

End Props.

Section MoreProps.

  Lemma maps_to_length_rw:
    forall {A:Type} {B:Type} (vs:list A) (vs':list B),
    length vs = length vs' ->
    fresh vs = fresh vs'.
  Proof.
    intros.
    unfold fresh.
    auto.
  Qed.

  Let length_node_id_rw:
    forall {A} (vs:list A) n,
    length vs = node_id n ->
    fresh vs = n.
  Proof.
    unfold fresh.
    intros.
    destruct n; auto.
  Qed.

  Lemma maps_to_to_in:
    forall {A} x n (vs:list A),
    MapsTo x n vs ->
    List.In x vs.
  Proof.
    unfold MapsTo; eauto using Bijection.maps_to_to_in.
  Qed.

  Lemma maps_to_inv:
    forall {A} x (y:A) n vs,
    MapsTo x n (y :: vs) ->
    (x = y /\ n = fresh vs) \/ (x <> y /\ MapsTo x n vs).
  Proof.
    intros.
    inversion H; subst.
    - apply length_node_id_rw in H1.
      subst.
      intuition.
    - intuition.
  Qed.

  Lemma task_of_inv:
    forall {A} x (y:A) n vs,
    TaskOf n x (y :: vs) ->
    (x = y /\ n = fresh vs) \/ TaskOf n x vs.
  Proof.
    intros.
    inversion H; subst.
    - apply length_node_id_rw in H1.
      subst.
      intuition.
    - intuition.
  Qed.

  Lemma node_to_task_of:
    forall {A} n (vs:list A),
    Node n vs ->
    exists x, TaskOf n x vs.
  Proof.
    intros.
    destruct H as (x, H).
    eauto.
  Qed.

  Lemma task_of_to_node:
    forall {A} x n (vs:list A),
    TaskOf n x vs ->
    Node n vs.
  Proof.
    intros.
    unfold Node, TaskOf in *.
    eauto using Bijection.index_def.
  Qed.

  Lemma task_of_to_in:
    forall {A} x n (vs:list A),
    TaskOf n x vs ->
    List.In x vs.
  Proof.
    unfold TaskOf; eauto using Bijection.index_of_to_in.
  Qed.

  Lemma task_of_cons:
    forall {A} x y n (vs:list A),
    TaskOf n x vs ->
    TaskOf n x (y::vs).
  Proof.
    unfold TaskOf; eauto using Bijection.index_of_cons.
  Qed.

  Lemma node_inv:
    forall {A} (x:A) n vs,
    Node n (x :: vs) ->
    n = fresh vs \/ Node n vs.
  Proof.
    intros.
    apply node_to_task_of in H.
    destruct H as (y, H).
    apply task_of_inv in H.
    destruct H as [(?,?)|?].
    - subst.
      intuition.
    - eauto using task_of_to_node.
  Qed.

  Lemma task_of_inv_eq:
    forall {A} x (y:A) vs,
    TaskOf (fresh vs) x (y :: vs) ->
    x = y.
  Proof.
    unfold TaskOf, fresh; eauto using Bijection.index_of_inv_key.
  Qed.

  Lemma task_of_eq:
    forall {A} (x:A) vs,
    TaskOf (fresh vs) x (x :: vs).
  Proof.
    unfold TaskOf, fresh; eauto using Bijection.index_of_eq.
  Qed.

  Section Lookup.
    Variable A:Type.
    Variable eq_dec: forall (x y:A), {x = y} + {x <> y}.

    Lemma in_to_maps_to:
      forall (x:A) vs,
      List.In x vs ->
      exists n, MapsTo x n vs.
    Proof.
      intros.
      unfold MapsTo.
      apply Bijection.in_to_maps_to in H; auto.
      destruct H as (n, H).
      exists (make n).
      auto.
    Qed.

    Definition lookup (x:A) xs :=
    match Bijection.lookup eq_dec x xs with
    | Some n => Some (make n)
    | _ => None
    end.

    Lemma lookup_some:
      forall xs x n,
      lookup x xs = Some n ->
      MapsTo x n xs.
    Proof.
      unfold lookup.
      intros.
      remember (Bijection.lookup _ _ _).
      symmetry in Heqo.
      destruct o; inversion H; subst; clear H.
      apply Bijection.lookup_some in Heqo.
      auto.
    Qed.

    Lemma lookup_none:
      forall xs x,
      lookup x xs = None ->
      ~ List.In x xs.
    Proof.
      unfold lookup; intros.
      remember (Bijection.lookup _ _ _).
      symmetry in Heqo.
      destruct o; inversion H; subst; clear H.
      apply Bijection.lookup_none in Heqo.
      assumption.
    Qed.
  End Lookup.

End MoreProps.

  Ltac simpl_node := 
  repeat match goal with
  | [ H1: MapsTo ?x ?n ?v, H2: MapsTo ?y ?n ?v |- _ ] =>
      let H' := fresh "H" in
      assert (H': y = x) by eauto using maps_to_fun_1;
      rewrite H' in *;
      clear H' H2
  | [ H1: MapsTo ?x ?n1 ?v, H2: MapsTo ?x ?n2 ?v |- _ ] =>
      let H' := fresh "H" in
      assert (H': n1 = n2) by eauto using maps_to_fun_2;
      rewrite H' in *;
      clear H' H2
  | [ H: MapsTo _ (fresh ?vs) ?vs |- _ ] =>
      apply maps_to_absurd_fresh in H;
      contradiction
  | [ H: Node (fresh ?vs) ?vs |- _ ] =>
      apply node_absurd_fresh in H;
      contradiction
  | [ H: MapsTo ?x (fresh ?vs) (?x :: ?vs) |- _ ] => clear H
  | [ H1: MapsTo ?x _ (?y :: _), H2: ?x <> ?y |- _ ] => apply maps_to_neq in H1; auto
  | [ H1: MapsTo ?x _ (?y :: _), H2: ?y <> ?x |- _ ] => apply maps_to_neq in H1; auto
  | [ H: MapsTo ?x _ (?x :: _) |- _ ] => apply maps_to_inv_eq in H; rewrite H in *; clear H
  | [ H: TaskOf (fresh ?vs) _ ?vs |- _ ] =>
      apply task_of_absurd_fresh in H;
      contradiction
  | [ H: TaskOf (fresh ?vs) ?x (?y :: ?vs) |- _ ] => apply task_of_inv_eq in H; subst
  | [ H1: TaskOf ?n ?x ?v, H2: TaskOf ?n ?y ?v |- _ ] =>
      let H' := fresh "H" in
      assert (H': y = x) by eauto using task_of_fun_2;
      rewrite H' in *;
      clear H' H2
  end.
