Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.

Require Import Aniceto.List.

Require Import HJ.Finish.Lang.

Section Find.
  Variable check: finish -> bool.
  
  Fixpoint get_children (f:finish) : list finish :=
  match f with
  | Node l =>
    (fix aux (l:list l_task) :=
      match l with
      | ((t, Blocked f') :: l) => f' :: (aux l)
      | (t, Ready) :: l => aux l
      | nil => nil
      end) l
  end.

  Lemma get_children_rw_cons_ready:
    forall t l,
    get_children (Node ((t, Ready) :: l)) = get_children (Node l).
  Proof.
    intros.
    simpl.
    auto.
  Qed.

  Lemma get_children_rw_cons_blocked:
    forall t f l,
    get_children (Node ((t, Blocked f) :: l)) = f :: get_children (Node l).
  Proof.
    intros.
    simpl.
    auto.
  Qed.

  Fixpoint size (f:finish) := 
  S (
  match f with
  | Node l =>
    (fix aux (l:list l_task) :=
      match l with
      | cons (t, Blocked f') l => S (size f') + aux l
      | cons (t, Ready) l => S (aux l)
      | nil => 0
      end
    ) l
  end).

  Lemma size_rw_cons_ready:
    forall t l,
    size (Node ((t, Ready) :: l)) = S (size (Node l)).
  Proof.
    intros.
    simpl.
    auto.
  Qed.

  Lemma size_rw_cons_blocked:
    forall t f l,
    size (Node ((t, Blocked f) :: l)) = S (size f) + size (Node l).
  Proof.
    intros; simpl; auto.
  Qed.

  Definition l_size (l:list finish) : nat := summation size l.

  Definition is_nil {A} (l:list A) : bool :=
  match l with
  | nil => true
  | _ => false
  end.

  Let summation_size_get_children:
    forall f,
    (summation size (get_children f) < size f) % nat.
  Proof.
    intros.
    induction f using finish_ind_strong.
    - compute. auto.
    - rewrite get_children_rw_cons_ready.
      rewrite size_rw_cons_ready.
      auto with *.
    - rewrite get_children_rw_cons_blocked.
      rewrite summation_rw_cons.
      rewrite size_rw_cons_blocked.
      auto with *.
  Qed.

  Let summation_flat_map:
    forall l,
    summation size (flat_map get_children l) <= summation size l.
  Proof.
    induction l.
    { auto. }
    simpl.
    rewrite summation_rw_cons.
    rewrite summation_rw_app.
    assert (summation size (get_children a) < size a) by auto using summation_size_get_children.
    auto with *.
  Qed.

  Lemma l_size_children_not_nil:
    forall l,
    is_nil (flat_map get_children l) = false ->
    l_size (flat_map get_children l) < l_size l.
  Proof.
    intros.
    induction l.
    { inversion H. }
    simpl.
    simpl.
    unfold l_size.
    rewrite summation_rw_cons.
    rewrite summation_rw_app.
    assert (summation size (get_children a) < size a) by auto using summation_size_get_children.
    assert (summation size (flat_map get_children l) <= summation size l) by auto using summation_flat_map.
    auto with *.
  Qed.

  (** The general-purpose breadth-first search function. *)
  Function find_generic (l:list finish) { measure l_size l } : option finish :=
  match (List.find check l) with
  | Some x => Some x
  | None =>
    let frontier := flat_map get_children l in
    if is_nil frontier then None else find_generic frontier
  end.
  Proof.
    intros.
    auto using l_size_children_not_nil.
  Qed.
  
  Lemma flat_map_get_children_rw_cons_ready:
    forall t l1 l2,
    flat_map get_children (Node ((t, Ready) :: l1) :: l2) =
    flat_map get_children (Node l1 :: l2).
  Proof.
    intros.
    simpl.
    trivial.
  Qed.
    
  (** A wrapper around [find_generic] that retrieves *)
  Definition find (f:finish) := find_generic (f::nil).

  Lemma find_generic_impl_check:
    forall l f,
    find_generic l = Some f ->
    check f = true.
  Proof.
    intros.
    functional induction (find_generic l).
    - inversion H; subst; clear H.
      induction l.
      + inversion e.
      + simpl in e.
        remember (check a).
        destruct b.
        * inversion e; subst; auto.
        * auto.
    - inversion H.
    - auto.
  Qed.
  
  Lemma find_impl_check:
    forall f f',
    find f = Some f' ->
    check f' = true.
  Proof.
    intros.
    eauto using find_generic_impl_check.
  Qed.

  Lemma find_generic_nil:
    find_generic nil = None.
  Proof.
    rewrite find_generic_equation.
    auto.
  Qed.

  Import FinishNotations.
  Local Open Scope finish_scope.
  
  Lemma in_get_children_lt:
    forall y x,
    List.In y (get_children x) ->
    y < x.
  Proof.
    intros.
    induction x using finish_ind_strong.
    - simpl in H.
      inversion H.
    - rewrite get_children_rw_cons_ready in *.
      auto using lt_cons.
    - destruct H.
      + subst.
        auto using lt_eq.
      + auto using lt_cons.
  Qed.

  Lemma forall_get_children_lt:
    forall f,
    Forall (fun f'0 : finish => f'0 < f) (get_children f).
  Proof.
    intros.
    apply Forall_forall.
    intros.
    auto using in_get_children_lt.
  Qed.

  Lemma forall_lt_flat_map_get_children:
    forall f l,
    Forall (fun f' => f' < f) l ->
    Forall (fun f' => f' < f) (flat_map get_children l).
  Proof.
    intros.
    rewrite Forall_forall in *.
    intros.
    apply in_flat_map in H0.
    destruct H0 as (y, (Hin, Hg)).
    apply in_get_children_lt in Hg.
    apply H in Hin.
    eauto using lt_trans.
  Qed.

  Lemma find_generic_impl_lt:
    forall f l f',
    Forall (fun f' => f' < f) l ->
    find_generic l = Some f' ->
    f' < f.
  Proof.
    intros.
    functional induction (find_generic l).
    - inversion H0; subst; clear H0.
      apply find_some_spec in e.
      destruct e as (Hx, _).
      rewrite Forall_forall in H.
      auto.
    - inversion H0.
    - auto using forall_lt_flat_map_get_children.
  Qed.

  Lemma find_generic_contract:
    forall t l1 l2 f,
    find_generic (Node ((t, Ready) :: l1) :: l2) = Some f ->
    check (Node ((t, Ready) :: l1)) = false ->
    check (Node l1) = false ->
    find_generic (Node l1 :: l2) = Some f.
  Proof.
    intros.
    rewrite find_generic_equation in *.
    rewrite flat_map_get_children_rw_cons_ready in H.
    simpl in *.
    rewrite H1.
    rewrite H0 in H.
    trivial.
  Qed.

  Lemma find_spec_lt:
    forall f f',
    find f = Some f' ->
    check f = false ->
    f' < f /\ check f' = true.
  Proof.
    intros.
    split.
    - unfold find in *.
      rewrite find_generic_equation in H.
      simpl in H.
      rewrite H0 in *.
      remember (is_nil _).
      destruct b.
      { inversion H. }
      simpl in H.
      assert (Hx : get_children f ++ nil = get_children f) by auto with *.
      rewrite Hx in *; clear Hx.
      eauto using find_generic_impl_lt, forall_get_children_lt.
    - eauto using find_impl_check.
  Qed.

  Lemma find_inv_check_true:
    forall f,
    check f = true ->
    find f = Some f.
  Proof.
    intros.
    unfold find.
    rewrite find_generic_equation.
    simpl.
    rewrite H.
    trivial.
  Qed.

  Lemma find_spec_le:
    forall f f',
    find f = Some f' ->
    f' <= f /\ check f' = true.
  Proof.
    intros.
    remember (check f).
    destruct b.
    - symmetry in Heqb.
      assert (Hx := Heqb).
      apply find_inv_check_true in Heqb.
      rewrite Heqb in H.
      inversion H.
      subst.
      split.
      + auto using le_refl.
      + assumption.
    - assert (Hx : f' < f /\ check f' = true) by auto using find_spec_lt.
      destruct Hx.
      split; auto using lt_to_le.
  Qed.
End Find.

