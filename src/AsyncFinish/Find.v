Require Import Coq.Lists.List.

Require Import Aniceto.List.

Require Import HJ.AsyncFinish.Lang.

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
    summation size (get_children f) < size f.
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

  Require Import Coq.Relations.Relation_Operators.
  
  Lemma find_generic_impl_lt:
    forall f l f',
    Forall (fun f' => Lt f' f) l ->
    find_generic l = Some f' ->
    Lt f' f.
  Proof.
    intros f.
    induction f using lt_ind.
    - intros.
      destruct l.
      + rewrite find_generic_nil in H0; inversion H0.
      + inversion H.
        subst.
        apply lt_leaf_absurd in H3.
        inversion H3.
    - intros.
      apply lt_cons.
      assert (Hx := IHf l0 f').
      apply Hx; auto.
      + rewrite Forall_forall in *.
        intros.
        eauto using lt_inv_cons_ready.
    - intros.
      unfold Lt.
      apply t_trans.
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

  Lemma find_spec_1:
    forall f f',
    find f = Some f' ->
    check f = false ->
    Lt f' f /\ check f' = true.
  Proof.
    intros f.
    unfold find.
    induction f using finish_ind_strong.
    - intros.
      rewrite find_generic_equation in H.
      simpl in H.
      rewrite H0 in H.
      inversion H.
    - intros.
      assert (Lt f' (Node l) /\ check f' = true). {
        apply IHf.
        + apply find_generic_contract with (t); auto.
          
      }*)
      rewrite find_generic_equation in H.
      rewrite H in *.
      remember (is_nil _).
      destruct b.
      { inversion H. }
      apply IHf in H.
      } 
      rewrite find_generic_equation in H.
      simpl List.find in H.
      rewrite H0 in H.
      remember (flat_map _ _) as l'.
      assert (l' = get_children (Node l)). {
        subst.
        simpl.
        auto with *.
      }
      rewrite H1 in *.
      remember (is_nil _).
      destruct b.
      { inversion H. }
      apply IHf in H.
End Find.

