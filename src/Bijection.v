Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Omega.

Section Defs.
  Variable A:Type.

  (** [MapsTo] is the last index of [x]. *)

  Inductive MapsTo (x:A) : nat -> list A -> Prop :=
  | maps_to_eq:
    forall l,
    MapsTo x (length l) (x::l)
  | maps_to_cons:
    forall l y n,
    x <> y ->
    MapsTo x n l ->
    MapsTo x n (y :: l).

  (** [IndexOf] assigns an element to an index with respect to a given list. *)

  Inductive IndexOf (x:A) : nat -> list A -> Prop :=
  | index_of_eq:
    forall l,
    IndexOf x (length l) (x :: l)
  | index_of_cons:
    forall y n l,
    IndexOf x n l ->
    IndexOf x n (y :: l).

  (** Checks if a number is an index of the given list,
      which is defined whenever there is an element [x] with an
      index of [n]. *)

  Inductive Index (n:nat) (l:list A) : Prop :=
  | index_def:
    forall x,
    IndexOf x n l ->
    Index n l.

  Lemma index_of_to_in:
    forall x n l,
    IndexOf x n l ->
    In x l.
  Proof.
    intros.
    induction l. {
      inversion H.
    }
    inversion H; subst.
    - auto using in_eq.
    - auto using in_cons.
  Qed.

  Lemma index_of_fun_1:
    forall l x n n',
    NoDup l ->
    IndexOf x n l ->
    IndexOf x n' l ->
    n' = n.
  Proof.
    intros.
    induction l. {
      inversion H0.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    - inversion H1; subst; clear H1.
      + trivial.
      + contradiction H4; eauto using index_of_to_in.
    - inversion H1; subst; clear H1.
      + contradiction H4; eauto using index_of_to_in.
      + eauto.
  Qed.

  Lemma index_of_lt:
    forall x n l,
    IndexOf x n l ->
    n < length l.
  Proof.
    intros.
    induction l. {
      inversion H.
    }
    inversion H; subst.
    - auto.
    - simpl.
      assert (n < length l) by eauto.
      eauto.
  Qed.

  Lemma index_cons:
    forall n l x,
    Index n l ->
    Index n (x::l).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using index_def, index_of_cons.
  Qed.

  Lemma lt_to_index:
    forall n l,
    n < length l ->
    Index n l.
  Proof.
    induction l; intros; simpl in *. {
      inversion H.
    }
    inversion H; subst; clear H.
    - eauto using index_def, index_of_eq.
    - auto using index_cons with *.
  Qed.

  Lemma index_lt:
    forall n l,
    Index n l ->
    n < length l.
  Proof.
    intros.
    inversion H.
    eauto using index_of_lt.
  Qed.

  Lemma index_iff_length:
    forall n l,
    Index n l <-> n < length l.
  Proof.
    split; auto using index_lt, lt_to_index.
  Qed.

  Lemma in_to_index_of:
    forall l x,
    In x l ->
    exists n, n < length l /\ IndexOf x n l.
  Proof.
    induction l; intros. {
      inversion H.
    }
    destruct H.
    - subst.
      exists (length l).
      simpl.
      eauto using index_of_eq.
    - apply IHl in H.
      destruct H as (n, (?,?)).
      exists n.
      simpl.
      eauto using index_of_cons.
  Qed.

  Lemma index_of_bij:
    forall l x x' n,
    NoDup l ->
    IndexOf x n l ->
    IndexOf x' n l ->
    x' = x.
  Proof.
    intros.
    induction l. {
      inversion H0.
    }
    inversion H; clear H; subst.
    inversion H0; subst; clear H0.
    - inversion H1; subst; clear H1.
      + trivial.
      + assert (length l < length l). {
          eauto using index_of_lt.
        }
        omega.
    - inversion H1; subst; clear H1.
      + assert (length l < length l). {
          eauto using index_of_lt.
        }
        omega.
      + eauto.
  Qed.

  Lemma index_of_neq:
    forall l x y n n',
    NoDup l ->
    IndexOf x n l ->
    IndexOf y n' l ->
    n <> n' ->
    x <> y.
  Proof.
    intros.
    induction l. {
      inversion H0.
    }
    inversion H; clear H; subst.
    inversion H0; subst; clear H0.
    - inversion H1; subst; clear H1.
      + omega.
      + unfold not; intros; subst.
        contradiction H5.
        eauto using index_of_to_in.
    - inversion H1; subst; clear H1.
      + unfold not; intros; subst.
        contradiction H5.
        eauto using index_of_to_in.
      + eauto.
  Qed.

  Inductive Lt (l:list A) (x:A) (y:A) : Prop :=
  | lt_def:
    forall xn yn,
    IndexOf x xn l ->
    IndexOf y yn l ->
    xn < yn ->
    Lt l x y.

  Definition Gt (l:list A) (x:A) (y:A) : Prop := Lt l y x.

  Lemma lt_trans (l:list A) (N:NoDup l):
    forall x y z,
    Lt l x y ->
    Lt l y z ->
    Lt l x z.
  Proof.
    intros.
    inversion H; clear H.
    inversion H0; clear H0.
    rename yn0 into zn.
    assert (xn0 = yn) by
    eauto using index_of_fun_1; subst.
    apply lt_def with (xn:=xn) (yn:=zn); auto.
    omega.
  Qed.

  Lemma gt_trans (l:list A) (N:NoDup l):
    forall x y z,
    Gt l x y ->
    Gt l y z ->
    Gt l x z.
  Proof.
    unfold Gt; intros.
    eauto using lt_trans.
  Qed.

  Lemma lt_irrefl (l:list A) (N:NoDup l):
    forall x,
    ~ Lt l x x.
  Proof.
    intros.
    intuition.
    inversion H.
    assert (xn=yn) by eauto using index_of_fun_1.
    intuition.
  Qed.

  Lemma gt_irrefl (l:list A) (N:NoDup l):
    forall x,
    ~ Gt l x x.
  Proof.
    unfold Gt; intros.
    eauto using lt_irrefl.
  Qed.

  Lemma lt_neq (l:list A) (N:NoDup l):
    forall x y,
    Lt l x y ->
    x <> y.
  Proof.
    intros.
    inversion H; clear H.
    assert (xn <> yn) by omega.
    eauto using index_of_neq.
  Qed.

  Lemma gt_neq (l:list A) (N:NoDup l):
    forall x y,
    Gt l x y ->
    x <> y.
  Proof.
    unfold Gt; intros.
    apply lt_neq in H; auto.
  Qed.

  Lemma lt_absurd_nil:
    forall x y,
    ~ Lt nil x y.
  Proof.
    intuition.
    destruct H.
    inversion H.
  Qed.

  Lemma lt_cons:
    forall z l x y,
    Lt l x y ->
    Lt (z :: l) x y.
  Proof.
    intros.
    inversion H.
    eauto using lt_def, index_of_cons.
  Qed.

End Defs.


Section MapsTo.
  Variable A:Type.

  Lemma maps_to_inv_eq:
    forall (x:A) n vs,
    MapsTo x n (x :: vs) ->
    n = length vs.
  Proof.
    intros.
    inversion H; subst; auto.
    contradiction H3; trivial.
  Qed.

  Lemma maps_to_neq:
    forall (x:A) y vs n,
    x <> y ->
    MapsTo y n (x :: vs) ->
    MapsTo y n vs.
  Proof.
    intros.
    inversion H0.
    - subst; contradiction H; trivial.
    - assumption.
  Qed.

  Lemma maps_to_fun_2:
    forall vs (x:A) n n',
    MapsTo x n vs ->
    MapsTo x n' vs ->
    n' = n.
  Proof.
    induction vs; intros. {
      inversion H.
    }
    inversion H; subst; clear H;
    inversion H0; subst; clear H0; auto.
    - contradiction H3; trivial.
    - contradiction H4; trivial.
    - eauto.
  Qed.

  Lemma maps_to_to_index_of:
    forall (x:A) nx vs,
    MapsTo x nx vs ->
    IndexOf x nx vs.
  Proof.
    intros.
    induction H. {
      auto using index_of_eq.
    }
    auto using index_of_cons.
  Qed.

  Lemma maps_to_lt:
    forall (x:A) n vs,
    MapsTo x n vs ->
    n < length vs.
  Proof.
    induction vs; intros. {
      inversion H.
    }
    inversion H; subst. {
      auto.
    }
    apply IHvs in H4.
    simpl.
    auto.
  Qed.

  Lemma maps_to_absurd_length:
    forall (x:A) vs,
    ~ MapsTo x (length vs) vs.
  Proof.
    intros.
    unfold not; intros.
    apply maps_to_lt in H.
    apply Lt.lt_irrefl in H.
    assumption.
  Qed.

  Lemma index_of_absurd_length:
    forall (x:A) vs,
    ~ IndexOf x (length vs) vs.
  Proof.
    intuition.
    apply index_of_lt in H.
    omega.
  Qed.

  Lemma index_absurd_length:
    forall (vs:list A),
    ~ Index (length vs) vs.
  Proof.
    intuition.
    inversion H.
    apply index_of_absurd_length in H0.
    contradiction.
  Qed.

  Lemma maps_to_absurd_cons:
    forall (x:A) y n vs,
    MapsTo x n vs ->
    ~ (MapsTo y n (y :: vs)).
  Proof.
    intros.
    unfold not; intros.
    assert (n = length vs) by eauto using maps_to_inv_eq; subst.
    apply maps_to_absurd_length in H.
    contradiction.
  Qed.

  Lemma maps_to_inv_key:
    forall (x:A) y l,
    MapsTo y (length l) (x :: l) ->
    y = x.
  Proof.
    intros.
    inversion H; subst. {
      trivial.
    }
    apply maps_to_absurd_length in H4; contradiction.
  Qed.

  Lemma index_of_inv_key:
    forall (x:A) y l,
    IndexOf y (length l) (x :: l) ->
    y = x.
  Proof.
    intros.
    inversion H; subst. {
      trivial.
    }
    apply index_of_absurd_length in H2; contradiction.
  Qed.

  Lemma index_of_fun_2:
    forall l (x:A) y n,
    IndexOf x n l ->
    IndexOf y n l ->
    y = x.
  Proof.
    induction l; intros. {
      inversion H.
    }
    inversion H; subst; clear H. {
      inversion H0; subst; clear H0. {
        trivial.
      }
      apply index_of_absurd_length in H2; contradiction.
    }
    inversion H0; subst; clear H0. {
      apply index_of_absurd_length in H3; contradiction.
    }
    eauto.
  Qed.

  Lemma maps_to_fun_1:
    forall (x:A) y n vs,
    MapsTo x n vs ->
    MapsTo y n vs ->
    y = x.
  Proof.
    intros.
    induction H. {
      eauto using maps_to_inv_key.
    }
    inversion H0; subst. {
      apply maps_to_absurd_length in H1.
      contradiction.
    }
    auto.
  Qed.

  Lemma maps_to_to_in:
    forall (x:A) n vs,
    MapsTo x n vs ->
    List.In x vs.
  Proof.
    intros.
    induction H. {
      auto using List.in_eq.
    }
    auto using List.in_cons.
  Qed.

  Lemma index_eq:
    forall (x:A) vs,
    Index (length vs) (x::vs).
  Proof.
    intros.
    eauto using index_def, index_of_eq.
  Qed.

  Lemma maps_to_to_index:
    forall (x:A) n vs,
    MapsTo x n vs ->
    Index n vs.
  Proof.
    intros.
    eauto using index_def, maps_to_to_index_of.
  Qed.

  Section MapsToDec.
    Variable eq_dec: forall (x y:A), { x = y } + { x <> y }.

    Lemma in_to_maps_to:
      forall (x:A) vs,
      List.In x vs ->
      exists n, MapsTo x n vs.
    Proof.
      induction vs; intros. {
        inversion H.
      }
      destruct H. {
        subst.
        eauto using maps_to_eq.
      }
      destruct (eq_dec x a). {
        subst.
        eauto using maps_to_eq.
      }
      apply IHvs in H.
      destruct H.
      eauto using maps_to_cons.
    Qed.

    Fixpoint lookup x l :=
    match l with
    | nil => None
    | y :: l => if eq_dec x y then Some (length l) else lookup x l
    end.

    Lemma lookup_some:
      forall xs x n,
      lookup x xs = Some n ->
      MapsTo x n xs.
    Proof.
      induction xs; intros. {
        inversion H.
      }
      simpl in *.
      destruct (eq_dec x a). {
        inversion H; subst.
        auto using maps_to_eq.
      }
      auto using maps_to_cons.
    Qed.

    Lemma lookup_none:
      forall xs x,
      lookup x xs = None ->
      ~ List.In x xs.
    Proof.
      induction xs; intros; simpl in *; auto.
      destruct (eq_dec x a).
      - inversion H.
      - unfold not; intros.
        apply IHxs in H.
        destruct H0.
        * contradiction n; auto.
        * contradiction.
    Qed.

    Lemma maps_to_to_lookup:
      forall x n xs,
      MapsTo x n xs ->
      lookup x xs = Some n.
    Proof.
      induction xs; intros. {
        inversion H.
      }
      simpl.
      destruct (eq_dec x a). {
        subst.
        apply maps_to_inv_eq in H; subst.
        trivial.
      }
      apply maps_to_neq in H; auto.
    Qed.

    Lemma not_in_lookup_none:
      forall xs x,
      ~ List.In x xs ->
      lookup x xs = None.
    Proof.
      induction xs; intros. {
        auto.
      }
      simpl.
      destruct (eq_dec x a). {
        subst.
        contradiction H; auto using in_eq.
      }
      apply IHxs.
      unfold not; intros N.
      contradiction H; auto using in_cons.
    Qed.

  End MapsToDec.
End MapsTo.