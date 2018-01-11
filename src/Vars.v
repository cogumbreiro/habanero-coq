(* begin hide *)
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FMapAVL.
Require Coq.FSets.FMapFacts.
Require Coq.FSets.FSetProperties.
Require Coq.FSets.FSetBridge.
Require Import Aniceto.Map.
Require Import Aniceto.Set.
Require Import Aniceto.EqDec.

Module TID := Nat_as_OT.
Module TID_Facts := OrderedTypeFacts TID.
Module Set_TID := FSetAVL.Make TID.
Module Set_TID_Props := FSetProperties.Properties Set_TID.
Module Set_TID_Extra := SetUtil Set_TID.
Module Set_TID_Dep := FSetBridge.DepOfNodep Set_TID.
Module Map_TID := FMapAVL.Make TID.
Module Map_TID_Facts := FMapFacts.Facts Map_TID.
Module Map_TID_Props := FMapFacts.Properties Map_TID.
Module Map_TID_Extra := MapUtil Map_TID.

Definition tid := TID.t.
Definition set_tid := Set_TID.t.

Lemma tid_eq_rw:
  forall k k' : tid, k = k' <-> k = k'.
Proof.
  intros.
  auto with *.
Qed.

(** Boolean comparison of tid instances. *)
Definition beq_tid := eq_dec_to_bool tid TID.eq_dec.

Lemma beq_tid_to_eq:
  forall x y,
  beq_tid x y = true ->
  x = y.
Proof.
  intros.
  unfold beq_tid in *.
  eauto using eq_dec_inv_true.
Qed.

Lemma beq_tid_refl:
  forall x,
  beq_tid x x = true.
Proof.
  intros.
  unfold beq_tid.
  auto using eq_dec_refl.
Qed.

Module PHID := Nat_as_OT.
Module Set_PHID := FSetAVL.Make PHID.
Module Set_PHID_Extra := SetUtil Set_PHID.
Module Map_PHID := FMapAVL.Make PHID.
Module Map_PHID_Facts := FMapFacts.Facts Map_PHID.
Module Map_PHID_Props := FMapFacts.Properties Map_PHID.
Module Map_PHID_Extra := MapUtil Map_PHID.

Definition phid := PHID.t.
Definition set_phid := Set_PHID.t.

Lemma phid_eq_rw:
  forall k k' : phid, k = k' <-> k = k'.
Proof.
  intros.
  auto with *.
Qed.

Inductive lt : list tid -> list tid -> Prop :=
| lt_nil:
  forall t l,
  lt nil (t::l)
| lt_lt:
  forall t1 t2 l1 l2,
  TID.lt t1 t2 ->
  lt (t1::l1) (t2::l2)
| lt_cons:
  forall t l1 l2,
  lt l1 l2 ->
  lt (t::l1) (t::l2)
| lt_cons_rhs:
  forall t1 t2 l1 l2,
  lt l1 (t2::l2) ->
  t1 < t2 ->
  lt (t1::l1) (t2::l2).

Module FID <: UsualOrderedType.

  Definition t := list tid.

  Definition eq := @eq (list tid).
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  
  Definition lt := lt.

  Let lt_trans' : forall x y : t, lt x y -> forall z, lt y z -> lt x z.
  Proof.
    intros x y H.
    unfold lt.
    induction H.
    - intros.
      destruct H; auto using lt_nil, lt_lt.
    - intros.
      destruct z.
      inversion H0.
      inversion H0; (subst; destruct z;  eauto using lt_lt, lt_cons, lt_nil, TID.lt_trans).
    - intros.
      destruct z.
      inversion H0.
      inversion H0; (subst; destruct z;  eauto using lt_lt, lt_cons, lt_nil, TID.lt_trans).
    - intros.
      destruct z.
      inversion H1.
      inversion H1; (subst; destruct z;  eauto using lt_lt, lt_cons, lt_nil, TID.lt_trans).
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros.
    eauto using lt_trans'.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros.
    unfold eq.
    induction H.
    - auto with *.
    - apply TID.lt_not_eq in H.
      intuition.
      unfold TID.eq in H.
      inversion H0.
      contradiction H.
    - intuition.
      inversion H0.
      subst.
      contradiction IHlt.
      trivial.
    - intuition.
      inversion H1; subst; clear H1.
      apply TID.lt_not_eq in H0.
      intuition.
  Qed.

  Lemma compare:
    forall x y, Compare lt eq x y.
  Proof.
    unfold lt.
    induction x.
    - intros.
      destruct y.
      + apply EQ.
        intuition.
      + apply LT; intuition.
        auto using lt_nil.
    - intros.
      destruct y.
      + apply GT.
        auto using lt_nil.
      + assert (Hx := IHx y).
        assert (Hy : Compare  TID.lt TID.eq a t0) by auto using TID.compare.
        inversion Hy.
        * auto using LT, lt_lt.
        * unfold TID.eq in H; subst.
          inversion Hx.
          {
            clear Hx.
            destruct x.
            {
              apply LT.
              inversion H; subst.
              auto using lt_cons with *.
            }
            apply LT.
            destruct y.
            { inversion H. }
            auto using lt_cons with *.
          }
          {
            unfold eq in *; subst.
            apply EQ.
            auto.
          }
          {
            apply GT.
            destruct x.
            inversion H.
            auto using lt_cons with *.
          }
        * auto using GT, lt_lt.
  Qed.

  Definition eq_dec := list_eq_dec TID.eq_dec.

End FID.

Module Set_FID := FSetAVL.Make FID.
Module Set_FID_Extra := SetUtil Set_FID.
Module Map_FID := FMapAVL.Make FID.
Module Map_FID_Facts := FMapFacts.Facts Map_FID.
Module Map_FID_Props := FMapFacts.Properties Map_FID.
Module Map_FID_Extra := MapUtil Map_FID.
Definition fid := FID.t.

Lemma fid_eq_rw:
  forall k k' : fid, k = k' <-> k = k'.
Proof.
  intros.
  auto with *.
Qed.

(* end hide  *)