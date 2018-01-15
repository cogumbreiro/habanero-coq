Require Coq.Arith.Compare_dec.

Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.Arith.Peano_dec.
Require Import Omega.

Require Import Aniceto.Map.

Require Coq.FSets.FMapFacts.

Inductive fid := finishid : nat -> fid.

Definition fid_nat r := match r with | finishid n => n end.

Definition fid_first := finishid 0.

Definition fid_next m := finishid (S (fid_nat m)).

Module FID <: UsualOrderedType.
  Definition t := fid.
  Definition eq := @eq fid.
  Definition lt x y := lt (fid_nat x) (fid_nat y).
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

  Lemma lt_not_eq : forall x y : t, lt x y -> x <> y.
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

  Import Coq.Arith.Compare_dec.
  Lemma compare:
    forall x y, Compare lt Logic.eq x y.
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

  Lemma eq_dec : forall x y : t, {x = y} + {x <> y}.
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
End FID.


Module Map_FID := FMapAVL.Make FID.
Module Map_FID_Facts := FMapFacts.Facts Map_FID.
Module Map_FID_Props := FMapFacts.Properties Map_FID.
Module Map_FID_Extra := MapUtil Map_FID.
Module Set_FID := FSetAVL.Make FID.
Definition set_fid := Set_FID.t.
Lemma fid_eq_rw:
  forall (k k':fid), FID.eq k k' <-> k = k'.
Proof.
  intros.
  auto with *.
Qed.

Section NotIn.
  Variable elt:Type.

  Let lt_irrefl:
    forall x : fid, ~ FID.lt x x.
  Proof.
    unfold not; intros.
    apply FID.lt_not_eq in H.
    contradiction H.
    apply FID.eq_refl.
  Qed.

  Let lt_next:
    forall x, FID.lt x (fid_next x).
  Proof.
    intros.
    destruct x.
    unfold fid_next, fid_nat, FID.lt.
    simpl.
    auto.
  Qed.

  Let fid_impl_eq:
    forall k k' : fid, k = k' -> k = k'.
  Proof.
    auto.
  Qed.

  Definition supremum {elt:Type} := @Map_FID_Extra.supremum elt fid_first fid_next FID.lt FID.compare.

  Theorem find_not_in:
    forall (m: Map_FID.t elt),
    ~ Map_FID.In (supremum m) m.
  Proof.
    intros.
    eauto using Map_FID_Extra.find_not_in, FID.lt_trans.
  Qed.

End NotIn.