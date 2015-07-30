Require Import Coq.Lists.List.

Section REL.
Variable A : Type.
Variable IsA : A -> Prop.
Variable LE : A -> A -> Prop.
Variable LE_inv: forall t t', LE t t' -> IsA t /\ IsA t'.
Variable LE_dec: forall t t', {LE t t'} + {~ LE t t'}.
Variable LE_refl: forall t, IsA t -> LE t t.
Variable LE_trans:
  forall t1 t2 t3,
  LE t1 t2 ->
  LE t2 t3 ->
  LE t1 t3.

Definition Unrelated t t' := (~ LE t t' /\ ~ LE t' t).

Let le_inv_left: forall t t', LE t t' -> IsA t.
Proof.
  intros.
  apply LE_inv in H.
  intuition.
Qed.

Let le_inv_right: forall t t', LE t t' -> IsA t'.
Proof.
  intros.
  apply LE_inv in H.
  intuition.
Qed.

Lemma unrelated_symm:
  forall t t',
  Unrelated t t' ->
  Unrelated t' t.
Proof.
  intros.
  unfold Unrelated in *.
  intuition.
Qed.

Definition Smallest (t:A) (ts:list A) :=
  In t ts /\ forall t', In t' ts -> Unrelated t t' \/ LE t t'.

Lemma smallest_inv:
  forall x l,
  Smallest x l ->
  In x l.
Proof.
  intros.
  unfold Smallest in *.
  intuition.
Qed.

Lemma has_smallest_step_eq:
  forall x y ts,
  LE y x ->
  In y ts ->
  Smallest y ts ->
  Smallest y (x :: ts).
Proof.
  intros.
  unfold Smallest in *.
  destruct H1 as (_, H1).
  intuition.
  inversion H2.
  - subst. intuition.
  - apply H1. intuition.
Qed.

Lemma has_smallest_step_le:
  forall t t' ts,
  Smallest t' ts ->
  LE t t' ->
  Forall IsA ts ->
  Smallest t (t::ts).
Proof.
  intros.
  unfold Smallest.
  split.
  { intuition. }
  intros.
  rename t'0 into x.
  unfold Smallest in *.
  destruct H as (_, H).
  assert (Hx := H x).
  inversion H2.
  - subst.
    right.
    apply LE_refl.
    apply le_inv_left with (t':=t').
    assumption.
  - apply Hx in H3. clear Hx H.
    destruct (LE_dec t x).
    { intuition. }
    left.
    destruct H3.
    + unfold Unrelated in *.
      split. { intuition. }
      destruct H.
      intuition.
      assert (LE x t'). {
        apply LE_trans with (t2:=t); repeat auto.
      }
      contradiction H5.
    + assert (LE t x). {
        apply LE_trans with (t2:=t'); repeat auto.
      }
      contradiction H3.
Qed.

Lemma has_smallest_step_unrelated:
  forall x y ts,
  In y ts ->
  Smallest y ts ->
  Unrelated x y ->
  Smallest y (x :: ts).
Proof.
  intros.
  unfold Smallest.
  intuition.
  inversion H2.
  - subst.
    left.
    apply unrelated_symm.
    assumption.
  - unfold Smallest in H0.
    destruct H0 as (_, H0).
    apply H0.
    assumption.
Qed.

Lemma has_smallest_cons:
  forall x y ts,
  Forall IsA ts -> 
  Smallest y ts ->
  exists z, Smallest z (x :: ts).
Proof.
  intros x y ts Hisa Hsmall.
  destruct (LE_dec y x).
  - exists y.
    apply has_smallest_step_eq; repeat auto.
    apply smallest_inv in Hsmall; assumption.
  - destruct (LE_dec x y).
    + exists x.
      split. { intuition. }
      apply has_smallest_step_le with (t':=y); repeat auto.
    + exists y.
      assert (Unrelated x y). {
        unfold Unrelated; intuition.
      }
      intuition.
      apply has_smallest_step_unrelated; repeat auto.
      apply smallest_inv in Hsmall; assumption.
Qed.


Let in_inv_eq:
  forall {A} (x y:A),
  In x (y :: nil) ->
  x = y.
Proof.
  intros.
  inversion H.
  auto.
  inversion H0.
Qed.

Theorem has_smallest:
  forall ts,
  ts <> nil ->
  Forall IsA ts ->
  exists t, Smallest t ts.
Proof.
  intros ts Hnil Hfor.
  induction ts.
  (* absurd *) {
    contradiction Hnil.
    auto.
  }
  destruct ts.
  - exists a.
    unfold Smallest.
    split. { intuition. }
    intros t' Hin.
    apply in_inv_eq in Hin.
    subst.
    right; apply LE_refl.
    apply Forall_inv with (l:=nil); assumption.
  - assert (IHnil : a0 :: ts <> nil). {
      intuition. inversion H.
    }
    assert (IHfor : Forall IsA (a0 :: ts)). {
      inversion Hfor.
      auto.
    }
    assert (Hoo := IHts IHnil IHfor).
    destruct Hoo as (t, H).
    apply has_smallest_cons with (y:=t); repeat auto.
Qed.
End REL.
