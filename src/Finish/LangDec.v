Require Import Coq.Lists.List.

Require Import Aniceto.EqDec.
Require Import HJ.Vars.
Require Import HJ.Finish.Lang.

Definition match_tid (t:tid) (p:l_task) := beq_tid t (fst p).

Lemma match_tid_inv_true:
  forall t p,
  match_tid t p = true ->
  t = fst p.
Proof.
  intros.
  unfold match_tid in *.
  auto using beq_tid_to_eq.
Qed.

Lemma match_tid_eq_refl:
  forall x y,
  match_tid x (x, y) = true.
Proof.
  intros.
  unfold match_tid.
  simpl.
  auto using beq_tid_refl.
Qed.

Definition is_registered (t:tid) (f:finish) := existsb (match_tid t) (get_tasks f).

Lemma is_registered_to_prop:
  forall t f,
  is_registered t f = true ->
  Registered t f.
Proof.
  intros.
  unfold is_registered in *.
  apply existsb_exists in H.
  destruct H as (p, (Hin,Hm)).
  apply match_tid_inv_true in Hm.
  destruct p as (a,b).
  simpl in *; subst.
  eauto using registered_def, child_def.
Qed.

Lemma is_registered_from_prop:
  forall t f,
  Registered t f ->
  is_registered t f = true.
Proof.
  intros.
  destruct H.
  unfold is_registered.
  rewrite existsb_exists.
  destruct H.
  eauto using match_tid_eq_refl.
Qed.

Section RegisteredDec.
  Set Implicit Arguments.
  Require Import Aniceto.Spec.
  Variable t:tid.
  Variable f:finish.

  (** We establish that [Register] is a decidable property, by using
    class [Decidable]. *)

  Program Instance Registered_Decidable: Decidable (Registered t f) := {
    Decidable_witness := is_registered t f
  }.
  Next Obligation.
    split; auto using is_registered_to_prop, is_registered_from_prop.
  Qed.

  Lemma registered_dec:
    { Registered t f } + { ~ Registered t f }.
  Proof.
    destruct decide_sumbool; intuition.
  Qed.

End RegisteredDec.

