Require Import Coq.ZArith.BinInt.
Require Import Coq.Relations.Relations.
Require Import Coq.Lists.List.
Require Import Vars.
Require Import ListUtil.
Require Import MapUtil.
Require Import Lang.
Require Import ListSetUtil.

Definition ph_diff (ph:phaser) (t1:tid) (t2:tid) (z:Z)
  := exists v1, Map_TID.MapsTo t1 v1 ph /\
     exists v2, Map_TID.MapsTo t2 v2 ph /\
     exists n1, WaitPhase v1 n1 /\
     exists n2, WaitPhase v2 n2 /\
     ((Z_of_nat n1) - (Z_of_nat n2))%Z = z.

Definition diff (ph:phaser) (t1:tid) (t2:tid) : option Z := 
  match Map_TID.find t1 ph with
    | Some v1 => 
      match Map_TID.find t2 ph with
        | Some v2 =>
          Some ((Z_of_nat (wait_phase v1)) - (Z_of_nat (wait_phase v2)))%Z
        | _ => None
      end
    | _ => None
  end.

Lemma diff_spec_1:
  forall ph t1 t2 z,
  diff ph t1 t2 = Some z ->
  ph_diff ph t1 t2 z.
Proof.
  intros.
  unfold diff in *.
  unfold ph_diff.
  remember (Map_TID.find t1 ph).
  symmetry in Heqo.
  destruct o.
  - rewrite <- Map_TID_Facts.find_mapsto_iff in Heqo.
    exists t.
    intuition.
    remember (Map_TID.find t2 ph).
    symmetry in Heqo0.
    destruct o.
    + rewrite <- Map_TID_Facts.find_mapsto_iff in Heqo0.
      exists t0.
      intuition.
      exists (wait_phase t).
      split.
      { apply wait_phase_spec_1. }
      exists (wait_phase t0).
      split.
      { apply wait_phase_spec_1. }
      inversion H.
      auto.
    + inversion H.
  - inversion H.
Qed.

Lemma diff_spec_2:
  forall ph t1 t2 z,
  ph_diff ph t1 t2 z ->
  diff ph t1 t2 = Some z.
Proof.
  intros.
  unfold ph_diff in H.
  unfold diff.
  destruct H as (v1, (Hmt1, (v2, (Hmt2, (n1, (Hw1, (n2, (Hw2, Hdiff)))))))).
  apply Map_TID_Facts.find_mapsto_iff in Hmt1.
  apply Map_TID_Facts.find_mapsto_iff in Hmt2.
  rewrite Hmt1.
  rewrite Hmt2.
  apply wait_phase_spec_2 in Hw1.
  apply wait_phase_spec_2 in Hw2.
  subst.
  trivial.
Qed.

Lemma diff_none:
  forall ph t t',
  diff ph t t' = None ->
  forall z, ~ ph_diff ph t t' z.
Proof.
  intros.
  intuition.
  apply diff_spec_2 in H0.
  rewrite H in H0.
  inversion H0.
Qed.

Lemma ph_diff_fun:
  forall ph t t' z z',
  ph_diff ph t t' z ->
  ph_diff ph t t' z' ->
  z = z'.
Proof.
  intros.
  apply diff_spec_2 in H.
  apply diff_spec_2 in H0.
  rewrite H in H0.
  inversion H0.
  trivial.
Qed.

Definition WTaskIn (t:tid) (ph:phaser) := Map_TID.In t ph.

Lemma wtaskin_spec:
  forall t ph,
  WTaskIn t ph <-> Map_TID.In t ph.
Proof.
  intros.
  unfold WTaskIn in *.
  intuition.
Qed.

Lemma wtask_in_def:
  forall t ph,
  Map_TID.In t ph ->
  WTaskIn t ph.
Proof.
  intros.
  unfold WTaskIn.
  intuition.
Qed.

Lemma ph_diff_refl:
  forall t ph,
  WTaskIn t ph ->
  ph_diff ph t t 0.
Proof.
  intros.
  unfold ph_diff.
  rewrite wtaskin_spec in H.
  apply Map_TID_Extra.in_to_mapsto in H.
  destruct H as (v, H).
  exists v.
  intuition.
  exists v.
  intuition.
  destruct (get_wait_phase v) as (n,?).
  repeat (exists n; intuition).
Qed.

Lemma ph_diff_symm:
  forall ph t t' z,
  ph_diff ph t t' z ->
  ph_diff ph t' t (-z).
Proof.
  intros.
  unfold ph_diff in *.
  destruct H as (v1, (Hmt1, (v2, (Hmt2,
    (n1, (Hw1, (n2, (Hw2, Hdiff)))))))).
  exists v2; intuition.
  exists v1; intuition.
  exists n2; intuition.
  exists n1; intuition.
Qed.

Lemma ph_diff_inv:
  forall ph t t' z,
  ph_diff ph t t' z ->
  WTaskIn t ph /\ WTaskIn t' ph.
Proof.
  intros.
  unfold ph_diff in H.
  destruct H as (v1, (Hmt1, (v2, (Hmt2,
    (n1, (Hw1, (n2, (Hw2, Hdiff)))))))).
  unfold WTaskIn in *.
  split.
  - exists v1.
    intuition.
  - exists v2.
    intuition.
Qed.

Lemma ph_diff_inv_in:
  forall ph t t' z,
  ph_diff ph t t' z ->
  Map_TID.In t ph /\ Map_TID.In t' ph.
Proof.
  intros.
  destruct (ph_diff_inv _ _ _ _ H).
  apply wtaskin_spec in H0.
  apply wtaskin_spec in H1.
  intuition.
Qed.

Lemma ph_diff_inv_left:
  forall ph t t' z,
  ph_diff ph t t' z ->
  WTaskIn t ph.
Proof.
  intros.
  apply ph_diff_inv in H.
  intuition.
Qed.

Lemma ph_diff_inv_right:
  forall ph t t' z,
  ph_diff ph t t' z ->
  WTaskIn t' ph.
Proof.
  intros.
  apply ph_diff_inv in H.
  intuition.
Qed.

Definition tid_In (t:tid) (pm:phasermap) :=
  exists p ph, Map_PHID.MapsTo p ph pm /\ WTaskIn t ph.

Definition ph_le (ph:phaser) (t1:tid) (t2:tid) :=
  exists (z:Z), ph_diff ph t1 t2 z /\ (z <= 0)%Z.

Lemma ph_le_refl:
  forall t ph,
  WTaskIn t ph ->
  ph_le ph t t.
Proof.
  intros.
  unfold ph_le.
  exists 0%Z.
  intuition.
  apply ph_diff_refl.
  assumption.
Qed.

Lemma ph_le_inv:
  forall t t' ph,
  ph_le ph t t' ->
  WTaskIn t ph /\ WTaskIn t' ph.
Proof.
  intros.
  unfold ph_le in *.
  destruct H as (z, (H1, H2)).
  apply ph_diff_inv with (z:=z).
  assumption.
Qed.

Lemma ph_le_inv_in:
  forall t t' ph,
  ph_le ph t t' ->
  Map_TID.In t ph /\ Map_TID.In t' ph.
Proof.
  intros.
  unfold ph_le in *.
  destruct H as (z, (H, Hdiff)).
  apply ph_diff_inv_in in H.
  intuition.
Qed.

Lemma ph_le_inv_in_left:
  forall t t' ph,
  ph_le ph t t' ->
  Map_TID.In t ph.
Proof.
  intros.
  apply ph_le_inv_in in H.
  intuition.
Qed.

Lemma ph_le_inv_in_right:
  forall t t' ph,
  ph_le ph t t' ->
  Map_TID.In t' ph.
Proof.
  intros.
  apply ph_le_inv_in in H.
  intuition.
Qed.

Section LE.
Variable pm:phasermap.

(** Less-than-equals *)
Definition wp_le (t:tid) (t':tid) :=
  exists p ph, Map_PHID.MapsTo p ph pm /\ ph_le ph t t'.

Lemma wp_le_refl:
  forall t,
  tid_In t pm ->
  wp_le t t.
Proof.
  intros.
  unfold wp_le.
  unfold tid_In in H.
  destruct H as (p, (ph, (Hmt, Hin))).
  exists p; exists ph.
  intuition.
  apply ph_le_refl.
  assumption.
Qed.

Lemma wp_le_inv:
  forall t t',
  wp_le t t' ->
  tid_In t pm /\ tid_In t' pm.
Proof.
  intros.
  unfold wp_le in *.
  destruct H as (p, (ph, (Hmt, Hin))).
  apply ph_le_inv in Hin.
  unfold tid_In.
  split; repeat (exists p; exists ph; intuition).
Qed.

Definition LE := clos_trans tid wp_le.

Variable LE_dec:
  forall t t',
  {LE t t'} + {~ LE t t'}.

Lemma LE_refl:
  forall t,
  tid_In t pm ->
  LE t t.
Proof.
  intros.
  unfold LE.
  apply t_step.
  apply wp_le_refl.
  assumption.
Qed.

Lemma LE_inv:
  forall t t',
  LE t t' ->
  tid_In t pm /\ tid_In t' pm.
Proof.
  intros.
  unfold LE in H.
  induction H.
  - apply wp_le_inv in H.
    intuition.
  - intuition.
Qed.

Lemma LE_trans:
  forall t1 t2 t3,
  LE t1 t2 ->
  LE t2 t3 ->
  LE t1 t3.
Proof.
  intros.
  apply t_trans with (y:=t2).
  auto.
  auto.
Qed.

End LE.
