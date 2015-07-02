Require Import Coq.ZArith.BinInt.
Require Import Coq.Relations.Relations.
Require Import Coq.Lists.List.
Require Import Vars.
Require Import ListUtil.
Require Import MapUtil.
Require Import Lang.

Definition ph_diff (ph:phaser) (t1:tid) (t2:tid) (z:Z)
  := exists v1, Map_TID.MapsTo t1 v1 ph /\
     exists v2, Map_TID.MapsTo t2 v2 ph /\
     exists n1, WaitPhase v1 n1 /\
     exists n2, WaitPhase v2 n2 /\
     ((Z_of_nat n1) - (Z_of_nat n2))%Z = z.

Definition WTaskIn (t:tid) (ph:phaser) :=
  exists v, Map_TID.MapsTo t v ph /\
  exists n, WaitPhase v n.

Lemma ph_diff_refl:
  forall t ph,
  WTaskIn t ph ->
  ph_diff ph t t 0.
Proof.
  intros.
  unfold ph_diff.
  unfold WTaskIn in H.
  destruct H as (v, (Hmt, (n, Hw))).
  repeat (exists v; intuition).
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
    exists n1.
    intuition.
  - exists v2.
    intuition.
    exists n2.
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

Section ENABLED.
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

End ENABLED.

Require Rel.

Section HAS_SMALLEST.
Variable pm: phasermap.
Let IsA t := tid_In t pm.

Let wtid_le (t1:tid) (t2:tid) := LE pm t1 t2.

Let wtid_le_inv := LE_inv pm.

Variable wtid_le_dec:
  forall t1 t2,
  { LE pm t1 t2 } + { ~ LE pm t1 t2 }.

Let wtid_le_trans:
  forall t1 t2 t3,
  wtid_le t1 t2 ->
  wtid_le t2 t3 ->
  wtid_le t1 t3.
Proof.
  unfold wtid_le in *.
  apply LE_trans.
Qed.

Let wtid_has_smallest :=
  Rel.has_smallest tid IsA wtid_le (LE_inv pm) wtid_le_dec
  (LE_refl pm) wtid_le_trans.

Theorem has_smallest:
  forall ts,
  ts <> nil ->
  Forall IsA ts ->
  exists t,
  In t ts /\
  forall t', In t' ts -> (~ LE pm t t' /\ ~ LE pm t' t) \/ LE pm t t'.
Proof.
  intros.
  destruct (wtid_has_smallest _ H H0) as (x, Hx).
  unfold Rel.Smallest in *.
  unfold Rel.Unrelated in *.
  unfold wtid_le in *.
  exists x.
  auto.
Qed.
End HAS_SMALLEST.

Require Import PairUtil.

Section LE_DEC.
Variable pm:phasermap.

Definition edge (T:Type) := (T * T) % type.

Definition Edge (e:edge tid) := LE pm (fst e) (snd e).

Definition fgraph (T:Type) := list (edge T).

(** Predicate [PhaseDiff] holds when the following list represnts the LE relation. *)
Definition PhaseDiff (g:fgraph tid) :=
  forall e, In e g <-> Edge e.

Lemma edge_dec:
  forall g,
  PhaseDiff g ->
  forall t t',
  {In (t, t') g } + { ~ In (t, t') g }.
Proof.
  intros.
  apply in_dec.
  apply pair_eq_dec.
  apply TID.eq_dec.
Qed.

Lemma LE_dec:
  forall g,
  PhaseDiff g ->
  forall t t',
  {LE pm t t'} + {~ LE pm t t'}.
Proof.
  intros.
  unfold PhaseDiff in *.
  unfold Edge in *.
  assert (Hy := H (t, t')).
  simpl in Hy.
  destruct (edge_dec _ H t t'); repeat intuition.
Qed.
End LE_DEC.


Definition Fun (pm:phasermap) :=
  forall t1 t2 p p' ph ph' i i',
  Map_PHID.MapsTo p ph pm ->
  Map_PHID.MapsTo p' ph' pm ->
  ph_diff ph t1 t2 i ->
  ph_diff ph' t1 t2 i' ->
  i = i'.

Definition Trans (pm:phasermap) :=
  forall t1 t2 t3 p p' p'' ph ph' ph'' i i' i'',
  Map_PHID.MapsTo p ph pm ->
  Map_PHID.MapsTo p' ph' pm ->
  Map_PHID.MapsTo p'' ph'' pm ->
  ph_diff ph t1 t2 i ->
  ph_diff ph' t2 t3 i' ->
  ph_diff ph'' t1 t3 i'' ->
  (i + i')%Z = i''.

Definition WF (pm:phasermap) := Fun pm /\ Trans pm.
