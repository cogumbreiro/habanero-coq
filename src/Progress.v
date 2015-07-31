Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.

Require Import HJ.Vars.
Require Import HJ.Lang.
Require Import HJ.PhaseDiff.
Require Import HJ.LEDec.
Require HJ.Rel.
Require Import TransDiff.

Open Local Scope Z.

Let diff (pm:phasermap) (e:tid*tid % type) : Z -> Prop := pm_diff pm (fst e) (snd e).

(**
  Our notion of a valid phaser map is such that
  the transitive difference is a function, which means that
  any [t1 - ... - t2] yields the the same difference [z].
*)

Definition Valid (pm:phasermap) := TransDiffFun tid (diff pm).

Section HAS_SMALLEST.
Variable pm: phasermap.
Let IsA t := tid_In t pm.

Let wtid_le (t1:tid) (t2:tid) := LE pm t1 t2.

Let wtid_le_inv := LE_inv pm.

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
  Rel.has_smallest tid IsA wtid_le (LE_inv pm) (LE_dec pm)
  (LE_refl pm) wtid_le_trans.

Definition Smallest (t:tid) (ts:list tid)  :=
  In t ts /\
  forall t', In t' ts -> (~ LE pm t t' /\ ~ LE pm t' t) \/ LE pm t t'.

Theorem has_smallest:
  forall ts,
  ts <> nil ->
  Forall IsA ts ->
  exists t,
  Smallest t ts.
Proof.
  intros.
  destruct (wtid_has_smallest _ H H0) as (x, Hx).
  unfold Rel.Smallest in *.
  unfold Rel.Unrelated in *.
  unfold wtid_le in *.
  exists x.
  auto.
Qed.

Let tids := pm_tids pm.

Let tids_def:
  forall t, In t tids <-> IsA t.
Proof.
  unfold tids.
  intros.
  rewrite pm_tids_spec.
  unfold IsA.
  unfold tid_In.
  intuition.
Qed.

Let smallest_inv:
  forall t,
  Smallest t tids ->
  In t tids.
Proof.
  intros.
  unfold Smallest in *.
  intuition.
Qed.

Lemma in_tids:
  forall p ph t,
  Map_PHID.MapsTo p ph pm ->
  Map_TID.In t ph ->
  In t tids.
Proof.
  intros.
  rewrite tids_def.
  unfold IsA.
  unfold tid_In.
  exists p; exists ph.
  intuition.
Qed.

Lemma Smallest_to_LE :
  forall t t' p ph,
  Smallest t tids ->
  Map_PHID.MapsTo p ph pm ->
  Map_TID.In t ph ->
  Map_TID.In t' ph ->
  LE pm t t'.
Proof.
  intros.
  unfold Smallest in *.
  destruct H as (Hin, H).
  assert (Hx := H t'); clear H.
  assert (Hin' : In t' tids). {
    apply in_tids with (p:=p) (ph:=ph); repeat auto.
  }
  apply Hx in Hin'; clear Hx.
  destruct Hin' as [(?,?)|?].
  - destruct (LE_total _ _ _ _ _ H0 H1 H2); repeat contradiction. (* absurd *)
  - assumption.
Qed.

Let diff := diff pm.

Variable check : Valid pm.

Let diff_det : TransDiffFun tid diff.
Proof.
  unfold Valid in *.
  intuition.
Qed.

Lemma Smallest_to_WaitPhase :
  forall t t' v v' p ph,
  Smallest t tids ->
  Map_PHID.MapsTo p ph pm ->
  Map_TID.MapsTo t v ph ->
  Map_TID.MapsTo t' v' ph ->
  (wait_phase v <= wait_phase v') % nat.
Proof.
  intros.
  assert (Hin :  Map_TID.In t ph). {
    apply Map_TID_Extra.mapsto_to_in with (e:=v).
    assumption.
  }
  assert (Hin' :  Map_TID.In t' ph). {
    apply Map_TID_Extra.mapsto_to_in with (e:=v').
    assumption.
  }
  assert (Hle : LE pm t t'). {
    apply Smallest_to_LE with (p:=p) (ph:=ph); repeat auto.
  }
  remember ((Z.of_nat (wait_phase v)) - (Z.of_nat (wait_phase v'))) as z.
  assert (Hdiff : ph_diff ph t t' z). {
    subst.
    auto using ph_diff_def.
  }
  assert (Hz: (z <= 0 \/ -z <= 0) % Z). {
    omega.
  }
  destruct Hz.
  - omega.
  - subst.
    remember (Z.of_nat (wait_phase v) - Z.of_nat (wait_phase v')) as z.
    assert (Hd: pm_diff pm t t' z). { eauto using pm_diff_def. }
    assert ((z <= 0) % Z). { eauto using LE_to_pm_diff. }
    intuition.
Qed.


Open Local Scope nat.

(**
  A crucial precondition to the wait-all working is that all tasks must have
  performed a signal prior to waiting.
*)

Variable AllSignalled :
  forall p ph,
  Map_PHID.MapsTo p ph pm ->
  forall t v,
  Map_TID.MapsTo t v ph ->
  v.(wait_phase) < v.(signal_phase).

Lemma smallest_to_sync:
  forall t p ph,
  Smallest t tids ->
  Map_PHID.MapsTo p ph pm ->
  Sync ph t.
Proof.
  intros.
  remember (Map_TID.find t ph).
  symmetry in Heqo.
  destruct o as [v|].
  * rewrite <- Map_TID_Facts.find_mapsto_iff in Heqo.
    destruct (wait_cap_or_sigonly v).
    - apply sync_wait with (v:=v); repeat intuition.
      unfold Await.
      intros t' v' Hmt'.
      (* show that: n <= WP(v') *)
      assert (Hle : wait_phase v <= wait_phase v'). {
        eauto using Smallest_to_WaitPhase.
      }
      assert (wait_phase v' < signal_phase v'). {
        eauto using AllSignalled.
      }
      intuition.
    - eauto using sync_so.
  * rewrite <- Map_TID_Facts.not_find_in_iff in Heqo.
    auto using sync_skip.
Qed.

Theorem has_unblocked:
  tids <> nil ->
  exists t, In t tids /\
  exists pm', Reduce pm t WAIT_ALL pm'.
Proof.
  intros.
  assert (Hisa : Forall IsA tids). {
    apply Forall_forall.
    intros.
    apply tids_def.
    assumption.
  }
  assert (Hsmall := has_smallest _ H Hisa).
  destruct Hsmall as (t, Hsmall).
  exists t.
  intuition.
  exists (mapi t wait pm).
  apply reduce_wait_all.
  intros.
  eauto using smallest_to_sync.
Qed.
End HAS_SMALLEST.
