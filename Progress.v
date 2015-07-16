Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.

Require Import Vars.
Require Import Lang.
Require Import PhaseDiff.
Require Import LEDec.
Require Rel.

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

Variable pm_diff_fun:
  forall t t' z z',
  pm_diff pm t t' z ->
  pm_diff pm t t' z' ->
  z = z'.

Variable pm_diff_trans:
  forall t1 t2 t3 z12 z23 z13,
  pm_diff pm t1 t2 z12 ->
  pm_diff pm t2 t3 z23 ->
  pm_diff pm t1 t3 z13 ->
  (z12 + z23 = z13) % Z.

Lemma LE_to_pm_diff:
  forall t1 t2,
  LE pm t1 t2 ->
  forall z,
  pm_diff pm t1 t2 z ->
  (z <= 0) %Z.
Proof.
  intros ? ? H.
  induction H.
  - intros.
    inversion H; subst.
    apply pm_diff_fun with (z:=z) in H1; repeat (auto;intuition).
  - intros z' ?.
    destruct (pm_diff_dec pm x y), (pm_diff_dec pm y z).
    + destruct e as (z1, ?); destruct e0 as (z2, ?).
      assert ((z1 + z2) % Z = z'). {
        apply pm_diff_trans with (t1:=x) (t2:=y) (t3:=z); repeat auto.
      }
      apply IHclos_trans1 in H2.
      apply IHclos_trans2 in H3.
      intuition.
    +
Admitted.

(* TODO: prove this *)
Lemma Smallest_to_WaitPhase :
  forall t t' v v' p ph n n',
  Smallest t tids ->
  Map_PHID.MapsTo p ph pm ->
  Map_TID.MapsTo t v ph ->
  Map_TID.MapsTo t' v' ph ->
  WaitPhase v n ->
  WaitPhase v' n' ->
  n <= n'.
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
  remember ((Z.of_nat n) - (Z.of_nat n'))%Z as z.
  assert (Hdiff : ph_diff ph t t' z). {
    subst.
    apply ph_diff_def with (v1:=v) (v2:=v'); repeat auto.
  }
  assert (Hz: (z <= 0 \/ -z <= 0) % Z). {
    omega.
  }
  destruct Hz.
  - omega.
  - subst.
    remember (Z.of_nat n - Z.of_nat n')%Z as z.
    assert (Hd: pm_diff pm t t' z). {
      apply pm_diff_def with (p:=p) (ph:=ph); repeat auto.
    }
    assert (Hel := LE_to_pm_diff _ _ Hle _ Hd).
    intuition.
Qed.

(* XXX: move this into a proposition *)
Variable OnlySW :
  forall (ph:phaser) (t:tid) (v:taskview),
  Map_TID.MapsTo t v ph ->
  exists n, v = SW n true \/ v = WO n \/ exists w, (v = SO n w /\ w < n).

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
    - destruct (get_wait_phase v) as (n, Hwp).
      apply sync_wait with (v:=v) (w:=n); repeat intuition.
      unfold Await.
      intros t' v' n' Hmt' Hsp.
      destruct (OnlySW ph _ _ Hmt') as (n'', [Heq|[Heq|(w, (Heq, Hw))]]).
      + (* v' is SW *)
        subst.
        inversion Hsp.
        subst.
        (* WP of v' *)
        assert (Hwait : WaitPhase (SW n'' true) n''). {
          apply wait_phase_sw.
        }
        (* show that: n <= WP(v') *)
        assert (Hle : n <= n''). {
          apply Smallest_to_WaitPhase with
          (t:=t) (t':=t') (v:=v) (v':=(SW n'' true))
          (p:=p) (ph:=ph); repeat auto.
        }
        intuition.
      + (* v' is WO *)
        subst. (* absurd *)
        inversion Hsp.
      + (* v' is SO *)
        subst.
        inversion Hsp.
        subst.
        assert (Hwait : WaitPhase (SO n' w) w). {
          apply wait_phase_so.
        }
        (* show that: n <= WP(v') *)
        assert (Hle : n <= w). {
          apply Smallest_to_WaitPhase with
          (t:=t) (t':=t') (v:=v) (v':=(SO n' w))
          (p:=p) (ph:=ph); repeat auto.
       }
       intuition.
    - apply sync_so with (v:=v); repeat auto.
  * rewrite <- Map_TID_Facts.not_find_in_iff in Heqo.
    apply sync_skip.
    assumption.
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
  apply smallest_to_sync with (p:=p) ; repeat auto.
Qed.
End HAS_SMALLEST.


