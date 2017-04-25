Set Implicit Arguments.

Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.SetoidList.

Require Import HJ.Vars.
Require Import HJ.Phasers.Lang.
Require Import HJ.Phasers.PhaseDiff.
Require Import HJ.Phasers.LEDec.

Require Import HJ.Phasers.TransDiff.
Require Import HJ.Phasers.Typesystem.

Require Coq.FSets.FMapFacts.

Require HJ.Phasers.PhaseDiff.
Require HJ.Phasers.Rel.
Require HJ.Phasers.SubjectReduction.
Require HJ.Phasers.Typesystem.
Require HJ.Phasers.WellFormed.

Require Import Phasers.SubjectReduction.

Module S := HJ.Phasers.Lang.

Open Scope Z.

Section SIMPLE.

Lemma progress_unblocking_simple:
  forall pm t i,
  Valid pm ->
  Check pm t i ->
  i <> WAIT_ALL ->
  exists m, Reduces pm t i m.
Proof.
  intros.
  exists (run (get_impl i) t pm).
  apply reduces.
  destruct i; simpl; inversion H0; auto.
  contradiction H1.
  trivial.
Qed.

End SIMPLE.

Section HAS_SMALLEST.
Variable pm: phasermap.
Let IsA t := In t pm.

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
  List.In t ts /\
  forall t', List.In t' ts -> (~ LE pm t t' /\ ~ LE pm t' t) \/ LE pm t t'.

Let has_smallest:
  forall ts,
  ts <> nil ->
  Forall IsA ts ->
  exists t,
  Smallest t ts.
Proof.
  intros.
  destruct (wtid_has_smallest H H0) as (x, Hx).
  unfold Rel.Smallest in *.
  unfold Rel.Unrelated in *.
  unfold wtid_le in *.
  exists x.
  auto.
Qed.

Let tids := pm_tids pm.

Let smallest_inv:
  forall t,
  Smallest t tids ->
  List.In t tids.
Proof.
  intros.
  unfold Smallest in *.
  intuition.
Qed.

Let in_tids:
  forall p ph t,
  Map_PHID.MapsTo p ph pm ->
  Map_TID.In t ph ->
  List.In t tids.
Proof.
  intros.
  unfold tids.
  rewrite pm_tids_spec.
  eauto using in_def.
Qed.

Let Smallest_to_LE :
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
  assert (Hin' : List.In t' tids) by eauto using in_tids.
  apply Hx in Hin'; clear Hx.
  destruct Hin' as [(?,?)|?].
  - destruct (LE_total _ _ _ _ _ H0 H1 H2); repeat contradiction. (* absurd *)
  - assumption.
Qed.

Let diff := pm_diff pm.

Variable check : Valid pm.

Let diff_det : TransDiffFun diff.
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
  assert (Hin: Map_TID.In t ph) by eauto using Map_TID_Extra.mapsto_to_in.
  assert (Hin': Map_TID.In t' ph) by eauto using Map_TID_Extra.mapsto_to_in.
  assert (Hle: LE pm t t') by eauto using Smallest_to_LE.
  remember ((Z.of_nat (wait_phase v)) - (Z.of_nat (wait_phase v'))) as z.
  assert (Hdiff : ph_diff ph (t, t') z). {
    subst.
    auto using ph_diff_def.
  }
  assert (Hz: (z <= 0 \/ -z <= 0) % Z) by omega.
  destruct Hz.
  - omega.
  - subst.
    remember (Z.of_nat (wait_phase v) - Z.of_nat (wait_phase v')) as z.
    assert (Hd: pm_diff pm (t, t') z) by eauto using pm_diff_def.
    assert ((z <= 0) % Z) by eauto using LE_to_pm_diff.
    intuition.
Qed.


Open Scope nat.

(**
  A crucial precondition to the wait-all working is that all tasks must have
  performed a signal prior to waiting.
*)


Import HJ.Phasers.WellFormed.

Import Phasermap.

Variable WF : WellFormed pm.

  Section Unblocked.
  Variable check_def:
    forall t,
    List.In t tids ->
    Check pm t WAIT_ALL.

  Theorem has_unblocked:
    tids <> nil ->
    exists t,
    List.In t tids /\ exists m, Reduces pm t WAIT_ALL m.
  Proof.
    intros.
    assert (Hisa : Forall IsA tids). {
      apply Forall_forall.
      intros.
      unfold IsA, tids in *.
      auto using pm_tids_spec_1.
    }
    assert (Hsmall := has_smallest H Hisa).
    destruct Hsmall as (t, Hsmall).
    exists t.
    split; auto.
    exists (Phasermap.wait_all t pm).
    apply reduces.
    simpl.
    apply wait_all_pre.
    intros.
    assert (i := H1).
    apply Map_TID_Extra.in_to_mapsto in H1.
    destruct H1 as (v, mt).
    assert (v_wf:Taskview.WellFormed v). {
      inversion WF.
      assert (Phaser.WellFormed ph) by eauto.
      inversion H2.
      eauto.
    }
    destruct (can_wait_so (mode v)). {
      apply try_wait_pre_can_wait.
      apply wait_pre_def with (v:=v); auto. {
        inversion c;
        symmetry in H2.
        - apply Taskview.wait_pre_sw; auto.
          apply Taskview.tv_well_formed_inv_sw in H2; auto.
          destruct H2; auto.
          assert (wait_phase v <> signal_phase v). {
            assert (Hk : Check pm t WAIT_ALL) by eauto.
            inversion Hk.
            assert (wait_phase v < signal_phase v) by eauto.
            intuition.
          }
          contradiction.
        - apply Taskview.wait_pre_wo; auto.
      }
      assert (Hs := mt).
      (* -- *)
      apply phase_def.
      intros x w; intros.
      assert (wait_phase w < signal_phase w). {
        assert (Hk : Check pm x WAIT_ALL). {
          eauto using in_tids, Map_TID_Extra.mapsto_to_in.
        }
        inversion Hk.
        eauto.
      }
      assert (wait_phase v <= wait_phase w). {
        eauto using Smallest_to_WaitPhase.
      }
      auto with *.
    }
    eauto using try_wait_pre_so.
  Qed.
  End Unblocked.

  Let both_cases:
    forall l,
    (forall x, List.In x l -> In x pm) ->
    (exists x, List.In x l /\ ~ Check pm x WAIT_ALL) \/
    (forall x, List.In x l -> Check pm x WAIT_ALL).
  Proof.
    induction l; intros. {
      right.
      intros.
      inversion H0.
    }
    assert (i: In a pm) by eauto using in_eq.
    destruct (check_dec pm a WAIT_ALL). {
      assert (j: forall x, List.In x l -> In x pm) by eauto using in_cons.
      apply IHl in j.
      destruct j as [(?,(?,?))|?]. {
        eauto using in_cons.
      }
      right.
      intros.
      destruct H1; subst; auto.
    }
    eauto using in_eq.
  Qed.

  Theorem progress:
    tids <> nil ->
    exists t,
    forall o,
    Check pm t o ->
    exists m, Reduces pm t o m.
  Proof.
    intros.
    edestruct (both_cases) as [(?,(?,?))|?]; eauto using pm_tids_spec_1. {
      exists x.
      intros.
      assert (o <> WAIT_ALL). {
        unfold not; intros; subst.
        contradiction.
      }
      eauto using progress_unblocking_simple.
    }
    destruct (has_unblocked) as (x,(?,?)); auto.
    exists x.
    intros.
    assert (Ho: o = WAIT_ALL \/ o <> WAIT_ALL). {
      destruct o; auto; right; unfold not; intros N; inversion N.
    }
    destruct Ho. {
      subst.
      auto.
    }
    auto using progress_unblocking_simple.
  Qed.

End HAS_SMALLEST.

Section ProgressEmpty.
  Lemma progress_empty:
    forall t o pm l,
    ReducesN pm l ->
    pm_tids pm = nil ->
    Check pm t o ->
    exists pm', Reduces pm t o pm'.
  Proof.
    intros.
    assert (O: o = WAIT_ALL \/ o <> WAIT_ALL). {
      destruct o; auto; right; unfold not; intros N; inversion N.
    }
    destruct O as [?|?]. {
      exists (run (get_impl o) t pm).
      apply reduces.
      subst; simpl.
      apply wait_all_pre.
      intros.
      assert (i: In t pm) by eauto using in_def.
      apply pm_tids_spec_2 in i.
      rewrite H0 in *.
      inversion i.
    }
    eauto using progress_unblocking_simple, reduces_n_to_valid.
  Qed.

End ProgressEmpty.

Section ProgressEx.
  Corollary progress_ex:
    forall pm l,
    ReducesN pm l ->
    pm_tids pm <> nil ->
    exists t,
    forall o,
    Check pm t o ->
    exists m, Reduces pm t o m.
  Proof.
    intros.
    eauto using progress, reduces_n_to_valid, WellFormed.Phasermap.well_formed_to_reduces_n.
  Qed.

End ProgressEx.
