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

Module S := HJ.Phasers.Lang.

Open Scope Z.

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

Theorem has_smallest:
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

Lemma in_tids:
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

Definition AllSignalled : Prop  :=
  forall p ph,
  Map_PHID.MapsTo p ph pm ->
  forall t v,
  Map_TID.MapsTo t v ph ->
  wait_phase v < signal_phase v.

Variable AS : AllSignalled.

Import HJ.Phasers.WellFormed.

Import Phasermap.

Variable WF : WellFormed pm.


  (**
    Predicate [Sync] defines what happens when a
    task synchronizes with the other members of a phaser, which is triggered when
    a task performs either wait on a phaser, or next.
    The semantics of [Sync] depends on the registration mode of the task.
    Tasks registered in [SIGNAL_ONLY] mode do not block, so predicate [Sync] always
    holds. Tasks that are not registered in [SIGNAL_ONLY] mode
    (that is tasks with a wait capability) only holds once all 
    members with a signal capability issued at least as many signals as the task
    synchronizing.
   *)

  Inductive Sync : phaser -> tid -> Prop :=
  | sync_def:
    forall ph t v,
    Map_TID.MapsTo t v ph ->
    CanWait (mode v) ->
    Phase ph (S (wait_phase v)) ->
    Sync ph t.

  Definition sync x ph:
    { Sync ph x } + { ~ Sync ph x }.
  Proof.
    intros.
    remember (Map_TID.find x ph).
    symmetry in Heqo.
    destruct o as [v|]. {
      rewrite <- Map_TID_Facts.find_mapsto_iff in *.
      destruct (can_wait_so (mode v)). {
        destruct (phase ph (S (wait_phase v))). {
          eauto using sync_def.
        }
        right; unfold not; intros N; inversion N; subst; clear N;
        assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
        contradiction.
      }
      right; unfold not; intros N; inversion N; subst; clear N;
      assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      rewrite e in *.
      inversion H0.
    }
    right; unfold not; intros N.
    inversion N; subst; clear N;
    rewrite Map_TID_Facts.find_mapsto_iff in *;
    rewrite H in *;
    inversion Heqo.
  Defined.

Lemma smallest_to_sync:
  forall t p ph v,
  Smallest t tids ->
  Map_PHID.MapsTo p ph pm ->
  Map_TID.MapsTo t v ph ->
  Sync ph t \/ mode v = SIGNAL_ONLY.
Proof.
  intros.
  rename H1 into mt.
  destruct (can_wait_so(mode v)).
  - left; apply sync_def with (v:=v); auto.
    apply phase_def.
    intros t' v' Hmt'; intros.
    (* show that: n <= WP(v') *)
    assert (Hle : wait_phase v <= wait_phase v')
    by eauto using Smallest_to_WaitPhase.
    assert (wait_phase v' < signal_phase v') by eauto using AS.
    assert (wf: Taskview.WellFormed v). {
      assert (WF1: Phaser.WellFormed ph) by (inversion WF; eauto).
      inversion WF1; eauto.
    }
    destruct wf.
    + assert (wait_phase v <> signal_phase v). {
        unfold AllSignalled in *.
        assert (wait_phase v < signal_phase v) by eauto.
        intuition.
      }
      contradiction.
    + intuition.
    + apply so_to_not_can_wait in H3; contradiction.
    + intros.
      intuition. 
  - auto.
Qed.

Theorem has_unblocked:
  tids <> nil ->
  exists t, List.In t tids /\
  exists m, Reduces pm t WAIT_ALL m.
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
  intuition.
  exists (Phasermap.wait_all t pm).
  apply reduces.
  simpl.
  apply wait_all_pre.
  intros.
  unfold AllSignalled in *.
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
          assert (wait_phase v < signal_phase v) by eauto.
          intuition.
        }
        contradiction.
      - apply Taskview.wait_pre_wo; auto.
    }
    assert (Hs := mt).
    eapply smallest_to_sync in Hs; eauto.
    destruct Hs as [Hs|Hs].
    - destruct Hs.
      assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      assumption.
    - rewrite Hs in *.
      inversion c.
  }
  eauto using try_wait_pre_so.
Qed.

End HAS_SMALLEST.

Import HJ.Phasers.Typesystem.

Module M := FMapFacts.WProperties_fun TID Map_TID.

Section PROGRESS.

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

Variable reqs: Map_TID.t op.
Variable pm: phasermap.
Variable IsValid: Valid pm.

Import HJ.Phasers.PhaseDiff.

Variable reqs_spec_1:
  forall t,
  In t pm -> Map_TID.In t reqs.
(*
Variable reqs_spec_1:
  forall t,
  In t pm <-> Map_TID.In t reqs.
*)
Variable reqs_spec_3:
  forall t i,
  Map_TID.MapsTo t i reqs ->
  Check pm t i.

Import HJ.Phasers.WellFormed.

Variable WF: Phasermap.WellFormed pm.
Let tids := pm_tids pm.  


Definition eq_wait_all (i:op) :=
  match i with
    | WAIT_ALL => true
    | _ => false
  end.

Let eq_wait_all_true:
  forall i,
  eq_wait_all i = true <->
  i = WAIT_ALL.
Proof.
  intros.
  unfold eq_wait_all in *.
  split;
  ( intros;
    destruct i;
    try (inversion H || auto)).
Qed.

Let eq_wait_all_false:
  forall i,
  eq_wait_all i = false <->
  i <> WAIT_ALL.
Proof.
  intros.
  unfold eq_wait_all in *.
  split; (
    intros;
    destruct i; (
      intuition;
      inversion H0
    )
  ).
Qed.

Let negb_eq_wait_all:
  forall o,
  negb (eq_wait_all o) = false <-> o = WAIT_ALL.
Proof.
  intros.
  rewrite Bool.negb_false_iff, eq_wait_all_true.
  tauto.
Qed.

Let all_sig:
  (forall t o, Map_TID.MapsTo t o reqs -> o = WAIT_ALL) ->
  AllSignalled pm.
Proof.
  unfold AllSignalled.
  intros.
  assert (Hin : In t pm). {
    eauto using in_def, Map_TID_Extra.mapsto_to_in.
  }
  assert (Hcheck : Check pm t WAIT_ALL). {
    apply reqs_spec_3.
    apply reqs_spec_1 in Hin.
    destruct Hin as (?, Hmt).
    assert (Heq : x = WAIT_ALL). {
      apply H in Hmt.
      assumption.
    }
    subst.
    assumption.
 }
 inversion Hcheck; subst.
 eauto.
Qed.

Let eq_wait_all_dec:
  forall i,
  { i <> WAIT_ALL } + { i = WAIT_ALL }.
Proof.
  intros.
  destruct i;
  try (left; intuition; inversion H; assumption).
  right; auto.
Defined.

Let check_pm_inv_in:
  forall t i,
  Map_TID.MapsTo t i reqs ->
  ~ In t pm ->
  exists m, Reduces pm t i m.
Proof.
  intros.
  assert (Check pm t i) by eauto.
  destruct (eq_wait_all_dec i).
  - eauto using progress_unblocking_simple.
  - subst.
    exists (wait_all t pm).
    apply reduces.
    simpl.
    apply wait_all_pre.
    intros.
    contradiction H0.
    eauto using in_def.
Qed.

Let nonempty_to_tids_not_nil:
  ~ Map_TID.Empty reqs ->
  (exists t i m, Map_TID.MapsTo t i reqs /\ Reduces pm t i m) \/ (tids <> nil /\ (forall t o, Map_TID.MapsTo t o reqs -> o = WAIT_ALL)).
Proof.
  intros.
  destruct (Map_TID_Extra.pred_choice reqs (fun (_:tid) (o:op) =>  negb (eq_wait_all o))); auto with *.
  - destruct e as (t, (o, (mt, He))).
    rewrite Bool.negb_true_iff in *.
    apply eq_wait_all_false in He.
    left.
    exists t.
    exists o.
    assert (Check pm t o) by eauto.
    assert (R: exists m, Reduces pm t o m) by eauto using progress_unblocking_simple.
    destruct R as (m, O).
    eauto.
  -
  apply Map_TID_Extra.nonempty_in in H.
  destruct H as (t, Hin).
  apply Map_TID_Extra.in_to_mapsto in Hin.
  destruct Hin as (i, mt).
    destruct (in_dec pm t).
    + apply pm_tids_spec_2 in i0.
      right.
      split. {
        intuition.
        unfold tids in *.
        rewrite H in *.
        contradiction.
      }
      intros.
      assert (Hx: negb (eq_wait_all o) = false) by eauto.
      rewrite Bool.negb_false_iff in Hx.
      apply eq_wait_all_true in Hx.
      assumption.
    + left.
      exists t.
      exists i.
      assert (Hx : exists m, Reduces pm t i m) by eauto.
      destruct Hx as (m, Hx).
      eauto.
Qed.

Lemma progress_blocking:
  ~ Map_TID.Empty reqs ->
  (forall t o, Map_TID.MapsTo t o reqs -> negb (eq_wait_all o) = false) ->
  exists t i m, Map_TID.MapsTo t i reqs /\ Reduces pm t i m.
Proof.
  intros.
  assert (AllSig: AllSignalled pm). {
    eapply all_sig.
    intros.
    apply H0 in H1.
    rewrite negb_eq_wait_all in *.
    assumption.
  }
  destruct (nonempty_to_tids_not_nil H); auto.
  destruct H1 as (Hnil, Hall).
  destruct (has_unblocked IsValid AllSig WF Hnil) as (t, (Hin, (m, Hred))).
  exists t.
  assert (In t pm). {
    auto using pm_tids_spec_1.
  }
  exists WAIT_ALL.
  exists m.
  assert (Map_TID.MapsTo t WAIT_ALL reqs). {
    apply reqs_spec_1 in H1.
    destruct H1 as (o, Hmt).
    assert (Heq : o = WAIT_ALL). {
      eauto.
    }
    subst.
    auto.
  }
  auto using reduces.
Qed.

Lemma tids_nonempty:
  forall t,
  In t pm -> tids <> nil.
Proof.
  intros.
  unfold tids.
  apply pm_tids_nonempty.
  exists t.
  assumption.
Qed.

Theorem progress:
  ~ Map_TID.Empty reqs ->
  exists t i m,
  Map_TID.MapsTo t i reqs /\ Reduces pm t i m.
Proof.
  intros.
  destruct (Map_TID_Extra.pred_choice reqs (fun (_:tid) (o:op) =>  negb (eq_wait_all o))); auto with *.
  - destruct e as (t, (o, (Hmt, Hneq))).
    exists t; exists o.
    assert (R : exists m, Reduces pm t o m). {
      apply Bool.negb_true_iff in Hneq.
      rewrite eq_wait_all_false in Hneq.
      auto using progress_unblocking_simple, IsValid, reqs_spec_3.
    }
    destruct R as (m, R).
    exists m.
    intuition.
  - eauto using progress_blocking.
Qed.
End PROGRESS.
Module ProgressSpec.

  Import HJ.Phasers.SubjectReduction.
  Import HJ.Phasers.WellFormed.
  Import HJ.Phasers.Typesystem.
  Import WellFormed.Phasermap.

  Section ValidPRequest.
    Set Implicit Arguments.
    Unset Strict Implicit.

    Structure phasermap_t := {
      pm_t_value: phasermap;
      pm_t_spec_1: Valid pm_t_value;
      pm_t_spec_2: WellFormed pm_t_value
    }.
    Variable pm:phasermap.
    Structure pm_request := {
      pm_request_value: Map_TID.t Phasermap.op;
      pm_request_spec_1: forall t : tid, In t pm -> Map_TID.In t pm_request_value;
      pm_request_spec_2: forall t i, Map_TID.MapsTo t i pm_request_value -> Phasers.Typesystem.Check pm t i;
      pm_request_spec_3: ~ Map_TID.Empty pm_request_value
    }.
  End ValidPRequest.


  Let progress_aux:
    forall (m: phasermap_t) (r:pm_request (pm_t_value m)),
    exists t i m', Map_TID.MapsTo t i (pm_request_value r) /\ Reduces (pm_t_value m) t i m'.
  Proof.
    intros.
    destruct m.
    destruct r.
    simpl in *.
    eauto using progress.
  Qed.

  Lemma progress:
    forall (m: phasermap_t) (r:pm_request (pm_t_value m)),
    exists t i (m':phasermap_t), Map_TID.MapsTo t i (pm_request_value r) /\ Reduces (pm_t_value m) t i (pm_t_value m').
  Proof.
    intros.
    destruct (@progress_aux m r) as (t, (i, (pm, (mt, R)))).
    assert (V: Valid pm) by eauto using subject_reduction, pm_t_spec_1.
    assert (W: WellFormed pm) by eauto using pm_reduces_preserves_well_formed, pm_t_spec_2.
    remember ({| pm_t_value := pm; pm_t_spec_1 := V; pm_t_spec_2:= W |}) as m'.
    exists t.
    exists i.
    exists m'.
    subst.
    intuition.
  Qed.
End ProgressSpec.
