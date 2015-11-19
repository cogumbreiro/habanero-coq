Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.SetoidList.

Require Import HJ.Vars.
Require Import HJ.Phasers.Lang.
Require Import HJ.Phasers.PhaseDiff.
Require Import HJ.Phasers.LEDec.
Require HJ.Phasers.Rel.
Require Import HJ.Phasers.TransDiff.
Require Import HJ.Phasers.Typesystem.

Module S := HJ.Phasers.Lang.

Open Local Scope Z.

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
  assert (Hin: Map_TID.In t ph) by eauto using Map_TID_Extra.mapsto_to_in.
  assert (Hin': Map_TID.In t' ph) by eauto using Map_TID_Extra.mapsto_to_in.
  assert (Hle: LE pm t t') by eauto using Smallest_to_LE.
  remember ((Z.of_nat (wait_phase v)) - (Z.of_nat (wait_phase v'))) as z.
  assert (Hdiff : ph_diff ph t t' z). {
    subst.
    auto using ph_diff_def.
  }
  assert (Hz: (z <= 0 \/ -z <= 0) % Z) by omega.
  destruct Hz.
  - omega.
  - subst.
    remember (Z.of_nat (wait_phase v) - Z.of_nat (wait_phase v')) as z.
    assert (Hd: pm_diff pm t t' z) by eauto using pm_diff_def.
    assert ((z <= 0) % Z) by eauto using LE_to_pm_diff.
    intuition.
Qed.


Open Local Scope nat.

(**
  A crucial precondition to the wait-all working is that all tasks must have
  performed a signal prior to waiting.
*)

Definition AllSignalled : Prop  :=
  forall p ph,
  Map_PHID.MapsTo p ph pm ->
  forall t v,
  Map_TID.MapsTo t v ph ->
  v.(wait_phase) < v.(signal_phase).

Variable AS : AllSignalled.

Require Import HJ.Phasers.Welformedness.

Import Phasermap.

Variable WF : Welformed pm.

Lemma smallest_to_sync:
  forall t p ph,
  Smallest t tids ->
  Map_PHID.MapsTo p ph pm ->
  Map_TID.In t ph ->
  Sync ph t.
Proof.
  intros.
  apply Map_TID_Extra.in_to_mapsto in H1.
  destruct H1 as (v, mt).
  destruct (wait_cap_so_dec (mode v)).
  - apply sync_wait with (v:=v); auto.
    apply await_def. 
    intros t' v' Hmt'.
    (* show that: n <= WP(v') *)
    assert (Hle : wait_phase v <= wait_phase v')
    by eauto using Smallest_to_WaitPhase.
    assert (wait_phase v' < signal_phase v')
    by eauto using AS.
    assert (wf: Taskview.Welformed v). {
      assert (WF1: Phaser.Welformed ph) by (inversion WF; eauto).
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
    + apply so_to_not_wait_cap in H2; contradiction.
  - eauto using sync_so.
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
  eauto using wait_pre, Taskview.wait_pre, smallest_to_sync.
Qed.
End HAS_SMALLEST.

Require Import HJ.Phasers.Typesystem.

Require Coq.FSets.FMapFacts.
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

Structure state := {
  get_requests : Map_TID.t op;
  get_state : phasermap;
  IsValid : Valid get_state;
  reqs_spec_1: forall t, In t get_state -> Map_TID.In t get_requests;
  reqs_spec_2: forall t, Map_TID.In t get_requests ->  In t get_state;
  reqs_spec_3: forall t i, Map_TID.MapsTo t i get_requests -> Check get_state t i
}.

Inductive RReduce (s:state) (t:tid) (o:op) (m:phasermap) : Prop :=
  r_reduce_def:
    Map_TID.MapsTo t o (get_requests s) ->
    Reduces (get_state s) t o m ->
    RReduce s t o m.

Variable s:state.

(*
Variable reqs: Map_TID.t op.
Variable pm: phasermap.
Variable pm_spec: Valid pm.
*)
Require Import HJ.Phasers.PhaseDiff.
(*
Variable reqs_spec_1:
  forall t,
  In t pm <-> Map_TID.In t reqs.

Variable reqs_spec_2:
  forall t i,
  Map_TID.MapsTo t i reqs ->
  Check pm t i.
*)
Notation pm := (get_state s).
Notation reqs := (get_requests s).

Require Import HJ.Phasers.Welformedness.

Variable WF: Phasermap.Welformed pm.
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

Lemma negb_eq_wait_all:
  forall o,
  negb (eq_wait_all o) = false <-> o = WAIT_ALL.
Proof.
  intros.
  rewrite Bool.negb_false_iff, eq_wait_all_true.
  tauto.
Qed.

Lemma all_sig:
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
 assert (Taskview.WaitPre v) by eauto.
 inversion H3; auto.
Qed.

Lemma nonempty_to_tids_not_nil:
  ~ Map_TID.Empty reqs ->
  tids <> nil.
Proof.
  intros.
  apply Map_TID_Extra.nonempty_in in H.
  destruct H as (t, Hin).
  intuition.
  apply reqs_spec_2 in Hin.
  unfold tids in *.
  apply pm_tids_spec_2 in Hin.
  rewrite H in *.
  inversion Hin.
Qed.

Lemma progress_blocking:
  ~ Map_TID.Empty reqs ->
  (forall t o, Map_TID.MapsTo t o reqs -> negb (eq_wait_all o) = false) ->
  exists t i m, RReduce s t i m.
Proof.
  intros.
  assert (AllSig: AllSignalled pm). {
    eapply all_sig.
    intros.
    apply H0 in H1.
    rewrite negb_eq_wait_all in *.
    assumption.
  }
  assert (Hnil : tids <> nil). {
    auto using nonempty_to_tids_not_nil.
  }
  destruct (has_unblocked (IsValid s) AllSig WF Hnil) as (t, (Hin, (m, Hred))).
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
      apply H0 in Hmt.
      rewrite negb_eq_wait_all in Hmt.
      assumption.
    }
    subst.
    auto.
  }
  auto using r_reduce_def.
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
  RReduce s t i m.
Proof.
  intros.
  destruct (Map_TID_Extra.pred_choice reqs (fun (_:tid) (o:op) =>  negb (eq_wait_all o))); auto with *.
  - destruct e as (t, (o, (Hmt, Hneq))).
    exists t; exists o.
    intuition.
    assert (R : exists m, Reduces pm t o m). {
      apply Bool.negb_true_iff in Hneq.
      rewrite eq_wait_all_false in Hneq.
      auto using progress_unblocking_simple, IsValid, reqs_spec_3.
    }
    destruct R as (m, R).
    exists m.
    auto using r_reduce_def.
  - auto using progress_blocking.
Qed.
End PROGRESS.
