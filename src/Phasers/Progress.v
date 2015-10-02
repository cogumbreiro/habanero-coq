Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.SetoidList.

Require Import HJ.Vars.
Require Import HJ.Phasers.Lang.
Require Import HJ.Phasers.PhaseDiff.
Require Import HJ.Phasers.LEDec.
Require HJ.Phasers.Rel.
Require Import HJ.Phasers.TransDiff.
Require HJ.Progress.

Module P := HJ.Progress.

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
  destruct (wtid_has_smallest _ H H0) as (x, Hx).
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
  assert (Hin' : List.In t' tids). {
    eauto using in_tids.
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

Definition AllSignalled : Prop  :=
  forall p ph,
  Map_PHID.MapsTo p ph pm ->
  forall t v,
  Map_TID.MapsTo t v ph ->
  v.(wait_phase) < v.(signal_phase).

Variable AS : AllSignalled.

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
        eauto using AS.
      }
      intuition.
    - eauto using sync_so.
  * rewrite <- Map_TID_Facts.not_find_in_iff in Heqo.
    auto using sync_skip.
Qed.

Theorem has_unblocked:
  tids <> nil ->
  exists t, List.In t tids /\
  P.CanReduce (Reduce pm) t WAIT_ALL.
Proof.
  intros.
  assert (Hisa : Forall IsA tids). {
    apply Forall_forall.
    intros.
    unfold IsA, tids in *.
    apply pm_tids_spec.
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

Require Import HJ.Phasers.Typesystem.

Require Coq.FSets.FMapFacts.
Module M := FMapFacts.WProperties_fun TID Map_TID.

Section PROGRESS.

Let async_preserves_pm:
  forall l p ph r pm t t' pm',
  ~ SetoidList.InA eq_phid (p, r) l ->
  Async pm t l t' pm' ->
  Map_PHID.MapsTo p ph pm ->
  Map_PHID.MapsTo p ph pm'.
Proof.
  intros l.
  induction l.
  - intros.
    inversion H0; subst.
    auto.
  - intros.
    inversion H0; subst; clear H0.
    apply IHl with (r:=r) (t:=t) (t':=t') (pm':=m') in H1; auto; clear IHl.
    rename p0 into p'.
    rename ph0 into ph'.
    destruct (PHID.eq_dec p p').
    + subst.
      intuition.
      assert ( InA eq_phid (p', r) ((p', r0) :: l)). {
        apply InA_cons_hd.
        unfold eq_phid.
        auto.
      }
      contradiction H0.
    + apply Map_PHID_Facts.add_neq_mapsto_iff; repeat auto.
Qed.

Lemma progress_unblocking_simple:
  forall pm t i,
  Valid pm ->
  Check t i pm ->
  i <> WAIT_ALL ->
  P.CanReduce (Reduce pm) t i.
Proof.
  intros.
  destruct i.
  - inversion H0.
    subst.
    exists (Map_PHID.add p (newPhaser t) pm).
    auto using reduce_new.
  - inversion H0.
    subst.
    exists (Map_PHID.add p (apply t signal ph) pm).
    auto using reduce_signal.
  - inversion H0; subst.
    exists (Map_PHID.add p (Map_TID.remove t ph) pm).
    auto using reduce_drop.
  - exists (mapi t signal pm).
    auto using reduce_signal_all.
  - contradiction H1; auto.
  - inversion H0; subst; clear H0.
    clear H1.
    rename t0 into t'.
    assert (Hpm : exists pm', Async pm t l t' pm'). {
      induction l.
      + exists pm.
        auto using async_nil.
      + inversion H8; subst; clear H8.
        inversion H6; subst; clear H6.
        apply IHl in H7; auto; clear IHl.
        destruct H7 as (pm', Ha).
        destruct a as (p, r).
        inversion H2; subst; clear H2.
        exists  (Map_PHID.add p (Map_TID.add t' (set_mode v r) ph0) pm').
        apply async_step; repeat auto.
        eauto using async_preserves_pm.
   }
   destruct Hpm as (pm', ?).
   exists pm'.
   auto using reduce_async.
Qed.


Variable reqs: Map_TID.t op.
Variable pm: phasermap.
Variable pm_spec: Valid pm.

Require Import HJ.Phasers.PhaseDiff.

Variable reqs_spec_1:
  forall t,
  In t pm <-> Map_TID.In t reqs.

Variable reqs_spec_2:
  forall t i,
  Map_TID.MapsTo t i reqs ->
  Check t i pm.

Let tids := pm_tids pm.  

Definition eq_wait_all (i:op) :=
  match i with
    | WAIT_ALL => true
    | _ => false
  end.

Lemma eq_wait_all_true:
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

Lemma eq_wait_all_false:
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

Lemma wait_all_dec:
  forall i,
  { i = WAIT_ALL } + { i <> WAIT_ALL }.
Proof.
  intros.
  remember (eq_wait_all i).
  symmetry in Heqb.
  destruct b.
  - rewrite eq_wait_all_true in *.
    auto.
  - rewrite eq_wait_all_false in *.
    auto.
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
  assert (Hcheck : Check t WAIT_ALL pm). {
    apply reqs_spec_2.
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
 eauto using Hin.
Qed.


Lemma progress_blocking:
  tids <> nil ->
  (forall t o, Map_TID.MapsTo t o reqs -> negb (eq_wait_all o) = false) ->
  exists t i,  Map_TID.MapsTo t i reqs /\ P.CanReduce (Reduce pm) t i.
Proof.
  intros.
  assert (AllSig: AllSignalled pm). {
    eapply all_sig.
    intros.
    apply H0 in H1.
    rewrite negb_eq_wait_all in *.
    assumption.
  }
  destruct (has_unblocked _ pm_spec AllSig H) as (t, (Hin, Hred)).
  exists t.
  assert (In t pm). {
    auto using pm_tids_spec_1.
  }
  exists WAIT_ALL.
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
  intuition.
Qed.

Theorem progress_wait_all_notin:
  forall t,
  ~ In t pm ->
  exists pm', Reduce pm t WAIT_ALL pm'.
Proof.
  intros.
  exists (mapi t wait pm).
  eapply reduce_wait_all.
  intros.
  destruct (Map_TID_Extra.in_dec tid_eq_rw t ph).
  - assert (In t pm). {
      eauto using in_def.
    }
    contradiction H1.
  - auto using sync_skip.
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

Theorem progress_blocked':
  ~ Map_TID.Empty reqs ->
  (forall t o, Map_TID.MapsTo t o reqs -> o = WAIT_ALL) ->
  exists t o,
  Map_TID.MapsTo t o reqs /\ P.CanReduce (Reduce pm) t o.
Proof.
  intros.
  assert (AllSig: AllSignalled pm). {
    auto using all_sig.
  }
  assert (Hmt: exists t, Map_TID.In t reqs). {
    apply Map_TID_Extra.nonempty_in; auto.
  }
  destruct Hmt as (t, Hin).
  assert (Hn: tids <> nil). {
    apply reqs_spec_1 in Hin.
    eauto using tids_nonempty.
  }
  rename t into t'.
  clear Hin.
  destruct (has_unblocked _ pm_spec AllSig Hn) as (t, (Hin, Hred)).
  exists t.
  assert (In t pm). {
      auto using pm_tids_spec_1.
    }
    exists WAIT_ALL.
    assert (Map_TID.MapsTo t WAIT_ALL reqs). {
      apply reqs_spec_1 in H1.
      destruct H1 as (o, Hmt).
      assert (Heq : o = WAIT_ALL). {
        apply H0 in Hmt.
        assumption.
      }
      subst.
      auto.
    }
    intuition.
Qed.
(*
Lemma progress_unblocking:
  forall (t : tid) (o : op),
  Check t o pm ->
  eq_wait_all o = false -> exists s' : phasermap, Reduce pm t o s'.
Proof.
  intros.
  rewrite eq_wait_all_false in *.
  auto using progress_unblocking_simple.
Qed.
*)
Theorem progress:
  tids <> nil ->
  exists t i,
  Map_TID.MapsTo t i reqs /\
  P.CanReduce (Reduce pm) t i.
Proof.
  intros.
  destruct (Map_TID_Extra.pred_choice reqs (fun (_:tid) (o:op) =>  negb (eq_wait_all o))); auto with *.
  - destruct e as (t, (o, (Hmt, Hneq))).
    exists t; exists o.
    intuition.
    apply progress_unblocking_simple; auto.
    rewrite <- eq_wait_all_false.
    destruct (eq_wait_all o).
    + inversion Hneq.
    + trivial.
  - auto using progress_blocking.
Qed.

End PROGRESS.

Module PhProg.
Require Import HJ.Phasers.Lang.
Require Import HJ.Phasers.PhaseDiff.
Require Import HJ.Phasers.Typesystem.
Require Import HJ.Progress.
Module R := HJ.Progress.Request.

Section  XP.
Variable pm:phasermap.
Variable is_valid: Valid pm.
Variable reqs : Map_TID.t op.
Let Check' (t:tid) (o:op) := Check t o pm.
Let In' (t:tid) := In t pm.
Variable reqs_spec :
  HJ.Progress.RequestSpec.request_spec reqs
  Check'
  In'.

Lemma pm_prog:
  @P.progress_spec op reqs Check' phasermap (Reduce pm) eq_wait_all.
Proof.
  intros.
  refine (
    @P.mk_progress_spec op reqs Check' phasermap
      (Reduce pm) eq_wait_all _ _ ); auto.
  - intros.
    rewrite eq_wait_all_false in *.
    apply progress_unblocking_simple; auto.
  - intros.
    apply progress_blocked'; auto.
    + apply (P.RequestSpec.reqs_in reqs_spec).
    + apply (P.RequestSpec.reqs_check reqs_spec).
    + intros.
      apply H0 in H1.
      rewrite eq_wait_all_true in *.
      assumption.
Defined.
Import HJ.Progress.
Lemma progress:
  ~ Map_TID.Empty reqs ->
  (** There is a task that can reduce. *)
  exists t o,
  Map_TID.MapsTo t o reqs /\ P.CanReduce (Reduce pm) t o.
Proof.
  intros.
  eauto using main_progress, pm_prog. 
Qed.
End XP.
End PhProg.
