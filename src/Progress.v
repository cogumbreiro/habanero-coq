Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.SetoidList.

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
(*
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
*)
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
  exists t, List.In t tids /\
  exists pm', Reduce pm t WAIT_ALL pm'.
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

Require Import HJ.Typesystem.

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

Lemma progress_simple:
  forall pm t i,
  Valid pm ->
  Check t i pm ->
  i <> WAIT_ALL ->
  exists pm',
  Reduce pm t i pm'.
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

Require Import HJ.PhaseDiff.

Variable reqs_spec_1:
  forall t,
  In t pm -> (exists i, Map_TID.MapsTo t i reqs).

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
(*
Theorem progress_blocked:
  (forall t o, Map_TID.MapsTo t o reqs -> o = WAIT_ALL) ->
  exists t o,
  Map_TID.MapsTo t o reqs /\ (exists pm' : phasermap, Reduce pm t o pm').
Proof.
  intros.
  
Qed.
*)
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

Lemma i_case:
  (exists t i, Map_TID.MapsTo t i reqs /\ i <> WAIT_ALL)
  \/
  (forall t, Map_TID.In t reqs -> Map_TID.MapsTo t WAIT_ALL reqs).
Proof.
  intros.
  remember (snd (M.partition (fun (t:tid) => eq_wait_all) reqs)).
  destruct (Map_TID_Extra.in_choice y).
  - left.
    destruct e as (t, Hin).
    apply Map_TID_Extra.in_to_mapsto in Hin.
    destruct Hin as (i, Hin).
    exists t.
    exists i.
    apply M.partition_iff_2 with (k:=t) (e:=i) in Heqy; auto with *.
    apply Heqy in Hin; clear Heqy.
    destruct Hin.
    rewrite eq_wait_all_false  in H0.
    intuition.
  - right.
    intros.
    apply Map_TID_Extra.in_to_mapsto in H.
    destruct H as (i, Hmt).
    destruct (wait_all_dec i).
    + subst; assumption.
    + (* absurd case *)
      assert (exists (k:tid), Map_TID.In (elt:=op) k y). {
        exists t.
        apply M.partition_iff_2 with (k:=t) (e:=i) in Heqy; auto with *.
        apply Map_TID_Extra.mapsto_to_in with (e:=i).
        rewrite Heqy.
        rewrite eq_wait_all_false.
        intuition.
      }
      contradiction H.
Qed.

Theorem progress:
  tids <> nil ->
  exists t i,
  Map_TID.MapsTo t i reqs /\
  exists pm', Reduce pm t i pm'.
Proof.
  intros.
  destruct i_case.
  - destruct H0 as (t, (i, (Hmt, Hneq))).
    exists t; exists i.
    intuition.
    apply progress_simple; auto.
  - assert (AllSig: forall p ph,
            Map_PHID.MapsTo p ph pm ->
            forall t v,
            Map_TID.MapsTo t v ph ->
            (wait_phase v < signal_phase v)%nat). {
      intros.
      assert (In t pm). {
        eauto using in_def, Map_TID_Extra.mapsto_to_in.
      }
      assert (Hcheck : Check t WAIT_ALL pm). {
        apply reqs_spec_2.
        apply reqs_spec_1 in H3.
        apply H0.
        destruct H3 as (?, H3).
        eauto using Map_TID_Extra.mapsto_to_in.
     }
     inversion Hcheck; subst.
     eauto using H4.
    }
    destruct (has_unblocked _ pm_spec AllSig H) as (t, (Hin, Hred)).
    exists t.
    exists WAIT_ALL.
    assert (In t pm). {
      auto using pm_tids_spec_1.
    }
    apply reqs_spec_1 in H1.
    destruct H1 as (i, Hmt).
    apply Map_TID_Extra.mapsto_to_in in Hmt.
    apply H0 in Hmt.
    intuition.
Qed.

End PROGRESS.
