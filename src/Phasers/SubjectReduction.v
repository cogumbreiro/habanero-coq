Require Import HJ.Phasers.Progress.
Require Import HJ.Phasers.Lang.
Require Import HJ.Phasers.TransDiff.
Require Import HJ.Phasers.PhaseDiff.
Require Import HJ.Phasers.Typesystem.
Require Import HJ.Vars.

Require Import Aniceto.Graphs.Graph.
Require Import Aniceto.Pair.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.

Section SR.


Definition tid_eq_sig x y := if TID.eq_dec x y then 1%Z else 0%Z.

Definition wait_delta t e := ((tid_eq_sig (snd e) t) - (tid_eq_sig (fst e) t)) % Z.

Lemma wait_delta_refl:
  forall t t',
  wait_delta t (t', t') = 0%Z.
Proof.
  intros.
  unfold wait_delta, tid_eq_sig.
  simpl.
  destruct (TID.eq_dec t' t); intuition.
Qed.

Lemma wait_delta_left:
  forall t t',
  t <> t' ->
  wait_delta t (t, t') = (- 1)%Z.
Proof.
  intros.
  unfold wait_delta, tid_eq_sig.
  simpl.
  destruct (TID.eq_dec t' t), (TID.eq_dec t t); intuition.
Qed.

Lemma wait_delta_right:
  forall t t',
  t <> t' ->
  wait_delta t (t', t) = 1%Z.
Proof.
  intros.
  unfold wait_delta, tid_eq_sig.
  simpl.
  destruct (TID.eq_dec t' t), (TID.eq_dec t t); intuition.
Qed.

Lemma wait_delta_neq:
  forall t t1 t2,
  t <> t1 ->
  t <> t2 ->
  wait_delta t (t1, t2) = 0%Z.
Proof.
  intros.
  unfold wait_delta, tid_eq_sig.
  simpl.
  destruct (TID.eq_dec t1 t), (TID.eq_dec t2 t); intuition.
Qed.

Lemma wait_phase_wait:
  forall v,
  wait_phase (Taskview.wait v) = S (wait_phase v).
Proof.
  intros.
  unfold wait.
  simpl.
  intuition.
Qed.

Lemma Z_add_to_succ:
  forall p,
  Pos.add p xH = Pos.succ p.
Proof.
  intros.
  destruct p; repeat auto.
Qed.

Lemma Z_of_nat_succ:
  forall (n:nat),
  Z.of_nat (S n) = ((Z.of_nat n) + 1) % Z.
Proof.
 intros.
 unfold Z.of_nat.
 destruct n.
 - auto.
 - simpl.
   rewrite Z_add_to_succ.
   trivial.
Qed.

Lemma ph_diff_add_wait:
  forall t t1 t2 z v ph,
  ph_diff (Map_TID.add t (Taskview.wait v) ph) t1 t2 z ->
  Map_TID.MapsTo t v ph ->
  ph_diff ph t1 t2 (z + wait_delta t (t1, t2)).
Proof.
  intros.
    inversion H; subst; clear H.
    rewrite Map_TID_Facts.add_mapsto_iff in *.
    destruct H1 as [(?,?)|(?,?)].
    + destruct H2 as [(?,?)|(?,?)].
      * subst.
        subst.
        rewrite wait_delta_refl.
        remember (Z.of_nat (wait_phase (Taskview.wait v))) as z.
        assert (Heq: ((z - z + 0 = 0) %Z)). {
          intuition.
        }
        rewrite Heq.
        eauto using Map_TID_Extra.mapsto_to_in, ph_diff_refl.
      * subst.
        rewrite wait_delta_left; auto.
        rewrite wait_phase_wait.
        rewrite Z_of_nat_succ.
        assert (Heq:
          (Z.of_nat (wait_phase v) + 1 - Z.of_nat (wait_phase v2) + -1 =
          (Z.of_nat (wait_phase v) - Z.of_nat (wait_phase v2))) % Z). {
          intuition.
        }
        rewrite Heq.
        auto using ph_diff_def.
    + destruct H2 as [(?,?)|(?,?)].
      * subst.
        rewrite wait_delta_right; auto.
        rewrite wait_phase_wait.
        rewrite Z_of_nat_succ.
        assert (Heq: (
          (Z.of_nat (wait_phase v1) - (Z.of_nat (wait_phase v) + 1) + 1) =
          (Z.of_nat (wait_phase v1) - (Z.of_nat (wait_phase v)))) % Z). {
          intuition.
        }
        rewrite Heq.
        auto using ph_diff_def.
      * rewrite wait_delta_neq; repeat auto.
        assert (Heq: (
          (Z.of_nat (wait_phase v1) - Z.of_nat (wait_phase v2) + 0) =
          (Z.of_nat (wait_phase v1) - Z.of_nat (wait_phase v2))) % Z). {
          intuition.
        }
        rewrite Heq; auto using ph_diff.
Qed.

Lemma in_neq:
  forall t t1 ph,
  ~ Map_TID.In (elt:=taskview) t ph ->
  Map_TID.In (elt:=taskview) t1 ph ->
  t <> t1.
Proof.
  intros.
  destruct (TID.eq_dec t t1); repeat auto.
  subst.
  contradiction.
Qed.

Lemma ph_wait_in:
  forall t t' ph,
  Map_TID.In t (wait t' ph) ->
  Map_TID.In t ph.
Proof.
  intros.
  apply Map_TID_Extra.in_to_mapsto in H.
  destruct H as (v, mt).
  unfold wait, Phaser.update in *.
  remember (Map_TID.find _ _).
  symmetry in Heqo.
  destruct o as [v'|].
  - apply Map_TID_Facts.add_mapsto_iff in mt.
    rewrite <- Map_TID_Facts.find_mapsto_iff in Heqo.
    destruct mt.
    + destruct H.
      subst.
      eauto using Map_TID_Extra.mapsto_to_in.
    + destruct H; eauto using Map_TID_Extra.mapsto_to_in.
  - eauto using Map_TID_Extra.mapsto_to_in.
Qed.

Lemma ph_diff_apply_wait:
  forall t t1 t2 z ph,
  ph_diff (wait t ph) t1 t2 z ->
  ph_diff ph t1 t2 (z + wait_delta t (t1, t2)).
Proof.
  intros.
  remember (Map_TID.find t ph).
  symmetry in Heqo.
  destruct o as [v|].
  - apply Map_TID_Facts.find_mapsto_iff in Heqo.
    assert (R:=Heqo).
    apply ph_wait_rw in R; rewrite R in *.
    eauto using ph_diff_add_wait.
 - unfold wait, Phaser.update in *.
   rewrite Heqo in *.
   rewrite <- Map_TID_Facts.not_find_in_iff in Heqo.
   assert (t <> t1). {
     apply ph_diff_inv_left in H.
     intuition; subst.
     contradiction.
   }
   assert (t <> t2). {
     apply ph_diff_inv_right in H.
     intuition; subst.
     contradiction.
   }
   rewrite wait_delta_neq; repeat auto.
   assert (Heq: ((z + 0 = z) % Z)); intuition.
   rewrite Heq.
   assumption.
Qed.

Lemma pm_diff_wait_all:
  forall t t1 t2 z pm,
  pm_diff (wait_all t pm) t1 t2 z ->
  pm_diff pm t1 t2 (z + wait_delta t (t1, t2)).
Proof.
  intros.
  inversion H; subst; clear H.
  unfold foreach in *.
  apply Map_PHID_Facts.mapi_inv in H0.
  destruct H0 as (ph', (p', (?, (?, ?)))).
  subst.
  rename ph' into ph.
  eauto using ph_diff_apply_wait, pm_diff_def.
Qed.

Lemma diff_wait_all:
  forall t e z pm,
  diff (wait_all t pm) e z ->
  diff pm e (z + wait_delta t e).
Proof.
  intros.
  unfold diff in *.
  destruct e as (t1, t2).
  simpl in *.
  auto using pm_diff_wait_all.
Qed.

Lemma walk2_wait_all:
  forall t pm t1 t2 w,
  Walk2 (HasDiff (diff (wait_all t pm))) t1 t2 w ->
  Walk2 (HasDiff (diff pm)) t1 t2 w.
Proof.
  intros.
  apply walk2_impl with (E:=HasDiff (diff (wait_all t pm))); repeat auto.
  intros.
  unfold HasDiff in *.
  destruct e as (ta, tb).
  destruct H0 as (z, ?).
  eauto using diff_wait_all.
Qed.

Lemma pm_diff_mapi_sig:
  forall t t1 t2 pm z,
  pm_diff (wait_all t pm) t1 t2 z ->
  pm_diff pm t1 t2 (z - (tid_eq_sig t1 t) + (tid_eq_sig t2 t)).
Proof.
  intros.
  assert (Heq: ((z - tid_eq_sig t1 t + tid_eq_sig t2 t) = (z + wait_delta t (t1, t2))) %Z). {
    unfold wait_delta.
    simpl.
    intuition.
  }
  rewrite Heq.
  eauto using pm_diff_wait_all.
Qed.

Lemma diff_sum_wait_all:
  forall w t t1 tn pm z,
  DiffSum (diff (wait_all t pm)) w z ->
  StartsWith w t1 ->
  EndsWith w tn ->
  DiffSum (diff pm) w (z - (tid_eq_sig t1 t) + (tid_eq_sig tn t)).
Proof.
  intros w.
  induction w.
  { (* absurd case *)
    intros.
    inversion H; subst.
    apply ends_with_nil_inv in H1.
    inversion H1.
  }
  intros.
  destruct a as (t1', t2).
  assert (t1' = t1). { eauto using starts_with_eq. }
  destruct w.
  - subst.
    inversion H.
    subst.
    assert (t2 = tn). {
      eauto using ends_with_eq.
    }
    subst.
    apply pm_diff_mapi_sig in H5.
    auto using diff_sum_pair.
  - subst.
    destruct p as (t2', t3).
    inversion H; subst; clear H.
    rename t2' into t2.
    assert (StartsWith ((t2, t3) :: w) t2). {
      eauto using starts_with_def.
    }
    apply ends_with_inv in H1.
    assert ( DiffSum (diff pm) ((t2, t3) :: w) (s - tid_eq_sig t2 t + tid_eq_sig tn t)). {
      apply IHw; repeat auto.
    }
    apply pm_diff_mapi_sig in H9. (* invert diff_mapi *)
    simpl in *.
    assert (Heq: ((z0 + s - tid_eq_sig t1 t + tid_eq_sig tn t) =
          (z0 - tid_eq_sig t1 t + tid_eq_sig t2 t) +
          (s - tid_eq_sig t2 t + tid_eq_sig tn t)) % Z). { intuition. }
    rewrite Heq.
    auto using diff_sum_cons.
Qed.

Lemma transdiff_wait_all:
  forall t pm t1 t2 z,
  TransDiff tid (diff (wait_all t pm)) t1 t2 z ->
  TransDiff tid (diff pm) t1 t2 (z - (tid_eq_sig t1 t) + (tid_eq_sig t2 t)).
Proof.
  intros.
  inversion H; subst; clear H.
  apply walk2_wait_all in H1.
  inversion H1; subst.
  apply diff_sum_wait_all with (t1:=t1) (tn:=t2) in H0; repeat auto.
  eauto using trans_diff_def.
Qed.

Lemma wait_all_sr:
  forall pm t,
  Valid pm ->
  Valid (wait_all t pm).
Proof.
  unfold Valid in *.
  unfold TransDiffFun in *.
  intros.
  apply transdiff_wait_all in H0.
  apply transdiff_wait_all in H1.
  assert (Hx := H _ _ _ _ H0 H1).
  intuition.
Qed.

Section PreservesDiff.
Variable f : phasermap -> phasermap.

Variable preserves_ph_diff:
  forall p ph pm z t1 t2,
  ph_diff ph t1 t2 z ->
  Map_PHID.MapsTo p ph (f pm) ->
  exists ph', Map_PHID.MapsTo p ph' pm /\ ph_diff ph' t1 t2 z.

Let preserves_pm_diff:
  forall t1 t2 z pm,
  pm_diff (f pm) t1 t2 z ->
  pm_diff pm t1 t2 z.
Proof.
  intros.
  inversion H; subst; clear H.
  apply preserves_ph_diff with (z:=z) (t1:=t1) (t2:=t2) in H0; auto.
  destruct H0 as (ph', (mt, d)).
  eauto using pm_diff_def.
Qed.

Let preserves_diff:
  forall e z pm,
  diff (f pm) e z ->
  diff pm e z.
Proof.
  intros.
  unfold diff in *.
  destruct e as (t1, t2).
  simpl in *.
  auto using preserves_pm_diff.
Qed.

Let preserves_walk2:
  forall pm t1 t2 w,
  Walk2 (HasDiff (diff (f pm))) t1 t2 w ->
  Walk2 (HasDiff (diff pm)) t1 t2 w.
Proof.
  intros.
  apply walk2_impl with (E:=HasDiff (diff (f pm))); repeat auto.
  intros.
  unfold HasDiff in *.
  destruct e as (ta, tb).
  destruct H0 as (z, ?).
  eauto using preserves_diff.
Qed.

Let preserves_diff_sum:
  forall w t1 tn pm z,
  DiffSum (diff (f pm)) w z ->
  StartsWith w t1 ->
  EndsWith w tn ->
  DiffSum (diff pm) w z.
Proof.
  intros w.
  induction w.
  { (* absurd case *)
    intros.
    inversion H; subst.
    apply ends_with_nil_inv in H1.
    inversion H1.
  }
  intros.
  destruct a as (t1', t2).
  assert (t1' = t1). { eauto using starts_with_eq. }
  destruct w.
  - subst.
    inversion H.
    subst.
    assert (t2 = tn). {
      eauto using ends_with_eq.
    }
    subst.
    apply preserves_pm_diff in H5.
    auto using diff_sum_pair.
  - subst.
    destruct p as (t2', t3).
    inversion H; subst; clear H.
    rename t2' into t2.
    assert (StartsWith ((t2, t3) :: w) t2). {
      eauto using starts_with_def.
    }
    apply ends_with_inv in H1.
    assert ( DiffSum (diff pm) ((t2, t3) :: w) s) by eauto.
    apply preserves_pm_diff in H9. (* invert diff_mapi *)
    simpl in *.
    auto using diff_sum_cons.
Qed.

Let preserves_transdiff:
  forall pm t1 t2 z,
  TransDiff tid (diff (f pm)) t1 t2 z ->
  TransDiff tid (diff pm) t1 t2 z.
Proof.
  intros.
  inversion H; subst; clear H.
  apply preserves_walk2 in H1.
  inversion H1; subst.
  apply preserves_diff_sum with (t1:=t1) (tn:=t2) in H0; repeat auto.
  eauto using trans_diff_def.
Qed.

Lemma preserves_diff_sr:
  forall pm,
  Valid pm ->
  Valid (f pm).
Proof.
  unfold Valid in *.
  unfold TransDiffFun in *.
  intros.
  eauto using preserves_transdiff.
Qed.
End PreservesDiff.

Let ph_diff_apply_drop:
  forall t t1 t2 z ph,
  ph_diff (drop t ph) t1 t2 z ->
  ph_diff ph t1 t2 z.
Proof.
  intros.
  inversion H; subst.
  apply drop_mapsto in H0.
  apply drop_mapsto in H1.
  destruct H0; destruct H1.
  auto using ph_diff_def.
Qed.

Let ph_diff_drop_all:
  forall p ph t pm t1 t2 z,
  ph_diff ph t1 t2 z ->
  Map_PHID.MapsTo p ph (drop_all t pm) ->
  exists ph' : phaser, Map_PHID.MapsTo p ph' pm /\ ph_diff ph' t1 t2 z.
Proof.
  intros.
  unfold drop_all, foreach in *.
  apply Map_PHID_Facts.mapi_inv in H0.
  destruct H0 as (ph', (p', (?, (?, ?)))).
  subst.
  eauto.
Qed.

Lemma drop_all_sr:
  forall pm t,
  Valid pm ->
  Valid (drop_all t pm).
Proof.
  intros.
  eauto using preserves_diff_sr, ph_diff_drop_all.
Qed.

Let ph_diff_apply_signal:
  forall t t1 t2 z ph,
  ph_diff (signal t ph) t1 t2 z ->
  ph_diff ph t1 t2 z.
Proof.
  intros.
  inversion H; subst.
  apply signal_mapsto_inv in H0.
  apply signal_mapsto_inv in H1.
  destruct H0.
  - destruct H1.
    + destruct a as (?, (?,(?,?))).
      destruct a0 as (?, (?,(?,?))).
      subst.
      repeat rewrite signal_preserves_wait_phase in *.
      auto using ph_diff_def.
    + destruct a as (?, (?,(?,?))).
      destruct a0 as (?, ?).
      subst.
      repeat rewrite signal_preserves_wait_phase in *.
      auto using ph_diff_def.
  - destruct H1.
    + destruct a0 as (?, (?,(?,?))).
      destruct a as (?, ?).
      subst.
      repeat rewrite signal_preserves_wait_phase in *.
      auto using ph_diff_def.
    + destruct a0 as (?, ?).
      destruct a as (?, ?).
      subst.
      repeat rewrite signal_preserves_wait_phase in *.
      auto using ph_diff_def.
Qed.

Let ph_diff_signal_all:
  forall p ph t pm t1 t2 z,
  ph_diff ph t1 t2 z ->
  Map_PHID.MapsTo p ph (signal_all t pm) ->
  exists ph' : phaser, Map_PHID.MapsTo p ph' pm /\ ph_diff ph' t1 t2 z.
Proof.
  intros.
  unfold signal_all, foreach in *.
  apply Map_PHID_Facts.mapi_inv in H0.
  destruct H0 as (ph', (p', (?, (?, ?)))).
  subst.
  eauto using ph_diff_apply_signal.
Qed.

Lemma signal_all_sr:
  forall pm t,
  Valid pm ->
  Valid (drop_all t pm).
Proof.
  intros.
  eauto using preserves_diff_sr, ph_diff_signal_all.
Qed.

End SR.
