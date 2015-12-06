Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.SetoidList.

Require Import Aniceto.Graphs.Graph.
Require Import Aniceto.Pair.
Require Import Aniceto.List.

Require Import HJ.Phasers.Progress.
Require Import HJ.Phasers.Lang.
Require Import HJ.Phasers.TransDiff.
Require Import HJ.Phasers.PhaseDiff.
Require Import HJ.Phasers.Typesystem.
Require Import HJ.Vars.

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
  ph_diff (Map_TID.add t (Taskview.wait v) ph) (t1, t2) z ->
  Map_TID.MapsTo t v ph ->
  ph_diff ph (t1, t2) (z + wait_delta t (t1, t2)).
Proof.
  intros.
    inversion H; subst; clear H.
    rewrite Map_TID_Facts.add_mapsto_iff in *.
    destruct H3 as [(?,?)|(?,?)].
    + destruct H5 as [(?,?)|(?,?)].
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
    + destruct H5 as [(?,?)|(?,?)].
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
  ph_diff (wait t ph) (t1, t2) z ->
  ph_diff ph (t1, t2) (z + wait_delta t (t1, t2)).
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
  forall t e z pm,
  pm_diff (wait_all t pm) e z ->
  pm_diff pm e (z + wait_delta t e).
Proof.
  intros.
  destruct e as (t1, t2).
  inversion H; subst; clear H.
  unfold foreach in *.
  apply Map_PHID_Facts.mapi_inv in H0.
  destruct H0 as (ph', (p', (?, (?, ?)))).
  subst.
  rename ph' into ph.
  eauto using ph_diff_apply_wait, pm_diff_def.
Qed.

Lemma walk2_wait_all:
  forall t pm t1 t2 w,
  Walk2 (HasDiff (pm_diff (wait_all t pm))) t1 t2 w ->
  Walk2 (HasDiff (pm_diff pm)) t1 t2 w.
Proof.
  intros.
  apply walk2_impl with (E:=HasDiff (pm_diff (wait_all t pm))); repeat auto.
  intros.
  unfold HasDiff in *.
  destruct e as (ta, tb).
  destruct H0 as (z, ?).
  eauto using pm_diff_wait_all.
Qed.

Lemma pm_diff_mapi_sig:
  forall t t1 t2 pm z,
  pm_diff (wait_all t pm) (t1, t2) z ->
  pm_diff pm (t1, t2) (z - (tid_eq_sig t1 t) + (tid_eq_sig t2 t)).
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
  DiffSum (pm_diff (wait_all t pm)) w z ->
  StartsWith w t1 ->
  EndsWith w tn ->
  DiffSum (pm_diff pm) w (z - (tid_eq_sig t1 t) + (tid_eq_sig tn t)).
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
    assert ( DiffSum (pm_diff pm) ((t2, t3) :: w) (s - tid_eq_sig t2 t + tid_eq_sig tn t)). {
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
  TransDiff (pm_diff (wait_all t pm)) t1 t2 z ->
  TransDiff (pm_diff pm) t1 t2 (z - (tid_eq_sig t1 t) + (tid_eq_sig t2 t)).
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
(*
  Variable preserves_ph_diff:
    forall p ph pm z t1 t2,
    ph_diff ph t1 t2 z ->
    Map_PHID.MapsTo p ph (f pm) ->
    exists ph', Map_PHID.MapsTo p ph' pm /\ ph_diff ph' t1 t2 z.
*)
(*
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
*)
  Variable preserves_diff:
    forall e z pm,
    pm_diff (f pm) e z ->
    pm_diff pm e z.

  Lemma preserves_walk2:
    forall pm t1 t2 w,
    Walk2 (HasDiff (pm_diff (f pm))) t1 t2 w ->
    Walk2 (HasDiff (pm_diff pm)) t1 t2 w.
  Proof.
    intros.
    apply walk2_impl with (E:=HasDiff (pm_diff (f pm))); repeat auto.
    intros.
    unfold HasDiff in *.
    destruct e as (ta, tb).
    destruct H0 as (z, ?).
    eauto using preserves_diff.
  Qed.

  Let preserves_diff_sum:
    forall w t1 tn pm z,
    DiffSum (pm_diff (f pm)) w z ->
    StartsWith w t1 ->
    EndsWith w tn ->
    DiffSum (pm_diff pm) w z.
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
    assert (t1' = t1) by eauto using starts_with_eq.
    destruct w; subst.
    - inversion H.
      assert (t2 = tn) by eauto using ends_with_eq.
      subst.
      auto using preserves_diff, diff_sum_pair.
    - destruct p as (t2', t3).
      inversion H; subst; clear H.
      rename t2' into t2.
      assert (StartsWith ((t2, t3) :: w) t2). {
        eauto using starts_with_def.
      }
      apply ends_with_inv in H1.
      assert ( DiffSum (pm_diff pm) ((t2, t3) :: w) s) by eauto.
      apply preserves_diff in H9. (* invert diff_mapi *)
      simpl in *.
      auto using diff_sum_cons.
  Qed.

  Let preserves_transdiff:
    forall pm t1 t2 z,
    TransDiff (pm_diff (f pm)) t1 t2 z ->
    TransDiff (pm_diff pm) t1 t2 z.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply preserves_walk2 in H1.
    inversion H1; subst.
    eauto using trans_diff_def, preserves_diff_sum.
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

Section Drop.
  Let ph_diff_apply_drop:
    forall t e z ph,
    ph_diff (drop t ph) e z ->
    ph_diff ph e z.
  Proof.
    intros.
    inversion H; subst.
    apply drop_mapsto in H0.
    apply drop_mapsto in H1.
    destruct H0; destruct H1.
    auto using ph_diff_def.
  Qed.

  Let ph_diff_drop_all:
    forall t e z pm,
    pm_diff (drop_all t pm) e z ->
    pm_diff pm e z.
  Proof.
    intros.
    unfold drop_all, foreach in *.
    inversion H; subst; clear H.
    inversion H1; subst; clear H1.
    apply Map_PHID_Facts.mapi_inv in H0.
    destruct H0 as (ph', (p', (?, (?, ?)))).
    subst.
    eauto using pm_diff_def, ph_diff_def.
  Qed.

  Lemma drop_all_sr:
    forall pm t,
    Valid pm ->
    Valid (drop_all t pm).
  Proof.
    intros.
    eauto using preserves_diff_sr, ph_diff_drop_all.
  Qed.

  Let pm_diff_preserves_drop:
    forall p t pm e z,
    pm_diff (ph_drop p t pm) e z ->
    pm_diff pm e z.
  Proof.
    intros.
    inversion H; subst; clear H.
    unfold ph_drop, update in *.
    remember (Map_PHID.find  _ _).
    symmetry in Heqo.
    destruct o as [ph'|].
    - rewrite <- Map_PHID_Facts.find_mapsto_iff in Heqo.
      apply Map_PHID_Facts.add_mapsto_iff in H0.
      destruct H0.
      + destruct H.
        subst.
        eauto using pm_diff_def, ph_diff_def.
      + destruct H.
        eauto using pm_diff_def, ph_diff_def.
    - eauto using pm_diff_def, ph_diff_def.
  Qed.

  Lemma ph_drop_sr:
    forall pm p t,
    Valid pm ->
    Valid (ph_drop p t pm).
  Proof.
    intros.
    eauto using preserves_diff_sr.
  Qed.

End Drop.

Section Signal.

  Let ph_diff_signal:
    forall t e z ph,
    ph_diff (signal t ph) e z ->
    ph_diff ph e z.
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

  Let pm_diff_signal_all:
    forall t e z pm,
    pm_diff (signal_all t pm) e z ->
    pm_diff pm e z.
  Proof.
    intros.
    unfold signal_all, foreach in *.
    inversion H; subst; clear H.
    apply Map_PHID_Facts.mapi_inv in H0.
    destruct H0 as (ph', (p', (?, (?, ?)))).
    subst.
    eauto using pm_diff_def, ph_diff_def, ph_diff_signal.
  Qed.

  Lemma signal_all_sr:
    forall pm t,
    Valid pm ->
    Valid (signal_all t pm).
  Proof.
    eauto using preserves_diff_sr, pm_diff_signal_all.
  Qed.

  Let pm_diff_ph_signal:
    forall p' t e z pm,
    pm_diff (ph_signal p' t pm) e z ->
    pm_diff pm e z.
  Proof.
    intros.
    inversion H; subst; clear H.
    unfold ph_signal, update in *.
    remember (Map_PHID.find  _ _).
    symmetry in Heqo.
    destruct o as [ph'|].
    - rewrite <- Map_PHID_Facts.find_mapsto_iff in Heqo.
      apply Map_PHID_Facts.add_mapsto_iff in H0.
      destruct H0.
      + destruct H.
        subst.
        eauto using pm_diff_def, ph_diff_def.
      + destruct H.
        eauto using pm_diff_def, ph_diff_def.
    - eauto using pm_diff_def, ph_diff_def.
  Qed.

  Lemma ph_signal_sr:
    forall pm p t,
    Valid pm ->
    Valid (ph_signal p t pm).
  Proof.
    intros.
    eauto using preserves_diff_sr, pm_diff_ph_signal.
  Qed.

End Signal.


  Let DiffSumEx E (m:phasermap) t1 t2 w z :=
    DiffSum (pm_diff m) w z /\ Walk2 E t1 t2 w.

  Let diff_sum_ex_cons:
    forall (E:(tid*tid)->Prop) m t1 t2 tn l s z,
    E (t1, t2) ->
    pm_diff m (t1, t2) z ->
    DiffSumEx E m t2 tn l s ->
    DiffSumEx E m t1 tn ((t1, t2) :: l) (z + s).
  Proof.
    intros.
    unfold DiffSumEx in *.
    destruct H1.
    split.
    - destruct l. {
        inversion H2.
        subst.
        apply ends_with_nil_inv in H4.
        inversion H4.
      }
      destruct p.
      inversion H2.
      subst.
      assert (t = t2). {
        eauto using starts_with_eq.
      }
      subst.
      auto using diff_sum_cons.
    - auto using walk2_cons.
  Qed.

Section PhNew.

  Let pm_diff_ph_new:
    forall p t t1 t2 z pm,
    (t1 <> t \/ t2 <> t) ->
    pm_diff (ph_new p t pm) (t1, t2) z ->
    pm_diff pm (t1, t2) z.
  Proof.
    intros.
    unfold ph_new in *.
    inversion H0; subst.
    apply Map_PHID_Facts.add_mapsto_iff in H1.
    destruct H1.
    - destruct H1.
      subst.
      inversion H2; subst; clear H2.
      apply make_mapsto in H4.
      apply make_mapsto in H6.
      destruct H4, H6.
      repeat subst.
      destruct H;
      contradiction H; trivial.
    - destruct H1.
      eauto using pm_diff_def.
  Qed.

  (* Removes all self links *)

  Variable t:tid.

  Let skip_self p := if pair_eq_dec TID.eq_dec (t,t) p then false else true.

  Let skip_self_inv_false:
    forall x y,
    skip_self (x, y) = false ->
    x = t /\ y = t.
  Proof.
    unfold skip_self.
    intros.
    remember (pair_eq_dec _ _ _).
    destruct s.
    - inversion e; auto.
    - inversion H.
  Qed.

  Let skip_self_inv_true:
    forall x y,
    skip_self (x, y) = true ->
    x <> t \/ y <> t.
  Proof.
    unfold skip_self.
    intros.
    remember (pair_eq_dec _ _ _).
    destruct s.
    - inversion H.
    - destruct (TID.eq_dec x t). {
        subst.
        right.
        destruct (TID.eq_dec y t). {
          subst.
          contradiction n.
          trivial.
        }
        auto.
      }
      intuition.
  Qed.

  Let linked_filter_self:
    forall a w,
    Linked a w ->
    Connected w ->
    Linked a (filter skip_self w).
  Proof.
    intros.
    induction w as [|e].
    - auto.
    - destruct a as (x, y).
      destruct e as (y', z).
      assert (Hx:= H).
      apply linked_inv in H.
      subst.
      simpl.
      remember (skip_self (y, z)).
      symmetry in Heqb.
      destruct b; auto using linked_eq.
      apply skip_self_inv_false in Heqb.
      destruct Heqb.
      subst.
      inversion H0; subst.
      assert (Linked (x, t) w) by auto.
      auto.
  Qed.

  Let walk_filter_self:
    forall E w,
    Walk E w ->
    Walk E (filter skip_self w).
  Proof.
    intros.
    induction w.
    - simpl in *.
      auto.
    - simpl.
      remember (skip_self a).
      symmetry in Heqb.
      destruct b.
      + inversion H; subst.
        assert (Hx := H2).
        apply walk_inv in H2; destruct H2.
        auto using walk_cons.
      + destruct a as (x,y).
        apply skip_self_inv_false in Heqb.
        destruct Heqb.
        subst.
        inversion H; auto.
  Qed.

  Let filter_skip_inv_cons_eq_nil:
    forall w p,
    filter skip_self (p :: w) = nil ->
    p = (t, t).
  Proof.
    intros.
    simpl in H.
    remember (skip_self p).
    symmetry in Heqb.
    destruct b. {
      inversion H.
    }
    destruct p.
    apply skip_self_inv_false in Heqb.
    destruct Heqb.
    subst.
    trivial.
  Qed.

  Let filter_skip_inv_ends_with:
    forall w p,
    filter skip_self (p :: w) = nil ->
    EndsWith (p::w) t.
  Proof.
    induction w; intros.
    - apply filter_skip_inv_cons_eq_nil in H.
      subst.
      auto using ends_with_edge.
    - apply ends_with_cons.
      apply IHw.
      simpl in *.
      destruct (skip_self p).
      + inversion H.
      + auto.
  Qed.

  Let filter_skip_ends_with:
    forall E w x,
    Walk E w ->
    EndsWith w x ->
    filter skip_self w = nil \/
    EndsWith (filter skip_self w) x.
  Proof.
    induction w; intros. {
      apply ends_with_nil_inv in H0.
      inversion H0.
    }
    simpl.
    remember (skip_self a).
    symmetry in Heqb.
    destruct w. {
      destruct a as (y,x').
      apply ends_with_inv_cons_nil in H0.
      destruct b. {
        right.
        subst.
        simpl.
        auto using ends_with_edge.
      }
      apply skip_self_inv_false in Heqb.
      destruct Heqb.
      repeat subst.
      intuition.
    }
    assert (ew : EndsWith (p :: w) x) by eauto using ends_with_inv.
    assert (W:  Walk E (p :: w)) by (inversion H; auto).
    apply IHw in ew; auto.
    destruct b. {
      right.
      destruct ew as [ew|ew]. {
        rewrite ew.
        assert (Hx := ew).
        apply filter_skip_inv_cons_eq_nil in ew.
        apply filter_skip_inv_ends_with in Hx.
        subst.
        inversion H.
        subst.
        destruct a as (a, t').
        apply linked_inv in H5.
        rewrite <- H5 in *.
        apply ends_with_inv in H0.
        assert (x = t). {
          eauto using ends_with_fun.
        }
        rewrite H1.
        auto using ends_with_edge.
      }
      auto using ends_with_cons.
    }
    intuition.
  Qed.

  Let ends_with_filter_skip:
    forall E t1 t2 tn l,
    Walk E ((t1, t2) :: l) ->
    EndsWith ((t1, t2) :: l) tn ->
    filter skip_self l = nil ->
    EndsWith ((t1, t2) :: nil) tn.
  Proof.
    intros.
    destruct l. {
      assumption.
    }
    apply ends_with_inv in H0.
    assert (tn = t). {
      apply filter_skip_inv_ends_with in H1.
      eauto using ends_with_fun.
    }
    subst.
    assert (t2 = t). {
      assert (R: p = (t, t)). {
        assert (List.In p (p :: l)) by auto using in_eq.
        assert (R: ~ List.In p (filter skip_self (p :: l))). {
          rewrite H1.
          intuition.
        }
        apply filter_notin_to_false in R; auto.
        destruct p.
        apply skip_self_inv_false in R.
        destruct R.
        subst; auto.
      }
      subst.
      inversion H.
      subst.
      eauto using linked_inv.
    }
    subst; auto using ends_with_edge.
  Qed.

  Let filter_skip_walk2_aux_1:
    forall p w E t1 t2 tn,
    filter skip_self (p :: w) = nil ->
    Walk2 E t2 tn (p :: w) ->
    EndsWith ((t1,t2) :: filter skip_self (p :: w)) tn.
  Proof.
    intros.
    assert (Hx := H0).
    inversion Hx.
            subst.
            assert (tn = t). {
              eauto using filter_skip_inv_ends_with, ends_with_fun.
            }
            apply walk2_inv_cons in Hx.
            destruct Hx as (?, (?,?)).
            rewrite H.
            subst.
            assert (R: t2 = t). {
              assert (Hy : List.In (t2, x) ((t2,x) :: w)) by auto using in_eq.
              apply filter_notin_to_false with (f:=skip_self) in Hy.
              - apply skip_self_inv_false in Hy.
                destruct Hy; auto.
              - rewrite H.
                intuition.
            }
            subst.
            auto using ends_with_edge.
  Qed.

  Let filter_skip_walk2:
    forall E tn w t1,
    Walk2 E t1 tn w ->
    filter skip_self w = nil \/
    Walk2 E t1 tn (filter skip_self w).
  Proof.
    induction w; intros. {
      intuition.
    }
    simpl in *.
    remember (skip_self a).
    symmetry in Heqb.
    destruct w.
    - simpl in *.
      destruct b. {
        auto.
      }
      intuition.
    - apply walk2_inv in H.
      destruct H as (t2,(?,(?,?))).
      destruct b. {
        right.
        assert (Hx:=H1).
        apply IHw in H1.
        destruct H1.
        - apply walk2_def.
          + subst; auto using starts_with_def.
          + rewrite H in *.
            apply filter_skip_walk2_aux_1 with (E:=E) (t1:=t1) (t2:=t2) (tn:=tn) in H1; auto.
          + rewrite H1.
            subst.
            auto using edge_to_walk.
        - subst.
          auto using walk2_cons.
      }
      destruct a as (x, y).
      apply skip_self_inv_false in Heqb.
      inversion H.
      destruct Heqb.
      subst.
      rewrite <- H4 in *.
      rewrite <- H3 in *.
      clear H3 H4 H.
      auto.
  Qed.

  Let diff_sum_2_sieve:
    forall E m tn w t1 z,
    DiffSumEx E m t1 tn w z ->
    ((filter skip_self w = nil /\ z = 0%Z)
    \/ (filter skip_self w <> nil /\ DiffSumEx E m t1 tn (filter skip_self w) z)).
  Proof.
    induction w; intros. {
      destruct H as (?, ?).
      inversion H.
      left.
      intuition.
    }
    destruct H as (?, ?).
    destruct a as (t1', t2).
    inversion H0; subst.
    assert (t1' = t1) by
    eauto using starts_with_eq; subst.
    simpl.
    remember (skip_self (t1, t2)).
    symmetry in Heqb.
    destruct b. {
      right.
      inversion H; subst.
      - simpl.
        split; try split; auto with *.
      - rename w0 into w.
        assert (D: DiffSumEx E m t2 tn ((t2,t4)::w) s). {
          unfold DiffSumEx.
          apply walk2_inv_2 in H0.
          intuition.
        }
        apply IHw in D.
        split; auto with *.
        destruct D as [(R1,?)|?]. {
          assert (R2: (z0 + s = z0)%Z) by
          intuition.
          rewrite R1.
          rewrite R2.
          split.
          - inversion H3.
            auto using diff_sum_pair.
          - apply filter_skip_walk2 in H0.
            remember ((t2,t4)::_) as l.
            destruct H0. {
              assert (R3: (t1,t2)::filter skip_self l = filter skip_self ((t1, t2) :: l)). {
              simpl.
              rewrite Heqb.
              trivial.
            }
            rewrite R1 in R3.
            rewrite <- R3 in H0.
            inversion H0.
          }
          rewrite <- R1.
          simpl in H0.
          rewrite Heqb in *.
          assumption.
        }
        destruct H4.
        apply diff_sum_ex_cons.
        + inversion H3; auto.
        + inversion H; auto.
        + auto.
      }
      apply skip_self_inv_false in Heqb.
      destruct Heqb; subst.
      destruct w. {
        left.
        inversion H.
        subst.
        simpl in *.
        apply pm_diff_refl_inv in H7.
        intuition.
      }
      destruct p as (t', t1).
      assert (t' = t). {
        inversion H3.
        subst.
        eauto using linked_inv.
      }
      subst.
      assert (DiffSumEx E m t tn ((t,t1)::w) z). {
        apply walk2_inv_2 in H0.
        split.
        - inversion H; subst.
          assert (z0 = 0%Z) by eauto using pm_diff_refl_inv.
          subst.
          inversion H.
          subst.
          assert ((0 + s = s)%Z). {
            intuition.
          }
          rewrite H4 in *.
          rewrite H6.
          apply pm_diff_refl_inv in H14.
          subst.
          assert (R: (0 + s0 = s0)%Z) by intuition.
          rewrite R.
          assumption.
        - assumption.
      }
      auto.
  Qed.

  Let transdiff_diff_sum_ex:
    forall m tn t1 z,
    TransDiff (pm_diff m) t1 tn z ->
    ((t1 = t /\ tn = t /\ z = 0%Z)
    \/ exists w, w <> nil /\ DiffSumEx (HasDiff (pm_diff m)) m t1 tn (filter skip_self w) z).
  Proof.
    intros.
    inversion H.
    subst.
    assert (DiffSumEx (HasDiff (pm_diff m)) m t1  tn w z). {
      split; auto.
    }
    apply diff_sum_2_sieve in H2.
    destruct H2.
    - left.
      inversion H1.
      subst.
      destruct w. {
        apply ends_with_nil_inv in H4.
        inversion H4.
      }
      destruct p as (t1', ?).
      assert (t1' = t1). {
       eauto using starts_with_eq.
      }
      subst.
      destruct H2.
      assert (t1 = t). {
        assert (Hx : ~ List.In (t1, t0) (filter skip_self ((t1, t0) :: w))). {
          rewrite H2.
          intuition.
        }
        apply filter_notin_to_false in Hx.
        - apply skip_self_inv_false in Hx; destruct Hx; subst; auto.
        - auto using in_eq.
      }
      assert (tn = t). {
        eauto using ends_with_fun, filter_skip_inv_ends_with.
      }
      intuition.
    - right.
      destruct H2.
      exists w.
      split.
      + intuition.
        subst.
        auto.
      + auto.
  Qed.

  Let in_pm_diff:
    forall p m w e z,
    List.In e (filter skip_self w) ->
    pm_diff (ph_new p t m) e z ->
    pm_diff m e z.
  Proof.
    intros.
    destruct e as (ti, tj).
    rewrite filter_In in H.
    destruct H.
    apply skip_self_inv_true in H1.
    eauto using pm_diff_ph_new.
  Qed.


  Let has_diff_trans:
    forall p t1 tn m z w,
    DiffSumEx (HasDiff (pm_diff (ph_new p t m))) (ph_new p t m) t1 tn (filter skip_self w) z ->
    DiffSumEx (HasDiff (pm_diff m)) m t1 tn (filter skip_self w) z.
  Proof.
    intros.
    destruct H.
    split.
    - eauto using diff_sum_impl_weak.
    - apply walk2_impl_weak with (E:=(HasDiff (pm_diff (ph_new p t m)))); auto.
      intros.
      inversion H2.
      unfold HasDiff.
      eauto.
  Qed.

  Let transdiff_fin:
    forall p m tn t1 z,
    TransDiff (pm_diff (ph_new p t m)) t1 tn z ->
    ((t1 = t /\ tn = t /\ z = 0%Z)
    \/ TransDiff (pm_diff m) t1 tn z).
  Proof.
    intros.
    apply transdiff_diff_sum_ex in H.
    destruct H. {
      intuition.
    }
    right.
    destruct H as (w, (Hn, Hd)).
    apply has_diff_trans in Hd.
    inversion Hd.
    eauto using trans_diff_def.
  Qed.

  Lemma pm_diff_to_refl_left:
    forall t1 t2 z pm,
    pm_diff pm (t1, t2) z ->
    pm_diff pm (t1, t1) 0%Z.
  Proof.
    intros.
    inversion H.
    apply ph_diff_inv_left in H1.
    eauto using pm_diff_refl.
  Qed.

  Lemma edge_to_walk2:
    forall {A:Type} (E:(A*A)->Prop) x y,
    E (x, y) ->
    Walk2 E x y ((x, y) :: nil).
  Proof.
    intros.
    apply walk2_def.
    + auto using starts_with_def.
    + auto using ends_with_edge.
    + auto using edge_to_walk.
  Qed.

  Lemma trans_diff_inv_refl:
    forall t pm z,
    TransDiff (pm_diff pm) t t z ->
    TransDiff (pm_diff pm) t t 0%Z.
  Proof.
    intros.
    inversion H.
    subst.
    inversion H0; subst; auto.
    - assert (t1 = t0). {
        inversion H1; eauto using starts_with_eq.
      }
      subst.
      assert (pm_diff pm (t0, t0) 0%Z). {
        eauto using pm_diff_to_refl_left.
      }
      apply trans_diff_def with ((t0,t0)::nil).
      auto using diff_sum_pair.
      apply edge_to_walk2.
      unfold HasDiff.
      eauto.
    - assert (t1 = t0). {
        inversion H1; eauto using starts_with_eq.
      }
      subst.
      assert (pm_diff pm (t0, t0) 0%Z). {
        eauto using pm_diff_to_refl_left.
      }
      apply trans_diff_def with ((t0,t0)::nil).
      auto using diff_sum_pair.
      apply edge_to_walk2.
      unfold HasDiff.
      eauto.
  Qed.

  Lemma pm_ph_new_sr:
    forall p pm,
    Valid pm ->
    Valid (ph_new p t pm).
  Proof.
    unfold Valid in *.
    unfold TransDiffFun in *.
    intros.
    apply transdiff_fin in H0.
    apply transdiff_fin in H1.
    destruct H0, H1.
    - intuition.
    - destruct H0 as (?,(?,?)).
      subst.
      eauto using trans_diff_inv_refl.
    - destruct H1 as (?,(?,?)).
      subst.
      eauto using trans_diff_inv_refl.
    - eauto.
  Qed.


End PhNew.

  Lemma async_in_1:
    forall p l t' t m,
    Map_PHID.In p (async l t' t m)->
    Map_PHID.In p m.
  Proof.
    intros.
    unfold async in *.
    rewrite Map_PHID_Facts.mapi_in_iff in H.
    assumption.
  Qed.

  Lemma async_in_2:
    forall p l t' t m,
    Map_PHID.In p m ->
    Map_PHID.In p (async l t' t m).
  Proof.
    intros.
    unfold async in *.
    rewrite Map_PHID_Facts.mapi_in_iff.
    assumption.
  Qed.

(*
  Lemma async_in_iff:
    forall p l t' t m,
    Map_PHID.In p (async l t' t m) <->
    Map_PHID.In p m.
  Proof.
    intros.
    split; eauto using async_in_1, async_in_2.
  Qed.
*)
(*
  Lemma async_pre_inv_ina_pre:
    forall l t' t m p r,
    AsyncPre l t' t m ->
    InA eq_phid (p,r) l ->
    Map_PHID.In p m.
  Proof.
    intros.
    inversion H.
    rewrite Forall_forall in H1.
    rewrite InA_alt in H0.
    destruct H0 as (a', (?, i)).
    apply H1 in i.
    destruct a' as (p', y).
    compute in H0.
    subst.
    inversion i.
    simpl in *.
    eauto using Map_PHID_Extra.mapsto_to_in.
  Qed.

  Lemma async_pre_inv_in_pre:
    forall l t' t m p r,
    AsyncPre l t' t m ->
    In (p,r) l ->
    Map_PHID.In p m.
  Proof.
    intros.
    assert (InA eq_phid (p,r) l). {
      rewrite InA_alt.
      exists (p, r).
      intuition.
    }
    eauto using async_pre_inv_ina_pre.
  Qed.

  Lemma async_pre_inv_in_post:
    forall l t' t m p ph r,
    AsyncPre l t' t m ->
    In (p,r) l ->
    Map_PHID.MapsTo p ph m->
    Map_PHID.MapsTo p (register {| get_task := t'; get_mode := r |} t ph) (async l t' t m).
  Proof.
    intros.
    induction l. {
      inversion H0.
    }
    destruct a as (p',r').
    simpl.
    unfold async_1.
    remember (Map_PHID.find _ _).
    symmetry in Heqo.
    destruct o as [ph'|].
    - apply Map_PHID_Facts.find_mapsto_iff in Heqo.
      inversion H0.
      + inversion H2; subst; clear H2.
        assert (ph' = ph). {
          assert (Map_PHID.MapsTo p ph (async l  t' t m)). {
            assert (~ InA eq_phid (p, r) l). {
              inversion H.
              intuition.
              inversion H3.
              subst.
              contradiction.
            }
            eauto using async_notina_mapsto.
          }
          eauto using Map_PHID_Facts.MapsTo_fun.
        }
        subst.
        auto using Map_PHID.add_1.
      + rewrite Map_PHID_Facts.add_mapsto_iff.
        right; intuition.
        * subst.
          inversion H.
          inversion H4.
          subst.
          contradiction H8.
          rewrite InA_alt.
          exists (p, r).
          intuition.
          auto using Phasermap.eq_phid_fst_eq.
        * eauto using async_pre_inv.
    - inversion H0.
      + inversion H2; subst; clear H2.
        apply Map_PHID_Extra.mapsto_to_in in H1.
        apply async_in_2 with (l:=l) (t':=t') (t:=t) in H1.
        assert (~ Map_PHID.In p (async l t' t m)). {
          apply Map_PHID_Facts.not_find_in_iff.
          assumption.
        }
        contradiction.
      + eauto using async_pre_inv.
  Qed.
  *)
(*
  Lemma async_inv_mapsto_cons:
    forall p ph a l t' t m,
    AsyncPre (a :: l) t' t m ->
    Map_PHID.MapsTo p ph (async (a :: l) t' t m) ->
    Map_PHID.MapsTo p ph (async l t' t m) \/ False.
  Proof.
    intros.
    destruct a as (p', r).
    simpl in *.
    assert (i: Map_PHID.In p' m). {
      eauto using async_pre_inv_in, InA_cons_hd, eq_phid_fst_eq.
    }
    apply Map_PHID_Extra.in_to_mapsto in i.
    destruct i as (ph', mt).
    assert (R := mt).
    apply pre_async_rw with (t:=t) (t':=t') (r:=r) in R.
    rewrite R in H0.
  Qed.
*)

Section Async.
  Variable t:tid.
  Variable t':tid.

  Let chg_tid t'' := if TID.eq_dec t'' t' then t else t''.

  Let chg_edge (e:tid * tid) := match e with (x,y) => (chg_tid x, chg_tid y) end.

  Variable p : phid.

  Variable m : phasermap.

  Variable l : list phased.

  Variable pre: AsyncPre l t' t m.

  Let m' := async l t' t m.

  Lemma walk_map_impl:
    forall {A:Type} (E F: (A*A)->Prop) f,
    (forall a, E a -> F (f a)) ->
    (forall a w, Linked a w -> Linked (f a) (map f w)) ->
    forall w,
    Walk E w ->
    Walk F (map f w).
  Proof.
    intros.
    induction w. {
      eauto using walk_nil.
    }
    inversion H1.
    subst.
    apply IHw in H4.
    clear IHw.
    simpl.
    apply walk_cons; auto.
  Qed.

  Let chg_edge_inv:
    forall pi ph ti v,
    Map_PHID.MapsTo pi ph m' ->
    Map_TID.MapsTo ti v ph ->
    (exists ph' v', Map_PHID.MapsTo pi ph' m /\ Map_TID.MapsTo t v' ph' /\ wait_phase v = wait_phase v') \/
    (exists ph' v', Map_PHID.MapsTo pi ph' m /\ Map_TID.MapsTo ti v' ph' /\ wait_phase v = wait_phase v').
  Proof.
    intros.
    unfold m' in *.
    apply pm_async_mapsto_rw in H.
    destruct H as (ph', (R, mt)).
    rewrite R in *; clear R.
    destruct (pm_async_1_rw l t' t pi ph').
    - destruct e as (r, (i, R)).
      rewrite R in *; clear R.
      apply ph_register_inv_mapsto in H0.
      destruct H0 as [mt2|(?, (v', (mt2, R)))].
      + right; eauto.
      + left.
        subst.
        exists ph'.
        exists v'.
        intuition.
   - destruct a as (R, Hx).
     right.
     rewrite R in *; clear R.
     eauto.
  Qed.
  (*
  Let chg_edge_aux_1:
    forall t'',
    t'' <> t' ->
    In t'' m' ->
    In t'' m.
  Proof.
    intros.
    inversion H0.
    assert (Map_PHID.In p0 m). {
      apply
      assert (Map_PHID.In p0 m') by eauto using Map_PHID_Extra.mapsto_to_in.
      unfold m' in *.
      apply 
      apply pm_async_1_mapsto in H
    apply 
    apply in_def.
  Qed.
*)
  Let chg_edge_impl:
    forall p' r ph e z,
    List.In (p', r) l ->
    Map_PHID.MapsTo p' ph m' ->
    ph_diff ph e z ->
    pm_diff m (chg_edge e) z.
  Proof.
    intros.
    destruct e as (x,y).
    simpl in *.
    unfold chg_tid.
    inversion H1; subst.
    unfold m' in *.
    rewrite pm_async_mapsto_rw in H0.
    destruct H0 as  (ph', (R, mt)).
    rewrite R in *; clear R.
    (*
    apply pm_async_1_mapsto in H6.
    destruct H6 as [?|(v',(r',(mt1,(i,?))))]. {
      
    }
    *)
    destruct (TID.eq_dec x t'). {
      subst.
      destruct (TID.eq_dec y t'). {
        subst.
        inversion pre.
        rewrite Forall_forall in H0.
        apply H0 in H.
        inversion H.
        simpl in *.
        remember (Z.of_nat (wait_phase v1) - Z.of_nat (wait_phase v2))%Z as z.
        assert (R: z = 0%Z) by eauto using ph_diff_refl_inv.
        rewrite R in *; clear R.
        assert (Map_TID.In t ph0) by eauto using Map_TID_Extra.mapsto_to_in.
        eauto using pm_diff_def, ph_diff_refl.
      }
      apply pm_async_1_mapsto in H6.
      destruct H6 as [?|(v',(r',(mt1,(i,?))))]. {
        
      }
    }
  Qed.

  Let edge_impl:
    forall e z,
    pm_diff m' e z ->
    pm_diff m (chg_edge e) z.
  Proof.
    intros.
    unfold m' in *.
    induction l.
    - simpl in H.
      destruct 
      unfold chg_edge.
  Qed.

  Let walk_chg_edge:
    forall w,
    Walk (HasDiff (pm_diff m')) w ->
    Walk (HasDiff (pm_diff m)) (map chd_edge w).
  Proof.
    intros.
    apply walk_map_impl with (E:=(HasDiff (pm_diff m'))); intros.
    - destruct H0.
      unfold HasDiff.
      exists x.
    induction w. {
      eauto using walk_nil.
    }
    inversion H.
    subst.
    simpl.
    apply walk_cons; auto.
    -  
    - 
  Qed.

(*
  Let ph_diff_register:
    forall t' r t e z ph,
    ph_diff (register {| get_task := t'; get_mode := r |} t ph) e z ->
    ph_diff ph e z.
  Proof.
    intros.
    unfold register in *.
    remember (Map_TID.find _ _).
    symmetry in Heqo.
    destruct o as [v'|].
    - apply Map_TID_Facts.find_mapsto_iff in Heqo.
      inversion H.
      subst.
      simpl in *.
      apply Map_TID_Facts.add_mapsto_iff in H0.
      apply Map_TID_Facts.add_mapsto_iff in H1.
      destruct H0, H1.
      + destruct H0, H1.
        repeat subst.
        rewrite set_mode_preserves_wait_phase in *.
        apply ph_diff_def.
  Qed.
*)
(*
  Let ph_diff_preserves_new:
    forall l p ph t t' pm t1 t2 z,
    ph_diff ph t1 t2 z ->
    Map_PHID.MapsTo p ph (async l t' t pm) ->
    exists ph' : phaser, Map_PHID.MapsTo p ph' pm /\ ph_diff ph' t1 t2 z.
  Proof.
    intros l.
    induction l; intros; eauto.
    destruct a as (p', r).
    simpl in *.
    unfold async_1 in *.
    remember (Map_PHID.find _ _).
    symmetry in Heqo.
    destruct o as [ph'|].
    - rewrite Map_PHID_Facts.add_mapsto_iff in H0.
      destruct H0.
      + destruct H0.
        subst.
        apply Map_PHID_Facts.find_mapsto_iff in Heqo.
        exists ph'.
        apply Map_PHID_Facts.find_mapsto_iff in Heqo.
        assert (Hx := Heqo).
        apply Map_PHID_Facts.MapsTo_fun with (e:=(register {| get_task := t'; get_mode := r |} t ph')) in Heqo.
        rewrite Heqo.
        assumption.
        apply ph_register_rw in Heqo.
        apply pre_async_rw with (t:=t) (t':=t') (r:=r)in Heqo.
    rewrite pre_async_rw with (ph:=ph) in H0. 
    unfold as in *.
    apply Map_PHID_Facts.add_mapsto_iff in H0.
    destruct H0.
    + destruct H0.
      subst.
      exists (Phaser.make t).
        intuition.
        eauto.
      + destruct H0.
        eauto.
  Qed.
*)
(*
  Let async_transdiff:
    forall pm t1 t2 z,
    In t1 pm ->
    In t2  pm ->
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
*)
(*
  Let ph_new_transdiff:
    forall p t pm t1 t2 z,
    TransDiff tid (diff (ph_new p t pm)) t1 t2 z ->
    TransDiff tid (diff pm) t1 t2 z.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply preserves_walk2 in H1.
    - inversion H1; subst.
      apply preserves_diff_sum with (t1:=t1) (tn:=t2) in H0; repeat auto.
    eauto using trans_diff_def.
  Qed.

  Lemma ph_new_sr:
    forall p t pm,
    Valid pm ->
    Valid (ph_new p t pm).
  Proof.
    unfold Valid in *.
    unfold TransDiffFun in *.
    intros.
    inversion H0; subst; clear H0.
    inversion H1; subst; clear H1.
    eauto using preserves_transdiff.
  Qed.

  Lemma ph_new_sr:
    forall pm p t,
    Valid pm ->
    Valid (ph_new p t pm).
  Proof.
    intros.
    eauto using preserves_diff_sr.
  Qed.*)
End Async.

End SR.


