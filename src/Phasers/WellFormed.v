Require Import HJ.Vars.

Require Import Coq.Lists.List.

Require HJ.Phasers.Regmode.
Require HJ.Phasers.Taskview.
Require HJ.Phasers.Phaser.
Require HJ.Phasers.Lang.

(**
  WellFormedness catpures a local property of taskviews: the relationship between
  signal-phase, wait-phase, and mode.
  It is an invariant of execution, thus, as we show, well_formedness is preserved by
  the various reduction relations.

  We, first, define the notion of well_formed for taskviews. *)

Module Taskview.
  Import HJ.Phasers.Regmode.
  Import HJ.Phasers.Taskview.

  (** A well_formed taskview has three possible cases:
  (i) the task has wait-capability and is ready to issue a signal,
  in which case the signal-phase and wait-phase match;
  (ii) the  task has wait-capability and has issued a signal, in which case
  the signal-phase is ahead of the wait-phase exactly one phase;
  (iii) the task is registered in signal-only mode, in which case the wait-phase
  cannot be ahead of the signal-phase.*)

  Inductive WellFormed v : Prop :=
    | tv_well_formed_sw_eq:
      mode v = SIGNAL_WAIT ->
      wait_phase v = signal_phase v ->
      WellFormed v
    | tv_well_formed_sw_succ:
      mode v = SIGNAL_WAIT ->
      S (wait_phase v) = signal_phase v ->
      WellFormed v
    | tv_well_formed_so:
      mode v = SIGNAL_ONLY ->
      WellFormed v
    | tv_well_formed_wo:
      mode v = WAIT_ONLY ->
      WellFormed v.


  Hint Constructors WellFormed.
  Section Facts.
  Lemma tv_well_formed_inv_sw:
    forall v,
    WellFormed v ->
    mode v = SIGNAL_WAIT ->
    wait_phase v = signal_phase v \/ S (wait_phase v) = signal_phase v.
  Proof.
    intros.
    inversion H; intuition.
    - rewrite H0 in H1; inversion H1.
    - rewrite H0 in H1; inversion H1.
  Qed.

  (**
    Regardless of the registration mode, the wait-phase cannot be
    greater than the signal-phase. *)

  Lemma well_formed_wait_phase_le_signal_phase:
    forall v,
    WellFormed v ->
    mode v = SIGNAL_WAIT ->
    wait_phase v <= signal_phase v.
  Proof.
    intros.
    apply tv_well_formed_inv_sw in H0; auto.
    destruct H0; intuition.
  Qed.

  Lemma tv_make_well_formed:
    WellFormed Taskview.make.
  Proof.
    intros.
    apply tv_well_formed_sw_eq.
    - rewrite make_mode.
      auto.
    - rewrite make_signal_phase.
      rewrite make_wait_phase.
      trivial.
  Qed.

  Lemma tv_signal_preserves_well_formed:
    forall v,
    WellFormed v ->
    SignalPre v ->
    WellFormed (Taskview.signal v).
  Proof.
    intros.
    inversion H0; auto.
    apply tv_well_formed_sw_succ.
    + rewrite signal_preserves_mode.
      assumption.
    + rewrite signal_preserves_wait_phase.
      simpl.
      rewrite H2.
      trivial.
  Qed.

  Lemma tv_try_signal_preserves_well_formed:
    forall v,
    WellFormed v ->
    WellFormed (Taskview.try_signal v).
  Proof.
    intros.
    inversion H.
    - apply tv_well_formed_sw_succ.
      + rewrite try_signal_preserves_mode.
        assumption.
      + rewrite try_signal_preserves_wait_phase.
        rewrite try_signal_signal_phase_sw; auto.
    - apply tv_well_formed_sw_succ.
      + rewrite try_signal_preserves_mode.
        assumption.
      + rewrite try_signal_preserves_wait_phase.
        rewrite try_signal_signal_phase_sw; auto.
    - apply tv_well_formed_so.
      rewrite try_signal_preserves_mode.
      assumption.
    - apply tv_well_formed_wo.
      rewrite try_signal_preserves_mode.
      assumption.
  Qed.

  Lemma tv_wait_preserves_well_formed:
    forall v,
    WellFormed v ->
    WaitPre v ->
    WellFormed (Taskview.wait v).
  Proof.
    intros.
    destruct H0.
    - auto.
    - apply tv_well_formed_sw_eq.
      + rewrite wait_preserves_mode; auto.
      + simpl.
        assumption.
  Qed.

  (** The operational semantics of taskviews preserves the property of [WellFormed]. *)

  Theorem tv_reduces_preserves_well_formed:
    forall v o v',
    WellFormed v ->
    Reduces v o v' ->
    WellFormed v'.
  Proof.
    intros.
    inversion H0; subst;
    auto using tv_signal_preserves_well_formed, tv_wait_preserves_well_formed.
  Qed.

  Lemma signal_phase_le_signal:
    forall v,
    WellFormed v ->
    signal_phase v <= signal_phase (signal v).
  Proof.
    intros.
    simpl.
    intuition.
  Qed.

  Lemma reduces_wait_inv_can_wait:
    forall v v',
    WellFormed v ->
    mode v = SIGNAL_WAIT ->
    Reduces v WAIT v' ->
    signal_phase v' = wait_phase v'.
  Proof.
    intros.
    inversion H1; subst.
    inversion H2.
    - rewrite H3 in H0.
      inversion H0.
    - auto.
  Qed.

  Lemma reduces_trans_inv:
    forall x y z o,
    WellFormed x ->
    CanSignal (mode x) ->
    Reduces x WAIT y ->
    Reduces y o z ->
    o = SIGNAL.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    - trivial.
    - assert (mode x = SIGNAL_WAIT). {
        inversion H3.
        + rewrite H2 in H0.
          inversion H0.
        + trivial.
      }
      destruct H1. {
        rewrite wait_preserves_mode in *.
        rewrite H1 in H2.
        inversion H2.
      }
      destruct H3. {
        rewrite wait_preserves_mode in *.
        rewrite H3 in H2.
        inversion H2.
      }
      rewrite wait_preserves_signal_phase in *.
      simpl in *.
      rewrite H5 in H4.
      clear H5.
      remember (signal_phase x) as s.
      induction s.
      + inversion H4.
      + inversion H4.
        eauto.
  Qed.

  Let tv_well_formed_set_mode_sw:
    forall v r,
    WellFormed v ->
    mode v = SIGNAL_WAIT ->
    WellFormed (set_mode v r).
  Proof.
    intros.
    destruct r.
    - auto using tv_well_formed_so.
    - auto using tv_well_formed_wo.
    - apply tv_well_formed_inv_sw in H; auto.
      destruct H; auto using tv_well_formed_sw_eq, tv_well_formed_sw_succ.
  Qed.

  Lemma set_mode_preserves_well_formed:
    forall v r,
    WellFormed v ->
    r_le r (mode v) ->
    WellFormed (set_mode v r).
  Proof.
    intros.
    remember (mode v) as r'.
    symmetry in Heqr'.
    destruct r';
    try (inversion H0;
      subst;
      rewrite <- Heqr';
      rewrite set_mode_ident;
      auto).
    auto using tv_well_formed_set_mode_sw.
  Qed.

End Facts.
End Taskview.

(** A well_formed phaser is such that
  every taskview mentioned in this phaser is well_formed. *)

Module Phaser.
  Import Taskview.
  Import HJ.Phasers.Phaser.

  Inductive WellFormed (ph:phaser) : Prop :=
    ph_well_formed_def:
      (forall t v,
        Map_TID.MapsTo t v ph ->
        Taskview.WellFormed v) ->
      WellFormed ph.

  Lemma ph_well_formed_add:
    forall t v ph,
    WellFormed ph ->
    Taskview.WellFormed v ->
    WellFormed (Map_TID.add t v ph).
  Proof.
    intros.
    apply ph_well_formed_def.
    intros p' ph' ?.
    apply Map_TID_Facts.add_mapsto_iff in H1.
    destruct H1.
    - destruct H1; subst; auto.
    - destruct H1; inversion H; eauto.
  Qed.

  Lemma ph_well_formed_to_tv_well_formed:
    forall t v ph,
    WellFormed ph ->
    Map_TID.MapsTo t v ph ->
    Taskview.WellFormed v.
  Proof.
    intros.
    inversion H.
    eauto.
  Qed.

  Lemma ph_signal_preserves_well_formed:
    forall ph t,
    WellFormed ph ->
    SignalPre t ph ->
    WellFormed (signal t ph).
  Proof.
    intros.
    unfold signal.
    unfold update.
    remember (Map_TID.find _ _).
    symmetry in Heqo.
    destruct o as [v|]; auto.
    rewrite <- Map_TID_Facts.find_mapsto_iff in Heqo.
    apply ph_well_formed_def.
    intros t' v'; intros.
    rewrite Map_TID_Facts.add_mapsto_iff in H1.
    destruct H1.
    - destruct H1; subst.
      assert (Taskview.WellFormed v) by (inversion H; eauto).
      assert (Taskview.SignalPre v). {
        destruct H0.
        assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
        auto.
      }
      auto using tv_signal_preserves_well_formed.
    - destruct H1; inversion H; eauto.
  Qed.

  Lemma ph_try_signal_preserves_well_formed:
    forall ph t,
    WellFormed ph ->
    WellFormed (try_signal t ph).
  Proof.
    intros.
    unfold try_signal.
    unfold update.
    remember (Map_TID.find _ _).
    symmetry in Heqo.
    destruct o as [v|]; auto.
    rewrite <- Map_TID_Facts.find_mapsto_iff in Heqo.
    apply ph_well_formed_def.
    intros t' v'; intros.
    rewrite Map_TID_Facts.add_mapsto_iff in H0.
    destruct H0.
    - destruct H0; subst.
      assert (Taskview.WellFormed v) by (inversion H; eauto).
      auto using tv_try_signal_preserves_well_formed.
    - destruct H0; inversion H; eauto.
  Qed.

  Lemma ph_wait_preserves_well_formed:
    forall ph t,
    WellFormed ph ->
    WaitPre t ph ->
    WellFormed (wait t ph).
  Proof.
    intros.
    destruct H0.
    assert (rw := H0).
    apply wait_rw in rw.
    rewrite rw.
    apply ph_well_formed_add; auto.
    assert (Taskview.WellFormed v) by (inversion H; eauto).
    eauto using tv_wait_preserves_well_formed.
  Qed.

  Lemma ph_try_wait_preserves_well_formed:
    forall ph t,
    WellFormed ph ->
    TryWaitPre t ph ->
    WellFormed (try_wait t ph).
  Proof.
    intros.
    unfold try_wait.
    inversion H0; auto using ph_wait_preserves_well_formed.
    assert (rw := H1).
    apply wait_rw in rw.
    rewrite rw.
    apply ph_well_formed_add; auto.
  Qed.

  Lemma ph_drop_preserves_well_formed:
    forall ph t,
    WellFormed ph ->
    WellFormed (drop t ph).
  Proof.
    intros.
    unfold drop in *.
    apply ph_well_formed_def.
    intros t' v ?.
    rewrite Map_TID_Facts.remove_mapsto_iff in H0.
    destruct H0.
    inversion H; eauto.
  Qed.

  Lemma ph_register_preserves_well_formed:
    forall ph t r,
    WellFormed ph ->
    RegisterPre r t ph ->
    WellFormed (register r t ph).
  Proof.
    intros.
    inversion H0.
    assert (rw := H2).
    apply register_rw with (r:=r) in rw.
    rewrite rw.
    assert (Taskview.WellFormed v) by (inversion H; eauto).
    auto using ph_well_formed_add, set_mode_preserves_well_formed.
  Qed.

  Lemma ph_reduces_preserves_well_formed:
    forall ph t o ph',
    WellFormed ph ->
    Reduces ph (t, o) ph' ->
    WellFormed ph'.
  Proof.
    intros.
    destruct o; subst; inversion H; simpl in *; inversion H0; simpl in *; clear H0; subst.
    - eauto using
      ph_signal_preserves_well_formed.
    - eauto using
      ph_wait_preserves_well_formed.
    - eauto using 
      ph_drop_preserves_well_formed.
    - eauto using ph_register_preserves_well_formed.
  Qed.

  Lemma ph_make_well_formed:
    forall t,
    WellFormed (make t).
  Proof.
    intros.
    unfold make.
    apply ph_well_formed_def.
    intros t'; intros.
    apply Map_TID_Facts.add_mapsto_iff in H.
    destruct H.
    - destruct H.
      subst.
      auto using tv_make_well_formed.
    - destruct H.
      rewrite Map_TID_Facts.empty_mapsto_iff in H0; inversion H0.
  Qed.

End Phaser.

(** Nonsurprisingly, a well_formed phasermap is such that
  every phaser mentioned in this phasermap is well_formed. *)


Module Phasermap.
  Import HJ.Phasers.Lang.
  Import Phaser.

  Inductive WellFormed (m:phasermap) : Prop :=
    pm_well_formed_def:
      (forall p ph,
        Map_PHID.MapsTo p ph m ->
        Phaser.WellFormed ph) ->
      WellFormed m.

  Lemma pm_well_formed_add:
    forall m ph p,
    WellFormed m ->
    Phaser.WellFormed ph ->
    WellFormed (Map_PHID.add p ph m).
  Proof.
    intros.
    apply pm_well_formed_def.
    intros p' ph' ?.
    apply Map_PHID_Facts.add_mapsto_iff in H1.
    destruct H1.
    - destruct H1; subst; auto.
    - destruct H1; inversion H; eauto.
  Qed.

  Lemma pm_ph_new_preserves_well_formed:
    forall p m t,
    WellFormed m ->
    PhNewPre p t m ->
    WellFormed (ph_new p t m).
  Proof.
    intros.
    unfold ph_new.
    apply pm_well_formed_add; auto.
    auto using ph_make_well_formed.
  Qed.

  Lemma pm_ph_signal_preserves_well_formed:
    forall p t m,
    WellFormed m ->
    PhSignalPre p t m ->
    WellFormed (ph_signal p t m).
  Proof.
    intros.
    destruct H0.
    apply pm_well_formed_def.
    intros p' ph'; intros.
    rewrite ph_signal_rw with (ph:=ph) in H2; auto.
    rewrite Map_PHID_Facts.add_mapsto_iff in H2.
    destruct H2 as [(?,?)|(?,?)].
    - subst.
      assert (Phaser.Reduces ph (t, SIGNAL) (signal t ph)). {
        apply reduces_def.
        simpl.
        trivial.
      }
      assert (Phaser.WellFormed ph) by (inversion H; eauto).
      eauto using ph_signal_preserves_well_formed.
    - inversion H; eauto.
  Qed.

  Lemma pm_ph_drop_preserves_well_formed:
    forall p t m,
    WellFormed m ->
    PhDropPre p t m ->
    WellFormed (ph_drop p t m).
  Proof.
    intros.
    destruct H0.
    apply pm_well_formed_def.
    intros p' ph'; intros.
    rewrite ph_drop_rw with (ph:=ph) in H2; auto.
    rewrite Map_PHID_Facts.add_mapsto_iff in H2.
    destruct H2.
    - destruct H2; subst.
      assert (Phaser.Reduces ph (t, DROP) (drop t ph)). {
        apply reduces_def.
        simpl.
        trivial.
      }
      assert (Phaser.WellFormed ph) by (inversion H; eauto).
      eauto using ph_drop_preserves_well_formed.
    - destruct H2.
      inversion H; eauto.
  Qed.

  Lemma pm_signal_all_preserves_well_formed:
    forall t m,
    WellFormed m ->
    WellFormed (signal_all t m).
  Proof.
    intros.
    unfold signal_all.
    apply pm_well_formed_def.
    intros.
    rewrite foreach_mapsto_rw in H0.
    destruct H0 as (ph', (Heq, mt)).
    subst.
    rename ph' into ph.
    assert (Phaser.WellFormed ph) by (inversion H; eauto).
    auto using ph_try_signal_preserves_well_formed.
  Qed.

  Lemma pm_wait_all_preserves_well_formed:
    forall t m,
    WellFormed m ->
    WaitAllPre t m ->
    WellFormed (wait_all t m).
  Proof.
    intros.
    unfold wait_all.
    apply pm_well_formed_def.
    intros.
    rewrite foreach_mapsto_rw in H1.
    destruct H1 as (ph', (Heq, mt)).
    subst.
    rename ph' into ph.
    destruct (Map_TID_Extra.in_dec tid_eq_rw t ph). {
      assert (TryWaitPre t ph)
      by (inversion H0; eauto).
      assert (Phaser.WellFormed ph) by (inversion H; eauto).
      auto using ph_try_wait_preserves_well_formed.
    }
    unfold wait.
    unfold Phaser.update.
    rewrite Map_TID_Facts.not_find_in_iff in n.
    rewrite n.
    inversion H; eauto.
  Qed.

  Lemma pm_drop_all_preserves_well_formed:
    forall t m,
    WellFormed m ->
    WellFormed (drop_all t m).
  Proof.
    intros.
    unfold drop_all.
    apply pm_well_formed_def.
    intros.
    rewrite foreach_mapsto_rw in H0.
    destruct H0 as (ph', (Heq, mt)).
    subst.
    assert (Phaser.WellFormed ph') by (inversion H; eauto).
    eauto using ph_drop_preserves_well_formed.
  Qed.

  Lemma ph_async_1_preserves_well_formed:
    forall ps t m p ph,
    AsyncPre ps t m ->
    Map_PHID.MapsTo p ph m ->
    Phaser.WellFormed ph ->
    Phaser.WellFormed (async_1 ps t p ph).
  Proof.
    intros.
    destruct (async_1_rw ps t p ph) as [(r,(i,R))|?]. {
      rewrite R; clear R.
      assert (Hx: RegisterPre {| Phaser.get_task := (get_new_task ps); get_mode := r |} t ph). {
        inversion H.
        apply H2 in H0.
        inversion H0.
        assert (r0 = r) by eauto using Map_PHID_Facts.MapsTo_fun; subst.
        assumption.
      }
      auto using ph_register_preserves_well_formed.
    }
    destruct a as (R,?).
    rewrite R.
    assumption.
  Qed.

  Lemma pm_async_preserves_well_formed:
    forall ps t m,
    WellFormed m ->
    AsyncPre ps t m ->
    WellFormed (async ps t m).
  Proof.
    intros.
    apply pm_well_formed_def.
    intros.
    apply async_mapsto_rw in H1.
    destruct H1 as (ph', (R, mt)).
    rewrite R in *; clear R.
    assert (Phaser.WellFormed ph') by (inversion H; eauto).
    inversion H0.
    eauto using ph_async_1_preserves_well_formed.
  Qed.

  Lemma pm_reduces_preserves_well_formed:
    forall m t o m',
    WellFormed m ->
    Reduces m t o m' ->
    WellFormed m'.
  Proof.
    intros.
    destruct H0.
    destruct o; simpl in *.
    - auto using pm_ph_new_preserves_well_formed.
    - auto using pm_ph_signal_preserves_well_formed.
    - auto using pm_ph_drop_preserves_well_formed.
    - auto using pm_signal_all_preserves_well_formed.
    - auto using pm_wait_all_preserves_well_formed.
    - auto using pm_drop_all_preserves_well_formed.
    - auto using pm_async_preserves_well_formed.
  Qed.
End Phasermap.
