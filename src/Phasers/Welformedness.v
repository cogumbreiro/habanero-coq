Require Import HJ.Vars.

Require Import Coq.Lists.List.

(**
  Welformedness catpures a local property of taskviews: the relationship between
  signal-phase, wait-phase, and mode.
  It is an invariant of execution, thus, as we show, welformedness is preserved by
  the various reduction relations.

  We, first, define the notion of welformed for taskviews. *)

Module Taskview.
  Require Import HJ.Phasers.Regmode.
  Require Import HJ.Phasers.Taskview.

(* end hide *)

  (** A welformed taskview has three possible cases:
  (i) the task has wait-capability and is ready to issue a signal,
  in which case the signal-phase and wait-phase match;
  (ii) the  task has wait-capability and has issued a signal, in which case
  the signal-phase is ahead of the wait-phase exactly one phase;
  (iii) the task is registered in signal-only mode, in which case the wait-phase
  cannot be ahead of the signal-phase.*)

  Inductive Welformed v : Prop :=
    | tv_welformed_wait_cap_eq:
      WaitCap (mode v) ->
      wait_phase v = signal_phase v ->
      Welformed v
    | tv_welformed_wait_cap_succ:
      WaitCap (mode v) ->
      S (wait_phase v) = signal_phase v ->
      Welformed v
    | tv_welformed_so:
      mode v = SIGNAL_ONLY ->
      wait_phase v <= signal_phase v ->
      Welformed v.

  Hint Constructors Welformed.

  (**
    Regardless of the registration mode, the wait-phase cannot be
    greater than the signal-phase. *)

  Lemma welformed_wait_phase_le_signal_phase:
    forall v,
    Welformed v ->
    wait_phase v <= signal_phase v.
  Proof.
    intros.
    inversion H; intuition.
  Qed.

(* begin hide *)

  Lemma tv_welformed_eq:
    forall v,
    wait_phase v = signal_phase v ->
    Welformed v.
  Proof.
    intros.
    destruct (wait_cap_so_dec (mode v)); auto; intuition.
  Qed.

  Lemma tv_welformed_succ:
    forall v,
    S (wait_phase v) = signal_phase v ->
    Welformed v.
  Proof.
    intros.
    destruct (wait_cap_so_dec (mode v)); auto; intuition.
  Qed.

  Lemma welformed_inv_sw:
    forall v,
    Welformed v ->
    WaitCap (mode v) ->
    (wait_phase v = signal_phase v) \/ (S (wait_phase v) = signal_phase v).
  Proof.
    intros.
    inversion H; intuition.
    apply so_to_not_wait_cap in H1.
    contradiction.
  Qed.

  Lemma tv_make_welformed:
    Welformed Taskview.make.
  Proof.
    intros.
    apply tv_welformed_wait_cap_eq.
    rewrite make_mode.
    auto.
    rewrite make_signal_phase.
    rewrite make_wait_phase.
    trivial.
  Qed.

  Lemma tv_signal_preserves_welformed:
    forall v,
    Welformed v ->
    Welformed (Taskview.signal v).
  Proof.
    intros.
    inversion H.
    - apply tv_welformed_wait_cap_succ.
      rewrite signal_preserves_mode; auto.
      apply signal_wait_cap_signal_phase in H0.
      rewrite H0.
      auto using signal_preserves_wait_phase.
    - apply tv_welformed_wait_cap_succ.
      rewrite signal_preserves_mode; auto.
      apply signal_wait_cap_signal_phase in H0.
      rewrite H0.
      auto using signal_preserves_wait_phase.
    - apply tv_welformed_so.
      rewrite signal_preserves_mode; auto.
      rewrite signal_preserves_wait_phase.
      rewrite signal_so_signal_phase; auto.
  Qed.

  Lemma tv_wait_preserves_welformed:
    forall v,
    Welformed v ->
    WaitPre v ->
    Welformed (Taskview.wait v).
  Proof.
    intros.
    destruct H0.
    inversion H.
    - assert (wait_phase v <> signal_phase v) by intuition.
      contradiction.
    - apply tv_welformed_wait_cap_eq.
      rewrite wait_preserves_mode; auto.
      rewrite wait_preserves_signal_phase.
      rewrite <- H1.
      rewrite wait_wait_phase.
      trivial.
    - apply tv_welformed_so.
      rewrite wait_preserves_mode; auto.
      rewrite wait_wait_phase.
      rewrite wait_preserves_signal_phase.
      intuition.
  Qed.

  (* end hide*)

  (** The operational semantics of taskviews preserves the property of [Welformed]. *)

  Theorem tv_reduces_preserves_welformed:
    forall v o v',
    Welformed v ->
    Reduces v o v' ->
    Welformed v'.
  Proof.
    intros.
    inversion H0;
    subst;
    auto using tv_signal_preserves_welformed, tv_wait_preserves_welformed.
  Qed.

  (* begin hide *)

  Lemma signal_phase_signal_inv:
    forall v,
    Welformed v ->
    signal_phase (Taskview.signal v) = signal_phase v
    \/ signal_phase (Taskview.signal v) = S (signal_phase v).
  Proof.
    intros.
    inversion H.
    - rewrite signal_wait_cap_signal_phase; auto.
    - rewrite signal_wait_cap_signal_phase; auto.
    - rewrite signal_so_signal_phase; auto.
  Qed.

  Lemma signal_phase_le_signal:
    forall v,
    Welformed v ->
    signal_phase v <= signal_phase (signal v).
  Proof.
    intros.
    apply signal_phase_signal_inv in H.
    destruct H; intuition.
  Qed.

  Lemma reduces_wait_post:
    forall v v',
    Welformed v ->
    Reduces v WAIT v' ->
    (mode v' = SIGNAL_ONLY \/ WaitCap (mode v') /\ wait_phase v' = signal_phase v').
  Proof.
    intros.
    inversion H0.
    destruct H1.
    inversion H.
    - assert (wait_phase v <> signal_phase v) by intuition.
      contradiction H4.
    - right.
      rewrite wait_preserves_signal_phase.
      rewrite wait_wait_phase.
      intuition.
    - left.
      rewrite wait_preserves_mode.
      assumption.
  Qed.

  Lemma reduces_wait_inv_wait_cap:
    forall v v',
    Welformed v ->
    WaitCap (mode v) ->
    Reduces v WAIT v' ->
    signal_phase v' = wait_phase v'.
  Proof.
    intros.
    inversion H1; subst.
    apply reduces_wait_post in H1; auto.
    destruct H1 as [R|(?,?)].
    - (* absurd case *)
      assert (WaitCap (mode (wait v))). {
        auto using wait_preserves_mode.
      }
      rewrite R in *.
      inversion H1.
    - intuition.
  Qed.

  Lemma reduces_trans_inv:
    forall x y z o,
    Welformed x ->
    WaitCap (mode x) ->
    Reduces x WAIT y ->
    Reduces y o z ->
    o = SIGNAL.
  Proof.
    intros.
    inversion H1; subst.
    inversion H2; trivial; subst.
    subst.
    apply reduces_wait_post in H1.
    {
      destruct H1 as [?|(?,?)].
      - rewrite wait_cap_rw in *.
        rewrite wait_preserves_mode in *.
        contradiction.
      - destruct H3 as [H3].
        destruct H4 as [H4].
        rewrite wait_preserves_signal_phase in *.
        rewrite H5 in *.
        assert (signal_phase x <> signal_phase x). {
          intuition.
        }
        assert (signal_phase x = signal_phase x) by auto.
        contradiction.
    }
    assumption.
  Qed.

  Lemma set_mode_preserves_welformed:
    forall v r,
    Welformed v ->
    r_le r (mode v) ->
    Welformed (set_mode v r).
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
    inversion H.
    - auto using tv_welformed_eq.
    - auto using tv_welformed_succ.
    - rewrite Heqr' in H1.
      inversion H1.
  Qed.

(* end hide *)

End Taskview.

(** A welformed phaser is such that
  every taskview mentioned in this phaser is welformed. *)

Module Phaser.
  Import Taskview.
  Require Import HJ.Phasers.Phaser.

  Inductive Welformed (ph:phaser) : Prop :=
    ph_welformed_def:
      (forall t v,
        Map_TID.MapsTo t v ph ->
        Taskview.Welformed v) ->
      Welformed ph.

  (* begin hide *)

  Lemma ph_welformed_add:
    forall t v ph,
    Welformed ph ->
    Taskview.Welformed v ->
    Welformed (Map_TID.add t v ph).
  Proof.
    intros.
    apply ph_welformed_def.
    intros p' ph' ?.
    apply Map_TID_Facts.add_mapsto_iff in H1.
    destruct H1.
    - destruct H1; subst; auto.
    - destruct H1; inversion H; eauto.
  Qed.

  Lemma ph_welformed_to_tv_welformed:
    forall t v ph,
    Welformed ph ->
    Map_TID.MapsTo t v ph ->
    Taskview.Welformed v.
  Proof.
    intros.
    inversion H.
    eauto.
  Qed.

  Lemma ph_signal_preserves_welformed:
    forall ph t,
    Welformed ph ->
    Welformed (signal t ph).
  Proof.
    intros.
    unfold signal.
    unfold update.
    remember (Map_TID.find _ _).
    symmetry in Heqo.
    destruct o as [v|]; auto.
    rewrite <- Map_TID_Facts.find_mapsto_iff in Heqo.
    apply ph_welformed_def.
    intros t' v'; intros.
    rewrite Map_TID_Facts.add_mapsto_iff in H0.
    destruct H0.
    - destruct H0; subst.
      assert (Taskview.Welformed v) by (inversion H; eauto).
      auto using tv_signal_preserves_welformed.
    - destruct H0; inversion H; eauto.
  Qed.

  Lemma ph_wait_preserves_welformed:
    forall ph t,
    Welformed ph ->
    WaitPre t ph ->
    Welformed (wait t ph).
  Proof.
    intros.
    destruct H0.
    assert (rw := H0).
    apply ph_wait_rw in rw.
    rewrite rw.
    apply ph_welformed_add; auto.
    assert (Taskview.Welformed v) by (inversion H; eauto).
    eauto using tv_wait_preserves_welformed.
  Qed.

  Lemma ph_drop_preserves_welformed:
    forall ph t,
    Welformed ph ->
    Welformed (drop t ph).
  Proof.
    intros.
    unfold drop in *.
    apply ph_welformed_def.
    intros t' v ?.
    rewrite Map_TID_Facts.remove_mapsto_iff in H0.
    destruct H0.
    inversion H; eauto.
  Qed.

  Lemma ph_register_preserves_welformed:
    forall ph t r,
    Welformed ph ->
    RegisterPre r t ph ->
    Welformed (register r t ph).
  Proof.
    intros.
    inversion H0.
    assert (rw := H2).
    apply ph_register_rw with (r:=r) in rw.
    rewrite rw.
    assert (Taskview.Welformed v) by (inversion H; eauto).
    auto using ph_welformed_add, set_mode_preserves_welformed.
  Qed.

  (* end hide *)

  Lemma ph_reduces_preserves_welformed:
    forall ph t o ph',
    Welformed ph ->
    Reduces ph t o ph' ->
    Welformed ph'.
  Proof.
    intros.
    destruct o; subst; inversion H; simpl in *; destruct H0; simpl in *.
    - eauto using
      ph_signal_preserves_welformed.
    - eauto using
      ph_wait_preserves_welformed.
    - eauto using 
      ph_drop_preserves_welformed.
    - eauto using ph_register_preserves_welformed.
  Qed.

  Lemma ph_make_welformed:
    forall t,
    Welformed (make t).
  Proof.
    intros.
    unfold make.
    apply ph_welformed_def.
    intros t'; intros.
    apply Map_TID_Facts.add_mapsto_iff in H.
    destruct H.
    - destruct H.
      subst.
      auto using tv_make_welformed.
    - destruct H.
      rewrite Map_TID_Facts.empty_mapsto_iff in H0; inversion H0.
  Qed.

End Phaser.

(** Nonsurprisingly, a welformed phasermap is such that
  every phaser mentioned in this phasermap is welformed. *)


Module Phasermap.
  Require Import HJ.Phasers.Lang.
  Import Phaser.

  Inductive Welformed (m:phasermap) : Prop :=
    pm_welformed_def:
      (forall p ph,
        Map_PHID.MapsTo p ph m ->
        Phaser.Welformed ph) ->
      Welformed m.
  (* begin hide *)
  Lemma pm_welformed_add:
    forall m ph p,
    Welformed m ->
    Phaser.Welformed ph ->
    Welformed (Map_PHID.add p ph m).
  Proof.
    intros.
    apply pm_welformed_def.
    intros p' ph' ?.
    apply Map_PHID_Facts.add_mapsto_iff in H1.
    destruct H1.
    - destruct H1; subst; auto.
    - destruct H1; inversion H; eauto.
  Qed.

  Lemma pm_ph_new_preserves_welformed:
    forall p m t,
    Welformed m ->
    PhNewPre p t m ->
    Welformed (ph_new p t m).
  Proof.
    intros.
    unfold ph_new.
    apply pm_welformed_add; auto.
    auto using ph_make_welformed.
  Qed.

  Lemma pm_ph_signal_preserves_welformed:
    forall p t m,
    Welformed m ->
    PhSignalPre p t m ->
    Welformed (ph_signal p t m).
  Proof.
    intros.
    destruct H0.
    apply pm_welformed_def.
    intros p' ph'; intros.
    rewrite pm_ph_signal_rw with (ph:=ph) in H2; auto.
    rewrite Map_PHID_Facts.add_mapsto_iff in H2.
    destruct H2.
    - destruct H2; subst.
      assert (Phaser.Reduces ph t SIGNAL (signal t ph)). {
        apply ph_reduces.
        simpl.
        trivial.
      }
      assert (Phaser.Welformed ph) by (inversion H; eauto).
      eauto using ph_signal_preserves_welformed.
    - destruct H2.
      inversion H; eauto.
  Qed.

  Lemma pm_ph_drop_preserves_welformed:
    forall p t m,
    Welformed m ->
    PhDropPre p t m ->
    Welformed (ph_drop p t m).
  Proof.
    intros.
    destruct H0.
    apply pm_welformed_def.
    intros p' ph'; intros.
    rewrite pm_ph_drop_rw with (ph:=ph) in H2; auto.
    rewrite Map_PHID_Facts.add_mapsto_iff in H2.
    destruct H2.
    - destruct H2; subst.
      assert (Phaser.Reduces ph t DROP (drop t ph)). {
        apply ph_reduces.
        simpl.
        trivial.
      }
      assert (Phaser.Welformed ph) by (inversion H; eauto).
      eauto using ph_drop_preserves_welformed.
    - destruct H2.
      inversion H; eauto.
  Qed.

  Lemma pm_signal_all_preserves_welformed:
    forall t m,
    Welformed m ->
    Welformed (signal_all t m).
  Proof.
    intros.
    unfold signal_all.
    apply pm_welformed_def.
    intros.
    rewrite pm_foreach_mapsto_rw in H0.
    destruct H0 as (ph', (Heq, mt)).
    subst.
    assert (Phaser.Welformed ph') by (inversion H; eauto).
    auto using ph_signal_preserves_welformed.
  Qed.

  Lemma pm_wait_all_preserves_welformed:
    forall t m,
    Welformed m ->
    WaitAllPre t m ->
    Welformed (wait_all t m).
  Proof.
    intros.
    unfold wait_all.
    apply pm_welformed_def.
    intros.
    rewrite pm_foreach_mapsto_rw in H1.
    destruct H1 as (ph', (Heq, mt)).
    subst.
    destruct (Map_TID_Extra.in_dec tid_eq_rw t ph'). {
      assert (Phaser.WaitPre t ph')
      by (inversion H0; eauto).
      assert (Phaser.Welformed ph') by (inversion H; eauto).
      auto using ph_wait_preserves_welformed.
    }
    unfold wait.
    unfold Phaser.update.
    rewrite Map_TID_Facts.not_find_in_iff in n.
    rewrite n.
    inversion H; eauto.
  Qed.

  Lemma pm_drop_all_preserves_welformed:
    forall t m,
    Welformed m ->
    Welformed (drop_all t m).
  Proof.
    intros.
    unfold drop_all.
    apply pm_welformed_def.
    intros.
    rewrite pm_foreach_mapsto_rw in H0.
    destruct H0 as (ph', (Heq, mt)).
    subst.
    assert (Phaser.Welformed ph') by (inversion H; eauto).
    eauto using ph_drop_preserves_welformed.
  Qed.

  Lemma pm_async_preserves_welformed:
    forall l t' t m,
    Welformed m ->
    AsyncPre l t' t m ->
    Welformed (async l t' t m).
  Proof.
    intros.
    induction l; auto.
    inversion H0.
    simpl.
    destruct a.
    apply async_pre_inv in H0.
    apply IHl in H0.
    clear IHl.
    inversion H1; subst; clear H1.
    inversion H6.
    simpl in *.
    unfold async_1.
    remember (Map_PHID.find _ _).
    symmetry in Heqo.
    destruct o as [ph'|]; auto.
    apply pm_welformed_add; auto.
    apply ph_register_preserves_welformed.
    - rewrite <- Map_PHID_Facts.find_mapsto_iff in Heqo.
      inversion H0; eauto.
    - inversion H2; subst; clear H2.
      assert (ph' = ph). {
        apply Map_PHID_Facts.find_mapsto_iff in Heqo.
        eauto using async_notina_mapsto, Map_PHID_Facts.MapsTo_fun.
      }
      subst.
      auto.
  Qed.
  (* end hide *)
  
  Lemma pm_reduces_preserves_welformed:
    forall m t o m',
    Welformed m ->
    Reduces m t o m' ->
    Welformed m'.
  Proof.
    intros.
    destruct H0.
    destruct o; simpl in *.
    - auto using pm_ph_new_preserves_welformed.
    - auto using pm_ph_signal_preserves_welformed.
    - auto using pm_ph_drop_preserves_welformed.
    - auto using pm_signal_all_preserves_welformed.
    - auto using pm_wait_all_preserves_welformed.
    - auto using pm_drop_all_preserves_welformed.
    - auto using pm_async_preserves_welformed.
  Qed.
End Phasermap.
