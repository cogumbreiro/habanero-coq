Require Import HJ.Vars.
Require Import HJ.Phasers.Lang.

Open Scope nat.

Module Taskview.

  (** Valid task view *)
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

  Lemma welformed_wait_phase_le_signal_phase:
    forall v,
    Welformed v ->
    wait_phase v <= signal_phase v.
  Proof.
    intros.
    inversion H; intuition.
  Qed.

  Lemma make_welformed:
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

  Lemma signal_preserves_welformed:
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

  Lemma wait_preserves_welformed:
    forall v,
    Welformed v ->
    wait_phase v < signal_phase v ->
    Welformed (Taskview.wait v).
  Proof.
    intros.
    inversion H.
    - assert (wait_phase v <> signal_phase v) by intuition.
      contradiction.
    - apply tv_welformed_wait_cap_eq.
      rewrite wait_preserves_mode; auto.
      rewrite wait_preserves_signal_phase.
      rewrite <- H2.
      rewrite wait_wait_phase.
      trivial.
    - apply tv_welformed_so.
      rewrite wait_preserves_mode; auto.
      rewrite wait_wait_phase.
      rewrite wait_preserves_signal_phase.
      intuition.
  Qed.

  Theorem tv_reduction_preserves_welformed:
    forall v o v',
    Welformed v ->
    Semantics.Reduce v o v' ->
    Welformed v'.
  Proof.
    intros.
    inversion H0;
    subst; 
    auto using signal_preserves_welformed, wait_preserves_welformed.
  Qed.

  Lemma signal_phase_signal_inv:
    forall v,
    Welformed v ->
    signal_phase (signal v) = signal_phase v
    \/ signal_phase (signal v) = S (signal_phase v).
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

  Lemma reduce_wait_post:
    forall v v',
    Welformed v ->
    Semantics.Reduce v Semantics.WAIT v' ->
    (mode v' = SIGNAL_ONLY \/ WaitCap (mode v') /\ wait_phase v' = signal_phase v').
  Proof.
    intros.
    inversion H0.
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

  Lemma reduce_wait_inv_wait_cap:
    forall v v',
    Welformed v ->
    WaitCap (mode v) ->
    Semantics.Reduce v Semantics.WAIT v' ->
    signal_phase v' = wait_phase v'.
  Proof.
    intros.
    inversion H1; subst.
    apply reduce_wait_post in H1; auto.
    destruct H1 as [R|(?,?)].
    - (* absurd case *)
      assert (WaitCap (mode (wait v))). {
        auto using wait_preserves_mode.
      }
      rewrite R in *.
      inversion H1.
    - intuition.
  Qed.

  Lemma reduce_trans_inv:
    forall x y z o,
    Welformed x ->
    WaitCap (mode x) ->
    Semantics.Reduce x Semantics.WAIT y ->
    Semantics.Reduce y o z ->
    o = Semantics.SIGNAL.
  Proof.
    intros.
    inversion H1; subst.
    inversion H2; trivial; subst.
    subst.
    apply reduce_wait_post in H1.
    {
      destruct H1 as [?|(?,?)].
      - rewrite wait_cap_rw in *.
        rewrite wait_preserves_mode in *.
        contradiction.
      - rewrite wait_preserves_signal_phase in *.
        rewrite H5 in *.
        assert (signal_phase x <> signal_phase x). {
          intuition.
        }
        assert (signal_phase x = signal_phase x) by auto.
        contradiction.
    }
    assumption.
  Qed.

End Taskview.

Module Phaser.
  Import Taskview.
  Import Lang.Phaser.
  Import Lang.Phaser.Semantics.

  Inductive Welformed (ph:phaser) : Prop :=
    ph_welformed_def:
      (forall t v,
        Map_TID.MapsTo t v ph ->
        Taskview.Welformed v) ->
      Welformed ph.

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
    forall ph t ph',
    Welformed ph ->
    Reduction ph t SIGNAL ph' ->
    Welformed ph'.
  Proof.
    intros.
    inversion H0; subst.
    apply Map_TID_Extra.in_to_mapsto in H1.
    destruct H1 as (v, Hmt).
    assert (R: signal t ph = Map_TID.add t (Taskview.signal v) ph) by auto using ph_signal_spec.
    rewrite R.
    apply ph_welformed_def.
    intros.
    destruct (TID.eq_dec t0 t).
    + subst.
      remember (Taskview.signal _) as v'.
      assert (v0 = v'). {
        assert (Map_TID.MapsTo t v' (Map_TID.add t v' ph)) by auto using Map_TID.add_1.
        eauto using Map_TID_Facts.MapsTo_fun.
      }
      subst.
      assert (Taskview.Welformed v) by eauto using ph_welformed_to_tv_welformed.
      auto using signal_preserves_welformed.
    + apply Map_TID_Facts.add_neq_mapsto_iff in H1; auto with *.
      eauto using ph_welformed_to_tv_welformed.
  Qed.

  Lemma ph_wait_preserves_welformed:
    forall ph t ph',
    Welformed ph ->
    Reduction ph t WAIT ph' ->
    Welformed ph'.
  Proof.
    intros.
    inversion H0; subst.
    assert (R: wait t ph = Map_TID.add t (Taskview.wait v) ph) by auto using ph_wait_spec.
    rewrite R; clear R.
    apply ph_welformed_def.
    intros.
    destruct (TID.eq_dec t0 t).
    + subst.
      remember (Taskview.wait _) as v'.
      assert (v0 = v'). {
        assert (Map_TID.MapsTo t v' (Map_TID.add t v' ph)) by auto using Map_TID.add_1.
        eauto using Map_TID_Facts.MapsTo_fun.
      }
      subst.
      assert (Taskview.Welformed v) by eauto using ph_welformed_to_tv_welformed.
      auto using wait_preserves_welformed.
    + apply Map_TID_Facts.add_neq_mapsto_iff in H4; auto with *.
      eauto using ph_welformed_to_tv_welformed.
  Qed.

  Lemma ph_drop_preserves_welformed:
    forall ph t ph',
    Welformed ph ->
    Reduction ph t DROP ph' ->
    Welformed ph'.
  Proof.
    intros.
    inversion H0; subst.
    unfold drop in *.
    apply ph_welformed_def.
    intros.
    rewrite Map_TID_Facts.remove_mapsto_iff in H2.
    destruct H2.
    eauto using ph_welformed_to_tv_welformed.
  Qed.

  Lemma ph_register_preserves_welformed:
    forall ph t v ph',
    Welformed ph ->
    Taskview.Welformed v ->
    Reduction ph t (REGISTER v) ph' ->
    Welformed ph'.
  Proof.
    intros.
    inversion H1; subst.
    assert (R: register t v ph = Map_TID.add t v ph) by auto using ph_register_spec.
    rewrite R; clear R.
    apply ph_welformed_def.
    intros.
    destruct (TID.eq_dec t0 t).
    + subst.
      assert (v0 = v). {
        assert (Map_TID.MapsTo t v (Map_TID.add t v ph)) by auto using Map_TID.add_1.
        eauto using Map_TID_Facts.MapsTo_fun.
      }
      subst.
      assumption.
    + apply Map_TID_Facts.add_neq_mapsto_iff in H2; auto with *.
      eauto using ph_welformed_to_tv_welformed.
  Qed.

  Inductive WelformedOp : op -> Prop :=
    | welformed_op_signal:
      WelformedOp SIGNAL
    | welformed_op_wait:
      WelformedOp WAIT
    | welformed_op_drop:
      WelformedOp DROP
    | welformed_op_register:
      forall v,
      Taskview.Welformed v ->
      WelformedOp (REGISTER v).

  Lemma ph_reduce_preserves_welformed:
    forall ph t o ph',
    Welformed ph ->
    WelformedOp o ->
    Reduction ph t o ph' ->
    Welformed ph'.
  Proof.
    intros.
    inversion H1; subst; inversion H0;
    eauto using
      ph_signal_preserves_welformed,
      ph_wait_preserves_welformed,
      ph_drop_preserves_welformed,
      ph_register_preserves_welformed.
  Qed.
End Phaser.