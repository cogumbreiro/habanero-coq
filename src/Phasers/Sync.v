Require Import HJ.Vars.
Require Import HJ.Phasers.Phaser.
Require Import HJ.Phasers.Welformedness.
Require Import HJ.Phasers.Regmode.
Require Import HJ.Phasers.Taskview.
Require Import HJ.Phasers.Phaser.

Section ReducesPreservesAwait.
  Import Welformedness.Taskview.
  Import Welformedness.Phaser.
  Variable ph: phaser.
  Variable n: nat.
  Variable wf: WellFormed ph.
  Variable W: Await ph n.

  Lemma ph_signal_preserves_await:
    forall t,
    SignalPre t ph ->
    Await (signal t ph) n.
  Proof.
    intros.
    apply await_def.
    intros ? ? mt1 Hs.
    apply signal_mapsto_inv in mt1.
    destruct mt1.
    - destruct a as (E, (v', (R, mt2))).
      symmetry in E.
      subst.
      rewrite signal_preserves_mode in Hs.
      assert (signal_phase v' >= n) by (inversion W; eauto).
      assert (signal_phase v' <= signal_phase (Taskview.signal v')). {
        assert (Taskview.WellFormed v') by (inversion wf; eauto).
        eauto using signal_phase_le_signal.
      }
      intuition.
    - destruct a.
      inversion W; eauto.
  Qed.

  Lemma ph_wait_preserves_await:
    forall t,
    WaitPre t ph ->
    Await (wait t ph) n.
  Proof.
    intros.
    apply await_def.
    intros ? ? mt1 Hs.
    apply wait_mapsto_inv in mt1.
    destruct mt1.
    - destruct a as (E, (v', (R, mt2))).
      symmetry in E.
      subst.
      rewrite wait_preserves_mode in Hs.
      assert (signal_phase v' >= n) by (inversion W; eauto).
      rewrite wait_preserves_signal_phase.
      assumption.
    - destruct a.
      inversion W; eauto.
  Qed.

  Lemma ph_drop_preserves_await:
    forall t,
    DropPre t ph ->
    Await (drop t ph) n.
  Proof.
    intros.
    apply await_def.
    intros ? ? mt1 Hs.
    apply drop_mapsto_inv in mt1.
    destruct mt1.
    inversion W; eauto.
  Qed.

  Lemma ph_register_preserves_await:
    forall r t,
    RegisterPre r t ph ->
    Await (register r t ph) n.
  Proof.
    intros.
    apply await_def.
    intros ? ? mt1 Hs.
    apply register_inv_mapsto in mt1.
    destruct mt1.
    - inversion W; eauto.
    - destruct H0 as (R1, (v', (mt2, R2))).
      subst.
      rewrite set_mode_preserves_signal_phase.
      inversion W.
      apply H0 with (t:=t); auto.
      rewrite mode_set_mode_rw in *.
      inversion H.
      assert (v' = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      inversion H3.
      * rewrite H5 in *.
        rewrite H6 in *.
        assumption.
      * rewrite H5 in *.
        rewrite H6 in *.
        assumption.
      * subst.
        auto using can_signal_sw.
  Qed.
    

  Lemma ph_reduces_preserves_await:
    forall ph' t o,
    Reduces ph t o ph' ->
    Await ph' n.
  Proof.
    intros.
    destruct o; inversion H; simpl in *; subst.
    - auto using ph_signal_preserves_await.
    - auto using ph_wait_preserves_await.
    - auto using ph_drop_preserves_await.
    - auto using ph_register_preserves_await.
  Qed.
  End ReducesPreservesAwait.

  Section PhReducesAwaitEnabled.
    Import Welformedness.Phaser.
    Variable ph1 ph2 ph1': phaser.
    Variable wf1: WellFormed ph1.
    Variable t t': tid.
    Variable o: op.
    Variable Hneq: t' <> t.
    Variable R1: Reduces ph1 t WAIT ph1'.
    Variable R2: Reduces ph1 t' o ph2.

  Axiom ph_reduces_disjoint:
    forall ph t o ph' v,
    t' <> t ->
    Map_TID.MapsTo t v ph ->
    Reduces ph t' o ph' ->
    Map_TID.MapsTo t v ph'.

  Lemma ph_reduces_preserves_wait:
    Reduces ph2 t WAIT (wait t ph2).
  Proof.
    intros.
    inversion R1;
    simpl in *; clear R1; subst.
    inversion H; clear H; subst.
    assert (Map_TID.MapsTo t v ph2)
    by eauto using ph_reduces_disjoint.
    apply ph_reduces.
    simpl in *.
    apply wait_pre with (v:=v); auto.
    inversion H2; subst.
    - assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      eauto using sync_so.
    - assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      eauto using sync_wait, ph_reduces_preserves_await.
  Qed.
  End PhReducesAwaitEnabled.

(*
  Section PhReducesEnabled.
    Variable ph1 ph2 ph1': phaser.
    Variable wf1: Welformed ph1.
    Variable t t': tid.
    Variable o o': op.
    Variable Hneq: t' <> t.
    Variable R1: Reduces ph1 t o ph1'.
    Variable R2: Reduces ph1 t' o' ph2.

  Lemma ph_reduces_preserves_enabled:
    exists ph2', Reduces ph2 t o ph2'.
  Proof.
    intros.
    destruct o.
    - 
    inversion R1;
    simpl in *; clear R1; subst.
    destruct o
    inversion H; clear H; subst.
    assert (Map_TID.MapsTo t v ph2)
    by eauto using ph_reduces_disjoint.
    apply ph_reduces.
    simpl in *.
    apply wait_pre with (v:=v); auto.
    inversion H2; subst.
    - assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      eauto using sync_so.
    - assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      eauto using sync_wait, ph_reduces_preserves_await.
  Qed.
  End PhReducesAwaitEnabled.
*)