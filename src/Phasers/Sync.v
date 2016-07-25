Require Import HJ.Vars.
Require Import HJ.Phasers.Phaser.
Require Import HJ.Phasers.WellFormed.
Require Import HJ.Phasers.Regmode.
Require Import HJ.Phasers.Taskview.
Require Import HJ.Phasers.Phaser.

(** Show that [Await ph n] is a stable property. *)

Section ReducesPreservesAwait.
  Import WellFormed.Taskview.
  Import WellFormed.Phaser.
  Variable ph: phaser.
  Variable n: nat.
  Variable wf: WellFormed ph.
  Variable W: Phase ph n.

  Let ph_signal_preserves_await:
    forall t,
    SignalPre t ph ->
    Phase (signal t ph) n.
  Proof.
    intros.
    apply phase_def.
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

  Let ph_wait_preserves_await:
    forall t,
    WaitPre t ph ->
    Phase (wait t ph) n.
  Proof.
    intros.
    apply phase_def.
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

  Let ph_drop_preserves_await:
    forall t,
    DropPre t ph ->
    Phase (drop t ph) n.
  Proof.
    intros.
    apply phase_def.
    intros ? ? mt1 Hs.
    apply drop_mapsto_inv in mt1.
    destruct mt1.
    inversion W; eauto.
  Qed.

  Let ph_register_preserves_await:
    forall r t,
    RegisterPre r t ph ->
    Phase (register r t ph) n.
  Proof.
    intros.
    apply phase_def.
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

  Theorem ph_reduces_preserves_await:
    forall ph' t o,
    Reduces ph t o ph' ->
    Phase ph' n.
  Proof.
    intros.
    destruct o; inversion H; simpl in *; subst.
    - auto using ph_signal_preserves_await.
    - auto using ph_wait_preserves_await.
    - auto using ph_drop_preserves_await.
    - auto using ph_register_preserves_await.
  Qed.
End ReducesPreservesAwait.
