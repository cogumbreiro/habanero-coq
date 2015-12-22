Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.

Require Import HJ.Vars.
Require Import HJ.Phasers.Welformedness.

Set Implict Arguments.

(**
  Phase-ordering is a phaser-level property that considers the
  relationship between two arbitrary taskviews.
  It is a correctness property that lets us reason about the "temporal" ordering
  of a taskview, with respect to a given reduction relation.
  
  Phase ordering is a way
  to compare the various members, the taskviews, of a phaser. We say that
  v1 <= v2 if (i) the wait phase of v1 is smaller than or equals the signal phase
  of v2, (ii) v2 has signal-only mode, or (iii) v1 has wait-only mode. 
  
  
  There are two important ideas behind the Phase Ordering property, both
  capture how phaser synchronization develops. The first idea is that
  phase ordering defines the correctness of synchronization: for any
  taskviews v1 and v2 picked from the same phaser we have that v1 <= v2,
  that is the wait phase of v1 is at *most* as great as the signal-phase of v2,
  but not greater. For instance, after executing a wait, the task's signal
  phase must be greater-than or equal other members' wait phase. 
  
  
*)
Section Defs.
  Require Import HJ.Phasers.Regmode.
  Require Import HJ.Phasers.Taskview.
  Import Welformedness.Taskview.

  Inductive HappensBefore v1 v2 : Prop :=
    tv_hb_def:
      signal_phase v1 < wait_phase v2 ->
      SignalCap (mode v1) ->
      WaitCap (mode v2) ->
      HappensBefore v1 v2.

  (** v2 is beghind of v1, or v1 and v2 intersect. *)

  Inductive Facilitates v1 v2 : Prop := 
    | tv_nhb_ge:
       signal_phase v1 >= wait_phase v2 ->
       Facilitates v1 v2
    | tv_nhb_so:
      mode v2 = SIGNAL_ONLY ->
      Facilitates v1 v2
    | tv_nhb_wo:
      mode v1 = WAIT_ONLY ->
      Facilitates v1 v2.

  Definition MayHappenParallel v1 v2 := Facilitates v2 v1.

  Definition BlockedBy v1 v2 := HappensBefore v2 v1.
End Defs.


Module Notations.
  Infix "<" := HappensBefore : phaser_scope.
  Infix ">" := BlockedBy : phaser_scope.
  Infix "<=" := MayHappenParallel : phaser_scope.
  Infix ">=" := Facilitates : phaser_scope.
End Notations.


Section Facts.    
  Open Scope phaser_scope.
  Import Notations.
  Import Welformedness.Taskview.

  Lemma le_spec:
    forall v1 v2,
    v1 <= v2 <-> v2 >= v1.
  Proof.
    split; auto.
  Qed.

  Lemma lt_spec:
    forall v1 v2,
    v1 < v2 <-> v2 > v1.
  Proof.
    split; auto.
  Qed.

  Lemma tv_nhb_dec:
    forall v1 v2,
    { v1 >= v2 } + { ~ v1 >= v2 }.
  Proof.
    intros.
    destruct (ge_dec (signal_phase v1) (wait_phase v2)).
    { left; auto using tv_nhb_ge. }
    destruct (regmode_eq_dec (mode v2) SIGNAL_ONLY).
    { left; auto using tv_nhb_so. }
    destruct (regmode_eq_dec (mode v1) WAIT_ONLY).
    { left; auto using tv_nhb_wo. }
    right.
    intuition.
  Qed.

  Lemma tv_hb_dec:
    forall v1 v2,
    { v1 < v2 } + { ~ v1 < v2 }.
  Proof.
    intros.
    destruct (wait_cap_dec (mode v2)). {
      destruct (signal_cap_dec (mode v1)). {
        destruct (lt_dec (signal_phase v1) (wait_phase v2)). {
          left; auto using tv_hb_def.
        }
        right; intuition.
      }
      right; intuition.
    }
    right; intuition.
  Qed.

  Lemma tv_nhb_to_not_lt:
    forall v1 v2,
    v1 >= v2 -> ~ v1 < v2.
  Proof.
    intros.
    intuition.
    - destruct H0; inversion H3.
    - destruct H2; inversion H3.
  Qed.

  Lemma tv_hb_to_not_ge:
    forall v1 v2,
    v1 < v2 -> ~ v1 >= v2.
  Proof.
    intros.
    intuition.
    - destruct H; inversion H3.
    - inversion H2; rewrite H3 in *; inversion H4.
  Qed.

  Lemma tv_not_lt_to_ge:
    forall v1 v2,
    ~ v1 < v2 -> v1 >= v2.
  Proof.
    intros.
    destruct (ge_dec (signal_phase v1) (wait_phase v2)).
    { auto using tv_nhb_ge. }
    destruct (regmode_eq_dec (mode v2) SIGNAL_ONLY).
    { auto using tv_nhb_so. }
    destruct (regmode_eq_dec (mode v1) WAIT_ONLY).
    { auto using tv_nhb_wo. }
    assert (HappensBefore v1 v2). {
      assert (signal_phase v1 < wait_phase v2) % nat by intuition.
      auto using tv_hb_def, neq_wo_to_signal_cap, neq_so_to_wait_cap.
    }
    contradiction.
  Qed.

  Lemma tv_not_lt_rw_tv_ge:
    forall v1 v2,
    ~ v1 < v2 <-> v1 >= v2.
  Proof.
    split; auto using tv_not_lt_to_ge, tv_nhb_to_not_lt.
  Qed.

  Lemma tv_not_ge_to_lt:
    forall v1 v2,
    ~ v1 >= v2 -> v1 < v2.
  Proof.
    intros.
    destruct (wait_cap_dec (mode v2)). {
      destruct (signal_cap_dec (mode v1)). {
        destruct (lt_dec (signal_phase v1) (wait_phase v2)). {
          auto using tv_hb_def.
        }
        assert (Facilitates v1 v2). {
          assert (signal_phase v1 >= wait_phase v2) % nat by intuition.
          auto using tv_nhb_ge.
        }
        contradiction.
      }
      assert (Facilitates v1 v2) by
        auto using tv_nhb_wo, not_signal_cap_to_wo.
      contradiction.
    }
    assert (Facilitates v1 v2) by
      auto using tv_nhb_so, not_wait_cap_to_so.
    contradiction.
  Qed.

  Lemma tv_not_ge_rw_lt:
    forall v1 v2,
    ~ v1 >= v2 <-> v1 < v2.
  Proof.
    split; auto using tv_not_ge_to_lt, tv_hb_to_not_ge.
  Qed.

  Lemma tv_hb_ge_dec:
    forall v1 v2,
    { v1 < v2 } + { v1 >= v2 }.
  Proof.
    intros.
    destruct (tv_hb_dec v1 v2);
    auto using tv_not_lt_to_ge.
  Qed.

  Lemma tv_welformed_to_ge_refl:
    forall v,
    Welformed v ->
    v >= v.
  Proof.
    intros.
    inversion H;
      apply tv_nhb_ge;
      intuition.
  Qed.

  Let signal_preserves_lhs:
    forall v,
    Welformed v ->
    forall v',
    v >= v' ->
    (Taskview.signal v) >= v'.
  Proof.
    intros.
    inversion H0; subst.
    - apply tv_nhb_ge.
      destruct (signal_phase_signal_inv _ H); intuition.
    - auto using tv_nhb_so.
    - rewrite <- signal_preserves_mode in *.
      auto using tv_nhb_wo.
  Qed.

  Lemma signal_preserves_rhs:
    forall v1 v2,
    v1 >= v2 ->
    v1 >= (Taskview.signal v2).
  Proof.
    intros.
    inversion H; subst.
    - apply tv_nhb_ge.
      rewrite signal_preserves_wait_phase.
      assumption.
    - apply tv_nhb_so.
      rewrite signal_preserves_mode.
      assumption.
    - auto using tv_nhb_wo.
  Qed.

  Section wait_preserves_rhs.
  Variable v1 v2: taskview.
  Variable G1: v1 >= v2.
  Variable L1: SignalCap (mode v1) -> (signal_phase v1 >= signal_phase v2)%nat.
  Variable L2: WaitPre v2.
  Lemma wait_preserves_rhs:
    v1 >= (wait v2).
  Proof.
    intros.
    inversion G1; subst; clear G1.
    - destruct (signal_cap_wo_dec (mode v1)). {
        apply tv_nhb_ge.
        apply L1 in s.
        rewrite wait_wait_phase.
        inversion L2.
        intuition.
      }
      auto using tv_nhb_wo.
    - apply tv_nhb_so.
      rewrite wait_preserves_mode.
      assumption.
    - auto using tv_nhb_wo.
  Qed.
  End wait_preserves_rhs.

  Let tv_signal_ge_lhs:
    forall v v',
    Welformed v ->
    Reduces v SIGNAL v' ->
    Facilitates v' v.
  Proof.
    intros.
    inversion H0.
    subst.
    apply signal_preserves_lhs; auto using tv_welformed_to_ge_refl.
  Qed.

  Let tv_wait_ge_lhs:
    forall v,
    WaitPre v ->
    Facilitates (wait v) v.
  Proof.
    intros.
    destruct H.
    apply tv_nhb_ge.
    intuition.
 Qed.

  Let tv_nhb_reduces:
    forall v o v',
    Welformed v ->
    Reduces v o v' ->
    Facilitates v' v.
  Proof.
    intros.
    inversion H0; subst.
    - auto using tv_signal_ge_lhs.
    - auto using tv_wait_ge_lhs.
  Qed.

  Let tv_nhb_reduces_trans_sw:
    forall x o y o' z,
    Welformed x ->
    Welformed y ->
    Welformed z ->
    Reduces x o y ->
    Reduces y o' z ->
    mode x = SIGNAL_WAIT ->
    (signal_phase z >= wait_phase x)%nat.
  Proof.
    intros.
    assert (Facilitates z y) by eauto using tv_nhb_reduces.
    assert (Facilitates y x) by eauto using tv_nhb_reduces.
    destruct o.
    - apply reduces_rw_signal in H2.
      destruct o'.
      + apply reduces_rw_signal in H3.
        assert (R: mode z = mode x). {
          subst.
          repeat rewrite signal_preserves_mode in *.
          trivial.
        }
        assert (WaitCap (mode z)). {
          rewrite R.
          rewrite H4.
          apply wait_cap_sw.
        }
        subst.
        assert (WaitCap (mode x)). {
          rewrite H4.
          apply wait_cap_sw.
        }
        rewrite signal_signal_wait_cap; auto.
        rewrite signal_wait_cap_signal_phase; (intuition || auto).
      + apply reduces_rw_wait in H3.
        assert (wait_phase x <= signal_phase x)%nat by auto
          using welformed_wait_phase_le_signal_phase.
        subst.
        rewrite wait_preserves_signal_phase.
        assert (signal_phase x <= signal_phase (signal x)) % nat. {
          auto using signal_phase_le_signal.
        }
        intuition.
    - assert (WaitCap (mode x)). {
        rewrite H4.
        auto using wait_cap_sw.
      }
      assert (o' = SIGNAL) by eauto using reduces_trans_inv.
      subst.
      assert (R: signal_phase y = wait_phase y) by eauto using reduces_wait_inv_wait_cap.
      inversion H2; subst.
      inversion H3; subst.
      rewrite wait_preserves_signal_phase in *.
      rewrite signal_wait_cap_signal_phase in *; auto.
      rewrite wait_wait_phase in *.
      intuition.
  Qed.

  Let tv_eval_preserves_le:
    forall v1 v2 o,
    Welformed v1 ->
    (signal_phase v1 >= wait_phase v2)%nat ->
    (signal_phase (eval o v1) >= wait_phase v2)%nat.
  Proof.
    intros.
    destruct o; simpl.
    - apply signal_phase_le_signal in H.
      intuition.
    - assumption.
  Qed.

  Lemma tv_lhs_eval_ge:
    forall v1 v2 v1' o,
    Welformed v1 ->
    Facilitates v1 v2 ->
    Reduces v1 o v1' ->
    Facilitates v1' v2.
  Proof.
    intros.
    inversion H0.
    - apply tv_nhb_ge.
      apply reduces_spec in H1.
      subst.
      auto using tv_eval_preserves_le.
    - auto using tv_nhb_so.
    - apply reduces_preserves_mode in H1.
      rewrite H2 in H1.
      auto using tv_nhb_wo.
  Qed.

  Lemma tv_nhb_eval_lhs:
    forall v1 v2 o,
    Welformed v1 ->
    Facilitates v1 v2 ->
    Reduces v1 o (eval o v1) ->
    Facilitates (eval o v1) v2.
  Proof.
    intros.
    inversion H0.
    - apply tv_nhb_ge.
      destruct o; simpl in *.
      + apply signal_phase_signal_inv in H; intuition.
      + assumption.
    - auto using tv_nhb_so.
    - apply tv_nhb_wo.
      rewrite eval_preserves_mode.
      assumption.
  Qed.

  Theorem tv_lt_irreflexive:
    forall v,
    Welformed v ->
    ~ (HappensBefore v v).
  Proof.
    intros.
    rewrite tv_not_lt_rw_tv_ge.
    auto using tv_welformed_to_ge_refl.
  Qed.

  Theorem tv_lt_trans:
    forall x y z,
    Welformed y ->
    x < y ->
    y < z ->
    x < z.
  Proof.
    intros.
    inversion H0.
    inversion H1.
    apply tv_hb_def; auto.
    assert (wait_phase y <= signal_phase y)%nat
    by auto using welformed_wait_phase_le_signal_phase.
    intuition.
  Qed.

  Section Antisym.

  Variable x y:taskview.
  
  Variable wfx: Welformed x.
  Variable wfy: Welformed y.

  Theorem tv_lt_antisym:
    x < y ->
    ~ (y < x).
  Proof.
    intros.
    rewrite tv_not_lt_rw_tv_ge.
    inversion H; clear H.
    destruct x as (sx, wx, rx).
    destruct y as (sy, wy, ry).
    simpl in *.
    inversion H1; clear H1. {
      subst.
      inversion H2; clear H2. {
        subst; simpl in *.
        apply tv_nhb_ge.
        simpl in *.
        inversion wfx; simpl in *; subst;
        inversion wfy; simpl in *; subst; intuition.
      }
      subst.
      auto using tv_nhb_wo.
    }
    subst.
    auto using tv_nhb_so.
  Qed.
  End Antisym.

  Lemma lt_trans_ex:
    forall x y y' z,
    x < y ->
    y <= y' ->
    y' < z ->
    x < z.
  Proof.
    intros.
    inversion H; clear H.
    inversion H1; clear H1.
    apply tv_hb_def; auto.
    inversion H0.
    - intuition.
    - rewrite H1 in *.
      inversion H4.
    - rewrite H1 in *.
      inversion H5.
  Qed.

  Example tv_ex_1:
    {| signal_phase := 0; wait_phase := 0; mode := SIGNAL_WAIT |} <
    {| signal_phase := 1; wait_phase := 1; mode := SIGNAL_WAIT |}.
  Proof.
    eauto using tv_hb_def.
  Qed.

  Example tv_ex_2:
    forall (v:taskview),
    SignalPre v ->
    WaitPre (signal v) ->
    mode v = SIGNAL_WAIT ->
    v < (wait (signal v)).
  Proof.
    intros.
    inversion H0; clear H0.
    apply tv_hb_def.
    - rewrite wait_wait_phase.
      rewrite signal_preserves_wait_phase.
      inversion H.
      + intuition.
      + rewrite H0 in *.
        inversion H1.
    - rewrite H1.
      apply signal_cap_sw.
    - rewrite wait_preserves_mode.
      rewrite signal_preserves_mode.
      rewrite H1.
      apply wait_cap_sw.
  Qed.
End Facts.

