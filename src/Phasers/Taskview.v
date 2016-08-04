Require Import HJ.Phasers.Regmode.

Section Defs.
  (**
    The taskview represents the local view of a phaser that a registered
    task has. It records: the number of signals
    the task issued, the number of waits the task issued, and the task's
    registration mode. The taskview is changed by invoking signal and wait
    on a phaser (or next). 
  *)

  Record taskview := mk_taskview {
    signal_phase: nat;
    wait_phase: nat;
    mode: regmode
  }.

  (** * Creation *)

  (**
    When creating a phaser, the creator is the only task registered in that phaser.
    Value [make] represents the first taskview that is initialized in [SIGNAL_WAIT] mode
    and accounts for zero signals and zero waits.
  *)

  Definition make := mk_taskview 0 0 SIGNAL_WAIT.

  (** * Basic mutators *)

  (** We define the mutators of a taskview. These are only used internally. *)

  Definition set_signal_phase v n := mk_taskview n (wait_phase v) (mode v).
  Definition set_wait_phase v n := mk_taskview (signal_phase v) n (mode v).
  Definition set_mode v m := mk_taskview (signal_phase v) (wait_phase v) m.

  (** * Signal *)

  (** 
    The two mutators available of taskviews are signal and wait, defined following.
    The semantics of signal depends on the
    registration mode of the issuer (this is captured by [SignalPre]: 
    [SIGNAL_WAIT] tasks interleave signals and waits and the first operation is a signal;
    [SIGNAL_ONLY] tasks can always issue a signal.
  *)

  Inductive SignalPre v: Prop :=
    | signal_pre_w:
      mode v = SIGNAL_WAIT ->
      wait_phase v = signal_phase v ->
      SignalPre v
    | signal_pre_s:
      mode v = SIGNAL_ONLY ->
      SignalPre v.

  (** The operation simply increments the signal phase. *)

  Definition signal v := set_signal_phase v (S (signal_phase v)).

  (**
    At the language-level, however, invoking [signal] multiple times is not considered
    an error, yet only the first [signal] after a [wait] is observed. Precondition [SignalPre v]
    models the first [signal] after a wait.
    Function [try_signal] can be invoked without a pre-condition and models the user-facing
    signal operation.
  *)

  Definition try_signal v :=
  match mode v with
  | SIGNAL_WAIT => set_signal_phase v (S (wait_phase v))
  | _ => signal v
  end.

  (** * Wait *)

  (**
    The wait operation increments the wait-phase.
    A [SIGNAL_WAIT] task must have signalled before invoking wait.
    Tasks registered as [WAIT_ONLY] are always capable of invoking a wait.
    [SIGNAL_ONLY] tasks cannot issue a wait.
  *)

  Inductive WaitPre v: Prop :=
    | wait_pre_wo:
      mode v = WAIT_ONLY ->
      WaitPre v
    | wait_pre_sw:
      mode v = SIGNAL_WAIT ->
      S (wait_phase v) = signal_phase v ->
      WaitPre v.

  Definition wait v := set_wait_phase v (S (wait_phase v)).


  (** * Small-step operational semantics*)

  (**
    The operational semantics not only defines a closed set of operations that
    can operate on a value (here a taskview), but also defines the preconditions of
    each operation.
    Contrary to [eval], relation [Reduces] defines a precondition
    to [wait], called [WaitPre]: in order to issue a wait, the wait phase must be
    behind (smaller than) the signal phase. We define [CanWait] so it can be reused
    in other developments.

    The operational semantics of taskviews defines a closed set of operations [op]
    that can change taskviews, signal and  wait.
  *)

  Inductive op := SIGNAL | WAIT.

  (**
  Function [eval] interprets the given operation [o] as the appropriate function.
  *)

  Definition eval o :=
  match o with
  | SIGNAL => signal
  | WAIT => wait
  end.

  Inductive Reduces v : op -> taskview -> Prop :=
    | tv_reduces_signal:
      SignalPre v ->
      Reduces v SIGNAL (signal v)
    | tv_reduces_wait:
      WaitPre v ->
      Reduces v WAIT (wait v).

End Defs.

Section Facts.
  Import Notations.
  Open Scope reg_scope.

  (**
   We can simplify an expression that sets the mode it already has.
   This lemma also shows the correctness of [set_mode].
   *)
  
  Lemma set_mode_ident:
    forall v,
    set_mode v (mode v) = v.
  Proof.
    intros; destruct v; trivial.
  Qed.

  Lemma mode_set_mode_rw:
    forall v r,
    mode (set_mode v r) = r.
  Proof.
    intros.
    destruct r; simpl; eauto.
  Qed.

  (** A property of correctness: [set_mode] preserves the signal phase. *)
  

  Lemma set_mode_preserves_signal_phase:
    forall v r,
    signal_phase (set_mode v r) =  signal_phase v.
  Proof.
    intros.
    destruct v; auto.
  Qed.

  (** A property of correctness: [set_mode] preserves the wait phase. *)

  Lemma set_mode_preserves_wait_phase:
    forall v r,
    wait_phase (set_mode v r) =  wait_phase v.
  Proof.
    intros.
    destruct v; auto.
  Qed.

  (** The initial taskview is registered in [SIGNAL_WAIT] mode. *)

  Lemma make_mode:
    mode make = SIGNAL_WAIT.
  Proof.
    unfold make.
    auto.
  Qed.

  (** The initial taskview accounts for zero signals. *)

  Lemma make_signal_phase:
    signal_phase make = 0.
  Proof.
    unfold make.
    auto.
  Qed.

  (** The initial taskview accounts for zero waits. *)

  Lemma make_wait_phase:
    wait_phase make = 0.
  Proof.
    unfold make.
    auto.
  Qed.
    
  Ltac simpl_taskview v :=
    destruct v as (?, ?, m); destruct m; simpl in *; subst; intuition.

  Lemma signal_preserves_mode:
    forall v,
    mode (signal v) = mode v.
  Proof.
    intros.
    simpl_taskview v.
  Qed.

  Lemma try_signal_preserves_mode:
    forall v,
    mode (try_signal v) = mode v.
  Proof.
    intros.
    simpl_taskview v.
  Qed.

  Lemma signal_preserves_wait_phase:
    forall v,
    wait_phase (signal v) = wait_phase v.
  Proof.
    intros.
    simpl_taskview v.
  Qed.

  Lemma try_signal_preserves_wait_phase:
    forall v,
    wait_phase (try_signal v) = wait_phase v.
  Proof.
    intros.
    simpl_taskview v.
  Qed.

  Lemma try_signal_signal_phase_sw:
    forall v,
    mode v = SIGNAL_WAIT ->
    S (wait_phase v) = signal_phase (try_signal v).
  Proof.
    intros.
    simpl_taskview v; inversion H.
  Qed.

  Lemma signal_phase_set_signal_phase:
    forall v n,
    signal_phase (set_signal_phase v n) = n.
  Proof.
    intros.
    unfold set_signal_phase.
    auto.
  Qed.

  Lemma signal_so_signal_phase:
    forall v,
    mode v = SIGNAL_ONLY ->
    signal_phase (signal v) = S (signal_phase v).
  Proof.
    intros.
    simpl.
    trivial.
  Qed.

  Lemma wait_preserves_mode:
    forall v,
    mode (wait v) = mode v.
  Proof.
    intros.
    simpl_taskview v.
  Qed.

  Lemma wait_preserves_signal_phase:
    forall v,
    signal_phase (wait v) = signal_phase v.
  Proof.
    intros; simpl_taskview v.
  Qed.

  Lemma wait_phase_set_wait_phase:
    forall v n,
    wait_phase (set_wait_phase v n) = n.
  Proof.
    intros; simpl_taskview v.
  Qed.

  Lemma wait_wait_phase:
    forall v,
    wait_phase (wait v) = S (wait_phase v).
  Proof.
    intros.
    unfold wait.
    destruct (can_signal_wo (mode v)).
    - destruct (mode v);
      inversion c;
      rewrite wait_phase_set_wait_phase;
      trivial.
    - simpl.
      trivial.
  Qed.

  Lemma signal_can_wait_signal_phase:
    forall v,
    SignalPre v ->
    mode v = SIGNAL_WAIT ->
    signal_phase (signal v) = S (wait_phase v).
  Proof.
    intros.
    simpl.
    inversion H; auto.
    rewrite H0 in H1.
    inversion H1.
  Qed.

  Lemma signal_pre_to_can_signal:
    forall v,
    SignalPre v ->
    CanSignal (mode v).
  Proof.
    intros.
    inversion H;
    rewrite H0; auto using can_signal_sw, can_signal_so.
  Qed.
End Facts.

Section Semantics.
  

  (**
  A trivial property we choose to highlight is that [Reduces]
  performs an [eval] on the right-hand side.
  *)

  Lemma reduces_spec:
    forall v o v',
    Reduces v o v' ->
    v' = eval o v.
  Proof.
    intros.
    inversion H; subst; simpl; trivial.
  Qed.

  Lemma reduces_rw_signal:
    forall v v',
    Reduces v SIGNAL v' ->
    v' = signal v.
  Proof.
    intros.
    inversion H.
    trivial.
  Qed.

  Lemma reduces_rw_wait:
    forall v v',
    Reduces v WAIT v' ->
    v' = wait v.
  Proof.
    intros.
    inversion H.
    trivial.
  Qed.

  Lemma eval_preserves_mode:
    forall v o,
    mode (eval o v) = mode v.
  Proof.
    intros.
    destruct o;
    simpl;
    auto using signal_preserves_mode, wait_preserves_mode.
  Qed.

  Lemma reduces_preserves_mode:
    forall v o v',
    Reduces v o v' ->
    mode v' = mode v.
  Proof.
    intros.
    apply reduces_spec in H.
    subst.
    auto using eval_preserves_mode.
  Qed.

  Lemma reduces_signal_inv_sw:
    forall x y z o,
    Reduces x SIGNAL y ->
    Reduces y o z ->
    mode x = SIGNAL_WAIT ->
    o = WAIT.
  Proof.
    intros.
    inversion H; subst.
    assert (wait_phase x = signal_phase x). {
      inversion H2.
      - trivial.
      - rewrite H1 in H3.
        inversion H3.
    }
    destruct H0.
    - assert (wait_phase (signal x) = signal_phase (signal x)). {
        inversion H0.
        - trivial.
        - rewrite signal_preserves_mode in *.
          rewrite H1 in H4.
          inversion H4.
      }
      rewrite signal_preserves_wait_phase in *.
      rewrite H3 in H4.
      simpl in *.
      remember (signal_phase x).
      clear Heqn H3.
      induction n.
      + inversion H4.
      + inversion H4.
        auto.
    - trivial.
  Qed.

  Lemma reduces_wait_inv_sw:
    forall x y z o,
    Reduces x WAIT y ->
    Reduces y o z ->
    mode x = SIGNAL_WAIT ->
    o = SIGNAL.
  Proof.
    intros.
    inversion H; subst.
    assert (S (wait_phase x) = signal_phase x). {
      inversion H2.
      - rewrite H1 in H3.
        inversion H3.
      - trivial.
    }
    destruct H0.
    - trivial.
    - assert (S (wait_phase (wait x)) = signal_phase (wait x)). {
        inversion H0.
        - rewrite wait_preserves_mode in *.
          rewrite H1 in H4.
          inversion H4.
        - trivial.
      }
      rewrite wait_preserves_signal_phase in *.
      simpl in *.
      rewrite <- H3 in H4.
      remember (wait_phase x).
      clear Heqn H3.
      induction n.
      + inversion H4.
      + inversion H4.
        auto.
  Qed.

End Semantics.

