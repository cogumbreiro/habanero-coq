(** * Registration modes *)

(**
  There are three registration modes:
  - [SIGNAL_ONLY] for tasks that do not wait for others and produce signals;
  - [WAIT_ONLY] for tasks that wait for others and do not produce signals;
  - [SIGNAL_WAIT] for tasks that wait for others and produce signals.
*)

Inductive regmode := SIGNAL_ONLY | WAIT_ONLY | SIGNAL_WAIT.

(**
  The relation [r_le], notation <=, establishes an ordering among registration
  modes. This relation plays a crutial role in the registration of tasks.
  Tasks can only register tasks being spawned. Registration must follow the
  Capability rule that states that the registration mode of the spawned task
  cannot be greater than the spawner.
*)

Inductive r_le : regmode -> regmode -> Prop :=
  | r_le_so:
    r_le SIGNAL_ONLY SIGNAL_ONLY
  | r_le_wo:
    r_le WAIT_ONLY WAIT_ONLY
  | r_le_sw:
    forall m,
    r_le m SIGNAL_WAIT.

Module Notations.
  Infix "<=" := (r_le) : reg_scope.
End Notations.

(**
  Two important notions used throught the formalization are wait-/signal-capabilities.
*)

Inductive WaitCap : regmode -> Prop :=
  | wait_cap_sw:
    WaitCap SIGNAL_WAIT
  | wait_cap_wo:
    WaitCap WAIT_ONLY.

Hint Constructors WaitCap.

Inductive SignalCap : regmode -> Prop :=
  | signal_cap_sw:
    SignalCap SIGNAL_WAIT
  | signal_cap_so:
    SignalCap SIGNAL_ONLY.

Hint Constructors SignalCap.

(** * Taskviews *)

(**
  A taskview is the local view of a task over a phaser.
  It records: the number of signals the task issued,
  the number of waits the task issued, and the task's
  registration mode.
*)

Record taskview := TV {
  signal_phase: nat;
  wait_phase: nat;
  mode: regmode
}.

(**
  When creating a phaser, the creator is the only task registered in that phaser.
  The first taskview is initialized in [SIGNAL_WAIT] mode and accounts for zero signals
  and zero waits.
 *)

Definition make := TV 0 0 SIGNAL_WAIT.

(** We define the mutators of a taskview, although they are only used internally. *)

Definition set_signal_phase v n := TV n (wait_phase v) (mode v).
Definition set_wait_phase v n := TV (signal_phase v) n (mode v).
Definition set_mode v m := TV (signal_phase v) (wait_phase v) m.

(** 
  The two available mutators of taskviews are signal and wait, defined following.
  The semantics of signal depends on the
  registration mode of the issuer: when the issuer is registered in signal-only mode,
  a signal increments the signal phase; otherwise, the signal becomes sets the signal-phase
  one phase ahead of the wait phase.
*)

Definition signal v :=
match mode v with
| SIGNAL_ONLY => set_signal_phase v (S (signal_phase v))
| _ => set_signal_phase v (S (wait_phase v))
end.

(**
  A task with wait capability must interleave a signal with an await.
  Only the first signal is observed by other tasks, and consecutive signals are ignored until
  another the task invokes a waits, which is why the signal phase in relation to the wait phase.
  We postpone discussing the error-conditions of invoking signal and wait to
  the presentation of the operational semantics of task view operations.
*)

(**
  The wait operation increments the wait-phase. Altough the semantics of wait does not depends
  on the registration mode, invoking wait should be guarded by a precondition that we postpone
  its definition to the following section.
*)

Definition wait v := set_wait_phase v (S (wait_phase v)).

(* begin hide *)

Section Facts.
  Import Notations.
  Open Scope reg_scope.

  (** The equality of registration mode is decidable. *)

  Lemma regmode_eq_dec:
    forall (m1 m2:regmode),
    { m1 = m2 } + { m1 <> m2 }.
  Proof.
    intros.
    destruct m1, m2; solve [ left; auto | right; intuition; inversion H]. 
  Qed.

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

  (** Checking for the wait capability is a decidable property. *)

  Lemma wait_cap_dec:
    forall r,
    { WaitCap r } + { ~ WaitCap r }.
  Proof.
    intros.
    destruct r; auto.
    right; intuition; inversion H.
  Qed.

  Lemma neq_so_to_wait_cap:
    forall r,
    r <> SIGNAL_ONLY ->
    WaitCap r.
  Proof.
    intros.
    destruct r; auto.
    contradiction H; trivial.
  Qed.

  Lemma wait_cap_to_neq_so:
    forall r,
    WaitCap r ->
    r <> SIGNAL_ONLY.
  Proof.
    intros.
    inversion H;
      subst;
      intuition;
      inversion H0.
  Qed.

  Lemma wait_cap_rw:
    forall r,
    WaitCap r <-> r <> SIGNAL_ONLY.
  Proof.
    intros.
    split; auto using wait_cap_to_neq_so, neq_so_to_wait_cap.
  Qed.

  Lemma not_wait_cap_to_so:
    forall r,
    ~ WaitCap r ->
    r = SIGNAL_ONLY.
  Proof.
    intros.
    destruct r;
    intuition;
    contradiction H;
    auto.
  Qed.

  Lemma so_to_not_wait_cap:
    forall r,
    r = SIGNAL_ONLY ->
    ~ WaitCap r.
  Proof.
    intros.
    intuition.
    inversion H0;
    rewrite <- H1 in *;
    inversion H.
  Qed.

  Lemma wait_cap_so_dec:
    forall r,
    { WaitCap r } + { r = SIGNAL_ONLY }.
  Proof.
    intros.
    destruct (wait_cap_dec r);
    auto using not_wait_cap_to_so.
  Qed.

  Lemma signal_cap_dec:
    forall r,
    { SignalCap r } + { ~ SignalCap r }.
  Proof.
    intros.
    destruct r; auto.
    right; intuition; inversion H.
  Qed.

  Lemma neq_wo_to_signal_cap:
    forall r,
    r <> WAIT_ONLY ->
    SignalCap r.
  Proof.
    destruct r; intuition.
  Qed.

  Lemma signal_cap_to_neq_wo:
    forall r,
    SignalCap r ->
    r <> WAIT_ONLY.
  Proof.
    intros.
    inversion H;
      subst;
      intuition;
      inversion H0.
  Qed.

  Lemma signal_cap_rw:
    forall r,
    SignalCap r <-> r <> WAIT_ONLY.
  Proof.
    intros.
    split; auto using signal_cap_to_neq_wo, neq_wo_to_signal_cap.
  Qed.

  Lemma not_signal_cap_to_wo:
    forall r,
    ~ SignalCap r ->
    r = WAIT_ONLY.
  Proof.
    intros.
    destruct r;
    intuition;
    contradiction H;
    auto.
  Qed.

  Lemma signal_cap_wo_dec:
    forall r,
    { SignalCap r } + { r = WAIT_ONLY }.
  Proof.
    intros.
    destruct (signal_cap_dec r);
    auto using not_signal_cap_to_wo.
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

  Lemma signal_preserves_wait_phase:
    forall v,
    wait_phase (signal v) = wait_phase v.
  Proof.
    intros.
    simpl_taskview v.
  Qed.

  Lemma signal_wait_cap_signal_phase:
    forall v,
    WaitCap (mode v) ->
    signal_phase (signal v) = S (wait_phase v).
  Proof.
    intros.
    simpl_taskview v.
    inversion H.
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
    unfold signal.
    rewrite H.
    rewrite signal_phase_set_signal_phase.
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
    rewrite wait_phase_set_wait_phase.
    trivial.
  Qed.

  Lemma signal_signal_wait_cap:
    forall v,
    WaitCap (mode v) ->
    signal (signal v) = signal v.
  Proof.
    intros.
    inversion H;
      unfold signal;
      unfold set_signal_phase;
      rewrite <- H1;
      simpl;
      auto.
  Qed.
End Facts.

Module Semantics.

(* end hide *)
  
  (** * Small-step operational semantics*)

  (**
  The operational semantics of taskviews defines a closed set of operations [op]
  that can change taskviews, that is signal and  wait.
  *)

  Inductive op := SIGNAL | WAIT.

  (**
  The of these operations can actually be represented by an interpreter function
  [eval] that given an operation and a taskview applies the appropried operation to the given
  taskview.
  *)

  Definition eval (o:op) :=
  match o with
  | SIGNAL => signal
  | WAIT => wait
  end.

  (**
  The operational semantics not only define a closed set of operations that
  can operate on a value (here a taskview), but also the preconditions of each operation.
  Contrary to [eval], relation [Reduces] defines a precondition
  to [wait]: in order to issue a wait, the wait phase must be behind (smaller than)
  the signal phase.
  *)

  Inductive Reduces v : op -> taskview -> Prop :=
    | tv_reduces_signal:
      Reduces v SIGNAL (signal v)
    | tv_reduces_wait:
      wait_phase v < signal_phase v ->
      Reduces v WAIT (wait v).

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

(* begin hide *)
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

End Semantics.
(* end hide *)
