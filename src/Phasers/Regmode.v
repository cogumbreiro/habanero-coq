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

  Definition union r1 r2 :=
  match r1, r2 with
  | WAIT_ONLY, WAIT_ONLY => WAIT_ONLY
  | SIGNAL_ONLY, SIGNAL_ONLY => SIGNAL_ONLY
  | _, _ => SIGNAL_WAIT
  end.

Module Notations.
  Infix "<=" := (r_le) : reg_scope.
End Notations.

(**
  Two important notions used throught the formalization are wait-/signal-capabilities.
*)

Inductive CanWait : regmode -> Prop :=
  | can_wait_sw:
    CanWait SIGNAL_WAIT
  | can_wait_wo:
    CanWait WAIT_ONLY.

Hint Constructors CanWait.

Inductive CanSignal : regmode -> Prop :=
  | can_signal_sw:
    CanSignal SIGNAL_WAIT
  | can_signal_so:
    CanSignal SIGNAL_ONLY.

Hint Constructors CanSignal.

Section Facts.
  
  (** We now define the facts related to registration modes. *)

  Import Notations.
  Open Scope reg_scope.

  (** The equality of registration mode is decidable. *)

  Lemma regmode_eq:
    forall (m1 m2:regmode),
    { m1 = m2 } + { m1 <> m2 }.
  Proof.
    intros.
    destruct m1, m2; solve [ left; auto | right; intuition; inversion H]. 
  Defined.

  (** Checking for the wait capability is a decidable property. *)

  Lemma can_wait:
    forall r,
    { CanWait r } + { ~ CanWait r }.
  Proof.
    intros.
    destruct r; auto.
    right; intuition; inversion H.
  Defined.

  Lemma neq_so_to_can_wait:
    forall r,
    r <> SIGNAL_ONLY ->
    CanWait r.
  Proof.
    intros.
    destruct r; auto.
    contradiction H; trivial.
  Qed.

  Lemma can_wait_to_neq_so:
    forall r,
    CanWait r ->
    r <> SIGNAL_ONLY.
  Proof.
    intros.
    inversion H;
      subst;
      intuition;
      inversion H0.
  Qed.

  Lemma can_wait_rw:
    forall r,
    CanWait r <-> r <> SIGNAL_ONLY.
  Proof.
    intros.
    split; auto using can_wait_to_neq_so, neq_so_to_can_wait.
  Qed.

  Lemma not_can_wait_to_so:
    forall r,
    ~ CanWait r ->
    r = SIGNAL_ONLY.
  Proof.
    intros.
    destruct r;
    intuition;
    contradiction H;
    auto.
  Qed.

  Lemma so_to_not_can_wait:
    forall r,
    r = SIGNAL_ONLY ->
    ~ CanWait r.
  Proof.
    intros.
    intuition.
    inversion H0;
    rewrite <- H1 in *;
    inversion H.
  Qed.

  Lemma can_wait_so:
    forall r,
    { CanWait r } + { r = SIGNAL_ONLY }.
  Proof.
    intros.
    destruct (can_wait r);
    auto using not_can_wait_to_so.
  Defined.

  Lemma can_signal:
    forall r,
    { CanSignal r } + { ~ CanSignal r }.
  Proof.
    intros.
    destruct r; auto.
    right; intuition; inversion H.
  Defined.

  Lemma neq_wo_to_can_signal:
    forall r,
    r <> WAIT_ONLY ->
    CanSignal r.
  Proof.
    destruct r; intuition.
  Qed.

  Lemma can_signal_to_neq_wo:
    forall r,
    CanSignal r ->
    r <> WAIT_ONLY.
  Proof.
    intros.
    inversion H;
      subst;
      intuition;
      inversion H0.
  Qed.

  Lemma can_signal_rw:
    forall r,
    CanSignal r <-> r <> WAIT_ONLY.
  Proof.
    intros.
    split; auto using can_signal_to_neq_wo, neq_wo_to_can_signal.
  Qed.

  Lemma not_can_signal_to_wo:
    forall r,
    ~ CanSignal r ->
    r = WAIT_ONLY.
  Proof.
    intros.
    destruct r;
    intuition;
    contradiction H;
    auto.
  Qed.

  Lemma can_signal_wo:
    forall r,
    { CanSignal r } + { r = WAIT_ONLY }.
  Proof.
    intros.
    destruct (can_signal r);
    auto using not_can_signal_to_wo.
  Defined.

  Lemma can_signal_and_can_wait_to_sw:
    forall r,
    CanSignal r ->
    CanWait r ->
    r = SIGNAL_WAIT.
  Proof.
    intros.
    destruct H; trivial.
    inversion H0.
  Qed.

  Lemma can_signal_can_wait_to_sw:
    forall r,
    CanWait r ->
    CanSignal r ->
    r = SIGNAL_WAIT.
  Proof.
    intros.
    destruct r; try (inversion H || inversion H0).
    trivial.
  Qed.

  Definition le_dec x y:
    { x <= y } + { ~ x <= y }.
  Proof.
    destruct x, y;
    auto using r_le_so, r_le_sw, r_le_wo;
    right; unfold not; intros N;
    inversion N.
  Defined.

  Lemma can_wait_le:
    forall x y,
    CanWait y ->
    y <= x ->
    CanWait x.
  Proof.
    intros.
    inversion H0; subst; auto using can_wait_sw, can_wait_wo.
  Qed.

  Lemma can_signal_le:
    forall x y,
    CanSignal y ->
    y <= x ->
    CanSignal x.
  Proof.
    intros.
    inversion H0; subst; auto using can_signal_sw, can_signal_wo.
  Qed.
End Facts.
