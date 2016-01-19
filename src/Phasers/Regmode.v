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

Section Facts.
  
  (** We now define the facts related to registration modes. *)

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

  Lemma signal_cap_and_wait_cap_to_sw:
    forall r,
    SignalCap r ->
    WaitCap r ->
    r = SIGNAL_WAIT.
  Proof.
    intros.
    destruct H; trivial.
    inversion H0.
  Qed.

  Lemma signal_cap_wait_cap_to_sw:
    forall r,
    WaitCap r ->
    SignalCap r ->
    r = SIGNAL_WAIT.
  Proof.
    intros.
    destruct r; try (inversion H || inversion H0).
    trivial.
  Qed.
End Facts.
