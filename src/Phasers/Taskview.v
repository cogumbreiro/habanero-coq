
Inductive regmode : Set:=
  | SIGNAL_ONLY : regmode
  | WAIT_ONLY : regmode
  | SIGNAL_WAIT : regmode.

(** Defines a <= relation between registration modes. *)

Inductive r_le : regmode -> regmode -> Prop :=
  | r_le_so:
    r_le SIGNAL_ONLY SIGNAL_ONLY
  | r_le_wo:
    r_le WAIT_ONLY WAIT_ONLY
  | r_le_sw:
    forall m,
    r_le m SIGNAL_WAIT
where "n <= m" := (r_le n m) : reg_scope.

Open Scope reg_scope.

Record taskview := TV {
  signal_phase: nat;
  wait_phase: nat;
  mode: regmode
}.

Definition make := TV 0 0 SIGNAL_WAIT.

(** Standard mutators. *)

Definition set_mode (v:taskview) (m:regmode) := TV v.(signal_phase) v.(wait_phase) m.
Definition set_signal_phase (v:taskview) (n:nat) := TV n (wait_phase v) (mode v).
Definition set_wait_phase (v:taskview) (n:nat) := TV (signal_phase v) n (mode v).

(** Signal operation on taskviews. *)

Definition signal (v:taskview) :=
match v.(mode) with
| SIGNAL_ONLY => set_signal_phase v (S (signal_phase v))
| _ => set_signal_phase v (S (wait_phase v))
end.

(** Wait operation on taskviews. *)

Definition wait (v:taskview) := set_wait_phase v (S (wait_phase v)).

Inductive WaitCap : regmode -> Prop :=
  | wait_cap_sw:
    WaitCap SIGNAL_WAIT
  | wait_cap_wo:
    WaitCap WAIT_ONLY.

Hint Resolve wait_cap_sw wait_cap_wo.

Inductive SignalCap : regmode -> Prop :=
  | signal_cap_sw:
    SignalCap SIGNAL_WAIT
  | signal_cap_so:
    SignalCap SIGNAL_ONLY.

Hint Resolve signal_cap_so signal_cap_sw.

Module Semantics.
  Inductive op := | SIGNAL | WAIT.
  Inductive Reduction (v:taskview) : op -> taskview -> Prop :=
    | reduction_signal:
      Reduction v SIGNAL (signal v)
    | reduction_wait_wait_cap:
      wait_phase v < signal_phase v -> 
      Reduction v WAIT (wait v).
End Semantics.

Section Facts.

  Lemma regmode_eq_dec:
    forall (m1 m2:regmode),
    { m1 = m2 } + { m1 <> m2 }.
  Proof.
    intros.
    destruct m1, m2; solve [ left; auto | right; intuition; inversion H]. 
  Qed.

  Lemma make_mode:
    mode make = SIGNAL_WAIT.
  Proof.
    unfold make.
    auto.
  Qed.

  Lemma make_signal_phase:
    signal_phase make = 0.
  Proof.
    unfold make.
    auto.
  Qed.

  Lemma make_wait_phase:
    wait_phase make = 0.
  Proof.
    unfold make.
    auto.
  Qed.

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

End Facts.