
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
    r_le m SIGNAL_WAIT.

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

Hint Constructors WaitCap.

Inductive SignalCap : regmode -> Prop :=
  | signal_cap_sw:
    SignalCap SIGNAL_WAIT
  | signal_cap_so:
    SignalCap SIGNAL_ONLY.

Hint Constructors SignalCap.

Module Notations.
  Infix "<=" := (r_le) : reg_scope.
End Notations.

Section Facts.
  Import Notations.
  Open Scope reg_scope.

  Lemma regmode_eq_dec:
    forall (m1 m2:regmode),
    { m1 = m2 } + { m1 <> m2 }.
  Proof.
    intros.
    destruct m1, m2; solve [ left; auto | right; intuition; inversion H]. 
  Qed.
  
  Lemma set_mode_ident:
    forall v,
    set_mode v (mode v) = v.
  Proof.
    intros; destruct v; trivial.
  Qed.

  Lemma set_mode_preserves_signal_phase:
    forall v r,
    signal_phase (set_mode v r) =  signal_phase v.
  Proof.
    intros.
    destruct v; auto.
  Qed.

  Lemma set_mode_preserves_wait_phase:
    forall v r,
    wait_phase (set_mode v r) =  wait_phase v.
  Proof.
    intros.
    destruct v; auto.
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
  Inductive op := | SIGNAL | WAIT.

  Definition eval (o:op) :=
  match o with
  | SIGNAL => signal
  | WAIT => wait
  end.

  Inductive Reduce (v:taskview) : op -> taskview -> Prop :=
    | reduce_signal:
      Reduce v SIGNAL (signal v)
    | reduce_wait:
      wait_phase v < signal_phase v ->
      Reduce v WAIT (wait v).

  Lemma reduce_spec:
    forall v o v',
    Reduce v o v' ->
    v' = eval o v.
  Proof.
    intros.
    inversion H; subst; simpl; trivial.
  Qed.

  Lemma reduce_rw_signal:
    forall v v',
    Reduce v SIGNAL v' ->
    v' = signal v.
  Proof.
    intros.
    inversion H.
    trivial.
  Qed.

  Lemma reduce_rw_wait:
    forall v v',
    Reduce v WAIT v' ->
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

  Lemma reduce_preserves_mode:
    forall v o v',
    Reduce v o v' ->
    mode v' = mode v.
  Proof.
    intros.
    apply reduce_spec in H.
    subst.
    auto using eval_preserves_mode.
  Qed.

End Semantics.
