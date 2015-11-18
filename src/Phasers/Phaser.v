(* begin hide *)

Require Import HJ.Vars.
Require Import HJ.Phasers.Regmode.
Require Import HJ.Phasers.Taskview.

Section Defs.
Import HJ.Vars.Map_TID.

(* end hide *)

(**
  A phaser is a map from task names [tid] into taskviews, represented
  by parametric type [Map_TID.t].
*)

Definition phaser := Map_TID.t taskview.

(**
  Predicate [Await] holds when all tasks registered in phaser [ph] 
  that have a signal capability have a signal phase of at least [n].
  By only awaiting tasks with a signal capability, predicate [Await]
  does *not* wait for any task registered with [WAIT_ONLY] mode, regardless
  of its signal phase. Intuitively, this predicate lets a task to wait for
  all members of a phaser to reach a given phase.
  *)

Inductive Await ph n : Prop :=
  await_def:
    (forall t v,
      MapsTo t v ph ->
      SignalCap (mode v) ->
      signal_phase v >= n) ->
    Await ph n.

(**
  Predicate [Sync] defines what happens when a
  task synchronizes with the other members of a phaser, which is triggered when
  a task performs either wait on a phaser, or next.
  The semantics of [Sync] depends on the registration mode of the task.
  Tasks registered in [SIGNAL_ONLY] mode do not block, so predicate [Sync] always
  holds. Tasks that are not registered in [SIGNAL_ONLY] mode
  (that is tasks with a wait capability) only holds once all 
  members with a signal capability issued at least as many signals as the task
  synchronizing.
  *)

Inductive Sync : phaser -> tid -> Prop :=
  | sync_so:
    forall t v ph,
    MapsTo t v ph ->
    mode v = SIGNAL_ONLY ->
    Sync ph t
  | sync_wait:
    forall ph t v,
    MapsTo t v ph ->
    WaitCap (mode v) ->
    Await ph (signal_phase v) ->
    Sync ph t.

(**
  Function [make] creates a new phaser and registers task [t] with it.
  Task [t] becomes registered with the initial taskview [Taskview.make].
*)

Definition make t := add t Taskview.make (Map_TID.empty taskview).

(**
  Function [update] targets a phaser [ph and is used internal to mutate
  the taskview associated with the given task [t] with function [f].
  If task [t] is not registered in [ph], then the phaser is left unhaltered.
*)

Definition update (t:tid) (f:taskview -> taskview) (ph:phaser) : phaser :=
  match find t ph with
  | Some v => add t (f v) ph
  | None => ph
  end.

(**
  Signal and wait use [update] to apply either [Taskview.signal] or
  [Taskview.wait] to the registered taskview.
  *)

Definition signal (t:tid) : phaser -> phaser := update t Taskview.signal.

Definition wait (t:tid) : phaser -> phaser := update t Taskview.wait.

(** Function [drop] removes the taskview associated with the given task. *)

Definition drop : tid -> phaser -> phaser := @remove taskview.

(**
  Function [register] embodies invoking an [async phased].
  Operationally, this operation puts a new taskview in the phaser, associated to
  task [get_task r].
  The new taskview is a copy of the issuer's taskview, whose mode is set to [get_mode r].
  *)

Record registry := mk_registry {
  get_task: tid;
  get_mode: regmode
}.

Definition register (t:tid) (r:registry) (ph:phaser) : phaser := 
  match find t ph with
  | Some v => add (get_task r) (set_mode v (get_mode r)) ph
  | None => ph
  end.

(* begin hide *)

End Defs.

Module Semantics.

  Import Regmode.Notations.
  Open Scope reg_scope.
(* end hide *)

(** * Small-step Operational Semantics *)

(** The operational semantics define a set of four possible operations: signal, wait, drop (that deregisters the issuer),
and register (that adds a new task to the phaser). *)

  Inductive op := SIGNAL | WAIT | DROP | REGISTER : registry -> op.

  (**
    Relation [Reduces] defines the operational semantics. Two operations are worth detailing.
    Operation [WAIT] has two pre-conditions: (i) the issuer must have signalled previously,
    and (ii) the issuer must synchronize by means of the given phaser with [Sync t ph].
    Operation [REGISTER r] has two pre-conditions: (i) task [get_task r] must be unknown to the phaser,
    and (ii) the mode in the registry can only pass capabilities that the issuer already has.
  *)

  Inductive Reduces (ph:phaser) (t:tid) : op -> phaser -> Prop :=
  | reduces_signal:
    Map_TID.In t ph ->
    Reduces ph t SIGNAL (signal t ph)
  | reduces_wait:
    forall v,
    Map_TID.MapsTo t v ph ->
    wait_phase v < signal_phase v ->
    Sync ph t ->
    Reduces ph t WAIT (wait t ph)
  | reduces_drop:
    Map_TID.In t ph ->
    Reduces ph t DROP (drop t ph)
  | reduces_register:
    forall v r,
    ~ Map_TID.In (get_task r) ph ->
    Map_TID.MapsTo t v ph ->
    get_mode r <= mode v ->
    Reduces ph t (REGISTER r) (register t r ph).

  (** Relation [SReducess] simply omits the task and operation of relation [Reduces]. *)

  Inductive SReduces (ph1:phaser) (ph2:phaser) : Prop :=
    s_reduces:
      forall t o,
      Reduces ph1 t o ph2 ->
      SReduces ph1 ph2.

  (** Finally, we declare a function that converts a [Phaser.op] to a [Taskview.op]. *)

  Definition as_tv_op (o:op) :=
  match o with
  | SIGNAL => Some Taskview.Semantics.SIGNAL
  | WAIT =>  Some Taskview.Semantics.WAIT
  | _ => None
  end.
  
  (* begin hide *)

  Lemma as_tv_op_inv_signal:
    forall o,
    as_tv_op o = Some Taskview.Semantics.SIGNAL ->
    o = SIGNAL.
  Proof.
    intros.
    destruct o; auto; simpl in *; try (inversion H).
  Qed.

  Lemma as_tv_op_inv_wait:
    forall o,
    as_tv_op o = Some Taskview.Semantics.WAIT ->
    o = WAIT.
  Proof.
    intros.
    destruct o; auto; simpl in *; try (inversion H).
  Qed.

  Lemma ph_update_spec:
    forall t v f ph,
    Map_TID.MapsTo t v ph ->
    update t f ph = Map_TID.add t (f v) ph.
  Proof.
    intros.
    unfold update.
      remember (Map_TID.find _ _).
      symmetry in Heqo.
      destruct o as [v'|].
      {
        apply Map_TID_Facts.find_mapsto_iff in Heqo.
        assert (v' = v) by eauto using Map_TID_Facts.MapsTo_fun.
        subst; clear Heqo.
        trivial.
      }
      apply Map_TID_Facts.not_find_in_iff in Heqo.
      contradiction Heqo.
      eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Lemma ph_signal_spec:
    forall t v ph ph',
    Map_TID.MapsTo t v ph ->
    Reduces ph t SIGNAL ph' ->
    ph' = Map_TID.add t (Taskview.signal v) ph.
  Proof.
    intros.
    inversion H0.
    subst.
    unfold signal.
    auto using ph_update_spec.
  Qed.

  Lemma ph_wait_spec:
    forall t v ph ph',
    Map_TID.MapsTo t v ph ->
    Reduces ph t WAIT ph' ->
    ph' = Map_TID.add t (Taskview.wait v) ph.
  Proof.
    intros.
    inversion H0.
    subst.
    unfold wait.
    auto using ph_update_spec.
  Qed.

  Lemma ph_drop_spec:
    forall t ph ph',
    Map_TID.In t ph ->
    Reduces ph t DROP ph' ->
    ph' = Map_TID.remove t ph.
  Proof.
    intros.
    inversion H0; subst.
    unfold drop; auto.
  Qed.

  Lemma ph_register_spec:
    forall t v r ph ph',
    Map_TID.MapsTo t v ph ->
    Reduces ph t (REGISTER r) ph' ->
    ph' = Map_TID.add (get_task r) (set_mode v (get_mode r)) ph.
  Proof.
    intros.
    inversion H0; subst.
    unfold register in *.
    remember (Map_TID.find _ _ ).
    symmetry in Heqo.
    destruct o.
    - rewrite Map_TID_Facts.find_mapsto_iff in *.
      assert (v0 = v). {
        rewrite H in *.
        inversion H3; auto.
      }
      assert (t0 = v). {
        rewrite H in *.
        inversion Heqo; auto.
      }
      subst.
      trivial.
    - apply Map_TID_Extra.mapsto_to_in in H3.
      apply Map_TID_Facts.not_find_in_iff in Heqo.
      contradiction.
  Qed.

  Lemma ph_in:
    forall ph t o ph',
    Reduces ph t o ph' ->
    Map_TID.In t ph.
  Proof.
    intros.
    inversion H; eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  (* end hide *)

  (**
    The importance of function [as_tv_op] is captured by the following two properties.
    If the phaser operation is convertible to a taskview operation, then
    the resulting phaser the result of updating the taskview of tasks [t]
    with [Semantics.eval o' v].
  *)

  Lemma ph_to_tv_correct:
    forall ph t o o' ph' v,
    Reduces ph t o ph' ->
    as_tv_op o = Some o' ->
    Map_TID.MapsTo t v ph ->
    ph' = Map_TID.add t (Semantics.eval o' v) ph.
  Proof.
    intros.
    destruct o'; simpl.
    - apply as_tv_op_inv_signal in H0; subst.
      auto using ph_signal_spec.
    - apply as_tv_op_inv_wait in H0; subst.
      auto using ph_wait_spec.
  Qed.
  
  (**
    The second property states that if the phaser-operation is convertible to
    a taskview-operation, then the taskview reduces with the resulting operation.
  *)

  Lemma ph_reduces_to_tv_reduce:
    forall ph t o o' ph' v,
    Reduces ph t o ph' ->
    as_tv_op o = Some o' ->
    Map_TID.MapsTo t v ph ->
    Taskview.Semantics.Reduces v o' (Semantics.eval o' v).
  Proof.
    intros.
    destruct o'; simpl.
    - apply as_tv_op_inv_signal in H0; subst.
      apply Semantics.tv_reduces_signal.
    - apply as_tv_op_inv_wait in H0; subst.
      inversion H.
      subst.
      apply Semantics.tv_reduces_wait.
      assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun.
      subst.
      intuition.
  Qed.
(* begin hide *)
End Semantics.
(* end hide *)
