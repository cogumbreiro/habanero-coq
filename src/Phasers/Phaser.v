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
  The following record defines the specification of a phaser operation.
  An operation is issued by a task of type [tid] and targets a [phaser].
  The pre condition [can_run] must be satisfied to execute the implementation [run] on
  a given phaser.
  *)


Record Op := mk_op {
  can_run: phaser -> Prop;
  run: phaser -> phaser
}.

(**
  Function [make] creates a new phaser and registers task [t] with it.
  Task [t] becomes registered with the initial taskview [Taskview.make].
*)

Definition make t := add t Taskview.make (Map_TID.empty taskview).

(** * Signal *)

(**
  Function [update] targets a phaser [ph] and is used internally to mutate
  the taskview associated with task [t] using function [f] to mutate.
  If task [t] is not registered in [ph], then the phaser is left unchanged.
*)

Definition update (t:tid) (f:taskview -> taskview) (ph:phaser) : phaser :=
  match find t ph with
  | Some v => add t (f v) ph
  | None => ph
  end.

(** For the signal to take any effect the task must be registered with the phaser. *)

Inductive SignalPre (t:tid) (ph:phaser) : Prop :=
  signal_pre:
    Map_TID.In t ph ->
    SignalPre t ph.

(**
  Signal just applies [Taskview.signal] to the taskview associated with
  task [t].
  *)

Definition signal (t:tid) : phaser -> phaser := update t Taskview.signal.

(**
  We now pair the pre condition with the implementation. This is later used
  in the definition of the operational semantics.
  *)

Definition signal_op t := mk_op (SignalPre t) (signal t).

(** * Wait *)

(**
  Predicate [Await] holds when all tasks registered in phaser [ph] 
  with a signal capability have a signal phase of at least [n].
  By only awaiting tasks with a signal capability, predicate [Await]
  _disregards_ any task registered with a [WAIT_ONLY] mode, regardless
  of its signal phase.
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
  Wait consists of thee pre-conditions: (i) task [t] is registered in phaser [ph],
  (ii) task [t] has signalled as per [Taskview.WaitPre],
  and (iii) task [t] must be able to synchronize with the other members through phaser [ph].
  *)

Inductive WaitPre t ph : Prop  := 
  wait_pre:
    forall v,
    Map_TID.MapsTo t v ph ->
    Taskview.WaitPre v ->
    Sync ph t ->
    WaitPre t ph.

(** Operationally, wait applies [Taskview.wait] on the taskview associated with task [t].*)

Definition wait (t:tid) : phaser -> phaser := update t Taskview.wait.

Definition wait_op t := mk_op (WaitPre t) (wait t).


(** * Drop *)

(**
  Function [drop] removes the taskview associated with the given task.
  The pre-condition to issue a [drop] is that task [t] must be registered
  in phaser [ph].
  *)

Inductive DropPre t (ph:phaser) : Prop :=
  drop_pre:
    Map_TID.In t ph ->
    DropPre t ph.

Definition drop : tid -> phaser -> phaser := @remove taskview.

Definition drop_op t := mk_op (DropPre t) (drop t).

(** * Register *)

(**
  Function [register] embodies the invocation of an async phased, and
  it requires the task being registered and the registration mode of the task.
  *)

Record registry := mk_registry {
  get_task: tid;
  get_mode: regmode
}.

(**
  Register has two pre-conditions: (i) task [get_task r] must be
  unknown to phaser [ph], and (ii) the mode in registry [r] cannot escalate the
  capabilities of the issuer.
*)

Import Regmode.Notations.
Open Scope reg_scope.

Inductive RegisterPre r t ph : Prop :=
  register_pre:
    forall v,
    ~ Map_TID.In (get_task r) ph ->
    Map_TID.MapsTo t v ph ->
    get_mode r <= mode v ->
    RegisterPre r t ph.

(**
  Operationally, register adds task [get_task r]  to the phaser, assigning new taskview
  that is a copy of the issuer's taskview with the mode set to [get_mode r].
  *)

Definition register (r:registry) (t:tid) (ph:phaser) : phaser := 
  match find t ph with
  | Some v => add (get_task r) (set_mode v (get_mode r)) ph
  | None => ph
  end.

Definition register_op r t := mk_op (RegisterPre r t) (register r t).

(** * Operational semantics *)
(* begin hide *)
End Defs.
(* end hide *)

(** The operational semantics defines a closed set of the possible operations:
  signal, wait, drop (that deregisters the issuer),
  and register (that adds a new task to the phaser). *)

Inductive op := SIGNAL | WAIT | DROP | REGISTER : registry -> op.

(** Function [eval] interprets operation [o] as its operation specification [Op]. *)

Definition get_impl o :=
match o with
| SIGNAL => signal_op
| WAIT => wait_op
| DROP => drop_op
| REGISTER r => register_op r
end.

(**
  Relation [Reduces] defines the operational semantics.
*)

Inductive Reduces ph t o : phaser -> Prop :=
  ph_reduces:
    can_run (get_impl o t) ph ->
    Reduces ph t o (run (get_impl o t) ph).

(** Relation [SReducess] simply omits the task and operation of relation [Reduces]. *)

Inductive SReduces (ph1:phaser) (ph2:phaser) : Prop :=
  ph_s_reduces:
    forall t o,
    Reduces ph1 t o ph2 ->
    SReduces ph1 ph2.

(** Finally, we declare a function that converts a [Phaser.op] to a [Taskview.op]. *)

Definition as_tv_op (o:op) :=
match o with
| SIGNAL => Some Taskview.SIGNAL
| WAIT =>  Some Taskview.WAIT
| _ => None
end.

  (* begin hide *)
Section Facts.

  Lemma as_tv_op_inv_signal:
    forall o,
    as_tv_op o = Some Taskview.SIGNAL ->
    o = SIGNAL.
  Proof.
    intros.
    destruct o; auto; simpl in *; try (inversion H).
  Qed.

  Lemma as_tv_op_inv_wait:
    forall o,
    as_tv_op o = Some Taskview.WAIT ->
    o = WAIT.
  Proof.
    intros.
    destruct o; auto; simpl in *; try (inversion H).
  Qed.

  Lemma ph_reduces_spec:
    forall ph t o ph',
    Reduces ph t o ph' ->
    ph' = run (get_impl o t) ph.
  Proof.
    intros.
    destruct o;
    simpl; inversion H; auto.
  Qed.

  Lemma ph_update_rw:
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

  Lemma ph_signal_rw:
    forall t v ph,
    Map_TID.MapsTo t v ph ->
    signal t ph = Map_TID.add t (Taskview.signal v) ph.
  Proof.
    intros.
    eauto using ph_update_rw.
  Qed.

  Lemma ph_wait_rw:
    forall t v ph,
    Map_TID.MapsTo t v ph ->
    wait t ph = Map_TID.add t (Taskview.wait v) ph.
  Proof.
    intros.
    eauto using ph_update_rw.
  Qed.

  Lemma ph_drop_rw:
    forall t ph,
    drop t ph = Map_TID.remove t ph.
  Proof.
    unfold drop; auto.
  Qed.

  Lemma ph_register_rw:
    forall t v r ph,
    Map_TID.MapsTo t v ph ->
    register r t ph = Map_TID.add (get_task r) (set_mode v (get_mode r)) ph.
  Proof.
    intros.
    unfold register in *.
    remember (Map_TID.find _ _ ).
    symmetry in Heqo.
    destruct o as [v'|].
    - rewrite Map_TID_Facts.find_mapsto_iff in *.
      assert (v' = v). {
        rewrite H in *.
        inversion Heqo.
        trivial.
      }
      subst.
      trivial.
    - apply Map_TID_Facts.not_find_in_iff in Heqo.
      contradiction Heqo.
      eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Lemma ph_in:
    forall ph t o ph',
    Reduces ph t o ph' ->
    Map_TID.In t ph.
  Proof.
    intros.
    inversion H.
    destruct o;
    simpl in *; inversion H0; eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Lemma drop_mapsto:
    forall t v ph t',
    Map_TID.MapsTo t v (drop t' ph) ->
    t' <> t /\ Map_TID.MapsTo t v ph.
  Proof.
    intros.
    unfold drop in *.
    rewrite Map_TID_Facts.remove_mapsto_iff in H.
    assumption.
  Qed.

  (* end hide *)

  (**
    The importance of function [as_tv_op] is captured by the following two properties.
    If the phaser operation is convertible to a taskview operation, then
    then resulting taskview update is [Taskview.Semantics.eval o' v].
  *)

  Lemma ph_to_tv_correct:
    forall ph t o o' ph' v,
    Reduces ph t o ph' ->
    as_tv_op o = Some o' ->
    Map_TID.MapsTo t v ph ->
    ph' = Map_TID.add t (Taskview.eval o' v) ph.
  Proof.
    intros.
    destruct o'; simpl.
    - apply as_tv_op_inv_signal in H0; subst.
      destruct H. simpl in *.
      auto using ph_signal_rw.
    - apply as_tv_op_inv_wait in H0; subst.
      destruct H. simpl in *.
      auto using ph_wait_rw.
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
    Taskview.Reduces v o' (Taskview.eval o' v).
  Proof.
    intros.
    destruct o'; simpl.
    - apply as_tv_op_inv_signal in H0; subst.
      apply tv_reduces_signal.
    - apply as_tv_op_inv_wait in H0; subst.
      inversion H.
      subst; simpl in *.
      apply tv_reduces_wait.
      inversion H0.
      assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun.
      subst.
      intuition.
  Qed.
(* begin hide *)
End Facts.
(* end hide *)
