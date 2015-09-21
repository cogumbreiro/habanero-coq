Require Import HJ.Vars.

Module Progress.
Record Progress {S:Type} {O:Type} := mk_progress {
  (** Defines the state of our synchronization mechanism. *)
  state: S;
  (** A map of possible requests issued by some tasks. *)
  reqs: Map_TID.t O;
  (** The given task can invoke the given operation. *)
  Check : tid -> O -> Prop;
  (** The given task issues an operation that yields a new state. *)
  Reduce : tid -> O -> S -> Prop;
  (** Returns [true] when the given operation is blocking, [false] if unblocking. *)
  blocking : O -> bool;
  (** All requests are valid. *)
  reqs_spec:
    forall t o,
    Map_TID.MapsTo t o reqs -> Check t o;
  (** Any valid unblocked operation must be able to reduce. *)
  progress_unblocked:
    forall t o,
    Check t o ->
    blocking o = false ->
    exists s', Reduce t o s';
  (**
    If all our requests are blocking requests, then there is at least
    one that can be issued.
  *)
  progress_blocked:
    (** The [state] must be nonempty. *)
    ~ Map_TID.Empty reqs ->
    (** All available requests are blocking. *)
    (forall t o, Map_TID.MapsTo t o reqs -> blocking o = true) ->
    (** There is a task that can reduce. *)
    exists t o,
    Map_TID.MapsTo t o reqs /\ exists s', Reduce t o s' 
}.

Lemma progress:
  forall {S O:Type} (p:@Progress S O),
  ~ Map_TID.Empty (reqs p) ->
  (** There is a task that can reduce. *)
  exists t o,
  Map_TID.MapsTo t o (reqs p) /\ exists s', (Reduce p) t o s'.
Proof.
  intros.
  destruct (Map_TID_Extra.pred_choice (reqs p) (fun (_:tid) (o:O) => (negb (blocking p o)))).
  - auto with *. (* Proper *)
  - destruct e as (t, (o, (Hmt, Hb))).
    remember (blocking p  o) as b.
    destruct b.
    + inversion Hb.
    + exists t.
      exists o.
      intuition.
      apply (progress_unblocked p); auto.
      apply (reqs_spec p); auto.
  - apply (progress_blocked p); auto.
    intros.
    apply e in H0.
    destruct (blocking p o); auto.
Qed.
End Progress.


Module PhProg.
Require Import HJ.Lang.
Require HJ.Progress.
Module P := HJ.Progress.
Require Import HJ.PhaseDiff.
Require Import HJ.Typesystem.
Lemma pm_prog:
  forall (pm:phasermap) (r:Map_TID.t op),
  (forall t, tid_In t pm -> Map_TID.In t r) ->
  (forall t o, Map_TID.MapsTo t o r -> Check t o pm) ->
  P.Valid pm ->
  @Progress.Progress phasermap op.
Proof.
  intros.
  refine (
    @Progress.mk_progress
      _ _
      pm r
      (fun (t:tid) (o:op) => Check t o pm)
      (Reduce pm)
      P.eq_wait_all
      _ _ _); auto.
  - intros.
    eapply P.progress_simple; auto.
    destruct o; (
      simpl in *;
      intuition;
      inversion H4).
  - intros.
    assert (LEDec.pm_tids pm <> nil). {
    intuition.
    apply Map_TID_Extra.non_empty_eq_in in H2.
    destruct H2 as (k, Hin).
    apply Map_TID_Extra.in_to_mapsto in Hin.
    destruct Hin as (v, Hmt).
    assert (forall t, ~ List.In t (LEDec.pm_tids pm)). {
      intros.
      intuition.
      unfold LEDec.pm_tids in *.
      rewrite H4 in H2.
      inversion H2.
    }
    assert (List.In k (LEDec.pm_tids pm)). {
      assert (Hc : Check k WAIT_ALL pm). {
        assert (Hw : P.eq_wait_all v = true). {
          eauto using H3.
        }
        assert (Heq : v = WAIT_ALL). {
          destruct v; (inversion Hw; trivial).
        }
        subst.
        auto.
      }
      inversion Hc; subst; clear Hc.
      rewrite LEDec.pm_tids_spec.
      unfold tid_In in *.
      assert (Hx := H k).
      destruct H2 as (p, (ph, (?, ?))).
      exists p.
      exists ph.
      intuition.
    }
    contradiction (H4 x).
  }

    (*
    apply Map_TID_Extra.non_empty_eq_in in H2.
    destruct H2 as (k, Hin).
    apply Map_TID_Extra.in_to_mapsto in Hin.
    destruct Hin as (v, Hmt).
    *)
    assert (LEDec.pm_tids pm <> nil). {
      intuition.
      destruct (List.in_dec TID.eq_dec tid (LEDec.pm_tids pm)).
      rewrite <- LEDec.pm_tids_spec in H5.
      unfold LEDec.pm_tids in *.
      
    apply Map_TID_Extra.non_empty_eq_in in H2.
    destruct H2 as (tm, Hmt).
    apply Map_TID_Extra.in_to_mapsto in Hmt.
    destruct Hmt as (o, Hmt).
    assert (P.eq_wait_all o = true). {
      eauto.
    }
      
    
  
    eapply P.has_unblocked.
(simpl in *; try inversion H3; intuition).
  intros.
  assert (LEDec.pm_tids pm <> nil). {
    destruct H2.
    intuition.
    assert (forall t, ~ List.In t (LEDec.pm_tids pm)). {
      intros.
      intuition.
      unfold LEDec.pm_tids in *.
      rewrite H3 in H4.
      inversion H4.
    }
    assert (List.In x (LEDec.pm_tids pm)). {
      rewrite LEDec.pm_tids_spec.
      unfold tid_In in *.
      destruct H2 as (p, (ph, (?, ?))).
      exists p.
      exists ph.
      intuition.
    }
    contradiction (H4 x).
  }
  eauto using P.progress.
Defined.

Check pm_prog.

Module Latch.
(**
  A count-down latch with dynamic registration works exactly like
  a reverse semaphore, it includes has three operations:
  - an operation to register a task that increments the reverse semaphore;
  - an operation to signal, or deregister, a task that decrements the reverse semaphore;
  - an operation to wait that checks if the reverse semaphore is zero.
  The reason the we call it a "reverse" semaphore is because the blocking condition
  is reversed, that is a semaphore blocks while it is zero, whereas a reverse semaphore
  blocks until it becomes zero.

  We represent a latch as a set of tasks to be able to bookkeep registered tasks.
  *)

Record latch := mk_latch {
  value : set_tid
}.

(**
  We create a latch without any registered task.
  *) 

Definition zero := mk_latch Set_TID.empty.

Section Ops.

Variable l:latch.

(**
  Registers a task in the latch. Registered task must
  be eventually signaled or deregistered so that
  synchronization can happen.
  *)

Definition register (t:tid) :=
  mk_latch (Set_TID.add t (value l)).

Definition inc := register.

(**
  Signaling a task revokes its registration,
  so tasks blocked on [wait] will no longer wait for
  the signalling task.
  *)

Definition signal (t:tid) :=
  mk_latch (Set_TID.remove t (value l)).

Definition deregister := signal.
Definition dec := signal.

(**
  The [wait] operation should block until there are
  no registered tasks.
  *)

Definition Wait :=
  Set_TID.Empty (value l).

(**
  Asserts that task [t] is registerd in latch [l].
  *)

Definition Registered (t:tid) :=
  Set_TID.In t (value l).

End Ops.
End Latch.

Module LatchSem.
Import Latch.

(** How do we represent that synchronization works? *)

Inductive op :=
  | REG : tid -> op
  | SIG : tid -> op
  | WAIT : op.

Inductive Redex (l:latch) (t:tid) : op -> latch -> Prop  :=
  | redex_reg:
    forall t',
    ~ Registered l t' ->
    Redex l t (REG t') (register l t')

  | redex_sig:
    forall t',
    Registered l t' ->
    Redex l t (SIG t') (signal l t')

  | redex_wait:
    Wait l ->
    Redex l t WAIT l.

End LatchSem.

Module LatchProps.

Import Latch.
Import LatchSem.

Inductive Check (l:latch) (t:tid) : op -> Prop :=
  | check_reg:
    forall t',
    ~ Registered l t' ->
    Check l t (REG t')
  | check_sig:
    forall t',
    Registered l t' ->
    Check l t (SIG t')
  | check_wait:
    ~ Registered l t ->
    Check l t WAIT.

Section Progress.
(**
  Progress means that either the latch is a value, or there
  is at least an operation that can be issued.
  But how can we enumerate the available operations?

  At any time a task may be registered, which means that there is always  
  *)

Variable l: latch.

(**
  The first thing to show is that there is progress for
  unblocked tasks. We define a unblocking predicate that yields [true]
  when the operation is unblocking.
*)

Definition unblocking (o:op) :=
  match o with
  | REG _ => true
  | SIG _ => true
  | WAIT => false
  end.

(**
  The proof for this lemma is trivial, by inversion of proposition [Check].
  *)

Lemma progress_unblocked:
  forall t o,
  unblocking o = true ->
  Check l t o ->
  exists l',
  LatchSem.Redex l t o l'.
Proof.
  intros.
  destruct o.
  - inversion H0.
    subst.
    eauto using redex_reg.
  - inversion H0.
    subst.
    eauto using redex_sig.
  - inversion H.
Qed.

Lemma l_prog:
  forall (l:latch) (r:Map_TID.t op),
  (forall t, Registered l t -> Map_TID.In t r) ->
  (forall t o, Map_TID.MapsTo t o r -> Check l t o) ->
  Progress.Progress latch op.
Proof.
  intros.
  
Qed.

Lemma latch_prog:
  forall (l:latch) (r:Map_TID.t op),
  (forall t, Registered l t -> Map_TID.In t r) ->
  (forall t o, Map_TID.MapsTo t o r -> Check l t o) ->
  
   => Progress.mk_progress latch op l r
  (Registered l)
  (Check l) (Redex l).

End Progress.

End LatchProps.

Require Import HJ.Lang.

Module Finish.

(**
  We now want to define a finish state that encompasses
  a latch that represents the finish instruction and a
  phaser map that is available inside the finish scope.
  *)

Record state := mk_state {
  get_latch: Latch.latch;
  get_phasers: phasermap;
  get_owner: tid
}.

(**
  We define two obvious mutators.
  *)

Definition set_latch (s:state) (l:Latch.latch) :=
  mk_state l (get_phasers s) (get_owner s).

Definition set_phasers (s:state) (m:phasermap) :=
  mk_state (get_latch s) m (get_owner s). 

Definition set_owner (s:state) (t:tid) :=
  mk_state (get_latch s) (get_phasers s) t.

(**
  We also define a new language of operations. Most are
  phasermap-operations, with two exceptions: [BEGIN_ASYNC] and
  [END_ASYNC]. The former represents an [Lang.ASYNC] and at the same 
  a [LatchSem.REG]. The latter represents a [LatchSem.SIG].
  *)

Inductive op : Type :=
  | PH_NEW : phid -> op
  | PH_SIGNAL : phid -> op
  | PH_DROP : phid -> op
  | SIGNAL_ALL : op
  | WAIT_ALL : op
  | BEGIN_ASYNC : list phased -> tid -> op
  | END_ASYNC : tid -> op.

(**
  We define a translation from [op] to [Lang.op]. The function returns
  [None] when undefined.
  *)

Definition as_pm_op(o:op) : option Lang.op :=
  match o with
  | PH_NEW p => Some (Lang.PH_NEW p)
  | PH_SIGNAL p => Some (Lang.PH_SIGNAL p)
  | PH_DROP p => Some (Lang.PH_SIGNAL p)
  | SIGNAL_ALL => Some Lang.SIGNAL_ALL
  | WAIT_ALL => Some Lang.WAIT_ALL
  | BEGIN_ASYNC l t => Some (Lang.ASYNC l t)
  | END_ASYNC _ => None
  end.  

(**
  Definition [PmReduce] abbreviates the translation of [op] and a call to [Lang.Reduce].
 *)

Definition PmReduce (s:state) (t:tid) (o:op) (m:phasermap) :=
  exists pm_op, as_pm_op o = Some pm_op /\ Lang.Reduce (get_phasers s) t pm_op m.

(**
  Function [as_latch_op] translates an [op] into a [LatchSem.op] and returns
  [None] when it is undefined.
  *)

Definition as_latch_op(o:op) : option LatchSem.op :=
  match o with
  | PH_NEW p => None
  | PH_SIGNAL p => None
  | PH_DROP p => None
  | SIGNAL_ALL => None
  | WAIT_ALL => None
  | BEGIN_ASYNC _ t => Some (LatchSem.REG t)
  | END_ASYNC t => Some (LatchSem.SIG t)
  end.

(**
  Similarly to [PmReduce], definition [LatchReduce] translates operation [op]
  into [LatchSem.op] and invokes [LatchSem.Redex].
  *)

Definition LatchReduce (s:state) (t:tid) (o:op) (l:Latch.latch) :=
  exists l_op, as_latch_op o = Some l_op /\ LatchSem.Redex (get_latch s) t l_op l.

(**
  Finally, we define the reduction.
  *)

Inductive Redex (s:state) (t:tid) : op -> state -> Prop  :=
  | redex_ph_new:
    forall p m,
    PmReduce s t (PH_NEW p) m ->
    Redex s t (PH_NEW p) (set_phasers s m)

  | redex_ph_signal:
    forall p m,
    PmReduce s t (PH_SIGNAL p) m ->
    Redex s t (PH_SIGNAL p) (set_phasers s m)

  | redex_ph_drop:
    forall p m,
    PmReduce s t (PH_DROP p) m ->
    Redex s t (PH_DROP p) (set_phasers s m)

  | redex_ph_signal_all:
    forall m,
    PmReduce s t SIGNAL_ALL m ->
    Redex s t SIGNAL_ALL (set_phasers s m)

  | redex_ph_wait_all:
    forall m,
    PmReduce s t WAIT_ALL m ->
    Redex s t WAIT_ALL (set_phasers s m)

  | redex_begin_async:
    forall p t' l m,
    LatchReduce s t (BEGIN_ASYNC p t') l ->
    PmReduce s t (BEGIN_ASYNC p t') m ->
    Redex s t (BEGIN_ASYNC p t') (mk_state l m (get_owner s))

 | redex_end_async:
   forall l,
   LatchReduce s t (END_ASYNC t) l ->
   Redex s t (END_ASYNC t) (set_latch s l).


