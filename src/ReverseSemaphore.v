Require Import HJ.Vars.
Set Arguments Implicit.


(**
  A count-down rsem with dynamic registration works exactly like
  a reverse semaphore, it includes has three operations:
  - an operation to register a task that increments the reverse semaphore;
  - an operation to signal, or deregister, a task that decrements the reverse semaphore;
  - an operation to wait that checks if the reverse semaphore is zero.
  The reason the we call it a "reverse" semaphore is because the blocking condition
  is reversed, that is a semaphore blocks while it is zero, whereas a reverse semaphore
  blocks until it becomes zero.

  We represent a rsem as a set of tasks to be able to bookkeep registered tasks.
  *)

Record rsem := mk_rsem {
  value : set_tid
}.

(**
  We create a rsem without any registered task.
  *) 

Definition zero := mk_rsem Set_TID.empty.

Section API.

Variable l:rsem.

(**
  Registers a task in the rsem. Registered task must
  be eventually signaled or deregistered so that
  synchronization can happen.
  *)

Definition register (t:tid) :=
  mk_rsem (Set_TID.add t (value l)).

Definition inc := register.

(**
  Signaling a task revokes its registration,
  so tasks blocked on [wait] will no longer wait for
  the signalling task.
  *)

Definition signal (t:tid) :=
  mk_rsem (Set_TID.remove t (value l)).

Definition deregister := signal.
Definition dec := signal.

(**
  The [wait] operation should block until there are
  no registered tasks.
  *)

Inductive Wait : Prop :=
  wait_def:
    Set_TID.Empty (value l) ->
    Wait.

(**
  Asserts that task [t] is registerd in rsem [l].
  *)

Inductive Registered (t:tid) : Prop :=
  registered_def:
    Set_TID.In t (value l) ->
    Registered t.

End API.

Inductive Eq (l1:rsem) (l2:rsem) : Prop :=
  eq_def:
    Set_TID.eq (value l1) (value l2) ->
    Eq l1 l2.
Module Sem.

(** How do we represent that synchronization works? *)

Inductive op :=
  | REG
  | SIG
  | WAIT.

Inductive Redex (l:rsem) (t:tid) : op -> rsem -> Prop  :=
  | redex_reg:
    ~ Registered l t ->
    Redex l t REG (register l t)

  | redex_sig:
    Registered l t ->
    Redex l t SIG (signal l t)

  | redex_wait:
    Wait l ->
    Redex l t WAIT l.

End Sem.

Module Props.

Import Sem.

Inductive Check (l:rsem) (t:tid) : op -> Prop :=
  | check_reg:
    ~ Wait l ->
    ~ Registered l t ->
    Check l t REG
  | check_sig:
    Registered l t ->
    Check l t SIG
  | check_wait:
    ~ Registered l t ->
    Check l t WAIT.

(*
Module Commutativity.

Lemma check_respects_reduce:
  forall l l' t t' o o',
  Check l t o ->
  Redex l t' o' l' ->
  t <> t' ->
  Check l' t o.
Admitted.

Lemma check_reduces_inv:
  forall l t o l',
  Redex l t o l' ->
  Check l t o.
Admitted.

Lemma commutativity:
  forall l1 l2 l2' l3 l3' t1 t2 o1 o2,
  t1 <> t2 ->
  Redex l1 t1 o1 l2  -> Redex l2  t2 o2 l3 ->
  Redex l1 t2 o2 l2' -> Redex l2' t1 o1 l3' ->
  Eq l1 l2.
Admitted.  
*)

Section Progress.
(**
  Progress means that either the rsem is a value, or there
  is at least an operation that can be issued.
  But how can we enumerate the available operations?

  At any time a task may be registered, which means that there is always  
  *)

Variable l: rsem.

(**
  The first thing to show is that there is progress for
  unblocked tasks. We define a unblocking predicate that yields [true]
  when the operation is unblocking.
*)

Definition blocking (o:op) :=
  match o with
  | REG => false
  | SIG => false
  | WAIT => true
  end.

Lemma blocking_true:
  forall o,
  blocking o = true <-> o = WAIT.
Proof.
  destruct o; (simpl;
    (split; (
    intros;
    inversion H))); auto.
Qed.

(**
  Any unblocked 
  The proof for this lemma is trivial, by inversion of proposition [Check].
  *)

Require Import HJ.Progress.

Lemma progress_unblocked:
  forall t o,
  Check l t o ->
  blocking o = false ->
  CanReduce (Redex l) t o.
Proof.
  intros.
  destruct o.
  - inversion H.
    subst.
    eauto using redex_reg, can_reduce_def.
  - inversion H.
    subst.
    eauto using redex_sig, can_reduce_def.
  - inversion H0.
Qed.

Variable r:Map_TID.t op.

Variable reg_in_r : forall t, Registered l t <-> Map_TID.In t r.

Variable r_check: 
  forall t o, Map_TID.MapsTo t o r -> Check l t o.

Lemma registered_in_reqs:
  (forall t o, Map_TID.MapsTo t o r -> blocking o = true) ->
  forall t,
  Registered l t ->
  Map_TID.MapsTo t WAIT r.
Proof.
  intros.
  apply reg_in_r in H0.
  apply Map_TID_Extra.in_to_mapsto in H0.
  destruct H0 as (o,  Hmt).
  assert (o = WAIT). {
    apply H in Hmt.
    apply blocking_true.
    assumption.
  }
  subst.
  assumption.
Qed.

Lemma registered_check_wait:
  (forall t o, Map_TID.MapsTo t o r -> blocking o = true) ->
  forall t,
  Registered l t ->
  Check l t WAIT.
Proof.
  intros.
  auto using registered_in_reqs.
Qed.

Lemma progress_blocked:
  ~ Map_TID.Empty r ->
  (forall t o, Map_TID.MapsTo t o r -> blocking o = true) ->
  exists t o,
  Map_TID.MapsTo t o r /\
  CanReduce (Redex l) t o.
Proof.
  intros.
  (** Wait is enabled. *)
  assert (Hw: Wait l). {
    apply wait_def.
    unfold Set_TID.Empty.
    intros.
    destruct (Set_TID_Props.In_dec a (value l)).
    - assert (Hreg : Registered l a). { auto using registered_def. }
      assert (Check l a WAIT). {
        eapply registered_check_wait; auto.
      }
      inversion H1.
      contradiction H2.
    - assumption.
  }
  (** We can pick a task. *)
  destruct (Vars.Set_TID_Dep.choose (value l)) as [(t,Hin)|Hempty].
  - exists t.
    exists WAIT.
    split.
    + eauto using registered_def, registered_in_reqs.
    + exists l.
      auto using redex_wait.
  - apply Map_TID_Extra.nonempty_in in H.
    destruct H as (t, Hin).
    assert (Hsin : Set_TID.In t (value l)). {
      apply reg_in_r in Hin.
      inversion Hin.
      assumption.
    }
    unfold Set_TID.Empty in Hempty.
    assert (~ Set_TID.In t (value l)). {
      apply Hempty.
    }
    contradiction Hsin.
Qed.

Require HJ.Progress.

Variable reqs_spec :
  HJ.Progress.RequestSpec.request_spec r
  (Check l)
  (Registered l).

Let l_prog:
  @HJ.Progress.progress_spec op r (Check l) rsem (Redex l) blocking.
Proof.
  intros.
  refine (
    @HJ.Progress.mk_progress_spec op r (Check l) _
      (Redex l) blocking _ _); auto.
  - apply progress_unblocked.
  - apply progress_blocked.
Defined.

Lemma prog:
  ~ Map_TID.Empty r ->
  (** There is a task that can reduce. *)
  exists t o,
  Map_TID.MapsTo t o r /\ CanReduce (Redex l) t o.
Proof.
  intros.
  eauto using HJ.Progress.main_progress, l_prog.
Qed.
End Progress.
End Props.

