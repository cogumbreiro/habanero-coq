Require Import HJ.Vars.
Require Import HJ.Phasers.Regmode.
Require Import HJ.Phasers.Phaser.
Require Import Coq.Lists.SetoidList.

(** This chapter defines a deadlock-free phaser language. A [phasermap] represents
all phasers available for a set of tasks. A phasermap is a map from phaser handles [phid]
into phasers. *)

Definition phasermap := Map_PHID.t phaser.

(** Function [make] creates an empty phasermap. *)

Definition make : phasermap := Map_PHID.empty phaser.

(**
  We now define phasermap operations, first with a pre-condition and
  then a function that executes the operation.
  *)

Record Op := mk_op {
  can_run: tid -> phasermap -> Prop;
  run: tid -> phasermap -> phasermap
}.

(**
  Function [new_phaser] places a new empty phaser in the phasermap.
  The pre-condition is that [p] is not in phasermap [m]. *)

Inductive PhNewPre p (t:tid) (m:phasermap) : Prop :=
  ph_new_pre:
    ~ Map_PHID.In p m ->
    PhNewPre p t m.

Definition ph_new (p:phid) (t:tid) : phasermap -> phasermap := Map_PHID.add p (Phaser.make t).

Definition ph_new_op p := mk_op (PhNewPre p) (ph_new p).

(**
  Function [update] mutates the phaser associated to [p] by applying
  parameter [f] to the phaser.
 *)

Definition update p (f:phaser -> phaser) m : phasermap := 
match Map_PHID.find p m with
| Some ph => Map_PHID.add p (f ph) m
| None => m
end.

(**
  Signal applies the phaser-signal to the phaser associated with [p].
  The pre-condition is that [p] must be in the phasermap and
  we must meet the pre-conditions of the phaser-signal.
  *)

Inductive PhSignalPre p t m : Prop :=
  ph_signal_pre:
    forall ph,
    Map_PHID.MapsTo p ph m ->
    SignalPre t ph ->
    PhSignalPre p t m.

Definition ph_signal p t := update p (Phaser.signal t).

Definition ph_signal_op p := mk_op (PhSignalPre p) (ph_signal p).

(** Droping a phaser has a similar implementation and pre-conditions. *)

Inductive PhDropPre p t m : Prop :=
  ph_drop_pre:
    forall ph,
    Map_PHID.MapsTo p ph m ->
    DropPre t ph ->
    PhDropPre p t m.

Definition ph_drop p t := update p (Phaser.drop t).

Definition ph_drop_op p := mk_op (PhDropPre p) (ph_drop p).

(**
  We now introduce functions that act on all phasers the task is regitered  with.
  Function [foreach] updates all phasers in the phasermap by applying function [f].
  *)

Definition foreach (f:phaser -> phaser) : phasermap -> phasermap :=
Map_PHID.mapi (fun _ ph => f ph).

(** Function [signal_all] lets task [t] perform a [Phaser.signal] on all phasers
    it is registered with. There are no pre-conditions to this operation. *)

Definition signal_all (t:tid) := foreach (Phaser.signal t).

Definition signal_all_op := mk_op (fun _ _ => True) signal_all.

(**
  Wait-all invokes a wait on every phaser the task is registered with.
  The pre-condition of wait-all is the pre-condition of each phaser the
  task is registered with. *)

Inductive WaitAllPre t m : Prop :=
  wait_all_pre:
    (forall p ph, Map_PHID.MapsTo p ph m -> Map_TID.In t ph -> WaitPre t ph) ->
    WaitAllPre t m.

Definition wait_all (t:tid) := foreach (Phaser.wait t).

Definition wait_all_op := mk_op WaitAllPre wait_all.

(**
  Function [drop_all] deregisters task [t] from all phasers in the phasermap; it
  has no pre-conditions.
  *)

Definition drop_all (t:tid) := foreach (Phaser.drop t).

Definition drop_all_op := mk_op (fun _ _ => True) drop_all.

(**
  Finally, we define async. To be able to spawn a task we must ensure
  that the spawned task name is unknown in all phasers, so we need to
  define a task membership for phasermaps.
  Predicate [In t m] holds when task [t] is registered in a phaser of [m]. *)

Inductive In (t:tid) (pm:phasermap) : Prop :=
  in_def:
    forall p ph,
    Map_PHID.MapsTo p ph pm ->
    Map_TID.In t ph ->
    In t pm.

(** The parameter of a phased async is list of pairs, each of which
  consists of a phaser name and a registration  mode. *)

Definition phased := (phid * regmode) % type.

(** 
  Async phased register a new task in a list of [phased].
  Function [async_1] registers task [t] with phaser named by [p] according
  to mode [r].
  *)

Definition async_1 p r t pm :=
match Map_PHID.find p pm with
| Some ph => Map_PHID.add p (register r t ph) pm
| _ => pm
end.

(**
  Function [async] implements the phased async, by applying function
  [async_1] to each pair of the list of [phased] objects.
*)

Fixpoint async (l:list phased) t' t pm :=
match l with
| cons (p, r) l => async_1 p (mk_registry t' r) t (async l t' t pm)
| nil => pm
end.


(**
  Predicate [PhasedPre] ensures that task [t] can register task [t']
  using the phased object [ps].
   *)

Inductive PhasedPre (m:phasermap) (t t':tid) (ps:phased) : Prop := 
  phased_def:
    forall ph v,
    Map_PHID.MapsTo (fst ps) ph m ->
    Map_TID.MapsTo t v ph ->
    RegisterPre (mk_registry t' (snd ps)) t ph ->
    PhasedPre m t t' ps.

(**
  The pre-condition of executing an async are three:
  (i) all phased pairs in [ps] must meet the preconditions of [PhasedPre],
  (ii) the phaser names in [ps] cannot be appear multiple times in [ps],
  (iii) the spawned task [t'] cannot be known in the phasermap.
  *)

Definition eq_phid (p p':phased) := (fst p) = (fst p').

Inductive AsyncPre ps t' t m : Prop :=
  async_pre:
    Forall (PhasedPre m t t') ps ->
    NoDupA eq_phid ps ->
    ~ In t' m -> 
    AsyncPre ps t' t m.

Definition async_op l t := mk_op (AsyncPre l t) (async l t).

(**
  We are now ready to define the closed set of operations on phasermaps.
 *)

Inductive op : Type :=
| PH_NEW : phid -> op
| PH_SIGNAL : phid -> op
| PH_DROP : phid -> op
| SIGNAL_ALL
| WAIT_ALL
| DROP_ALL
| ASYNC : list phased -> tid -> op.
  
(** Function [get_impl] yields the [Op] object. *)

Definition get_impl o :=
match o with
| PH_NEW p => ph_new_op p
| PH_SIGNAL p => ph_signal_op p
| PH_DROP p => ph_drop_op p
| SIGNAL_ALL => signal_all_op
| WAIT_ALL => wait_all_op
| DROP_ALL => drop_all_op
| ASYNC ps t => async_op ps t
end.


(** In closing, we define the [Reduces] relation. *)

Inductive Reduces m t o : phasermap -> Prop :=
  reduces:
    can_run (get_impl o) t m ->
    Reduces m t o (run (get_impl o) t m).

