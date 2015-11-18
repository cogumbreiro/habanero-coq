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

(** Function [new_phaser] places a new empty phaser in the phasermap. *)

Definition ph_new (p:phid) (t:tid) : phasermap -> phasermap := Map_PHID.add p (Phaser.make t).

(**
  Similarly, to [Phaser.update] function [update] mutates the phaser associated to [p]
  with function [f].
 *)

Definition update p (f:phaser -> phaser) m : phasermap := 
match Map_PHID.find p m with
| Some ph => Map_PHID.add p (f ph) m
| None => m
end.

(** We defined signaling a phaser. *)

Definition ph_signal p t := update p (Phaser.signal t).

(** And droping a phaser. *)

Definition ph_drop p t := update p (Phaser.drop t).


(** Function [foreach] updates all phasers in the phasermap using function [f]. *)

Definition foreach (f:phaser -> phaser) : phasermap -> phasermap := Map_PHID.mapi (fun _ ph => f ph).

(** Function [drop_all] deregisters task [t] from all phasers in the phasermap. *)

Definition drop_all (t:tid) := foreach (Phaser.drop t).

(** Function [wait_all] lets task [t] perform a [Phaser.wait] on all phasers it is registered with. *)

Definition wait_all (t:tid) := foreach (Phaser.wait t).

(** Function [signal_all] lets task [t] perform a [Phaser.signal] on all phasers it is registered with. *)

Definition signal_all (t:tid) := foreach (Phaser.signal t).

(**
  We define async phased in two functions: [async] ranges over each phaser in the list 
  of phasers and uses [async_1] to registers the spawned
  task in a single phaser. Task [t] registers task [t'] in phaser [first ps]
  with mode [snd ps].
 *)

Definition phased := (phid * regmode) % type.

Definition async_1 (ps:phased) t' t pm :=
match Map_PHID.find (fst ps) pm with
| Some ph =>
  let ph' := register (mk_registry t' (snd ps)) t ph in
  Map_PHID.add (fst ps) ph' pm
| _ => pm
end.

(** Function [async] applies [async_1] to each element of [l]. *)

Fixpoint async l t' t pm :=
match l with
| cons ps l => async_1 ps t' t (async l t' t pm)
| nil => pm
end.

Module Semantics.
  Import Regmode.Notations.
  Require Import HJ.Phasers.Taskview.

  Open Scope reg_scope.

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
  
  (** Function [eval] interprets an operation as a function. *)

  Definition eval o :=
  match o with
  | PH_NEW p => ph_new p
  | PH_SIGNAL p => ph_signal p
  | PH_DROP p => ph_drop p
  | SIGNAL_ALL => signal_all
  | WAIT_ALL => wait_all
  | DROP_ALL => drop_all
  | ASYNC ps t => async ps t
  end.

  (** Predicate [In t m] holds when task [t] is registered in a phaser of [m]. *)

  Inductive In (t:tid) (pm:phasermap) : Prop :=
    in_def:
      forall p ph,
      Map_PHID.MapsTo p ph pm ->
      Map_TID.In t ph ->
      In t pm.

  (**
    The behaviour of [Async] is defined inductively, not computationally like the remaining
    operations.
   *)

  Inductive Phased (m:phasermap) (t:tid): list phased -> Prop :=
    | phased_step:
      forall p r l v ph,
      Phased m t l ->
      Map_PHID.MapsTo p ph m ->
      Map_TID.MapsTo t v ph ->
      r <= (mode v) ->
      Phased m t ((p,r)::l)
    | phased_nil:
      Phased m t nil.

  Definition eq_phid (p p':phased) := (fst p) = (fst p').

  (** Finally, we defined the [Reduce] relation. *)

  Inductive Reduce (m:phasermap) (t:tid): op -> phasermap -> Prop :=
    | reduce_ph_new:
      forall p,
      ~ Map_PHID.In p m ->
      Reduce m t (PH_NEW p) (ph_new p t m)
    | reduce_ph_signal:
      forall p ph,
      Map_PHID.MapsTo p ph m ->
      Reduce m t (PH_SIGNAL p) (ph_signal p t m)
    | reduce_ph_drop:
      forall p ph,
      Map_PHID.MapsTo p ph m ->
      Reduce m t (PH_DROP p) (ph_drop p t m)
   | reduce_signal_all:
      Reduce m t SIGNAL_ALL (signal_all t m)
   | reduce_wait_all:
     (forall p ph, Map_PHID.MapsTo p ph m -> Map_TID.In t ph -> Sync ph t) ->
     Reduce m t WAIT_ALL (wait_all t m)
   | reduce_drop_all:
      Reduce m t DROP_ALL (drop_all t m)
   | reduce_async:
      forall ps t',
      Phased m t ps ->
      NoDupA eq_phid ps ->
      ~ In t' m -> 
      Reduce m t (ASYNC ps t') (async ps t' t m).

End Semantics.
