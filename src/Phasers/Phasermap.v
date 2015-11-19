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

Record Op := mk_op {
  can_run: tid -> phasermap -> Prop;
  run: tid -> phasermap -> phasermap
}.

(** Function [new_phaser] places a new empty phaser in the phasermap. *)

Inductive PhNewPre p (t:tid) (m:phasermap) : Prop :=
  ph_new_pre:
    ~ Map_PHID.In p m ->
    PhNewPre p t m.

Definition ph_new (p:phid) (t:tid) : phasermap -> phasermap := Map_PHID.add p (Phaser.make t).

Definition ph_new_op p := mk_op (PhNewPre p) (ph_new p).

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

Inductive PhSignalPre p t m : Prop :=
  ph_signal_pre:
    forall ph,
    Map_PHID.MapsTo p ph m ->
    SignalPre t ph ->
    PhSignalPre p t m.

Definition ph_signal p t := update p (Phaser.signal t).

Definition ph_signal_op p := mk_op (PhSignalPre p) (ph_signal p).

(** And droping a phaser. *)

Inductive PhDropPre p t m : Prop :=
  ph_drop_pre:
    forall ph,
    Map_PHID.MapsTo p ph m ->
    DropPre t ph ->
    PhDropPre p t m.

Definition ph_drop p t := update p (Phaser.drop t).

Definition ph_drop_op p := mk_op (PhDropPre p) (ph_drop p).

(** Function [foreach] updates all phasers in the phasermap using function [f]. *)

Definition foreach (f:phaser -> phaser) : phasermap -> phasermap := Map_PHID.mapi (fun _ ph => f ph).

(** Function [signal_all] lets task [t] perform a [Phaser.signal] on all phasers it is registered with. *)

Definition signal_all (t:tid) := foreach (Phaser.signal t).

Definition signal_all_op := mk_op (fun _ _ => True) signal_all.

Inductive WaitAllPre t m : Prop :=
  wait_all_pre:
    (forall p ph, Map_PHID.MapsTo p ph m -> Map_TID.In t ph -> WaitPre t ph) ->
    WaitAllPre t m.

(** Function [wait_all] lets task [t] perform a [Phaser.wait] on all phasers it is registered with. *)

Definition wait_all (t:tid) := foreach (Phaser.wait t).

Definition wait_all_op := mk_op WaitAllPre wait_all.

(** Function [drop_all] deregisters task [t] from all phasers in the phasermap. *)

Definition drop_all (t:tid) := foreach (Phaser.drop t).

Definition drop_all_op := mk_op (fun _ _ => True) drop_all.

  (** Predicate [In t m] holds when task [t] is registered in a phaser of [m]. *)

  Inductive In (t:tid) (pm:phasermap) : Prop :=
    in_def:
      forall p ph,
      Map_PHID.MapsTo p ph pm ->
      Map_TID.In t ph ->
      In t pm.

  (**
    Predicate [Phased m t t' ps] holds when:
    1. task [t] is registered with phaser [fst ps]
    2. task [t] can register [t'] according to mode [snd ps]
   *)

(**
  Function [async] applies [async_1] to each element of [l], converting
  each pair to a [registry] object. *)

Definition phased := (phid * regmode) % type.

Inductive Phased (m:phasermap) (t t':tid) (ps:phased) : Prop := 
  phased_def:
    forall ph v,
    Map_PHID.MapsTo (fst ps) ph m ->
    Map_TID.MapsTo t v ph ->
    RegisterPre (mk_registry t' (snd ps)) t ph ->
    Phased m t t' ps.

Definition eq_phid (p p':phased) := (fst p) = (fst p').

Inductive AsyncPre ps t' t m : Prop :=
  async_pre:
    Forall (Phased m t t') ps ->
    NoDupA eq_phid ps ->
    ~ In t' m -> 
    AsyncPre ps t' t m.

(**
  We define async phased in two functions: [async] ranges over each phaser in the list 
  of phasers and uses [async_1] to registers the spawned
  task in a single phaser. Task [t] registers task [t'] in phaser [first ps]
  with mode [snd ps].
 *)

(** Function [async_1] expects the name of the phaser where
  to register [r]; task [t] is the issuer; phasermap [pm] is the target. *)

Definition async_1 p r t pm :=
match Map_PHID.find p pm with
| Some ph => Map_PHID.add p (register r t ph) pm
| _ => pm
end.

Fixpoint async (l:list phased) t' t pm :=
match l with
| cons (p, r) l => async_1 p (mk_registry t' r) t (async l t' t pm)
| nil => pm
end.

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
  
(** Function [eval] interprets an operation as a function. *)

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


(** Finally, we define the [Reduce] relation. *)

Inductive Reduces m t o : phasermap -> Prop :=
  reduces:
    can_run (get_impl o) t m ->
    Reduces m t o (run (get_impl o) t m).

