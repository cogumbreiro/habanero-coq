Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
Require Import HJ.Vars.
Require Export HJ.Phasers.Taskview.
Require Export HJ.Phasers.Phaser.

Definition phased := (phid * regmode) % type.

Inductive op : Type :=
  | PH_NEW : phid -> op
  | PH_SIGNAL : phid -> op
  | PH_DROP : phid -> op
  | SIGNAL_ALL : op
  | WAIT_ALL : op
  | DROP_ALL : op
  | ASYNC : list phased -> tid -> op.

Definition phasermap := Map_PHID.t phaser.

Module Phasermap.
  Definition make : phasermap := Map_PHID.empty phaser.
  Definition new_phaser (p:phid) (t:tid) : phasermap -> phasermap := Map_PHID.add p (Phaser.make t).
  Definition put (p:phid) (ph:phaser) : phasermap -> phasermap := Map_PHID.add p ph.
  Definition foreach (f:phaser -> phaser) : phasermap -> phasermap := Map_PHID.mapi (fun _ ph => f ph).
  Definition drop_all (t:tid) := foreach (Phaser.drop t).
  Definition wait_all (t:tid) := foreach (Phaser.wait t).
  Definition signal_all (t:tid) := foreach (Phaser.signal t).
End Phasermap.

Import Phasermap.

Section PhasermapDef.
Import Taskview.Notations.
Open Scope reg_scope.

Inductive Async : phasermap -> tid -> list phased -> tid -> phasermap -> Prop :=
  | async_step:
    forall m t p r a t' m' v ph,
    Async m t a t' m' ->
    Map_PHID.MapsTo p ph m' ->
    Map_TID.MapsTo t v ph ->
    (r <= v.(mode)) ->
    (* -------------- *)
    Async m t ((p,r)::a) t' (Map_PHID.add p (Map_TID.add t' (set_mode v r) ph) m')

  | async_nil:
    forall m t t',
    Async m t nil t' m.

Inductive Reduce (m:phasermap) (t:tid): op -> phasermap -> Prop :=
  | reduce_new:
    forall p,
    ~ Map_PHID.In p m ->
    (* --------------- *)
    Reduce m t (PH_NEW p) (new_phaser p t m)

  | reduce_signal:
    forall p ph,
    Map_PHID.MapsTo p ph m ->
    (* --------------- *)
    Reduce m t (PH_SIGNAL p) (put p (Phaser.signal t ph) m)

  | reduce_drop:
    forall p ph,
    Map_PHID.MapsTo p ph m ->
    (* --------------- *)
    Reduce m t (PH_DROP p) (put p (Phaser.drop t ph) m)

 | reduce_signal_all:
    (* --------------- *)
    Reduce m t SIGNAL_ALL (signal_all t m)

 | reduce_wait_all:
    (* check if it can synchronize on every phaser *)
    (forall p ph, Map_PHID.MapsTo p ph m -> Sync ph t) ->
    (* --------------- *)
    Reduce m t WAIT_ALL (wait_all t m)

 | reduce_drop_all:
    (* --------------- *)
    Reduce m t DROP_ALL (drop_all t m)

 | reduce_async:
    forall ps t' m',
    Async m t ps t' m' ->
    Reduce m t (ASYNC ps t') m'.

Inductive In (t:tid) (pm:phasermap) : Prop :=
  in_def:
    forall p ph,
    Map_PHID.MapsTo p ph pm ->
    Map_TID.In t ph ->
    In t pm.
End PhasermapDef.
