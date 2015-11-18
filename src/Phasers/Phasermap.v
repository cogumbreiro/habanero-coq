Require Import HJ.Vars.
Require Import HJ.Phasers.Regmode.
Require Import HJ.Phasers.Phaser.

Definition phasermap := Map_PHID.t phaser.

Definition make : phasermap := Map_PHID.empty phaser.
Definition new_phaser (p:phid) (t:tid) : phasermap -> phasermap := Map_PHID.add p (Phaser.make t).
Definition put (p:phid) (ph:phaser) : phasermap -> phasermap := Map_PHID.add p ph.
Definition foreach (f:phaser -> phaser) : phasermap -> phasermap := Map_PHID.mapi (fun _ ph => f ph).
Definition drop_all (t:tid) := foreach (Phaser.drop t).
Definition wait_all (t:tid) := foreach (Phaser.wait t).
Definition signal_all (t:tid) := foreach (Phaser.signal t).

Module Semantics.
  Import Regmode.Notations.
  Require Import HJ.Phasers.Taskview.

  Open Scope reg_scope.

  Definition phased := (phid * regmode) % type.

  Inductive op : Type :=
  | PH_NEW : phid -> op
  | PH_SIGNAL : phid -> op
  | PH_DROP : phid -> op
  | SIGNAL_ALL
  | WAIT_ALL
  | DROP_ALL
  | ASYNC : list phased -> tid -> op.

  Inductive Async : phasermap -> tid -> list phased -> tid -> phasermap -> Prop :=
    | async_step:
      forall m t p r a t' m' v ph,
      Async m t a t' m' ->
      Map_PHID.MapsTo p ph m' ->
      Map_TID.MapsTo t v ph ->
      (r <= v.(mode)) ->
      Async m t ((p,r)::a) t' (Map_PHID.add p (Map_TID.add t' (set_mode v r) ph) m')
    | async_nil:
      forall m t t',
      Async m t nil t' m.

  Inductive Reduce (m:phasermap) (t:tid): op -> phasermap -> Prop :=
    | reduce_new:
      forall p,
      ~ Map_PHID.In p m ->
      Reduce m t (PH_NEW p) (new_phaser p t m)
    | reduce_signal:
      forall p ph,
      Map_PHID.MapsTo p ph m ->
      Reduce m t (PH_SIGNAL p) (put p (Phaser.signal t ph) m)
    | reduce_drop:
      forall p ph,
      Map_PHID.MapsTo p ph m ->
      Reduce m t (PH_DROP p) (put p (Phaser.drop t ph) m)
   | reduce_signal_all:
      Reduce m t SIGNAL_ALL (signal_all t m)
   | reduce_wait_all:
     (forall p ph, Map_PHID.MapsTo p ph m -> Map_TID.In t ph -> Sync ph t) ->
     Reduce m t WAIT_ALL (wait_all t m)
   | reduce_drop_all:
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
End Semantics.
