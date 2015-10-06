Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
Require Import HJ.Vars.

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
    r_le m SIGNAL_WAIT
where "n <= m" := (r_le n m) : reg_scope.

Local Open Scope reg_scope.

Record taskview := TV {
  signal_phase: nat;
  wait_phase: nat;
  mode: regmode
}.

Let inc_signal (v:taskview) := TV (v.(signal_phase) + 1) v.(wait_phase) v.(mode).

Let set_mode (v:taskview) (m:regmode) := TV v.(signal_phase) v.(wait_phase) m.

Definition signal (v:taskview) :=
  match v.(mode) with
    | SIGNAL_ONLY => v
    | _ => if eq_nat_dec v.(signal_phase) v.(wait_phase) then (inc_signal v) else v
  end.

Definition wait (v:taskview) := TV v.(signal_phase) (v.(wait_phase) + 1) v.(mode).

Definition WaitCap (v:taskview) :=
  mode v = SIGNAL_WAIT \/ mode v = WAIT_ONLY.

Lemma wait_cap_dec:
  forall v,
  { WaitCap v } + { ~ WaitCap v }.
Proof.
  intros.
  remember (mode v).
  destruct r.
  - right. intuition.
    unfold WaitCap in *.
    intuition; repeat (rewrite H0 in Heqr; inversion Heqr).
  - left. unfold WaitCap; intuition.
  - left. unfold WaitCap; intuition.
Qed.

Lemma wait_cap_or_sigonly:
  forall v,
  WaitCap v \/  mode v = SIGNAL_ONLY.
Proof.
  intros.
  destruct (wait_cap_dec v).
  - intuition.
  - destruct v.
    right.
    simpl in *.
    unfold WaitCap in *.
    intuition.
    simpl in *.
    destruct mode0; repeat (intuition).
Qed.

Definition SignalCap (v:taskview) :=
  mode v = SIGNAL_WAIT \/ mode v = SIGNAL_ONLY.

Definition phaser := Map_TID.t taskview.

Definition drop : tid -> phaser -> phaser := @Map_TID.remove taskview.

Definition Await (ph:phaser) (n:nat) :=
  forall t v,
  Map_TID.MapsTo t v ph ->
  v.(signal_phase) >= n.

Inductive Sync : phaser -> nat -> Prop :=
  | sync_so:
    forall t v ph,
    Map_TID.MapsTo t v ph ->
    mode v = SIGNAL_ONLY ->
    Sync ph t
  | sync_wait:
    forall ph t v,
    Map_TID.MapsTo t v ph ->
    WaitCap v ->
    Await ph (v.(wait_phase) + 1) ->
    Sync ph t
  | sync_skip:
    forall t ph,
    ~ Map_TID.In t ph ->
    Sync ph t.

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

Definition newPhaser (t:tid) := Map_TID.add t (TV 0 0 SIGNAL_WAIT) (Map_TID.empty taskview).

Definition update (t:tid) (f:taskview -> phaser) (ph:phaser) :=
  match Map_TID.find t ph with
    | Some v => f v
    | None => ph
  end.

Definition apply (t:tid) (f:taskview -> taskview) (ph:phaser) : phaser :=
  update t (fun v => Map_TID.add t (f v) ph) ph.

Definition mapi (t:tid) (f:taskview->taskview) : phasermap -> phasermap :=
  Map_PHID.mapi (fun p ph => apply t f ph).

Definition drop_all (t:tid) : phasermap -> phasermap :=
  Map_PHID.mapi (fun _ ph => drop t ph).

Inductive Reduce (m:phasermap) (t:tid): op -> phasermap -> Prop :=
  | reduce_new:
    forall p,
    ~ Map_PHID.In p m ->
    (* --------------- *)
    Reduce m t (PH_NEW p) (Map_PHID.add p (newPhaser t) m)

  | reduce_signal:
    forall p ph,
    Map_PHID.MapsTo p ph m ->
    (* --------------- *)
    Reduce m t (PH_SIGNAL p) (Map_PHID.add p (apply t signal ph) m)

  | reduce_drop:
    forall p ph,
    Map_PHID.MapsTo p ph m ->
    (* --------------- *)
    Reduce m t (PH_DROP p) (Map_PHID.add p (drop t ph) m)

 | reduce_signal_all:
    (* --------------- *)
    Reduce m t SIGNAL_ALL (mapi t signal m)

 | reduce_wait_all:
    (* check if it can synchronize on every phaser *)
    (forall p ph, Map_PHID.MapsTo p ph m -> Sync ph t) ->
    (* --------------- *)
    Reduce m t WAIT_ALL (mapi t wait m)

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
