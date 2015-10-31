Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
Require Import HJ.Vars.

Inductive regmode : Set:=
  | SIGNAL_ONLY : regmode
  | WAIT_ONLY : regmode
  | SIGNAL_WAIT : regmode.

Lemma regmode_eq_dec:
 forall (m1 m2:regmode),
 { m1 = m2 } + { m1 <> m2 }.
Proof.
  intros.
  destruct m1, m2; solve [ left; auto | right; intuition; inversion H]. 
Qed.

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

Open Scope reg_scope.

Record taskview := TV {
  signal_phase: nat;
  wait_phase: nat;
  mode: regmode
}.

Module Taskview.

  Definition make := TV 0 0 SIGNAL_WAIT.

  (** Standard mutators. *)

  Definition set_mode (v:taskview) (m:regmode) := TV v.(signal_phase) v.(wait_phase) m.
  Definition set_signal_phase (v:taskview) (n:nat) := TV n (wait_phase v) (mode v).
  Definition set_wait_phase (v:taskview) (n:nat) := TV (signal_phase v) n (mode v).

  (** Signal operation on taskviews. *)

  Definition signal (v:taskview) :=
  match v.(mode) with
    | SIGNAL_ONLY => set_signal_phase v (S (signal_phase v))
    | _ => set_signal_phase v (S (wait_phase v))
  end.

  (** Wait operation on taskviews. *)

  Definition wait (v:taskview) := set_wait_phase v (S (wait_phase v)).
End Taskview.

Import Taskview. 

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

Lemma neq_so_to_wait_cap:
  forall v,
  mode v <> SIGNAL_ONLY ->
  WaitCap v.
Proof.
  intros.
  unfold WaitCap.
  destruct v; simpl in *; destruct mode0.
  - contradiction H; trivial.
  - intuition.
  - intuition.
Qed.

Lemma not_wait_cap_to_so:
  forall v,
  ~ WaitCap v ->
  mode v = SIGNAL_ONLY.
Proof.
  intros.
  unfold WaitCap in *.
  destruct v; simpl in *.
  destruct mode0; intuition.
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

Lemma signal_cap_dec:
  forall v,
  { SignalCap v } + { ~ SignalCap v }.
Proof.
  intros.
  remember (mode v).
  destruct r.
  - left; unfold SignalCap; intuition.
  - right. intuition.
    unfold SignalCap in *.
    intuition; repeat (
    rewrite H0 in Heqr; inversion Heqr).
  - left; unfold SignalCap; intuition.
Qed.

Lemma neq_wo_to_signal_cap:
  forall v,
  mode v <> WAIT_ONLY ->
  SignalCap v.
Proof.
  intros.
  unfold SignalCap.
  destruct v; simpl in *; destruct mode0.
  - intuition.
  - contradiction H; trivial.
  - intuition.
Qed.

Lemma not_signal_cap_to_wo:
  forall v,
  ~ SignalCap v ->
  mode v = WAIT_ONLY.
Proof.
  intros.
  unfold SignalCap in *.
  destruct v; simpl in *.
  destruct mode0; intuition.
Qed.

Definition phaser := Map_TID.t taskview.


Module Phaser.

  Definition make (t:tid) := Map_TID.add t Taskview.make (Map_TID.empty taskview).

  Definition update (t:tid) (f:taskview -> taskview) (ph:phaser) : phaser :=
  match Map_TID.find t ph with
    | Some v => Map_TID.add t (f v) ph
    | None => ph
  end.

  Definition signal (t:tid) := update t Taskview.signal.

  Definition wait (t:tid) := update t Taskview.wait.

  Definition drop : tid -> phaser -> phaser := @Map_TID.remove taskview.

End Phaser.

Definition Await (ph:phaser) (n:nat) :=
  forall t v,
  Map_TID.MapsTo t v ph ->
  SignalCap v ->
  v.(signal_phase) >= n.

Inductive Sync : phaser -> tid -> Prop :=
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
