Require Import Vars.
Require Import Coq.Arith.Peano_dec.

Inductive taskview : Set:=
  | SW : nat -> nat -> taskview
  | SO : nat -> taskview
  | WO : nat -> taskview.

Inductive SignalPhase: taskview -> nat -> Prop :=
  | signal_phase_sw:
    forall s w,
    SignalPhase (SW s w) s
  | signal_phase_so:
    forall s,
    SignalPhase (SO s) s.

Inductive WaitPhase : taskview -> nat -> Prop :=
  | wait_phase_sw:
    forall s w,
    WaitPhase (SW s w) w
  | wait_phase_so:
    forall w,
    WaitPhase (WO w) w.

Definition signal (v:taskview) := 
  match v with
    | SW s w => if eq_nat_dec s w then (SW (S s) w) else (SW s w)
    | SO s => SO (S s)
    | WO w => WO w
  end.

Definition wait (v:taskview) := 
  match v with
    | SW s w => if eq_nat_dec s (S w) then (SW s (S w)) else (SW s w)
    | SO s => SO s
    | WO w => WO (S w)
  end.

Inductive regmode : Set:=
  | SIGNAL_ONLY : regmode
  | WAIT_ONLY : regmode
  | SIGNAL_WAIT : regmode.

Definition mode (v:taskview) : regmode :=
  match v with
    | SW _ _ => SIGNAL_WAIT
    | SO _ => SIGNAL_ONLY
    | WO _ => WAIT_ONLY
  end.

Inductive copy : taskview -> regmode -> taskview -> Prop :=
  | copy_sw:
    forall v s w,
    SignalPhase v s ->
    WaitPhase v w ->
    copy v SIGNAL_WAIT (SW s w)
  | copy_so:
    forall v s,
    SignalPhase v s ->
    copy v SIGNAL_ONLY (SO s)
  | copy_wo:
    forall v w,
    WaitPhase v w ->
    copy v WAIT_ONLY (WO w).

Lemma copy_correct:
  forall v r v',
  copy v r v' ->
  r = mode v'.
Proof.
  intros.
  inversion H; repeat (subst; auto).
Qed.

Definition phaser := Map_TID.t taskview.

(* Phaser op *)
Inductive phop : Type :=
  | SIGNAL : phop
  | WAIT : phop
  | DROP : phop
  | REGISTER : tid -> regmode -> phop.

Definition Await (ph:phaser) (n:nat) :=
  forall t v s,
  Map_TID.MapsTo t v ph ->
  SignalPhase v s ->
  s >= n.

Inductive Sync : phaser -> nat -> Prop :=
  | sync_so:
    forall ph t s,
    Map_TID.MapsTo t (SO s) ph ->
    Sync ph t
  | sync_wait:
    forall ph t v w,
    Map_TID.MapsTo t v ph ->
    WaitPhase v w ->
    Await ph (S w) ->
    Sync ph t.
