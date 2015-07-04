Require Import Vars.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.

Inductive taskview : Set:=
  | SW : nat -> bool -> taskview
  | SO : nat -> taskview
  | WO : nat -> taskview.

Inductive SignalPhase: taskview -> nat -> Prop :=
  | signal_phase_sw_on:
    forall w,
    SignalPhase (SW w true) (S w)
  | signal_phase_sw_off:
    forall w,
    SignalPhase (SW w false) w
  | signal_phase_so:
    forall s,
    SignalPhase (SO s) s.

Inductive WaitPhase : taskview -> nat -> Prop :=
  | wait_phase_sw:
    forall w b,
    WaitPhase (SW w b) w
  | wait_phase_wo:
    forall w,
    WaitPhase (WO w) w.

Lemma wait_phase_inv:
  forall (v:taskview),
  exists n, (WaitPhase v n \/ v = SO n).
Proof.
  intros.
  destruct v.
  - (* SW *)
    exists n.
    left.
    apply wait_phase_sw.
  - (* SO *)
    exists n; auto.
  - (* WO *)
    exists n.
    left.
    apply wait_phase_wo.
Qed.

Definition signal (v:taskview) := 
  match v with
    | SW s w => SW s true
    | SO s => SO (S s)
    | WO w => WO w
  end.

Definition wait (v:taskview) := 
  match v with
    | SW w b => 
      match b with
        | true => (SW (S w) false)
        | false => SW w b
      end
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

Inductive Copy : taskview -> regmode -> taskview -> Prop :=
  | copy_sw:
    forall s b,
    Copy (SW s b) SIGNAL_WAIT (SW s b)
  | copy_so:
    forall v s,
    SignalPhase v s ->
    Copy v SIGNAL_ONLY (SO s)
  | copy_wo:
    forall v w,
    WaitPhase v w ->
    Copy v WAIT_ONLY (WO w).

Lemma copy_correct:
  forall v r v',
  Copy v r v' ->
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

Inductive PhReduce : phaser -> tid -> phop -> phaser -> Prop :=
  | ph_reduce_signal:
    forall t v ph,
    Map_TID.MapsTo t v ph ->
    PhReduce ph t SIGNAL (Map_TID.add t (signal v) ph)
  | ph_reduce_wait:
    forall t v ph,
    Map_TID.MapsTo t v ph ->
    Sync ph t ->
    PhReduce ph t WAIT (Map_TID.add t (wait v) ph)
  | ph_reduce_register:
    forall t t' v v' ph m,
    Map_TID.MapsTo t v ph ->
    Copy v m v' ->
    PhReduce ph t (REGISTER t' m) (Map_TID.add t' v' ph)
  | ph_reduce_drop:
    forall t v ph,
    Map_TID.MapsTo t v ph ->
    PhReduce ph t DROP (Map_TID.remove t ph).

Definition phased := (phid * regmode) % type.

Inductive op : Type :=
  | PH_NEW : phid -> op
  | PH_SIGNAL : phid -> op
  | PH_DROP : phid -> op
  | SIGNAL_ALL : op
  | WAIT_ALL : op
  | ASYNC : list phased -> tid -> op.

Definition phasermap := Map_PHID.t phaser.

Inductive Call : phasermap -> tid -> phid -> phop -> phasermap -> Prop :=
  call_def:
    forall pm t p ph o ph',
    Map_PHID.MapsTo p ph pm ->
    PhReduce ph t o ph' ->
    Call pm t p o (Map_PHID.add t ph' pm).

Inductive Foreach : phasermap -> tid -> list phid -> phop -> phasermap -> Prop :=
  | foreach_step:
    forall m t p ps o m' m'',
    Foreach m t ps o m' ->
    Call m' t p o m'' ->
    (* -------------- *)
    Foreach m t (p::ps) o m''

  | foreach_nil:
    forall m t o,
    Foreach m t nil o m.

Inductive Async : phasermap -> tid -> list phased -> tid -> phasermap -> Prop :=
  | async_step:
    forall m t p r a t' m' m'',
    Async m t a t' m' ->
    Call m' t p (REGISTER t' r)  m'' ->
    (* -------------- *)
    Async m t ((p,r)::a) t' m''

  | async_nil:
    forall m t t',
    Async m t nil t' m.

Definition newPhaser (t:tid) := Map_TID.add t (SW 0 false) (Map_TID.empty taskview).

Definition TaskIn (t:tid) (p:phid) (pm:phasermap) :=
  exists ph, Map_PHID.MapsTo p ph pm /\ Map_TID.In t ph.

Lemma task_in_def:
  forall t p ph pm,
  Map_PHID.MapsTo p ph pm ->
  Map_TID.In t ph ->
  TaskIn t p pm.
Proof.
  intros.
  unfold TaskIn.
  exists ph.
  intuition.
Qed.

Definition TaskInMany (t:tid) (ps:list phid) (pm:phasermap) :=
  Forall (fun p => TaskIn t p pm) ps.

Inductive Registered : phasermap -> tid -> list phid -> Prop :=
  registered_def:
    forall pm t ps,
    NoDup ps ->
    TaskInMany t ps pm ->
    (forall p, TaskIn t p pm -> In p ps) ->
    Registered pm t ps.

Inductive Reduce : phasermap -> tid -> op -> phasermap -> Prop :=
  | reduce_new:
    forall pm t p,
    ~ Map_PHID.In p pm ->
    (* --------------- *)
    Reduce pm t (PH_NEW p) (Map_PHID.add p (newPhaser t) pm)

  | reduce_signal:
    forall pm t p pm',
    Call pm t p SIGNAL pm' ->
    (* --------------- *)
    Reduce pm t (PH_SIGNAL p) pm'

  | reduce_drop:
    forall pm t p pm',
    Call pm t p DROP pm' ->
    (* --------------- *)
    Reduce pm t (PH_DROP p) pm'

 | reduce_signal_all:
    forall m t m' ps,
    Registered m t ps ->
    Foreach m t ps SIGNAL m' ->
    (* --------------- *)
    Reduce m t SIGNAL_ALL m'

 | reduce_wait_all:
    forall m t m' ps,
    Registered m t ps ->
    Foreach m t ps WAIT m' ->
    (* --------------- *)
    Reduce m t WAIT_ALL m'.
