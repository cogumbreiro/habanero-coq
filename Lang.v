Require Import Vars.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.

Inductive taskview : Set:=
  | SW : nat -> bool -> taskview
  | SO : nat -> nat -> taskview
  | WO : nat -> taskview.

Inductive SignalPhase: taskview -> nat -> Prop :=
  | signal_phase_sw_on:
    forall w,
    SignalPhase (SW w true) (S w)
  | signal_phase_sw_off:
    forall w,
    SignalPhase (SW w false) w
  | signal_phase_so:
    forall s w,
    SignalPhase (SO s w) s.

Inductive WaitPhase : taskview -> nat -> Prop :=
  | wait_phase_sw:
    forall w b,
    WaitPhase (SW w b) w
  | wait_phase_wo:
    forall w,
    WaitPhase (WO w) w
  | wait_phase_so:
    forall s w,
    WaitPhase (SO s w) w.

Definition signal_phase (v:taskview) :=
  match v with
    | SW w b => if b then (Some (S w)) else (Some w)
    | WO w => None
    | SO s _ => Some s
  end.

Definition wait_phase (v:taskview) :=
  match v with
    | SW w _ => w
    | WO w => w
    | SO _ w => w
  end.

Lemma get_wait_phase:
  forall (v:taskview),
  exists n, (WaitPhase v n).
Proof.
  intros.
  destruct v.
  - (* SW *)
    exists n.
    apply wait_phase_sw.
  - (* SO *)
    exists n0; apply wait_phase_so.
  - (* WO *)
    exists n.
    apply wait_phase_wo.
Qed.

Lemma wait_phase_spec_1:
  forall v,
  WaitPhase v (wait_phase v).
Proof.
  intros.
  destruct v.
  - apply wait_phase_sw.
  - apply wait_phase_so.
  - apply wait_phase_wo.
Qed.

Lemma wait_phase_spec_2:
  forall v n,
  WaitPhase v n ->
  n = wait_phase v.
Proof.
  intros.
  destruct v;
  repeat (simpl; inversion H; auto).
Qed.

Lemma signal_phase_spec_1:
  forall v s,
  signal_phase v = Some s ->
  SignalPhase v s.
Proof.
  intros.
  destruct v.
  - simpl in *.
    destruct b.
    + inversion H; apply signal_phase_sw_on.
    + inversion H; apply signal_phase_sw_off.
  - simpl in *.
    inversion H; apply signal_phase_so.
  - simpl in H.
    inversion H.
Qed.

Definition signal (v:taskview) := 
  match v with
    | SW s w => SW s true
    | SO s w => SO (S s) w
    | WO w => WO w
  end.

Definition wait (v:taskview) := 
  match v with
    | SW w b => 
      match b with
        | true => SW (S w) false
        | false => SW w b
      end
    | SO s w => SO s (S w)
    | WO w => WO (S w)
  end.

Inductive regmode : Set:=
  | SIGNAL_ONLY : regmode
  | WAIT_ONLY : regmode
  | SIGNAL_WAIT : regmode.

Definition mode (v:taskview) : regmode :=
  match v with
    | SW _ _ => SIGNAL_WAIT
    | SO _ _ => SIGNAL_ONLY
    | WO _ => WAIT_ONLY
  end.

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
  - right.
    unfold WaitCap in *.
    intuition.
    remember (mode v).
    destruct v; repeat intuition.
Qed.

Definition SignalCap (v:taskview) :=
  mode v = SIGNAL_WAIT \/ mode v = SIGNAL_ONLY.

Inductive Copy : taskview -> regmode -> taskview -> Prop :=
  | copy_sw:
    forall s b,
    Copy (SW s b) SIGNAL_WAIT (SW s b)
  | copy_so:
    forall v s w,
    SignalPhase v s ->
    WaitPhase v w ->
    Copy v SIGNAL_ONLY (SO s w)
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

Definition Await (ph:phaser) (n:nat) :=
  forall t v s,
  Map_TID.MapsTo t v ph ->
  SignalPhase v s ->
  s >= n.

Inductive Sync : phaser -> nat -> Prop :=
  | sync_so:
    forall t v ph,
    Map_TID.MapsTo t v ph ->
    mode v = SIGNAL_ONLY ->
    Sync ph t
  | sync_wait:
    forall ph t v w,
    Map_TID.MapsTo t v ph ->
    WaitPhase v w ->
    WaitCap v ->
    Await ph (S w) ->
    Sync ph t
  | sync_skip:
    forall t ph,
    ~ Map_TID.In t ph ->
    Sync ph t.

Inductive reg : Type :=
  | REGISTER : tid -> regmode -> reg.

Inductive Register : phaser -> tid -> reg -> phaser -> Prop :=
  register_def:
    forall t t' v v' ph m,
    Map_TID.MapsTo t v ph ->
    Copy v m v' ->
    Register ph t (REGISTER t' m) (Map_TID.add t' v' ph).

Definition phased := (phid * regmode) % type.

Inductive op : Type :=
  | PH_NEW : phid -> op
  | PH_SIGNAL : phid -> op
  | PH_DROP : phid -> op
  | SIGNAL_ALL : op
  | WAIT_ALL : op
  | ASYNC : list phased -> tid -> op.

Definition phasermap := Map_PHID.t phaser.

Inductive Async : phasermap -> tid -> list phased -> tid -> phasermap -> Prop :=
  | async_step:
    forall m t p r a t' m' ph ph',
    Async m t a t' m' ->
    Map_PHID.MapsTo p ph m' ->
    Register ph t (REGISTER t' r) ph' ->
    (* -------------- *)
    Async m t ((p,r)::a) t' (Map_PHID.add p ph' m')

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

Definition update (t:tid) (f:taskview -> phaser) (ph:phaser) :=
  match Map_TID.find t ph with
    | Some v => f v
    | None => ph
  end.

Definition apply (t:tid) (f:taskview -> taskview) (ph:phaser) : phaser :=
  update t (fun v => Map_TID.add t (f v) ph) ph.

Definition mapi (t:tid) (f:taskview->taskview) (m:phasermap) : phasermap :=
  Map_PHID.mapi (fun p ph => apply t f ph) m.

Inductive Reduce : phasermap -> tid -> op -> phasermap -> Prop :=
  | reduce_new:
    forall pm t p,
    ~ Map_PHID.In p pm ->
    (* --------------- *)
    Reduce pm t (PH_NEW p) (Map_PHID.add p (newPhaser t) pm)

  | reduce_signal:
    forall pm t p ph,
    Map_PHID.MapsTo p ph pm ->
    (* --------------- *)
    Reduce pm t (PH_SIGNAL p) (Map_PHID.add p (apply t signal ph) pm)

  | reduce_drop:
    forall pm t p ph,
    Map_PHID.MapsTo p ph pm ->
    (* --------------- *)
    Reduce pm t (PH_DROP p) (Map_PHID.add p (Map_TID.remove t ph) pm)

 | reduce_signal_all:
    forall m t,
    (* --------------- *)
    Reduce m t SIGNAL_ALL (mapi t signal m)

 | reduce_wait_all:
    forall m t,
    (* check if it can synchronize on every phaser *)
    (forall p ph, Map_PHID.MapsTo p ph m -> Sync ph t) ->
    (* --------------- *)
    Reduce m t WAIT_ALL (mapi t wait m).
