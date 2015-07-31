Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
Require Import HJ.Vars.

Inductive regmode : Set:=
  | SIGNAL_ONLY : regmode
  | WAIT_ONLY : regmode
  | SIGNAL_WAIT : regmode.


Inductive r_le : regmode -> regmode -> Prop :=
  | r_le_so:
    r_le SIGNAL_ONLY SIGNAL_ONLY
  | r_le_wo:
    r_le WAIT_ONLY WAIT_ONLY
  | r_le_sw:
    forall m,
    r_le m SIGNAL_WAIT.

Record taskview := TV {
  signal_phase: nat;
  wait_phase: nat;
  mode: regmode
}.

Inductive SignalPhase: taskview -> nat -> Prop :=
  | signal_phase_tv:
    forall v,
    SignalPhase v (signal_phase v).

Inductive WaitPhase : taskview -> nat -> Prop :=
  | wait_phase_tv:
    forall v,
    WaitPhase v (wait_phase v).


Lemma get_wait_phase:
  forall (v:taskview),
  exists n, (WaitPhase v n).
Proof.
  intros.
  exists (v.(wait_phase)).
  apply wait_phase_tv.
Qed.

Lemma wait_phase_spec_1:
  forall v,
  WaitPhase v (wait_phase v).
Proof.
  intros.
  apply wait_phase_tv.
Qed.

Lemma wait_phase_spec_2:
  forall v n,
  WaitPhase v n ->
  n = wait_phase v.
Proof.
  intros.
  inversion H.
  auto.
Qed.

Lemma signal_phase_spec_1:
  forall v s,
  signal_phase v = s ->
  SignalPhase v s.
Proof.
  intros.
  subst.
  apply signal_phase_tv.
Qed.

Let inc_signal (v:taskview) := TV (v.(signal_phase) + 1) v.(wait_phase) v.(mode).

Let inc_wait (v:taskview) := TV v.(signal_phase) (v.(wait_phase) + 1) v.(mode).

Let set_mode (v:taskview) (m:regmode) := TV v.(signal_phase) v.(wait_phase) m.

Definition signal (v:taskview) :=
  match v.(mode) with
    | SIGNAL_ONLY => v
    | _ => if eq_nat_dec v.(signal_phase) v.(wait_phase) then (inc_signal v) else v
  end.

Definition wait (v:taskview) := inc_wait v.

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

Inductive Copy : taskview -> regmode -> taskview -> Prop :=
  | copy_def:
    forall v m,
    r_le m v.(mode) -> (* m <= v.(mode) *)
    Copy v m (set_mode v m).

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

Definition newPhaser (t:tid) := Map_TID.add t (TV 0 0 SIGNAL_WAIT) (Map_TID.empty taskview).

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

Section REGISTERED.
Variable pm:phasermap.

Definition registered_pm t :=
  Map_PHID_Extra.filter
  (fun (p:phid) (ph:phaser) =>
    if Map_TID_Facts.In_dec ph t then true else false)
  pm.

Definition get_registered t := Map_PHID_Extra.keys (registered_pm t).

Lemma get_registered_spec :
  forall (t:tid),
  Registered pm t (get_registered t).
Proof.
  intros.
  unfold get_registered.
  unfold registered_pm.
  apply registered_def.
  - apply Map_PHID_Extra.keys_nodup. intuition.
  - unfold TaskInMany.
    apply Forall_forall.
    intros.
    rewrite <- Map_PHID_Extra.keys_spec in H. {
      apply Map_PHID_Extra.in_to_mapsto in H.
      destruct H as (ph, H).
      rewrite Map_PHID_Extra.filter_spec in H. {
        destruct H.
        destruct (Map_TID_Facts.In_dec ph t).
        + apply task_in_def with (ph:=ph); repeat auto.
        + inversion H0. (* absurd *)
      }
      intuition.
    }
    intuition.
  - intros.
    rewrite <- Map_PHID_Extra.keys_spec. {
      unfold TaskIn in *.
      destruct H as (ph, (Hmt, Hin)).
      apply Map_PHID_Extra.mapsto_to_in with (e:=ph).
      rewrite Map_PHID_Extra.filter_spec. {
        intuition.
        destruct (Map_TID_Facts.In_dec ph t).
        - auto.
        - intuition.
      }
      intuition.
    }
    intuition.
Qed.

Lemma get_registered_spec_alt :
  forall (t:tid),
  exists ps, Registered pm t ps.
Proof.
  intros.
  exists (get_registered t).
  apply get_registered_spec.
Qed.
End REGISTERED.
