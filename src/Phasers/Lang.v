Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
Require Import HJ.Vars.
Require Export HJ.Phasers.Taskview.

Definition phaser := Map_TID.t taskview.

Definition Await (ph:phaser) (n:nat) : Prop :=
  forall t v,
  Map_TID.MapsTo t v ph ->
  SignalCap (mode v) ->
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
    WaitCap (mode v) ->
    Await ph (S (wait_phase v)) ->
    Sync ph t
  | sync_skip:
    forall t ph,
    ~ Map_TID.In t ph ->
    Sync ph t.

Module Phaser.

  Definition make (t:tid) := Map_TID.add t Taskview.make (Map_TID.empty taskview).

  Definition update (t:tid) (f:taskview -> taskview) (ph:phaser) : phaser :=
  match Map_TID.find t ph with
    | Some v => Map_TID.add t (f v) ph
    | None => ph
  end.

  Definition signal (t:tid) : phaser -> phaser := update t Taskview.signal.

  Definition wait (t:tid) : phaser -> phaser := update t Taskview.wait.

  Definition drop : tid -> phaser -> phaser := @Map_TID.remove taskview.

  Definition register (t:tid) (v:taskview) (ph:phaser) : phaser := 
  match Map_TID.find t ph with
    | Some _ => ph
    | None => Map_TID.add t v ph
  end.



  Module Semantics.
    Inductive op := SIGNAL | WAIT | DROP | REGISTER : taskview -> op.
    Inductive Reduction (ph:phaser) (t:tid) : op -> phaser -> Prop :=
    | reduction_signal:
      Map_TID.In t ph ->
      Reduction ph t SIGNAL (signal t ph)
    | reduction_wait:
      forall v,
      Map_TID.MapsTo t v ph ->
      wait_phase v < signal_phase v ->
      Sync ph t ->
      Reduction ph t WAIT (wait t ph)
    | reduction_drop:
      Map_TID.In t ph ->
      Reduction ph t DROP (drop t ph)
    | reduction_register:
      forall v,
      ~ Map_TID.In t ph ->
      Reduction ph t (REGISTER v) (register t v ph).
    
    Definition as_tv_op (o:op) :=
    match o with
    | SIGNAL => Some Taskview.Semantics.SIGNAL
    | WAIT =>  Some Taskview.Semantics.WAIT
    | _ => None
    end.
    
    Lemma as_tv_op_inv_signal:
      forall o,
      as_tv_op o = Some Taskview.Semantics.SIGNAL ->
      o = SIGNAL.
    Proof.
      intros.
      destruct o; auto; simpl in *; try (inversion H).
    Qed.

    Lemma as_tv_op_inv_wait:
      forall o,
      as_tv_op o = Some Taskview.Semantics.WAIT ->
      o = WAIT.
    Proof.
      intros.
      destruct o; auto; simpl in *; try (inversion H).
    Qed.

    Lemma ph_update_spec:
      forall t v f ph,
      Map_TID.MapsTo t v ph ->
      update t f ph = Map_TID.add t (f v) ph.
    Proof.
      intros.
      unfold update.
        remember (Map_TID.find _ _).
        symmetry in Heqo.
        destruct o as [v'|].
        {
          apply Map_TID_Facts.find_mapsto_iff in Heqo.
          assert (v' = v) by eauto using Map_TID_Facts.MapsTo_fun.
          subst; clear Heqo.
          trivial.
        }
        apply Map_TID_Facts.not_find_in_iff in Heqo.
        contradiction Heqo.
        eauto using  Map_TID_Extra.mapsto_to_in.
    Qed.

    Lemma ph_signal_spec:
      forall t v ph ph',
      Map_TID.MapsTo t v ph ->
      Reduction ph t SIGNAL ph' ->
      ph' = Map_TID.add t (Taskview.signal v) ph.
    Proof.
      intros.
      inversion H0.
      subst.
      unfold signal.
      auto using ph_update_spec.
    Qed.

    Lemma ph_wait_spec:
      forall t v ph ph',
      Map_TID.MapsTo t v ph ->
      Reduction ph t WAIT ph' ->
      ph' = Map_TID.add t (Taskview.wait v) ph.
    Proof.
      intros.
      inversion H0.
      subst.
      unfold wait.
      auto using ph_update_spec.
    Qed.

    Lemma ph_drop_spec:
      forall t ph ph',
      Map_TID.In t ph ->
      Reduction ph t DROP ph' ->
      ph' = Map_TID.remove t ph.
    Proof.
      intros.
      inversion H0; subst.
      unfold drop; auto.
    Qed.

    Lemma ph_register_spec:
      forall t v ph ph',
      ~ Map_TID.In t ph ->
      Reduction ph t (REGISTER v) ph' ->
      ph' = Map_TID.add t v ph.
    Proof.
      intros.
      inversion H0; subst.
      unfold register in *.
      rewrite Map_TID_Facts.not_find_in_iff in H.
      rewrite H in *.
      trivial.
    Qed.

    Lemma ph_tv_in:
      forall ph t o o' ph',
      Reduction ph t o ph' ->
      as_tv_op o = Some o' ->
      Map_TID.In t ph.
    Proof.
      intros.
      destruct o'.
      - apply as_tv_op_inv_signal in H0; subst.
        inversion H; auto.
      - apply as_tv_op_inv_wait in H0; subst.
        inversion H; auto.
        eauto using Map_TID_Extra.mapsto_to_in.
    Qed.

    Lemma ph_to_tv_correct:
      forall ph t o o' ph' v,
      Reduction ph t o ph' ->
      as_tv_op o = Some o' ->
      Map_TID.MapsTo t v ph ->
      ph' = Map_TID.add t (Semantics.eval o' v) ph.
    Proof.
      intros.
      destruct o'; simpl.
      - apply as_tv_op_inv_signal in H0; subst.
        auto using ph_signal_spec.
      - apply as_tv_op_inv_wait in H0; subst.
        auto using ph_wait_spec.
    Qed.

    Lemma ph_reduce_to_tv_reduce:
      forall ph t o o' ph' v,
      Reduction ph t o ph' ->
      as_tv_op o = Some o' ->
      Map_TID.MapsTo t v ph ->
      Semantics.Reduce v o' (Semantics.eval o' v).
    Proof.
      intros.
      destruct o'; simpl.
      - apply as_tv_op_inv_signal in H0; subst.
        apply Semantics.reduce_signal.
      - apply as_tv_op_inv_wait in H0; subst.
        inversion H.
        subst.
        apply Semantics.reduce_wait.
        assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun.
        subst.
        intuition.
    Qed.

 End Semantics.
End Phaser.

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
