Require Import HJ.Vars.
Require Import HJ.Phasers.Taskview.

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
