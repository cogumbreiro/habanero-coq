Require Import HJ.Vars.
Require Import HJ.Phasers.Taskview.

Section Defs.
Import HJ.Vars.Map_TID.

Definition phaser := t taskview.

Definition Await (ph:phaser) (n:nat) : Prop :=
  forall t v,
  MapsTo t v ph ->
  SignalCap (mode v) ->
  v.(signal_phase) >= n.

Inductive Sync : phaser -> tid -> Prop :=
  | sync_so:
    forall t v ph,
    MapsTo t v ph ->
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

Definition make (t:tid) := add t Taskview.make (Map_TID.empty taskview).

Definition update (t:tid) (f:taskview -> taskview) (ph:phaser) : phaser :=
  match find t ph with
  | Some v => add t (f v) ph
  | None => ph
  end.

Definition signal (t:tid) : phaser -> phaser := update t Taskview.signal.

Definition wait (t:tid) : phaser -> phaser := update t Taskview.wait.

Definition drop : tid -> phaser -> phaser := @remove taskview.

Record registry := mk_registry {
  get_task: tid;
  get_mode: regmode
}.

Definition register (t:tid) (r:registry) (ph:phaser) : phaser := 
  match find t ph with
  | Some v => add (get_task r) (set_mode v (get_mode r)) ph
  | None => ph
  end.

End Defs.

Module Semantics.

  Import Taskview.Notations.
  Open Scope reg_scope.

  Inductive op :=
    | SIGNAL
    | WAIT
    | DROP
    | REGISTER : registry -> op.


  Inductive Reduces (ph:phaser) (t:tid) : op -> phaser -> Prop :=

  | reduces_signal:
    Map_TID.In t ph ->
    Reduces ph t SIGNAL (signal t ph)

  | reduces_wait:
    forall v,
    Map_TID.MapsTo t v ph ->
    wait_phase v < signal_phase v ->
    Sync ph t ->
    Reduces ph t WAIT (wait t ph)

  | reduces_drop:
    Map_TID.In t ph ->
    Reduces ph t DROP (drop t ph)

  | reduces_register:
    forall v r,
    ~ Map_TID.In (get_task r) ph ->
    Map_TID.MapsTo t v ph ->
    get_mode r <= mode v ->
    Reduces ph t (REGISTER r) (register t r ph).
  
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
      eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Lemma ph_signal_spec:
    forall t v ph ph',
    Map_TID.MapsTo t v ph ->
    Reduces ph t SIGNAL ph' ->
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
    Reduces ph t WAIT ph' ->
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
    Reduces ph t DROP ph' ->
    ph' = Map_TID.remove t ph.
  Proof.
    intros.
    inversion H0; subst.
    unfold drop; auto.
  Qed.

  Lemma ph_register_spec:
    forall t v r ph ph',
    Map_TID.MapsTo t v ph ->
    Reduces ph t (REGISTER r) ph' ->
    ph' = Map_TID.add (get_task r) (set_mode v (get_mode r)) ph.
  Proof.
    intros.
    inversion H0; subst.
    unfold register in *.
    remember (Map_TID.find _ _ ).
    symmetry in Heqo.
    destruct o.
    - rewrite Map_TID_Facts.find_mapsto_iff in *.
      assert (v0 = v). {
        rewrite H in *.
        inversion H3; auto.
      }
      assert (t0 = v). {
        rewrite H in *.
        inversion Heqo; auto.
      }
      subst.
      trivial.
    - apply Map_TID_Extra.mapsto_to_in in H3.
      apply Map_TID_Facts.not_find_in_iff in Heqo.
      contradiction.
  Qed.

  Lemma ph_in:
    forall ph t o ph',
    Reduces ph t o ph' ->
    Map_TID.In t ph.
  Proof.
    intros.
    inversion H; eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Lemma ph_to_tv_correct:
    forall ph t o o' ph' v,
    Reduces ph t o ph' ->
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
    Reduces ph t o ph' ->
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
