Require Import HJ.Vars.
Require Import HJ.Phasers.Taskview.
Import HJ.Vars.Map_TID.
Import HJ.Vars.Map_TID_Facts.
Import HJ.Vars.Map_TID_Extra.

Definition phaser := Map_TID.t taskview.

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
    MapsTo t v ph ->
    WaitCap (mode v) ->
    Await ph (S (wait_phase v)) ->
    Sync ph t
  | sync_skip:
    forall t ph,
    ~ In t ph ->
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

Module Semantics.

  Import Taskview.Notations.
  Open Scope reg_scope.

  Inductive op :=
    | SIGNAL
    | WAIT
    | DROP
    | REGISTER : registry -> op.


  Inductive Reduction (ph:phaser) (t:tid) : op -> phaser -> Prop :=

  | reduction_signal:
    In t ph ->
    Reduction ph t SIGNAL (signal t ph)

  | reduction_wait:
    forall v,
    MapsTo t v ph ->
    wait_phase v < signal_phase v ->
    Sync ph t ->
    Reduction ph t WAIT (wait t ph)

  | reduction_drop:
    In t ph ->
    Reduction ph t DROP (drop t ph)

  | reduction_register:
    forall v r,
    ~ In (get_task r) ph ->
    MapsTo t v ph ->
    get_mode r <= mode v ->
    Reduction ph t (REGISTER r) (register t r ph).
  
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
    MapsTo t v ph ->
    update t f ph = add t (f v) ph.
  Proof.
    intros.
    unfold update.
      remember (Map_TID.find _ _).
      symmetry in Heqo.
      destruct o as [v'|].
      {
        apply find_mapsto_iff in Heqo.
        assert (v' = v) by eauto using MapsTo_fun.
        subst; clear Heqo.
        trivial.
      }
      apply not_find_in_iff in Heqo.
      contradiction Heqo.
      eauto using  mapsto_to_in.
  Qed.

  Lemma ph_signal_spec:
    forall t v ph ph',
    Map_TID.MapsTo t v ph ->
    Reduction ph t SIGNAL ph' ->
    ph' = add t (Taskview.signal v) ph.
  Proof.
    intros.
    inversion H0.
    subst.
    unfold signal.
    auto using ph_update_spec.
  Qed.

  Lemma ph_wait_spec:
    forall t v ph ph',
    MapsTo t v ph ->
    Reduction ph t WAIT ph' ->
    ph' = add t (Taskview.wait v) ph.
  Proof.
    intros.
    inversion H0.
    subst.
    unfold wait.
    auto using ph_update_spec.
  Qed.

  Lemma ph_drop_spec:
    forall t ph ph',
    In t ph ->
    Reduction ph t DROP ph' ->
    ph' = remove t ph.
  Proof.
    intros.
    inversion H0; subst.
    unfold drop; auto.
  Qed.

  Lemma ph_register_spec:
    forall t v r ph ph',
    MapsTo t v ph ->
    Reduction ph t (REGISTER r) ph' ->
    ph' = add (get_task r) (set_mode v (get_mode r)) ph.
  Proof.
    intros.
    inversion H0; subst.
    unfold register in *.
    remember (find _ _ ).
    symmetry in Heqo.
    destruct o.
    - rewrite find_mapsto_iff in *.
      assert (v0 = v). {
        rewrite H in *.
        inversion H3; auto.
      }
      assert (t1 = v). {
        rewrite H in *.
        inversion Heqo; auto.
      }
      subst.
      trivial.
    - apply mapsto_to_in in H3.
      apply not_find_in_iff in Heqo.
      contradiction.
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
