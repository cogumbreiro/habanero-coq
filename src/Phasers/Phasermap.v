Set Implicit Arguments.

Require Import HJ.Vars.
Require Import HJ.Phasers.Regmode.
Require Import HJ.Phasers.Phaser.
Require Import Coq.Lists.SetoidList.

(** This chapter defines a deadlock-free phaser language. A [phasermap] represents
all phasers available for a set of tasks. A phasermap is a map from phaser handles [phid]
into phasers. *)

Definition phasermap := Map_PHID.t phaser.

(** Function [make] creates an empty phasermap. *)

Definition make : phasermap := Map_PHID.empty phaser.

(**
  We now define phasermap operations, first with a pre-condition and
  then a function that executes the operation.
  *)

Record Op := mk_op {
  can_run: tid -> phasermap -> Prop;
  run: tid -> phasermap -> phasermap
}.

(**
  Function [new_phaser] places a new empty phaser in the phasermap.
  The pre-condition is that [p] is not in phasermap [m]. *)

Inductive PhNewPre p (t:tid) (m:phasermap) : Prop :=
  ph_new_pre:
    ~ Map_PHID.In p m ->
    PhNewPre p t m.

Definition ph_new (p:phid) (t:tid) : phasermap -> phasermap := Map_PHID.add p (Phaser.make t).

Definition ph_new_op p := mk_op (PhNewPre p) (ph_new p).

(**
  Function [update] mutates the phaser associated to [p] by applying
  parameter [f] to the phaser.
 *)

Definition update p (f:phaser -> phaser) m : phasermap := 
match Map_PHID.find p m with
| Some ph => Map_PHID.add p (f ph) m
| None => m
end.

(**
  Signal applies the phaser-signal to the phaser associated with [p].
  The pre-condition is that [p] must be in the phasermap and
  we must meet the pre-conditions of the phaser-signal.
  *)

Inductive PhSignalPre p t m : Prop :=
  ph_signal_pre:
    forall ph,
    Map_PHID.MapsTo p ph m ->
    SignalPre t ph ->
    PhSignalPre p t m.

Definition ph_signal p t := update p (Phaser.signal t).

Definition ph_signal_op p := mk_op (PhSignalPre p) (ph_signal p).

(** Droping a phaser has a similar implementation and pre-conditions. *)

Inductive PhDropPre p t m : Prop :=
  ph_drop_pre:
    forall ph,
    Map_PHID.MapsTo p ph m ->
    DropPre t ph ->
    PhDropPre p t m.

Definition ph_drop p t := update p (Phaser.drop t).

Definition ph_drop_op p := mk_op (PhDropPre p) (ph_drop p).

(**
  We now introduce functions that act on all phasers the task is regitered  with.
  Function [foreach] updates all phasers in the phasermap by applying function [f].
  *)

Definition foreach (f:phaser -> phaser) : phasermap -> phasermap :=
Map_PHID.mapi (fun _ ph => f ph).

(** Function [signal_all] lets task [t] perform a [Phaser.signal] on all phasers
    it is registered with. There are no pre-conditions to this operation. *)

Definition signal_all (t:tid) := foreach (Phaser.signal t).

Definition signal_all_op := mk_op (fun _ _ => True) signal_all.

(**
  Wait-all invokes a wait on every phaser the task is registered with.
  The pre-condition of wait-all is the pre-condition of each phaser the
  task is registered with. *)

Inductive WaitAllPre t m : Prop :=
  wait_all_pre:
    (forall p ph, Map_PHID.MapsTo p ph m -> Map_TID.In t ph -> WaitPre t ph) ->
    WaitAllPre t m.

Definition wait_all (t:tid) := foreach (Phaser.wait t).

Definition wait_all_op := mk_op WaitAllPre wait_all.

(**
  Function [drop_all] deregisters task [t] from all phasers in the phasermap; it
  has no pre-conditions.
  *)

Definition drop_all (t:tid) := foreach (Phaser.drop t).

Definition drop_all_op := mk_op (fun _ _ => True) drop_all.

(**
  Finally, we define async. To be able to spawn a task we must ensure
  that the spawned task name is unknown in all phasers, so we need to
  define a task membership for phasermaps.
  Predicate [In t m] holds when task [t] is registered in a phaser of [m]. *)

Inductive In (t:tid) (pm:phasermap) : Prop :=
  in_def:
    forall p ph,
    Map_PHID.MapsTo p ph pm ->
    Map_TID.In t ph ->
    In t pm.

(** The parameter of a phased async is list of pairs, each of which
  consists of a phaser name and a registration  mode. *)

Record phased := mk_phased {
  get_args : Map_PHID.t regmode;
  get_new_task : tid
}.

(** 
  Async phased register a new task in a list of [phased].
  Function [async_1] registers task [t] with phaser named by [p] according
  to mode [r].
  *)

Definition async_1 (ps:phased) t p ph : phaser :=
match Map_PHID.find p (get_args ps) with
| Some r => register (mk_registry (get_new_task ps) r) t ph
| _ => ph
end.

Definition async ps t : phasermap -> phasermap := Map_PHID.mapi (async_1 ps t).

(**
  Predicate [PhasedPre] ensures that task [t] can register task [t']
  using the phased object [ps].
   *)

Inductive PhasedPre (m:phasermap) (t:tid) (ps:phased) (p:phid) (ph:phaser) : Prop := 
  phased_pre:
    forall r,
    Map_PHID.MapsTo p r (get_args ps) ->
    Map_TID.In t ph ->
    RegisterPre (mk_registry (get_new_task ps) r) t ph ->
    PhasedPre m t ps p ph.

(**
  The pre-condition of executing an async are three:
  (i) all phased pairs in [ps] must meet the preconditions of [PhasedPre],
  (ii) the phaser names in [ps] cannot be appear multiple times in [ps],
  (iii) the spawned task [t'] cannot be known in the phasermap.
  *)

Inductive AsyncPre (ps:phased) t m : Prop :=
  async_pre:
    (forall p ph, Map_PHID.MapsTo p ph m -> PhasedPre m t ps p ph) ->
    ~ In (get_new_task ps) m -> 
    AsyncPre ps t m.

Definition async_op (ps:phased) := mk_op (AsyncPre ps) (async ps).

(**
  We are now ready to define the closed set of operations on phasermaps.
 *)

Inductive op : Type :=
| PH_NEW : phid -> op
| PH_SIGNAL : phid -> op
| PH_DROP : phid -> op
| SIGNAL_ALL
| WAIT_ALL
| DROP_ALL
| ASYNC : phased -> op.
  
(** Function [get_impl] yields the [Op] object. *)

Definition get_impl o :=
match o with
| PH_NEW p => ph_new_op p
| PH_SIGNAL p => ph_signal_op p
| PH_DROP p => ph_drop_op p
| SIGNAL_ALL => signal_all_op
| WAIT_ALL => wait_all_op
| DROP_ALL => drop_all_op
| ASYNC ps => async_op ps
end.

(** In closing, we define the [Reduces] relation. *)

Inductive Reduces m t o : phasermap -> Prop :=
  reduces:
    can_run (get_impl o) t m ->
    Reduces m t o (run (get_impl o) t m).

(* begin hide *)
Section Facts.

  Lemma pm_update_rw:
    forall p f ph m,
    Map_PHID.MapsTo p ph m ->
    update p f m = Map_PHID.add p (f ph) m.
  Proof.
    intros.
    unfold update.
    remember (Map_PHID.find _ _) as o.
    symmetry in Heqo.
    destruct o.
    - rewrite <- Map_PHID_Facts.find_mapsto_iff in Heqo.
      assert (p0 = ph) by eauto using Map_PHID_Facts.MapsTo_fun.
      subst.
      trivial.
    - rewrite <- Map_PHID_Facts.not_find_in_iff in Heqo.
      contradiction Heqo.
      eauto using Map_PHID_Extra.mapsto_to_in.
  Qed.

  Lemma pm_ph_signal_rw:
    forall p t ph m,
    Map_PHID.MapsTo p ph m ->
    ph_signal p t m = Map_PHID.add p (Phaser.signal t ph) m.
  Proof.
    intros.
    unfold ph_signal.
    rewrite pm_update_rw with (ph:=ph); auto.
  Qed.

  Lemma pm_ph_drop_rw:
    forall p t ph m,
    Map_PHID.MapsTo p ph m ->
    ph_drop p t m = Map_PHID.add p (Phaser.drop t ph) m.
  Proof.
    intros.
    unfold ph_drop.
    rewrite pm_update_rw with (ph:=ph); auto.
  Qed.

  Lemma pm_foreach_mapsto_rw:
    forall p ph f m,
    Map_PHID.MapsTo p ph (foreach f m) <->
    exists ph', ph = f ph' /\ Map_PHID.MapsTo p ph' m.
  Proof.
    intros.
    unfold foreach in *.
    rewrite Map_PHID_Facts.mapi_mapsto_iff; auto.
    split; eauto.
  Qed.

  Lemma async_simpl_notin:
    forall p (ps:phased) ph t,
    ~ Map_PHID.In p (get_args ps) ->
    async_1 ps t p ph = ph.
  Proof.
    intros.
    unfold async_1.
    destruct (Map_PHID_Extra.find_rw p (get_args ps)) as [(R,?)|(r,(R,?))].
    - rewrite R; clear R.
      trivial.
    - contradiction H.
      eauto using Map_PHID_Extra.mapsto_to_in.
  Qed.

  Lemma pm_async_1_rw:
    forall ps t p ph,
      { exists r, Map_PHID.MapsTo p r (get_args ps) /\ async_1 ps t p ph = register (mk_registry (get_new_task ps) r) t ph }
      +
      { async_1 ps t p ph = ph /\ ~ Map_PHID.In p (get_args ps)}.
  Proof.
    intros.
    unfold async_1.
    destruct (Map_PHID_Extra.find_rw p (get_args ps)).
    - right.
      destruct a as (R,?).
      rewrite R.
      intuition.
    - left.
      destruct e as (r,(R,?)).
      rewrite R.
      eauto.
  Qed.

  Lemma pm_async_1_mapsto_neq:
    forall t' v ps t p ph,
    t' <> (get_new_task ps) ->
    Map_TID.MapsTo t' v (async_1 ps t p ph) ->
    Map_TID.MapsTo t' v ph.
  Proof.
    intros.
    unfold async_1 in *.
    destruct (Map_PHID_Extra.find_rw p (get_args ps)) as [(R,?)|(r,(R,?))]. {
      rewrite R in *; clear R.
      assumption.
    }
    rewrite R in *; clear R.
    eauto using ph_register_mapsto_neq.
  Qed.

  Lemma pm_async_1_mapsto_eq:
    forall v ps t p ph r,
    Map_TID.In t ph ->
    Map_PHID.MapsTo p r (get_args ps) ->
    Map_TID.MapsTo (get_new_task ps) v (async_1 ps t p ph) ->
    exists v', Map_TID.MapsTo t v' ph /\ v = Taskview.set_mode v' r.
  Proof.
    intros.
    unfold async_1 in *.
    destruct (Map_PHID_Extra.find_rw p (get_args ps)) as [(R,?)|(r',(R,?))]. {
      (* absurd *)
      rewrite R in *; clear R.
      contradiction H2.
      eauto using Map_PHID_Extra.mapsto_to_in.
    }
    rewrite R in *; clear R.
    assert (r' = r) by eauto using Map_PHID_Facts.MapsTo_fun; subst; clear H2.
    eauto using ph_register_mapsto_eq.
  Qed.

  Lemma pm_async_1_mapsto:
    forall p ph ps t' t v,
    Map_TID.MapsTo t' v (async_1 ps t p ph) ->
    Map_TID.MapsTo t' v ph \/
    (exists v' r, Map_TID.MapsTo t v' ph /\ Map_PHID.MapsTo p r (get_args ps) /\
    v = Taskview.set_mode v' r).
  Proof.
    intros.
    destruct (pm_async_1_rw ps t p ph) as [(r,(i,R))|(R1,R2)]. {
      rewrite R in *; clear R.
      apply ph_register_inv_mapsto in H.
      destruct H; auto.
      destruct H as (?, (v', (mt2, ?))).
      subst.
      right.
      eauto.
    }
    left.
    rewrite R1 in *; clear R1.
    auto.
  Qed.

  Lemma pm_async_mapsto_rw:
    forall p ph ps t m,
    Map_PHID.MapsTo p ph (async ps t m) <->
    exists ph', ph = async_1 ps t p ph' /\ Map_PHID.MapsTo p ph' m.
  Proof.
    intros.
    unfold async in *.
    rewrite Map_PHID_Facts.mapi_mapsto_iff; auto.
    split; eauto.
    intros.
    subst.
    trivial.
  Qed.

  Lemma async_notina_mapsto:
    forall p ps m t ph,
    ~ Map_PHID.In p (get_args ps) ->
    Map_PHID.MapsTo p ph m ->
    Map_PHID.MapsTo p ph (async ps t m).
  Proof.
    intros.
    apply pm_async_mapsto_rw.
    exists ph.
    intuition.
    symmetry.
    eauto using async_simpl_notin.
  Qed.

  Lemma async_notina_mapsto_rtl:
    forall p ps m t ph,
    ~ Map_PHID.In p (get_args ps) ->
    Map_PHID.MapsTo p ph (async ps t m) ->
    Map_PHID.MapsTo p ph m.
  Proof.
    intros.
    apply pm_async_mapsto_rw in H0.
    destruct H0 as (ph', (R, mt)).
    rewrite R in *.
    apply async_simpl_notin with (ph:=ph') (t:=t) in H.
    rewrite H.
    assumption.
  Qed.

  Lemma ph_new_impl_mapsto:
    forall p t pm,
    Map_PHID.MapsTo p (Phaser.make t) (ph_new p t pm).
  Proof.
    intros.
    unfold ph_new.
    auto using Map_PHID.add_1.
  Qed.
End Facts.

(* end hide *)
