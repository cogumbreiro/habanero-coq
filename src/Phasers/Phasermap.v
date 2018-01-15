Set Implicit Arguments.
Require Import HJ.Tid.
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

Definition signal_all (t:tid) := foreach (Phaser.try_signal t).

Definition signal_all_op := mk_op (fun _ _ => True) signal_all.

(**
  Wait-all invokes a wait on every phaser the task is registered with.
  The pre-condition of wait-all is the pre-condition of each phaser the
  task is registered with. *)

Inductive WaitAllPre t m : Prop :=
  wait_all_pre:
    (forall p ph, Map_PHID.MapsTo p ph m -> Map_TID.In t ph -> TryWaitPre t ph) ->
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

Inductive Nonempty (pm:phasermap) : Prop :=
| nonempty_def:
  forall x,
  In x pm ->
  Nonempty pm.

Definition Empty (pm:phasermap) : Prop := forall x, ~ In x pm.

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

Inductive PhasedPre (ps:phased) (t:tid) pm : Prop := 
  phased_pre_def:
    (forall p m,
      Map_PHID.MapsTo p m (get_args ps) -> 
      exists ph, Map_PHID.MapsTo p ph pm /\ RegisterPre (mk_registry (get_new_task ps) m) t ph) ->
    PhasedPre ps t pm.

(**
  The pre-condition of executing an async are three:
  (i) all phased pairs in [ps] must meet the preconditions of [PhasedPre],
  (ii) the spawned task [t'] cannot be known in the phasermap.
  *)

Inductive AsyncPre (ps:phased) t m : Prop :=
  async_pre:
    PhasedPre ps t m ->
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

Module Trace.
  Definition t := (list (tid * op)) % type.

  Inductive ReducesN: phasermap -> t -> Prop :=
  | reduces_n_nil:
    ReducesN make nil
  | reduces_n_cons:
    forall t l o pm pm',
    ReducesN pm l ->
    Reduces pm t o pm' ->
    ReducesN pm' ((t,o)::l).
End Trace.

Section Facts.

  Let update_rw:
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

  Lemma ph_signal_rw:
    forall p t ph m,
    Map_PHID.MapsTo p ph m ->
    ph_signal p t m = Map_PHID.add p (Phaser.signal t ph) m.
  Proof.
    intros.
    unfold ph_signal.
    rewrite update_rw with (ph:=ph); auto.
  Qed.

  Lemma ph_drop_rw:
    forall p t ph m,
    Map_PHID.MapsTo p ph m ->
    ph_drop p t m = Map_PHID.add p (Phaser.drop t ph) m.
  Proof.
    intros.
    unfold ph_drop.
    rewrite update_rw with (ph:=ph); auto.
  Qed.

  Lemma foreach_mapsto_rw:
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

  Lemma async_1_rw:
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

  Lemma async_1_mapsto_neq:
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
    eauto using register_mapsto_neq.
  Qed.

  Lemma async_1_mapsto_eq:
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
    eauto using register_mapsto_eq.
  Qed.

  Lemma async_1_mapsto:
    forall p ph ps t' t v,
    Map_TID.MapsTo t' v (async_1 ps t p ph) ->
    Map_TID.MapsTo t' v ph \/
    (exists v' r, Map_TID.MapsTo t v' ph /\ Map_PHID.MapsTo p r (get_args ps) /\
    v = Taskview.set_mode v' r).
  Proof.
    intros.
    destruct (async_1_rw ps t p ph) as [(r,(i,R))|(R1,R2)]. {
      rewrite R in *; clear R.
      apply register_inv_mapsto in H.
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

  Lemma async_mapsto_rw:
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
    apply async_mapsto_rw.
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
    apply async_mapsto_rw in H0.
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

  Lemma async_pre_to_in_ph:
    forall ps t pm r ph p,
    AsyncPre ps t pm ->
    Map_PHID.MapsTo p r (get_args ps) ->
    Map_PHID.MapsTo p ph pm ->
    Map_TID.In t ph.
  Proof.
    intros.
    inversion H as [Hx].
    inversion Hx.
    specialize (H3 _ _ H0).
    destruct H3 as (ph', (?, Hr)).
    assert (ph' = ph) by eauto using Map_PHID_Facts.MapsTo_fun; subst.
    eauto using Phaser.register_pre_to_in.
  Qed.
End Facts.

Section Decidability.
  Ltac handle_not := right; unfold not; intros N; inversion N; contradiction; fail.
  Lemma ph_new_pre_dec p t pm:
    { PhNewPre p t pm } + { ~ PhNewPre p t pm }.
  Proof.
    destruct (Map_PHID_Facts.In_dec pm p); try handle_not.
    auto using ph_new_pre.
  Defined.
  
  Lemma ph_signal_pre_dec p t pm:
    { PhSignalPre p t pm } + { ~ PhSignalPre p t pm }.
  Proof.
    destruct (Map_PHID_Extra.lookup_dec phid_eq_rw p pm) as [(ph,mt)|(_,?)]. {
      destruct (signal_pre t ph). {
        eauto using ph_signal_pre.
      }
      right.
      unfold not; intros N.
      inversion N.
      assert (ph0 = ph) by eauto using Map_PHID_Facts.MapsTo_fun; subst.
      contradiction.
    }
    right.
    unfold not; intros N.
    inversion N.
    apply Map_PHID_Extra.mapsto_to_in in H.
    contradiction.
  Defined.

  Lemma ph_drop_pre_dec p t pm:
    { PhDropPre p t pm } + { ~ PhDropPre p t pm }.
  Proof.
    destruct (Map_PHID_Extra.lookup_dec phid_eq_rw p pm) as [(ph,mt)|(_,?)]. {
      destruct (drop_pre t ph). {
        eauto using ph_drop_pre.
      }
      right.
      unfold not; intros N.
      inversion N.
      assert (ph0 = ph) by eauto using Map_PHID_Facts.MapsTo_fun; subst.
      contradiction.
    }
    right.
    unfold not; intros N.
    inversion N.
    apply Map_PHID_Extra.mapsto_to_in in H.
    contradiction.
  Defined.

  Definition phased_pre_dec ps t (pm:phasermap):
    { PhasedPre ps t pm } + { ~ PhasedPre ps t pm }.
  Proof.
    remember (forallb (fun kv => 
      match Map_PHID.find (fst kv) pm with
      | Some ph =>
        if register_pre {| get_task := get_new_task ps; get_mode := (snd kv) |} t ph
        then true else false
      | _ => false
      end
    ) (Map_PHID.elements (get_args ps))).
    symmetry in Heqb.
    destruct b. {
      left.
      apply phased_pre_def.
      intros.
      rewrite forallb_forall in *.
      specialize Heqb with (p, m).
      rewrite <- Map_PHID_Extra.maps_to_iff_in_elements in Heqb; auto using phid_eq_rw.
      specialize (Heqb H).
      simpl in *.
      destruct (Map_PHID_Extra.find_rw p pm) as [(R,N)|(ph,(R,?))]; rewrite R in *; clear R. {
        inversion Heqb.
      }
      destruct (register_pre {| get_task := get_new_task ps; get_mode := m |} t ph). {
        eauto.
      }
      inversion Heqb.
    }
    right.
    rewrite List.forallb_existsb in Heqb.
    rewrite Bool.negb_false_iff in *.
    apply existsb_exists in Heqb.
    unfold not; intros N.
    destruct Heqb as ((p,m),(Hi,Hx)).
    apply Map_PHID_Extra.maps_to_iff_in_elements in Hi; auto using phid_eq_rw.
    rewrite Bool.negb_true_iff in *.
    simpl in *.
    inversion N.
    specialize (H _ _ Hi).
    destruct H as (ph, (mt, Hr)).
    destruct (Map_PHID_Extra.find_rw p pm) as [(R,N1)|(ph',(R,?))]; rewrite R in *; clear R. {
      contradiction N1.
      eauto using Map_PHID_Extra.mapsto_to_in.
    }
    destruct (register_pre {| get_task := get_new_task ps; get_mode := m |} t ph'). {
      inversion Hx.
    }
    assert (ph' = ph) by eauto using Map_PHID_Facts.MapsTo_fun; subst.
    contradiction.
  Defined.

  Definition in_dec t pm:
    { In t pm } + { ~ In t pm }.
  Proof.
    destruct (Map_PHID_Extra.pred_choice pm (fun p ph =>
      if Map_TID_Extra.in_dec tid_eq_rw t ph then true else false
    )); auto with *. {
      left.
      destruct e as (p,(ph, (?,Hx))).
      destruct (Map_TID_Extra.in_dec tid_eq_rw t ph). {
        eauto using in_def.
      }
      inversion Hx.
    }
    right.
    unfold not; intros N.
    inversion N; subst; clear N.
    specialize (e _ _ H).
    destruct (Map_TID_Extra.in_dec tid_eq_rw t ph). {
      inversion e.
    }
    contradiction.
  Defined.

  Lemma async_pre_dec ps t pm: 
    { AsyncPre ps t pm } + { ~ AsyncPre ps t pm }.
  Proof.
    destruct (in_dec (get_new_task ps) pm). {
      right.
      unfold not; intros N.
      inversion N.
      contradiction.
    }
    destruct (phased_pre_dec ps t pm). {
      auto using async_pre.
    }
    right.
    unfold not; intros N.
    inversion N.
    contradiction.
  Defined.
End Decidability.

Section InInv.
  Let in_add_inv:
    forall x p ph s,
    In x (Map_PHID.add p ph s) ->
    Map_TID.In x ph \/ In x s.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_PHID_Facts.add_mapsto_iff in H0.
    destruct H0 as [(?,?)|(?,?)]. {
      subst.
      auto.
    }
    eauto using in_def.
  Qed.

  Let in_make_inv:
    forall x y,
    Map_TID.In y (Phaser.make x) ->
    y = x.
  Proof.
    intros.
    apply Map_TID_Extra.in_to_mapsto in H.
    destruct H as (?, mt).
    apply make_mapsto in mt.
    destruct mt; auto.
  Qed.

  Let ph_in_signal_inv:
    forall x y ph,
    Map_TID.In x (signal y ph) ->
    Map_TID.In x ph.
  Proof.
    unfold signal, Phaser.update; intros.
    destruct (Map_TID_Extra.find_rw y ph) as [(R,?)|(?,(R,?))];
    rewrite R in *; clear R. {
      assumption.
    }
    apply Map_TID_Extra.F.add_in_iff in H.
    destruct H. {
      subst.
      eauto using Map_TID_Extra.mapsto_to_in.
    }
    assumption.
  Qed.

  Let ph_in_try_signal_inv:
    forall x y ph,
    Map_TID.In x (try_signal y ph) ->
    Map_TID.In x ph.
  Proof.
    unfold try_signal, Phaser.update; intros.
    destruct (Map_TID_Extra.find_rw y ph) as [(R,?)|(?,(R,?))];
    rewrite R in *; clear R. {
      assumption.
    }
    apply Map_TID_Extra.F.add_in_iff in H.
    destruct H. {
      subst.
      eauto using Map_TID_Extra.mapsto_to_in.
    }
    assumption.
  Qed.

  Let ph_in_wait_inv:
    forall x y ph,
    Map_TID.In x (wait y ph) ->
    Map_TID.In x ph.
  Proof.
    unfold wait, Phaser.update; intros.
    destruct (Map_TID_Extra.find_rw y ph) as [(R,?)|(?,(R,?))];
    rewrite R in *; clear R. {
      assumption.
    }
    apply Map_TID_Facts.add_in_iff in H.
    destruct H. {
      subst.
      eauto using Map_TID_Extra.mapsto_to_in.
    }
    assumption.
  Qed.

  Let ph_in_drop_inv:
    forall x y ph,
    Map_TID.In x (drop y ph) ->
    y <> x /\ Map_TID.In x ph.
  Proof.
    unfold drop, Phaser.update; intros.
    apply Map_TID_Facts.remove_in_iff in H.
    assumption.
  Qed.

  Let ph_in_async_1_inv:
    forall x y p ph h,
    Map_TID.In y (async_1 p x h ph) ->
    get_new_task p = y \/ Map_TID.In y ph.
  Proof.
    unfold async_1; intros.
    destruct (Map_PHID_Extra.find_rw h (get_args p)) as [(R,?)|(?,(R,?))];
    rewrite R in *; clear R. {
      auto.
    }
    unfold register in *.
    destruct (Map_TID_Extra.find_rw x ph) as [(R,?)|(?,(R,?))];
    rewrite R in *; clear R. {
      auto.
    }
    simpl in *.
    apply Map_TID_Facts.add_in_iff in H.
    auto.
  Qed.

  Let in_signal_inv:
    forall x y p s,
    In x (ph_signal p y s) ->
    In x s.
  Proof.
    unfold ph_signal, update.
    intros.
    destruct (Map_PHID_Extra.find_rw p s) as [(R,?)|(?,(R,?))];
    rewrite R in *; clear R. {
      assumption.
    }
    apply in_add_inv in H.
    destruct H; eauto using in_def, ph_in_signal_inv.
  Qed.

  Let in_drop_inv:
    forall x y p s,
    In x (ph_drop p y s) ->
    In x s.
  Proof.
    unfold ph_drop, update.
    intros.
    destruct (Map_PHID_Extra.find_rw p s) as [(R,?)|(?,(R,?))];
    rewrite R in *; clear R. {
      assumption.
    }
    apply in_add_inv in H.
    destruct H; auto.
    apply ph_in_drop_inv in H.
    destruct H; eauto using in_def.
  Qed.

  Let in_signal_all_inv:
    forall x y s,
    In x (signal_all y s) ->
    In x s.
  Proof.
    unfold signal_all, foreach.
    intros.
    inversion H; subst; clear H.
    rewrite Map_PHID_Facts.mapi_mapsto_iff in *; auto.
    destruct H0 as (ph', (?,mt)).
    subst.
    eauto using in_def, ph_in_try_signal_inv.
  Qed.

  Let in_wait_all_inv:
    forall x y s,
    In x (wait_all y s) ->
    In x s.
  Proof.
    unfold wait_all, foreach.
    intros.
    inversion H; subst; clear H.
    rewrite Map_PHID_Facts.mapi_mapsto_iff in *; auto.
    destruct H0 as (ph', (?,mt)).
    subst.
    eauto using in_def, ph_in_wait_inv.
  Qed.

  Let in_drop_all_inv:
    forall x y s,
    In x (drop_all y s) ->
    y <> x /\ In x s.
  Proof.
    unfold drop_all, foreach.
    intros.
    inversion H; subst; clear H.
    rewrite Map_PHID_Facts.mapi_mapsto_iff in *; auto.
    destruct H0 as (ph', (?,mt)).
    subst.
    apply ph_in_drop_inv in H1.
    destruct H1.
    eauto using in_def.
  Qed.

  Let in_async_inv:
    forall x y s p,
    In x (async p y s) ->
    get_new_task p = x \/ In x s.
  Proof.
    unfold async, foreach.
    intros.
    inversion H; subst; clear H.
    rewrite Map_PHID_Facts.mapi_mapsto_iff in *. {
      destruct H0 as (ph', (?,mt)).
      subst.
      apply ph_in_async_1_inv in H1.
      destruct H1;
      eauto using in_def.
    }
    intros.
    subst.
    auto.
  Qed.

  Lemma reduces_in_inv:
    forall x y o s s',
    In y s' ->
    Reduces s x o s' ->
    (y = x /\ exists p, o = PH_NEW p) \/
    (exists p, get_new_task p = y /\ o = ASYNC p) \/
    In y s.
  Proof.
    intros.
    destruct o; inversion H0; subst; clear H0; simpl in *;
    inversion H1; subst; clear H1.
    - unfold ph_new in *.
      apply in_add_inv in H.
      destruct H; auto.
      apply in_make_inv in H.
      eauto 4.
    - eauto using in_signal_inv.
    - eauto using in_drop_inv.
    - eauto using in_signal_all_inv.
    - eauto using in_wait_all_inv.
    - apply in_drop_all_inv in H.
      destruct H; auto.
    - apply in_async_inv in H.
      destruct H; eauto.
  Qed.

  Lemma reduces_drop_all_not_in:
    forall pm x pm',
    Reduces pm x DROP_ALL pm' ->
    ~ In x pm'.
  Proof.
    intros.
    unfold not; intros N.
    inversion H; subst; clear H.
    simpl in *.
    apply in_drop_all_inv in N.
    destruct N.
    contradiction.
  Qed.

  Lemma not_in_make:
    forall x,
    ~ In x make.
  Proof.
    intros.
    unfold not, make in *; intros N.
    inversion N; subst; clear N.
    rewrite Map_PHID_Facts.empty_mapsto_iff in *.
    assumption.
  Qed.
End InInv.