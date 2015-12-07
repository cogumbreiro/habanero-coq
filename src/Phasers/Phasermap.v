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

Definition phased := (phid * regmode) % type.

(** 
  Async phased register a new task in a list of [phased].
  Function [async_1] registers task [t] with phaser named by [p] according
  to mode [r].
  *)

(* ---- *)

Section EqDec.

Variable A:Type.

Variable eq_dec: forall (x y:A), { x = y } + { x <> y }.

Definition eq_dec_to_bool x y := if eq_dec x y then true else false.

Lemma eq_dec_inv_true:
  forall x y,
  eq_dec_to_bool x y = true -> x = y.
Proof.
  intros.
  unfold eq_dec_to_bool in *.
  destruct (eq_dec x y); auto; try inversion H.
Qed.

Lemma eq_dec_inv_false:
  forall x y,
  eq_dec_to_bool x y = false -> x <> y.
Proof.
  intros.
  unfold eq_dec_to_bool in *.
  destruct (eq_dec x y); auto; try inversion H.
Qed.

Lemma eq_dec_rw:
  forall x y,
  { eq_dec_to_bool x y = true /\ x = y } +
  { eq_dec_to_bool x y = false /\ x <> y }.
Proof.
  intros.
  unfold eq_dec_to_bool.
  destruct (eq_dec x y).
  - left; intuition.
  - right; intuition.
Qed.

End EqDec.

(* ---- *)

Definition tid_beq := eq_dec_to_bool TID.eq_dec.

Definition async_1 (l:list phased) t' t p ph : phaser :=
match findA (tid_beq p) l with
| Some r => register (mk_registry t' r) t ph
| _ => ph
end.

Definition async l t' t pm := Map_PHID.mapi (async_1 l t' t) pm.

(**
  Predicate [PhasedPre] ensures that task [t] can register task [t']
  using the phased object [ps].
   *)

Inductive PhasedPre (m:phasermap) (t t':tid) (ps:phased) : Prop := 
  phased_pre:
    forall ph v,
    Map_PHID.MapsTo (fst ps) ph m ->
    Map_TID.MapsTo t v ph ->
    RegisterPre (mk_registry t' (snd ps)) t ph ->
    PhasedPre m t t' ps.

(**
  The pre-condition of executing an async are three:
  (i) all phased pairs in [ps] must meet the preconditions of [PhasedPre],
  (ii) the phaser names in [ps] cannot be appear multiple times in [ps],
  (iii) the spawned task [t'] cannot be known in the phasermap.
  *)

Definition eq_phid (p p':phased) := (fst p) = (fst p').

Inductive AsyncPre ps t' t m : Prop :=
  async_pre:
    Forall (PhasedPre m t t') ps ->
    NoDupA eq_phid ps ->
    ~ In t' m -> 
    AsyncPre ps t' t m.

Definition async_op l t := mk_op (AsyncPre l t) (async l t).

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
| ASYNC : list phased -> tid -> op.
  
(** Function [get_impl] yields the [Op] object. *)

Definition get_impl o :=
match o with
| PH_NEW p => ph_new_op p
| PH_SIGNAL p => ph_signal_op p
| PH_DROP p => ph_drop_op p
| SIGNAL_ALL => signal_all_op
| WAIT_ALL => wait_all_op
| DROP_ALL => drop_all_op
| ASYNC ps t => async_op ps t
end.


(** In closing, we define the [Reduces] relation. *)

Inductive Reduces m t o : phasermap -> Prop :=
  reduces:
    can_run (get_impl o) t m ->
    Reduces m t o (run (get_impl o) t m).

(* begin hide *)
Section Facts.

  Lemma eq_phid_fst_eq:
    forall x y z,
    eq_phid (x, y) (x, z).
  Proof.
    compute.
    trivial.
  Qed.

  Lemma eq_phid_rw:
    forall x y z w,
    eq_phid (x, y) (z, w) ->
    x = z.
  Proof.
    compute.
    trivial.
  Qed.

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

  Lemma async_pre_inv:
    forall p l t' t m,
    AsyncPre (p :: l) t' t m ->
    AsyncPre l t' t m.
  Proof.
    intros.
    destruct H.
    inversion H0.
    inversion H.
    apply async_pre; auto.
  Qed.

  (* ----- *)

  Lemma finda_spec_some_1:
    forall {A : Type} {B:Type} (f : A -> bool) (e:B) l,
    findA f l = Some e -> exists k, List.In (k,e) l /\ f k = true.
  Proof.
    intros.
    induction l. {
      inversion H.
    }
    destruct a as (k', e').
    simpl in *.
    remember (f k').
    destruct b.
    - inversion H; subst.
      exists k'.
      intuition.
    - apply IHl in H; clear IHl.
      destruct H as  (k, (?,?)).
      eauto.
  Qed.

  Lemma finda_spec_none_1:
    forall {A : Type} {B:Type} (f : A -> bool) l,
    findA f l = None -> forall k (e:B), List.In (k,e) l -> f k = false.
  Proof.
    intros.
    induction l. {
      inversion H0.
    }
    destruct a as (k',e').
    simpl in *.
    remember (f k').
    destruct b.
    - inversion H.
    - destruct H0.
      + inversion H0; subst. auto.
      + auto.
  Qed.

  Lemma finda_rw:
    forall {A:Type} {B:Type} f l,
    { exists k e, findA f l = Some e /\ List.In (k,e) l /\ f k = true } +
    { findA f l = None /\ forall (k:A) (e:B), List.In (k,e) l -> f k = false }.
  Proof.
    intros.
    remember (findA f l).
    symmetry in Heqo.
    destruct o.
    - left.
      apply finda_spec_some_1 in Heqo.
      destruct Heqo as  (k, (?,?)).
      eauto.
    - right.
      eauto using finda_spec_none_1.
  Qed.

  (* ----- *)
(*
  Lemma tid_beq_inv_true:
    forall p p',
    tid_beq p p' = true ->
    p = p'.
  Proof.
    intros.
    unfold tid_beq in *.
    eauto using eq_dec_inv_true.
  Qed.

  Lemma tid_beq_inv_false:
    forall p p',
    tid_beq p p' = false ->
    p <> p'.
  Proof.
    intros.
    unfold tid_beq in *.
    eauto using eq_dec_inv_false.
  Qed.
*)
  Lemma async_simpl_notina:
    forall  p r l ph t' t,
    ~ InA eq_phid (p, r) l ->
    async_1 l t' t p ph = ph.
  Proof.
    intros.
    unfold async_1.
    destruct (finda_rw (tid_beq p) l) as [(p',(r',(R,(?,?))))|(R,?)].
    - rewrite R; clear R.
      contradiction H.
      rewrite InA_alt.
      exists (p', r').
      intuition.
      apply eq_dec_inv_true in H1.
      subst.
      apply eq_phid_fst_eq.
    - rewrite R; clear R.
      trivial.
  Qed.

  Lemma pm_async_1_rw:
    forall l t' t p ph,
      { exists r, List.In (p, r) l /\ async_1 l t' t p ph = register (mk_registry t' r) t ph }
      +
      { async_1 l t' t p ph = ph /\ forall r, ~ List.In (p, r) l}.
  Proof.
    intros.
    unfold async_1.
    destruct (finda_rw (tid_beq p) l) as [?|?].
    - left.
      destruct e as (p', (r, (R1,(?,R2)))).
      exists r.
      rewrite R1.
      apply eq_dec_inv_true in R2.
      subst.
      intuition.
    - right.
      destruct a as (R, Hx).
      rewrite R.
      intuition.
      apply Hx in H.
      apply eq_dec_inv_false in H.
      contradiction H.
      trivial.
  Qed.

  Lemma pm_async_1_mapsto_neq:
    forall t'' v l t' t p ph,
    t'' <> t' ->
    Map_TID.MapsTo t'' v (async_1 l t' t p ph) ->
    Map_TID.MapsTo t'' v ph.
  Proof.
    intros.
    unfold async_1 in *.
    destruct (finda_rw (tid_beq p) l) as [(p'',(r',(?,(?,?))))|(R,?)]. {
      apply eq_dec_inv_true in H3.
      subst.
      rewrite H1 in *; clear H1.
      eauto using ph_register_mapsto_neq.
    }
    rewrite R in *; clear R.
    assumption.
  Qed.

  Lemma pm_async_1_mapsto_eq:
    forall v l t' t p ph r,
    Map_TID.In t ph ->
    List.In (p, r) l ->
    Map_TID.MapsTo t' v (async_1 l t' t p ph) ->
    exists v' r, Map_TID.MapsTo t v' ph /\ List.In (p, r) l /\
    v = Taskview.set_mode v' r.
  Proof.
    intros.
    unfold async_1 in *.
    destruct (finda_rw (tid_beq p) l) as [(p'',(r',(?,(?,?))))|(R,?)]. {
      apply eq_dec_inv_true in H4.
      rewrite H2 in *; clear H2.
      subst.
      apply ph_register_mapsto_eq in H1; auto.
      destruct H1 as (v', (mt, R)).
      exists v'.
      exists r'.
      intuition.
    }
    (* absurd *)
    rewrite R in *; clear R.
    apply H2 in H0.
    apply eq_dec_inv_false in H0.
    contradiction H0.
    trivial.
  Qed.

  Lemma pm_async_1_mapsto:
    forall p ph l t' t t'' v,
    Map_TID.MapsTo t'' v (async_1 l t' t p ph) ->
    Map_TID.MapsTo t'' v ph \/
    (exists v' r, Map_TID.MapsTo t v' ph /\ List.In (p, r) l /\
    v = Taskview.set_mode v' r).
  Proof.
    intros.
    destruct (pm_async_1_rw l t' t p ph) as [(r,(i,R))|(R1,R2)]. {
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
    forall p ph l t' t m,
    Map_PHID.MapsTo p ph (async l t' t m) <->
    exists ph', ph = async_1 l t' t p ph' /\ Map_PHID.MapsTo p ph' m.
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
    forall p r l t' m t ph,
    ~ SetoidList.InA eq_phid (p, r) l ->
    Map_PHID.MapsTo p ph m ->
    Map_PHID.MapsTo p ph (async l t' t m).
  Proof.
    intros.
    apply pm_async_mapsto_rw.
    exists ph.
    intuition.
    symmetry.
    eauto using async_simpl_notina.
  Qed.

  Lemma async_notina_mapsto_rtl:
    forall l p r t' m t ph,
    ~ SetoidList.InA eq_phid (p, r) l ->
    Map_PHID.MapsTo p ph (async l t' t m) ->
    Map_PHID.MapsTo p ph m.
  Proof.
    intros.
    apply pm_async_mapsto_rw in H0.
    destruct H0 as (ph', (R, mt)).
    rewrite R in *.
    apply async_simpl_notina with (ph:=ph') (t':=t') (t:=t) in H.
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
