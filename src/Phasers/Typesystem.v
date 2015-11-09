Require Import HJ.Vars.
Require Import HJ.Phasers.Lang.
Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.

Import Taskview.Notations.

Open Scope reg_scope.

Inductive CanRegister: tid -> phasermap -> phased -> Prop :=
  can_register_def:
    forall p (ph:phaser) pm t v ph r,
    Map_PHID.MapsTo p ph pm ->
    Map_TID.MapsTo t v ph ->
    r <= (mode v) ->
    CanRegister t pm (p, r).

Definition eq_phid (p p':phased) := (fst p) = (fst p').

Inductive Check (pm:phasermap) (t:tid) : op -> Prop :=
  | check_ph_new:
    forall p,
    ~ Map_PHID.In p pm ->
    Check pm t (PH_NEW p)

  | check_ph_signal:
    forall p ph,
    Map_PHID.MapsTo p ph pm ->
    Map_TID.In t ph ->
    Check pm t (PH_SIGNAL p)
  
  | check_ph_drop:
    forall p ph,
    Map_PHID.MapsTo p ph pm ->
    Map_TID.In t ph ->
    Check pm t (PH_DROP p)

  | check_signal_all:
    Check pm t SIGNAL_ALL

  | check_wait_all:
    (forall p ph,
      Map_PHID.MapsTo p ph pm ->
      forall v,
      Map_TID.MapsTo t v ph ->
      v.(wait_phase) < v.(signal_phase)) ->
    Check pm t WAIT_ALL

  | check_async:
    forall t' ps,
    ~ Lang.In t' pm ->
    NoDupA eq_phid ps ->
    Forall (CanRegister t pm) ps ->
    Check pm t (ASYNC ps t').

Section Valid.
Require Import Coq.ZArith.BinInt.
Require Import HJ.Phasers.PhaseDiff.
Require Import HJ.Phasers.TransDiff.

Definition diff (pm:phasermap) (e:tid*tid % type) : Z -> Prop := pm_diff pm (fst e) (snd e).

(**
  Our notion of a valid phaser map is such that
  the transitive difference is a function, which means that
  any [t1 - ... - t2] yields the the same difference [z].
*)

Definition Valid (pm:phasermap) := TransDiffFun tid (diff pm).
End Valid.