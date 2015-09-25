Require Import HJ.Vars.
Require Import HJ.Phasers.Lang.
Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.

Local Open Scope reg_scope.

Inductive CanRegister: tid -> phasermap -> phased -> Prop :=
  can_register_def:
    forall p (ph:phaser) pm t v ph r,
    Map_PHID.MapsTo p ph pm ->
    Map_TID.MapsTo t v ph ->
    r <= (mode v) ->
    CanRegister t pm (p, r).

Definition eq_phid (p p':phased) := (fst p) = (fst p').

Inductive Check: tid -> op -> phasermap -> Prop :=
  | check_ph_new:
    forall t p pm,
    ~ Map_PHID.In p pm ->
    Check t (PH_NEW p) pm

  | check_ph_signal:
    forall t p ph pm,
    Map_PHID.MapsTo p ph pm ->
    Map_TID.In t ph ->
    Check t (PH_SIGNAL p) pm
  
  | check_ph_drop:
    forall t p ph pm,
    Map_PHID.MapsTo p ph pm ->
    Map_TID.In t ph ->
    Check t (PH_DROP p) pm

  | check_signal_all:
    forall t pm,
    Check t SIGNAL_ALL pm

  | check_wait_all:
    forall t pm,
    (forall p ph,
      Map_PHID.MapsTo p ph pm ->
      forall v,
      Map_TID.MapsTo t v ph ->
      v.(wait_phase) < v.(signal_phase)) ->
    Check t WAIT_ALL pm

  | check_async:
    forall t t' ps pm,
    ~ Lang.In t' pm ->
    NoDupA eq_phid ps ->
    Forall (CanRegister t pm) ps ->
    Check t (ASYNC ps t') pm.
