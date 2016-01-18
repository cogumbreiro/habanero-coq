Require Import HJ.Vars.
Require Import HJ.Phasers.Lang.
Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.
Import Regmode.Notations.

Open Scope reg_scope.

Inductive Check (pm:phasermap) (t:tid) : op -> Prop :=
  | check_ph_new:
    forall p,
    PhNewPre p t pm ->
    Check pm t (PH_NEW p)
  | check_ph_signal:
    forall p,
    PhSignalPre p t pm ->
    Check pm t (PH_SIGNAL p)
  | check_ph_drop:
    forall p,
    PhDropPre p t pm ->
    Check pm t (PH_DROP p)
  | check_signal_all:
    Check pm t SIGNAL_ALL
  | check_wait_all:
    (forall p ph,
      Map_PHID.MapsTo p ph pm ->
      forall v,
      Map_TID.MapsTo t v ph ->
      wait_phase v < signal_phase v) ->
    Check pm t WAIT_ALL
  | check_async:
    forall ps,
    AsyncPre ps t pm ->
    Check pm t (ASYNC ps).

Section Valid.
Require Import Coq.ZArith.BinInt.
Require Import HJ.Phasers.PhaseDiff.
Require Import HJ.Phasers.TransDiff.

(**
  Our notion of a valid phaser map is such that
  the transitive difference is a function, which means that
  any [t1 - ... - t2] yields the the same difference [z].
*)

Definition Valid (pm:phasermap) := TransDiffFun (pm_diff pm).
End Valid.