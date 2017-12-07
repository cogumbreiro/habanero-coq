Require Import HJ.Vars.
Require Import HJ.Phasers.Lang.
Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.
Import Regmode.Notations.
Require Import Aniceto.List.

Open Scope reg_scope.
Module Op.
Inductive Valid (pm:phasermap) (t:tid) : op -> Prop :=
  | valid_ph_new:
    forall p,
    PhNewPre p t pm ->
    Valid pm t (PH_NEW p)
  | valid_ph_signal:
    forall p,
    PhSignalPre p t pm ->
    Valid pm t (PH_SIGNAL p)
  | valid_ph_drop:
    forall p,
    PhDropPre p t pm ->
    Valid pm t (PH_DROP p)
  | valid_signal_all:
    Valid pm t SIGNAL_ALL
  | valid_wait_all:
    (forall p ph,
      Map_PHID.MapsTo p ph pm ->
      forall v,
      Map_TID.MapsTo t v ph ->
      wait_phase v < signal_phase v) ->
    Valid pm t WAIT_ALL
  | valid_drop_all:
    Valid pm t DROP_ALL
  | valid_async:
    forall ps,
    AsyncPre ps t pm ->
    Valid pm t (ASYNC ps).

Section Props.
  Ltac handle_not := 
      right; unfold not; intros N; inversion N;
      subst;
      contradiction;
      fail.

  Let valid_wait_all_dec pm t:
    {Valid pm t WAIT_ALL} + {~ Valid pm t WAIT_ALL}.
  Proof.
    assert (valid_lt:forall v, { wait_phase v < signal_phase v } + { ~ wait_phase v < signal_phase v }). {
      auto using Compare_dec.lt_dec.
    }
    remember (List.forallb (fun kv =>
      match Map_TID.find t (snd kv) with
      | Some v => if valid_lt v then true else false
      | None => true
      end
    ) (Map_PHID.elements pm)).
    symmetry in Heqb.
    destruct b. {
      left.
      apply valid_wait_all; intros.
      rewrite forallb_forall in Heqb.
      assert (i: In (p, ph) (Map_PHID.elements pm)). {
        rewrite Map_PHID_Extra.maps_to_iff_in_elements in H; auto using phid_eq_rw.
      }
      specialize Heqb with (p,ph).
      specialize (Heqb i).
      simpl in *.
      destruct (Map_TID_Extra.find_rw t ph) as [(?,N)|(v',(R,?))]. {
        contradiction N.
        eauto using Map_TID_Extra.mapsto_to_in.
      }
      rewrite R in *.
      assert (v' = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      destruct (valid_lt v); auto.
      inversion Heqb.
    }
    right.
    rewrite forallb_existsb in Heqb.
    rewrite Bool.negb_false_iff in *.
    apply existsb_exists in Heqb.
    unfold not; intros N.
    destruct Heqb as ((p,ph),(Hi,Hx)).
    apply Map_PHID_Extra.maps_to_iff_in_elements in Hi; auto using phid_eq_rw.
    rewrite Bool.negb_true_iff in *.
    simpl in *.
    destruct (Map_TID_Extra.find_rw t ph) as [(R,N1)|(v',(R,?))]; rewrite R in *; clear R. {
      inversion Hx.
    }
    destruct (valid_lt v'). {
      inversion Hx.
    }
    contradiction n.
    inversion N; subst; eauto.
  Defined.

  Lemma valid_dec pm t o :
    { Valid pm t o } + { ~ Valid pm t o }.
  Proof.
    destruct o.
    - destruct (ph_new_pre_dec p t pm); try handle_not.
      auto using valid_ph_new.
    - destruct (ph_signal_pre_dec p t pm); try handle_not.
      auto using valid_ph_signal.
    - destruct (ph_drop_pre_dec p t pm); try handle_not.
      auto using valid_ph_drop.
    - auto using valid_signal_all.
    - auto using valid_wait_all_dec.
    - auto using valid_drop_all.
    - destruct (async_pre_dec p t pm); try handle_not.
      auto using valid_async.
  Defined.
End Props.
End Op.
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