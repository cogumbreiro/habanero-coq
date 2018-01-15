Require Import Coq.Lists.List.
Import ListNotations.

Require Import Phasers.Lang.
Require Import Tid.
Require Import Vars.
Require HJ.Phasers.Typesystem.
Require HJ.Phasers.WellFormed.
Require HJ.Phasers.Progress.
Require HJ.Phasers.SubjectReduction.
Require Import HJ.Phasers.Phasermap.
Section Defs.

  Structure t := {
    state : phasermap;
    history : Trace.t;
    spec: Trace.ReducesN state history
  }.

  Inductive Reduces: t -> (tid*op) -> t -> Prop :=
  | reduces_def:
    forall t o pm1 pm2,
    Phasermap.Reduces (state pm1) t o (state pm2) ->
    history pm2 = (t,o)::(history pm1) ->
    Reduces pm1 (t, o) pm2.

  Lemma make : t.
  Proof.
    refine ({| state := make; history := nil |}).
    auto using Trace.reduces_n_nil.
  Defined.

End Defs.

Section Props.
  Let progress_aux:
    forall o x m s',
    Phasermap.Reduces (state m) x o s' ->
    exists n, Reduces m (x, o) n.
  Proof.
    intros.
    assert (Hr: Trace.ReducesN s' ( (x,o)::(history m))%list ). {
      eauto using Trace.reduces_n_cons, spec.
    }
    exists {|
      state := s';
      history := ((x,o)::(history m))%list;
      spec := Hr
    |}.
    eauto using reduces_def.
  Qed.

  Definition Enabled s x :=
  forall o,
  Typesystem.Op.Valid (state s) x o -> exists q, Reduces s (x, o) q.

  Theorem progress:
    forall (s:t),
    Nonempty (state s) ->
    exists x, In x (state s) /\ Enabled s x.
  Proof.
    intros.
    apply Progress.progress in H;
    eauto using
      SubjectReduction.reduces_n_to_valid,
      spec,
      WellFormed.Phasermap.well_formed_to_reduces_n.
    destruct H as (x, (Hi, He)).
    exists x.
    unfold Enabled; split; auto.
    intros.
    edestruct He; eauto.
  Qed.
  
  Theorem progress_empty:
    forall (s:t),
    Empty (state s) ->
    forall x, Enabled s x.
  Proof.
    intros.
    apply LEDec.pm_tids_empty in H.
    unfold Enabled; intros.
    edestruct Progress.progress_empty; eauto using spec.
  Qed.

  Lemma progress_nonblocking:
    forall pm t i,
    i <> WAIT_ALL ->
    Typesystem.Op.Valid (state pm) t i ->
    exists m, Reduces pm (t, i) m.
  Proof.
    intros.
    eapply Progress.progress_unblocking_simple in H; eauto using spec, SubjectReduction.reduces_n_to_valid.
    destruct H as (m', Hr).
    eauto.
  Qed.

End Props.