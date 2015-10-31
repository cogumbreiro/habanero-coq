Require Import HJ.Vars.
Require Import HJ.Phasers.Lang.
Open Scope nat.

Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.

Module Taskview.

  (* We negate prec *)

  Inductive Ge v1 v2 : Prop := 
    | tv_ge_ge:
       signal_phase v1 >= wait_phase v2 ->
       Ge v1 v2
    | tv_ge_so:
      mode v1 = SIGNAL_ONLY ->
      Ge v1 v2
    | tv_ge_wo:
      mode v2 = WAIT_ONLY ->
      Ge v1 v2.

  Lemma tv_ge_dec:
    forall v1 v2,
    { Ge v1 v2 } + { ~ Ge v1 v2 }.
  Proof.
    intros.
    destruct (ge_dec (signal_phase v1) (wait_phase v2)).
    { left; auto using tv_ge_ge. }
    destruct (regmode_eq_dec (mode v1) SIGNAL_ONLY).
    { left; auto using tv_ge_so. }
    destruct (regmode_eq_dec (mode v2) WAIT_ONLY).
    { left; auto using tv_ge_wo. }
    right.
    intuition.
  Qed.

  Inductive Lt v1 v2 : Prop :=
    tv_lt_def:
      (signal_phase v1) < (wait_phase v2) ->
      WaitCap v1 ->
      SignalCap v2 ->
      Lt v1 v2.

  Lemma tv_lt_dec:
    forall v1 v2,
    { Lt v1 v2 } + { ~ Lt v1 v2 }.
  Proof.
    intros.
    destruct (wait_cap_dec v1). {
      destruct (signal_cap_dec v2). {
        destruct (lt_dec (signal_phase v1) (wait_phase v2)). {
          left; auto using tv_lt_def.
        }
        right; intuition.
      }
      right; intuition.
    }
    right; intuition.
  Qed.

  Lemma tv_ge_to_not_lt:
    forall v1 v2,
    Ge v1 v2 -> ~ Lt v1 v2.
  Proof.
    intros.
    intuition.
    - destruct H2; rewrite H in H3; inversion H3.
    - destruct H0; rewrite H in H3; inversion H3.
  Qed.

  Lemma tv_lt_to_not_ge:
    forall v1 v2,
    Lt v1 v2 -> ~ Ge v1 v2.
  Proof.
    intros.
    intuition.
    - destruct H2; rewrite H0 in H3; inversion H3.
    - destruct H; rewrite H in H3; inversion H3.
  Qed.

  Lemma tv_not_lt_to_ge:
    forall v1 v2,
    ~ Lt v1 v2 -> Ge v1 v2.
  Proof.
    intros.
    destruct (ge_dec (signal_phase v1) (wait_phase v2)).
    { auto using tv_ge_ge. }
    destruct (regmode_eq_dec (mode v1) SIGNAL_ONLY).
    { auto using tv_ge_so. }
    destruct (regmode_eq_dec (mode v2) WAIT_ONLY).
    { auto using tv_ge_wo. }
    assert (Lt v1 v2). {
      assert (signal_phase v1 < wait_phase v2) by intuition.
      auto using tv_lt_def, neq_wo_to_signal_cap, neq_so_to_wait_cap.
    }
    contradiction.
  Qed.

  Lemma tv_not_lt_rw_tv_ge:
    forall v1 v2,
    ~ Lt v1 v2 <-> Ge v1 v2.
  Proof.
    split; auto using tv_not_lt_to_ge, tv_ge_to_not_lt.
  Qed.

  Lemma tv_not_ge_to_lt:
    forall v1 v2,
    ~ Ge v1 v2 -> Lt v1 v2.
  Proof.
    intros.
    destruct (wait_cap_dec v1). {
      destruct (signal_cap_dec v2). {
        destruct (lt_dec (signal_phase v1) (wait_phase v2)). {
          auto using tv_lt_def.
        }
        assert (Ge v1 v2). {
          assert (signal_phase v1 >= wait_phase v2) by intuition.
          auto using tv_ge_ge.
        }
        contradiction.
      }
      assert (Ge v1 v2). {
        auto using tv_ge_wo, not_signal_cap_to_wo.
      }
      contradiction.
    }
    assert (Ge v1 v2) by
      auto using tv_ge_so, not_wait_cap_to_so.
    contradiction.
  Qed.

  Lemma tv_not_ge_rw_lt:
    forall v1 v2,
    ~ Ge v1 v2 <-> Lt v1 v2.
  Proof.
    split; auto using tv_not_ge_to_lt, tv_lt_to_not_ge.
  Qed.

  Lemma tv_lt_ge_dec:
    forall v1 v2,
    { Lt v1 v2 } + { Ge v1 v2 }.
  Proof.
    intros.
    destruct (tv_lt_dec v1 v2).
    - left; auto.
    - right; auto using tv_not_lt_to_ge.
  Qed.



  (** Valid task view *)
  Inductive Valid v : Prop :=
    | tv_valid_wait_cap_eq:
      WaitCap v ->
      wait_phase v = signal_phase v ->
      Valid v
    | tv_valid_wait_cap_succ:
      WaitCap v ->
      S (wait_phase v) = signal_phase v ->
      Valid v
    | tv_valid_so:
      mode v = SIGNAL_ONLY ->
      wait_phase v <= signal_phase v ->
      Valid v.


  Lemma signal_preserves_valid:
    forall v,
    Valid v ->
    Valid (Lang.Taskview.signal v).
  Proof.
    intros.
    inversion H.
    - apply tv_valid_wait_cap_succ.
      auto using signal_presevers_wait_cap.
      apply signal_wait_cap_signal_phase in H0.
      rewrite H0.
      auto using signal_preserves_wait_phase.
    - apply tv_valid_wait_cap_succ.
      auto using signal_presevers_wait_cap.
      apply signal_wait_cap_signal_phase in  H0.
      rewrite H0.
      auto using signal_preserves_wait_phase.
    - apply tv_valid_so.
      rewrite signal_preserves_mode; auto.
      rewrite signal_preserves_wait_phase.
      rewrite signal_so_signal_phase; auto.
  Qed.


  Lemma wait_preserves_valid:
    forall v,
    Valid v ->
    wait_phase v < signal_phase v ->
    Valid (Lang.Taskview.wait v).
  Proof.
    intros.
    inversion H.
    - assert (wait_phase v <> signal_phase v) by intuition.
      contradiction.
    - apply tv_valid_wait_cap_eq.
      eauto using wait_preserves_mode, wait_cap_eq_mode.
      rewrite wait_preserves_signal_phase.
      rewrite <- H2.
      rewrite wait_wait_phase.
      trivial.
    - apply tv_valid_so.
      eauto using wait_preserves_mode, wait_cap_eq_mode.
      rewrite wait_wait_phase.
      rewrite wait_preserves_signal_phase.
      intuition.
  Qed.
  
End Taskview.



Inductive PhRel (R: taskview -> taskview -> Prop) (ph1 ph2:phaser) : Prop := 
  ph_rel_def:
    (forall t1 t2 v1 v2,
    Map_TID.MapsTo t1 v1 ph1 ->
    Map_TID.MapsTo t2 v2 ph2 ->
    R v1 v2) ->
    PhRel R ph1 ph2.

Definition PhGe := PhRel TvGe.

Inductive PmRel (R: phaser -> phaser -> Prop) (m1 m2:phasermap) : Prop :=
  pm_rel_def:
    (forall p ph1 ph2,
      Map_PHID.MapsTo p ph1 m1 ->
      Map_PHID.MapsTo p ph2 m2 ->
      R ph1 ph2) ->
    PmRel R m1 m2.

Definition PmGe := PmRel PhGe.

Inductive Valid (m:phasermap) :=
  valid_def:
    PmGe m m ->
    Valid m.

Lemma signal_respects_tv_ge:
  forall v,
  TvGe v v ->
  TvGe v (Taskview.signal v) /\
  TvGe (Taskview.signal v) (Taskview.signal v).
Proof.
  split; intros;
  unfold Taskview.signal;
  destruct v;
  inversion H; simpl in *;
  first [
    solve [(apply tv_ge_ge;
    simpl in  *;
    destruct mode; (simpl in *; auto))] |
    (subst; auto using tv_ge_so, tv_ge_wo) ].
Qed.

Lemma tv_ge_signal_3:
  forall v v',
  TvGe v v' ->
  TvGe v (Taskview.signal v').
Proof.
  intros.
  unfold Taskview.signal.
  destruct v';
  inversion H; simpl in *;
  first [
    solve [(apply tv_ge_ge;
    simpl in  *;
    destruct mode; (simpl in *; auto))] |
    (subst; auto using tv_ge_so, tv_ge_wo) ].
Qed.

Lemma signal_respects_tv_ge_1:
  forall v,
  TvGe v v ->
  TvGe (Taskview.signal v) (Taskview.signal v).
Proof.
  intros.
  apply signal_respects_tv_ge in H.
  destruct H; assumption.
Qed.

Lemma signal_respects_tv_ge_2:
  forall v,
  TvGe v v ->
  TvGe v (Taskview.signal v).
Proof.
  intros.
  apply signal_respects_tv_ge in H.
  destruct H; assumption.
Qed.

Lemma tv_signal_ge_4:
  forall v,
  TvGe v (Taskview.signal v) ->
  TvGe (Taskview.signal v) (Taskview.signal v).
Proof.
  intros.
  unfold Taskview.signal.
  destruct v;
  inversion H; simpl in *;
  first [
    solve [(apply tv_ge_ge;
    simpl in  *;
    destruct mode; (simpl in *; auto))] |
    (subst; auto using tv_ge_so, tv_ge_wo) ].
Qed.  


Lemma tv_signal_ge_5 (Hx:forall v, wait_phase v <= signal_phase v)
  (v:taskview)
  (Hsig: signal_phase v = wait_phase v \/ signal_phase v = S (wait_phase v)):
  forall v',
  TvGe v v' ->
  TvGe (Taskview.signal v) v'.
Proof.
  intros.
  unfold Taskview.signal.
  destruct v;
  inversion H; simpl in *.
  - apply tv_ge_ge.
    destruct mode;  simpl in *; subst; intuition.
  - subst. auto using tv_ge_so.
  - subst. auto using tv_ge_wo.
Qed.

Lemma signal_respect_ph_ge:
  forall ph,
  PhGe ph ph ->
  forall t,
  PhGe ph (Phaser.signal t ph).
Proof.
  intros.
  unfold PhGe in *.
  apply ph_rel_def.
  intros.
  inversion H.
  unfold Phaser.signal in *.
  unfold Phaser.update in *.
  remember (Map_TID.find _ _).
  symmetry in Heqo.
  destruct o as [v|?].
  - apply Map_TID_Facts.add_mapsto_iff in H1.
    destruct H1 as [(?,?)|(?,?)].
    + subst. 
      apply Map_TID_Facts.find_mapsto_iff in Heqo.
      eauto using tv_ge_signal_3.
    + eauto.
  - eauto.
Qed.

Inductive TvValid (v:taskview) : Prop :=
  tv_valid_def:
    wait_phase <= signal_phase v - >
    TvValid  v

Inductive ValidPh (ph:phaser) : Prop := 
  valid_ph_def:
    (forall t v, Map_TID.MapsTo t v ph -> 

Lemma signal_respect_ph_ge_2:
  forall ph t,
  PhGe ph (Phaser.signal t ph) ->
  PhGe (Phaser.signal t ph) (Phaser.signal t ph).
Proof.
  intros.
  unfold PhGe in *.
  apply ph_rel_def.
  intros.
  inversion H.
  clear H.
  unfold Phaser.signal in *.
  unfold Phaser.update in *.
  remember (Map_TID.find _ _).
  symmetry in Heqo.
  destruct o as [v|?].
  - apply Map_TID_Facts.add_mapsto_iff in H1.
    apply Map_TID_Facts.add_mapsto_iff in H0.
    destruct H0, H1 as [(?,?)|(?,?)].
    + destruct H.
      repeat subst.
      assert (TvGe v (Taskview.signal v)). {
        apply H2 with (t2) (t2).
        apply Map_TID_Facts.find_mapsto_iff in Heqo; auto.
        auto using Map_TID.add_1.
      }
      eauto using signal_respects_tv_ge_1, tv_signal_ge_4.
    + destruct H; subst.
      apply Map_TID_Facts.find_mapsto_iff in Heqo; auto.
      assert (TvGe v v2). {
        eauto using Map_TID.add_2.
      }
      apply tv_signal_ge_5.
Qed.

Lemma signal_respects_tv_ge_2:
  forall v,
  TvGe v v ->
  TvGe v (Taskview.signal v).
Proof.
  intros.
  unfold Taskview.signal.
  destruct v.
  inversion H; simpl in *.
  - apply tv_ge_ge.
    simpl in  *.
    destruct mode; (simpl in *; auto).
  - subst.
    auto using tv_ge_so.
  - subst.
    apply tv_ge_wo.
    auto.
Qed.
Import Phaser.

Lemma ph_update_respects_ph_ge
  (f: taskview -> taskview)
  (Hge1: forall v, TvGe v v -> TvGe (f v) (f v))
  (Hge2: forall v v', TvGe v v' -> TvGe (f v) v')
  (Hge3: forall v v', TvGe v v' -> TvGe v (f v')):
  forall t ph,
  PhGe ph ph ->
  PhGe (update t f ph) (update t f ph).
Proof.
  intros.
  unfold PhGe in *.
  unfold update in *.
  inversion H.
  apply ph_rel_def.
  intros.
  remember (Map_TID.find _ _) as o.
  symmetry in Heqo.
  destruct o.
  - rename t0 into v.
    apply Map_TID_Facts.add_mapsto_iff in H1.
    apply Map_TID_Facts.add_mapsto_iff in H2.
    destruct H1, H2;(
      destruct H1, H2;
      repeat subst;
      apply Map_TID_Facts.find_mapsto_iff in Heqo;
      eauto
    ).
  - eauto.
Qed.



Inductive Prec t1 m1 t2 m2 : Prop :=
  prec_def:
    forall p ph1 ph2 (v1 v2:taskview),
    Map_PHID.MapsTo p ph1 m1 ->
    Map_PHID.MapsTo p ph2 m2 ->
    Map_TID.MapsTo t1 v1 ph1 ->
    Map_TID.MapsTo t2 v2 ph2 ->
    TvPrec v1 v2 ->
    Prec t1 m1 t2 m2.

Inductive Registered (t:tid) (p:phid) (m:phasermap) :=
  registered_def:
    forall ph,
    Map_PHID.MapsTo p ph m ->
    Map_TID.In t ph ->
    Registered t p m.
    

Inductive Related (i1 i2:timestamp) : Prop :=
  related_def:
    forall p,
    Registered (fst i1) p (snd i1) ->
    Registered (fst i2) p (snd i2) ->
    Related i1 i2.

Lemma phase_ordering_step:
  forall m t1 t2 o1 o2 m1 m2,
  (* both tasks are related on at least one phaser *)
  Related (t1,m1) (t2,m2) ->
  Reduce m t1 o1 m1 ->
  Reduce m1 t2 o2 m2 ->
  ~ Prec (t2, m2) (t1, m1).
Proof.
  intros.
  intuition.
  inversion H2.
  simpl in *.
  inversion H0; subst.
  simpl in *.
  inversion H; subst.
  -  
Admitted.


(** Reduction rule that hides the task and operation. *)

Inductive SilentReduction (m m':phasermap) : Prop :=
  silent_reduce_def:
    forall t o,
    Reduce m t o m' ->
    SilentReduction m m'.

Require Import Coq.Relations.Relation_Operators.

Definition StarReduce := clos_trans phasermap SilentReduction.

Lemma phase_ordering_step:
  forall m m',
  SilentReduction m m' ->
  forall t' t, ~ Prec (t', m') (t, m).
Proof.
  intros.
  destruct H as (t'', o, H).
  
Admitted.

Theorem phase_ordering_correct:
  forall m1 m2,
  StarReduce m1 m2 ->
  forall t1 t2,
  ~ Prec (t2,m2) (t1,m1).
Proof.
  intros m1 m2 H.
  induction H; intros.
  - auto using phase_ordering_step.
  - intuition.

(*
 Is it possible for i1 < i2 an i2 < i1?
*)

(*
  M ->^(i1,t1) -> M1 ->*^(i2,t2) -> M1
  \/
  M ->^(i2,t2) -> M2 ->*^(i1,t1) -> M1

Here we only consider two triplets:

(i1,t1,M1) and (i2, t2, M2)

Although, for the discussions only i an M is important.
*)

(*
The activity executing i1 is registered on phaser ph as
wait-only. Then S(ph, i1) = ∞, and the S(ph, i1) <
W(ph, i2) precondition will be false.

Can we conclude anything about the precondition being false?

*)

(*
The activity executing i1 is registered on phaser ph as
signal-only. If S(ph, i1) < W(ph, i2) then i2 is being
executed by an activity that has waited on the phaser
more times than the activity executing i1 has signaled.
It must be that i1 is executed before i2 , because i2
could not be executed without at least one more signal
from the activity executing i1 .

If t1 <ph t2, then
  M ->^(i1,t1) -> M1 ->*^(i2,t2) -> M1
and
  ~ M ->^(i2,t2) -> M2 ->*^(i1,t1) -> M1

*)

(*
 The activity executing i1 is registered on phaser ph
as signal-wait. If S(ph, i1 ) < W(ph, i2) then the same
argument follows as in the signal case above. If i1
occurs in a split phase then we cannot establish any
order on the activities executing in the next wait phase
W(ph, i1) + 1 because we have signaled that they may
continue on to phase W(ph, i1 ) + 1. The inequality
will only hold for instructions two wait phases ahead,
W(ph, i1) + 2.
---

If t1 <ph t2 and SPLIT-PHASE t1 - t2 = 1, then what can we conclude?

---

Can we use the phase-ordering property to verify the correctness of the semantics?

For instance, can we just state that for any:
forall m m',
m reducesto m' ->
forall t t', ~ (t', m') < (t, m)
?
*)
Example case3:
  forall x y a b ph,
  x <> y ->
  Map_TID.MapsTo x a ph ->
  Map_TID.MapsTo y b ph ->
  signal_phase a < wait_phase b ->
  WaitCap a ->
  SignalCap b ->
  (forall v, signal_phase v >= wait_phase v) ->
  signal_phase a = wait_phase a + 1 ->
  (forall t, t <> x -> forall v, Map_TID.MapsTo t v ph -> signal_phase v = wait_phase v) ->
  signal_phase b >= wait_phase a + 1.
Proof.
  intros.
  assert (RW: signal_phase b = wait_phase b) by eauto; rewrite RW in *; clear RW H7.
  rewrite H6 in *; clear H6.
  intuition.
Qed.

(*
Lemma phase_ordering:
  forall m x y p ph,
  Map_PHID.MapsTo p ph m ->
  Sync ph 1 ->
  Map_TID.MapsTo x (TV 0 0 SIGNAL_WAIT) ph ->
  Map_TID.MapsTo y (TV 2 2 SIGNAL_WAIT) ph ->
  exists m', Reduce m x WAIT_ALL m'.
Proof.
  intros.
  exists (mapi ph 
Qed.
*)
Lemma phase_ordering:
  forall m x y m',
  Prec m x y ->
  ~ Reduce m x WAIT_ALL m'.
Proof.
  intros.
  intuition.
  inversion H0; clear H0; subst.
  destruct H.
  apply H1 in H; clear H1.
  inversion H; subst.
  - assert (v0 = v) by eauto using Map_TID_Extra.F.MapsTo_fun; subst.
    inversion H4;
    rewrite H6 in H7; inversion H7.
  - assert (v0 = v) by eauto using Map_TID_Extra.F.MapsTo_fun; subst.
    assert (Hx : signal_phase v' >= wait_phase v + 1) by (unfold Await in *; eauto).
    clear H7.
    (* 
      signal_phase v' >= wait_phase v + 1
      signal_phase v < wait_phase v'
      ---
      v' > v + 1
      v < v'
      ---
      y + k >= x + 1
      x + l < y
      ---
      y >= x + 1 - k
      x + l < y
      ---
      l < 1 - k
      ---
      if k = 0 -> true
      if k > 1 -> false
      ---
      if signal_phase v' = wait_phase v'
      then true
      else false
      *)
      
      assert (n: ~signal_phase v' < wait_phase v)). {
        intuition.
      }
    contradiction n.
    
    
Qed.  