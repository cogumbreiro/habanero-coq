Require Import Coq.ZArith.BinInt.
Require Import Coq.Relations.Relations.
Require Import Coq.Lists.List.
Require Import Vars.
Require Import ListUtil.
Require Import MapUtil.
Require Import Lang.

Definition ph_diff (ph:phaser) (t1:tid) (t2:tid) (z:Z)
  := exists v1, Map_TID.MapsTo t1 v1 ph /\
     exists v2, Map_TID.MapsTo t2 v2 ph /\
     exists n1, WaitPhase v1 n1 /\
     exists n2, WaitPhase v2 n2 /\
     ((Z_of_nat n1) - (Z_of_nat n2))%Z = z.

Definition diff (ph:phaser) (t1:tid) (t2:tid) : option Z := 
  match Map_TID.find t1 ph with
    | Some v1 => 
      match Map_TID.find t2 ph with
        | Some v2 =>
          Some ((Z_of_nat (wait_phase v1)) - (Z_of_nat (wait_phase v2)))%Z
        | _ => None
      end
    | _ => None
  end.

Lemma diff_spec_1:
  forall ph t1 t2 z,
  diff ph t1 t2 = Some z ->
  ph_diff ph t1 t2 z.
Proof.
  intros.
  unfold diff in *.
  unfold ph_diff.
  remember (Map_TID.find t1 ph).
  symmetry in Heqo.
  destruct o.
  - rewrite <- Map_TID_Facts.find_mapsto_iff in Heqo.
    exists t.
    intuition.
    remember (Map_TID.find t2 ph).
    symmetry in Heqo0.
    destruct o.
    + rewrite <- Map_TID_Facts.find_mapsto_iff in Heqo0.
      exists t0.
      intuition.
      exists (wait_phase t).
      split.
      { apply wait_phase_spec_1. }
      exists (wait_phase t0).
      split.
      { apply wait_phase_spec_1. }
      inversion H.
      auto.
    + inversion H.
  - inversion H.
Qed.

Lemma diff_spec_2:
  forall ph t1 t2 z,
  ph_diff ph t1 t2 z ->
  diff ph t1 t2 = Some z.
Proof.
  intros.
  unfold ph_diff in H.
  unfold diff.
  destruct H as (v1, (Hmt1, (v2, (Hmt2, (n1, (Hw1, (n2, (Hw2, Hdiff)))))))).
  apply Map_TID_Facts.find_mapsto_iff in Hmt1.
  apply Map_TID_Facts.find_mapsto_iff in Hmt2.
  rewrite Hmt1.
  rewrite Hmt2.
  apply wait_phase_spec_2 in Hw1.
  apply wait_phase_spec_2 in Hw2.
  subst.
  trivial.
Qed.

Lemma diff_none:
  forall ph t t',
  diff ph t t' = None ->
  forall z, ~ ph_diff ph t t' z.
Proof.
  intros.
  intuition.
  apply diff_spec_2 in H0.
  rewrite H in H0.
  inversion H0.
Qed.

Lemma ph_diff_fun:
  forall ph t t' z z',
  ph_diff ph t t' z ->
  ph_diff ph t t' z' ->
  z = z'.
Proof.
  intros.
  apply diff_spec_2 in H.
  apply diff_spec_2 in H0.
  rewrite H in H0.
  inversion H0.
  trivial.
Qed.

Definition WTaskIn (t:tid) (ph:phaser) :=
  exists v, Map_TID.MapsTo t v ph /\
  exists n, WaitPhase v n.

Lemma wtask_in_def:
  forall t ph v n,
  Map_TID.MapsTo t v ph ->
  WaitPhase v n ->
  WTaskIn t ph.
Proof.
  intros.
  unfold WTaskIn.
  exists v.
  intuition.
  exists n.
  assumption.
Qed.

Lemma ph_diff_refl:
  forall t ph,
  WTaskIn t ph ->
  ph_diff ph t t 0.
Proof.
  intros.
  unfold ph_diff.
  unfold WTaskIn in H.
  destruct H as (v, (Hmt, (n, Hw))).
  repeat (exists v; intuition).
  repeat (exists n; intuition).
Qed.

Lemma ph_diff_symm:
  forall ph t t' z,
  ph_diff ph t t' z ->
  ph_diff ph t' t (-z).
Proof.
  intros.
  unfold ph_diff in *.
  destruct H as (v1, (Hmt1, (v2, (Hmt2,
    (n1, (Hw1, (n2, (Hw2, Hdiff)))))))).
  exists v2; intuition.
  exists v1; intuition.
  exists n2; intuition.
  exists n1; intuition.
Qed.

Lemma ph_diff_inv:
  forall ph t t' z,
  ph_diff ph t t' z ->
  WTaskIn t ph /\ WTaskIn t' ph.
Proof.
  intros.
  unfold ph_diff in H.
  destruct H as (v1, (Hmt1, (v2, (Hmt2,
    (n1, (Hw1, (n2, (Hw2, Hdiff)))))))).
  unfold WTaskIn in *.
  split.
  - exists v1.
    intuition.
    exists n1.
    intuition.
  - exists v2.
    intuition.
    exists n2.
    intuition.
Qed.

Lemma ph_diff_inv_left:
  forall ph t t' z,
  ph_diff ph t t' z ->
  WTaskIn t ph.
Proof.
  intros.
  apply ph_diff_inv in H.
  intuition.
Qed.

Lemma ph_diff_inv_right:
  forall ph t t' z,
  ph_diff ph t t' z ->
  WTaskIn t' ph.
Proof.
  intros.
  apply ph_diff_inv in H.
  intuition.
Qed.

Definition tid_In (t:tid) (pm:phasermap) :=
  exists p ph, Map_PHID.MapsTo p ph pm /\ WTaskIn t ph.

Definition ph_le (ph:phaser) (t1:tid) (t2:tid) :=
  exists (z:Z), ph_diff ph t1 t2 z /\ (z <= 0)%Z.

Lemma ph_le_refl:
  forall t ph,
  WTaskIn t ph ->
  ph_le ph t t.
Proof.
  intros.
  unfold ph_le.
  exists 0%Z.
  intuition.
  apply ph_diff_refl.
  assumption.
Qed.

Lemma ph_le_inv:
  forall t t' ph,
  ph_le ph t t' ->
  WTaskIn t ph /\ WTaskIn t' ph.
Proof.
  intros.
  unfold ph_le in *.
  destruct H as (z, (H1, H2)).
  apply ph_diff_inv with (z:=z).
  assumption.
Qed.

Section ENABLED.
Variable pm:phasermap.

(** Less-than-equals *)
Definition wp_le (t:tid) (t':tid) :=
  exists p ph, Map_PHID.MapsTo p ph pm /\ ph_le ph t t'.

Lemma wp_le_refl:
  forall t,
  tid_In t pm ->
  wp_le t t.
Proof.
  intros.
  unfold wp_le.
  unfold tid_In in H.
  destruct H as (p, (ph, (Hmt, Hin))).
  exists p; exists ph.
  intuition.
  apply ph_le_refl.
  assumption.
Qed.

Lemma wp_le_inv:
  forall t t',
  wp_le t t' ->
  tid_In t pm /\ tid_In t' pm.
Proof.
  intros.
  unfold wp_le in *.
  destruct H as (p, (ph, (Hmt, Hin))).
  apply ph_le_inv in Hin.
  unfold tid_In.
  split; repeat (exists p; exists ph; intuition).
Qed.

Definition LE := clos_trans tid wp_le.

Variable LE_dec:
  forall t t',
  {LE t t'} + {~ LE t t'}.

Lemma LE_refl:
  forall t,
  tid_In t pm ->
  LE t t.
Proof.
  intros.
  unfold LE.
  apply t_step.
  apply wp_le_refl.
  assumption.
Qed.

Lemma LE_inv:
  forall t t',
  LE t t' ->
  tid_In t pm /\ tid_In t' pm.
Proof.
  intros.
  unfold LE in H.
  induction H.
  - apply wp_le_inv in H.
    intuition.
  - intuition.
Qed.

Lemma LE_trans:
  forall t1 t2 t3,
  LE t1 t2 ->
  LE t2 t3 ->
  LE t1 t3.
Proof.
  intros.
  apply t_trans with (y:=t2).
  auto.
  auto.
Qed.

End ENABLED.

Require Rel.

Section HAS_SMALLEST.
Variable pm: phasermap.
Let IsA t := tid_In t pm.

Let wtid_le (t1:tid) (t2:tid) := LE pm t1 t2.

Let wtid_le_inv := LE_inv pm.

Variable wtid_le_dec:
  forall t1 t2,
  { LE pm t1 t2 } + { ~ LE pm t1 t2 }.

Let wtid_le_trans:
  forall t1 t2 t3,
  wtid_le t1 t2 ->
  wtid_le t2 t3 ->
  wtid_le t1 t3.
Proof.
  unfold wtid_le in *.
  apply LE_trans.
Qed.

Let wtid_has_smallest :=
  Rel.has_smallest tid IsA wtid_le (LE_inv pm) wtid_le_dec
  (LE_refl pm) wtid_le_trans.

Definition Smallest (t:tid) (ts:list tid)  :=
  In t ts /\
  forall t', In t' ts -> (~ LE pm t t' /\ ~ LE pm t' t) \/ LE pm t t'.

Theorem has_smallest:
  forall ts,
  ts <> nil ->
  Forall IsA ts ->
  exists t,
  Smallest t ts.
Proof.
  intros.
  destruct (wtid_has_smallest _ H H0) as (x, Hx).
  unfold Rel.Smallest in *.
  unfold Rel.Unrelated in *.
  unfold wtid_le in *.
  exists x.
  auto.
Qed.

Variable get_registered:
  forall (t:tid),
  exists ps, Registered pm t ps.

Variable tids: list tid.

Variable tids_def:
  forall t, In t tids <-> IsA t.

Let smallest_inv:
  forall t,
  Smallest t tids ->
  In t tids.
Proof.
  intros.
  unfold Smallest in *.
  intuition.
Qed.

(** XXX: add support for SO *)
Variable OnlySW :
  forall (ph:phaser) (t:tid) (v:taskview),
  Map_TID.MapsTo t v ph ->
  exists n, v = SW n true \/ v = WO n \/ exists w, (v = SO n w /\ w < n).

Variable Smallest_to_WaitPhase :
  forall t t' v v' p ph n n',
  Smallest t tids ->
  Map_PHID.MapsTo p ph pm ->
  Map_TID.MapsTo t v ph ->
  Map_TID.MapsTo t' v' ph ->
  WaitPhase v n ->
  WaitPhase v' n' ->
  n <= n'.

Lemma smallest_to_sync:
  forall t p ph,
  Smallest t tids ->
  Map_PHID.MapsTo p ph pm ->
  Sync ph t.
Proof.
  intros.
  remember (Map_TID.find t ph).
  symmetry in Heqo. 
  destruct o as [v|].
  * rewrite <- Map_TID_Facts.find_mapsto_iff in Heqo.
    destruct (wait_cap_or_sigonly v).
    - destruct (get_wait_phase v) as (n, Hwp).
      apply sync_wait with (v:=v) (w:=n); repeat intuition.
      unfold Await.
      intros t' v' n' Hmt' Hsp.
      destruct (OnlySW ph _ _ Hmt') as (n'', [Heq|[Heq|(w, (Heq, Hw))]]).
      + (* v' is SW *)
        subst.
        inversion Hsp.
        subst.
        (* WP of v' *)
        assert (Hwait : WaitPhase (SW n'' true) n''). {
          apply wait_phase_sw.
        }
        (* show that: n <= WP(v') *)
        assert (Hle : n <= n''). {
          apply Smallest_to_WaitPhase with
          (t:=t) (t':=t') (v:=v) (v':=(SW n'' true))
          (p:=p) (ph:=ph); repeat auto.
        }
        intuition.
      + (* v' is WO *)
        subst. (* absurd *)
        inversion Hsp.
      + (* v' is SO *)
        subst.
        inversion Hsp.
        subst.
        assert (Hwait : WaitPhase (SO n' w) w). {
          apply wait_phase_so.
        }
        (* show that: n <= WP(v') *)
        assert (Hle : n <= w). {
          apply Smallest_to_WaitPhase with
          (t:=t) (t':=t') (v:=v) (v':=(SO n' w))
          (p:=p) (ph:=ph); repeat auto.
       }
       intuition.
    - apply sync_so with (v:=v); repeat auto.
  * rewrite <- Map_TID_Facts.not_find_in_iff in Heqo.
    apply sync_skip.
    assumption.
Qed.
(*
Lemma smallest_to_reduce:
  forall t p ph v,
  Smallest t tids ->
  Map_PHID.MapsTo p ph pm ->
  Map_TID.MapsTo t v ph ->
  exists ph', PhReduce ph t WAIT ph'.
Proof.
  intros.
  exists (Map_TID.add t (wait v) ph).
  apply ph_reduce_wait; repeat auto.
Qed.

Lemma smallest_to_call_wait:
  forall t p ph v,
  Smallest t tids ->
  Map_PHID.MapsTo p ph pm ->
  Map_TID.MapsTo t v ph ->
  exists pm', Call pm t p WAIT pm'.
Proof.
  intros.
  assert (Hx : exists ph', PhReduce ph t WAIT ph'). {
    apply smallest_to_reduce with (p:=p) (v:=v); repeat auto.
  }
  destruct Hx as (ph', Hred).
  exists (Map_PHID.add t ph' pm).
  apply call_def with (ph:=ph).
  assumption.
  assumption.
Qed.*)

Theorem has_unblocked:
  tids <> nil ->
  exists t, In t tids /\
  exists pm', Reduce pm t WAIT_ALL pm'.
Proof.
  intros.
  assert (Hisa : Forall IsA tids). {
    apply Forall_forall.
    intros.
    apply tids_def.
    assumption.
  }
  assert (Hsmall := has_smallest _ H Hisa).
  destruct Hsmall as (t, Hsmall).
  exists t.
  intuition.
  exists (mapi t wait pm).
  apply reduce_wait_all.
  intros.
  apply smallest_to_sync with (p:=p) ; repeat auto.
Qed.
End HAS_SMALLEST.

Require Import PairUtil.

Section LE_DEC.
Variable pm:phasermap.

Let map_phid_in:
  forall p,
  { Map_PHID.In p pm } + { ~ Map_PHID.In p pm }.
Proof.
  intros.
  remember (Map_PHID.mem p pm).
  symmetry in Heqb.
  destruct b.
  - apply Map_PHID_Facts.mem_in_iff in Heqb.
    intuition.
  - apply Map_PHID_Facts.not_mem_in_iff in Heqb.
    intuition.
Qed.

Let map_tid_in:
  forall t (ph:phaser),
  { Map_TID.In t ph } + { ~ Map_TID.In t ph }.
Proof.
  intros.
  remember (Map_TID.mem t ph).
  symmetry in Heqb.
  destruct b.
  - apply Map_TID_Facts.mem_in_iff in Heqb.
    intuition.
  - apply Map_TID_Facts.not_mem_in_iff in Heqb.
    intuition.
Qed.

Lemma ph_diff_dec:
  forall ph t t',
  { exists z, ph_diff ph t t' z } + { ~ exists z, ph_diff ph t t' z }.
Proof.
  intros.
  unfold ph_diff.
  destruct (map_tid_in t ph).
  - destruct (map_tid_in t' ph).
    + apply Map_TID_Extra.in_to_mapsto in i.
      apply Map_TID_Extra.in_to_mapsto in i0.
      left.
      destruct i as (v, Hmt).
      destruct i0 as (v', Hmt').
      destruct (get_wait_phase v) as (w, Hw).
      destruct (get_wait_phase v') as (w', Hw').
      exists (Z.of_nat w - Z.of_nat w')%Z.
      exists v.
      intuition.
      exists v'.
      intuition.
      exists w.
      intuition.
      exists w'.
      intuition.
    + right.
      intuition.
      destruct H as (z, (?, (?, (?, (Hmt, _))))).
      apply Map_TID_Extra.mapsto_to_in in Hmt.
      contradiction Hmt.
  - right.
    intuition.
    destruct H as (?, (?, (Hmt, _))).
    apply Map_TID_Extra.mapsto_to_in in Hmt.
    contradiction Hmt.
Qed.

Require Import SigUtil.

Section GET_DIFF.
Variable ph: phaser.
Variable t1: tid.
Variable t2: tid.

Definition get_diff_nil := { _:unit | diff ph t1 t2 = None }.

Definition get_diff_pos := { z | ph_diff ph t1 t2 z /\ ~ (z <= 0) % Z }.

Definition get_diff_ok := { z | ph_diff ph t1 t2 z /\ (z <= 0) % Z }.

Inductive get_diff_result : Type :=
  | GET_DIFF_NIL : get_diff_nil -> get_diff_result
  | GET_DIFF_POS : get_diff_pos -> get_diff_result
  | GET_DIFF_OK : get_diff_ok -> get_diff_result.

Lemma get_diff:
  get_diff_result.
Proof.
  remember (diff ph t1 t2).
  symmetry in Heqo.
  destruct o.
  - destruct (ZArith_dec.Z_le_dec z 0).
    + refine (GET_DIFF_OK (Sig_yes z)).
      intuition.
      apply diff_spec_1.
      assumption.
    + refine (GET_DIFF_POS (Sig_yes z)).
      intuition.
      apply diff_spec_1.
      assumption.
  - refine (GET_DIFF_NIL (Sig_yes tt)).
    assumption.
Defined.
End GET_DIFF.

Lemma ph_le_dec:
  forall ph t t', 
  { ph_le ph t t' } + { ~ ph_le ph t t' }.
Proof.
  intros.
  unfold ph_le.
  remember (get_diff ph t t').
  symmetry in Heqg.
  destruct g.
  - destruct g.
    right.
    intuition.
    destruct H as (?, (Hdiff, _)).
    assert (Hx := e).
    apply diff_none with (z:=x0) in Hx.
    contradiction Hx.
  - destruct g.
    right.
    intuition.
    destruct H as (z', (?, Hle)).
    destruct a as (?, Hle').
    assert (z' = x). {
      apply ph_diff_fun with (ph:=ph) (t:=t) (t':=t'); repeat assumption.
    }
    subst.
    apply Hle' in Hle.
    assumption.
  - destruct g.
    left.
    exists x.
    destruct a.
    intuition.
Qed.

Section PM_DIFF.
Variable t: tid.
Variable t': tid.

Definition ph_le_ok := { ph: phaser | ph_le ph t t' }.

Definition ph_le_error := { ph: phaser | ~ ph_le ph t t' }.

Inductive ph_le_result :=
  | PH_LE_OK : ph_le_ok -> ph_le_result
  | PH_LE_ERROR : ph_le_error -> ph_le_result.

Let as_ph_le (ph:phaser):
  ph_le_result.
Proof.
  destruct (ph_le_dec ph t t').
  - refine (PH_LE_OK (Sig_yes ph)).
    assumption.
  - refine (PH_LE_ERROR (Sig_yes ph)).
    assumption.
Defined.
  

Let map_ph_le : list ph_le_result :=
  map
  (
    fun e:(phid*phaser)%type => 
    let (p, ph) := e in
    as_ph_le ph
  )
  (Map_PHID.elements pm).

Lemma not_exists_to_forall:
  forall {A:Type} (P:A -> Prop),
  ~ (exists a, P a) ->
  forall a, ~ P a.
Proof.
  intros.
  intuition.
  apply H.
  exists a.
  assumption.
Qed.

Lemma no_wp_le_inv:
  ~ wp_le pm t t' <-> 
  (forall p ph, Map_PHID.MapsTo p ph pm -> ~ ph_le ph t t').
Proof.
  intros.
  split.
  -
    intuition.
    assert (Hx : wp_le pm t t'). {
      unfold wp_le.
      exists p; exists ph.
      intuition.
    }
    apply H; repeat auto.
  - intros.
    intuition.
    unfold wp_le in *.
    destruct H0 as (p, (ph, (Hmt, Hph))).
    apply H with (p:=p) (ph:=ph); repeat auto.
Qed.
(*
Let asd:
  forall ph_ex,
  In ph_ex map_ph_le ->
  exists p, Map_PHID.MapsTo p (Sig_take ph_ex) pm.

Let filter_ph_le : list ph_le_result := 
  filter
  (fun o:ph_le_result =>
    match o with
      | PH_LE_OK e => true
      | _ => false
    end
  )
  map_ph_le.

Definition pm_le : option ph_le_ok :=
  match filter_ph_le with
    | cons (PH_LE_OK r) _ => Some r
    | _ => None
  end.

Lemma pm_le_spec_1:
  forall r,
  pm_le = Some r ->
  wp_le pm t t'.
Proof.
  intros.
  destruct r.
  unfold wp_le.
  exists 

End PM_DIFF.
*)

Lemma wp_le_dec:
  forall t t',
  {wp_le pm t t'} + {~ wp_le pm t t'}.
Proof.
  intros.
  unfold wp_le.
  remember (Map_PHID.is_empty pm).
  symmetry in Heqb.
  destruct b.
  + rewrite <- Map_PHID_Facts.is_empty_iff in Heqb.
    right.
    intuition.
    destruct H as (p, (ph, (Hmt, Hle))).
    apply Map_PHID_Extra.empty_to_mapsto in Hmt; repeat auto.
  + 
Qed.
*)

Lemma LE_dec:
  forall t t',
  {LE pm t t'} + {~ LE pm t t'}.
Proof.
  intros.
  
  unfold LE.
  destruct (edge_dec _ H t t'); repeat intuition.
Qed.*)
End PM_DIFF.
End LE_DEC.


Section LE_DEC.
Variable pm:phasermap.

Definition edge (T:Type) := (T * T) % type.

Definition Edge (e:edge tid) := LE pm (fst e) (snd e).

Definition fgraph (T:Type) := list (edge T).

(** Predicate [PhaseDiff] holds when the following list represnts the LE relation. *)
Definition PhaseDiff (g:fgraph tid) :=
  forall e, In e g <-> Edge e.

Lemma edge_dec:
  forall g,
  PhaseDiff g ->
  forall t t',
  {In (t, t') g } + { ~ In (t, t') g }.
Proof.
  intros.
  apply in_dec.
  apply pair_eq_dec.
  apply TID.eq_dec.
Qed.

Lemma LE_dec:
  forall g,
  PhaseDiff g ->
  forall t t',
  {LE pm t t'} + {~ LE pm t t'}.
Proof.
  intros.
  unfold PhaseDiff in *.
  unfold Edge in *.
  assert (Hy := H (t, t')).
  simpl in Hy.
  destruct (edge_dec _ H t t'); repeat intuition.
Qed.
End LE_DEC.

Definition Fun (pm:phasermap) :=
  forall t1 t2 p p' ph ph' i i',
  Map_PHID.MapsTo p ph pm ->
  Map_PHID.MapsTo p' ph' pm ->
  ph_diff ph t1 t2 i ->
  ph_diff ph' t1 t2 i' ->
  i = i'.

Definition Trans (pm:phasermap) :=
  forall t1 t2 t3 p p' p'' ph ph' ph'' i i' i'',
  Map_PHID.MapsTo p ph pm ->
  Map_PHID.MapsTo p' ph' pm ->
  Map_PHID.MapsTo p'' ph'' pm ->
  ph_diff ph t1 t2 i ->
  ph_diff ph' t2 t3 i' ->
  ph_diff ph'' t1 t3 i'' ->
  (i + i')%Z = i''.

Definition WF (pm:phasermap) := Fun pm /\ Trans pm.

