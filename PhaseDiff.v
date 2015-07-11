Require Import Coq.ZArith.BinInt.
Require Import Coq.Relations.Relations.
Require Import Coq.Lists.List.
Require Import Vars.
Require Import ListUtil.
Require Import MapUtil.
Require Import Lang.
Require Import ListSetUtil.

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

Lemma wtask_in_inv:
  forall t ph,
  WTaskIn t ph ->
  Map_TID.In t ph.
Proof.
  intros.
  unfold WTaskIn in *.
  destruct H as (v, (Hmt, _)).
  apply Map_TID_Extra.mapsto_to_in in Hmt.
  assumption.
Qed.

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

Lemma ph_diff_inv_in:
  forall ph t t' z,
  ph_diff ph t t' z ->
  Map_TID.In t ph /\ Map_TID.In t' ph.
Proof.
  intros.
  destruct (ph_diff_inv _ _ _ _ H).
  apply wtask_in_inv in H0.
  apply wtask_in_inv in H1.
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

Lemma ph_le_inv_in:
  forall t t' ph,
  ph_le ph t t' ->
  Map_TID.In t ph /\ Map_TID.In t' ph.
Proof.
  intros.
  unfold ph_le in *.
  destruct H as (z, (H, Hdiff)).
  apply ph_diff_inv_in in H.
  intuition.
Qed.

Lemma ph_le_inv_in_left:
  forall t t' ph,
  ph_le ph t t' ->
  Map_TID.In t ph.
Proof.
  intros.
  apply ph_le_inv_in in H.
  intuition.
Qed.

Lemma ph_le_inv_in_right:
  forall t t' ph,
  ph_le ph t t' ->
  Map_TID.In t' ph.
Proof.
  intros.
  apply ph_le_inv_in in H.
  intuition.
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

Definition is_ph_le (p:phid) (ph:phaser) := if ph_le_dec ph t t' then true else false.

Definition pm_le := Map_PHID_Extra.filter is_ph_le pm.

Lemma pm_le_spec:
  forall p ph,
  Map_PHID.MapsTo p ph pm /\ ph_le ph t t' <-> Map_PHID.MapsTo p ph pm_le.
Proof.
  unfold pm_le.
  intros.
  rewrite Map_PHID_Extra.filter_spec.
  unfold is_ph_le.
  - intuition.
    + destruct (ph_le_dec ph t t').
      auto.
      contradiction H1.
    + destruct (ph_le_dec ph t t').
      assumption.
      inversion H1.
  - intuition.
Qed.

Lemma wp_le_dec:
  { wp_le pm t t' } + { ~ wp_le pm t t' }.
Proof.
  unfold wp_le.
  destruct (Map_PHID_Extra.in_choice pm_le).
  - left.
    destruct e as (p, H).
    apply Map_PHID_Extra.in_to_mapsto in H.
    destruct H as (ph, H).
    exists p; exists ph.
    apply pm_le_spec.
    assumption.
  - right.
    intuition.
    destruct H as (p, (ph, H)).
    apply pm_le_spec in H.
    assert (absurd: exists k, Map_PHID.In (elt:=phaser) k pm_le). {
      exists p.
      apply Map_PHID_Extra.mapsto_to_in with (e:=ph).
      assumption.
    }
    apply n in absurd.
    assumption.
Qed.
End PM_DIFF.

Require TransClosure.


(* Tasks registered with a phaser *)
Definition ph_tids (ph:phaser) := Map_TID_Extra.keys ph.

Lemma ph_tids_spec:
  forall ph t,
  In t (ph_tids ph) <->
  Map_TID.In t ph.
Proof.
  intros.
  unfold ph_tids in *.
  rewrite Map_TID_Extra.keys_spec; 
  repeat (intros; intuition).
Qed.

Definition pm_tids :=
  flat_map ph_tids (Map_PHID_Extra.values pm).

Lemma pm_tids_spec_1:
  forall t,
  In t pm_tids ->
  exists (p : Map_PHID.key) (ph : phaser), Map_PHID.MapsTo p ph pm /\ Map_TID.In t ph.
Proof.
  intros.
  unfold pm_tids in *.
  rewrite in_flat_map in H.
  destruct H as (ph, (Hmt, Hin)).
  rewrite ph_tids_spec in Hin.
  apply Map_PHID_Extra.values_spec in Hmt.
  destruct Hmt as (p, Hmt).
  exists p; exists ph.
  intuition.
Qed.

Lemma pm_tids_spec_2:
  forall p ph t,
  Map_PHID.MapsTo p ph pm ->
  Map_TID.In t ph ->
  In t pm_tids.
Proof.
  intros.
  unfold pm_tids in *.
  rewrite in_flat_map.
  exists ph.
  rewrite ph_tids_spec.
  intuition.
  apply Map_PHID_Extra.values_spec_2 with (k:=p).
  assumption.
Qed.

Lemma ph_le_in_pm_tids:
  forall p ph x y,
  Map_PHID.MapsTo p ph pm ->
  ph_le ph x y ->
  In x pm_tids /\ In y pm_tids.
Proof.
  intros.
  apply ph_le_inv_in in H0.
  destruct H0.
  split; repeat(
    apply pm_tids_spec_2 with (p:=p) (ph:=ph);
    assumption
  ).
Qed.

Lemma wp_le_in_pm_tids:
  forall x y,
  wp_le pm x y ->
  In x pm_tids /\ In y pm_tids.
Proof.
  intros.
  unfold wp_le in *.
  destruct H as (p, (ph, (Hmt, Hle))).
  apply ph_le_in_pm_tids with (p:=p) (ph:=ph); repeat auto.
Qed.

Definition product (t:tid) := map (fun t' => (t, t')) pm_tids.

Lemma wp_le_in_product:
  forall x y,
  wp_le pm x y ->
  In (x, y) (product x).
Proof.
  intros.
  unfold product.
  apply in_map.
  apply wp_le_in_pm_tids in H.
  intuition.
Qed.

Lemma in_product_inv_eq:
  forall x y z,
  In (x, y) (product z) ->
  x = z.
Proof.
  intros.
  unfold product in *.
  remember (fun t' : Map_TID.key => (z, t')) as f.
  rewrite in_map_iff in H.
  destruct H as (w, (Heq, Hin)).
  subst.
  inversion Heq.
  auto.
Qed.

Definition all_pairs : list (tid*tid)%type :=
  flat_map (fun t => product t) pm_tids.

Lemma all_pairs_spec_1:
  forall x y : tid,
  wp_le pm x y -> In (x, y) all_pairs.
Proof.
  intros.
  unfold all_pairs.
  rewrite in_flat_map.
  exists x.
  split.
  + apply wp_le_in_pm_tids with (y:=y); assumption.
  + apply wp_le_in_product; assumption.
Qed.

Definition wp_le_rel :=
  filter (fun (p:(tid*tid)%type) => let (t, t') := p in if wp_le_dec t t' then true else false) all_pairs.

Lemma wp_rels_spec:
  forall x y : tid,
  wp_le pm x y <-> In (x, y) wp_le_rel.
Proof.
  intros.
  unfold wp_le_rel.
  rewrite filter_In.
  split.
  - intros.
    destruct (wp_le_dec x y).
    + intuition.
      apply all_pairs_spec_1.
      assumption.
    + contradiction H.
  - intros.
    destruct H.
    destruct (wp_le_dec x y).
    + assumption.
    + inversion H0.
Qed.

Lemma LE_dec:
  forall t t',
  {LE pm t t'} + {~ LE pm t t'}.
Proof.
  unfold LE.
  intros.
  apply TransClosure.clos_trans_dec with (pairs:=wp_le_rel).
  apply wp_rels_spec.
Qed.

End LE_DEC.
