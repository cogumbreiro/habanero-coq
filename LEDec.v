Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.

Require Import Vars.
Require Import Lang.
Require Import PhaseDiff.
Require Import PairUtil.

Require TransClosure.

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

Definition get_diff_nil := { _:unit | get_ph_diff ph t1 t2 = None }.

Definition get_diff_pos := { z | ph_diff ph t1 t2 z /\ ~ (z <= 0) % Z }.

Definition get_diff_ok := { z | ph_diff ph t1 t2 z /\ (z <= 0) % Z }.

Inductive get_diff_result : Type :=
  | GET_DIFF_NIL : get_diff_nil -> get_diff_result
  | GET_DIFF_POS : get_diff_pos -> get_diff_result
  | GET_DIFF_OK : get_diff_ok -> get_diff_result.

Lemma get_diff:
  get_diff_result.
Proof.
  remember (get_ph_diff ph t1 t2).
  symmetry in Heqo.
  destruct o.
  - destruct (ZArith_dec.Z_le_dec z 0).
    + refine (GET_DIFF_OK (Sig_yes z)).
      intuition.
      apply get_ph_diff_spec_1.
      assumption.
    + refine (GET_DIFF_POS (Sig_yes z)).
      intuition.
      apply get_ph_diff_spec_1.
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
  remember (get_diff ph t t').
  symmetry in Heqg.
  destruct g.
  - destruct g.
    right.
    intuition.
    inversion H; subst.
    assert (Hx := e).
    apply get_diff_none with (z:=z) in Hx.
    contradiction Hx.
  - destruct g.
    right.
    intuition.
    inversion H; subst.
    destruct a as (?, Hle').
    assert (z = x). {
      apply ph_diff_fun with (ph:=ph) (t:=t) (t':=t'); repeat assumption.
    }
    subst.
    apply Hle' in H1.
    assumption.
  - destruct g.
    left.
    destruct a.
    apply ph_le_def with (z:=x); repeat auto.
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
  destruct (Map_PHID_Extra.in_choice pm_le).
  - left.
    destruct e as (p, H).
    apply Map_PHID_Extra.in_to_mapsto in H.
    destruct H as (ph, H).
    rewrite <- pm_le_spec in H.
    destruct H.
    apply wp_le_def_2 with (p:=p) (ph:=ph); repeat auto.
  - right.
    intuition.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    assert (Hx : Map_PHID.MapsTo p ph pm_le). {
      apply pm_le_spec.
      intuition.
      apply ph_le_def with (z:=z); auto.
    }
    assert (absurd: exists k, Map_PHID.In (elt:=phaser) k pm_le). {
      exists p.
      apply Map_PHID_Extra.mapsto_to_in with (e:=ph).
      assumption.
    }
    apply n in absurd.
    assumption.
Qed.
End PM_DIFF.

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

Lemma pm_tids_spec:
  forall t,
  In t pm_tids <->
  exists p ph, Map_PHID.MapsTo p ph pm /\ Map_TID.In t ph.
Proof.
  intros.
  split.
  - apply pm_tids_spec_1.
  - intros.
    destruct H as (p, (ph, (?, ?))).
    apply pm_tids_spec_2 with (p:=p) (ph:=ph); repeat auto.
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
  rewrite wp_le_alt in *.
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

Section PM_DIFF_FUNC.

Variable t1:tid.
Variable t2:tid.

Definition all_ph_diffs : phasermap :=
  Map_PHID_Extra.filter
    (fun (p:phid) (ph:phaser) =>
      match (get_ph_diff ph t1 t2) with
        | Some _ => true
        | _ => false
      end)
  pm.

Lemma pm_diff_dec:
  { exists z, pm_diff pm t1 t2 z} + {~  exists z, pm_diff pm t1 t2 z}.
Proof.
Admitted.
End PM_DIFF_FUNC.

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

Section LE_PM_DIFF.
Variable pm:phasermap.

Variable pm_diff_fun:
  forall t t' z z',
  pm_diff pm t t' z ->
  pm_diff pm t t' z' ->
  z = z'.

Variable pm_diff_trans:
  forall t1 t2 t3 z12 z23 z13,
  pm_diff pm t1 t2 z12 ->
  pm_diff pm t2 t3 z23 ->
  pm_diff pm t1 t3 z13 ->
  (z12 + z23 = z13) % Z.

Lemma LE_to_pm_diff:
  forall t1 t2,
  LE pm t1 t2 ->
  forall z,
  pm_diff pm t1 t2 z ->
  (z <= 0) %Z.
Admitted.
End LE_PM_DIFF.