Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.

Require Import Aniceto.Pair.

Require Import HJ.Vars.
Require Import HJ.Lang.
Require Import HJ.PhaseDiff.
Require HJ.TransClosure.

Open Local Scope Z.

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
  destruct (map_tid_in t ph).
  - destruct (map_tid_in t' ph).
    + apply Map_TID_Extra.in_to_mapsto in i.
      apply Map_TID_Extra.in_to_mapsto in i0.
      left.
      destruct i as (v, Hmt).
      destruct i0 as (v', Hmt').
      exists (Z.of_nat (wait_phase v) - Z.of_nat (wait_phase v')).
      auto using ph_diff_def.
    + right.
      intuition.
      destruct H as (z, H).
      inversion H.
      apply Map_TID_Extra.mapsto_to_in in H1.
      contradiction H1.
  - right.
    intuition.
    destruct H as (?, H).
    inversion H.
    apply Map_TID_Extra.mapsto_to_in in H0.
    contradiction H0.
Qed.

Section GET_DIFF.
Require Import Aniceto.Sig.
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
    + refine (GET_DIFF_OK (Sig_yes z)); auto using get_ph_diff_spec_1.
    + refine (GET_DIFF_POS (Sig_yes z)); auto using get_ph_diff_spec_1.
  - refine (GET_DIFF_NIL (Sig_yes tt)); assumption.
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
    assert (z = x). { eauto using ph_diff_fun. }
    subst.
    apply Hle' in H1.
    assumption.
  - destruct g.
    left.
    destruct a.
    eauto.
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
    eauto using wp_le_def_2.
  - right.
    intuition.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    assert (Hx : Map_PHID.MapsTo p ph pm_le). {
      apply pm_le_spec.
      intuition.
      eauto.
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
  List.In t (ph_tids ph) <->
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
  List.In t pm_tids ->
  In t pm.
Proof.
  intros.
  unfold pm_tids in *.
  rewrite in_flat_map in H.
  destruct H as (ph, (Hmt, Hin)).
  rewrite ph_tids_spec in Hin.
  apply Map_PHID_Extra.values_spec in Hmt.
  destruct Hmt as (p, Hmt).
  eauto using in_def.
Qed.

Lemma pm_tids_spec_2:
  forall t,
  In t pm -> List.In t pm_tids.
Proof.
  intros.
  unfold pm_tids in *.
  rewrite in_flat_map.
  inversion H.
  exists ph.
  rewrite ph_tids_spec.
  intuition.
  eauto using Map_PHID_Extra.values_spec_2.
Qed.

Lemma pm_tids_spec:
  forall t,
  List.In t pm_tids <-> In t pm.
Proof.
  intros.
  split.
  - apply pm_tids_spec_1.
  - apply pm_tids_spec_2.
Qed.

Lemma in_dec:
  forall t,
  { In t pm } + { ~ In t pm }.
Proof.
  intros.
  destruct (List.in_dec TID.eq_dec t pm_tids).
  - left. apply pm_tids_spec. assumption.
  - rewrite pm_tids_spec in n.
    right.
    assumption.
Qed.

Lemma pm_tids_nonempty:
  pm_tids <> nil <-> exists t, In t pm.
Proof.
  intros.
  intuition.
  remember (pm_tids).
  destruct l.
  + contradiction H; trivial.
  + exists k.
    rewrite <- pm_tids_spec.
    rewrite <- Heql.
    auto with *.
  + destruct H as (t, Hin).
    rewrite <- pm_tids_spec in Hin.
    rewrite H0 in *.
    inversion Hin.
Qed.


Lemma ph_le_in_pm_tids:
  forall p ph x y,
  Map_PHID.MapsTo p ph pm ->
  ph_le ph x y ->
  List.In x pm_tids /\ List.In y pm_tids.
Proof.
  intros.
  apply ph_le_inv_in in H0.
  destruct H0.
  split; (
  apply pm_tids_spec;
  eauto using in_def).
Qed.

Lemma wp_le_in_pm_tids:
  forall x y,
  wp_le pm x y ->
  List.In x pm_tids /\ List.In y pm_tids.
Proof.
  intros.
  rewrite wp_le_alt in *.
  destruct H as (p, (ph, (Hmt, Hle))).
  eauto using ph_le_in_pm_tids.
Qed.

Definition product (t:tid) := map (fun t' => (t, t')) pm_tids.

Lemma wp_le_in_product:
  forall x y,
  wp_le pm x y ->
  List.In (x, y) (product x).
Proof.
  intros.
  unfold product.
  apply in_map.
  apply wp_le_in_pm_tids in H.
  intuition.
Qed.

Lemma in_product_inv_eq:
  forall x y z,
  List.In (x, y) (product z) ->
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
  wp_le pm x y -> List.In (x, y) all_pairs.
Proof.
  intros.
  unfold all_pairs.
  rewrite in_flat_map.
  exists x.
  split.
  + apply wp_le_in_pm_tids with (y:=y); assumption.
  + auto using wp_le_in_product.
Qed.

Definition wp_le_rel :=
  filter (fun (p:(tid*tid)%type) => let (t, t') := p in if wp_le_dec t t' then true else false) all_pairs.

Lemma wp_rels_spec:
  forall x y : tid,
  wp_le pm x y <-> List.In (x, y) wp_le_rel.
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
  eauto using TransClosure.clos_trans_dec, wp_rels_spec.
Qed.

End LE_DEC.

Section LE_PM_DIFF.
Require Import Aniceto.Graphs.Graph.
Require Import HJ.TransDiff.

Variable pm:phasermap.
Notation t_edge := (tid * tid) % type.
Let diff (e:t_edge) : Z -> Prop := pm_diff pm (fst e) (snd e).
Let get_diff (e:t_edge) : option Z := get_pm_diff pm (fst e) (snd e).

Variable trans_diff_fun:
  TransDiffFun tid diff.

Let pm_diff_fun:
  forall t1 t2 z z',
  pm_diff pm t1 t2 z ->
  pm_diff pm t1 t2 z' ->
  z = z'.
Proof.
  intros.
  eauto using trans_diff_fun_2.
Qed.

Let get_diff_spec :
  forall e z,
  get_diff e = Some z <-> diff e z.
Proof.
  intros.
  unfold diff, get_diff.
  destruct e.
  simpl.
  rewrite (get_pm_diff_spec pm t t0 pm_diff_fun).
  intuition.
Qed.

Lemma LE_to_walk:
  forall t1 t2,
  LE pm t1 t2 ->
  exists w,
  Walk2 (HasDiff diff) t1 t2 w /\ List.Forall (NegDiff diff) w /\
  exists z, DiffSum diff w z.
Proof.
  intros.
  unfold LE in *.
  rewrite clos_trans_iff_walk2 with (Edge:=NegDiff diff) in H.
  - destruct H as (w, H).
    exists w.
    intuition; eauto using walk2_neg_diff_to_has_diff, walk2_to_forall.
    apply walk2_neg_diff_to_has_diff in H; eauto using has_diff_to_diff_sum.
  - intros.
    unfold NegDiff.
    unfold diff.
    simpl.
    apply wp_le_spec.
Qed.

Lemma LE_to_pm_diff:
  forall t1 t2,
  LE pm t1 t2 ->
  forall z,
  pm_diff pm t1 t2 z ->
  (z <= 0) %Z.
Proof.
  intros.
  apply LE_to_walk in H.
  destruct H as (w, (Hd, (Hw, (z', Hn)))).
  assert (TransDiff tid diff t1 t2 z'). {
    eauto using trans_diff_def.
  }
  assert (z' = z). {
    symmetry.
    eauto using trans_diff_fun_1.
  }
  subst.
  eauto using diff_sum_le_0.
Qed.
End LE_PM_DIFF.
