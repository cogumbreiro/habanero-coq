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

Lemma ph_diff_def:
  forall (ph:phaser) (t1 t2:tid) (v1 v2:taskview) (n1 n2:nat),
  Map_TID.MapsTo t1 v1 ph ->
  Map_TID.MapsTo t2 v2 ph ->
  WaitPhase v1 n1 ->
  WaitPhase v2 n2 ->
  ph_diff ph t1 t2 ((Z_of_nat n1) - (Z_of_nat n2))%Z.
Proof.
  intros.
  unfold ph_diff.
  exists v1.
  intuition.
  exists v2.
  intuition.
  exists n1.
  intuition.
  exists n2.
  intuition.
Qed.

Definition get_ph_diff (ph:phaser) (t1:tid) (t2:tid) : option Z := 
  match Map_TID.find t1 ph with
    | Some v1 => 
      match Map_TID.find t2 ph with
        | Some v2 =>
          Some ((Z_of_nat (wait_phase v1)) - (Z_of_nat (wait_phase v2)))%Z
        | _ => None
      end
    | _ => None
  end.

Lemma get_ph_diff_spec_1:
  forall ph t1 t2 z,
  get_ph_diff ph t1 t2 = Some z ->
  ph_diff ph t1 t2 z.
Proof.
  intros.
  unfold get_ph_diff in *.
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

Lemma get_ph_diff_spec_2:
  forall ph t1 t2 z,
  ph_diff ph t1 t2 z ->
  get_ph_diff ph t1 t2 = Some z.
Proof.
  intros.
  unfold ph_diff in H.
  unfold get_ph_diff.
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

Lemma get_ph_diff_spec:
  forall ph t1 t2 z,
  get_ph_diff ph t1 t2 = Some z <-> ph_diff ph t1 t2 z.
Proof.
  intros.
  split.
  - apply get_ph_diff_spec_1.
  - apply get_ph_diff_spec_2.
Qed.

Lemma get_ph_diff_spec_none:
  forall ph t1 t2,
  get_ph_diff ph t1 t2 = None <-> (~ Map_TID.In t1 ph \/ ~ Map_TID.In t2 ph).
Proof.
  intros.
  unfold get_ph_diff.
  remember (Map_TID.find (elt:=taskview) t1 ph) as o1.
  symmetry in Heqo1.
  remember (Map_TID.find (elt:=taskview) t2 ph) as o2.
  symmetry in Heqo2.
  destruct o1.
  - destruct o2.
    + split.
      intros.
      * inversion H.
      * intros.
        destruct H.
        {
          apply Map_TID_Facts.find_mapsto_iff in Heqo1.
          apply Map_TID_Extra.mapsto_to_in in Heqo1.
          contradiction H.
        }
        {
          apply Map_TID_Facts.find_mapsto_iff in Heqo2.
          apply Map_TID_Extra.mapsto_to_in in Heqo2.
          contradiction H.
        }
    + split.
      * intros.
        right.
        apply Map_TID_Facts.not_find_in_iff.
        assumption.
      * trivial.
  - split.
    + intros.
      left.
      apply Map_TID_Facts.not_find_in_iff.
      assumption.
    + trivial.
Qed.
        
Lemma get_diff_none:
  forall ph t t',
  get_ph_diff ph t t' = None ->
  forall z, ~ ph_diff ph t t' z.
Proof.
  intros.
  intuition.
  apply get_ph_diff_spec_2 in H0.
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
  apply get_ph_diff_spec_2 in H.
  apply get_ph_diff_spec_2 in H0.
  rewrite H in H0.
  inversion H0.
  trivial.
Qed.

Definition WTaskIn (t:tid) (ph:phaser) := Map_TID.In t ph.

Lemma wtaskin_spec:
  forall t ph,
  WTaskIn t ph <-> Map_TID.In t ph.
Proof.
  intros.
  unfold WTaskIn in *.
  intuition.
Qed.

Lemma wtask_in_def:
  forall t ph,
  Map_TID.In t ph ->
  WTaskIn t ph.
Proof.
  intros.
  unfold WTaskIn.
  intuition.
Qed.

Lemma ph_diff_refl:
  forall t ph,
  WTaskIn t ph ->
  ph_diff ph t t 0.
Proof.
  intros.
  unfold ph_diff.
  rewrite wtaskin_spec in H.
  apply Map_TID_Extra.in_to_mapsto in H.
  destruct H as (v, H).
  exists v.
  intuition.
  exists v.
  intuition.
  destruct (get_wait_phase v) as (n,?).
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
  - exists v2.
    intuition.
Qed.

Lemma ph_diff_inv_in:
  forall ph t t' z,
  ph_diff ph t t' z ->
  Map_TID.In t ph /\ Map_TID.In t' ph.
Proof.
  intros.
  destruct (ph_diff_inv _ _ _ _ H).
  apply wtaskin_spec in H0.
  apply wtaskin_spec in H1.
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

Lemma ph_diff_total:
  forall ph t t',
  WTaskIn t ph ->
  WTaskIn t' ph ->
  exists z, ph_diff ph t t' z.
Proof.
  intros.
  unfold ph_diff.
  rewrite wtaskin_spec in *.
  apply Map_TID_Extra.in_to_mapsto in H.
  apply Map_TID_Extra.in_to_mapsto in H0.
  destruct H as (v, Hmt).
  destruct H0 as (v', Hmt').
  destruct (get_wait_phase v) as (n1, Hw1).
  destruct (get_wait_phase v') as (n2, Hw2).
  exists (Z.of_nat n1 - Z.of_nat n2)%Z .
  exists v.
  intuition.
  exists v'.
  intuition.
  exists n1.
  intuition.
  exists n2.
  intuition.
Qed.

Definition tid_In (t:tid) (pm:phasermap) :=
  exists p ph, Map_PHID.MapsTo p ph pm /\ WTaskIn t ph.

Inductive ph_le : phaser -> tid -> tid -> Prop :=
  ph_le_def :
    forall ph t1 t2 z,
    ph_diff ph t1 t2 z ->
    (z <= 0)%Z ->
    ph_le ph t1 t2.

Section GET_PH_LE.
Variable ph:phaser.
Variable t1:tid.
Variable t2:tid.

Inductive ph_le_result :=
  | ph_le_result_ok_l : {z:Z | ph_diff ph t1 t2 z /\ (z <= 0) % Z } -> ph_le_result
  | ph_le_result_ok_r : {z:Z | ph_diff ph t2 t1 z /\ (z <= 0) % Z } -> ph_le_result
  | ph_le_fail : {_:unit | ~ Map_TID.In t1 ph \/ ~ Map_TID.In t2 ph } -> ph_le_result.

Program Definition get_ph_le : ph_le_result := 
  match get_ph_diff ph t1 t2 with
    | Some z =>
      if ZArith_dec.Z_le_dec z 0%Z then
        ph_le_result_ok_l z
      else ph_le_result_ok_r (-z)%Z
    | _ => ph_le_fail tt
  end.
Next Obligation.
  intuition.
  symmetry in Heq_anonymous.
  rewrite get_ph_diff_spec in Heq_anonymous.
  assumption.
Defined.
Next Obligation.
  symmetry in Heq_anonymous.
  rewrite get_ph_diff_spec in Heq_anonymous.
  apply ph_diff_symm in Heq_anonymous.
  intuition.
Qed.
Next Obligation.
  remember (get_ph_diff ph t1 t2).
  destruct o.
  - assert (Hx := H z).
    contradiction Hx.
    trivial.
  - symmetry in Heqo.
    apply get_ph_diff_spec_none.
    assumption.
Qed.
End GET_PH_LE.

Lemma ph_le_refl:
  forall t ph,
  WTaskIn t ph ->
  ph_le ph t t.
Proof.
  intros.
  apply ph_le_def with (z:=0%Z).
  apply ph_diff_refl.
  assumption.
  intuition.
Qed.

Lemma ph_le_inv:
  forall t t' ph,
  ph_le ph t t' ->
  WTaskIn t ph /\ WTaskIn t' ph.
Proof.
  intros.
  inversion H; subst.
  apply ph_diff_inv with (z:=z).
  assumption.
Qed.

Lemma ph_le_inv_in:
  forall t t' ph,
  ph_le ph t t' ->
  Map_TID.In t ph /\ Map_TID.In t' ph.
Proof.
  intros.
  inversion H; subst.
  apply ph_diff_inv_in in H0.
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

Lemma ph_le_total:
  forall ph t t',
  WTaskIn t ph ->
  WTaskIn t' ph ->
  { ph_le ph t t' } + { ph_le ph t' t }.
Proof.
  intros.
  remember (get_ph_le ph t t').
  destruct p.
  - left.
    destruct s as (z, (Hdiff, Hle)).
    apply ph_le_def with (z:=z); repeat auto.
  - right.
    destruct s as (z, (Hdiff, Hle)).
    apply ph_le_def with (z:=z); repeat auto.
  - destruct s.
    assert (False). {
      unfold WTaskIn in *.
      destruct o.
      + contradiction H.
      + contradiction H0.
    }
    inversion H1.
Qed.

Section PM_DIFF.
Variable pm:phasermap.

Inductive pm_diff : tid -> tid -> Z -> Prop :=
  pm_diff_def :
    forall p ph t t' z,
    Map_PHID.MapsTo p ph pm ->
    ph_diff ph t t' z ->
    pm_diff t t' z.

Lemma pm_diff_symm:
  forall t t' z,
  pm_diff t t' z ->
  pm_diff t' t (-z)%Z.
Proof.
  intros.
  inversion H; subst; clear H.
  apply pm_diff_def with (p:=p) (ph:=ph); repeat auto.
  apply ph_diff_symm.
  assumption.
Qed.

Variable t1: tid.
Variable t2: tid.

Definition all_ph_diffs : phasermap :=
  Map_PHID_Extra.filter
    (fun (p:phid) (ph:phaser) =>
      match (get_ph_diff ph t1 t2) with
        | Some _ => true
        | _ => false
      end)
  pm.

Definition get_pm_diff : option Z :=
  match Map_PHID.elements all_ph_diffs with
    | (p, ph) :: _ => get_ph_diff ph t1 t2
    | _ => None
  end.

Lemma get_pm_diff_eq:
  forall p ph l,
  (p, ph) :: l = Map_PHID.elements (elt:=phaser) all_ph_diffs ->
  Map_PHID.MapsTo p ph pm /\ exists z, ph_diff ph t1 t2 z.
Proof.
  intros.
  assert (Hmt: Map_PHID.MapsTo p ph all_ph_diffs). {
    apply Map_PHID_Extra.in_elements_impl_maps_to.
    rewrite <- H.
    apply in_eq.
  }
  unfold all_ph_diffs in *.
  rewrite Map_PHID_Extra.filter_spec in Hmt. {
    destruct Hmt.
    intuition.
    remember (get_ph_diff ph t1 t2).
    destruct o.
    - symmetry in Heqo.
      rewrite get_ph_diff_spec in *.
      exists z.
      trivial.
    - inversion H1.
  }
  intuition.
Qed.

Lemma get_pm_diff_spec_1:
  forall z,
  get_pm_diff = Some z ->
  pm_diff t1 t2 z.
Proof.
  intros.
  unfold get_pm_diff in *.
  remember (Map_PHID.elements all_ph_diffs).
  destruct l.
  { inversion H. }
  destruct p as (p, ph).
  apply get_pm_diff_eq in Heql.
  destruct Heql as (?, _).
  apply get_ph_diff_spec in H.
  apply pm_diff_def with (p:=p) (ph:=ph); repeat auto.
Qed.

Variable pm_diff_fun:
  forall t t' z z',
  pm_diff t t' z ->
  pm_diff t t' z' ->
  z = z'.

Lemma get_pm_diff_spec_2:
  forall z,
  pm_diff t1 t2 z ->
  get_pm_diff = Some z.
Proof.
  intros.
  unfold get_pm_diff.
  remember (Map_PHID.elements all_ph_diffs).
  destruct l.
  - (* absurd case *)
    symmetry in Heql.
    apply Map_PHID_Props.elements_Empty in Heql.
    inversion H; subst; clear H.
    apply Map_PHID_Extra.empty_to_mapsto with (k:=p) (e:=ph) in Heql.
    unfold all_ph_diffs in *.
    rewrite Map_PHID_Extra.filter_spec in Heql. {
      remember (get_ph_diff ph t1 t2).
      destruct o.
      intuition.
      intuition.
      symmetry in Heqo.
      apply get_diff_none with (z:=z) in Heqo.
      contradiction H1.
    }
    intuition.
  - destruct p as (p, ph).
    apply get_pm_diff_eq in Heql.
    destruct Heql as (?, (z', ?)).
    assert (pm_diff t1 t2 z'). {
      apply pm_diff_def with (p:=p) (ph:=ph); repeat auto.
    }
    assert (z = z'). {
      apply pm_diff_fun with (t:=t1) (t':=t2); repeat auto.
    }
    subst.
    apply get_ph_diff_spec.
    trivial.
Qed.

Lemma get_pm_diff_spec:
  forall z,
  get_pm_diff = Some z <-> pm_diff t1 t2 z.
Proof.
  intros.
  split.
  - apply get_pm_diff_spec_1.
  - apply get_pm_diff_spec_2.
Qed.
End PM_DIFF.

Section LE.
Variable pm:phasermap.

(** Less-than-equals *)
Inductive wp_le : tid -> tid -> Prop :=
  wp_le_def :
    forall t t' z,
    pm_diff t t' z ->
    (z <= 0 ) % Z ->
    wp_le t t'.

Lemma wp_le_def_2:
  forall p ph t t',
  Map_PHID.MapsTo p ph pm ->
  ph_le ph t t' ->
  wp_le t t'.
Proof.
  intros.
  inversion H0; subst.
  apply wp_le_def with (z:=z); auto.
  apply pm_diff_def with (p:=p) (ph:=ph); repeat auto.
Qed.

Lemma wp_le_alt :
  forall t t',
  wp_le t t' <->
  exists p ph, Map_PHID.MapsTo p ph pm /\ ph_le ph t t'.
Proof.
  split.
  - intros.
    inversion H.
    subst.
    inversion H0.
    subst.
    exists p; exists ph.
    intuition.
    apply ph_le_def with (z:=z); repeat auto.
  - intros.
    destruct H as (p, (ph, (Hmt, Hle))).
    inversion Hle; subst.
    apply wp_le_def with (z:=z); repeat auto.
    apply pm_diff_def with (p:=p) (ph:=ph); repeat auto.
Qed.

Lemma wp_le_refl:
  forall t,
  tid_In t pm ->
  wp_le t t.
Proof.
  intros.
  apply wp_le_def with (z:=0%Z).
  - unfold tid_In in H.
    destruct H as (p, (ph, (Hmt, Hin))).
    apply pm_diff_def with (p:=p) (ph:=ph); auto.
    apply ph_diff_refl; auto.
  - intuition.
Qed.

Lemma wp_le_inv:
  forall t t',
  wp_le t t' ->
  tid_In t pm /\ tid_In t' pm.
Proof.
  intros.
  apply wp_le_alt in H.
  destruct H as (p, (ph, (Hmt, Hin))).
  apply ph_le_inv in Hin.
  unfold tid_In.
  split; repeat (exists p; exists ph; intuition).
Qed.

Lemma wp_le_total:
  forall p ph t t',
  Map_PHID.MapsTo p ph pm ->
  WTaskIn t ph ->
  WTaskIn t' ph ->
  { wp_le t t' } + { wp_le t' t }.
Proof.
  intros.
  destruct (ph_le_total _ _ _ H0 H1).
  + left.
    apply wp_le_alt.
    exists p.
    exists ph.
    intuition.
  + right.
    apply wp_le_alt.
    exists p.
    exists ph.
    intuition.
Qed.

Definition LE := clos_trans tid wp_le.

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

Lemma LE_total:
  forall p ph t t',
  Map_PHID.MapsTo p ph pm ->
  WTaskIn t ph ->
  WTaskIn t' ph ->
  { LE t t' } + { LE t' t }.
Proof.
  intros.
  unfold LE.
  destruct (wp_le_total _ _ _ _ H H0 H1).
  - left.
    apply t_step.
    assumption.
  - right.
    apply t_step.
    assumption.
Qed.

End LE.
