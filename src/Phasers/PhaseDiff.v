(* begin hide *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.Relations.Relations.
Require Import Coq.Lists.List.
Require Import Aniceto.List.
Require Import Aniceto.Map.
Require Import Aniceto.ListSet.
Require Import HJ.Vars.
Require Import HJ.Phasers.Lang.

Open Scope Z.

(* end hide *)

Section PhDiff.

(**
  The task displacement over phasers is given by predicate [ph_diff] that given
  a phaser [ph], a task [t1], and a task [t2] yields some displacement [z].
  *)

Inductive ph_diff (ph:phaser): (tid * tid) -> Z -> Prop :=
  ph_diff_def:
    forall t1 t2 v1 v2,
    Map_TID.MapsTo t1 v1 ph ->
    Map_TID.MapsTo t2 v2 ph ->
    ph_diff ph (t1, t2) ((Z_of_nat (wait_phase v1)) - (Z_of_nat (wait_phase v2)))%Z.

(* begin hide *)
Hint Resolve ph_diff_def.
(* end hide *)

(** Function [get_ph_diff] implements  predicate [ph_diff]. *)

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

(* begin hide *)

Lemma get_ph_diff_spec_1:
  forall ph t1 t2 z,
  get_ph_diff ph t1 t2 = Some z ->
  ph_diff ph (t1, t2) z.
Proof.
  intros.
  unfold get_ph_diff in *.
  remember (Map_TID.find t1 ph).
  symmetry in Heqo.
  destruct o.
  - rewrite <- Map_TID_Facts.find_mapsto_iff in Heqo.
    remember (Map_TID.find t2 ph).
    symmetry in Heqo0.
    destruct o.
    + rewrite <- Map_TID_Facts.find_mapsto_iff in Heqo0.
      inversion H.
      auto.
    + inversion H.
  - inversion H.
Qed.

Lemma get_ph_diff_spec_2:
  forall ph t1 t2 z,
  ph_diff ph (t1, t2) z ->
  get_ph_diff ph t1 t2 = Some z.
Proof.
  intros.
  inversion H; subst; clear H.
  unfold get_ph_diff.
  rewrite Map_TID_Facts.find_mapsto_iff in H2, H4.
  rewrite H2, H4.
  auto.
Qed.

(* end hide *)

(** The main result for [ph_diff] is the proof of correctness. *)

Lemma get_ph_diff_spec:
  forall ph t1 t2 z,
  get_ph_diff ph t1 t2 = Some z <-> ph_diff ph (t1, t2) z.
Proof.
  intros.
  split.
  - apply get_ph_diff_spec_1.
  - apply get_ph_diff_spec_2.
Qed.

(* begin hide *)

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
        rewrite <- Map_TID_Facts.find_mapsto_iff in *.
        apply Map_TID_Extra.mapsto_to_in in Heqo1.
        apply Map_TID_Extra.mapsto_to_in in Heqo2.
        destruct H; contradiction H.
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
  forall z, ~ ph_diff ph (t, t') z.
Proof.
  intros.
  intuition.
  apply get_ph_diff_spec_2 in H0.
  rewrite H in H0.
  inversion H0.
Qed.

Lemma ph_diff_fun:
  forall ph t t' z z',
  ph_diff ph (t, t') z ->
  ph_diff ph (t, t') z' ->
  z = z'.
Proof.
  intros.
  apply get_ph_diff_spec_2 in H.
  apply get_ph_diff_spec_2 in H0.
  rewrite H in H0.
  inversion H0.
  trivial.
Qed.

(* end hide *)

(** The reflexive task displacement over a phaser is zero. *)

Lemma ph_diff_refl:
  forall t ph,
  Map_TID.In t ph ->
  ph_diff ph (t, t) 0.
Proof.
  intros.
  apply Map_TID_Extra.in_to_mapsto in H.
  destruct H as (v, H).
  assert (ph_diff ph (t, t) (Z.of_nat (wait_phase v) - Z.of_nat (wait_phase v))) by auto.
  assert ((Z.of_nat (wait_phase v) - Z.of_nat (wait_phase v)) = 0). { intuition. }
  rewrite H1 in *.
  assumption.
Qed.

(** The displacement between two tasks over a phaser is symmetric. *)

Lemma ph_diff_symm:
  forall ph t t' z,
  ph_diff ph (t, t') z ->
  ph_diff ph (t', t) (-z).
Proof.
  intros.
  inversion H; subst; clear H.
  remember (Z.of_nat (wait_phase v1)) as z1.
  remember (Z.of_nat (wait_phase v2)) as z2.
  assert (- (z1 - z2) = z2 - z1). { intuition. }
  rewrite H.
  subst.
  auto.
Qed.

(* begin hide *)

Lemma ph_diff_inv:
  forall ph t t' z,
  ph_diff ph (t, t') z ->
  Map_TID.In t ph /\ Map_TID.In t' ph.
Proof.
  intros.
  inversion H; subst; clear H.
  split.
  - exists v1.
    intuition.
  - exists v2.
    intuition.
Qed.

Lemma ph_diff_inv_left:
  forall ph t t' z,
  ph_diff ph (t, t') z ->
  Map_TID.In t ph.
Proof.
  intros.
  apply ph_diff_inv in H.
  intuition.
Qed.

Lemma ph_diff_inv_right:
  forall ph t t' z,
  ph_diff ph (t, t') z ->
  Map_TID.In t' ph.
Proof.
  intros.
  apply ph_diff_inv in H.
  intuition.
Qed.

Lemma ph_diff_refl_inv:
  forall ph t z,
  ph_diff ph (t, t) z ->
  z = 0 % Z.
Proof.
  intros.
  assert (ph_diff ph (t, t) 0). {
    apply ph_diff_inv_left in H.
    auto using ph_diff_refl.
  }
  eauto using ph_diff_fun.
Qed.

(* end hide *)

(**
  Any two tasks mentioned in a phaser are related with [ph_diff], that is
  there is a displacement between them.
  *)

Lemma ph_diff_total:
  forall ph t t',
  Map_TID.In t ph ->
  Map_TID.In t' ph ->
  exists z, ph_diff ph (t, t') z.
Proof.
  intros.
  apply Map_TID_Extra.in_to_mapsto in H.
  apply Map_TID_Extra.in_to_mapsto in H0.
  destruct H as (v, Hmt).
  destruct H0 as (v', Hmt').
  exists (Z.of_nat (wait_phase v) - Z.of_nat (wait_phase v')).
  auto.
Qed.

(**
  We are now ready to define a less-than operator over a phaser.
  *)

Inductive ph_le (ph : phaser) t t' : Prop :=
  ph_le_def :
    forall z,
    ph_diff ph (t,t') z ->
    (z <= 0)%Z ->
    ph_le ph t t'.

(* begin hide *)

Hint Resolve ph_le_def.

Section GET_PH_LE.
Variable ph:phaser.
Variable t1:tid.
Variable t2:tid.

Inductive ph_le_result :=
  | ph_le_result_ok_l : {z:Z | ph_diff ph (t1, t2) z /\ (z <= 0) % Z } -> ph_le_result
  | ph_le_result_ok_r : {z:Z | ph_diff ph (t2, t1) z /\ (z <= 0) % Z } -> ph_le_result
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

(* end hide *)

Lemma ph_le_refl:
  forall t ph,
  Map_TID.In t ph ->
  ph_le ph t t.
Proof.
  intros.
  apply ph_le_def with (z:=0%Z); intuition.
  auto using ph_diff_refl.
Qed.

Lemma ph_le_inv:
  forall t t' ph,
  ph_le ph t t' ->
  Map_TID.In t ph /\ Map_TID.In t' ph.
Proof.
  intros.
  inversion H; subst.
  eauto using ph_diff_inv.
Qed.

Lemma ph_le_inv_in:
  forall t t' ph,
  ph_le ph t t' ->
  Map_TID.In t ph /\ Map_TID.In t' ph.
Proof.
  intros.
  inversion H; subst.
  apply ph_diff_inv in H0.
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
  Map_TID.In t ph ->
  Map_TID.In t' ph ->
  { ph_le ph t t' } + { ph_le ph t' t }.
Proof.
  intros.
  remember (get_ph_le ph t t').
  destruct p.
  - left.
    destruct s as (z, (Hdiff, Hle)).
    eauto.
  - right.
    destruct s as (z, (Hdiff, Hle)).
    eauto.
  - destruct s.
    assert (False). {
      destruct o.
      + contradiction H.
      + contradiction H0.
    }
    inversion H1.
Qed.
End PhDiff.

Section PM_DIFF.
Variable pm:phasermap.

Inductive pm_diff e z: Prop :=
  pm_diff_def :
    forall p ph,
    Map_PHID.MapsTo p ph pm ->
    ph_diff ph e z ->
    pm_diff e z.

Hint Resolve pm_diff_def.

Lemma pm_diff_symm:
  forall t t' z,
  pm_diff (t, t') z ->
  pm_diff (t', t) (-z)%Z.
Proof.
  intros.
  inversion H; subst; clear H.
  eauto using ph_diff_symm.
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
  Map_PHID.MapsTo p ph pm /\ exists z, ph_diff ph (t1, t2) z.
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
  pm_diff (t1, t2) z.
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
  eauto.
Qed.

Lemma pm_diff_refl:
  forall t p ph,
  Map_PHID.MapsTo p ph pm ->
  Map_TID.In t ph ->
  pm_diff (t, t) 0.
Proof.
  intros.
  assert (ph_diff ph (t, t) 0). {
    auto using ph_diff_refl.
  }
  eauto.
Qed.

Lemma pm_diff_refl_inv:
  forall t z,
  pm_diff (t, t) z ->
  z = 0 % Z.
Proof.
  intros.
  inversion H; subst; clear H.
  eauto using ph_diff_refl_inv.
Qed.

Variable pm_diff_fun:
  forall e z z',
  pm_diff e z ->
  pm_diff e z' ->
  z = z'.

Lemma get_pm_diff_spec_2:
  forall z,
  pm_diff (t1, t2) z ->
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
      destruct o; intuition.
      symmetry in Heqo.
      apply get_diff_none with (z:=z) in Heqo.
      contradiction H1.
    }
    intuition.
  - destruct p as (p, ph).
    apply get_pm_diff_eq in Heql.
    destruct Heql as (?, (z', ?)).
    assert (pm_diff (t1, t2) z'). { eauto using pm_diff_def. }
    assert (z = z'). { eauto using pm_diff_fun. }
    subst.
    apply get_ph_diff_spec.
    trivial.
Qed.

Lemma get_pm_diff_spec:
  forall z,
  get_pm_diff = Some z <-> pm_diff (t1, t2) z.
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
Inductive wp_le t t' : Prop :=
  wp_le_def :
    forall z,
    pm_diff pm (t, t') z ->
    (z <= 0 ) % Z ->
    wp_le t t'.

Hint Resolve wp_le_def.


Lemma wp_le_spec:
  forall t t',
  wp_le t t' <-> (exists z : Z, pm_diff pm (t, t') z /\ (z <= 0)%Z).
Proof.
  intros.
  split.
  + intros.
    inversion H.
    subst.
    exists z.
    intuition.
  + intros.
    destruct H as (z, (Hd, Hle)).
    eauto.
Qed.

Lemma wp_le_def_2:
  forall p ph t t',
  Map_PHID.MapsTo p ph pm ->
  ph_le ph t t' ->
  wp_le t t'.
Proof.
  intros.
  inversion H0; subst.
  eauto using pm_diff_def.
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
    eauto using ph_le_def.
  - intros.
    destruct H as (p, (ph, (Hmt, Hle))).
    inversion Hle; subst.
    eauto using pm_diff_def.
Qed.

Lemma wp_le_refl:
  forall t,
  In t pm ->
  wp_le t t.
Proof.
  intros.
  apply wp_le_def with (z:=0%Z).
  - inversion H.
    eauto using pm_diff_def, ph_diff_refl.
  - intuition.
Qed.

Lemma wp_le_inv:
  forall t t',
  wp_le t t' ->
  In t pm /\ In t' pm.
Proof.
  intros.
  apply wp_le_alt in H.
  destruct H as (p, (ph, (Hmt, Hin))).
  apply ph_le_inv in Hin.
  destruct Hin.
  eauto using in_def.
Qed.

Lemma wp_le_total:
  forall p ph t t',
  Map_PHID.MapsTo p ph pm ->
  Map_TID.In t ph ->
  Map_TID.In t' ph ->
  { wp_le t t' } + { wp_le t' t }.
Proof.
  intros.
  destruct (ph_le_total _ _ _ H0 H1).
  + left.
    eauto using wp_le_def_2.
  + right.
    eauto using wp_le_def_2.
Qed.

Definition LE := clos_trans tid wp_le.

Lemma LE_refl:
  forall t,
  In t pm ->
  LE t t.
Proof.
  intros.
  unfold LE.
  auto using t_step, wp_le_refl.
Qed.

Lemma LE_inv:
  forall t t',
  LE t t' ->
  In t pm /\ In t' pm.
Proof.
  intros.
  unfold LE in H.
  induction H; repeat (eauto using wp_le_inv; intuition).
Qed.

Lemma LE_trans:
  forall t1 t2 t3,
  LE t1 t2 ->
  LE t2 t3 ->
  LE t1 t3.
Proof.
  intros.
  apply t_trans with (y:=t2); repeat auto.
Qed.

Lemma LE_total:
  forall p ph t t',
  Map_PHID.MapsTo p ph pm ->
  Map_TID.In t ph ->
  Map_TID.In t' ph ->
  { LE t t' } + { LE t' t }.
Proof.
  intros.
  unfold LE.
  destruct (wp_le_total _ _ _ _ H H0 H1); repeat (auto using t_step).
Qed.

End LE.
