Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FMapAVL.
Require Coq.FSets.FMapFacts.
Require Coq.FSets.FSetProperties.
Require Import Coq.ZArith.BinInt.

Require Import ListUtil.
Require Import MapUtil.

Module TID := Nat_as_OT.
Definition tid := TID.t.
Module TID_Facts := OrderedTypeFacts TID.
Module Set_TID := FSetAVL.Make TID.
Module Set_TID_Props := FSetProperties.Properties Set_TID.
Module Map_TID := FMapAVL.Make TID.
Module Map_TID_Facts := FMapFacts.Facts Map_TID.
Module Map_TID_Props := FMapFacts.Properties Map_TID.
Module Map_TID_Extra := MapUtil.MapUtil Map_TID.

Module PHID := Nat_as_OT.
Module Set_PHID := FSetAVL.Make PHID.
Module Map_PHID := FMapAVL.Make PHID.
Module Map_PHID_Facts := FMapFacts.Facts Map_PHID.
Module Map_PHID_Props := FMapFacts.Properties Map_PHID.
Module Map_PHID_Extra := MapUtil.MapUtil Map_PHID.

(* a phaser with just wait-phase *)
Definition phaser := Map_TID.t nat.

Definition ph_diff (ph:phaser) (t1:tid) (t2:tid) (z:Z)
  := exists n1, Map_TID.MapsTo t1 n1 ph /\
     exists n2, Map_TID.MapsTo t2 n2 ph /\
     ((Z_of_nat n1) - (Z_of_nat n2))%Z = z.

Lemma ph_diff_refl:
  forall t ph,
  Map_TID.In t ph ->
  ph_diff ph t t 0.
Proof.
  intros.
  unfold ph_diff.
  apply Map_TID_Extra.in_to_mapsto in H.
  destruct H as (n, Hmt).
  exists n.
  intuition.
  exists n.
  intuition.
Qed.

Lemma ph_diff_symm:
  forall ph t t' z,
  ph_diff ph t t' z ->
  ph_diff ph t' t (-z).
Proof.
  intros.
  unfold ph_diff in *.
  destruct H as (n1, (Hmt1, (n2, (Hmt2, H)))).
  exists n2; intuition.
  exists n1; intuition.
Qed.

Lemma ph_diff_inv:
  forall ph t t' z,
  ph_diff ph t t' z ->
  Map_TID.In t ph /\ Map_TID.In t' ph.
Proof.
  intros.
  unfold ph_diff in H.
  destruct H as (n1, (Hmt1, (n2, (Hmt2, Hz)))).
  apply Map_TID_Extra.mapsto_to_in in Hmt1.
  apply Map_TID_Extra.mapsto_to_in in Hmt2.
  intuition.
Qed.

Lemma ph_diff_inv_left:
  forall ph t t' z,
  ph_diff ph t t' z ->
  Map_TID.In t ph.
Proof.
  intros.
  apply ph_diff_inv in H.
  intuition.
Qed.

Lemma ph_diff_inv_right:
  forall ph t t' z,
  ph_diff ph t t' z ->
  Map_TID.In t' ph.
Proof.
  intros.
  apply ph_diff_inv in H.
  intuition.
Qed.  

Definition phasermap := Map_PHID.t (phaser).

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

Definition WF (pm:phasermap) :=
  Fun pm /\ Trans pm.

Definition tid_In (t:tid) (pm:phasermap) :=
  exists p ph, Map_PHID.MapsTo p ph pm /\ Map_TID.In t ph.

Definition tids_Dom (l:list tid) (pm:phasermap) :=
  forall t, In t l <-> tid_In t pm.

Definition ph_le (ph:phaser) (t1:tid) (t2:tid) :=
  exists (z:Z), ph_diff ph t1 t2 z /\ (z <= 0)%Z.

Lemma ph_le_refl:
  forall t ph,
  Map_TID.In t ph ->
  ph_le ph t t.
Proof.
  intros.
  unfold ph_le.
  exists 0%Z.
  intuition.
  apply ph_diff_refl.
  assumption.
Qed.

Lemma wp_le_eq_ph_diff:
  forall ph t t',
  (exists z, ph_diff ph t t' z) <-> (ph_le ph t t' \/ ph_le ph t' t).
Proof.
  unfold ph_le.
  intros.
  split.
  - intros.
    destruct H as (z, H).
    assert (Hz : (z <= 0 \/ (-z) <= 0)%Z). {
      omega.
    }
    destruct Hz.
    + left. exists z. auto.
    + right. exists (-z)%Z.
      apply ph_diff_symm in H.
      auto.
  - intros.
    destruct H.
    + destruct H as (z, (H1, H2)).
      exists z; auto.
    + destruct H as (z, (H1, H2)).
      exists (-z)%Z.
      apply ph_diff_symm in H1.
      assumption.
Qed.

Lemma ph_le_inv:
  forall t t' p ph pm,
  ph_le ph t t' ->
  Map_PHID.MapsTo p ph pm ->
  tid_In t pm /\ tid_In t' pm.
Proof.
  intros.
  unfold tid_In.
  unfold ph_le in H.
  destruct H as (z, (H, _)).
  split.
  - exists p; exists ph.
    intuition.
    apply ph_diff_inv_left in H.
    assumption.
  - exists p; exists ph.
    intuition.
    apply ph_diff_inv_right in H.
    assumption.
Qed.

Section ENABLED.
Variable pm:phasermap.
Parameter wf_pm: WF pm.

Require Import Coq.Relations.Relations.

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
  destruct H as (p, (ph, (Hmt, Hle))).
  apply ph_le_inv with (p:=p) (pm:=pm) in Hle.
  intuition.
  assumption.
Qed.

Lemma wp_le_inv_right:
  forall t t',
  wp_le t t' ->
  tid_In t' pm.
Proof.
  intros.
  apply wp_le_inv in H.
  intuition.
Qed.

Lemma wp_le_inv_left:
  forall t t',
  wp_le t t' ->
  tid_In t pm.
Proof.
  intros.
  apply wp_le_inv in H.
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

Definition LeastOf (t:tid) (ts:list tid) :=
  forall t', In t' ts -> LE t t'.

Lemma leastof_cons:
  forall t t' ts,
  LE t t' ->
  LeastOf t ts ->
  LeastOf t (t'::ts).
Proof.
  intros.
  unfold LeastOf in *.
  intros.
  rename t'0 into t''.
  inversion H1.
  - subst.
    assumption.
  - apply H0.
    assumption.
Qed.

Lemma leastof_trans:
  forall t t' ts,
  LeastOf t' ts ->
  LE t t' ->
  LeastOf t ts.
Proof.
  intros.
  unfold LeastOf in *.
  intros.
  rename t'0 into t''.
  apply H in H1; clear H.
  apply t_trans with (y:=t'); repeat auto.
Qed.

(** All tasks in [Tids ts] are waiting tasks. *)
Definition Wait (ts:list tid) :=
  forall t', In t' ts -> tid_In t' pm.

Lemma wait_in:
  forall t ts,
  Wait ts ->
  In t ts ->
  tid_In t pm.
Proof.
  intros.
  apply H in H0.
  assumption.
Qed.

Lemma wait_cons:
  forall t ts,
  tid_In t pm ->
  Wait ts ->
  Wait (t :: ts).
Proof.
  intros.
  unfold Wait in *.
  intros.
  inversion H1.
  - subst.
    assumption.
  - apply H0 in H2.
    assumption.
Qed.

Lemma wait_cons_inv_tid_In:
  forall t ts,
  Wait (t :: ts) ->
  tid_In t pm.
Proof.
  intros.
  assert (In t (t :: ts)). {
    apply in_eq.
  }
  apply wait_in with (t::ts); repeat auto.
Qed.

Lemma wait_cons_inv_decons:
  forall t ts,
  Wait (t :: ts) ->
  Wait ts.
Proof.
  intros.
  unfold Wait in *.
  intros.
  assert (In t' (t :: ts)). {
    apply in_cons.
    assumption.
  }
  apply H.
  assumption.
Qed.

Notation "'Sig_no'" := (False_rec _ _) (at level 42).
Notation "'Sig_yes' e" := (exist _ e _) (at level 42).
Notation "'Sig_take' e" :=
  (match e with Sig_yes ex => ex end) (at level 42).  

Lemma in_inv_eq:
  forall {A} (x y:A),
  In x (y :: nil) ->
  x = y.
Proof.
  intros.
  inversion H.
  auto.
  inversion H0.
Qed.

Lemma in_inv_eq_2:
  forall {A} (x y:A),
  In x (y :: y :: nil) ->
  x = y.
Proof.
  intros.
  inversion H.
  auto.
  apply in_inv_eq.
  auto.
Qed.

Definition LE_Comparable (t t':tid) :=
  LE t t' \/ LE t' t.


Lemma le_comparable_refl:
  forall t,
  tid_In t pm ->
  LE_Comparable t t.
Proof.
  intros.
  unfold LE_Comparable.
  left.
  apply LE_refl.
  assumption.
Qed.

Lemma le_comparable_symm:
  forall t t',
  LE_Comparable t t' ->
  LE_Comparable t' t.
Proof.
  intros.
  unfold LE_Comparable in *.
  intuition.
Qed.

Definition TotalSet (ts:list tid) :=
  forall t t',
  In t ts ->
  In t' ts ->
  LE_Comparable t' t.

Lemma totalset_cons:
  forall t ts,
  tid_In t pm ->
  (forall t', In t' ts -> LE_Comparable t t') ->
  TotalSet ts ->
  TotalSet (t :: ts).
Proof.
  intros.
  unfold TotalSet.
  intros.
  rename t0 into x.
  inversion H2.
  - subst.
    inversion H3.
    + subst.
      apply le_comparable_refl.
      assumption.
    + apply le_comparable_symm. auto.
  - inversion H3.
    + subst.
      apply H0.
      assumption.
    + unfold TotalSet in *.
      apply H1; repeat auto.
Qed.

Definition LE_total:
  forall t t' ts,
  TotalSet ts ->
  In t ts ->
  In t' ts ->
  LE_Comparable t t'.
Proof.
  intros.
  apply (H _ _ H1 H0).
Qed.

Theorem find_leastof:
  forall ts all,
  Wait ts ->
  incl ts all ->
  TotalSet all ->
  ts <> nil ->
  exists t,
  In t ts /\ LeastOf t ts.
Proof.
  intros.
  induction ts.
  contradiction H2; auto.
  (* there is no case empty. *)
  destruct ts.
  - (* Case where tids = (x :: nil) *)
    exists a.
    assert (tid_In a pm). {
      apply wait_cons_inv_tid_In with (ts:=nil).
      intuition.
    }
    split.
    + apply in_eq.
    + unfold LeastOf.
      intros.
      apply in_inv_eq in H4; subst.
      apply t_step.
      apply wp_le_refl.
      assumption.
  - (* Inductive case: *)
    assert (Hin := H).
    apply wait_cons_inv_tid_In in Hin.
    apply wait_cons_inv_decons in H.
    assert (Htids := H).
    apply IHts in H; clear IHts. (* apply induction *)
    + destruct H as (small_t, (Hsmall_t_in,small_t_le)). (* Destroy induction *)
      assert (Hle : LE a small_t \/ LE small_t a). {
        apply LE_total with (ts:=all);
        repeat (auto; intuition).
      }
      destruct Hle.
      * exists a.
        intuition.
        apply leastof_cons.
        apply LE_refl.
        assumption.
        apply leastof_trans with (t':=small_t); repeat auto.
      * exists small_t.
        intuition.
        apply leastof_cons.
        assumption.
        assumption.
   + unfold incl in *.
     intros.
     apply H0.
     apply in_cons.
     assumption.
   + intuition. inversion H3.
Qed.

Definition wp_le_Comparable t t' :=
  wp_le t t' \/ wp_le t' t.

Lemma wp_le_comparable_inv_right:
  forall t t',
  wp_le_Comparable t t' ->
  tid_In t' pm.
Proof.
  intros.
  unfold wp_le_Comparable in *.
  intuition.
  - apply wp_le_inv_right in H0.
    assumption.
  - apply wp_le_inv_left in H0.
    assumption.
Qed.

End ENABLED.
        
        
        
