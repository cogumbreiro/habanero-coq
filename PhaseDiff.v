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

(** We now view the phase difference relation [LE] as a graph. 
    An edge of the graph is just a pair of two tasks. *)

Definition edge (T:Type) := (T * T) % type.

Definition Edge (e:edge tid) := LE (fst e) (snd e).

Definition fgraph (T:Type) := list (edge T).

(** Predicate [PhaseDiff] holds when the following list represnts the LE relation. *)
Definition PhaseDiff (g:fgraph tid) :=
  forall e, In e g <-> Edge e.

Definition EQ t t' := LE t t' /\ LE t' t.

Definition Unrelated t t' := (~ LE t t' /\ ~ LE t' t).

Lemma unrelated_symm:
  forall t t',
  Unrelated t t' ->
  Unrelated t' t.
Proof.
  intros.
  unfold Unrelated in *.
  intuition.
Qed.

Definition Enabled (t:tid) (ts:list tid) := 
  In t ts /\ forall t', In t' ts -> Unrelated t t' \/ LE t t'.

Require Import PairUtil.

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
  {LE t t'} + {~ LE t t'}.
Proof.
  intros.
  unfold PhaseDiff in *.
  unfold Edge in *.
  assert (Hy := H (t, t')).
  simpl in Hy.
  destruct (edge_dec _ H t t'); repeat intuition.
Qed.

Lemma has_enabled_step_eq:
  forall g x y ts,
  PhaseDiff g ->
  tid_In x pm ->
  LE y x ->
  In y ts ->
  Enabled y ts ->
  Enabled y (x :: ts).
Proof.
  intros.
  unfold Enabled in *.
  destruct H3 as (_, H3).
  intuition.
  inversion H4.
  - subst. intuition.
  - apply H3. intuition.
Qed.

Lemma has_enabled_step_le:
  forall g t t' ts,
  PhaseDiff g ->
  tid_In t pm ->
  Enabled t' ts ->
  LE t t' ->
  Enabled t (t::ts).
Proof.
  intros.
  unfold Enabled.
  intuition.
  rename t'0 into x.
  unfold Enabled in H1.
  destruct H1 as (_, H1).
  assert (Hx := H1 x).
  inversion H3.
  - subst.
    right.
    apply LE_refl.
    assumption.
  - apply Hx in H4. clear Hx H3 H1.
    destruct (LE_dec _ H t x).
    { intuition. }
    left.
    destruct H4.
    + unfold Unrelated in *.
      split. { intuition. }
      destruct H1.
      intuition.
      assert (LE x t'). {
        apply LE_trans with (t2:=t); repeat auto.
      }
      contradiction H5.
    + assert (LE t x). {
        apply LE_trans with (t2:=t'); repeat auto.
      }
      contradiction H3.
Qed.

Lemma has_enabled_step_unrelated:
  forall g x y ts,
  PhaseDiff g ->
  tid_In x pm ->
  In y ts ->
  Enabled y ts ->
  Unrelated x y ->
  Enabled y (x :: ts).
Proof.
  intros.
  unfold Enabled.
  intuition.
  inversion H4.
  - subst.
    left.
    apply unrelated_symm.
    assumption.
  - unfold Enabled in H2.
    destruct H2 as (_, H2).
    apply H2.
    assumption.
Qed.

Lemma has_enabled_step:
  forall g x y ts,
  PhaseDiff g ->
  tid_In x pm ->
  In y ts ->
  Enabled y ts ->
  exists t, In t (x :: ts) /\ Enabled t (x :: ts).
Proof.
  intros.
  destruct (LE_dec _ H y x).
  - exists y.
    intuition.
    apply has_enabled_step_eq with (g:=g); repeat auto.
  - destruct (LE_dec _ H x y).
    + exists x.
      split. { intuition. }
      apply has_enabled_step_le with (g:=g) (t':=y); repeat auto.
    + exists y.
      assert (Unrelated x y). {
        unfold Unrelated; intuition.
      }
      intuition.
      apply has_enabled_step_unrelated with (g:=g); repeat auto.
Qed.

Lemma has_enabled_simple:
  forall ts g,
  ts <> nil ->
  PhaseDiff g ->
  Wait ts ->
  exists t, In t ts /\ Enabled t ts.
Proof.
  intros ts g Hnil Hphasediff Hwait.
  induction ts.
  (* absurd *) {
    contradiction Hnil.
    auto.
  }
  destruct ts.
  - exists a.
    intuition.
    unfold Enabled.
    split. intuition.
    intros t' Hin.
    apply in_inv_eq in Hin.
    subst.
    right; apply LE_refl.
    apply wait_cons_inv_tid_In in Hwait.
    assumption.
  - assert (IHnil : t :: ts <> nil). {
      intuition. inversion H.
    }
    assert (IHwait : Wait (t :: ts)). {
      apply wait_cons_inv_decons in Hwait.
      assumption.
    }
    destruct (IHts IHnil IHwait) as (x, (Hin, Hen)); clear IHts IHnil IHwait.
    apply has_enabled_step with (g:=g) (y:=x); repeat auto.
    apply wait_cons_inv_tid_In in Hwait.
    assumption.
Qed.

End ENABLED.

