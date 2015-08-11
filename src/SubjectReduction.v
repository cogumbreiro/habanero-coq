Require Import HJ.Progress.
Require Import HJ.Lang.
Require Import HJ.TransDiff.
Require Import HJ.Vars.
Require Import HJ.PhaseDiff.

Require Import Aniceto.Graphs.Core.
Require Import Aniceto.Pair.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.

Section SR.

Lemma walk2_mapi:
  forall t pm t1 t2 w,
  Walk2 (HasDiff (diff (mapi t wait pm))) t1 t2 w ->
  Walk2 (HasDiff (diff pm)) t1 t2 w.
Admitted.

Lemma diff_sum_mapi_neq:
  forall w (t:tid) pm z,
  (forall e, In e w -> ~ pair_In t e) ->
  DiffSum (diff (mapi t wait pm)) w z ->
  DiffSum (diff pm) w z.
Admitted.

Lemma ph_diff_add:
  forall t t1 t2 v ph z,
  t <> t1 ->
  t <> t2 ->
  ph_diff (Map_TID.add t (wait v) ph) t1 t2 z ->
  ph_diff ph t1 t2 z.
Proof.
  intros.
  inversion H1.
  subst.
  apply Map_TID_Facts.add_neq_mapsto_iff in H2; repeat auto.
  apply Map_TID_Facts.add_neq_mapsto_iff in H3; repeat auto.
Qed.

Lemma pm_diff_mapi_neq:
  forall t t1 t2 z pm,
  pm_diff (mapi t wait pm) t1 t2 z ->
  t <> t1 ->
  t <> t2 ->
  pm_diff pm t1 t2 z.
Proof.
  intros.
  inversion H.
  subst.
  unfold mapi in *.
  apply Map_PHID_Facts.mapi_inv in H2.
  destruct H2 as (ph', (p', (?, (?,Hmt)))).
  subst.
  assert (ph_diff ph' t1 t2 z). {
    unfold apply in *.
    unfold update in *.
    destruct (Map_TID.find t ph');
    eauto using ph_diff_add.
  }
  eauto using pm_diff_def.
Qed.

Lemma pm_diff_mapi_inv:
  forall t pm t1 t2 z,
  pm_diff (mapi t wait pm) t1 t2 z ->
  exists p ph,
  Map_PHID.MapsTo p ph pm /\
  (
    (~ Map_TID.In t ph /\ ph_diff ph t1 t2 z)
    \/
    (exists v, Map_TID.MapsTo t v ph /\ ph_diff (Map_TID.add t (wait v) ph) t1 t2 z)
  ).
Proof.
  intros.
  unfold mapi in *.
  inversion H; subst; clear H.
  unfold apply in *.
  unfold update in *.
  apply Map_PHID_Facts.mapi_inv in H0.
  destruct H0 as (ph', (p', (?, (?,?)))).
  subst.
  remember (Map_TID.find t ph').
  symmetry in Heqo.
  exists p; exists ph'; intuition.
  destruct o as [v|].
  - inversion H1; subst; clear H1.
    right.
    exists v.
    assert (Map_TID.MapsTo t v ph'). {
      rewrite Map_TID_Facts.find_mapsto_iff; assumption.
    }
    intuition.
  - left.
    rewrite <- Map_TID_Facts.not_find_in_iff in Heqo.
    intuition.
Qed.

Lemma Z_add_to_succ:
  forall p,
  Pos.add p xH = Pos.succ p.
Proof.
  intros.
  destruct p; repeat auto.
Qed.

Lemma Z_of_nat_succ:
  forall (n:nat),
  Z.of_nat (S n) = ((Z.of_nat n) + 1) % Z.
Proof.
 intros.
 unfold Z.of_nat.
 destruct n.
 - auto.
 - simpl.
   rewrite Z_add_to_succ.
   trivial.
Qed.

Lemma pm_diff_mapi_right:
  forall t pm t1 z,
  t <> t1 ->
  pm_diff (mapi t wait pm) t1 t z ->
  pm_diff pm t1 t (z + 1).
Proof.
  intros.
  apply pm_diff_mapi_inv in H0.
  destruct H0 as (p, (ph, (Hmt, [(?,?)|(v,(?,?))]))).
  - apply ph_diff_inv_right in H1.
    contradiction H1.
  - inversion H1; subst; clear H1.
    apply Map_TID_Facts.add_neq_mapsto_iff in H2; repeat auto.
    rewrite Map_TID_Facts.add_mapsto_iff in H3.
    destruct H3 as [(?, ?)|(?,?)].
    + subst.
      unfold wait in *.
      simpl.
      assert (Heq : (Z.of_nat (wait_phase v1) - Z.of_nat ((wait_phase v)+1)%nat + 1 = 
              Z.of_nat (wait_phase v1) - Z.of_nat (wait_phase v)) % Z ). {
        remember (wait_phase v1) as n1.
        remember (wait_phase v) as n.
        remember (Z.of_nat n1) as z1.
        remember (Z.of_nat (n + 1)) as z_1.
        remember (Z.of_nat n) as z.
        assert (n + 1 % nat = S n). { intuition. }
        rewrite H3 in *; clear H3.
        assert (z_1 = (z + 1) % Z). {
        rewrite Z_of_nat_succ in *. intuition. }
        intuition.
     }
     rewrite Heq.
     eauto using pm_diff_def.
   + contradiction H1; trivial.
Qed.

Lemma pm_diff_mapi_left:
  forall t pm t2 z,
  t <> t2 ->
  pm_diff (mapi t wait pm) t t2 z ->
  pm_diff pm t t2 (z - 1).
Proof.
  intros.
  intros.
  apply pm_diff_mapi_inv in H0.
  destruct H0 as (p, (ph, (Hmt, [(?,?)|(v,(?,?))]))).
  - apply ph_diff_inv_left in H1.
    contradiction H1.
  - inversion H1; subst; clear H1.
    apply Map_TID_Facts.add_neq_mapsto_iff in H2; repeat auto.
    rewrite Map_TID_Facts.add_mapsto_iff in H3.
    destruct H3 as [(?, ?)|(?,?)].
    + subst.
      contradiction H; trivial.
    + assert (Heq : (Z.of_nat (wait_phase v1) - Z.of_nat ((wait_phase v)+1)%nat - 1 = 
              Z.of_nat (wait_phase v1) - Z.of_nat (wait_phase v)) % Z ). {
Admitted.

Lemma ph_diff_wait_in_inv:
  forall t t1 t2 ph z,
  ph_diff (apply t wait ph) t1 t2 z ->
  Map_TID.In t1 ph /\ Map_TID.In t2 ph.
Proof.
  intros.
  apply ph_diff_inv in H.
  destruct H.
  unfold apply in *.
  unfold update in *.
  remember (Map_TID.find t ph) as o; symmetry in Heqo.
  destruct o; intuition.
  - apply Map_TID_Facts.add_in_iff in H.
    destruct H; auto.
    subst.
    apply Map_TID_Facts.in_find_iff.
    intuition.
    rewrite H in Heqo.
    inversion Heqo.
  - apply Map_TID_Facts.add_in_iff in H0.
    destruct H0; auto.
    subst.
    apply Map_TID_Facts.in_find_iff.
    intuition.
    rewrite H0 in Heqo.
    inversion Heqo.
Qed.

Lemma pm_diff_mapi_inv_eq:
  forall pm t t',
  pm_diff (mapi t' wait pm) t t 0 ->
  pm_diff pm t t 0.
Proof.
  intros.
  inversion H.
  subst.
  unfold mapi in *.
  apply Map_PHID_Facts.mapi_inv in H0.
  destruct H0 as (ph', (p', (?, (?, Hmt)))).
  subst.
  assert (Map_TID.In t ph'). {
    eapply ph_diff_wait_in_inv in H1; intuition.
 }
 eauto using pm_diff_refl.
Qed.

Definition tid_eq_sig x y := if TID.eq_dec x y then 1%Z else 0%Z.

Lemma pm_diff_mapi_sig:
  forall t t1 t2 pm z,
  pm_diff (mapi t wait pm) t1 t2 z ->
  pm_diff pm t1 t2 (z - (tid_eq_sig t1 t) + (tid_eq_sig t2 t)).
Proof.
  intros.
  unfold tid_eq_sig.
  destruct (TID.eq_dec t1 t), (TID.eq_dec t2 t).
  - subst.
    assert (z = 0%Z). {
      eauto using pm_diff_refl_inv.
    }
    subst.
    assert((0 - 1 + 1 = 0) % Z). {
      intuition.
    }
    rewrite H0.
    eauto using pm_diff_mapi_inv_eq.
  - subst.
    assert ((z - 1 + 0 = z - 1) % Z). {
      intuition.
    }
    rewrite H0.
    eauto using pm_diff_mapi_left.
  - subst.
    assert ((z - 0 + 1 = z + 1) % Z). {
      intuition.
    }
    rewrite H0.
    eauto using pm_diff_mapi_right.
  - assert (Heq : (z - 0 + 0 = z) % Z). {
      intuition.
    }
    rewrite Heq.
    eauto using pm_diff_mapi_neq.
Qed.

Lemma diff_sum_mapi:
  forall w t t1 tn pm z,
  DiffSum (diff (mapi t wait pm)) w z ->
  StartsWith w t1 ->
  EndsWith w tn ->
  DiffSum (diff pm) w (z - (tid_eq_sig t1 t) + (tid_eq_sig tn t)).
Proof.
  intros w.
  induction w.
  { (* absurd case *)
    intros.
    inversion H; subst.
    apply ends_with_nil_inv in H1.
    inversion H1.
  }
  intros.
  destruct a as (t1', t2).
  assert (t1' = t1). { eauto using starts_with_eq. }
  destruct w.
  - subst.
    inversion H.
    subst.
    assert (t2 = tn). {
      eauto using ends_with_eq.
    }
    subst.
    apply pm_diff_mapi_sig in H5.
    auto using diff_sum_pair.
  - subst.
    destruct p as (t2', t3).
    inversion H; subst; clear H.
    rename t2' into t2.
    assert (StartsWith ((t2, t3) :: w) t2). {
      eauto using starts_with_def.
    }
    apply ends_with_inv in H1.
    assert ( DiffSum (diff pm) ((t2, t3) :: w) (s - tid_eq_sig t2 t + tid_eq_sig tn t)). {
      apply IHw; repeat auto.
    }
    apply pm_diff_mapi_sig in H9. (* invert diff_mapi *)
    simpl in *.
    assert (Heq: ((z0 + s - tid_eq_sig t1 t + tid_eq_sig tn t) =
          (z0 - tid_eq_sig t1 t + tid_eq_sig t2 t) +
          (s - tid_eq_sig t2 t + tid_eq_sig tn t)) % Z). { intuition. }
    rewrite Heq.
    auto using diff_sum_cons.
Qed.


Lemma transdiff_mapi:
  forall t pm t1 t2 z,
  TransDiff tid (diff (mapi t wait pm)) t1 t2 z ->
  TransDiff tid (diff pm) t1 t2 (z - (tid_eq_sig t1 t) + (tid_eq_sig t2 t)).
Proof.
  intros.
  inversion H; subst; clear H.
  apply walk2_mapi in H1.
  inversion H1; subst.
  apply diff_sum_mapi with (t1:=t1) (tn:=t2) in H0; repeat auto.
  eauto using trans_diff_def.
Qed.

Lemma simpl_sr:
  forall pm t,
  Valid pm ->
  Valid (mapi t wait pm).
Proof.
  intros.
  unfold Valid in *.
  unfold TransDiffFun in *.
  intros.
  apply transdiff_mapi in H0.
  apply transdiff_mapi in H1.
  assert (Hx := H _ _ _ _ H0 H1).
  intuition.
Qed.

Theorem sr :
  forall pm t pm',
  Valid pm ->
  Reduce pm t WAIT_ALL pm' ->
  Valid pm'.
Proof.
  intros.
  inversion H0; subst; clear H0.
  auto using simpl_sr.
Qed.

End SR.