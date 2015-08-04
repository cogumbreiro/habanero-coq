Require Import HJ.Progress.
Require Import HJ.Lang.
Require Import HJ.TransDiff.
Require Import HJ.Vars.
Require Import HJ.PhaseDiff.

Require Import Aniceto.Graphs.Core.
Require Import Aniceto.Pair.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.

Section PROGRESS.

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
    unfold WTaskIn in *.
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

Lemma pm_diff_mapi_right:
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
    unfold WTaskIn in *.
    contradiction H1.
  - inversion H1; subst; clear H1.
    apply Map_TID_Facts.add_neq_mapsto_iff in H2; repeat auto.
    rewrite Map_TID_Facts.add_mapsto_iff in H3.
    destruct H3 as [(?, ?)|(?,?)].
    + subst.
      contradiction H; trivial.
    + assert (Heq : (Z.of_nat (wait_phase v1) - Z.of_nat ((wait_phase v)+1)%nat - 1 = 
              Z.of_nat (wait_phase v1) - Z.of_nat (wait_phase v)) % Z ). {
      

Lemma not_starts_with_inv {A:Type} (eq_dec: forall x y : A, {x = y} + {x <> y}):
  forall (v v1 v2:A) w,
  ~ StartsWith ((v1, v2) :: w) v ->
  v <> v1.
Proof.
  intros.
  assert (StartsWith ((v1, v2) :: w) v1). {
    auto using starts_with_def.
  }
  destruct (eq_dec v1 v); subst; (contradiction H0 || intuition).
Qed.

Lemma not_ends_with_inv {A:Type} (eq_dec: forall x y : A, {x = y} + {x <> y}):
  forall (v v1 v2:A),
  ~ EndsWith ((v1, v2) :: nil) v ->
  v <> v2.
Proof.
  intros.
  assert (EndsWith ((v1, v2) :: nil) v2). {
    eauto using end_nil, ends_with_def.
  }
  destruct (eq_dec v2 v); subst; (contradiction H0 || intuition).
Qed.

Lemma diff_sum_mapi:
  forall w t pm z,
  DiffSum (diff (mapi t wait pm)) w z ->
  ~ StartsWith w t ->
  ~ EndsWith w t ->
  DiffSum (diff pm) w z.
Proof.
  intros w.
  induction w.
  - intros.
    inversion H; subst.
    auto using diff_sum_nil.
  - intros.
    destruct a as (t1, t2).
    assert (t <> t1). {
        eauto using (not_starts_with_inv TID.eq_dec).
    }
    inversion H.
    + subst.
      apply diff_sum_pair.
      unfold diff in *.
      simpl in *.
      assert (t <> t2). {
        eauto using (not_ends_with_inv TID.eq_dec).
      }
      eauto using pm_diff_mapi.
    + subst.
      clear H.
      destruct (TID.eq_dec t t2).
      { subst.
        
Qed.

Lemma transdiff_mapi:
  forall t pm t1 t2 z,
  TransDiff tid (diff (mapi t wait pm)) t1 t2 z ->
  TransDiff tid (diff pm) t1 t2 z.
Proof.
  intros.
  inversion H; subst; clear H.
  apply walk2_mapi in H1.
  apply diff_sum_mapi in H0.
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
  eauto using H.
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

End Section.