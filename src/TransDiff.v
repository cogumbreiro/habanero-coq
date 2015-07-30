Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.

Require Import HJ.Vars.
Require Import HJ.Lang.
Require Import HJ.PhaseDiff.

Open Local Scope Z.

(**

The wait-phase difference [z] is defined for a pair of tasks t1 t2 such
that there exists a phaser ph for which its wait phase difference is [z], [WP(ph,t1) - WP(ph,t2) = z].

A well-formed phaser map respects a few properties:
 * for any task [t] registered in at least a phaser, we have that [t - t = 0]
 * for any two tasks [t1] and [t2], the wait-phase difference for any phaser is the same
   (so the wait-phase difference is a function).

*)

Section DIFF_SUM.

Variable A : Type.
Notation edge := (A * A) % type.
Variable diff: edge -> Z -> Prop.
Variable get_diff: edge -> option Z.
Variable get_diff_spec:
  forall e z,
  get_diff e = Some z <-> diff e z.

Lemma diff_fun:
  forall e z z',
  diff e z ->
  diff e z' ->
  z = z'.
Proof.
  intros.
  rewrite <- get_diff_spec in *.
  rewrite H in H0.
  inversion H0.
  trivial.
Qed.

(**
We say that the sequence of tasks [t1 t2 ... tn] has a sum of [s].

such that there exists a wait phase difference between any task [t_i] and
task [t_{i + 1}], where [1 <= i <= n] and the sum of all wait-phase
differences is [s].

*)
Inductive DiffSum : list edge -> Z -> Prop :=
  | diff_sum_nil:
    DiffSum nil 0
  | diff_sum_pair:
    forall t1 t2 z,
    diff (t1, t2) z ->
    DiffSum ((t1, t2) :: nil) z
  | diff_sum_cons:
    forall t1 t2 t3 w z s,
    DiffSum ((t2, t3) :: w) s ->
    diff (t1, t2) z ->
    DiffSum ((t1, t2) :: (t2, t3) :: w) (z + s).

Lemma diff_sum_nil_z:
  forall z,
  DiffSum nil z ->
  z = 0.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Definition as_z (o:option Z) :=
  match o with
  | Some z => z
  | None => 0
  end.

Definition diff_sum_accum (a:Z) (e:edge) : Z :=
  (as_z (get_diff e)) + a.

Lemma diff_sum_accum_0:
  forall e,
  diff_sum_accum 0 e = as_z (get_diff e).
Proof.
  intros.
  unfold diff_sum_accum.
  intuition.
Qed.

Definition diff_sum (l:list edge) : Z :=
  fold_left diff_sum_accum l 0.

Lemma diff_sum_0: diff_sum nil = 0.
Proof.
  unfold diff_sum.
  auto.
Qed.

Let fold_left_diff_sum_accum:
  forall w z,
  fold_left diff_sum_accum w z = z + fold_left diff_sum_accum w 0.
Proof.
  intros w.
  induction w.
  - intros.
    intuition.
  - intros.
    simpl.
    remember (diff_sum_accum z a) as s.
    rewrite diff_sum_accum_0 in *.
    remember ((as_z (get_diff a))) as s'.
    assert (Hx := IHw s).
    assert (Hy := IHw s').
    rewrite Hx.
    rewrite Hy.
    remember (fold_left diff_sum_accum w 0) as sum.
    unfold diff_sum_accum in Heqs.
    intuition.
Qed.

Lemma diff_sum_unfold:
  forall e w,
  diff_sum (e :: w) = (as_z (get_diff e)) + (diff_sum w).
Proof.
  intros.
  unfold diff_sum.
  simpl.
  remember (diff_sum_accum 0 e).
  unfold diff_sum_accum in Heqz.
  remember (get_diff e) as o.
  assert (as_z o = z). {
    intuition.
  }
  rewrite H in *.
  auto.
Qed.

Theorem diff_sum_spec:
  forall l z,
  DiffSum l z ->
  z = diff_sum l.
Proof.
  intros l.
  induction l.
  + intros; inversion H.
    auto.
  + intros.
    inversion H.
    - subst.
      unfold diff_sum.
      simpl.
      rewrite <- get_diff_spec in H3.
      remember (get_diff (t1, t2)).
      destruct o.
      * inversion H3; subst.
        rewrite diff_sum_accum_0.
        rewrite <- Heqo.
        auto.
      * inversion H3.
    - subst.
      simpl.
      apply IHl in H2; clear IHl H.
      rewrite <- get_diff_spec in H4.
      rewrite diff_sum_unfold.
      rewrite <- H2.
      rewrite H4.
      auto.
Qed.

Definition NegDiff (e:edge) := exists z, diff e z /\ z <= 0.

Lemma diff_sum_le_0:
  forall w z,
  Forall NegDiff w ->
  DiffSum w z ->
  z <= 0.
Proof.
  intros w.
  induction w.
  - intros.
    apply diff_sum_nil_z in H0.
    intuition.
  - intros.
    inversion H0.
    + subst.
      intuition.
      assert (Hin : In (t1, t2) ((t1, t2) :: nil)). {
        apply in_eq.
      }
      rewrite Forall_forall in H.
      destruct (H _ Hin) as (z', (?, ?)).
      assert (z' = z). {
        apply diff_fun with (t1, t2); repeat auto.
      }
      intuition.
   + subst. clear H0.
     assert (s <= 0). {
       inversion H; subst.
       apply IHw; repeat auto.
     }
     assert (z0 <= 0). {
       rewrite Forall_forall in H.
       assert (Hin : In (t1, t2) ((t1, t2) :: (t2, t3) :: w0)). {
         apply in_eq.
       }
       destruct (H _ Hin) as (z, (?,?)).
       assert (z0 = z). {
         apply diff_fun with (e:=(t1,t2)); repeat auto.
       }
       intuition.
    }
    intuition.
Qed.

Definition HasDiff e := exists z, diff e z.

Require Import Aniceto.Graphs.Core.

Lemma has_diff_to_diff_sum:
  forall w x y,
  Walk2 HasDiff x y w ->
  exists z : Z, DiffSum w z.
Proof.
  intros w.
  induction w.
  - intros. apply walk2_nil_inv in H.
    intuition.
  - intros.
    destruct w.
    + apply walk2_inv_pair in H.
      destruct H as (?, Hd).
      subst.
      unfold HasDiff in *.
      destruct Hd as (z, Hd).
      exists z.
      apply diff_sum_pair.
      auto.
    + apply walk2_inv in H.
      destruct H as (v1, (?, (?, ?))).
      destruct p as (v1', v2).
      assert (v1' = v1). {
        apply walk2_inv_cons in H1.
        destruct H1 as (?, (Heq, ?)).
        inversion Heq.
        reflexivity.
      }
      subst.
      apply IHw in H1.
      subst.
      destruct H1 as (s, Hs).
      unfold HasDiff in *.
      destruct H0 as (z, Hd).
      exists (z + s).
      apply diff_sum_cons; repeat auto.
Qed.

Lemma neg_diff_to_has_diff:
  forall e,
  NegDiff e ->
  HasDiff e.
Proof.
  intros.
  unfold NegDiff in *.
  unfold HasDiff in *.
  destruct H as (z, (H,_)).
  exists z; auto.
Qed.

Lemma walk2_neg_diff_to_has_diff:
  forall t1 t2 w,
  Walk2 NegDiff t1 t2 w ->
  Walk2 HasDiff t1 t2 w.
Proof.
  intros.
  apply walk2_impl with (E:=NegDiff); repeat auto.
  apply neg_diff_to_has_diff.
Qed.

Definition DiffSumDet :=
  forall t1 t2 w1 z1 w2 z2,
  DiffSum w1 z1 ->
  DiffSum w2 z2 ->
  Walk2 HasDiff t1 t2 w1 ->
  Walk2 HasDiff t1 t2 w2 ->
  z1 = z2.

Corollary diff_sum_det_alt (Hdet : DiffSumDet):
  forall t1 t2 w z,
  Walk2 HasDiff t1 t2 w ->
  DiffSum w z ->
  forall z',
  diff (t1, t2) z' ->
  z = z'.
Proof.
  intros.
  assert (Hw : Walk2 HasDiff t1 t2 ((t1,t2) :: nil)). {
    apply walk2_nil; repeat auto.
    unfold HasDiff; exists z'; auto.
  }
  assert (Hd : DiffSum ((t1, t2)::nil) z'). {
    apply diff_sum_pair.
    assumption.
  }
  apply Hdet with (t1:=t1) (t2:=t2) (w1:=w) (w2:=(t1,t2) :: nil); repeat auto.
Qed.

End DIFF_SUM.

Implicit Arguments DiffSum.
Implicit Arguments HasDiff.
Implicit Arguments NegDiff.
