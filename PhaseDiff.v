Require Import Coq.ZArith.BinInt.
Require Import Coq.Relations.Relations.
Require Import Coq.Lists.List.
Require Import Vars.
Require Import ListUtil.
Require Import MapUtil.
Require Import Lang.

Definition ph_diff (ph:phaser) (t1:tid) (t2:tid) (z:Z)
  := exists v1, Map_TID.MapsTo t1 v1 ph /\
     exists v2, Map_TID.MapsTo t2 v2 ph /\
     exists n1, WaitPhase v1 n1 /\
     exists n2, WaitPhase v2 n2 /\
     ((Z_of_nat n1) - (Z_of_nat n2))%Z = z.

Definition WTaskIn (t:tid) (ph:phaser) :=
  exists v, Map_TID.MapsTo t v ph /\
  exists n, WaitPhase v n.

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
(*
Variable t_in_tid:
  forall t p ph v,
  Map_PHID.MapsTo p ph pm ->
  Map_TID.MapsTo t v ph ->
  In t tids.

Definition Diff (t:tid) (t':tid) (i:Z) :=
  exists p ph, Map_PHID.MapsTo p ph pm /\ ph_diff ph t t' i.

Definition RespectDiff :=
  forall t t' p ph pm i v v' n n',
  Diff t t' i ->
  Map_PHID.MapsTo p ph pm ->
  Map_TID.MapsTo t v ph ->
  Map_TID.MapsTo t' v' ph ->
  WaitPhase v n ->
  SignalPhase v' n' ->
  (((Z_of_nat n) - (Z_of_nat n')) >= i) % Z.

Variable get_diff:
  forall t t',
  In t tids ->
  In t' tids ->
  exists i, Diff t t' i.

Variable respect: RespectDiff.
*)

(** XXX: add support for SO *)
Variable OnlySW :
  forall (ph:phaser) (t:tid) (v:taskview),
  Map_TID.MapsTo t v ph ->
  exists n, v = SW n true \/ v = WO n.

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
  forall t p ph v,
  Smallest t tids ->
  Map_PHID.MapsTo p ph pm ->
  Map_TID.MapsTo t v ph ->
  Sync ph t.
Proof.
  intros.
  destruct (wait_phase_inv v) as (n, [Hv|Hv]).
  - apply sync_wait with (v:=v) (w:=n); repeat intuition.
    unfold Await.
    intros t' v' n' Hmt' Hsp.
    destruct (OnlySW ph _ _ Hmt') as (n'', [Heq|Heq]).
    + subst.
      inversion Hsp.
      subst.
      assert (Hwait : WaitPhase (SW n'' true) n''). {
        apply wait_phase_sw.
      }
      assert (Hle : n <= n''). {
        apply Smallest_to_WaitPhase with
        (t:=t) (t':=t') (v:=v) (v':=(SW n'' true))
        (p:=p) (ph:=ph); repeat auto.
      }
      intuition.
    + subst. (* absurd *)
      inversion Hsp.
  - subst.
    apply sync_so with (s:=n).
    assumption.
Qed.

Lemma smallest_to_reduce:
  forall t p ph v,
  Smallest t tids ->
  Map_PHID.MapsTo p ph pm ->
  Map_TID.MapsTo t v ph ->
  exists ph', PhReduce ph t WAIT ph'.
Proof.
  intros.
  exists (Map_TID.add t (wait v) ph).
  apply ph_reduce_wait; repeat auto.
  apply smallest_to_sync with (p:=p) (v:=v); repeat auto.
Qed.

Lemma smallest_to_call_wait:
  forall t p ph v,
  Smallest t tids ->
  Map_PHID.MapsTo p ph pm ->
  Map_TID.MapsTo t v ph ->
  exists pm', Call pm t p WAIT pm'.
Proof.
  intros.
  assert (Hx : exists ph', PhReduce ph t WAIT ph'). {
    apply smallest_to_reduce with (p:=p) (v:=v); repeat auto.
  }
  destruct Hx as (ph', Hred).
  exists (Map_PHID.add t ph' pm).
  apply call_def with (ph:=ph).
  assumption.
  assumption.
Qed.

Lemma call_wait_preserves_task_in:
  forall m m' t p p',
  TaskIn t p m ->
  Call m t p' WAIT m' ->
  TaskIn t p m'.
Proof.
  intros.
  inversion H0.
  subst.
  inversion H2.
  subst.
  unfold TaskIn in H.
  destruct H as (ph', (Hmt', Hin)).
Admitted.  

Lemma wait_preserves_task_in:
  forall t p pm' ps,
  TaskIn t p pm ->
  Foreach pm t ps WAIT pm' ->
  TaskIn t p pm'.
Proof.
  intros t p pm' ps.
  generalize pm'; clear pm'.
  induction ps.
  - intros.
    inversion H0.
    rewrite <- H5.
    assumption.
  - intros.
    inversion H0.
    subst.
    apply call_wait_preserves_task_in with (p:=p) in H8; repeat auto.
Qed.

Lemma has_unblocked_step:
  forall t ps,
  Smallest t tids ->
  TaskInMany t ps pm ->
  exists pm', Foreach pm t ps WAIT pm'.
Proof.
  intros.
  induction ps.
  - exists pm.
    apply foreach_nil.
  - unfold TaskInMany in *.
    assert (Hx : Forall (fun p : phid => TaskIn t p pm) ps). {
      rewrite Forall_forall in *.
      intros.
      apply H0.
      apply in_cons.
      assumption.
    }
    assert (Hin : TaskIn t a pm). {
      apply Forall_inv in H0.
      assumption.
    }
    apply IHps in Hx; clear IHps.
    destruct Hx as (pm', Hfor).
    rename a into p.
    assert (Hwait : exists pm'', Call pm' t p WAIT pm''). {
      unfold TaskIn in Hin.
      destruct Hin as (ph, (Hmt, Hin)).
      apply Map_TID_Extra.in_to_mapsto in Hin.
      destruct Hin as (v, Hmt2).
      assert (Hcall : exists pm', Call pm t p WAIT pm'). {
        apply smallest_to_call_wait with (ph:=ph) (v:=v); repeat auto.
      }
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
  intuition. {
    unfold Smallest in *; intuition.
  }
  destruct (get_registered t) as (ps, Hreg).
  assert (Hx : exists m', Foreach pm t ps WAIT m'). {
    inversion Hreg.
    subst.
    induction ps.
    - 
  induction ps. (* induction on the registered phasers *)
  - (* no registered phasers *)
    assert (Hforeach := foreach_nil pm t WAIT).
    exists pm.
    apply reduce_wait_all with (ps:=nil); repeat auto.
  - 
    assert (Hx := reduce_wait_all pm t pm ps Hreg).
Qed.
End HAS_SMALLEST.

Require Import PairUtil.

Section LE_DEC.
Variable pm:phasermap.

Definition edge (T:Type) := (T * T) % type.

Definition Edge (e:edge tid) := LE pm (fst e) (snd e).

Definition fgraph (T:Type) := list (edge T).

(** Predicate [PhaseDiff] holds when the following list represnts the LE relation. *)
Definition PhaseDiff (g:fgraph tid) :=
  forall e, In e g <-> Edge e.

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
  {LE pm t t'} + {~ LE pm t t'}.
Proof.
  intros.
  unfold PhaseDiff in *.
  unfold Edge in *.
  assert (Hy := H (t, t')).
  simpl in Hy.
  destruct (edge_dec _ H t t'); repeat intuition.
Qed.
End LE_DEC.

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

Definition WF (pm:phasermap) := Fun pm /\ Trans pm.

