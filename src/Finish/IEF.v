Require Import HJ.Finish.Lang.
Require Import HJ.Vars.

Set Arguments Implicit.

Section IEF.
  Import Finish.Lang.FinishNotations.
  Local Open Scope finish_scope.

  Inductive IEF (t:tid) (f:finish) : Prop :=
    | ief_ready:
      Child (!t) f ->
      IEF t f
    | ief_blocked:
      forall x,
      Child (t <| x) f ->
      ~ Registered t x ->
      IEF t f.

  (** [IEF] behaves as a function in the whole tree [f]. *)

  Inductive IEFFun f : Prop :=
    ief_fun_def:
      (forall x y t, x <= f -> IEF t x -> y <= f -> IEF t y -> x = y) ->
      IEFFun f.

  (** No ancestors *)

  Inductive UniqueIEF f : Prop :=
    unique_child_def:
      (forall x t y, x <= f -> IEF t x -> y < x -> ~ In t y) ->
      UniqueIEF f.
  Require Import HJ.Finish.Typesystem.

  Lemma child_registered_not_ief:
    forall x y t,
    IsMap x ->
    Child (t <| y) x ->
    Registered t y ->
    ~ IEF t x.
  Proof.
    intros.
    unfold not; intros.
    inversion H1; clear H1.
    inversion H2.
    - assert (n: Ready = Blocked y) by eauto using child_fun.
      inversion n.
    - assert (R: Blocked x0 = Blocked y) by eauto using child_fun.
      inversion R; subst; clear R.
      contradiction H4.
      eauto using registered_def.
  Qed.

  Lemma ief_inv_registered:
    forall t f,
    IEF t f ->
    Registered t f.
  Proof.
    intros.
    inversion H;
    eauto using registered_def.
  Qed.

  Lemma ief_dec f (I:IsMap f):
    forall t,
    { IEF t f } + { ~ IEF t f }.
  Proof.
    intros.
    destruct (lookup_ex t f).
    - destruct c as (a,?).
      destruct a as [|f'].
      + left; auto using ief_ready.
      + destruct (lookup_ex t f'). {
          destruct c0.
          right.
          eauto using child_registered_not_ief, registered_def.
        }
        destruct u.
        left.
        eauto using ief_blocked.
    - destruct u.
      right.
      unfold not; intros.
      contradiction n.
      auto using ief_inv_registered.
  Qed.

  Lemma ief_cons:
    forall t t' a l,
    IEF t (Node l) ->
    IEF t (Node ((t', a) :: l)).
  Proof.
    intros.
    inversion H; eauto using ief_ready, ief_blocked, child_cons.
  Qed.

  Lemma unique_ief:
    forall x t y f,
    UniqueIEF f ->
    x <= f ->
    IEF t x ->
    y < x -> ~ In t y.
  Proof.
    intros.
    inversion H; eauto.
  Qed.

  Lemma registered_to_ief:
    forall x t,
    Registered t x ->
    IEF t x \/ exists y, y < x /\ IEF t y.
  Proof.
    intros.
    induction x using finish_ind_strong.
    - apply registered_absurd_nil in H.
      inversion H.
    - apply registered_inv_cons in H.
      destruct H.
      rewrite <- H in *; clear H.
      + eauto using ief_ready, child_eq.
      + apply IHx in H; clear IHx.
        destruct H.
        * eauto using ief_cons.
        * destruct H as (?, (?, ?)).
          eauto using Rel.lt_cons.
    - apply registered_inv_cons in H.
      destruct H.
      + rewrite <- H in *; clear H.
        destruct (registered_dec t x). {
          apply IHx in r; clear IHx.
          destruct r as [?| (y, (?,?))].
          - right.
            exists x.
            eauto using lt_eq.
          - right.
            exists y.
            eauto using lt_trans, lt_eq.
        }
        eauto using ief_blocked, child_eq.
      + apply IHx0 in H; clear IHx0 IHx.
        destruct H.
        * eauto using ief_cons.
        * destruct H as (?, (?,?)).
          eauto using Rel.lt_cons.
  Qed.

  Lemma ief_in:
    forall t f,
    IEF t f ->
    In t f.
  Proof.
    intros.
    inversion H; eauto using in_child.
  Qed.

  Lemma leaf_to_ief:
    forall f,
    UniqueIEF f ->
    forall t,
    Child (!t) f ->
    IEF t f.
  Proof.
    intros.
    auto using ief_ready.
  Qed.
  
  Lemma unique_ief_le:
    forall x y,
    UniqueIEF x ->
    y <= x ->
    UniqueIEF y.
  Proof.
    intros.
    destruct H as (H).
    apply unique_child_def.
    intros a b; intros.
    assert (a <= x) by eauto using le_trans.
    eauto.
  Qed.

  (**
    [FIDPath f1 l f2] means that we can go from [f1] to [f2] according to path [l].
   *)
  Inductive FIDPath: finish -> fid -> finish -> Prop :=
    | fid_path_nil:
      forall f,
      FIDPath f nil f
    | fid_path_cons:
      forall t x y z l,
      FIDPath y l z ->
      Child (t <| x) y ->
      FIDPath x (t::l) % list z.

  Require Import HJ.Finish.Typesystem.

  Lemma check_leaf_to_ief:
    forall f t o,
    UniqueIEF f ->
    CheckLeaf f t o ->
    IEF t f.
  Proof.
    intros.
    inversion H0; subst; eauto using leaf_to_ief.
    eauto using ief_blocked.
  Qed.

  Lemma check_ief:
    forall x t o y,
    UniqueIEF x ->
    IEFFun x ->
    Check x t o ->
    y <= x ->
    IEF t y ->
    Check y t o.
  Proof.
    intros.
    inversion H1.
    assert (IEF t f') by
    eauto using check_leaf_to_ief, unique_ief_le.
    assert (f'=y) by (inversion H0; eauto).
    subst.
    eauto using le_refl, check_def, disjoint_le.
  Qed.    

End IEF.

Section Sem.
  Require Import Finish.LangExtra.
  Import Rel.Notations.

  Lemma ief_inv_cons_nil:
    forall t t' a,
    IEF t (Node ((t', a) :: nil)) ->
    t' = t.
  Proof.
    intros.
    inversion H.
    - apply child_inv_cons_nil in H0.
      inversion H0; trivial.
    - apply child_inv_cons_nil in H0.
      inversion H0; trivial.
  Qed.

  Lemma ief_put_3:
    forall t f t' a,
    IEF t (put f (t', a)) ->
    t <> t' ->
    IEF t f.
  Proof.
    intros.
    inversion H.
    - apply put_3 in H1; auto.
      eauto using ief_ready.
    - apply put_3 in H1; auto.
      eauto using ief_blocked.
  Qed.

  Lemma ief_remove_3:
    forall t f t',
    IEF t (remove f t') ->
    IEF t f.
  Proof.
    intros.
    inversion H.
    - apply remove_3 in H0.
      auto using ief_ready.
    - apply remove_3 in H0; auto.
      eauto using ief_blocked.
  Qed.

  Require Import HJ.Finish.Typesystem.

  Lemma ief_put_absurd_1:
   forall t x y,
     WFTasks (put y (t, Blocked x)) ->
     IEF t x ->
     ~ IEF t (put y (t, Blocked x)).
  Proof.
    intros.
    assert (Hc: Child (t, Blocked x) (put y (t, Blocked x))). {
      eauto using child_eq.
    }
    assert (Hlt: x < put y (t, Blocked x)). {
      eauto using lt_child.
    }
    unfold not; intros.
    inversion H1.
    - assert (Ha : Ready = Blocked x) by eauto using wf_tasks_child_fun.
      inversion Ha.
    - assert (Ha : Blocked x0 = Blocked x) by eauto using wf_tasks_child_fun.
      inversion Ha; subst; clear Ha.
      contradiction H3.
      eauto using ief_inv_registered.
  Qed.

End Sem.

Section LeToFid.
  Set Arguments Implicit.
  Require Finish.Find.
  Require Import Coq.Lists.List.
  Require Import Aniceto.List.
  Require Import Coq.Relations.Relation_Operators.
  Require Import Coq.Relations.Operators_Properties.
  Import Finish.Lang.FinishNotations.
  Local Open Scope finish_scope.

  Lemma le_to_fid_path:
    forall f f',
    f <= f' -> exists i, FIDPath f i f'.
  Proof.
    intros.
    destruct H.
    rewrite clos_rt_rt1n_iff in H.
    induction H.
    - eauto using fid_path_nil.
    - destruct H.
      destruct IHclos_refl_trans_1n as (l, Hx).
      exists (t::l).
      eauto using fid_path_cons.
  Qed.

  Lemma fid_path_to_le:
    forall x l y,
    FIDPath x l y ->
    x <= y.
  Proof.
    intros.
    induction H.
    - auto using le_def, rt_refl.
    - assert (x <= y)
      by eauto using le_def, rt_step, sub_def.
      eauto using le_trans.
  Qed.
End LeToFid.



