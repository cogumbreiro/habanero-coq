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