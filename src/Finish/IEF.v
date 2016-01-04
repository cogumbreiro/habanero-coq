Require Import HJ.Finish.Lang.
Require Import HJ.Vars.

Set Arguments Implicit.

Section IEF.
  Import Finish.Lang.FinishNotations.
  Local Open Scope finish_scope.

  Inductive IEF (t:tid) (f:finish) : Prop :=
    ief_def:
      (forall c, Sub c f -> ~ In t c) ->
      Registered t f ->
      IEF t f.

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