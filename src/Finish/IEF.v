Require Import HJ.Finish.Lang.
Require Import HJ.Vars.


Import FinishNotations.
Local Open Scope finish_scope.

Inductive IEF (t:tid) (f:finish) : Prop :=
  ief_def:
    (forall c, Sub c f -> ~ In t c) ->
    Registered t f ->
    IEF t f.

(**
  [FIDPath f1 l f2] means that we can go from [f1] to [f2] according to path [l].
 *)
Inductive FIDPath (f:finish) : fid -> finish -> Prop :=
  | fid_path_nil:
     FIDPath f nil f
  | fid_path_cons:
    forall t' f' l f'',
    FIDPath f l f' ->
    Child (t' <| f') f'' ->
    FIDPath f (t'::l) % list f''.
