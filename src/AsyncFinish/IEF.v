Require Import HJ.AsyncFinish.Lang.
Require Import HJ.Vars.
Require Import Aniceto.Graphs.Bipartite.Bipartite.
Require Import Aniceto.Graphs.Graph.


Import FinishNotations.
Local Open Scope finish_scope.

Inductive IEF (t:tid) (f:finish) : Prop :=
  enclosing_def:
    (forall c, Sub c f -> ~ Registered t c) ->
    Registered t f ->
    IEF t f.

Inductive FIDPath (f:finish) : finish -> fid -> Prop :=
  | fid_path_nil:
     FIDPath f f nil
   | fid_path_cons:
     forall t' f' l f'',
     FIDPath f f' l ->
     Child (t' <| f') f'' ->
     FIDPath f f'' (t'::l) % list.

Inductive FID (f:finish) (i:fid) : Prop :=
  fid_def:
    forall f',
    FIDPath f' f i ->
    FID f i.