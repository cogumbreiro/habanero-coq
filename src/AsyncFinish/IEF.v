Require Import HJ.AsyncFinish.Lang.
Require Import HJ.Vars.
Require Import Aniceto.Graphs.Bipartite.Bipartite.
Require Import Aniceto.Graphs.Graph.


Import FinishNotations.
Local Open Scope finish_scope.

Inductive ChildIn (t:tid) (f:finish) : Prop :=
  in_def:
    forall a,
    Child (t, a) f ->
    ChildIn t f.

Inductive IEF (t:tid) (f:finish) : Prop :=
  enclosing_def:
    (forall c, Sub c f -> ~ ChildIn t c) ->
    ChildIn t f ->
    IEF t f.

Inductive FID (f:finish) (t:tid): fid -> Prop :=
  | fid_nil:
     IEF t f ->
     FID f t nil
   | fid_cons:
     forall t' f' l,
     FID f' t l ->
     Child (t' <| f') f ->
     FID f t (t'::l) % list.
