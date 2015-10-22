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

Inductive FID (f:finish) (t:tid): fid -> Prop :=
  | fid_nil:
     IEF t f ->
     FID f t nil
   | fid_cons:
     forall t' f' l,
     FID f' t l ->
     Child (t' <| f') f ->
     FID f t (t'::l) % list.
