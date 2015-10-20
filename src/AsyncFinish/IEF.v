Require Import HJ.AsyncFinish.Lang.
Require Import HJ.Vars.
Require Import Aniceto.Graphs.Bipartite.Bipartite.
Require Import Aniceto.Graphs.Graph.


Import RelNotations.
Local Open Scope finish_scope.

Inductive ChildIn (t:tid) (f:finish) : Prop :=
  in_def:
    forall a,
    Child t a f ->
    ChildIn t f.

Inductive IEF (t:tid) (f:finish) : Prop :=
  enclosing_def:
    (forall c, Sub c f -> ~ ChildIn t c) ->
    ChildIn t f ->
    IEF t f.

Inductive IEFPath (f:finish) (t:tid): list tid -> Prop :=
  | ief_path_eq:
     IEF t f ->
     IEFPath f t nil
   | ief_path_cons:
     forall t' f' l,
     IEFPath f' t l ->
     Child t' (Blocked f') f ->
     IEFPath f t (t'::l).
