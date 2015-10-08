Require Import Coq.Lists.SetoidList.

Require Import HJ.Vars.
Require Import HJ.AsyncFinish.Lang.

Definition IsMap := (NoDupA (Map_TID.eq_key (elt:=task))).

Inductive Valid: finish -> Prop :=
  | valid_nil:
    Valid (Node nil)
  | valid_cons_ready:
    forall t l,
    Valid (Node l) ->
    ~ In t (Node l) ->
    Valid (Node ((t,Ready)::l))
  | valid_cons_blocked:
    forall t f l,
    Valid f ->
    Valid (Node l) ->
    ~ In t (Node l) ->
    Valid (Node ((t,Blocked f)::l)).
