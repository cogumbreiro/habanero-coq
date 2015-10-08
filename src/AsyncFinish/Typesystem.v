Require Import Coq.Lists.SetoidList.

Require Import HJ.Vars.
Require Import HJ.AsyncFinish.Lang.

Inductive IsMap : finish -> Prop :=
  is_map_def:
    forall l,
    NoDupA (Map_TID.eq_key (elt:=task)) l ->
    IsMap (Node l).

Lemma is_map_nil:
  IsMap (Node nil).
Proof.
  auto using NoDupA_nil, is_map_def.
Qed.

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

Require Import HJ.AsyncFinish.LangExtra.

Lemma in_to_ina:
  forall t a l, 
  ~ In t (Node l) ->
  ~ InA (Map_TID.eq_key (elt:=task)) (t, a) l.
Proof.
  intros.
  apply notin_spec in H.
  induction l.
  - intuition.
    inversion H0.
  - apply notin_inv in H.
    destruct a0 as (t', a').
    destruct H as  (?, (?, ?)).
    simpl in H0, H.
    unfold not.
    intros.
    inversion H2.
    + subst.
      apply Map_TID_Extra.eq_key_unfold in H4; auto.
    + subst.
      intuition.
Qed.

Lemma valid_impl_is_map:
  forall f,
  Valid f ->
  IsMap f.
Proof.
  intros f.
  induction f using finish_ind_strong.
  - intros.
    auto using is_map_nil.
  - intros.
    inversion H.
    subst.
    apply is_map_def.
    apply NoDupA_cons.
    + auto using in_to_ina.
    + apply IHf in H2.
      inversion H2.
      assumption.
  - intros.
    inversion H.
    subst.
    apply is_map_def.
    apply NoDupA_cons.
    + auto using in_to_ina.
    + apply IHf0 in H4.
      inversion H4.
      assumption.
Qed.
    