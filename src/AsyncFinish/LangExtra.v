Require Import Coq.Lists.List.

Require Import HJ.Vars.
Require Import HJ.AsyncFinish.Lang.

Fixpoint NotIn (t:tid) (f:finish) : Prop :=
  match f with
   | Node l =>
     (fix aux (l:list l_task) : Prop :=
       match l with
       | (t',a) :: l =>
         t <> t' /\ aux l /\
         (match a with
         | Ready => True
         | Blocked f => NotIn t f
         end)
       | nil => True
       end
     ) l
  end.

Lemma notin_spec_1:
  forall f t,
  NotIn t f ->
  ~ In t f.
Proof.
  intros.
  induction f using finish_ind_strong.
  - eauto using in_leaf_absurd.
  - simpl in H.
    destruct H as (?, (?, _)).
    intuition.
    apply in_inv_cons in H1.
    destruct H1 as [?|[(f,(?,?))|?]].
    + contradiction H.
    + inversion H1.
    + contradiction H2.
  - simpl in H.
    destruct H as (?, (?, ?)).
    intuition.
    apply in_inv_cons in H2.
    destruct H2 as [?|[(f',(?,?))|?]].
    + contradiction H.
    + inversion H2; subst; rename f' into  f; clear H2.
      contradiction H5.
    + contradiction H2.
Qed.

Lemma notin_spec_2:
  forall f t,
  ~ In t f ->
  NotIn t f.
Proof.
  intros.
  induction f using finish_ind_strong.
  - simpl. trivial.
  - simpl.
    split.
    + destruct (TID.eq_dec t t0).
      subst.
      contradiction H.
      apply in_eq.
      assumption.
    + split; trivial.
      assert (Hr : (fix aux (l0 : list l_task) : Prop :=
      match l0 with
      | nil => True
      | (t', a) :: l2 =>
        t <> t' /\
        aux l2 /\
        match a with
        | Ready => True
        | Blocked f => NotIn t f
        end
      end) l = NotIn t (Node l)). {
        auto.
      }
      rewrite Hr; clear Hr.
      apply IHf.
      intuition.
      contradiction H.
      auto using in_cons_rhs.
  - simpl.
    split.
    + destruct (TID.eq_dec t t0).
      subst.
      contradiction H.
      apply in_eq.
      assumption.
    + split.
      * assert (Hr : (fix aux (l0 : list l_task) : Prop :=
        match l0 with
        | nil => True
        | (t', a) :: l2 =>
          t <> t' /\
          aux l2 /\
          match a with
          | Ready => True
          | Blocked f => NotIn t f
          end
        end) l = NotIn t (Node l)). {
          auto.
        }
        rewrite Hr; clear Hr.
        apply IHf0.
        intuition.
        contradiction H.
        auto using in_cons_rhs.
      * apply IHf.
        intuition.
        contradiction H.
        auto using in_cons.
Qed.

Theorem notin_spec:
  forall t f,
  ~ In t f <-> NotIn t f.
Proof.
  split; auto using notin_spec_1, notin_spec_2.
Qed.

(*
Fixpoint disjoint (t:tid) (f:finish) : bool :=
  match f with
    | Node l =>
      (fix disjoint_alt (l:list (tid*finish)) : bool :=
       match l with
       | (t',f) :: l =>
         if TID.eq_dec t t then false
         else andb (disjoint t f) (disjoint_alt l)
       | nil => true
       end
     ) l 
   | Running => true
  end.
*)
