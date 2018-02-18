Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import HJ.Finish.Lang.
Require Import HJ.Tid.
Require Import HJ.Fid.
Require Import Coq.Arith.EqNat.
Require Import HJ.Finish.Impl.

Section Defs.
  Import ListNotations.

  Definition trace := list package.
  Section Defs.
    Inductive At (f:fid) (n:nat) (p:package) : Prop :=
    | at_def:
      f = pkg_id p ->
      n = pkg_time p ->
      At f n p.

    Inductive WF: trace -> Prop :=
    | wf_nil:
      WF nil
    | wf_cons:
      forall l p,
      WF l ->
      ~ Exists (At (pkg_id p) (pkg_time p)) l ->
      WF (p::l).

    Inductive Full: trace -> fid -> nat -> Prop :=
    | full_zero:
      forall f l,
      ~ Exists (At f 0) l ->
      Full l f 0
    | full_succ:
      forall f l n,
      Full l f n ->
      Exists (At f (S n)) l ->
      Full l f (S n).

    (* A package is an element of the trace if its time is full *)
    Inductive In p l : Prop :=
    | in_def :
      List.In p l ->
      Full l (pkg_id p) (pkg_time p) ->
      In p l.

    (* Sequential order within the trace : *)
    Inductive SeqLt {A} : list A -> A -> A -> Prop :=
    | seq_lt_eq:
      forall x y l,
      List.In y l ->
      SeqLt (x::l) x y
    | seq_lt_cons:
      forall x y z l,
      SeqLt l x y ->
      SeqLt (z::l) x y.

    Inductive Lt l x y: Prop :=
    | lt_neq:
      pkg_id x <> pkg_id y ->
      SeqLt l x y ->
      Lt l x y
    | lt_eq:
      pkg_id x = pkg_id y ->
      pkg_time x < pkg_time y ->
      List.In x l ->
      List.In y l ->
      Lt l x y.

    Definition Incl l m := (forall x, In x l -> In x m).
    Definition Continuous l := (forall x, List.In x l -> In x l).
    Definition PreserveLt l m := (forall x y, Lt l x y -> Lt m x y).

    Inductive Norm: trace -> trace -> Prop :=
    | norm_def:
      forall l m,
      Incl l m ->
      Continuous m ->
      PreserveLt l m ->
      PreserveLt m l ->
      Norm l m.
(*
    Lemma in_absurd_nil:
      forall x,
      pkg_time x <> 0 ->
      ~ In x nil.
    Proof.
      unfold not; intros.
      inversion H0; subst; clear H0.
      - rewrite H1 in *.
        contradiction.
      - inversion H5.
    Qed.
*)
    Lemma incl_nil:
      Incl nil nil.
    Proof.
      unfold Incl; intros.
      inversion H.
      inversion H0.
    Qed.

    Lemma continuous_nil:
      Continuous nil.
    Proof.
      unfold Continuous; intros.
      inversion H.
    Qed.

    Lemma lt_absurd_nil:
      forall x y,
      ~ Lt nil x y.
    Proof.
      unfold not; intros.
      inversion H.
      - inversion H1.
      - inversion H2.
    Qed.

    Lemma preserves_lt_nil:
      forall x,
      PreserveLt nil x.
    Proof.
      induction x; unfold PreserveLt; intros. {
        apply lt_absurd_nil in H.
        contradiction. 
      }
      apply lt_absurd_nil in H.
      contradiction.
    Qed.
(*
    Lemma norm_nil:
      Norm nil nil.
    Proof.
      apply norm_def; auto using incl_nil, continuous_nil, preserves_lt_nil.
    Qed.

    Let spec_cons:
      forall l a l1 b,
      WF l ->
      ~ Exists (At (pkg_id a) (pkg_time a)) l ->
      Norm l l1 ->
      Norm (a :: l) (fst (buffer_add a b) ++ l1).
    Proof.
      intros.
      unfold buffer_add.
      destruct (Map_FID_Extra.find_rw (pkg_id a) b) as [(R,mt)|(?,(R,mt))];
      rewrite R; clear R. {
        destruct enq_zero; simpl.
      }
    Qed.

    Let spec_1:
      forall l,
      WF l ->
      let (m, b) := buffer_add_all l (Map_FID.empty _) in
      Norm l m.
    Proof.
      induction l; intros. {
        simpl.
        auto using norm_nil.
      }
      inversion H; subst; clear H.
      assert (R: let (m, _) := buffer_add_all l (Map_FID.empty enq) in Norm l m). {
        apply IHl; auto.
      }
      clear IHl.
      remember (buffer_add_all _  _).
      destruct p as (l1, b).
      simpl.
      rewrite <- Heqp.
      remember (buffer_add _ _).
      destruct p as (l2,b2).
      unfold buffer_add in *.
      
    Qed.
*)
End Defs.

