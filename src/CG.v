Require Import Vars.

Require Import Coq.Lists.List.
Require Import Node.
Require Import Coq.Relations.Relations.

Import ListNotations.

Section Defs.

  Inductive op_kind :=
  | ARRIVE
  | AWAIT.

  Definition op := (op_kind * phid * nat) % type.

  Definition segment := node.

  Variable vertices: list segment.
  Variable tid_of: segment -> tid.
  Variable op_of:  segment -> op.
  Variable segments: segment -> list segment.

  Inductive Seq {A}: list A -> A * A -> Prop :=
  | seq_eq:
    forall x y l,
    Seq (x::y::l) (y,x)
  | seq_cons:
    forall x l p,
    Seq l p ->
    Seq (x::l) p.

  Inductive Edge: segment * segment -> Prop :=
(*  | edge_seq:
    forall x p,
    Seq (segments x) p ->
    Edge p *)
  | edge_sync:
    forall x y p n z l,
    op_of z = (ARRIVE, p, n) ->
    op_of y = (AWAIT, p, n) ->
    segments z = z :: x :: l ->
    Edge (x, y).

  Definition phase := (phid * nat) % type.

  Record phase_ordering := {
    sp : Map_PHID.t nat;
    wp : Map_PHID.t nat;
  }.

  Definition empty := Build_phase_ordering (Map_PHID.empty nat) (Map_PHID.empty nat).

  Inductive Add: Map_PHID.t nat -> (phid * nat) -> Map_PHID.t nat -> Prop :=
  | add_new:
    forall ph p n,
    ~ Map_PHID.In p ph ->
    Add ph (p, n) (Map_PHID.add p n ph)
  | add_update:
    forall ph p n n',
    Map_PHID.MapsTo p n ph ->
    Add ph (p, n') (Map_PHID.add p (Nat.max n n') ph).

  Inductive Match k p x : Prop :=
  | match_def:
    forall n,
    op_of x = (k, p, n) ->
    Match k p x.

  Inductive Phase: op -> list segment -> Prop :=
  | phase_zero:
    forall l p n x k,
    ~ Exists (Match k p) l ->
    op_of x = (k, p, n) ->
    Phase (k, p, n) (x::l)
  | phase_succ:
    forall l p n x k,
    Phase (k, p, n) l ->
    op_of x = (k, p, S n) ->
    Phase (k, p, S n) (x::l)
  | phase_cons:
    forall l p n x k,
    Phase (k, p, n) l ->
    ~ Match k p x ->
    Phase (k, p, n) (x::l).

  Inductive HappensBefore (x y:segment) : Prop :=
  | happens_before_def:
    forall p nx ny,
    Phase (AWAIT, p, nx) (segments x) ->
    Phase (ARRIVE, p, ny) (segments y) ->
    nx < ny ->
    HappensBefore x y.

  Definition prec := clos_trans segment (prod_uncurry Edge).

  Infix "<" := prec.

  Lemma op_kind_dec (x y:op_kind) :
    { x = y } + { x <> y}.
  Proof.
    destruct x, y; auto; right; unfold not; intros N; inversion N.
  Defined.

  Lemma match_dec k p x:
    { Match k p x } + { ~ Match k p x }.
  Proof.
    remember (op_of x).
    destruct o as ((k', p'), n).
    destruct (op_kind_dec k' k). {
      destruct (PHID.eq_dec p' p). {
        subst.
        eauto using match_def.
      }
      subst.
      right.
      unfold not; intros.
      inversion H.
      rewrite H0 in *.
      inversion Heqo.
      contradiction.
    }
    right; unfold not; intros N; inversion N; subst; clear N.
    rewrite H in *.
    inversion Heqo.
    subst.
    contradiction.
  Defined.

  Variable segments_defined:
    forall x,
    exists l, segments x = x :: l.

  Variable segments_sub:
    forall x y l,
    segments x = x :: y :: l ->
    segments y = y :: l.

  Variable segments_phase_succ:
    forall x k p n l,
    segments x = x :: l ->
    Phase (k, p, n) l ->
    op_of x = (k, p, S n).

  Let foo:
    forall l k p x,
    segments x = x::l ->
    Exists (Match k p) (x::l) ->
    exists n, Phase (k, p, n) (x::l).
  Proof.
    induction l; intros. {
      inversion H0; subst; clear H0;
      inversion H2; subst; clear H2.
      exists n.
      apply phase_zero; auto.
      unfold not; intros N; inversion N.
    }
    inversion H0; subst; clear H0. {
      inversion H2; subst; clear H2.
      destruct (Exists_dec (Match k p) (a::l) (match_dec k p)). {
        apply IHl in e; eauto.
        destruct e as (n', Hp).
        eauto using phase_succ.
      }
      eauto using phase_zero.
    }
    eapply IHl in H2; eauto.
    destruct H2 as (n', Hp).
    eauto using phase_succ.
  Qed.

  Lemma hb_to_prec:
    forall (x y:segment),
    x < y ->
    HappensBefore x y.
  Proof.
    intros.
    induction H.
    - inversion H; subst; clear H.
      + 
      
        
  Qed.
(*
  Inductive PhaseOrderingOf : segment -> list segment -> phase_ordering -> Prop :=
  | phase_ordering_of:
    forall l po,
    PhaseOrdering l po ->
    PhaseOrderingOf l po
  | phase_ordering_of_cons:
    forall l x po,
    PhaseOrderingOf l po ->
    PhaseOrderingOf (x::l) po.

  Inductive Stamps:
*)
End Defs.