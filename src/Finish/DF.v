Require Import Vars.
Require Import Syntax2.
Require Import Coq.Lists.List.
Import ListNotations.

Section Defs.
  Structure t := make {
    state : state;
    history : Trace.t;
    spec: Trace.ReducesN state history
  }.

  (** A typed reduction *)

  Inductive Reduces: t -> (tid*op) -> t -> Prop :=
  | reduces_def:
    forall t o pm1 pm2,
    Syntax2.Reduces (state pm1) (t, o) (state pm2) ->
    history pm2 = (t,o)::(history pm1) ->
    Reduces pm1 (t, o) pm2.
End Defs.

Section Props.
(*
  Let progress_aux:
    forall o x m s',
    Syntax2.Reduces (state m) (x, o) s' ->
    exists n, Reduces m (x, o) n.
  Proof.
    intros.
    eapply Trace.reduces_n_cons; eauto.
  Qed.
*)

  Program Definition reduces_step_aux
    x o (s:t) s'
    (Hr: Syntax2.Reduces (state s) (x, o) s') :=
    {| state := s'; history := (x,o)::(history s) |}.
  Next Obligation.
    destruct s.
    eapply Trace.reduces_n_cons; eauto.
  Qed. (* leave it open *)

  Lemma reduces_step:
    forall x o s s' (X : Syntax2.Reduces (state s) (x, o) s'),
    exists s',
    Reduces s (x, o) s'.
  Proof.
    intros.
    exists (reduces_step_aux x o s s' X).
    eauto using reduces_def.
  Qed.

  (** An enabled task can reduce with any operation. *)
  Definition Enabled s t :=
  forall o, Valid (state s) t o -> exists s', Reduces s (t, o) s'.

  Let enabled_to_enabled:
    forall s t,
    Syntax2.Enabled (state s) t ->
    Enabled s t.
  Proof.
    intros.
    unfold Enabled, Syntax2.Enabled in *.
    intros ? Hv.
    apply H in Hv.
    destruct Hv as (s', Hr).
    eauto using reduces_step.
  Qed.

  Corollary progress_ex:
    forall (s:t),
    (* And that state is not empty *)
    ~ Map_TID.Empty (state s) ->
    (* Then there is some [f] such that *)
    exists f,
    ((* [f] is nonempty and every task in [f] reduces. *)
      Nonempty f (state s)
      /\
      forall t, Root t f (state s) -> Enabled s t
    )
    \/
    ((* Or [f] is empty, and [t]'s current finish-scope is [f] *)
      Empty f (state s)
      /\
      exists t, Current t f (state s) /\ Enabled s t
    ).
  Proof.
    intros.
    edestruct Trace.progress_ex as (f,[(Hx,Hy)|(Hx,(x,(Hy,Hz)))]); eauto using spec;
    exists f. {
      left.
      split; auto.
    }
    right.
    split; auto.
    exists x.
    split; auto.
  Qed.

  Lemma progress_nonblocking:
    forall s t o,
    Valid (state s) t o ->
    o <> END_FINISH ->
    exists s', Reduces s (t, o) s'.
  Proof.
    intros.
    eapply progress_nonblocking in H; eauto using spec.
    destruct H as (s', H).
    eauto using reduces_step.
  Qed.

  Theorem progress:
    forall s,
    ~ Map_TID.Empty (state s) ->
    (* Then there is some [f] such that *)
    exists t,
    Enabled s t.
  Proof.
    intros.
    eapply Trace.progress in H; eauto using spec.
    destruct H as (t, Hx);
    eauto using enabled_to_enabled.
  Qed.
End Props.
