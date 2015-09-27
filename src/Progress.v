Require Import HJ.Vars.

Module Request.

Record request {O:Type} := mk_request {
  reqs : Map_TID.t O;
  Check: tid -> O -> Prop;
  In : tid -> Prop
}.

Implicit Arguments reqs.
Implicit Arguments Check.
Implicit Arguments In.
Implicit Arguments mk_request.
End Request.

Module RequestSpec.
Record request_spec
  {O:Type} 
  (reqs : Vars.Map_TID.t O)
  (Check: tid -> O -> Prop)
  (In : tid -> Prop)
:= {
  (** We only consider operations from task in the state. *)
  reqs_in:
    forall t,
    In t <-> Map_TID.In t reqs;
  (** All requests are valid. *)
  reqs_check:
    forall t o,
    Map_TID.MapsTo t o reqs -> Check t o
}.
Implicit Arguments reqs_in.
Implicit Arguments reqs_check.
End RequestSpec.

Section ProgressProp.
Variable O:Type.
Variable reqs : Map_TID.t O.
Variable Check: tid -> O -> Prop.
Variable In : tid -> Prop.
Variable reqs_spec : RequestSpec.request_spec reqs Check In.
Variable S:Type.
(** The state. *)
Variable state : S.
(** The given task issues an operation that yields a new state. *)
Variable Reduce : tid -> O -> S -> Prop.
(** Returns [true] when the given operation is blocking, [false] if unblocking. *)
Variable blocking : O -> bool.

Record progress_spec
:= mk_progress_spec {
  (** Any valid unblocked operation must be able to reduce. *)
  progress_unblocked:
    forall t o,
    Check t o ->
    blocking o = false ->
    exists s', Reduce t o s';
  (**
    If all our requests are blocking requests, then there is at least
    one that can be issued.
  *)
  progress_blocked:
    (** The [state] must be nonempty. *)
    ~ Map_TID.Empty reqs ->
    (** All available requests are blocking. *)
    (forall t o, Map_TID.MapsTo t o reqs -> blocking o = true) ->
    (** There is a task that can reduce. *)
    exists t o,
    Map_TID.MapsTo t o reqs /\ exists s', Reduce t o s' 
}.
Implicit Arguments progress_unblocked.
Implicit Arguments progress_blocked.

Lemma main_progress:
  forall (p:progress_spec),
  ~ Map_TID.Empty reqs ->
  (** There is a task that can reduce. *)
  exists t o,
  Map_TID.MapsTo t o reqs /\ exists s', Reduce t o s'.
Proof.
  intros.
  destruct (Map_TID_Extra.pred_choice reqs (fun (_:tid) (o:O) => (negb (blocking o)))).
  - auto with *. (* Proper *)
  - destruct e as (t, (o, (Hmt, Hb))).
    remember (blocking o) as b.
    destruct b.
    + inversion Hb.
    + exists t.
      exists o.
      intuition.
      apply (progress_unblocked); auto.
      apply (RequestSpec.reqs_check reqs_spec); auto.
  - apply (progress_blocked p); auto.
    intros.
    apply e in H0.
    destruct (blocking o); auto.
Qed.
End ProgressProp.
