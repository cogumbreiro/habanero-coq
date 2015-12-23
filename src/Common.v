Require Import HJ.Vars.

Set Implicit Arguments.

Section RequestOf.
Variable O:Type.
Variable Check : tid -> O -> Prop.
Variable reqs: Map_TID.t O.

Inductive RequestToCheck : Prop :=
  request_to_check_def:
    (forall t o,
    Map_TID.MapsTo t o reqs ->
    Check t o) ->
    RequestToCheck.

Inductive CheckToRequest: Prop :=
  check_to_request_def:
    (forall t o,
      Check t o ->
      Map_TID.MapsTo t o reqs) ->
    CheckToRequest.

Inductive RequestOf : Prop :=
  request_of_def:
    CheckToRequest ->
    RequestToCheck ->
    RequestOf.
End RequestOf.


Section request_of.
Variable O:Type.
Variable Check: tid -> O -> Prop.
Definition request_of := { r: Map_TID.t O | @RequestOf O Check r} .
End request_of.


