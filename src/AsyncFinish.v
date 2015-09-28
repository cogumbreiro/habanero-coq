Require Import HJ.Phasers.Lang.
Require Import HJ.Vars.

Inductive tree :=
  | Finish : tree -> tid -> tree
  | Par : tree -> tree -> tree
  | Task : tid -> tree
  | Idle : tree.

Inductive In : tree -> tid -> Prop :=
  | in_finish_left:
    forall T1 T2 t,
    In T1 t ->
    In (Finish T1 T2) t
  | in_finish_right:
    forall T1 t,
    In (Finish T1 t) t
  | in_par_left:
    forall T1 T2 t,
    In T1 t ->
    In (Par T1 T2) t
  | in_par_right:
    forall T1 T2 t,
    In T2 t ->
    In (Par T1 T2) t
  | in_task:
    forall t,
    In (Task t) t.

Inductive op_kind :=
  | BEGIN_ASYNC : tid -> op_kind
  | END_ASYNC
  | BEGIN_FINISH
  | END_FINISH.

Inductive Disjoint (a:tree) : op_kind -> Prop :=
  | disjoint_ok:
    forall t,
    ~ In a t ->
    Disjoint a (BEGIN_ASYNC t)
  | disjoint_skip:
    forall o,
    (match o with | BEGIN_ASYNC _ => False |  _ => True end) ->
    Disjoint a o.

Fixpoint normalize (a:tree) : tree :=
match a with
  | Finish a' t => Finish (normalize a') t
  | Par a1 a2 =>
    match a1 with
     | Idle => normalize a2
     | _ =>
       match a2 with
         | Idle => normalize a1
         | _ => Par (normalize a1) (normalize a2)
       end
   end
 | Task t => Task t
 | Idle => Idle
end.

Inductive Reduce : tree -> tid -> op_kind -> tree -> Prop :=
  | begin_async:
    forall t t',
    Reduce (Task t) t (BEGIN_ASYNC t') (Par (Task t) (Task t'))
  | end_async:
    forall t,
    Reduce (Task t) t END_ASYNC Idle
  | begin_finish:
    forall t,
    Reduce (Task t) t BEGIN_FINISH (Finish (Task t) t)
  | end_finish:
    forall t,
    Reduce (Finish Idle t) t END_FINISH (Task t)
  | run_finish:
    forall T1 T2 t o T1',
    Reduce T1 t o T1' ->
    Reduce (Finish T1 T2) t o (Finish T1' T2)
  | run_par_left:
    forall T1 T2 t o T1',
    Disjoint T2 o ->
    Reduce T1 t o T1' ->
    Reduce (Par T1 T2) t o (Par T1' T2)
  | run_par_right:
    forall T1 T2 t o T2',
    Disjoint T1 o ->
    Reduce T2 t o T2' ->
    Reduce (Par T1 T2) t o (Par T1 T2')
  | run_congruence:
    forall a t o a',
    Reduce (normalize a) t o a' ->
    Reduce a t o a'.

Module Examples.
(**
Original FX10 example:

              (t1: "finish { async S3 f() } S2") -> (t1, begin_finish)
                (t1: "async S3 f()"> |> t1: "S2" -> (t1, begin_async t2)
           (t2: "S3") || (t1: "f()") |> t1: "S2" -> (... evaluates function)
      (t2: "S3") || (t1: "async S5") |> t1: "S2" -> (t2, begin_async t3) 
(t2: "S3") || (t1: "") || (t3: "S5") |> t1: "S2" -> (t1, end_async)
            (t2: "S3") || (t3: "S5") |> t1: "S2" -> (t2, end_async)
                          (t3: "S5") |> t1: "S2" -> (t3, end_async)
                                Idle |> t1: "S2" -> (t3, end_finish)
                                      (t1: "S2") -> (t1, end_async)
                                            Idle

*)
Let t1:= 1.
(*
(t1: "finish { async S3 f() } S2") -> (t1, begin_finish)
(t1: "async S3 f()"> |> t1: "S2"
*)
Goal Reduce (Task t1) t1 BEGIN_FINISH (Finish (Task t1) t1).
Proof.
  auto using begin_finish.
Qed.

Let t2 := 2.
(*
(t1: "async S3 f()"> |> t1: "S2" -> (t1, begin_async t2)
(t2: "S3") || (t1: "f()") |> t1: "S2"
*)
Goal Reduce (Finish (Task t1) t1) t1 (BEGIN_ASYNC t2)
  (Finish (Par (Task t1) (Task t2)) t1).
Proof.
  auto using run_finish, begin_async.
Qed.

(*
(t2: "S3") || (t1: "async S5") |> t1: "S2"
-> (t2, begin_async t3) 
(t2: "S3") || (t1: "") || (t3: "S5") |> t1: "S2"
*)

Let t3 := 3.

Goal Reduce
  (Finish (Par (Task t1) (Task t2)) t1)
  t1 (BEGIN_ASYNC t3)
  (Finish
    (Par (Par (Task t1) (Task t3)) (Task t2)) t1).
Proof.
  eapply run_finish.
  eapply run_par_left.
  - eapply disjoint_ok.
    intuition.
    inversion H.
  - eapply begin_async.
Qed.

(*
(t2: "S3") || (t1: "") || (t3: "S5") |> t1: "S2" -> (t1, end_async)
(t2: "S3") || Idle || (t3: "S5") |> t1: "S2"
*)
Goal Reduce
  (Finish
    (Par (Par (Task t1) (Task t3)) (Task t2)) t1)
  t1 END_ASYNC
  (Finish
    (Par (Par Idle (Task t3)) (Task t2)) t1).
Proof.
  eapply run_finish.
  eapply run_par_left.
  - eauto using disjoint_skip.
  - eapply run_par_left.
    + eauto using disjoint_skip.
    + eapply end_async.
Qed.

(*
(t2: "S3") || Idle || (t3: "S5") |> t1: "S2"
-> (t2, end_async)
(t3: "S5") || Idle || Idle |> t1: "S2"
*)
Goal Reduce
  (Finish
    (Par (Par Idle (Task t3)) (Task t2)) t1)
  t2 END_ASYNC
  (Finish
    (Par (Par Idle (Task t3)) Idle) t1).
Proof.
  eapply run_finish.
  eapply run_par_right.
  - eauto using disjoint_skip.
  - eapply end_async.
Qed.

(*
(t3: "S5") || Idle || Idle |> t1: "S2"
-> (t3, end_async)
Idle |> t1: "S2"
*)
Goal Reduce
  (Finish
    (Par (Par Idle (Task t3)) Idle) t1)
  t3 END_ASYNC
  (Finish
    (Par (Par Idle Idle) Idle) t1).
Proof.
  eapply run_finish.
  eapply run_par_left.
  - eauto using disjoint_skip.
  - eapply run_par_right.
    + eauto using disjoint_skip.
    + eapply end_async.
Qed.

(*
Idle  || Idle  || Idle |> t1: "S2"
-> (t3, end_async)
(t1: "S2")
*)
Goal Reduce
  (Finish
    (Par (Par Idle Idle) Idle) t1)
  t1 END_FINISH
  (Task t1).
Proof.
  eapply run_congruence.
  simpl.
  eapply end_finish.
Qed.

(*
(t1: "S2")
->
Idle
*)
Goal Reduce
  (Task t1)
  t1 END_ASYNC
  Idle.
Proof.
  eapply end_async.
Qed.

End Examples.
