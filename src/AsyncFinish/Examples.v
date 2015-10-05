Require Import HJ.Vars.
Require Import HJ.AsyncFinish.Lang.
Require Import HJ.AsyncFinish.LangExtra.


Module Examples.
Module FX10.
Import Semantics.

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

Import FinishNotations.
Open Scope finish_scope.


(** Helper tactics to solve disjoint. *)
Ltac solve_notin :=
  (apply notin_spec_1;
    simpl;
    intuition; inversion H).

(** Helper tactics to solve disjoint. *)
Ltac solve_disjoint :=
  (apply disjoint_ok; solve_notin) ||
  (apply disjoint_skip; auto).


(* Check if the notations are working. *)
Goal Node nil = [].
auto. Qed.

(* Making singleton works as expected. *)
Goal mk_finish t1 = [ ! t1 ].
Proof.
  auto.
Qed.

(*
(t1: "finish { async S3 f() } S2") -> (t1, begin_finish)
(t1: "async S3 f()"> |> t1: "S2"
*)
Goal
  Reduce
  [ ! t1 ]
  t1 BEGIN_FINISH
  (put t1 (Blocked [! t1]) [ ! t1 ])
  .
Proof.
  apply begin_finish.
Qed.

Goal put t1 (Blocked (mk_finish t1)) (mk_finish t1) = [ t1 <| [ ! t1 ] ] .
Proof.
  auto.
Qed.

Let t2 := 2.
(*
(t1: "async S3 f()"> |> t1: "S2" -> (t1, begin_async t2)
[(t2: "S3") || (t1: "f()") |> t1: "S2"]
*)
Goal Reduce
  [ t1 <| [ ! t1 ] ]
  t1 (BEGIN_ASYNC t2)
  (put t1 (Blocked [ ! t1 | ! t2 ])  [ t1 <| [ ! t1 ] ]).
Proof.
  apply reduce_nested with (f':=[!t1]).
  - solve_disjoint.
  - eapply child_eq.
  - eapply begin_async.
    eapply leaf_def, child_eq.
    solve_notin.
Qed.

(*
(t2: "S3") || (t1: "async S5") |> t1: "S2"
-> (t2, begin_async t3) 
(t2: "S3") || (t1: "") || (t3: "S5") |> t1: "S2"
*)

Let t3 := 3.

Goal Reduce
  [ t1 <| [ !t2 | !t1 ] ]
  t1 (BEGIN_ASYNC t3)
  (put t1 (Blocked (put_leaf t3 [ !t2 | !t1 ])) [ t1 <| [ !t2 | !t1 ] ]).
Proof.
  apply reduce_nested with ([ !t2 | !t1 ]).
  + solve_disjoint.
  + eapply child_eq.
  + eapply begin_async.
    eapply leaf_def.
    eapply child_cons.
    eapply child_eq.
    solve_notin.
Qed.

(** Test the output of test. *)
Goal
  (put_leaf t3 [ !t2 | !t1 ]) = 
  [ !t1 | !t2 | !t3 ].
auto.
Qed.


(** Test the simplification of this expression. *)
Goal 
  (put t1 (Blocked (put_leaf t3 [ !t2 | !t1 ])) [ t1 <| [ !t2 | !t1 ] ])
  = 
  [ t1 <| [  !t1 | !t2 | !t3 ] ].
auto.
Qed.

(*
(t2: "S3") || (t1: "") || (t3: "S5") |> t1: "S2" -> (t1, end_async)
(t2: "S3") || Idle || (t3: "S5") |> t1: "S2"
*)
Goal Reduce
  [ t1 <| [  !t1 | !t2 | !t3 ] ]
  t1 END_ASYNC
  (put t1 (Blocked (remove t1 [ !t1 | !t2 | !t3 ])) [ t1 <| [ !t1 | !t2 | !t3 ] ])
  .
Proof.
  apply reduce_nested with ([  !t1 | !t2 | !t3 ]).
  - solve_disjoint.
  - apply child_eq.
  - apply end_async.
    apply leaf_def.
    apply child_eq.
Qed.

Goal
  (put t1 (Blocked (remove t1 [ !t1 | !t2 | !t3 ])) [ t1 <| [ !t1 | !t2 | !t3 ] ])
  = 
  [ t1 <| [ !t2 | !t3 ] ].
auto.
Qed.

(*
(t2: "S3") || Idle || (t3: "S5") |> t1: "S2"
-> (t2, end_async)
(t3: "S5") || Idle || Idle |> t1: "S2"
*)
Goal Reduce
  [ t1 <| [ !t2 | !t3 ] ]
  t2 END_ASYNC
  (put t1 (Blocked (remove t2 [ !t2 | !t3 ])) [ t1 <| [ !t2 | !t3 ] ])
  .
Proof.
  apply reduce_nested with ([ !t2 | !t3 ]).
  - solve_disjoint.
  - apply child_eq.
  - apply end_async.
    apply leaf_def.
    apply child_eq.
Qed.

Goal (put t1 (Blocked (remove t2 [ !t2 | !t3 ])) [ t1 <| [ !t2 | !t3 ] ])
 = 
 [ t1 <| [ !t3 ] ].
auto.
Qed.

(*
(t3: "S5") || Idle || Idle |> t1: "S2"
-> (t3, end_async)
Idle |> t1: "S2"
*)
Goal Reduce
  [ t1 <| [ !t3 ] ]
  t3 END_ASYNC
  (put t1 (Blocked (remove t3 [ !t3 ])) [ t1 <| [ !t3 ] ])
  .
Proof.
  apply reduce_nested with ([ !t3 ]).
  - solve_disjoint.
  - apply child_eq.
  - apply end_async.
    apply leaf_def.
    apply child_eq.
Qed.

Goal
  put t1 (Blocked(remove t3 [ !t3 ])) [ t1 <| [ !t3 ] ]
  = 
  [t1 <| []].
auto.
Qed.

(*
Idle  || Idle  || Idle |> t1: "S2"
-> (t3, end_async)
(t1: "S2")
*)
Goal Reduce
  [t1 <| []]
  t1 END_FINISH
  [!t1].
Proof.
  apply end_finish.
  apply child_eq.
Qed.

(*
(t1: "S2")
->
Idle
*)
Goal Reduce
  [!t1]
  t1 END_ASYNC
  [].
Proof.
  eapply end_async.
  apply leaf_def.
  apply child_eq.
Qed.
End FX10.
End Examples.

