Require Import HJ.Vars.
Require Import HJ.AsyncFinish.Lang.
Require Import HJ.AsyncFinish.LangExtra.


Module Examples.
Module FX10Example.
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

(**
  Function [mk_finish] creates a finish scope, delimited by brackets,
  with the given task [t1] marked as ready, which is denoted 
  by the bang symbol [!]. *)
Goal mk_finish t1 = [ ! t1 ].
Proof.
  auto.
Qed.

(**
  The FX10 language is not concerned with observing the behaviour of tasks,
  it is instead focused with observing the interaction among procedures.

  (t1: "finish { async S3 f() } S2") -> (t1, begin_finish)
  (t1: "async S3 f()"> |> t1: "S2"

  We represent finish scope by a mapping from task identifiers of type [tid] to
  tasks of type [task]. A task [t] is either ready [!t] to execute or blocked
  on finish scope [f], notation
  [t <| f].
  
  Operator [put f (t, a)], notation [|+] updates the finish scope [f], by
  setting task [t] to have a task body [a].
  
  For example, let task [t1] be ready in a finish scope. If task [t1]
  issues a [BEGIN_FINISH], then we put task [t1] blocked on a new finish
  state where [t1] itself is running. In HJ, the same can begin multiple
  finish scopes.
*)
Goal
  Reduce
  [ ! t1 ] t1 BEGIN_FINISH ([ ! t1 ] |+ (t1 <| [! t1]) )
  .
Proof.
  apply begin_finish.
  apply leaf_def.
  apply child_eq.
Qed.

Goal (mk_finish t1) |+ (t1 <| (mk_finish t1))  = [ t1 <| [ ! t1 ] ] .
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
  ([ t1 <| [ ! t1 ] ] |+ t1 <| ([ ! t1 ] |+ ! t2 )).
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
  ([ t1 <| [ !t2 | !t1 ] ] |+ (t1  <| ([ !t2 | !t1 ] |+ (!t3) )) ).
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
  ([ !t2 | !t1 ] |+ (!t3)) = [ !t3 | !t2 | !t1 ].
  auto.
Qed.


(** Test the simplification of this expression. *)
Goal 
  ([ t1 <| [ !t2 | !t1 ] ] |+ (t1  <| ([ !t2 | !t1 ] |+ (!t3))) )
  = 
  [ t1 <| [  !t3 | !t2 | !t1 ] ].
auto.
Qed.

(*
(t2: "S3") || (t1: "") || (t3: "S5") |> t1: "S2" -> (t1, end_async)
(t2: "S3") || Idle || (t3: "S5") |> t1: "S2"
*)
Goal Reduce
  [ t1 <| [  !t1 | !t2 | !t3 ] ]
  t1 END_ASYNC
  ([ t1 <| [ !t1 | !t2 | !t3 ] ] |+ (t1 <| ([ !t1 | !t2 | !t3 ] |- t1 )) )
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
  ([ t1 <| [ !t1 | !t2 | !t3 ] ] |+ (t1 <| ([ !t1 | !t2 | !t3 ] |- t1)) )
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
  ([ t1 <| [ !t2 | !t3 ] ] |+ (t1 <| ([ !t2 | !t3 ] |- t2)) )
  .
Proof.
  apply reduce_nested with ([ !t2 | !t3 ]).
  - solve_disjoint.
  - apply child_eq.
  - apply end_async.
    apply leaf_def.
    apply child_eq.
Qed.

Goal
 ([ t1 <| [ !t2 | !t3 ] ] |+ (t1 <| ([ !t2 | !t3 ] |- t2)) )
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
  ([ t1 <| [ !t3 ] ] |+ t1 <| ([ !t3 ] |- t3) ) 
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
  ([ t1 <| [ !t3 ] ] |+ t1 <| ([ !t3 ] |- t3) ) 
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
End FX10Example.

Module FX10.

Definition fid := nat.

Inductive expression :=
  | constant:  nat -> expression
  | load: phid -> expression.

Inductive statement :=
  | snil 
  | seq: instruction -> statement -> statement
with instruction :=
  | skip
  | store: nat -> expression -> instruction
  | while: nat -> statement -> instruction
  | async: statement -> instruction
  | begin_finish
  | end_finish
  | call: fid -> instruction.

Definition program := Map_PHID.t statement.
Definition taskmap := Map_TID.t statement.
Definition heap := Map_PHID.t nat.
Inductive state := mk_state {
  get_finish: Lang.finish;
  get_taskmap: taskmap;
  get_heap:  heap;
  get_program: program
}.

Section StateOps.

Variable s:state.
Definition set_finish (f:Lang.finish) : state :=
  mk_state f s.(get_taskmap) s.(get_heap) s.(get_program).

Require Import Coq.Init.Datatypes.

Definition heap_load (h:phid) :=
  match Map_PHID.find h s.(get_heap) with
  | None => 0
  | Some n => n
  end.

Definition eval (e:expression) :=
  match e with
  | constant n => n
  | load h => S (heap_load h)
  end.

Definition heap_store (h:phid) (n:nat) : state :=
  mk_state s.(get_finish) s.(get_taskmap) (Map_PHID.add h n s.(get_heap)) s.(get_program).

Definition remove_task (t:tid) : state :=
  mk_state s.(get_finish) (Map_TID.remove t s.(get_taskmap)) s.(get_heap) s.(get_program).

Definition update_statement (t:tid) (s':statement) : state :=
  mk_state s.(get_finish) (Map_TID.add t s' s.(get_taskmap)) s.(get_heap) s.(get_program).

Definition get_function (h:phid) : statement :=
  match Map_PHID.find h s.(get_program) with
  | None => snil
  | Some s => s
  end.

End StateOps.

Section OS.
Variable S:state.

Inductive GetStatement (t:tid) (s':statement) : Prop :=
    get_sequence_def:
      Map_TID.MapsTo t s' S.(get_taskmap) ->
      GetStatement t s'.

Definition FReduce := Semantics.Reduce S.(get_finish).

Fixpoint concat (s1:statement) (s2:statement) : statement :=
  match s1 with
  | snil => s2
  | seq i s1' => seq i (concat s1' s2)
  end.


Inductive Reduce: state -> Prop :=
  | reduce_snil:
    forall t f',
    GetStatement t snil ->
    FReduce t Semantics.END_ASYNC f' ->
    let S' := (remove_task S t) in
    Reduce (set_finish S' f')

  | reduce_skip:
    forall t s,
    GetStatement t (seq skip s) ->
    Reduce (update_statement S t s)

  | reduce_store:
    forall t h s e,
    GetStatement t (seq (store h e) s) ->
    let n := eval S e in
    let S' := heap_store S h n in
    Reduce (update_statement S' t s)

  | reduce_while_end:
    forall t s1 s2 h,
    GetStatement t (seq (while h s1) s2) ->
    heap_load S h = 0 ->
    Reduce (update_statement S t s2)
  
  | reduce_while_loop:
    forall s1 s2 h t,
    GetStatement t (seq (while h s1) s2) ->
    heap_load S h <> 0 ->
    let s3 := concat s1 (seq (while h s1) s2) in
    Reduce (update_statement S t s3)
  
  | reduce_async:
    forall t1 t2 f' s1 s2,
    GetStatement t1 (seq (async s1) s2) ->
    ~ Map_TID.In t2 S.(get_taskmap) ->
    FReduce t1 (Semantics.BEGIN_ASYNC t2) f' ->
    let S' := update_statement (update_statement S t2 s2) t1 s1 in
    Reduce (set_finish S' f')

  | reduce_begin_finish:
    forall s t f',
    GetStatement t (seq begin_finish s) ->
    FReduce t Semantics.BEGIN_FINISH f' ->
    let S' := update_statement S t s in
    Reduce (set_finish S f')
    
  | reduce_end_finish:
    forall s t f',
    GetStatement t (seq end_finish s) ->
    FReduce t Semantics.END_FINISH f' ->
    let S' := update_statement S t s in
    Reduce (set_finish S f')

  | reduce_call:
    forall s t h,
    GetStatement t (seq (call h) s) ->
    let s' := concat (get_function S h) s in
    Reduce (update_statement S t s').
End OS.

End FX10.
End Examples.

