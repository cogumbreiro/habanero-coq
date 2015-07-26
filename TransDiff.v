Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.

Require Import Vars.
Require Import Lang.
Require Import PhaseDiff.

Open Local Scope Z.

Section DIFF_SUM.

Variable A : Type.
Variable diff: A -> A -> Z -> Prop.
Variable get_diff: A -> A -> option Z.
Variable get_diff_spec:
  forall a b z,
  get_diff a b = Some z <-> diff a b z.
(*
 (t1, t2) :: (t2, t3) :: nil
 *)

Notation edge := (A * A) % type.

Inductive DiffSum : list edge -> Z -> Prop :=
  | diff_sum_nil:
    DiffSum nil 0
  | diff_sum_pair:
    forall t1 t2 z,
    diff t1 t2 z ->
    DiffSum ((t1, t2) :: nil) z
  | diff_sum_cons:
    forall t1 t2 t3 w z s,
    DiffSum ((t2, t3) :: w) s ->
    diff t1 t2 z ->
    DiffSum ((t1, t2) :: (t2, t3) :: w) (z + s).

