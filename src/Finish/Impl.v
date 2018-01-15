Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import HJ.Finish.Lang.
Require Import HJ.Tid.
Require Import HJ.Fid.

Section Defs.
  Structure package := make {
    pkg_task : nat;
    pkg_op: nat;
    pkg_id: nat;
    pkg_time: nat;
    pkg_arg: nat;
    pkg_tid := taskid pkg_task;
    pkg_fid := finishid pkg_id;
    pkg_parse_op :=
    match pkg_op, pkg_arg with
    | 0, 0 => Some (INIT pkg_fid)
    | 1, 0 => Some (BEGIN_FINISH pkg_fid)
    | 2, x => Some (BEGIN_TASK (taskid x))
    | 3, 0 => Some END_TASK
    | _, _ => None
    end;
  }.

  Inductive pkg_err :=
  | PARSE_ERROR.

  Inductive run_err :=
  | PKG_ERROR: pkg_err -> run_err
  | REDUCES_ERROR: reduces_err -> run_err.

  Definition run (s:state) (p:package) : (state + run_err) % type :=
  match pkg_parse_op p with
  | Some o =>
    match Lang.reduces s (pkg_tid p) o with
    | inl s' => inl s'
    | inr e => inr (REDUCES_ERROR e)
    end
  | None => inr (PKG_ERROR PARSE_ERROR)
  end.

End Defs.

(* bools *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inlined Constant negb => "not".

Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Inductive sumor => "option" [ "Some" "None" ].

Extract Inductive option => "option" [ "Some" "None" ].

(* list *)
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inlined Constant length => "List.length".
Extract Inlined Constant app => "List.append".
Extract Inlined Constant map => "List.map".

(* pairs *)
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".

(* nat *)
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".
Extract Inlined Constant plus => "( + )".
Extract Inlined Constant mult => "( * )".
Extract Inlined Constant eq_nat_dec => "( = )".

Extraction Language Ocaml.

Extraction "ocaml/finish" run.
