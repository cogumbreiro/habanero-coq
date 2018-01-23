Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import HJ.Finish.Lang.
Require Import HJ.Tid.
Require Import HJ.Fid.
Require Import Coq.Arith.EqNat.

Section Defs.
  Import ListNotations.

  Inductive package_op :=
  | PKG_INIT
  | PKG_BEGIN_FINISH
  | PKG_END_FINISH
  | PKG_BEGIN_TASK
  | PKG_END_TASK.

  Definition nat_to_op (o:nat) :=
  match o with
  | 0 => Some PKG_INIT
  | 1 => Some PKG_BEGIN_FINISH
  | 2 => Some PKG_END_FINISH
  | 3 => Some PKG_BEGIN_TASK
  | 4 => Some PKG_END_TASK
  | _ => None
  end.

  Definition op_to_nat o :=
  match o with
  | PKG_INIT => 0
  | PKG_BEGIN_FINISH => 1
  | PKG_END_FINISH => 2
  | PKG_BEGIN_TASK => 3
  | PKG_END_TASK => 4
  end.

  Lemma op_to_nat_spec_1:
    forall o,
    nat_to_op (op_to_nat o) = Some o.
  Proof.
    destruct o; auto.
  Qed.

  Lemma op_to_nat_spec_2:
    forall n o,
    nat_to_op n = Some o ->
    op_to_nat o = n.
  Proof.
    intros.
    repeat (destruct n; simpl in *; inversion H; subst; auto).
  Qed.

  Lemma op_to_nat_spec_3:
    forall n o,
    op_to_nat o = n ->
    nat_to_op n = Some o.
  Proof.
    intros.
    destruct o; simpl in *; subst; simpl; auto.
  Qed.

  Definition nat_to_args o (a:nat) :=
  match o with
  | PKG_INIT => []
  | PKG_BEGIN_FINISH => []
  | PKG_END_FINISH => []
  | PKG_BEGIN_TASK => [a]
  | PKG_END_TASK => []
  end.

  Structure package := make {
    pkg_task : tid;
    pkg_op: package_op;
    pkg_id: fid;
    pkg_time: nat;
    pkg_args: list nat;
    pkg_parse_op :=
    match pkg_op, pkg_args with
    | PKG_INIT, [] => Some (INIT pkg_id)
    | PKG_BEGIN_FINISH, [] => Some (BEGIN_FINISH pkg_id)
    | PKG_END_FINISH, [] => Some (END_FINISH pkg_id)
    | PKG_BEGIN_TASK, [x] => Some (BEGIN_TASK (taskid x))
    | PKG_END_TASK, [] => Some END_TASK
    | _, _ => None
    end;
  }.

  (** Test cases that catch bugs we found: *)

  Goal forall p n,
    pkg_args p = [n] ->
    pkg_op p = PKG_BEGIN_TASK ->
    pkg_parse_op p = Some (BEGIN_TASK (taskid n)).
  Proof.
    intros.
    unfold pkg_parse_op.
    rewrite H0.
    rewrite H.
    trivial.
  Qed.

  Goal forall p,
    pkg_args p = [] ->
    pkg_op p <> PKG_BEGIN_TASK ->
    exists o, pkg_parse_op p = Some o.
  Proof.
    intros.
    unfold pkg_parse_op.
    remember (pkg_op p).
    destruct p0; subst; rewrite H; eauto.
    contradiction.
  Qed.

  Definition pkg_create (x:tid) (p:fid*nat) (o:package_op) (l:list nat) :=
  {| 
    pkg_task := x;
    pkg_op := o;
    pkg_id := (fst p);
    pkg_time := snd p;
    pkg_args := l;
  |}.

  Inductive pkg_err :=
  | PARSE_ERROR.

  Inductive run_err :=
  | PKG_ERROR: pkg_err -> run_err
  | REDUCES_ERROR: reduces_err -> run_err.

  Definition run (s:state) (p:package) : (state + run_err) % type :=
  match pkg_parse_op p with
  | Some o =>
    match Lang.reduces s (pkg_task p) o with
    | inl s' => inl s'
    | inr e => inr (REDUCES_ERROR e)
    end
  | None => inr (PKG_ERROR PARSE_ERROR)
  end.

  Definition add1 s n p :=
  if beq_nat n (pkg_time p)
  then (run s p, (S n, nil))
  else (inl s, (n, p::nil)).

  Definition enq := (nat * list package) % type.

  Definition enq_zero : enq := (0, []).

  Definition enq_curr (e:enq) := fst e.

  Definition enq_elems (e:enq) := snd e.

  Definition empty_enq n : enq := (n, []).

  Definition enq_cons p (e:enq) := let (x, y) := e in (x, p :: y).

  Definition enq_succ (e:enq) := let (x, y) := e in (S x, y).

  Definition enq_select p ps (e:enq) :=
  if beq_nat (enq_curr e) (pkg_time p)
  then (p::ps, enq_succ e)
  else (ps, enq_cons p e).

  Goal enq_select (pkg_create (taskid 0) (finishid 1, 0) PKG_INIT []) [] enq_zero
    = ([pkg_create (taskid 0) (finishid 1, 0) PKG_INIT []], (1, [])).
  Proof.
    compute.
    trivial.
  Qed.

  Goal enq_select (pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1]) [] (1, [])
    = ([pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1]], (2, [])).
  Proof.
    compute.
    trivial.
  Qed.

  Fixpoint poll_ready (n:nat) (elems:list package) {struct elems} :
     ((list package) * enq) % type:=
  match elems with
  | [] => ([], empty_enq n)
  | [p] => enq_select p [] (n, [])
  | p::elems =>
      let (ps, e) := poll_ready n elems in
      enq_select p ps e
  end.

  Goal poll_ready 0 [pkg_create (taskid 0) (finishid 1, 0) PKG_INIT []] =
    ([pkg_create (taskid 0) (finishid 1, 0) PKG_INIT []], (1, [])).
  Proof.
    compute.
    trivial.
  Qed.

  Goal poll_ready 1 [pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1]] =
    ([pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1]], (2, [])).
  Proof.
    compute.
    trivial.
  Qed.

  Fixpoint add_all (s:state) (n:nat) (elems:list package) {struct elems} : ((state + run_err) * (nat * list package)) % type:=
  match elems with
  | nil => (inl s, (n, nil))
  | p::ps =>
    match ps with
    | nil => add1 s n p
    | _ =>
      let result := add_all s n ps in
      match fst result with
      | inl s' => add1 s' n p
      | _ => result
      end
    end
  end.

  Definition buffer :=  Map_FID.t enq.

  Structure checks := {
    checks_buffer : buffer;
    checks_state : state;
  }.

  Definition buffer_add (p:package) (b:buffer) : (list package * buffer) :=
  let f := pkg_id p in
  let e := enq_cons p (match Map_FID.find f b with
  | Some e => e
  | None => enq_zero
  end) in
  let (l, e) := poll_ready (fst e) (snd e) in
  (l, Map_FID.add f e b).

  Goal buffer_add (pkg_create (taskid 0) (finishid 1, 0) PKG_INIT []) (Map_FID.empty _) =
    ([pkg_create (taskid 0) (finishid 1, 0) PKG_INIT []], Map_FID.add (finishid 1) (1, []) (Map_FID.empty _)).
  Proof.
    compute.
    trivial.
  Qed.

  Goal 
    let p := pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1] in
    let m := Map_FID.add (finishid 1) (1, []) (Map_FID.empty _) in
    buffer_add p m = ([p], Map_FID.add (finishid 1) (2, []) m).
  Proof.
    compute.
    trivial.
  Qed.

  Fixpoint buffer_add_all (ps:list package) (b:buffer) :=
  match ps with
  | [] => ([], b)
  | p::ps =>
    let (ps1, b) := buffer_add p b in
    let (ps2, b) := buffer_add_all ps b in
    (ps1 ++ ps2, b)
  end.

  Goal
    let l := [
      pkg_create (taskid 0) (finishid 1, 0) PKG_INIT []
    ] in
    let m := Map_FID.add (finishid 1) (1, []) (Map_FID.empty _) in
    buffer_add_all l (Map_FID.empty _) = (l, m).
  Proof.
    compute.
    trivial.
  Qed.

  Goal
    let l := [
      pkg_create (taskid 0) (finishid 1, 0) PKG_INIT [];
      pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1]
    ] in
    let m := Map_FID.add (finishid 1) (1, []) (Map_FID.empty _) in
    buffer_add_all l (Map_FID.empty _) = (l, Map_FID.add (finishid 1) (2, []) m).
  Proof.
    compute.
    trivial.
  Qed.

  (** Regression test: *)
  Goal
    let foo := [
      pkg_create (taskid 0) (finishid 1, 0) PKG_INIT [];
      pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1];
      pkg_create (taskid 1) (finishid 2, 0) PKG_BEGIN_FINISH [];
      pkg_create (taskid 1) (finishid 2, 1) PKG_BEGIN_TASK [2];
      pkg_create (taskid 2) (finishid 3, 0) PKG_BEGIN_FINISH [];
      pkg_create (taskid 2) (finishid 3, 1) PKG_BEGIN_TASK [5]
    ] in
    fst (buffer_add_all foo (Map_FID.empty _)) = foo.
  Proof.
   compute.
   trivial.
  Qed.

  (** Regression test: *)
  Goal
    let foo := [
      pkg_create (taskid 0) (finishid 0, 0) PKG_INIT [];
      pkg_create (taskid 0) (finishid 1, 0) PKG_BEGIN_FINISH []
    ] in
    fst (buffer_add_all foo (Map_FID.empty _)) = foo.
  Proof.
   compute.
   trivial.
  Qed.

  Fixpoint parse_trace (l:list package) : option (list action) :=
  match l with
  | [] => Some []
  | p::l =>
    match pkg_parse_op p, parse_trace l with
    | Some o, Some l => Some ((pkg_task p, o)::l)
    | _, _ => None
    end
  end.

  Goal
    let l := [
      pkg_create (taskid 0) (finishid 1, 0) PKG_INIT [];
      pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1];
      pkg_create (taskid 1) (finishid 2, 0) PKG_BEGIN_FINISH [];
      pkg_create (taskid 1) (finishid 2, 1) PKG_BEGIN_TASK [2];
      pkg_create (taskid 2) (finishid 3, 0) PKG_BEGIN_FINISH [];
      pkg_create (taskid 2) (finishid 3, 1) PKG_BEGIN_TASK [5]
    ] in
    parse_trace l = Some [
      (taskid 0, INIT (finishid 1));
      (taskid 0, BEGIN_TASK (taskid 1));
      (taskid 1, BEGIN_FINISH (finishid 2));
      (taskid 1, BEGIN_TASK (taskid 2));
      (taskid 2, BEGIN_FINISH (finishid 3));
      (taskid 2, BEGIN_TASK (taskid 5))
    ].
  Proof.
   compute.
   trivial.
  Qed.

  Fixpoint reduces_n (s:state) (l:list action): (state + reduces_err) % type :=
  match l with
  | [] => inl s
  | a::l =>
    match reduces s (fst a) (snd a) with
    | inl s =>
      reduces_n s l
    | inr e => inr e
    end
  end.

  Let checks_add_aux ps b s : (checks + run_err) %type :=
  match parse_trace ps with
  | Some l =>
    match reduces_n s l with
    | inl s => inl {| checks_buffer := b; checks_state := s |}
    | inr e => inr (REDUCES_ERROR e)
    end
  | None => inr (PKG_ERROR PARSE_ERROR)
  end.

  Definition checks_add (p:package) s : (checks + run_err) %type :=
  let (ps, b) := buffer_add p (checks_buffer s) in
  checks_add_aux ps b (checks_state s).

  Definition checks_make := {|
    checks_buffer := Map_FID.empty _;
    checks_state := Map_TID.empty _
  |}.

  Definition count_enqueued s :=
    List.fold_left (fun accum y => accum + length (snd y)) (Map_FID_Extra.values (checks_buffer s)) 0.
(*
  Inductive load_err :=
  | LOAD_ERROR: nat -> run_err -> load_err.
*)
  Definition checks_load (l:list package) : (checks + run_err) % type :=
  let (ps, b) := buffer_add_all l (Map_FID.empty _) in
  checks_add_aux ps b (Map_TID.empty _).
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

Extraction "libhsem/lib/finish"
  checks_add checks_make count_enqueued nat_to_op nat_to_args op_to_nat.
