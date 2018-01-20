Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import HJ.Finish.Lang.
Require Import HJ.Tid.
Require Import HJ.Fid.
Require Import Coq.Arith.EqNat.

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
    | 2, 0 => Some (END_FINISH pkg_fid)
    | 3, x => Some (BEGIN_TASK (taskid x))
    | 4, 0 => Some END_TASK
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

  Definition add1 s n p :=
  if beq_nat n (pkg_time p)
  then (run s p, (S n, nil))
  else (inl s, (n, p::nil)).

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

  Structure checks := {
    enqueued : Map_TID.t (list package);
    last_time : Map_TID.t nat;
    curr_state : state;
  }.

  Definition checks_add (p:package) s : (checks + run_err) %type :=
  let x := pkg_tid p in
  let ls := p::match Map_TID.find x (enqueued s) with
  | Some ls => ls
  | None => nil
  end in
  let n := match Map_TID.find x (last_time s) with
  | Some n => n
  | _ => 0
  end in
  let (s', y) := add_all (curr_state s) n ls in
  let (n, ls) := y in
  match s' with
  | inl s' =>  inl {|
      enqueued := Map_TID.add x ls (enqueued s);
      last_time := Map_TID.add x n (last_time s);
      curr_state := s'
    |}
  | inr x => inr x
  end.

  Definition checks_make := {|
    enqueued := Map_TID.empty _;
    last_time := Map_TID.empty _;
    curr_state := Map_TID.empty _
  |}.

  (** example of a reduction *)
  Goal
    forall p s',
    pkg_time p = 0 ->
    run (Map_TID.empty task) p = inl s'->
    checks_add p checks_make = inl {|
      enqueued := Map_TID.add (pkg_tid p) nil (Map_TID.empty _);
      last_time := Map_TID.add (pkg_tid p) 1 (Map_TID.empty _);
      curr_state := s'
    |}.
  Proof.
    intros.
    unfold checks_add, checks_make; simpl.
    unfold add1.
    remember (PeanoNat.Nat.eqb 0 (pkg_time p)).
    symmetry in Heqb.
    destruct b. {
      rewrite PeanoNat.Nat.eqb_eq in *.
      rewrite H0.
      trivial.
    }
    rewrite PeanoNat.Nat.eqb_neq in *.
    symmetry in H.
    contradiction.
  Qed.

  (** another unit test of a reduction *)
  Goal
    forall p s' s'',
    let e := Map_TID.add (pkg_tid p) nil (Map_TID.empty _) in
    let l := Map_TID.add (pkg_tid p) 1 (Map_TID.empty _) in
    let s := {|
      enqueued := e;
      last_time := l;
      curr_state := s'
    |} in
    pkg_time p = 1 ->
    run s' p = inl s'' ->
    checks_add p s = inl {|
      enqueued := Map_TID.add (pkg_tid p) nil e;
      last_time := Map_TID.add (pkg_tid p) 2 l;
      curr_state := s''
    |}.
  Proof.
    intros.
    unfold checks_add, checks_make; simpl.
    unfold add1.
    remember (PeanoNat.Nat.eqb 0 (pkg_time p)).
    symmetry in Heqb.
    destruct b. {
      rewrite PeanoNat.Nat.eqb_eq in *.
      rewrite H in *.
      inversion Heqb.
    }
    rewrite PeanoNat.Nat.eqb_neq in *.
    destruct (Map_TID_Extra.find_rw (pkg_tid p) e) as [(R,mt)|(?,(R,mt))];
    rewrite R in *; clear R. {
      unfold e in *.
      contradiction mt.
      rewrite Map_TID_Facts.add_in_iff.
      auto.
    }
    destruct (Map_TID_Extra.find_rw (pkg_tid p) l) as [(R,mt2)|(z,(R,mt2))];
    rewrite R in *; clear R. {
      unfold l in *.
      contradiction mt2.
      rewrite Map_TID_Facts.add_in_iff.
      auto.
    }
    assert (R: x = nil). {
      unfold e in *.
      rewrite Map_TID_Extra.P.F.add_mapsto_iff in *.
      destruct mt as [(?,?)|(?,?)]; auto.
      contradiction.
    }
    rewrite R; clear R.
    assert (R: z = 1). {
      unfold l in *.
      rewrite Map_TID_Extra.P.F.add_mapsto_iff in *.
      destruct mt2 as [(?,?)|(?,?)]; auto.
      contradiction.
    }
    subst.
    rewrite H0.
    remember (PeanoNat.Nat.eqb 1 (pkg_time p)).
    symmetry in Heqb0.
    destruct b. {
      trivial.
    }
    rewrite PeanoNat.Nat.eqb_neq in *.
    symmetry in H.
    contradiction.
  Qed.
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

Extraction "libhsem/lib/finish" checks_add checks_make.
