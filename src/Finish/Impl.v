Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import HJ.Finish.Lang.
Require Import HJ.Tid.
Require Import HJ.Fid.
Require Import Coq.Arith.EqNat.

Import ListNotations.

Module Queue.
  Section Defs.
  Variable A:Type.
  Variable time: A -> nat.

  Definition t := (nat * list A) % type.

  Definition make : t := (0, @nil A).

  Let curr (e:t) : nat := fst e.

  Let values (e:t) := snd e.

  Let empty n : t := (n, @nil A).

  Definition add p (e:t) := let (x, y) := e in (x, p :: y).

  (** Increments the current time of the queue. *)
  Let inc (e:t) := let (x, y) := e in (S x, y).

  Let step (n:nat) (elems:list A) :=
  let (l, r) :=
    partition (fun p => beq_nat n (time p)) elems
  in
  (l, (if beq_nat (length l) 0 then n else (S n), r)).

  Lemma partition_length:
    forall {A : Type} (f : A -> bool) (l : list A),
    length (fst (partition f l)) + length (snd (partition f l)) = length l.
  Proof.
    induction l. {
      simpl.
      trivial.
    }
    simpl.
    remember (f a).
    symmetry in Heqb.
    remember (partition f l).
    destruct p as (x, y).
    destruct b; simpl in *;
    auto with *.
  Qed.

  Let step_length:
    forall e l r n,
    step n e = (l, r) ->
    length l + length (snd r) = length e.
  Proof.
    induction e; intros; unfold step in *; simpl in *;
    inversion H; subst; clear H.
    - simpl.
      trivial.
    - remember (partition _ _).
      remember (length e) as z.
      symmetry in Heqz.
      rewrite <- partition_length with (f:=fun p : A => PeanoNat.Nat.eqb n (time p)) in Heqz.
      rewrite <- Heqp in *.
      remember (PeanoNat.Nat.eqb n _).
      symmetry in Heqb.
      destruct b. {
        rewrite PeanoNat.Nat.eqb_eq in *.
        rewrite Heqb in *; clear Heqb.
        destruct p as (a1, b1).
        remember (PeanoNat.Nat.eqb _ _).
        symmetry in Heqb.
        destruct b. {
          rewrite PeanoNat.Nat.eqb_eq in *.
          simpl in *.
          inversion Heqb.
        }
        rewrite PeanoNat.Nat.eqb_neq in *.
        inversion H1; subst; clear H1.
        simpl.
        trivial.
      }
      rewrite PeanoNat.Nat.eqb_neq in *.
      destruct p as (a1, b1).
      remember (PeanoNat.Nat.eqb _ _).
      symmetry in Heqb0.
      destruct b. {
        rewrite PeanoNat.Nat.eqb_eq in *.
        inversion H1; subst; clear H1.
        simpl.
        rewrite Heqb0.
        simpl.
        trivial.
      }
      inversion H1; subst; clear H1.
      rewrite PeanoNat.Nat.eqb_neq in *.
      simpl.
      auto with *.
  Qed.

  Function poll (n:nat) (elems: list A) {measure length elems} :=
  let (l1, e1) := step n elems in
  match l1 with
  | nil => (l1, e1)
  | _ =>
    let (l2, e2) := poll (fst e1) (snd e1) in
    (l1 ++ l2, e2)
  end.
  Proof.
    intros.
    apply step_length in teq.
    rewrite <- teq.
    simpl.
    auto with *.
  Defined.
  End Defs.

  Goal @poll _ (fun (x:nat) => x) 0 [1; 0; 3; 2] = ([0; 1; 2; 3], (4, [])).
  Proof.
    compute.
    trivial.
  Qed.
End Queue.

Section Defs.

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

  Inductive pkg_parse_err :=
  | PKG_PARSE_NOARGS_EXPECTED
  | PKG_PARSE_TASK_EXPECTED.

  Structure package := make {
    pkg_task : tid;
    pkg_op: package_op;
    pkg_id: fid;
    pkg_time: nat;
    pkg_args: list nat;
    pkg_lineno: option nat;
  }.

  Definition pkg_parse p := 
  match pkg_op p, pkg_args p with
  | PKG_INIT, [] => inl (INIT (pkg_id p))
  | PKG_BEGIN_FINISH, [] => inl (BEGIN_FINISH (pkg_id p))
  | PKG_END_FINISH, [] => inl END_FINISH
  | PKG_BEGIN_TASK, [x] => inl (BEGIN_TASK (taskid x))
  | PKG_END_TASK, [] => inl END_TASK
  | PKG_BEGIN_TASK, _ => inr PKG_PARSE_TASK_EXPECTED
  | _, _ => inr PKG_PARSE_NOARGS_EXPECTED
  end.

  (** Test cases that catch bugs we found: *)

  Goal forall p e,
    pkg_args p <> [] ->
    pkg_op p <> PKG_BEGIN_TASK ->
    pkg_parse p = inr e ->
    e = PKG_PARSE_NOARGS_EXPECTED.
  Proof.
    intros.
    unfold pkg_parse in *.
    destruct p, pkg_op0; simpl in *;
    destruct pkg_args0; try contradiction;
    inversion H1; subst; clear H1; trivial.
  Qed.

  Goal forall p e,
    length (pkg_args p) <> 1 ->
    pkg_op p = PKG_BEGIN_TASK ->
    pkg_parse p = inr e ->
    e = PKG_PARSE_TASK_EXPECTED.
  Proof.
    intros.
    unfold pkg_parse in *.
    destruct p, pkg_op0; simpl in *;
    destruct pkg_args0; inversion H0; clear H0;
    inversion H1; subst; clear H1; auto.
    destruct pkg_args0; inversion H2; subst; auto.
  Qed.

  Goal forall p n,
    pkg_args p = [n] ->
    pkg_op p = PKG_BEGIN_TASK ->
    pkg_parse p = inl (BEGIN_TASK (taskid n)).
  Proof.
    intros.
    unfold pkg_parse.
    rewrite H0.
    rewrite H.
    trivial.
  Qed.

  Goal forall p,
    pkg_args p = [] ->
    pkg_op p <> PKG_BEGIN_TASK ->
    exists o, pkg_parse p = inl o.
  Proof.
    intros.
    unfold pkg_parse.
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
    pkg_lineno := None
  |}.

  Inductive run_err :=
  | RUN_PKG_PARSE_ERROR: pkg_parse_err -> run_err
  | RUN_REDUCES_ERROR: reduces_err -> run_err.

  Definition run (s:state) (p:package) : (state + run_err) % type :=
  match pkg_parse p with
  | inl o =>
    match Lang.reduces s (pkg_task p) o with
    | inl s' => inl s'
    | inr e => inr (RUN_REDUCES_ERROR e)
    end
  | inr e => inr (RUN_PKG_PARSE_ERROR e)
  end.

  Definition add1 s n p :=
  if beq_nat n (pkg_time p)
  then (run s p, (S n, nil))
  else (inl s, (n, p::nil)).

  Definition buffer :=  Map_FID.t (Queue.t package).

  Structure checks := {
    checks_buffer : buffer;
    checks_state : state;
  }.

  Definition buffer_add (p:package) (b:buffer) : (list package * buffer) :=
  let f := pkg_id p in
  let e := Queue.add p (match Map_FID.find f b with
  | Some e => e
  | None => Queue.make package
  end) in
  let (l, e) := Queue.poll pkg_time (fst e) (snd e) in
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
    let (ps1, b1) := buffer_add_all ps b in
    let (ps2, b2) := buffer_add p b1 in
    (ps2 ++ ps1, b2)
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
    let (l', b) := buffer_add_all l (Map_FID.empty _) in
    l = l' /\ Map_FID.MapsTo (finishid 1) (2, []) b.
  Proof.
    simpl.
    split;
    auto using Map_FID.add_1.
  Qed.

  Goal
    let l := [
      pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1]
    ] in
    let m := Map_FID.add (finishid 1) (0, l) (Map_FID.empty _) in
    buffer_add_all l (Map_FID.empty _) = ([], m).
  Proof.
    compute.
    trivial.
  Qed.

  Goal
    let l1 := [
      pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1]
    ] in
    let l2 := [
      pkg_create (taskid 0) (finishid 1, 0) PKG_INIT []
    ] in
    let l3 := [
      pkg_create (taskid 0) (finishid 1, 0) PKG_INIT [];
      pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1]
    ] in
    let m := Map_FID.add (finishid 1) (0, l1) (Map_FID.empty _) in
    buffer_add_all l2 m = (l3, Map_FID.add (finishid 1) (2, []) m).
  Proof.
    intros.
    compute.
    trivial.
  Qed.

  Goal
    let l := [
      pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1];
      pkg_create (taskid 0) (finishid 1, 0) PKG_INIT []
    ] in
    let (l', b) := buffer_add_all l (Map_FID.empty _) in
    l' = l /\ Map_FID.MapsTo (finishid 1) (2, []) b.
  Proof.
    simpl; split; auto using Map_FID.add_1.
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

  Inductive parse_trace_err :=
  PARSE_TRACE_ERR: nat -> pkg_parse_err -> parse_trace_err.

  Fixpoint parse_trace (l:list package) : (list action + parse_trace_err) :=
  match l with
  | [] => inl []
  | p::l =>
    match pkg_parse p, parse_trace l with
    | inl o, inl l => inl ((pkg_task p, o)::l)
    | _, inr e => inr e
    | inr e, _ => inr (PARSE_TRACE_ERR (length l) e)
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
    parse_trace l = inl [
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

  Inductive reduces_n_err :=
  | REDUCES_N_ERROR: nat -> reduces_err -> reduces_n_err.

  Fixpoint reduces_n (s:state) (l:list action): (state + reduces_n_err) % type :=
  match l with
  | [] => inl s
  | a::l =>
    match reduces s (fst a) (snd a) with
    | inl s =>
      reduces_n s l
    | inr e => inr (REDUCES_N_ERROR (length l) e)
    end
  end.

  Goal
    let l := [
      (taskid 0, INIT (finishid 0));
      (taskid 0, INIT (finishid 1))
    ] in
    reduces_n (Map_TID.empty _) l = inr (REDUCES_N_ERROR 0 (TASK_EXIST (taskid 0))).
  Proof.
    intros.
    simpl.
    destruct (in_dec (finishid 0) (Map_TID.empty _)). {
      apply not_in_empty in i.
      contradiction.
    }
    remember (Map_TID.add _ _ _) as m.
    destruct (in_dec (finishid 1) m). {
      subst.
      inversion i. {
        inversion H; subst; clear H.
        apply Map_TID_Facts.add_mapsto_iff in H0.
        destruct H0 as [(?,Hx)|(?,?)]. {
          subst.
          inversion Hx; subst; clear Hx.
        }
        rewrite Map_TID_Facts.empty_mapsto_iff in *.
        contradiction.
      }
      inversion H; subst; clear H.
      rewrite Map_TID_Facts.add_mapsto_iff in *.
      destruct H1 as [(?,Hx)|(?,?)]. {
        subst.
        inversion Hx; subst; clear Hx.
        contradiction.
      }
      rewrite Map_TID_Facts.empty_mapsto_iff in *.
      contradiction.
    }
    subst.
    compute.
    trivial.
  Qed.

  Inductive checks_err :=
  | CHECKS_REDUCES_N_ERROR: package -> reduces_err -> checks_err
  | CHECKS_INTERNAL_ERROR
  | CHECKS_PARSE_TRACE_ERROR: package -> pkg_parse_err -> checks_err.

  Fixpoint get {A} (n:nat) (l:list A) {struct l} : option A :=
  match l with
  | x :: l => 
    if Nat.eqb n (length l) then Some x
    else (
      if Nat.ltb n (length l) then get n l
      else None
    )
  | _ => None
  end.

  Goal
    let l := [
      (taskid 2, INIT (finishid 2));
      (taskid 1, INIT (finishid 1));
      (taskid 0, INIT (finishid 0))
    ] in
    get 0 l = Some (taskid 0, INIT (finishid 0)) /\
    get 1 l = Some (taskid 1, INIT (finishid 1)) /\
    get 2 l = Some (taskid 2, INIT (finishid 2)).
  Proof.
    compute.
    intuition.
  Qed.

  (** Correctness check: *)
  Let reduces_n_length:
    forall l s n e,
    reduces_n s l = inr (REDUCES_N_ERROR n e) ->
    n < length l.
  Proof.
    induction l; intros. {
      simpl in *.
      inversion H.
    }
    simpl in *.
    remember (reduces _ _ _).
    symmetry in Heqs0.
    destruct s0. {
      apply IHl in H.
      auto.
    }
    inversion H; subst; clear H.
    auto.
  Qed.

  Let checks_add_aux ps b s : (checks + checks_err) %type :=
  match parse_trace ps with
  | inl l =>
    match reduces_n s l with
    | inl s => inl {| checks_buffer := b; checks_state := s |}
    | inr (REDUCES_N_ERROR n e) =>
      match get n ps with
      | Some p => inr (CHECKS_REDUCES_N_ERROR p e)
      | None => inr CHECKS_INTERNAL_ERROR
      end
    end
  | inr (PARSE_TRACE_ERR n e) =>
    match get n ps with
    | Some p => inr (CHECKS_PARSE_TRACE_ERROR p e)
    | None => inr CHECKS_INTERNAL_ERROR
    end
  end.

  Definition checks_add (p:package) s : (checks + checks_err) %type :=
  let (ps, b) := buffer_add p (checks_buffer s) in
  checks_add_aux ps b (checks_state s).

  Definition checks_make := {|
    checks_buffer := Map_FID.empty _;
    checks_state := Map_TID.empty _
  |}.

  Definition checks_running s : list tid :=
    Map_TID_Extra.keys (checks_state s).

  Definition checks_enqueued s : list package :=
    List.fold_left (fun accum y => accum ++ (snd y)) (Map_FID_Extra.values (checks_buffer s)) [].

  Definition checks_load (l:list package) : (checks + checks_err) % type :=
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
Extract Inlined Constant List.rev => "List.rev".
Extract Inlined Constant List.partition => "List.partition".
Extract Inlined Constant List.filter => "List.filter".

(* pairs *)
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".

(* nat *)
Extract Inductive nat => int [ "0" "Pervasives.succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Constant plus => "(+)".
Extract Constant pred => "fun n -> Pervasives.max 0 (n-1)".
Extract Constant minus => "fun n m -> Pervasives.max 0 (n-m)".
Extract Constant mult => "( * )".
Extract Inlined Constant max => "Pervasives.max".
Extract Inlined Constant min => "Pervasives.min".
(*Extract Inlined Constant nat_beq => "(=)".*)
Extract Inlined Constant EqNat.beq_nat => "(=)".
Extract Inlined Constant EqNat.eq_nat_decide => "(=)".

Extract Inlined Constant Peano_dec.eq_nat_dec => "(=)".
Extract Inlined Constant PeanoNat.Nat.eqb => "( = )".

Extract Constant Compare_dec.nat_compare =>
 "fun n m -> if n=m then Eq else if n<m then Lt else Gt".
Extract Inlined Constant Compare_dec.leb => "(<=)".
Extract Inlined Constant Compare_dec.le_lt_dec => "(<=)".
Extract Inlined Constant Compare_dec.lt_dec => "(<)".
Extract Constant Compare_dec.lt_eq_lt_dec => "fun n m -> if n>m then None else Some (n<m)".

Extraction Language Ocaml.

Extraction "libhsem/src/finish"
  checks_add checks_make checks_load checks_enqueued checks_running nat_to_op nat_to_args op_to_nat.
