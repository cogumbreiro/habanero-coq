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

  Definition elements (e:t) := snd e.

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

  (* ------------------------------------------------------------------------ *)

  Let timed_package := (nat * package) % type.

  Let queue := Queue.t timed_package.

  Structure buffer := {
    buffer_f_queue : Map_FID.t queue;
    buffer_t_queue: Map_TID.t queue;
    buffer_next_tick: Map_TID.t nat;
  }.


  Structure checks := {
    checks_buffer : buffer;
    checks_state : state;
  }.

  Inductive checks_err :=
  | CHECKS_REDUCES_N_ERROR: package -> reduces_err -> checks_err
  | CHECKS_TASK_EXISTS_ERROR: package -> tid -> checks_err
  | CHECKS_INTERNAL_ERROR
  | CHECKS_PARSE_TRACE_ERROR: package -> pkg_parse_err -> checks_err.

  (**
    Goal: we want to have a lexicographic order on (task-time, target-time).

    Idea:
    When adding a a package to the buffer, wrap the package in a pair:
      (number, package) where number is the timestamp of the owner task.

    When we are adding an init or a spawn, we initialize the task-queue
    to zero.

    After we poll from the finish queues, we enqueue the operations
    in the task queue.

    Finally, we poll the operations from each task queue.
    *)

  Let f_queue_add (p:timed_package) (b:Map_FID.t queue) : (list timed_package * Map_FID.t queue) :=
  let f := pkg_id (snd p) in
  let q := match Map_FID.find f b with
    | Some e => e
    | None => Queue.make _
    end
  in
  let e := Queue.add p q in
  let (l, e) := Queue.poll (fun x => pkg_time (snd x)) (fst e) (snd e) in
  (l, Map_FID.add f e b).

  Goal f_queue_add
    (10, (pkg_create (taskid 0) (finishid 1, 0) PKG_INIT [])) (Map_FID.empty _) =
    ([(10, pkg_create (taskid 0) (finishid 1, 0) PKG_INIT [])], Map_FID.add (finishid 1) (1, []) (Map_FID.empty _)).
  Proof.
    compute.
    trivial.
  Qed.

  Goal 
    let p := (10, pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1]) in
    let m := Map_FID.add (finishid 1) (1, []) (Map_FID.empty _) in
    f_queue_add p m = ([p], Map_FID.add (finishid 1) (2, []) m).
  Proof.
    compute.
    trivial.
  Qed.

  Let t_queue_add p (m:Map_TID.t queue) :=
  let x := pkg_task (snd p) in
  let q := match Map_TID.find x m with
    | Some q => q
    | None => Queue.make _
    end
  in
  (Map_TID.add x (Queue.add p q) m).

  Let t_queue_add_all ps q := List.fold_right t_queue_add q ps.

  Let t_poll (q:queue) :
    (list package * queue) :=
  let (l,q) :=
    Queue.poll (@fst nat package) (fst q) (snd q)
  in
  (snd (List.split l), q).

  Let do_poll k (p:list package * Map_TID.t queue) :=
  let (l1, m) := p in
  match Map_TID.find k m with
  | Some q =>
    let (l2, q') := t_poll q in
    (l2 ++ l1, Map_TID.add k q' m)
  | _ => (l1, m)
  end.

  Let t_queue_poll_aux (l:list tid) (m:Map_TID.t queue) :=
  List.fold_right do_poll ([], m) l.

(*
  Let entries := (tid * queue) % type.

  Let do_poll (p:entries)  (accum:list package * list entries) :
  list package * list (tid * queue) :=
    let (k, q) := p in
    let (l1, m) := accum in
    let (l2, q') := t_poll q in
    (l2 ++ l1, (k, q') :: m).

  Let t_queue_poll_aux (m:list entries) : (list package * list entries) :=
  List.fold_right do_poll ([], []) m.

  Let t_queue_poll_aux_rw_cons:
    forall m x q l,
    t_queue_poll_aux (x::l) m = do_poll x ([], m) (t_queue_poll_aux l m).
  Proof.
    unfold t_queue_poll_aux.
    simpl.
    auto.
  Qed.
*)
  Let t_queue_poll (m:Map_TID.t queue) : (list package * Map_TID.t queue) :=
  t_queue_poll_aux (Map_TID_Extra.keys m) m.
  (*
  let do_poll k q (accum:list package * list entries) :=
    let (l1, m) := accum in
    let (l2, q') := t_poll q in
    (l2 ++ l1, Map_TID.add k q' m)

  in
  Map_TID.fold do_poll m ([], []).
  *)
(*
  Definition t_queue_poll (m:Map_TID.t queue) : (list package * Map_TID.t queue) :=
  let poll q := (Queue.poll fst (fst q) (snd q)) in
  let t_queue_poll_2 :=
    let trim (q:queue) : queue := snd (poll q) in
    Map_TID.map trim m
  in
  let t_queue_poll_1 : list package :=
    let do_queue (x:tid) (q:queue) (l:list package) : list package :=
      snd (List.split (fst (poll q)))
    in
    Map_TID.fold do_queue m []
  in
  (t_queue_poll_1, t_queue_poll_2).
*)
(*
  Let PollEq (x y:Map_TID.t (list package) * Map_TID.t queue) :=
    Map_TID.Equal (fst x) (fst y) /\ Map_TID.Equal (snd x) (snd y).

  Let PollEq_refl:
    forall x,
    PollEq x x.
  Proof.
    unfold PollEq; intros.
    split; auto;
    apply Map_TID_Facts.EqualSetoid_Reflexive.
  Qed.

  Let PollEq_symm:
    forall x y,
    PollEq x y ->
    PollEq y x.
  Proof.
    unfold PollEq; intros; destruct H; split; auto;
    apply Map_TID_Facts.EqualSetoid_Symmetric; auto.
  Qed.

  Let PollEq_trans:
    forall x y z,
    PollEq x y ->
    PollEq y z ->
    PollEq x z.
  Proof.
    unfold PollEq; intros; destruct H; destruct H0; split;
    eapply Map_TID_Facts.EqualSetoid_Transitive; eauto.
  Qed.
*)

  Let clock_package p (m:Map_TID.t nat) :=
  (* next we increment the timestamp *)
  let inc x m :=
    match Map_TID.find x m with
    | Some n => inl (n, Map_TID.add x (S n) m)
    | None => inr CHECKS_INTERNAL_ERROR
    end
  in
  match (pkg_op p) with
  | PKG_INIT =>
    let x := pkg_task p in
    match Map_TID.find x m with
    | None => inl (0, Map_TID.add x 1 m)
    | _ => inr (CHECKS_TASK_EXISTS_ERROR p x)
    end
  | PKG_BEGIN_TASK =>
    match inc (pkg_task p) m with
    | inl (n, m) =>
      match pkg_args p with
      | [ x ] =>
        match Map_TID.find (taskid x) m with
        | Some _ => inr (CHECKS_TASK_EXISTS_ERROR p (taskid x))
        | None => inl (n, Map_TID.add (taskid x) 0 m)
        end
      | _ => inl (n, m)
      end
    | inr e => inr e
    end
  | _ => inc (pkg_task p) m
  end.

  Let clock_package_init:
    forall p m m' n,
    pkg_op p = PKG_INIT ->
    clock_package p m = inl (n, m') ->
    n = 0 /\ m' = Map_TID.add (pkg_task p) 1 m.
  Proof.
    unfold clock_package; intros.
    rewrite H in *.
    destruct (Map_TID_Extra.find_rw (pkg_task p) m) as [(R,?)|(?,(R,?))];
    rewrite R in *; clear R;
    inversion H0; subst; clear H0.
    split; auto.
  Qed.

  Let clock_package_other:
    forall p m n m' n',
    pkg_op p <> PKG_INIT ->
    pkg_op p <> PKG_BEGIN_TASK ->
    Map_TID.MapsTo (pkg_task p) n m ->
    clock_package p m = inl (n', m') ->
    n' = n /\ m' = Map_TID.add (pkg_task p) (S n) m.
  Proof.
    unfold clock_package.
    intros.
    destruct (pkg_op p);
    try (contradiction);
    try (destruct (Map_TID_Extra.find_rw (pkg_task p) m) as [(R,?)|(?,(R,?))];
    rewrite R in *; destruct R);
    inversion H2; subst; clear H2;
        try match goal with
      H: Map_TID.MapsTo ?k ?v1 ?m, H2: Map_TID.MapsTo ?k ?v2 ?m |- _
    => assert (R: v1 = v2) by eauto using Map_TID_Facts.MapsTo_fun;
       rewrite R in *; clear H2 R
     end; auto.
  Qed.

  Let clock_package_begin_task:
    forall p m m' n n' x,
    pkg_op p = PKG_BEGIN_TASK ->
    Map_TID.MapsTo (pkg_task p) n m ->
    clock_package p m = inl (n', m') ->
    pkg_args p = [ x ] ->
    n' = n /\ m' = Map_TID.add (taskid x) 0 (Map_TID.add (pkg_task p) (S n) m).
  Proof.
    unfold clock_package; intros.
    rewrite H in *; clear H.
    rewrite H2 in *; clear H2.
    destruct (Map_TID_Extra.find_rw (pkg_task p) m) as [(R,?)|(?,(R,?))];
    rewrite R in *; destruct R. {
      inversion H1.
    }
    assert (x0 = n) by eauto using Map_TID_Facts.MapsTo_fun; subst.
    remember (Map_TID.add _ _ _) as m1.
    destruct (Map_TID_Extra.find_rw (taskid x) m1) as [(R,?)|(?,(R,?))];
    rewrite R in *; destruct R. {
      subst.
      inversion H1; subst; clear H1.
      auto.
    }
    inversion H1.
  Qed.

  Let clock_package_inv_maps_to:
    forall p m m' n,
    clock_package p m = inl (n, m') ->
    Map_TID.MapsTo (pkg_task p) (S n) m'.
  Proof.
    unfold clock_package.
    intros.
    destruct (pkg_op p);
    try (destruct (Map_TID_Extra.find_rw (pkg_task p) m) as [(R,?)|(?,(R,?))];
    rewrite R in *; destruct R);
    inversion H; subst; clear H; auto using Map_TID.add_1.
    destruct (pkg_args p). {
      inversion H2; subst; clear H2.
      auto using Map_TID.add_1.
    }
    destruct l. {
      remember (Map_TID.add _ _ _) as m1.
      destruct (Map_TID_Extra.find_rw (taskid n0) m1) as [(R,?)|(?,(R,?))];
      rewrite R in *; destruct R. {
        subst; inversion H2; subst; clear H2.
        assert (taskid n0 <> pkg_task p). {
          unfold not; intros R; rewrite R in *.
          contradict H.
          rewrite Map_TID_Facts.add_in_iff.
          auto.
        }
        auto using Map_TID.add_1, Map_TID.add_2.
      }
      inversion H2.
    }
    inversion H2; subst; clear H2.
    auto using Map_TID.add_1.
  Qed.

  Let checks_try_run ps b s : (checks + checks_err) %type :=
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

  Definition buffer_add (p:package) b : ((list package * buffer) + checks_err) %type :=
  match clock_package p (buffer_next_tick b) with
  | inl (n, next_tick) =>
    let (ps, qf) := f_queue_add (n, p) (buffer_f_queue b) in
    let qt := t_queue_add_all ps (buffer_t_queue b) in
    let (ps, qt) := t_queue_poll qt in
    inl (ps, {| buffer_f_queue := qf; buffer_t_queue := qt; buffer_next_tick := next_tick |})
  | inr e => inr e
  end.

  Definition buffer_make := {|
    buffer_f_queue := Map_FID.empty _;
    buffer_t_queue := Map_TID.empty _;
    buffer_next_tick := Map_TID.empty _;
  |}.

  Definition checks_make := {|
    checks_buffer := buffer_make;
    checks_state := Map_TID.empty _
  |}.

  Definition checks_add (p:package) s : (checks + checks_err) %type :=
  match buffer_add p (checks_buffer s) with
  | inl (ps, b) => checks_try_run ps b (checks_state s)
  | inr e => inr e
  end.

  Definition checks_running s : list tid :=
  Map_TID_Extra.keys (checks_state s).

  Let to_packages (l:list queue) :=
  let l := List.flat_map (@Queue.elements timed_package) l in
  snd (List.split l).

  Definition checks_f_enqueued s : list package :=
  to_packages (Map_FID_Extra.values (buffer_f_queue (checks_buffer s))).

  Definition checks_t_enqueued s : list package :=
  to_packages (Map_TID_Extra.values (buffer_t_queue (checks_buffer s))).

  Definition checks_enqueued s : list package :=
  checks_f_enqueued s ++ checks_t_enqueued s.

  Definition checks_load (l:list package) : (checks + checks_err) % type :=
  let fix buffer_add_all l m :=
    match l with
    | [] => inl m
    | p::l => 
      match buffer_add_all l m with
      | inl m => checks_add p m
      | inr e => inr e
      end
    end
  in
  buffer_add_all l checks_make.

  Section TestFAdd.

    Let clock_package_1:
        clock_package (pkg_create (taskid 0) (finishid 1, 0) PKG_INIT [])
         (buffer_next_tick buffer_make) = inl
         (0,
         Map_TID.add (taskid 0) 1 (Map_TID.empty nat)).
    Proof.
      auto.
    Qed.

    Let f_queue_add_1:
      f_queue_add (0, pkg_create (taskid 0) (finishid 1, 0) PKG_INIT [])
         (buffer_f_queue buffer_make) = 
       ([(0, pkg_create (taskid 0) (finishid 1, 0) PKG_INIT [])],
       Map_FID.add (finishid 1) (1, []) (Map_FID.empty queue)).
    Proof.
      auto.
    Qed.

    Let t_queue_add_all_1:
      forall n p,
      t_queue_add_all [(n, p)]
              (buffer_t_queue buffer_make) =
      Map_TID.add (pkg_task p) (0, [(n, p)]) (Map_TID.empty queue).
    Proof.
      intros.
      unfold t_queue_add_all; simpl.
      unfold t_queue_add; simpl.
      trivial.
    Qed.
    Goal
      let p :=
        pkg_create (taskid 0) (finishid 1, 0) PKG_INIT []
      in
      exists b, buffer_add p buffer_make = inl ([p], b).
    Proof.
      simpl.
      unfold buffer_add.
      rewrite clock_package_1.
      remember (f_queue_add _ _).
      unfold f_queue_add in Heqp.
      simpl in Heqp.
      rewrite f_queue_add_1.
      rewrite t_queue_add_all_1.
      remember (pkg_task _).
      simpl in Heqt; rewrite Heqt; clear Heqt.
      remember (t_queue_poll _ ).
      compute in Heqp0.
      destruct p0 as (a,b).
      compute in Heqp0.
      inversion Heqp0; subst.
      eauto.
    Qed.

    (** Unit-test add *)

    Let buffer_add_all :=
    let fix f ps (b:buffer) :=
      match ps with
      | [] => inl ([], b)
      | p::ps =>
        match buffer_add p b with
        | inl (ps1, b1) =>
          match f ps b1 with
          | inl (ps2, b2) => inl (ps2 ++ ps1, b2)
          | inr e => inr e
          end
        | inr e => inr e
        end
      end
    in
    f.

    Goal
      let l := [
        pkg_create (taskid 0) (finishid 1, 0) PKG_INIT []
      ] in
      exists b, buffer_add_all l buffer_make = inl (l, b).
    Proof.
      simpl.
      eauto.
    Qed.

    Goal 
      exists m, 
      clock_package
          (pkg_create (taskid 0) (finishid 1, 0) PKG_INIT [])
          (Map_TID.empty _)
      = inl (0, m) /\ Map_TID.MapsTo (taskid 0) 1 m.
    Proof.
      unfold clock_package.
      simpl.
      eauto using Map_TID.add_1.
    Qed.

    Goal
      let l := [
        pkg_create (taskid 0) (finishid 1, 0) PKG_INIT [];
        pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1]
      ] in
      exists b, buffer_add_all l buffer_make = inl (l, b).
    Proof.
      simpl; eauto.
      unfold buffer_add_all.
      unfold buffer_add.
      remember (clock_package _ _).
      unfold clock_package in Heqs.
      remember (pkg_op _).
      simpl in Heqp.
      rewrite Heqp in *; clear Heqp.
      remember (pkg_task _) as x.
      remember (buffer_next_tick _) as m.
      destruct (Map_TID_Extra.find_rw x m) as [(R,?)|(?,(R,?))]; rewrite R in *; clear R. {
        assert (s = inl (0, Map_TID.add x (S 0) (Map_TID.add x 0 m))). {
          assert (Hx: Map_TID.MapsTo x 0 (Map_TID.add x 0 m)) by eauto using Map_TID.add_1.
          rewrite Map_TID_Facts.find_mapsto_iff in *.
          rewrite Hx in *.
          assumption.
        }
        rewrite H0.
      }
      remember (Map_TID.find _ _).
      
      remember (pkg_args _).
      simpl in Heql.
      rewrite Heql in *; clear Heql.
      simpl in Heqs.
      compute in Heqs.
      simpl.
      simpl.
      eauto.
      split;
      auto using Map_FID.add_1.
    Qed.

    Goal
      let l := [
        (10, pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1])
      ] in
      let m := Map_FID.add (finishid 1) (0, l) (Map_FID.empty _) in
      buffer_add_all l (Map_FID.empty _) = ([], m).
    Proof.
      compute.
      trivial.
    Qed.

    Goal
      let l1 := [
        (10, pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1])
      ] in
      let l2 := [
        (20, pkg_create (taskid 0) (finishid 1, 0) PKG_INIT [])
      ] in
      let l3 := [
        (20, pkg_create (taskid 0) (finishid 1, 0) PKG_INIT []);
        (10, pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1])
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
        (10, pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1]);
        (20, pkg_create (taskid 0) (finishid 1, 0) PKG_INIT [])
      ] in
      let (l', b) := buffer_add_all l (Map_FID.empty _) in
      l' = l /\ Map_FID.MapsTo (finishid 1) (2, []) b.
    Proof.
      simpl; split; auto using Map_FID.add_1.
    Qed.

    (** Regression test: *)
    Goal
      let foo := [
        (10, pkg_create (taskid 0) (finishid 1, 0) PKG_INIT []);
        (11, pkg_create (taskid 0) (finishid 1, 1) PKG_BEGIN_TASK [1]);
        (12, pkg_create (taskid 1) (finishid 2, 0) PKG_BEGIN_FINISH []);
        (13, pkg_create (taskid 1) (finishid 2, 1) PKG_BEGIN_TASK [2]);
        (14, pkg_create (taskid 2) (finishid 3, 0) PKG_BEGIN_FINISH []);
        (15, pkg_create (taskid 2) (finishid 3, 1) PKG_BEGIN_TASK [5])
      ] in
      fst (buffer_add_all foo (Map_FID.empty _)) = foo.
    Proof.
     compute.
     trivial.
    Qed.

    (** Regression test: *)
    Goal
      let foo := [
        (10, pkg_create (taskid 0) (finishid 0, 0) PKG_INIT []);
        (11, pkg_create (taskid 0) (finishid 1, 0) PKG_BEGIN_FINISH [])
      ] in
      fst (buffer_add_all foo (Map_FID.empty _)) = foo.
    Proof.
     compute.
     trivial.
    Qed.
  End TestFAdd.
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
  checks_add checks_make checks_load checks_enqueued checks_t_enqueued
  checks_f_enqueued checks_running nat_to_op nat_to_args op_to_nat.
