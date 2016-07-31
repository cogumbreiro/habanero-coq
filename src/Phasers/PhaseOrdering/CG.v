Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
Require Import Aniceto.Pair.
Require Import Aniceto.List.

Require Import Vars.
Require Import Node.

Section Defs.

  Inductive op :=
  | ASYNC : tid -> op
  | ASYNC_PHASED : tid -> op
  | SIGNAL: nat -> op
  | WAIT: nat -> op
  | DROP: nat -> op
  | PREC : op
  | CONTINUE: op.

  Definition event := (tid * op) % type.

  Notation edge := (node * node) %type.

  Inductive Phase ph : op -> Prop :=
  | phase_signal:
    Phase ph (SIGNAL ph)
  | phase_drop:
    Phase ph (DROP ph).

  Inductive Sync ph : (op * edge) -> node -> Prop:=
  | sync_def:
    forall o n n',
    Phase ph o ->
    Sync ph (o, (n, n')) n.

  Inductive WaitEdge (vs:list tid) ph (es:list (op * edge)) : op * edge -> Prop :=
  | wait_edge_def:
    forall e n',
    In e es ->
    Sync ph e n' ->
    WaitEdge vs ph es (PREC, (n',fresh vs)).

  Inductive Add vs (es:list (op*edge)) : event ->  list tid -> list (op * edge) -> Prop :=
  | add_async:
    forall x y n vs' es',
    Add vs es (x, CONTINUE) vs' es' ->
    MapsTo x n vs -> 
    Add vs es (x, ASYNC y) (y::vs') ((ASYNC y, (n, fresh vs')) :: es')
  | add_async_phased:
    forall x y vs' es' e,
    Add vs es (x, ASYNC y) vs' ((ASYNC y, e)::es') ->
    Add vs es (x, ASYNC_PHASED y) vs' ((ASYNC_PHASED y, e)::es')
  | add_signal:
    forall x vs' ph e,
    Add vs es (x, CONTINUE) vs' ((CONTINUE,e)::es) ->
    Add vs es (x, SIGNAL ph) vs' ((SIGNAL ph, e)::es)
  | add_wait:
    forall x ph vs' es' e,
    Add vs es (x, CONTINUE) vs' ((CONTINUE,e)::es) ->
    Forall (fun e => WaitEdge vs ph es e) es' ->
    Add vs es (x, WAIT ph) vs' (es' ++ (WAIT ph,e):: es)
  | add_drop:
    forall x vs' e n,
    Add vs es (x, CONTINUE) vs' ((CONTINUE, e)::es) ->
    Add vs es (x, DROP n) vs' ((DROP n,e):: es)
  | add_continue:
    forall x n,
    MapsTo x n vs ->
    Add vs es (x, CONTINUE) (x::vs) ((CONTINUE, (n, fresh vs))::es).

  Ltac try_absurd := try 
      (right; unfold not; intros N;
      inversion N;
      contradiction; fail).

  Lemma op_eq_dec (x y:op):
    { x = y } + { x <> y }.
  Proof.
    destruct x, y; auto;
    try (destruct (TID.eq_dec t t0); auto);
    try (destruct (TID.eq_dec n n0); auto);
    try_absurd.
  Defined.

  Let node_edge_eq_dec := pair_eq_dec node_eq_dec.

  Let edge_eq_dec := pair_eq_dec_2 op_eq_dec node_edge_eq_dec.

  Let phase_dec ph o :
    { Phase ph o } + { ~ Phase ph o }.
  Proof.
    destruct o; try_absurd;
    destruct (eq_nat_dec ph n); subst; auto using phase_signal, phase_drop; try_absurd.
  Defined.

  Let sync_dec (ph:nat) (e:op * edge) :
    { Sync ph e (fst (snd e)) } + { ~ Sync ph e (fst (snd e)) }.
  Proof.
    destruct e as (o, (n, n')).
    simpl.
    destruct (phase_dec ph o); auto using sync_def.
    try_absurd.
  Defined.

  Let wait_edge (vs:list tid) ph e :=
  if sync_dec ph e
  then Some (PREC, ((fst (snd e)), fresh vs))
  else None.

  Let wait_edges vs ph es := omap (wait_edge vs ph) es.

  Let wait_edge_some:
    forall e es x vs ph,
    In e es ->
    wait_edge vs ph e = Some x ->
    WaitEdge vs ph es x.
  Proof.
    unfold wait_edge; intros.
    destruct (sync_dec ph e);
    inversion H0; subst; clear H0.
    destruct e as (n, n').
    simpl in *.
    eauto using wait_edge_def.
  Qed.

  Let wait_edges_spec:
    forall vs ph es,
    Forall (fun e => WaitEdge vs ph es e) (wait_edges vs ph es).
  Proof.
    unfold wait_edges; intros.
    rewrite Forall_forall.
    intros.
    apply in_omap_2 in H.
    destruct H as  (e, (Hi, Hw)).
    eauto.
  Qed.

  Let do_add_continue vs es (x:tid) (n:node) :=
  ((x::vs), (CONTINUE, (n, fresh vs)) :: es).

  Let do_add_async vs es x (n:node) y :=
  let (vs', es') := do_add_continue vs es x n in
  ((y::vs'), ((ASYNC y, (n, fresh vs')) :: es')).

  Let do_add_async_phased vs es x (n:node) y :=
  let (vs', es') := do_add_continue vs es x n in
  ((y::vs'), ((ASYNC_PHASED y, (n, fresh vs')) :: es')).

  Let do_add_signal vs es (x:tid) ph (n:node) :=
  ((x::vs), (SIGNAL ph, (n, fresh vs)) :: es).

  Let do_add_wait vs es (x:tid) ph (n:node) :=
  ((x::vs), wait_edges vs ph es ++ (WAIT ph, (n, fresh vs)) :: es).

  Let do_add_drop vs es (x:tid) ph (n:node) :=
  ((x::vs), (DROP ph, (n, fresh vs)) :: es).

  (**
    Decidable implementation of adding an edge to the CG.
    *)

  Definition add vs es (e:event) :=
  let (x, o) := e in
  match lookup TID.eq_dec x vs with
  | Some n =>
    match o with
    | ASYNC y => Some (do_add_async vs es x n y)
    | ASYNC_PHASED y => Some (do_add_async_phased vs es x n y)
    | SIGNAL ph => Some (do_add_signal vs es x ph n)
    | WAIT ph => Some (do_add_wait vs es x ph n)
    | DROP ph => Some (do_add_drop vs es x ph n)
    | PREC => None
    | CONTINUE => Some (do_add_continue vs es x n)
    end
  | _ => None
  end.

  Lemma add_some:
    forall vs es e vs' es',
    add vs es e = Some (vs', es') ->
    Add vs es e vs' es'.
  Proof.
    unfold add; intros.
    destruct e as (x, o).
    remember (lookup _ _ _) as d.
    symmetry in Heqd.
    destruct d.
    apply lookup_some in Heqd. {
      destruct o; inversion H; subst; clear H;
      auto using add_async, add_continue,
                 add_async_phased, add_signal, add_wait, add_drop.
    }
    inversion H.
  Qed.

  Let add_to_in:
    forall vs es x o vs' es',
    Add vs es (x, o) vs' es' ->
    List.In x vs.
  Proof.
    intros.
    inversion H; subst; eauto using maps_to_to_in;
    try (inversion H4; subst; eauto using maps_to_to_in; fail).
    inversion H2; subst; eauto using maps_to_to_in.
  Qed.

  Lemma add_none:
    forall vs es e,
    add vs es e = None ->
    forall vs' es',
    ~ Add vs es e vs' es'.
  Proof.
    unfold add; intros.
    unfold not; intros N.
    destruct e as (x, o).
    remember (lookup _ _ _) as d.
    symmetry in Heqd.
    destruct d. {
      destruct o; inversion H.
      inversion N.
    }
    apply lookup_none in Heqd.
    contradiction Heqd.
    eauto using add_to_in.
  Qed.

  Inductive Build: list event -> list tid -> list (op * edge) -> Prop :=
  | build_nil:
    Build nil nil nil
  | build_cons_nil:
    forall x o vs es,
    Add (x::nil) nil (x,o) vs es -> 
    Build ((x,o)::nil) vs es
  | build_cons:
    forall e l vs es vs' es',
    Build l vs es ->
    Add vs es e vs' es' -> 
    Build (e::l) vs' es'.

  Fixpoint build l : option (list tid * list (op * edge)):=
  match l with
  | nil => Some (nil,nil)
  | (x,o) :: nil => add (x::nil) nil (x,o)
  | e :: l =>
    match build l with
    | Some (vs, es) => add vs es e
    | _ => None
    end
  end.

  Definition to_cg l :=
  match build l with
  | Some (_, es) => Some es
  | _ => None
  end.

  Lemma build_some:
    forall l vs es,
    build l = Some (vs, es) ->
    Build l vs es.
  Proof.
    induction l; intros. {
      inversion H; subst.
      auto using build_nil.
    }
    destruct a as (x,o).
    destruct l. {
      unfold build in H.
      apply add_some in H.
      auto using build_cons_nil.
    }
    remember (build (p::l)) as b.
    symmetry in Heqb.
    destruct b as [(a,b)|]; unfold build in H, Heqb; rewrite Heqb in *. {
      eauto using add_some, build_cons.
    }
    inversion H.
  Qed.

End Defs.

Extraction "ocaml/cg.ml" build to_cg.
