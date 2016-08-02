Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
Require Import Aniceto.Pair.
Require Import Aniceto.List.

Require Import Regmode.
Require Import Vars.
Require Import Node.

Section Defs.

  Inductive op :=
  | ASYNC : tid -> op
  | ASYNC_PHASED : tid -> regmode -> op
  | SIGNAL: op
  | WAIT: op
  | DROP: op
  | CONTINUE: op.

  Definition event := (tid * op) % type.

  Notation edge := (node * node) %type.

  Inductive IsSeq : op -> Prop :=
  | is_seq_signal: IsSeq SIGNAL
  | is_seq_wait: IsSeq WAIT
  | is_seq_drop: IsSeq DROP
  | is_seq_continue: IsSeq CONTINUE.

  Inductive IsPar : op -> tid -> Prop :=
  | is_par_async: forall x, IsPar (ASYNC x) x
  | is_par_phased: forall x r, IsPar (ASYNC_PHASED x r) x.

  Let is_par o :=
  match o with
  | ASYNC x => Some x
  | ASYNC_PHASED x _ => Some x
  | _ => None
  end.

  Let is_par_some:
    forall o x,
    is_par o = Some x ->
    IsPar o x.
  Proof.
    intros.
    destruct o; simpl in *; inversion H; subst; auto using is_par_async, is_par_phased.
  Qed.

  Let is_pair_some_prop:
    forall o x,
    IsPar o x ->
    is_par o = Some x.
  Proof.
    intros.
    inversion H; auto.
  Qed.

  Let is_pair_some_spec:
    forall o x,
    is_par o = Some x <-> IsPar o x.
  Proof.
    split; auto.
  Qed.

  Let is_par_none:
    forall o,
    is_par o = None ->
    IsSeq o.
  Proof.
    intros.
    destruct o; simpl in *; inversion H; subst;
    auto using is_seq_signal, is_seq_drop, is_seq_continue, is_seq_wait.
  Qed.

  Let is_pair_none_prop:
    forall o,
    IsSeq o ->
    is_par o = None.
  Proof.
    intros.
    inversion H; auto.
  Qed.

  Let is_pair_none_spec:
    forall o,
    is_par o = None <-> IsSeq o.
  Proof.
    split; auto.
  Qed.

  Definition update_nodes vs (e:event) :=
  let (x, o) := e in
  match is_par o with
  | Some y => y::x::vs
  | _ => x::vs
  end.

  (** Annotates the nodes with a phase number. *)

  Definition phases := (Map_TID.t node * MN.t nat) % type.

  Inductive GetPhase : tid -> nat -> phases -> Prop :=
  | get_phase_def:
    forall (n:node) x w ns phs,
    Map_TID.MapsTo x n ns -> (* get the last node *)
    MN.MapsTo n w phs -> (* get the phase number *)
    GetPhase x w (ns, phs).

  Let get_phase (x:tid) (ws:phases) :=
  let (ns, phs) := ws in
  match Map_TID.find x ns with
  | Some n =>
    match MN.find n phs with
    | Some ph => Some ph
    | _ => None
    end
  | _ => None
  end.

  Let get_phase_some:
    forall x ws n,
    get_phase x ws = Some n ->
    GetPhase x n ws.
  Proof.
    unfold get_phase; intros.
    destruct ws as (ns, phs).
    destruct (Map_TID_Extra.find_rw x ns) as [(R,?)|(n',(R,?))];
    rewrite R in *; clear R. {
      inversion H.
    }
    destruct (MN_Extra.find_rw n' phs) as [(R,?)|(?,(R,?))];
    rewrite R in *; clear R. {
      inversion H.
    }
    inversion H; subst.
    eauto using get_phase_def.
  Qed.

  Let get_phase_some_prop:
    forall x ws n,
    GetPhase x n ws ->
    get_phase x ws = Some n.
  Proof.
    unfold get_phase; intros.
    inversion H; subst; clear H.
    destruct (Map_TID_Extra.find_rw x ns) as [(R,?)|(n',(R,?))];
    rewrite R in *; clear R. {
      contradiction H.
      eauto using Map_TID_Extra.mapsto_to_in.
    }
    assert (n' = n0) by eauto using Map_TID_Facts.MapsTo_fun; subst.
    destruct (MN_Extra.find_rw n0 phs) as [(R,?)|(?,(R,?))];
    rewrite R in *; clear R. {
      contradiction H2.
      eauto using MN_Extra.mapsto_to_in.
    }
    assert (x0 = n) by eauto using MN_Facts.MapsTo_fun; subst.
    trivial.
  Qed.

  Inductive SetPhase vs : phases -> tid -> nat -> phases -> Prop :=
  | set_phase_def:
    forall n ns ps x ph,
    MapsTo x n vs ->
    SetPhase vs (ns,ps) x ph (Map_TID.add x n ns, MN.add n ph ps).

  Let set_phase vs (ws:phases) (x:tid) ph :=
  let (ns,ps) := ws in
  match lookup TID.eq_dec x vs with
  | Some n => Some (Map_TID.add x n ns, MN.add n ph ps)
  | _ => None
  end.

  Let set_phase_some:
    forall vs ws x ph ws',
    set_phase vs ws x ph = Some ws' ->
    SetPhase vs ws x ph ws'.
  Proof.
    unfold set_phase; intros.
    destruct ws as (ns,ps).
    remember (lookup _ _ _).
    symmetry in Heqo.
    destruct o. {
      apply lookup_some in Heqo.
      inversion H; subst.
      auto using set_phase_def.
    }
    inversion H.
  Qed.

  Inductive Inc vs ws x : phases -> Prop :=
  | inc_def:
    forall ph ws',
    GetPhase x ph ws ->
    SetPhase vs ws x (S ph) ws' ->
    Inc vs ws x ws'.

  Let inc vs ws x : option phases :=
  match get_phase x ws with
  | Some ph => set_phase vs ws x (S ph)
  | _ => None
  end.

  Inductive Drop: phases -> tid -> phases -> Prop :=
  | drop_def:
    forall ns ps x,
    Drop (ns, ps) x (Map_TID.remove x ns, ps).

  Let drop (x:tid) (ws:phases) : phases := let (ns, ps) := ws in (Map_TID.remove x ns, ps).

  Inductive Copy vs ws x y ws' : Prop :=
  | copy_def:
    forall ph,
    GetPhase x ph ws ->
    SetPhase vs ws y ph ws' ->
    Copy vs ws x y ws'.

  Let copy vs x y ws :=
  match get_phase x ws with
  | Some ph => set_phase vs ws y ph
  | _ => None
  end.

  Inductive UpdateWP (vs:list tid) (ws:phases): event -> phases -> Prop :=
  | update_wp_async:
    forall x y,
    UpdateWP vs ws (x, ASYNC y) ws
  | update_wp_phased:
    forall ws' x y r,
    CanWait r ->
    Copy vs ws x y ws' ->
    UpdateWP vs ws (x, ASYNC_PHASED y r) ws'
  | update_wp_signal:
    forall x,
    UpdateWP vs ws (x, SIGNAL) ws
  | upate_wp_wait:
    forall x ws',
    Inc vs ws x ws' ->
    UpdateWP vs ws (x, WAIT) ws'
  | upate_wp_drop:
    forall x ws',
    Drop ws x ws' ->
    UpdateWP vs ws (x, DROP) ws'
  | upate_wp_continue:
    forall x,
    UpdateWP vs ws (x, CONTINUE) ws.

  Definition update_wp vs (e:event) (wp:phases) : option phases :=
  let (x, o) := e in
  match o with
  | ASYNC_PHASED y r =>
    if can_wait_dec r then copy vs x y wp
    else None
  | WAIT => inc vs wp x
  | DROP => Some (drop x wp)
  | _ => Some wp
  end.

  Inductive UpdateSP (vs:list tid) (ws:phases): event -> phases -> Prop :=
  | update_sp_async:
    forall x y,
    UpdateSP vs ws (x, ASYNC y) ws
  | update_sp_phased:
    forall ws' x y r,
    CanSignal r ->
    Copy vs ws x y ws' ->
    UpdateSP vs ws (x, ASYNC_PHASED y r) ws'
  | update_sp_signal:
    forall x ws',
    Inc vs ws x ws' ->
    UpdateSP vs ws (x, SIGNAL) ws'
  | upate_sp_wait:
    forall x,
    UpdateSP vs ws (x, WAIT) ws
  | upate_sp_drop:
    forall x ws',
    Drop ws x ws' ->
    UpdateSP vs ws (x, DROP) ws'
  | upate_sp_continue:
    forall x,
    UpdateSP vs ws (x, CONTINUE) ws.

  Definition update_sp vs (e:event) wp :=
  let (x, o) := e in
  match o with
  | ASYNC_PHASED y r =>
    if can_signal_dec r then copy vs x y wp
    else None
  | SIGNAL => inc vs wp x
  | DROP => Some (drop x wp)
  | _ => Some wp
  end.

  (* Old nodes *)

  Inductive AddCEdges vs vs' : event -> list edge -> Prop :=
  | add_c_edges_def:
    forall x o n n',
    MapsTo x n vs ->
    MapsTo x n' vs' ->
    AddCEdges vs vs' (x,o) ((n, n')::nil).

  Let add_c_edges vs vs' (e:event) :=
  let (x, o) := e in
  match lookup TID.eq_dec x vs, lookup TID.eq_dec x vs' with
  | Some n, Some n' => Some ((n, n'):: nil)
  | _,_ => None
  end.

  (* Old nodes *)

  Inductive AddFEdges vs vs' : event -> list (node * node) -> Prop :=
  | add_f_edges_eq:
    forall x nx ny y o,
    MapsTo x nx vs ->
    MapsTo y ny vs' ->
    IsPar o y ->
    AddFEdges vs vs' (x, o) ((nx, ny)::nil)
  | fork_edge_neq:
    forall x o,
    IsSeq o ->
    AddFEdges vs vs' (x, o) nil.

  Let add_f_edges vs vs' (e:event) :=
  let (x, o) := e in
  match is_par o, lookup TID.eq_dec x vs with
  | Some y, Some nx =>
    match lookup TID.eq_dec y vs' with
    | Some ny => Some ((nx, ny)::nil)
    | _ => None
    end
  | _, _ => None
  end.

  Structure builder := {
    get_nodes: list tid;
    get_sp: phases;
    get_wp: phases
  }.

  Definition Phase n ph (sp:phases) := MN.MapsTo n ph (snd sp).

  (** Get all nodes that signaled phase [ph]. *)

  Let phase ph (sp:phases) :=
  List.omap (fun (e:node*nat) =>
    let (n, s) := e in
    if eq_nat_dec s ph
    then Some n
    else None
  )
  (MN.elements (snd sp)).

  Inductive AddSEdges (b:builder) (vs':list tid) : event -> list (node * node) -> Prop :=
  | add_s_edges_eq:
    forall es x n ph,
    GetPhase x ph (get_wp b) ->
    MapsTo x n vs' ->
    (forall n', List.In (n, n') es <-> Phase n' (S ph) (get_sp b)) ->
    AddSEdges b vs' (x, WAIT) es
  | add_s_edges_neq:
    forall x o,
    o <> WAIT ->
    AddSEdges b vs' (x, o) nil.

  Let add_s_edges b (vs':list tid) (e:event) :=
  let (x, o) := e in
  match o with
  | WAIT =>
    match get_phase x (get_wp b), lookup TID.eq_dec x vs' with
    | Some ph, Some n =>
      Some (map (fun n' => (n, n')) (phase (S ph) (get_sp b)))
    | _, _ => None
    end
  | _ => Some nil
  end.

  Inductive UpdateBuilder (b:builder) : event -> builder -> Prop :=
  | update_builder_def:
    forall sp wp e,
    UpdateSP (update_nodes (get_nodes b) e) (get_sp b) e sp ->
    UpdateWP (update_nodes (get_nodes b) e) (get_wp b) e wp ->
    UpdateBuilder b e {| get_nodes:=update_nodes (get_nodes b) e; get_sp:=sp; get_wp:=wp |}.

  Let update_builder (e:event) b :=
  let vs := update_nodes (get_nodes b) e in
  match update_sp vs e (get_sp b), update_wp vs e (get_wp b) with
  | Some sp, Some wp => Some {| get_nodes:=vs; get_sp:=sp; get_wp:=wp |}
  | _, _ => None
  end.

  Structure computation_graph := {
    c_edges : list edge;
    f_edges : list edge;
    s_edges : list edge
  }.

  Inductive AddEdges (b b':builder) (cg:computation_graph) (e:event) : computation_graph -> Prop :=
  | add_edges_def:
    forall ec ef es,
    AddCEdges (get_nodes b) (get_nodes b') e ec ->
    AddFEdges (get_nodes b) (get_nodes b') e ef ->
    AddSEdges b (get_nodes b') e es -> 
    AddEdges b b' cg e
      {| c_edges := ec ++ c_edges cg; f_edges:= ef ++ f_edges cg; s_edges:= es ++ s_edges cg |}.

  Let add_edges (b b':builder) (e:event) (cg:computation_graph) : option computation_graph :=
  match add_c_edges (get_nodes b) (get_nodes b') e,
        add_f_edges (get_nodes b) (get_nodes b') e,
        add_s_edges b (get_nodes b') e with
  | Some ec, Some ef, Some es =>
    Some {| c_edges := ec ++ c_edges cg; f_edges:= ef ++ f_edges cg; s_edges:= es ++ s_edges cg |}
  | _,_,_ => None
  end.

  Inductive Add : builder * computation_graph -> event -> builder * computation_graph -> Prop :=
  | add_def:
    forall b b' cg cg' e,
    UpdateBuilder b e b' ->
    AddEdges b b' cg e cg' ->
    Add (b, cg) e (b', cg').

  Definition add (e:event) (bcg:builder * computation_graph) :=
  let (b, cg) := bcg in
  match update_builder e b with
  | Some b' =>
    match add_edges b b' e cg with
    | Some cg' => Some (b', cg')
    | _ => None
    end
  | _ => None
  end.

  Definition edges cg := (c_edges cg) ++ (f_edges cg) ++ (s_edges cg).
(*


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
    try (destruct (regmode_eq_dec r r0); subst; auto);
    try_absurd.
  Defined.

  Let edge_eq_dec := pair_eq_dec node_edge_eq_dec.



(*
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
*)
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
*)
End Defs.

Extraction "ocaml/cg.ml" add.
