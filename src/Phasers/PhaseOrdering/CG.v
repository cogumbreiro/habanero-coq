Require Import Aniceto.Graphs.Graph.
Require Import Aniceto.Graphs.FGraph.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Aniceto.Pair.
Require Import Aniceto.List.

Require Import Phasers.Taskview.
Require Import Regmode.
Require Import Vars.
Require Import Node.
Require Import Phasers.Phaser.

Section Defs.

  Notation edge := (node * node) %type.

  Inductive IsSeq : op -> Prop :=
  | is_seq_signal: IsSeq SIGNAL
  | is_seq_wait: IsSeq WAIT
  | is_seq_drop: IsSeq DROP.

  Inductive IsPar : op -> tid -> Prop :=
  | is_par_def: forall r, IsPar (REGISTER r) (get_task r).

  Let is_par o :=
  match o with
  | REGISTER r => Some (get_task r)
  | _ => None
  end.

  Let is_par_some:
    forall o x,
    is_par o = Some x ->
    IsPar o x.
  Proof.
    intros.
    destruct o; simpl in *; inversion H; subst; auto using is_par_def.
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
    auto using is_seq_signal, is_seq_drop, is_seq_wait.
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

  Definition ph_empty : phases := (Map_TID.empty node, MN.empty nat).

  Definition ph_make (x:tid) : phases :=
  let n := (fresh (A:=tid) nil) in
  (Map_TID.add x n (Map_TID.empty node), MN.add n 0 (MN.empty nat)).

  Inductive GetPhase : tid -> nat -> phases -> Prop :=
  | get_phase_def:
    forall (n:node) x w ns phs,
    Map_TID.MapsTo x n ns -> (* get the last node *)
    MN.MapsTo n w phs -> (* get the phase number *)
    GetPhase x w (ns, phs).

  Inductive Registered x ws : Prop :=
  | registered_def:
    forall ph,
    GetPhase x ph ws ->
    Registered x ws.

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

  Notation Phase n ph sp := (MN.MapsTo n ph (snd sp)).
  Notation In n sp := (MN.In n (snd sp)).

  Inductive SetPhase vs : phases -> tid -> nat -> phases -> Prop :=
  | set_phase_def:
    forall n ns ps x ph,
    MapsTo x n vs ->
    ~ MN.In n ps ->
    SetPhase vs (ns,ps) x ph (Map_TID.add x n ns, MN.add n ph ps).

  Let set_phase vs (ws:phases) (x:tid) ph :=
  let (ns,ps) := ws in
  match lookup TID.eq_dec x vs with
  | Some n =>
    match MN.find n ps with
    | None => Some (Map_TID.add x n ns, MN.add n ph ps)
    | _ => None
    end
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
      destruct (MN_Extra.find_rw n ps) as [(R,?)|(?,(R,?))];
      rewrite R in *. {
        inversion H; subst; auto using set_phase_def.
      }
      inversion H.
    }
    inversion H.
  Qed.

  Inductive Inc vs ws x : phases -> Prop :=
  | inc_def:
    forall ph ws',
    GetPhase x ph ws ->
    SetPhase vs ws x (S ph) ws' ->
    Inc vs ws x ws'.

  Inductive TryInc vs ws x : phases -> Prop :=
  | try_inc_ok:
    forall ws',
    Inc vs ws x ws' ->
    TryInc vs ws x ws'
  | try_inc_skip:
    ~ Registered x ws ->
    TryInc vs ws x ws.

  Let is_registered x sp :
    { Registered x sp } + { ~ Registered x sp }.
  Proof.
    remember (get_phase x sp).
    symmetry in Heqo.
    destruct o. {
      eauto using registered_def.
    }
    right.
    unfold not; intros N.
    destruct N.
    apply get_phase_some_prop in H.
    rewrite H in *.
    inversion Heqo.
  Defined.

  Let inc vs ws x : option phases :=
  match get_phase x ws with
  | Some ph => set_phase vs ws x (S ph)
  | _ => None
  end.

  Let try_inc vs sp x :=
  if is_registered x sp then inc vs sp x else Some sp.

  Definition drop (x:tid) (ws:phases) : phases := let (ns, ps) := ws in (Map_TID.remove x ns, ps).

  Inductive Copy vs sp x y sp' :=
  | copy_def:
    forall ph,
    GetPhase x ph sp ->
    SetPhase vs sp y ph sp' ->
    Copy vs sp x y sp'.

  Let copy vs x y sp : option phases :=
  match get_phase x sp with
  | Some ph => set_phase vs sp y ph
  | _ => None
  end.

  Inductive TryCopy vs sp x y : phases -> Prop :=
  | try_copy_ok:
    forall sp',
    Copy vs sp x y sp' ->
    TryCopy vs sp x y sp'
  | try_copy_skip:
    ~ Registered x sp ->
    TryCopy vs sp x y sp.

  Let registered x sp :
    { Registered x sp } + { ~ Registered x sp }.
  Proof.
    intros.
    destruct sp as (ts, ns).
    remember (Map_TID.find x ts).
    symmetry in Heqo.
    destruct o. {
      rewrite <- Map_TID_Facts.find_mapsto_iff in *.
      remember (MN.find n ns).
      symmetry in Heqo0.
      destruct o. {
        left.
        rewrite <- MN_Facts.find_mapsto_iff in *.
        eauto using registered_def, get_phase_def.
      }
      right; unfold not; intros N.
      inversion N.
      inversion H; subst; clear H.
      assert (n0 = n) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      rewrite MN_Facts.find_mapsto_iff in *.
      rewrite H5 in *.
      inversion Heqo0.
    }
    right; unfold not; intros N.
    inversion N.
    inversion H; subst; clear H.
    rewrite Map_TID_Facts.find_mapsto_iff in *.
    rewrite H4 in *.
    inversion Heqo.
  Defined.

  Let try_copy vs x y sp : option phases :=
  if registered x sp then copy vs x y sp
  else Some sp.

  Inductive UpdateWP (vs:list tid) (wp:phases): event -> phases -> Prop :=
  | update_wp_register_ok:
    forall wp' x r wp'',
    CanWait (get_mode r) ->
    Copy vs wp x (get_task r) wp' ->
    Copy vs wp' x x wp'' ->
    UpdateWP vs wp (x, REGISTER r) wp''
  | update_wp_register_skip:
    forall x r wp',
    ~ CanWait (get_mode r) ->
    TryCopy vs wp x x wp' ->
    UpdateWP vs wp (x, REGISTER r) wp'
  | update_wp_signal:
    forall x wp',
    TryCopy vs wp x x wp' ->
    UpdateWP vs wp (x, SIGNAL) wp'
  | update_wp_wait:
    forall x wp',
    Inc vs wp x wp' ->
    UpdateWP vs wp (x, WAIT) wp'
  | update_wp_drop:
    forall x,
    UpdateWP vs wp (x, DROP) (drop x wp).

  Definition update_wp vs (e:event) (wp:phases) : option phases :=
  let (x, o) := e in
  match o with
  | REGISTER r =>
    if can_wait (get_mode r) then
      match copy vs x (get_task r) wp with
      | Some wp => copy vs x x wp
      | _ => None
      end
    else try_copy vs x x wp
  | WAIT => inc vs wp x
  | DROP => Some (drop x wp)
  | SIGNAL => try_copy vs x x wp
  end.

  Inductive UpdateSP (vs:list tid) (sp:phases): event -> phases -> Prop :=
  | update_sp_register_ok:
    forall sp' sp'' x r,
    CanSignal (get_mode r) ->
    Copy vs sp x (get_task r) sp' ->
    Copy vs sp' x x sp'' ->
    UpdateSP vs sp (x, REGISTER r) sp''
  | update_sp_register_skip:
    forall x r sp',
    ~ CanSignal (get_mode r) ->
    TryCopy vs sp x x sp' ->
    UpdateSP vs sp (x, REGISTER r) sp'
  | update_sp_signal:
    forall x sp',
    Inc vs sp x sp' ->
    UpdateSP vs sp (x, SIGNAL) sp'
  | update_sp_wait:
    forall x sp',
    TryCopy vs sp x x sp' ->
    UpdateSP vs sp (x, WAIT) sp'
  | update_sp_drop:
    forall x,
    UpdateSP vs sp (x, DROP) (drop x sp).

  Definition update_sp vs (e:event) sp :=
  let (x, o) := e in
  match o with
  | REGISTER r =>
    if can_signal (get_mode r) then
      match copy vs x (get_task r) sp with
      | Some sp => copy vs x x sp
      | _ => None
      end
    else try_copy vs x x sp
  | WAIT => try_copy vs x x sp
  | DROP => Some (drop x sp)
  | SIGNAL => inc vs sp x
  end.

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
  | add_f_edges_is_pair:
    forall x nx ny y o,
    MapsTo x nx vs ->
    MapsTo y ny vs' ->
    IsPar o y ->
    AddFEdges vs vs' (x, o) ((nx, ny)::nil)
  | add_f_edges_is_seq:
    forall x o,
    IsSeq o ->
    AddFEdges vs vs' (x, o) nil.

  Let add_f_edges vs vs' (e:event) :=
  let (x, o) := e in
  match is_par o with
  | Some y =>
    match lookup TID.eq_dec x vs, lookup TID.eq_dec y vs' with
    | Some nx, Some ny => Some ((nx, ny)::nil)
    | _,_ => None
    end
  | None => Some nil
  end.

  Structure builder := {
    get_nodes: list tid;
    get_sp: phases;
    get_wp: phases;
    node_to_op: MN.t op
  }.

  Definition builder_empty :=
  {| get_nodes := nil;
     get_sp:= ph_empty;
     get_wp := ph_empty;
     node_to_op:=MN.empty op |}.

  Definition builder_make x :=
  {| get_nodes := (x::nil);
     get_sp := ph_make x;
     get_wp := ph_make x;
     node_to_op := MN.empty op |}.

  (** Get all nodes that signaled phase [ph]. *)

  Let phase ph (sp:phases) :=
  List.omap (fun (e:node*nat) =>
    let (n, s) := e in
    if eq_nat_dec s ph
    then Some n
    else None
  )
  (MN.elements (snd sp)).

  Inductive WaitEdge b : (node * node) -> tid -> node -> nat -> Prop :=
  | wait_edge_def:
    forall x y n n' ph,
    Phase n ph (get_sp b) ->
    TaskOf n y (get_nodes b) ->
    y <> x ->
    WaitEdge b (n, n') x n' ph.

  Inductive AddSEdges (b:builder) (vs':list tid) : event -> list (node * node) -> Prop :=
  | add_s_edges_eq:
    forall es x n ph,
    GetPhase x ph (get_wp b) ->
    MapsTo x n vs' ->
    (forall e, List.In e es <-> WaitEdge b e x n ph) ->
    AddSEdges b vs' (x, WAIT) es
  | add_s_edges_neq:
    forall x o,
    o <> WAIT ->
    AddSEdges b vs' (x, o) nil.

  Definition filter_phases ec ns :=
  let handle_edge (e:node * node) :=
    if in_dec node_eq_dec (fst e) ns then
    (if in_dec node_eq_dec (snd e) ns then true else false)
    else false
  in
  let blacklist := fst (split (filter handle_edge ec)) in
  set_diff node_eq_dec ns blacklist.

  Definition wait_edges ec b x (n:node) ph :=
  let handle (n':node) :=
    match task_of n' (get_nodes b) with
    | Some y =>
      (* check for self edges *)
      if TID.eq_dec y x then None
      else
      
      Some (n', n)
    | _ => None
    end
  in
  List.omap handle (filter_phases ec (phase ph (get_sp b))).

  Let add_s_edges ec b (vs':list tid) (e:event) :=
  let (x, o) := e in
  match o with
  | WAIT =>
    match get_phase x (get_wp b), lookup TID.eq_dec x vs' with
    | Some ph, Some n =>
      Some (wait_edges ec b x n ph)
    | _, _ => None
    end
  | _ => Some nil
  end.

  Let phase_2:
    forall (a:node) a' b ph sp,
    List.In (b, a') (map (fun c' => (c', a)) (phase ph sp)) ->
    Phase b ph sp /\ a' = a.
  Proof.
    unfold phase; intros.
    apply in_map_iff in H.
    destruct H as (x, (Heq, Hin)).
    inversion Heq; subst.
    apply in_omap_2 in Hin.
    destruct Hin as ((n,ph'), (Hin, Heq')).
    destruct (eq_nat_dec ph' ph). {
      subst.
      inversion Heq'; subst; clear Heq'.
      apply MN_Extra.in_elements_impl_maps_to in Hin.
      auto.
    }
    inversion Heq'.
  Qed.

  Let phase_1:
    forall (a:node) b ph sp,
    Phase b ph sp ->
    List.In (b, a) (map (fun c => (c, a)) (phase ph sp)).
  Proof.
    unfold phase; intros.
    rewrite in_map_iff.
    exists b; split; auto.
    apply in_omap_1 with (x:=(b,ph)). {
      apply MN_Extra.maps_to_iff_in_elements; auto.
    }
    destruct (eq_nat_dec ph ph). {
      trivial.
    }
    intuition.
  Qed.

  Inductive UpdateOps (vs:list tid) (m:MN.t op): event -> MN.t op -> Prop :=
  | update_ops_def:
    forall n x o,
    MapsTo x n vs ->
    UpdateOps vs m (x, o) (MN.add n o m).

  Let update_ops (vs:list tid) (e:event) (m:MN.t op) :=
  let (x, o) := e in
  match lookup TID.eq_dec x vs with
  | Some n => Some (MN.add n o m)
  | _ => None
  end.

  Inductive UpdateBuilder (b:builder) : event -> builder -> Prop :=
  | update_builder_def:
    forall sp wp e m,
    let vs' := update_nodes (get_nodes b) e in
    UpdateSP vs' (get_sp b) e sp ->
    UpdateWP vs' (get_wp b) e wp ->
    UpdateOps (get_nodes b) (node_to_op b) e m ->
    UpdateBuilder b e
    {| get_nodes := vs';
       get_sp := sp;
       get_wp := wp;
       node_to_op := m |}.

  Let update_builder (e:event) b :=
  let vs' := update_nodes (get_nodes b) e in
  match update_sp vs' e (get_sp b),
        update_wp vs' e (get_wp b),
        update_ops (get_nodes b) e (node_to_op b) with
  | Some sp, Some wp, Some m =>
    Some {| get_nodes:=vs'; get_sp:=sp; get_wp:=wp; node_to_op := m |}
  | _,_,_ => None
  end.

  Structure computation_graph := {
    c_edges : list edge;
    f_edges : list edge;
    s_edges : list edge
  }.

  Definition cg_edges cg := c_edges cg ++ f_edges cg ++ s_edges cg.

  Definition cg_empty : computation_graph := {| c_edges:= nil; f_edges:=nil; s_edges:=nil|}.

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
        add_s_edges (c_edges cg) b (get_nodes b') e with
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

  Inductive WaitPhase x n ph : Prop :=
  | wait_phase_def:
    forall v,
    Map_TID.MapsTo x v ph ->
    CanWait (Taskview.mode v) ->
    Taskview.wait_phase v = n ->
    WaitPhase x n ph.

  Inductive SignalPhase x n ph : Prop :=
  | signal_phase_def:
    forall v,
    Map_TID.MapsTo x v ph ->
    CanSignal (Taskview.mode v) ->
    Taskview.signal_phase v = n ->
    SignalPhase x n ph.

  Lemma set_phase_to_get_phase:
    forall vs sp t ph sp',
    SetPhase vs sp t ph sp' ->
    GetPhase t ph sp'.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply get_phase_def with (n:=n); eauto using Map_TID.add_1, MN.add_1.
  Qed.

  Lemma get_phase_fun:
    forall t ph ph' sp,
    GetPhase t ph sp ->
    GetPhase t ph' sp ->
    ph' = ph.
  Proof.
    intros.
    inversion H; inversion H0; subst; clear H H0.
    inversion H10; subst; clear H10.
    assert (n0 = n) by eauto using Map_TID_Facts.MapsTo_fun; subst.
    eauto using MN_Facts.MapsTo_fun.
  Qed.

  Lemma inc_inv:
    forall vs sp t sp',
    Inc vs sp t sp' ->
    exists n, GetPhase t n sp /\ GetPhase t (S n) sp'.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply set_phase_to_get_phase in H1.
    eauto.
  Qed.

  Let try_inc_inv:
    forall vs sp t sp',
    TryInc vs sp t sp' ->
    (~ Registered t sp /\ sp' = sp) \/ exists n, (GetPhase t n sp /\ GetPhase t (S n) sp').
  Proof.
    intros.
    destruct H. {
      eauto using inc_inv.
    }
    auto.
  Qed.

  Notation WFPhases ts ns :=
  (forall x n, Map_TID.MapsTo x n ts ->
  MN.In n ns).

  Definition WF_Phases (sp:phases) := (WFPhases (fst sp) (snd sp)).

  Let set_phase_3:
    forall x ps' ps y vs ph ph',
    WF_Phases ps ->
    GetPhase x ph ps' ->
    y <> x ->
    SetPhase vs ps y ph' ps' ->
    GetPhase x ph ps.
  Proof.
    intros.
    inversion H2; subst; clear H2.
    inversion H0; subst; clear H0.
    apply Map_TID.add_3 in H8; auto.
    rewrite MN_Facts.add_mapsto_iff in *.
    destruct H9 as [(?,?)|(?,?)]. {
      subst.
      contradiction H4.
      apply H in H8.
      auto.
    }
    eauto using get_phase_def.
  Qed.

  Let set_phase_2:
    forall x y n ps ph ps' vs,
    WF_Phases ps ->
    y <> x ->
    GetPhase x n ps ->
    SetPhase vs ps y ph ps' ->
    GetPhase x n ps'.
  Proof.
    intros.
    inversion H2; subst; clear H2.
    inversion H1; subst; clear H1.
    apply get_phase_def with (n:=n1).
    - eauto using Map_TID.add_2.
    - apply MN.add_2; auto.
      unfold not; intros; subst.
      contradiction H4.
      simpl in *.
      apply H in H8.
      assumption.
  Qed.

  Let inc_2:
    forall x y n ps ps' vs,
    WF_Phases ps ->
    y <> x ->
    GetPhase x n ps ->
    Inc vs ps y ps' ->
    GetPhase x n ps'.
  Proof.
    intros.
    inversion H2; subst.
    eauto.
  Qed.

  Let try_inc_2:
    forall x y n ps ps' vs,
    WF_Phases ps ->
    y <> x ->
    GetPhase x n ps ->
    TryInc vs ps y ps' ->
    GetPhase x n ps'.
  Proof.
    intros.
    inversion H2; subst. {
      eauto.
    }
    auto.
  Qed.

  Lemma inc_3:
    forall vs t n sp' sp x,
    WF_Phases sp ->
    GetPhase t n sp' ->
    Inc vs sp x sp' ->
    x <> t ->
    GetPhase t n sp.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    eapply set_phase_3 in H4; eauto.
  Qed.

  Let try_inc_3:
    forall vs t n sp' sp x,
    WF_Phases sp ->
    GetPhase t n sp' ->
    TryInc vs sp x sp' ->
    x <> t ->
    GetPhase t n sp.
  Proof.
    intros.
    inversion H1; subst; clear H1. {
      inversion H3; subst; clear H3.
      eapply set_phase_3 in H4; eauto.
    }
    auto.
  Qed.

  Lemma signal_phase_signal_2:
    forall x y ph n,
    x <> y ->
    SignalPhase x n ph ->
    SignalPhase x n (Phaser.signal y ph).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eauto using signal_phase_def, signal_2.
  Qed.

  Lemma signal_phase_drop_2:
    forall x y ph n,
    x <> y ->
    SignalPhase x n ph ->
    SignalPhase x n (Phaser.drop y ph).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eauto using signal_phase_def, drop_2.
  Qed.

  Lemma signal_phase_wait_2:
    forall x n ph y,
    SignalPhase x n ph ->
    SignalPhase x n (Phaser.wait y ph).
  Proof.
    intros.
    inversion H; subst; clear H.
    destruct (TID.eq_dec x y). {
      subst.
      eauto using signal_phase_def, wait_mapsto_spec.
    }
    eauto using wait_2, signal_phase_def.
  Qed.

  Let wait_phase_drop:
    forall x n ph y,
    x <> y ->
    WaitPhase x n ph ->
    WaitPhase x n (Phaser.drop y ph).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eauto using drop_2, wait_phase_def.
  Qed.

  Lemma drop_inv:
    forall sp x y n,
    GetPhase y n (drop x sp) ->
    x <> y /\ GetPhase y n sp.
  Proof.
    unfold drop; intros.
    destruct sp as (ns, ps).
    inversion H; subst; clear H.
    destruct (TID.eq_dec x y). {
      subst.
      apply Map_TID_Extra.mapsto_to_in in H4.
      rewrite Map_TID_Facts.remove_in_iff in *.
      destruct H4 as (N,_).
      intuition.
    }
    split; auto.
    apply Map_TID.remove_3 in H4.
    eauto using get_phase_def.
  Qed.

  Let get_phase_3:
    forall x y n n' ns ps,
    y <> x ->
    GetPhase x n (Map_TID.add y n' ns, ps) ->
    GetPhase x n (ns, ps).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    rewrite Map_TID_Facts.add_mapsto_iff in *.
    destruct H5 as [(N,_)|(_, ?)]. {
      contradiction.
    }
    eauto using get_phase_def.
  Qed.

  Lemma copy_3:
    forall vs x y z sp sp' n,
    WF_Phases sp ->
    z <> y ->
    GetPhase z n sp' ->
    Copy vs sp x y sp' ->
    GetPhase z n sp.
  Proof.
    intros.
    inversion H2; subst; clear H2; eauto.
  Qed.

  Lemma copy_inv_eq:
    forall vs x y ps ps' n,
    GetPhase y n ps' ->
    Copy vs ps x y ps' ->
    GetPhase x n ps.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    apply set_phase_to_get_phase in H2.
    assert (n=ph) by eauto using get_phase_fun; subst.
    trivial.
  Qed.

  Let get_phase_2:
    forall x y n n' ns ps, 
    x <> y ->
    GetPhase x n (ns, ps) ->
    GetPhase x n (Map_TID.add y n' ns, ps).
  Proof.
    intros.
    inversion H0; subst.
    apply get_phase_def with (n:=n0); auto.
    rewrite Map_TID_Facts.add_mapsto_iff in *.
    auto.
  Qed.

  Lemma copy_2:
    forall x y z ps ps' n vs,
    WF_Phases ps ->
    z <> y ->
    Copy vs ps x y ps' ->
    GetPhase z n ps ->
    GetPhase z n ps'.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    eapply set_phase_2 in H4; eauto.
  Qed.

  Lemma copy_1:
    forall vs wp wp' x y n,
    Copy vs wp x y wp' ->
    GetPhase x n wp ->
    GetPhase y n wp'.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply set_phase_to_get_phase in H2.
    assert (ph=n) by eauto using get_phase_fun;subst.
    assumption.
  Qed.

  Lemma signal_phase_register_1:
    forall r x ph n,
    RegisterPre r x ph ->
    CanSignal (get_mode r) ->
    SignalPhase x n ph ->
    SignalPhase (get_task r) n (register r x ph).
  Proof.
    intros.
    inversion H1; subst; clear H1.
    eauto using signal_phase_def, register_spec.
  Qed.

  Lemma wait_phase_register_1:
    forall r x ph n,
    RegisterPre r x ph ->
    CanWait (get_mode r) ->
    WaitPhase x n ph ->
    WaitPhase (get_task r) n (register r x ph).
  Proof.
    intros.
    inversion H1; subst; clear H1.
    eauto using wait_phase_def, register_spec.
  Qed.

  Lemma signal_phase_register_2:
    forall x y n ph r,
    RegisterPre r y ph ->
    SignalPhase x n ph ->
    SignalPhase x n (register r y ph).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    inversion H; subst; clear H.
    destruct (TID.eq_dec (get_task r) x). {
      subst.
      contradiction H0.
      eauto using Map_TID_Extra.mapsto_to_in.
    }
    eauto using signal_phase_def, register_2.
  Qed.

  Lemma wait_phase_register_2:
    forall x y n ph r,
    RegisterPre r y ph ->
    WaitPhase x n ph ->
    WaitPhase x n (register r y ph).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    inversion H; subst; clear H.
    destruct (TID.eq_dec (get_task r) x). {
      subst.
      contradiction H0.
      eauto using Map_TID_Extra.mapsto_to_in.
    }
    eauto using wait_phase_def, register_2.
  Qed.

  Let get_phase_inv_eq:
    forall ph ph' x n ps ns,
    GetPhase x ph' (Map_TID.add x n ns, MN.add n ph ps) ->
    ph' = ph.
  Proof.
    intros.
    inversion H; subst; clear H.
    rewrite Map_TID_Facts.add_mapsto_iff in *.
    destruct H4 as [(?,?)|(N,_)]. {
      subst.
      rewrite MN_Facts.add_mapsto_iff in *.
      destruct H5 as [(_,?)|(N,_)]. {
        auto.
      }
      intuition.
    }
    intuition.
  Qed.

  Let get_phase_4:
    forall x ph ns n ph' ps y,
    WF_Phases (ns, ps) ->
    ~ MN.In n ps ->
    y <> x ->
    GetPhase x ph (Map_TID.add y n ns, MN.add n ph' ps) ->
    GetPhase x ph (ns, ps).
  Proof.
    intros.
    inversion H2; subst; clear H2.
    rewrite MN_Facts.add_mapsto_iff in *.
    rewrite Map_TID_Facts.add_mapsto_iff in *.
    destruct H7 as [(?,?)|(?,mt)]. {
      subst.
      intuition.
    }
    destruct H8 as [(?,?)|(?,?)]. {
      subst.
      contradiction H0.
      simpl in *.
      apply H in mt.
      auto.
    }
    eauto using get_phase_def.
  Qed.

  Let set_phase_1:
    forall x n sp sp' ph vs,
    GetPhase x n sp ->
    SetPhase vs sp x ph sp' ->
    GetPhase x ph sp'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    apply get_phase_def with (n:=n0).
    - auto using Map_TID.add_1.
    - auto using MN.add_1.
  Qed.
(*
  Let update_1:
    forall x n vs sp sp' y,
    WF_Phases sp ->
    GetPhase x n sp ->
    Copy vs sp y y sp' ->
    GetPhase x n sp'.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    destruct (TID.eq_dec x y). {
      subst.
      assert (n = ph) by (eapply get_phase_fun; eauto); subst.
      eapply set_phase_1; eauto.
    }
    eapply set_phase_2; eauto.
  Qed.

  Let update_3:
    forall x n sp' sp vs y,
    WF_Phases sp ->
    GetPhase x n sp' ->
    UpdatePhase vs sp y sp' ->
    GetPhase x n sp.
  Proof.
    intros.
    inversion H1; subst; clear H1; auto.
    inversion H3; subst; clear H3.
    destruct (TID.eq_dec x y). {
      subst.
      apply get_phase_inv_eq in H0.
      subst.
      assumption.
    }
    apply get_phase_4 in H0; auto.
  Qed.

  Let try_update_3:
    forall x n sp' sp vs y,
    WF_Phases sp ->
    GetPhase x n sp' ->
    TryUpdatePhase vs sp y sp' ->
    GetPhase x n sp.
  Proof.
    intros.
    inversion H1; subst; clear H1; auto.
    eapply update_3; eauto.
  Qed.
*)

  Lemma wf_phases_copy:
    forall vs x y sp sp',
    WF_Phases sp ->
    Copy vs sp x y sp' ->
    WF_Phases sp'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    unfold WF_Phases.
    inversion H2; subst; clear H2.
    simpl in *.
    intros.
    rewrite Map_TID_Facts.add_mapsto_iff in *.
    rewrite MN_Facts.add_in_iff in *.
    destruct H2 as [(?,?)|(?,?)]. {
      subst.
      auto.
    }
    apply H in H4.
    auto.
  Qed.

  Lemma copy_4:
    forall vs x y n sp sp',
    WF_Phases sp ->
    GetPhase y n sp' ->
    Copy vs sp x x sp' ->
    GetPhase y n sp.
  Proof.
    intros.
    destruct (TID.eq_dec x y). {
      subst.
      inversion H1; subst; clear H1.
      apply set_phase_to_get_phase in H3.
      assert (n = ph). {
        apply get_phase_fun with (t:=y) (sp:=sp'); auto.
      }
      subst.
      assumption.
    }
    apply copy_3 with (vs:=vs) (x:=x) (y:=x) (sp':=sp'); auto.
  Qed.
End Defs.

Section Props.

  Let SP_Sound (ph:Phaser.phaser) (sp:phases) : Prop :=
    forall x n,
    GetPhase x n sp ->
    SignalPhase x n ph.

  Let signal_eq:
    forall vs sp sp' ph t n,
    WF_Phases sp ->
    (forall x n, GetPhase x n sp -> SignalPhase x n ph) ->
    GetPhase t n sp' ->
    Phaser.SignalPre t ph ->
    Inc vs sp t sp' ->
    SignalPhase t n (Phaser.signal t ph).
  Proof.
    intros.
    apply inc_inv in H3.
    rename n into n'.
    destruct H3 as (n, (Hg1, Hg2)).
    apply H0 in Hg1.
    assert (n' = S n) by eauto using get_phase_fun; subst.
    inversion H2; subst; clear H2.
    apply signal_phase_def with (v:=Taskview.signal v).
    - rewrite Phaser.signal_rw with (v:=v); auto.
      auto using Map_TID.add_1.
    - rewrite Taskview.signal_preserves_mode.
      auto using signal_pre_to_can_signal.
    - inversion Hg1.
      subst.
      unfold signal.
      simpl.
      assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      trivial.
  Qed.

  Let sp_sound:
    forall vs' sp ph e ph' sp',
    WF_Phases sp ->
    WF_Phases sp' ->
    SP_Sound ph sp ->
    Phaser.Reduces ph e ph' ->
    UpdateSP vs' sp e sp' ->
    SP_Sound ph' sp'.
  Proof.
    unfold SP_Sound; intros.
    rename x into t.
    destruct e as (x, o).
    destruct o; inversion H2; simpl in *; subst;
    inversion H3; subst; clear H2 H3.
    - destruct (TID.eq_dec x t). {
        subst.
        eauto using signal_eq.
      }
      eapply inc_3 in H6; eauto using signal_phase_signal_2.
    - apply signal_phase_wait_2; inversion H6; subst; auto; clear H6.
      eauto using copy_4.
    - apply drop_inv with (y:=t) (n:=n) in H4; auto.
      destruct H4 as (Hx,Hy).
      auto using signal_phase_drop_2.
    - destruct (TID.eq_dec (get_task r) t). {
        subst.
        apply signal_phase_register_1; auto.
        eauto using wf_phases_copy, copy_inv_eq, copy_4.
      }
      apply copy_4 with (vs:=vs') (x:=x) (sp:=sp'0) in H4; eauto using wf_phases_copy;
      clear H11.
      apply signal_phase_register_2; auto.
      apply H1.
      apply copy_3 with (x:=x) (y:=get_task r) (vs:=vs') (sp':=sp'0); eauto.
    - inversion H10; subst; clear H10. {
        apply copy_4 with (vs:=vs') (x:=x) (sp:=sp) in H4; eauto using wf_phases_copy.
        apply signal_phase_register_2; auto.
      }
      assert (x <> t). {
        unfold not; intros; subst.
        contradiction H2.
        eauto using registered_def.
      }
      apply signal_phase_register_2; auto.
  Qed.

  Let WP_Sound (ph:Phaser.phaser) (sp:phases) : Prop :=
    forall x n,
    GetPhase x n sp ->
    WaitPhase x n ph.

  Let WP_Complete (ph:Phaser.phaser) (sp:phases) : Prop :=
    forall x n,
    WaitPhase x n ph ->
    GetPhase x n sp.

  Let SP_Complete (ph:Phaser.phaser) (wp:phases) : Prop :=
    forall x n,
    SignalPhase x n ph ->
    GetPhase x n wp.

  Lemma wait_phase_signal_1:
    forall x y n ph,
    WaitPhase x n ph ->
    WaitPhase x n (Phaser.signal y ph).
  Proof.
    intros.
    inversion H; subst; clear H.
    destruct (TID.eq_dec x y). {
      subst.
      apply wait_phase_def with (v:=Taskview.signal v);
      auto using signal_preserves_wait_phase, Phaser.signal_1.
    }
    apply wait_phase_def with (v:= v);
    auto using signal_preserves_wait_phase, signal_2.
  Qed.

  Let wp_wait_eq:
    forall x n ph,
    WaitPhase x n ph ->
    WaitPhase x (S n) (Phaser.wait x ph).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using wait_phase_def, Phaser.wait_1.
  Qed.

  Let wp_wait_neq:
    forall x y n ph,
    x <> y ->
    WaitPhase x n ph ->
    WaitPhase x n (Phaser.wait y ph).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eauto using wait_phase_def, Phaser.wait_2.
  Qed.

  Lemma wait_phase_drop_1:
    forall x y n ph,
    x <> y ->
    WaitPhase x n ph ->
    WaitPhase x n (Phaser.drop y ph).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eauto using wait_phase_def, Phaser.drop_2.
  Qed.

  Let wp_register:
    forall r x ph n,
    RegisterPre r x ph ->
    CanWait (get_mode r) ->
    WaitPhase x n ph ->
    WaitPhase (get_task r) n (register r x ph).
  Proof.
    intros.
    inversion H1; subst.
    eauto using wait_phase_def, register_spec.
  Qed.

  Let wp_register_neq:
    forall x y n ph r,
    RegisterPre r y ph ->
    WaitPhase x n ph ->
    WaitPhase x n (register r y ph).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    inversion H; subst; clear H.
    destruct (TID.eq_dec (get_task r) x). {
      subst.
      contradiction H0.
      eauto using Map_TID_Extra.mapsto_to_in.
    }
    eauto using wait_phase_def, register_2.
  Qed.

  Let wp_sound:
    forall vs wp ph e ph' wp',
    WF_Phases wp ->
    WP_Sound ph wp ->
    Phaser.Reduces ph e ph' ->
    UpdateWP vs wp e wp' ->
    WP_Sound ph' wp'.
  Proof.
    intros; unfold WP_Sound; intros.
    rename x into t.
    destruct e as  (x, []);
    inversion H1; simpl in *; subst;
    inversion H2; subst; clear H2 H1.
    - inversion H5; subst; clear H5. {
        eauto using wait_phase_signal_1, copy_4.
      }
      eauto using wait_phase_signal_1.
    - destruct (TID.eq_dec t x). {
        subst.
        apply inc_inv in H5.
        rename n into xw.
        destruct H5 as (n, (Hg1, Hg2)).
        assert (xw = S n) by eauto using get_phase_fun; subst.
        eauto.
      }
      eapply inc_3 in H5; eauto.
    - apply drop_inv in H3; auto.
      destruct H3 as (?, Hg).
      eauto using wait_phase_drop_1.
    - destruct (TID.eq_dec (get_task r) t). {
        subst.
        apply wait_phase_register_1; auto.
        eauto using wf_phases_copy, copy_inv_eq, copy_4.
      }
      apply copy_4 with (vs:=vs) (x:=x) (sp:=wp'0) in H3; eauto using wf_phases_copy.
      apply wait_phase_register_2; auto.
      apply H0.
      apply copy_3 with (x:=x) (y:=get_task r) (vs:=vs) (sp':=wp'0); eauto.
    - inversion H9; subst; clear H9. {
        apply copy_4 with (vs:=vs) (x:=x) (sp:=wp) in H3; eauto using wf_phases_copy.
      }
      assert (x <> t). {
        unfold not; intros; subst.
        contradiction H1.
        eauto using registered_def.
      }
      apply wait_phase_register_2; auto.
  Qed.

  Let wait_phase_inv_signal:
    forall x wp ph y,
    WaitPhase x wp (Phaser.signal y ph) ->
    WaitPhase x wp ph.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply signal_mapsto_inv in H0.
    destruct H0 as [(?,(v',(Heq,mt)))|(?,mt)]. {
      subst.
      rewrite signal_preserves_mode in *.
      rewrite signal_preserves_wait_phase.
      eauto using wait_phase_def.
    }
    eauto using wait_phase_def.
  Qed.

  Let signal_phase_inv_wait:
    forall x sp ph y,
    SignalPhase x sp (Phaser.wait y ph) ->
    SignalPhase x sp ph.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply wait_mapsto_inv in H0.
    destruct H0 as [(?,(v',(Heq,mt)))|(?,mt)]. {
      subst.
      rewrite wait_preserves_mode in *.
      rewrite wait_preserves_signal_phase.
      eauto using signal_phase_def.
    }
    eauto using signal_phase_def.
  Qed.

  Let wait_phase_inv_wait:
    forall x wp ph y,
    WaitPhase x wp (Phaser.wait y ph) ->
    (y = x /\ exists wp', wp = S wp' /\ WaitPhase x wp' ph) \/ (y <> x /\ WaitPhase x wp ph).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply wait_mapsto_inv in H0.
    destruct H0 as [(?, (v', (?, ?)))|(?,?)]. {
      subst; left; split; auto.
      rewrite wait_preserves_mode in *.
      exists (wait_phase v').
      split; auto.
      apply wait_phase_def with (v:=v'); auto.
    }
    eauto using wait_phase_def.
  Qed.

  Let signal_phase_inv_signal:
    forall x sp ph y,
    SignalPhase x sp (Phaser.signal y ph) ->
    (y = x /\ exists sp', sp = S sp' /\ SignalPhase x sp' ph) \/ (y <> x /\ SignalPhase x sp ph).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply signal_mapsto_inv in H0.
    destruct H0 as [(?, (v', (?, ?)))|(?,?)]. {
      subst; left; split; auto.
      rewrite signal_preserves_mode in *.
      exists (signal_phase v').
      split; auto.
      apply signal_phase_def with (v:=v'); auto.
    }
    eauto using signal_phase_def.
  Qed.

  Let get_phases_inc:
    forall x n ps ps' vs,
    GetPhase x n ps ->
    Inc vs ps x ps' ->
    GetPhase x (S n) ps'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    assert (ph = n) by eauto using get_phase_fun; subst.
    eauto using set_phase_to_get_phase.
  Qed.

  Let get_phases_set_phase_neq:
    forall x y n ps ps' n' vs,
    WF_Phases ps ->
    y <> x ->
    GetPhase x n ps ->
    SetPhase vs ps y n' ps' ->
    GetPhase x n ps'.
  Proof.
    intros.
    inversion H2; subst; clear H2.
    inversion H1; subst; clear H1.
    apply get_phase_def with (n:=n1).
    - auto using Map_TID.add_2.
    - apply MN.add_2; auto.
      unfold not; intros N.
      subst.
      contradiction H4.
      simpl in *.
      apply H in H8.
      assumption.
  Qed.

  Let get_phases_inc_neq:
    forall x y n ps ps' vs,
    WF_Phases ps ->
    y <> x ->
    GetPhase x n ps ->
    Inc vs ps y ps' ->
    GetPhase x n ps'.
  Proof.
    intros.
    inversion H2; subst; clear H2.
    eapply get_phases_set_phase_neq; eauto.
  Qed.

  Let wait_phase_drop_eq:
    forall x n y ph,
    WaitPhase x n (Phaser.drop y ph) ->
    y <> x /\ WaitPhase x n ph.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply drop_mapsto_inv in H0.
    destruct H0.
    split; auto.
    apply wait_phase_def with (v:=v); auto.
  Qed.

  Let signal_phase_drop_eq:
    forall x n y ph,
    SignalPhase x n (Phaser.drop y ph) ->
    y <> x /\ SignalPhase x n ph.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply drop_mapsto_inv in H0.
    destruct H0.
    split; auto.
    apply signal_phase_def with (v:=v); auto.
  Qed.

  Let wait_phase_drop_neq:
    forall x n y ph,
    y <> x ->
    WaitPhase x n ph ->
    WaitPhase x n (Phaser.drop y ph).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    apply wait_phase_def with (v:=v); auto using drop_2.
  Qed.

  Let get_phase_drop_neq:
    forall x y n sp,
    y <> x ->
    GetPhase x n sp ->
    GetPhase x n (drop y sp).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    simpl.
    apply get_phase_def with (n:=n0); auto.
    eauto using Map_TID.remove_2.
  Qed.

  Let wp_complete_reg_2:
    forall wp n ph x y r,
    WF_Phases wp ->
    WP_Complete ph wp ->
    WaitPhase x n (register r y ph) ->
    ~ CanWait (get_mode r) ->
    GetPhase x n wp.
  Proof.
    intros.
      destruct H1; subst.
      apply register_inv_mapsto in H1.
      destruct H1 as [?|(?, (v', (?,?)))]. {
        assert (WaitPhase x (wait_phase v) ph) by (apply wait_phase_def with (v:=v); auto).
        auto.
      }
      subst.
      rewrite mode_set_mode_rw in *.
      rewrite set_mode_preserves_wait_phase.
      contradiction.
  Qed.

  Let wp_complete_reg_3:
    forall vs wp ph t v r x wp',
    WF_Phases wp ->
    WP_Complete ph wp ->
    Map_TID.MapsTo t v ph ->
    RegisterPre r x ph ->
    CanWait (get_mode r) ->
    Copy vs wp x (get_task r) wp' ->
    CanWait (mode v) ->
    GetPhase t (wait_phase v) wp'.
  Proof.
    intros.
    assert (WaitPhase t (wait_phase v) ph) by (apply wait_phase_def with (v:=v); auto).
    apply H0 in H6.
    destruct (TID.eq_dec t (get_task r)). {
      subst.
      inversion H2.
      contradiction H7.
      eauto using Map_TID_Extra.mapsto_to_in.
    }
    eapply copy_2; eauto.
  Qed.

  Let wp_complete_reg_1:
    forall vs wp x ph t n r wp',
    WF_Phases wp ->
    WP_Complete ph wp ->
    WaitPhase t n (register r x ph) ->
    RegisterPre r x ph ->
    CanWait (get_mode r) ->
    Copy vs wp x (get_task r) wp' ->
    GetPhase t n wp'.
  Proof.
    intros.
    destruct H1; subst.
    apply register_inv_mapsto in H1.
    destruct H1 as [?|(?, (v', (?,?)))]. {
      eapply wp_complete_reg_3; eauto.
    }
    subst.
    rewrite mode_set_mode_rw in *.
    rewrite set_mode_preserves_wait_phase.
    assert (Hw: WaitPhase x (wait_phase v') ph). {
      apply wait_phase_def with (v:=v'); auto.
      inversion H2.
      assert (v'=v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      apply can_wait_le with (y:=get_mode r); auto.
    }
    apply H0 in Hw.
    apply copy_1 with (n:=wait_phase v') in H4; auto.
  Qed.

  Let sp_complete_reg_3:
    forall vs wp ph t v r x wp',
    WF_Phases wp ->
    SP_Complete ph wp ->
    Map_TID.MapsTo t v ph ->
    RegisterPre r x ph ->
    CanSignal (get_mode r) ->
    Copy vs wp x (get_task r) wp' ->
    CanSignal (mode v) ->
    GetPhase t (signal_phase v) wp'.
  Proof.
    intros.
    assert (SignalPhase t (signal_phase v) ph) by (apply signal_phase_def with (v:=v); auto).
    apply H0 in H6.
    destruct (TID.eq_dec t (get_task r)). {
      subst.
      inversion H2.
      contradiction H7.
      eauto using Map_TID_Extra.mapsto_to_in.
    }
    eapply copy_2; eauto.
  Qed.

  Let sp_complete_reg_1:
    forall vs wp x ph t n r wp',
    WF_Phases wp ->
    SP_Complete ph wp ->
    SignalPhase t n (register r x ph) ->
    RegisterPre r x ph ->
    CanSignal (get_mode r) ->
    Copy vs wp x (get_task r) wp' ->
    GetPhase t n wp'.
  Proof.
    intros.
    destruct H1; subst.
    apply register_inv_mapsto in H1.
    destruct H1 as [?|(?, (v', (?,?)))]. {
      eapply sp_complete_reg_3; eauto.
    }
    subst.
    rewrite mode_set_mode_rw in *.
    rewrite set_mode_preserves_signal_phase.
    assert (Hw: SignalPhase x (signal_phase v') ph). {
      apply signal_phase_def with (v:=v'); auto.
      inversion H2.
      assert (v'=v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      apply can_signal_le with (y:=get_mode r); auto.
    }
    apply H0 in Hw.
    apply copy_1 with (n:=signal_phase v') in H4; auto.
  Qed.

  Let sp_complete_reg_2:
    forall wp n ph x y r,
    WF_Phases wp ->
    SP_Complete ph wp ->
    SignalPhase x n (register r y ph) ->
    ~ CanSignal (get_mode r) ->
    GetPhase x n wp.
  Proof.
    intros.
      destruct H1; subst.
      apply register_inv_mapsto in H1.
      destruct H1 as [?|(?, (v', (?,?)))]. {
        assert (SignalPhase x (signal_phase v) ph) by (apply signal_phase_def with (v:=v); auto).
        auto.
      }
      subst.
      rewrite mode_set_mode_rw in *.
      rewrite set_mode_preserves_signal_phase.
      contradiction.
  Qed.

  Let wp_complete:
    forall vs wp ph e ph' wp',
    WF_Phases wp ->
    WP_Complete ph wp ->
    Phaser.Reduces ph e ph' ->
    UpdateWP vs wp e wp' ->
    WP_Complete ph' wp'.
  Proof.
    intros; unfold WP_Complete; intros.
    rename x into t.
    destruct e as (x,[]); inversion H1; simpl in *; subst;
    inversion H2; subst; clear H2 H1.
    - apply wait_phase_inv_signal in H3; auto.
    - apply wait_phase_inv_wait in H3.
      destruct H3 as [(?, (?, (?, ?)))|(?,?)]. {
        subst.
        eauto.
      }
      apply H0 in H2.
      eapply get_phases_inc_neq in H5; eauto.
    - apply wait_phase_drop_eq in H3.
      destruct H3.
      apply get_phase_drop_neq; auto.
      eapply try_inc_2 in H5; eauto.
    - eapply wp_complete_reg_1; eauto.
    - eapply wp_complete_reg_2; eauto.
  Qed.

  Let sp_complete:
    forall vs sp ph e ph' sp',
    WF_Phases vs sp ->
    WF_Phases (update_nodes vs e) sp ->
    SP_Complete ph sp ->
    Phaser.Reduces ph e ph' ->
    UpdateSP (update_nodes vs e) sp e sp' ->
    SP_Complete ph' sp'.
  Proof.
    intros; unfold SP_Complete; intros.
    destruct e as (y,[]); inversion H2; simpl in *; subst;
    inversion H3; subst; clear H2 H3.
    - apply signal_phase_inv_signal in H4.
      destruct H4 as [(?, (?, (?, ?)))|(?,?)]. {
        subst.
        eauto.
      }
      apply H1 in H3.
      apply get_phases_inc_neq with (y:=y) (ps':=sp') (vs:=y::vs) in H3; auto.
    - apply signal_phase_inv_wait in H4; auto.
    - apply signal_phase_drop_eq in H4.
      destruct H4.
      eapply try_inc_2 in H6; eauto.
    - eapply sp_complete_reg_1; eauto.
    - eapply sp_complete_reg_2; eauto.
  Qed.

  Let wf_phases_signal:
    forall vs sp t x n sp',
    WF_Phases vs sp ->
    Map_TID.MapsTo t n (fst sp') ->
    Inc vs sp x sp' ->
    In n sp'.
  Proof.
    intros.
    assert (Hx := H1);
    apply inc_inv in H1.
    destruct H1 as (w, (Hg1, Hg2)).
    inversion Hx; subst; clear Hx.
    inversion H2; subst; clear H2.
    simpl_node.
    simpl in *.
    assert (ph = w) by eauto using get_phase_fun; subst.
    rewrite Map_TID_Facts.add_mapsto_iff in *.
    destruct H0 as [(mt,?)|(Hneq,mt)]. {
      subst.
      rewrite MN_Facts.add_in_iff.
      intuition.
    }
    rewrite MN_Facts.add_in_iff.
    apply H in mt.
    intuition.
  Qed.

  Let wf_phases_wait:
    forall vs sp t x n sp',
    WF_Phases vs sp ->
    Map_TID.MapsTo t n (fst sp') ->
    Inc (x::vs) sp x sp' ->
    In n sp'.
  Proof.
    intros.
    assert (Hx := H1);
    apply inc_inv in H1.
    destruct H1 as (w, (Hg1, Hg2)).
    inversion Hx; subst; clear Hx.
    inversion H2; subst; clear H2.
    simpl_node.
    simpl in *.
    assert (ph = w) by eauto using get_phase_fun; subst.
    rewrite Map_TID_Facts.add_mapsto_iff in *.
    destruct H0 as [(mt,?)|(Hneq,mt)]. {
      subst.
      rewrite MN_Facts.add_in_iff.
      intuition.
    }
    rewrite MN_Facts.add_in_iff.
    apply H in mt.
    intuition.
  Qed.

  Let wf_phases_drop:
    forall vs wp t n x ws' vs',
    WF_Phases vs wp ->
    Map_TID.MapsTo t n (fst (drop x ws')) ->
    TryInc vs' wp x ws' ->
    In n (drop x ws').
  Proof.
    unfold drop; intros.
    simpl.
    destruct ws' as (ns, ps).
    inversion H1; subst; clear H1. {
      simpl in *.
      assert (t <> x). {
        unfold not; intros; subst.
        apply Map_TID_Extra.mapsto_to_in in H0.
        rewrite Map_TID_Facts.remove_in_iff in *.
        destruct H0 as (N,_).
        intuition.
      }
      apply Map_TID.remove_3 in H0.
      inversion H2; subst; clear H2.
      inversion H4; subst; clear H4.
      apply Map_TID.add_3 in H0; auto.
      rewrite MN_Facts.add_in_iff.
      apply H in H0.
      intuition.
    }
    simpl in *.
    apply Map_TID.remove_3 in H0.
    apply H in H0.
    assumption.
  Qed.

  Let wf_phases_reg:
    forall vs wp t n wp' r x ph,
    WF_Phases vs wp ->
    Map_TID.MapsTo t n (fst wp') ->
    Copy wp x (get_task r) wp' ->
    RegisterPre r x ph ->
    In n wp'.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    simpl in *.
    rewrite Map_TID_Facts.add_mapsto_iff in *.
    destruct H0 as [(?,?)|(?,mt)]. {
      subst.
      apply H in H3.
      assumption.
    }
    apply H in mt.
    assumption.
  Qed.


  Let wf_phases_wp:
    forall vs wp ph e ph' wp',
    WF_Phases vs wp ->
    Phaser.Reduces ph e ph' ->
    UpdateWP (update_nodes vs e) wp e wp' ->
    WF_Phases (update_nodes vs e) wp'.
  Proof.
    intros; unfold WFPhases, NodesDefined; intros.
    rename x into t.
    destruct e as (?,[]); inversion H0; simpl in *; subst;
    inversion H1; subst; clear H0 H1; eauto using task_of_cons.
  Qed.

  Let wf_phases_sp:
    forall vs sp ph e ph' sp',
    WF_Phases vs sp ->
    Phaser.Reduces ph e ph' ->
    UpdateSP vs sp e sp' ->
    WF_Phases (update_nodes vs e) sp'.
  Proof.
    intros; unfold WFPhases, NodesDefined; intros.
    rename x into t.
    destruct e as (?,[]); inversion H0; simpl in *; subst;
    inversion H1; subst; clear H0 H1; eauto.
  Qed.

  Inductive Sound ph b : Prop :=
  | sound_def:
    WF_Phases (get_nodes b) (get_sp b) ->
    WF_Phases (get_nodes b) (get_wp b) ->
    SP_Sound ph (get_sp b) ->
    WP_Sound ph (get_wp b) ->
    Sound ph b.

  Let wp_phases_up:
    forall vs ps e,
    WF_Phases vs ps ->
    WF_Phases (update_nodes vs e) ps.
  Proof.
    unfold WFPhases, NodesDefined; intros.
    destruct e as (y, []); simpl; 
    apply H in H0; assumption.
  Qed.

  Let soundness:
    forall b ph e ph' b',
    Sound ph b ->
    Phaser.Reduces ph e ph' ->
    UpdateBuilder b e b' ->
    Sound ph' b'.
  Proof.
    intros.
    inversion H;  subst; clear H.
    inversion H1; subst; clear H1.
    assert (Hsp := H2).
    assert (Hwp := H3).
    eapply wf_phases_wp in H3; simpl; eauto.
    apply sound_def; simpl; auto.
    - eapply wf_phases_sp in H; eauto.
    - remember (update_nodes _ _) as vs.
      apply sp_sound with (vs:=get_nodes b) (vs':=vs) (sp:=get_sp b) (ph:=ph) (e:=e);
      auto.
    - remember (update_nodes _ _) as vs.
      apply wp_sound with (vs:=vs) (wp:=get_wp b) (ph:=ph) (e:=e); auto.
  Qed.

  Inductive Complete ph b : Prop :=
  | complete_def:
    WF_Phases (get_nodes b) (get_sp b) ->
    WF_Phases (get_nodes b) (get_wp b) ->
    SP_Complete ph (get_sp b) ->
    WP_Complete ph (get_wp b) ->
    Complete ph b.

  Let completeness:
    forall b ph e ph' b',
    Complete ph b ->
    Phaser.Reduces ph e ph' ->
    UpdateBuilder b e b' ->
    Complete ph' b'.
  Proof.
    intros.
    inversion H; clear H.
    inversion H1; subst; clear H1.
    assert (Hsp := H2).
    assert (Hwp := H3).
    eapply wf_phases_wp in H3; simpl; eauto.
    apply complete_def; simpl; auto.
    - eapply wf_phases_sp in H; eauto.
    - apply sp_complete with (vs:=get_nodes b) (sp:=get_sp b) (ph:=ph) (e:=e); auto.
    - apply wp_complete with (vs:=vs') (wp:=get_wp b) (ph:=ph) (e:=e); subst; auto.
  Qed.

  Let NodesSpec b := forall n, MN.In n (node_to_op b) -> Node n (get_nodes b).

  Structure WF ph b := wf_def {
    wf_sound: Sound ph b;
    wf_complete: Complete ph b;
    wf_nodes: NodesSpec b
  }.

  Let wf_nodes_2:
    forall n b e m,
    NodesSpec b ->
    UpdateOps (get_nodes b) (node_to_op b) e m ->
    MN.In n m ->
    Node n (update_nodes (get_nodes b) e).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    simpl.
    destruct (is_par o). {
      rewrite MN_Facts.add_in_iff in *.
      destruct H1. {
        subst.
        eauto using maps_to_to_node, node_cons.
      }
      auto using node_cons.
    }
    rewrite MN_Facts.add_in_iff in *.
    destruct H1. {
      subst.
      eauto using maps_to_to_node, node_cons.
    }
    auto using node_cons.
  Qed.

  Let nodes_spec_preserves:
    forall b b' e,
    NodesSpec b ->
    UpdateBuilder b e b' ->
    NodesSpec b'.
  Proof.
    intros.
    unfold NodesSpec.
    intros.
    inversion H0; subst; clear H0; simpl in *.
    replace vs' with (update_nodes (get_nodes b) e) in *; trivial; clear vs'.
    eapply wf_nodes_2; eauto.
  Qed.

  Theorem correctness:
    forall b ph e ph' b',
    WF ph b ->
    Phaser.Reduces ph e ph' ->
    UpdateBuilder b e b' ->
    WF ph' b'.
  Proof.
    intros.
    destruct H.
    eapply wf_def; eauto.
  Qed.

  Let wf_sp_1:
    forall ph b x v,
    WF ph b ->
    SignalPhase x (signal_phase v) ph ->
    GetPhase x (signal_phase v) (get_sp b).
  Proof.
    intros.
    apply wf_complete in H.
    apply H.
    assumption.
  Qed.

  Let wf_sp_2:
    forall ph b x v,
    WF ph b ->
    GetPhase x (signal_phase v) (get_sp b) ->
    SignalPhase x (signal_phase v) ph.
  Proof.
    intros.
    apply wf_sound in H.
    apply H.
    assumption.
  Qed.

  Let wf_wp_1:
    forall ph b x v,
    WF ph b ->
    WaitPhase x (wait_phase v) ph ->
    GetPhase x (wait_phase v) (get_wp b).
  Proof.
    intros.
    apply wf_complete in H.
    apply H.
    assumption.
  Qed.

  Let wf_wp_2:
    forall ph b x v,
    WF ph b ->
    GetPhase x (wait_phase v) (get_wp b) ->
    WaitPhase x (wait_phase v) ph.
  Proof.
    intros.
    apply wf_sound in H.
    apply H.
    assumption.
  Qed.

  Let wf_get_sp:
    forall ph x b v,
    WF ph b ->
    Map_TID.MapsTo x v ph ->
    CanSignal (mode v) ->
    GetPhase x (signal_phase v) (get_sp b).
  Proof.
    intros.
    assert (Hsp: SignalPhase x (signal_phase v) ph) by
    (apply signal_phase_def with (v:=v); auto).
    eauto.
  Qed.

  Let wf_get_wp:
    forall ph x b v,
    WF ph b ->
    Map_TID.MapsTo x v ph ->
    CanWait (mode v) ->
    GetPhase x (wait_phase v) (get_wp b).
  Proof.
    intros.
    assert (Hsp: WaitPhase x (wait_phase v) ph) by
    (apply wait_phase_def with (v:=v); auto).
    eauto.
  Qed.

  Let get_phase_to_set_phase:
    forall x n n' ph ws vs,
    GetPhase x n ws ->
    MapsTo x n' vs ->
    ~ In n' ws ->
    exists ws', SetPhase vs ws x ph ws'.
  Proof.
    intros.
    destruct ws as (ns, ps).
    simpl in *.
    inversion H; subst; clear H.
    simpl_node.
    eauto using set_phase_def.
  Qed.

    
(*
  Let wf_ph_red_signal:
    forall ph b x ph',
    WF ph b ->
    Phaser.Reduces ph x Phaser.SIGNAL ph' ->
    exists sp, Inc (get_nodes b) (get_sp b) x sp.
  Proof.
    intros.
    inversion H0; simpl in *; subst; clear H0; inversion H1.
    apply signal_pre_to_can_signal in H2.
    assert (GetPhase x (signal_phase v) (get_sp b)). {
      apply wf_get_sp with (ph:=ph); auto.
    }
    eapply wf_sp_2 in H3; eauto.
    eauto using inc_def.
  Qed.
  
  Let update_sp_total:
    forall b x o ph ph',
    WF ph b ->
    Phaser.Reduces ph x o ph' ->
    exists sp, UpdateSP (get_nodes b) (update_nodes (get_nodes b) (x, of_op o)) (get_sp b) (x, of_op o) sp.
  Proof.
    intros.
    destruct o; eauto using update_sp_continue, update_sp_wait, update_sp_async.
    - (update_sp_signal (get_nodes b) (update_nodes (get_nodes b) (x, of_op Phaser.SIGNAL)) (get_sp b)
    - destruct (can_signal r). {
        
      }
  Qed.

  Let reduces_to_build:
    forall b ph x o ph',
    WF ph b ->
    Phaser.Reduces ph x o ph' ->
    exists b', UpdateBuilder b (x, of_op o) b'.
  Proof.
    intros.
    destruct o; inversion H0; simpl in *; subst; clear H0.
    - 
  Qed.
*)
  
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

*)



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

  Inductive Build: list event -> builder * computation_graph -> Prop :=
  | build_nil:
    Build nil (builder_empty, cg_empty)
  | build_cons_nil:
    forall x o cgb,
    Add (builder_make x, cg_empty) (x,o) cgb -> 
    Build ((x,o)::nil) cgb
  | build_cons:
    forall e l cgb cgb',
    Build l cgb ->
    Add cgb e cgb' -> 
    Build (e::l) cgb'.
*)
  Fixpoint build l : option (builder * computation_graph):=
  match l with
  | nil => Some (builder_empty, cg_empty)
  | (x,o) :: nil => add (x,o) (builder_make x, cg_empty)
  | e :: l =>
    match build l with
    | Some cgb => add e cgb
    | _ => None
    end
  end.
(*
  Let copy_some:
    forall x y sp sp',
    copy x y sp = Some sp' ->
    Copy sp x y sp'.
  Proof.
    unfold copy; intros.
    destruct sp as (ns, ps).
    destruct (Map_TID_Extra.find_rw x ns) as [(R,?)|(?,(R,?))];
    rewrite R in *; clear R. {
      inversion H.
    }
    inversion H; subst.
    auto using copy_def.
  Qed.

  Let inc_some:
    forall vs sp x sp',
    inc vs sp x = Some sp' ->
    Inc vs sp x sp'.
  Proof.
    unfold inc; intros.
    remember (get_phase x sp).
    symmetry in Heqo.
    destruct o. {
      apply get_phase_some in Heqo.
      apply set_phase_some in H.
      eauto using inc_def.
    }
    inversion H.
  Qed.

  Let try_inc_some:
    forall vs sp x sp',
    try_inc vs sp x = Some sp' ->
    TryInc vs sp x sp'.
  Proof.
    unfold try_inc; intros.
    destruct (is_registered x sp). {
      auto using try_inc_ok.
    }
    inversion H; subst.
    eauto using try_inc_skip.
  Qed.

  Let update_sp_some:
    forall vs e sp sp',
    update_sp vs e sp = Some sp' ->
    UpdateSP vs sp e sp'.
  Proof.
    unfold update_sp;intros.
    destruct e as (x, o).
    destruct o; inversion H; subst; auto using update_sp_wait, update_sp_signal.
    - inversion H.
      subst.
      remember (try_inc _ _ _).
      symmetry in Heqo.
      destruct o. {
        apply try_inc_some in Heqo.
        inversion H; subst.
        auto using update_sp_drop.
      }
      inversion H.
    - destruct (can_signal (get_mode r)). {
        auto using update_sp_register_ok.
      }
      inversion H; subst; auto using update_sp_register_skip.
  Qed.

  Let update_wp_some:
    forall vs e wp wp',
    update_wp vs e wp = Some wp' ->
    UpdateWP vs wp e wp'.
  Proof.
    unfold update_wp; intros.
    destruct e as (x, o).
    destruct o; inversion H; subst; auto using update_wp_wait, update_wp_signal.
    - inversion H.
      subst.
      remember (try_inc _ _ _).
      symmetry in Heqo.
      destruct o. {
        apply try_inc_some in Heqo.
        inversion H; subst.
        auto using update_wp_drop.
      }
      inversion H.
    - destruct (can_wait (get_mode r)). {
        auto using update_wp_register_ok.
      }
      inversion H; subst; auto using update_wp_register_skip.
  Qed.

  Let update_ops_some:
    forall vs e m m',
    update_ops vs e m = Some m' ->
    UpdateOps vs m e m'.
  Proof.
    unfold update_ops; intros.
    destruct e as (x, o).
    remember (lookup _ _ _).
    symmetry in Heqo0.
    destruct o0. {
      inversion H; subst.
      apply lookup_some in Heqo0.
      auto using update_ops_def.
    }
    inversion H.
  Qed.

  Let update_builder_some:
    forall b e b',
    update_builder e b = Some b' ->
    UpdateBuilder b e b'.
  Proof.
    unfold update_builder; intros.
    remember (update_sp _ _ _).
    symmetry in Heqo.
    destruct o. {
      apply update_sp_some in Heqo.
      remember (update_wp _ _ _).
      symmetry in Heqo0.
      destruct o. {
        remember (update_ops _ _ _).
        symmetry in Heqo1.
        destruct o. {
          apply update_wp_some in Heqo0.
          apply update_ops_some in Heqo1.
          inversion H; subst.
          apply update_builder_def; auto.
        }
        inversion H.
      }
      inversion H.
    }
    inversion H.
  Qed.

  Let add_c_edges_some:
    forall vs vs' e es,
    add_c_edges vs vs' e = Some es ->
    AddCEdges vs vs' e es.
  Proof.
    unfold add_c_edges; intros.
    destruct e as (x, y).
    remember (lookup _ _ vs).
    symmetry in Heqo.
    destruct o. {
      apply lookup_some in Heqo.
      remember (lookup _ _ _).
      symmetry in Heqo0.
      destruct o. {
        apply lookup_some in Heqo0.
        inversion H; subst.
        auto using add_c_edges_def.
      }
      inversion H.
    }
    inversion H.
  Qed.

  Let add_f_edges_some:
    forall vs vs' e es,
    add_f_edges vs vs' e = Some es ->
    AddFEdges vs vs' e es.
  Proof.
    unfold add_f_edges; intros.
    destruct e as (x, y).
    remember (is_par y).
    symmetry in Heqo.
    destruct o. {
      apply is_par_some in Heqo.
      remember (lookup _ _ vs).
      symmetry in Heqo0.
      destruct o. {
        apply lookup_some in Heqo0.
        remember (lookup _ _ _).
        symmetry in Heqo1.
        destruct o. {
          apply lookup_some in Heqo1.
          inversion H; subst.
          eauto using add_f_edges_is_pair.
        }
        inversion H.
      }
      inversion H.
    }
    inversion H.
    auto using add_f_edges_is_seq.
  Qed.
(*
  Let add_s_edges_some:
    forall b vs e es,
    add_s_edges b vs e = Some es ->
    AddSEdges b vs e es.
  Proof.
    unfold add_s_edges; intros.
    destruct e as (x, y).
    assert (Hx: y = WAIT \/ y <> WAIT). {
      destruct y; auto;
      right;
      unfold not; intros N;
      inversion N.
    }
    destruct Hx. {
      subst.
      remember (get_phase _ _).
      symmetry in Heqo.
      destruct o. {
        apply get_phase_some in Heqo.
        remember (lookup _ _ _).
        symmetry in Heqo0.
        destruct o. {
          apply lookup_some in Heqo0.
          inversion H.
          apply add_s_edges_eq with (ph:=n)(n:=n0); auto.
          split; intros.
          + apply phase_2 in H0.
            destruct H0.
            auto.
          + destruct H0; subst.
            auto.
        }
        inversion H.
      }
      inversion H.
    }
    destruct y; inversion H; subst; clear H; auto using add_s_edges_neq.
    intuition.
  Qed.

  Let add_edges_some:
    forall b b' e cg cg',
    add_edges b b' e cg = Some cg' ->
    AddEdges b b' cg e cg'.
  Proof.
    unfold add_edges; intros.
    remember (add_c_edges _ _ _).
    symmetry in Heqo.
    destruct o. {
      apply add_c_edges_some in Heqo.
      remember (add_f_edges _ _ _).
      symmetry in Heqo0.
      destruct o. {
        apply add_f_edges_some in Heqo0.
        remember (add_s_edges _ _ _).
        symmetry in Heqo1.
        destruct o. {
          inversion H.
          apply add_s_edges_some in Heqo1.
          auto using add_edges_def.
        }
        inversion H.
      }
      inversion H.
    }
    inversion H.
  Qed.

  Let add_some:
    forall e bcg bcg',
    add e bcg = Some bcg' ->
    Add bcg e bcg'.
  Proof.
    unfold add; intros.
    destruct bcg as (b, cg).
    remember (update_builder e b).
    symmetry in Heqo.
    destruct o. {
      apply update_builder_some in Heqo.
      remember (add_edges  _ _ _ _).
      symmetry in Heqo0.
      destruct o. {
        apply add_edges_some in Heqo0.
        inversion H.
        auto using add_def.
      }
      inversion H.
    }
    inversion H.
  Qed.

  Let build_some:
    forall l b cg,
    build l = Some (b, cg) ->
    Build l (b, cg).
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
    remember (build (p::l)) as b'.
    symmetry in Heqb'.
    destruct b' as [(a,b')|]; unfold build in H, Heqb'; rewrite Heqb' in *. {
      eauto using add_some, build_cons.
    }
    inversion H.
  Qed.
*)
  Notation HB cg := (Reaches (FGraph.Edge (cg_edges cg))).

  Let phase_inv_ph_make:
    forall n ph x,
    Phase n ph (ph_make x) ->
    ph = 0.
  Proof.
    intros.
    simpl in *.
    rewrite MN_Facts.add_mapsto_iff in *.
    destruct H as [(?,?)|(_,N)]; subst; auto.
    rewrite MN_Facts.empty_mapsto_iff in *.
    contradiction.
  Qed.
(*
  Let add_s_edges_inv:
    forall b vs x o es n1 n2,
    AddSEdges b vs (x, o) es ->
    List.In (n1, n2) es ->
    exists ph, o = WAIT /\
    GetPhase x ph (get_wp b)
    /\ MapsTo x n2 vs /\ Phase n1 (S ph) (get_sp b).
  Proof.
    intros.
    inversion H; subst; clear H. {
      apply H6 in H0.
      destruct H0; subst.
      eauto.
    }
    inversion H0.
  Qed.
*)
*)

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

Extraction "ocaml/cg.ml" build Phaser.eval_trace.
(*
Section Props.
  Notation Phase n ph sp := (MN.MapsTo n ph (snd sp)).
  Notation In n sp := (MN.In n (snd sp)).

  Let PhaseDef (vs:list tid) (sp:phases) :=
    forall n, In n sp -> Node n vs.

  Inductive WellFormed b : Prop :=
  | well_formed_def:
    PhaseDef (get_nodes b) (get_sp b) ->
    PhaseDef (get_nodes b) (get_wp b) ->
    WellFormed b.

  Let SEdgeSpec cgb :=
    forall n1 n2, List.In (n1, n2) (s_edges (snd cgb)) <->
    exists ph, Phase n1 ph (get_sp (fst cgb)) /\ Phase n2 ph (get_wp (fst cgb)).

  Let add_f_edges_inv_wait:
    forall vs vs' x es,
    AddFEdges vs vs' (x, WAIT) es ->
    es = nil.
  Proof.
    intros.
    inversion H. {
      subst.
      inversion H5.
    }
    subst.
    inversion H.
    subst.
    trivial.
  Qed.

  Let add_f_edges_inv_signal:
    forall vs vs' x es,
    AddFEdges vs vs' (x, SIGNAL) es ->
    es = nil.
  Proof.
    intros.
    inversion H. {
      subst.
      inversion H5.
    }
    subst.
    inversion H.
    subst.
    trivial.
  Qed.

  Let add_s_edges_inv_wait:
    forall b vs x es,
    AddSEdges b vs (x, WAIT) es ->
    exists ph n, (GetPhase x ph (get_wp b) /\
    MapsTo x n vs  /\ (forall n' n'',
     List.In (n', n'') es <-> n'' = n /\ Phase n' (S ph) (get_sp b))).
  Proof.
    intros.
    inversion H. {
      eauto.
    }
    intuition.
  Qed.

  Let add_s_edges_inv_signal:
    forall b vs x es,
    AddSEdges b vs (x, SIGNAL) es ->
    es = nil.
  Proof.
    intros.
    inversion H; subst; clear H.
    trivial.
  Qed.

  Ltac simpl_add :=
  repeat match goal with
  | [ H1: GetPhase ?x ?ph1 ?sp, H2: GetPhase ?x ?ph2 ?sp2 |- _] =>
    let H := fresh "H" in
    assert (H: ph1 = ph2) by eauto using get_phase_fun;
    rewrite H in *;
    clear H H2
  | [ H : Add _ (_, WAIT) _ |- _ ] =>
     inversion H; subst; simpl in *; clear H
  | [ H : Add _ (_, SIGNAL) _ |- _ ] =>
     inversion H; subst; simpl in *; clear H
  | [ H : Add _ (_, DROP) _ |- _ ] =>
     inversion H; subst; simpl in *; clear H
  | [ H : Add _ (_, REGISTER _) _ |- _ ] =>
     inversion H; subst; simpl in *; clear H
  | [ H: UpdateBuilder _ (_, _) _ |- _ ] =>
     inversion H; subst; simpl in *; clear H
  | [ H: UpdateSP _ _ (_, _) _ |- _] =>
     inversion H; subst; simpl in *; clear H
  | [ H: UpdateWP _ _ (_, _) _ |- _] =>
     inversion H; subst; simpl in *; clear H
  | [ H: UpdateOps _ _ (_, _) _ |- _] =>
     inversion H; subst; simpl in *; clear H
  | [ H: AddEdges _ _ _ (_, _) _ |- _] =>
     inversion H; subst; simpl in *; clear H
  | [ H: AddCEdges _ _ (_, _) _ |- _] =>
     inversion H; subst; simpl in *; clear H
  | [ H: AddFEdges _ _ (_,WAIT) _ |- _] =>
     apply add_f_edges_inv_wait in H; try rewrite H in *; clear H
  | [ H: AddFEdges _ _ (_,SIGNAL) _ |- _] =>
     apply add_f_edges_inv_signal in H; try rewrite H in *; clear H
  | [ H: AddSEdges _ _ (_,WAIT) _ |- _] =>
     apply add_s_edges_inv_wait in H;
     destruct H as (?, (?, (?,(?,?))))
  | [ H: AddSEdges _ _ (_,SIGNAL) _ |- _] =>
     apply add_s_edges_inv_signal in H;
     try rewrite H in *; clear H
  | [ H: Inc _ _ _ _ |- _ ] =>
     inversion H; subst; simpl in *; clear H
  | [ H: SetPhase _ _ _ _ _ |- _ ] =>
     inversion H; subst; simpl in *; clear H
  end; simpl_node.

  Let add_preserves_phase:
    forall n cg ph b o b' x cg',
    Phase n ph (get_wp b) ->
    Add (b, cg) (x, o) (b', cg') ->
    Phase n ph (get_wp b').
  Proof.
    intros.
    destruct o; simpl_add; auto.
    - assert (n <> fresh (get_nodes b)). {
        unfold not; intros; subst.
        
      }
    - 
  Qed.
    

  Let s_edge_spec_reduces_signal:
    forall b cg x cgb',
    SEdgeSpec (b, cg) ->
    WellFormed b ->
    Add (b, cg) (x, SIGNAL) cgb' ->
    SEdgeSpec cgb'.
  Proof.
    intros.
    simpl_add.
    unfold SEdgeSpec.
    simpl.
    split; intros.
    - apply H in H2.
      destruct H2 as (ph', (Hp1, Hp2)).
      simpl in *.
      exists ph'.
      split; auto.
      rewrite <- H3 in *.
      simpl in *.
      apply MN.add_2; auto.
      unfold not; intros; subst.
      clear n.
      clear n'.
      rename n2 into n.
      rename n3 into n'.
      contradiction H5.
      eauto using MN_Extra.mapsto_to_in.
    - destruct H2 as (ph', (Hp1, Hp2)).
      rewrite MN_Facts.add_mapsto_iff in *.
      destruct Hp1 as [(?,?)|(?, mt)]. {
        subst.
        inversion H1; subst; clear H1.
        rewrite <- H2 in *.
        inversion H3; subst; clear H3.
      }
  Qed.

  Let s_edge_spec_reduces_wait:
    forall b cg x cgb',
    SEdgeSpec (b, cg) ->
    WellFormed b ->
    Add (b, cg) (x, WAIT) cgb' ->
    SEdgeSpec cgb'.
  Proof.
    intros.
    simpl_add.
    unfold SEdgeSpec.
    simpl in *.
    intros.
    rewrite in_app_iff.
    split; intros. {
      destruct H2. {
        apply H3 in H2.
        destruct H2.
        subst.
        eauto using MN.add_1.
      }
      apply H in H2.
      destruct H2 as (ph', (Hp1, Hp2)).
      simpl in *.
      exists ph'.
      split; auto.
      rewrite <- H4 in *.
      apply MN.add_2; auto.
      unfold not; intros; subst.
      assert (Hi: In (fresh (get_nodes b)) (get_wp b)). {
        rewrite <- H4 in *.
        simpl in *.
        eauto using MN_Extra.mapsto_to_in.
      }
      inversion H0.
      apply H5 in Hi.
      simpl_node.
    }
    destruct H2 as (ph', (Hp1, Hp2)).
    rewrite MN_Facts.add_mapsto_iff in *.
    simpl_add.
    destruct Hp2 as [(?,?)|(?, mt)]. {
      subst.
      rewrite H3.
      auto.
    }
    right.
    apply H.
    exists ph'.
    split; auto.
    simpl.
    rewrite <- H4.
    trivial.
  Qed.

  Let s_edge_spec_reduces:
    forall cgb e cgb',
    SEdgeSpec cgb ->
    Add cgb e cgb' ->
    WellFormed (fst cgb) ->
    SEdgeSpec cgb'.
  Proof.
    intros.
    rename H1 into Hns.
    inversion H0; subst; clear H0.
    inversion H2; subst; clear H2.
    clear H0 H3.
    simpl in *.
    intros.
    inversion H4; subst; clear H4. {
      simpl in *.
      inversion H1; subst; clear H1.
      simpl_node.
      inversion H4; subst; clear H4.
      inversion H5; subst; clear H5.
      inversion H6; subst; clear H6.
      split; intros. {
        apply in_app_or in H1.
        destruct H1.
        - apply H3 in H1.
          destruct H1.
          subst.
          inversion H2; subst; clear H2.
          inversion H5; subst; clear H5.
          simpl_node.
          simpl.
          assert (ph0 = ph) by eauto using get_phase_fun; subst.
          eauto using MN.add_1.
        - apply H in H1.
          inversion H2; subst; clear H2.
          inversion H5; subst; clear H5.
          simpl_node.
          assert (ph0 = ph) by eauto using get_phase_fun; subst.
          destruct H1 as (ph', (Hp1, Hp2)).
          exists ph'.
          simpl.
          split; auto.
          simpl in *.
          rewrite <- H2 in *.
          apply MN.add_2; auto.
          unfold not; intros; subst.
          assert (Hi: In (fresh (get_nodes b)) (get_wp b)). {
            rewrite <- H2 in *.
            simpl in *.
            eauto using MN_Extra.mapsto_to_in.
          }
          inversion Hns.
          apply H5 in Hi.
          simpl_node.
        }
        destruct H1 as (ph', (Hp1, Hp2)).
        inversion H2; subst; clear H2.
        inversion H4; subst; clear H4.
        simpl_node.
        simpl in *.
        rewrite MN_Facts.add_mapsto_iff in *.
        assert (ph0 = ph) by
        eauto using get_phase_fun; subst.
        destruct Hp2 as [(?,?)|(?, mt)]. {
          subst.
          rewrite in_app_iff.
          left.
          rewrite H3.
          split; auto.
        }
        rewrite in_app_iff.
        right.
        apply H.
        exists ph'.
        split; auto.
        rewrite <- H2.
        trivial.
      }
      simpl.
      inversion H1; subst; clear H1.
      auto.
      simpl.
      clear H2.
      inversion H3; subst; clear H3.
      - inversion H7; subst; clear H7.
        inversion H4; subst; clear H4.
        inversion H2; subst; clear H2.
        simpl in *.
    }
  Qed.


  Lemma phase_matching:
    forall l b cg n1 n2 s w,
    Build l (b, cg) ->
    List.In (n1, n2) (s_edges cg) ->
    Phase n1 s (get_sp b) ->
    Phase n2 w (get_wp b) ->
    s = w.
  Proof.
    induction l; intros. {
      inversion H.
      subst.
      inversion H0.
    }
    inversion H; subst; clear H.
    - inversion H6; subst; clear H6.
      inversion H9; subst; clear H9.
      simpl in H0.
      rewrite app_nil_r in *.
      apply add_s_edges_inv with (b:=builder_make x) (vs:=get_nodes b) (x:=x) (o:=o) in H0; auto.
      destruct H0 as (ph, (?, (?, (?, ?)))).
      subst.
      simpl in *.
      apply phase_inv_ph_make in H8; auto.
      inversion H8.
    - inversion H7; subst; clear H7.
      inversion H9; subst; clear H9.
      simpl in *.
      apply in_app_or in H0.
      destruct H0. {
        destruct a as (x, o).
        apply add_s_edges_inv with
           (b:=b0) (vs:=get_nodes b) (x:=x) (o:=o) in H0; auto.
        destruct H0 as (ph, (?, (Hg, (Hmt, Hph)))).
        subst.
        rename b into b'; rename b0 into b.
        clear H H3 H5 H4.
        inversion H8; subst; clear H8.
        simpl in *.
        inversion H0; subst; clear H0.
        inversion H3; subst; clear H3;
        inversion H; subst; clear H.
        assert (s = S  ph) by eauto using MN_Facts.MapsTo_fun; subst; clear H1.
        inversion H5; subst; clear H5.
        inversion H0; subst; clear H0.
        simpl in *.
        rewrite MN_Facts.add_mapsto_iff in *.
        destruct H2 as [(?,?)|(?,mt)]. {
          subst.
          eauto.
        }
        assert (ph0 = ph) by eauto; subst.
        clear Hg.
        simpl_node.
        intuition.
      }
      eapply IHl in H0; eauto.
  Qed.
    

(*
  Lemma phase_ordering:
    forall l b cg n1 n2 s w,
    Build l (b, cg) ->
    MN.MapsTo n1 s (snd (get_sp b)) ->
    MN.MapsTo n2 w (snd (get_wp b)) ->
    s <= w ->
    HB cg n1 n2.
  Proof.
    intros.
  Qed.
    *)
*)