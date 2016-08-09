Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
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

  Definition ph_make (x:tid) :=
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
  | update_wp_register_can_wait:
    forall ws' x r,
    CanWait (get_mode r) ->
    Copy vs ws x (get_task r) ws' ->
    UpdateWP vs ws (x, REGISTER r) ws'
  | update_wp_phased_cannot_wait:
    forall x r,
    ~ CanWait (get_mode r) ->
    UpdateWP vs ws (x, REGISTER r) ws
  | update_wp_signal:
    forall x,
    UpdateWP vs ws (x, SIGNAL) ws
  | update_wp_wait:
    forall x ws',
    Inc vs ws x ws' ->
    UpdateWP vs ws (x, WAIT) ws'
  | update_wp_drop:
    forall x ws',
    TryInc vs ws x ws' ->
    UpdateWP vs ws (x, DROP) (drop x ws').

  Definition update_wp vs (e:event) (wp:phases) : option phases :=
  let (x, o) := e in
  match o with
  | REGISTER r =>
    if can_wait (get_mode r) then copy vs x (get_task r) wp
    else Some wp
  | WAIT => inc vs wp x
  | DROP =>
    match try_inc vs wp x with
    | Some wp' => Some (drop x wp')
    | _ => None
    end
  | _ => Some wp
  end.

  Inductive UpdateSP (vs vs':list tid) (ws:phases): event -> phases -> Prop :=
  | update_sp_register_can_signal:
    forall ws' x r,
    CanSignal (get_mode r) ->
    Copy vs' ws x (get_task r) ws' ->
    UpdateSP vs vs' ws (x, REGISTER r) ws'
  | update_sp_register_cannot_signal:
    forall x r,
    ~ CanSignal (get_mode r) ->
    UpdateSP vs vs' ws (x, REGISTER r) ws
  | update_sp_signal:
    forall x ws',
    Inc vs ws x ws' ->
    UpdateSP vs vs' ws (x, SIGNAL) ws'
  | update_sp_wait:
    forall x,
    UpdateSP vs vs' ws (x, WAIT) ws
  | update_sp_drop:
    forall x ws',
    TryInc vs ws x ws' ->
    UpdateSP vs vs' ws (x, DROP) (drop x ws').

  Definition update_sp vs vs' (e:event) sp :=
  let (x, o) := e in
  match o with
  | REGISTER r =>
    if can_signal (get_mode r) then copy vs' x (get_task r) sp
    else Some sp
  | SIGNAL => inc vs sp x
  | DROP =>
    match try_inc vs sp x with
    | Some sp' => Some (drop x sp')
    | _ => None
    end
  | _ => Some sp
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
    (forall n', List.In (n', n) es <-> Phase n' (S ph) (get_sp b)) ->
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
      Some (map (fun n' => (n', n)) (phase (S ph) (get_sp b)))
    | _, _ => None
    end
  | _ => Some nil
  end.

  Let phase_2:
    forall (a:node) b ph sp,
    In (b, a) (map (fun c => (c, a)) (phase ph sp)) ->
    Phase b ph sp.
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
    In (b, a) (map (fun c => (c, a)) (phase ph sp)).
  Proof.
    unfold phase; intros.
    rewrite in_map_iff.
    exists b; split; auto.
    unfold Phase in *.
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
    UpdateSP (get_nodes b) (update_nodes (get_nodes b) e) (get_sp b) e sp ->
    UpdateWP (update_nodes (get_nodes b) e) (get_wp b) e wp ->
    UpdateOps (get_nodes b) (node_to_op b) e m ->
    UpdateBuilder b e
    {| get_nodes := update_nodes (get_nodes b) e;
       get_sp := sp;
       get_wp := wp;
       node_to_op := m |}.

  Let update_builder (e:event) b :=
  let vs := update_nodes (get_nodes b) e in
  match update_sp (get_nodes b) vs e (get_sp b),
        update_wp vs e (get_wp b),
        update_ops (get_nodes b) e (node_to_op b) with
  | Some sp, Some wp, Some m =>
    Some {| get_nodes:=vs; get_sp:=sp; get_wp:=wp; node_to_op := m |}
  | _,_,_ => None
  end.

  Structure computation_graph := {
    c_edges : list edge;
    f_edges : list edge;
    s_edges : list edge
  }.

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

  Let SP_Sound (ph:Phaser.phaser) (sp:phases) : Prop :=
    forall x n,
    GetPhase x n sp ->
    SignalPhase x n ph.

  Let set_phase_to_get_phase:
    forall vs sp t ph sp',
    SetPhase vs sp t ph sp' ->
    GetPhase t ph sp'.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply get_phase_def with (n:=n); eauto using Map_TID.add_1, MN.add_1.
  Qed.

  Let get_phase_fun:
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

  Let inc_inv:
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
      eauto.
    }
    auto.
  Qed.

  Let NodesDefined (vs:list tid) (m:Map_TID.t node) : Prop :=
  forall x n, Map_TID.MapsTo x n m -> TaskOf n x vs. (* nodes are mapped to the correct owner *)

  Let WFPhases (vs:list tid) (ps:phases) := NodesDefined vs (fst ps).

  Let set_phase_3:
    forall x ps' ps y vs ph ph',
    WFPhases vs ps ->
    GetPhase x ph ps' ->
    y <> x ->
    SetPhase vs ps y ph' ps' ->
    GetPhase x ph ps.
  Proof.
    intros.
    inversion H2; subst; clear H2.
    inversion H0; subst; clear H0.
    apply Map_TID.add_3 in H7; auto.
    assert (n0 <> n). {
      unfold WFPhases in *; simpl in *.
      rewrite MN_Facts.add_mapsto_iff in *.
      destruct H8 as [(?,?)|(?,?)]. {
        subst.
        apply H in H7.
        apply maps_to_to_task_of in H3.
        simpl_node.
        contradiction H1; trivial.
      }
      auto.
    }
    apply MN.add_3 in H8; auto.
    eauto using get_phase_def.
  Qed.

  Let set_phase_2:
    forall x y n ps ph ps' vs,
    WFPhases vs ps ->
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
      apply H in H7.
      apply maps_to_to_task_of in H3.
      simpl_node.
      intuition.
  Qed.

  Let inc_2:
    forall x y n ps ps' vs,
    WFPhases vs ps ->
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
    WFPhases vs ps ->
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

  Let inc_3:
    forall vs t n sp' sp x,
    WFPhases vs sp ->
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
    WFPhases vs sp ->
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

  Let signal_neq:
    forall x y ph n,
    x <> y ->
    SignalPhase x n ph ->
    SignalPhase x n (Phaser.signal y ph).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eauto using signal_phase_def, signal_2.
  Qed.

  Let signal_neq_drop:
    forall x y ph n,
    x <> y ->
    SignalPhase x n ph ->
    SignalPhase x n (Phaser.drop y ph).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eauto using signal_phase_def, drop_2.
  Qed.

  Let signal_eq:
    forall vs sp sp' ph t n,
    WFPhases vs sp ->
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
    assert (n' = S n) by eauto; subst.
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

  Let signal_phase_wait:
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

  Let drop_inv:
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

  Let copy_3:
    forall x y z sp sp' vs n,
    WFPhases vs sp ->
    z <> y ->
    GetPhase z n sp' ->
    Copy vs sp x y sp' ->
    GetPhase z n sp.
  Proof.
    intros.
    inversion H2; subst; clear H2.
    eapply set_phase_3 in H4; eauto.
  Qed.

  Let copy_inv_eq:
    forall x y ps ps' vs n,
    GetPhase y n ps' ->
    Copy vs ps x y ps' ->
    GetPhase x n ps.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eapply set_phase_to_get_phase in H2; eauto.
    assert (ph = n) by eauto.
    subst.
    trivial.
  Qed.

  Let copy_2:
    forall x y z ps ps' vs n,
    WFPhases vs ps ->
    z <> y ->
    Copy vs ps x y ps' ->
    GetPhase z n ps ->
    GetPhase z n ps'.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    eapply set_phase_2 in H4; eauto.
  Qed.

  Let copy_1:
    forall vs wp wp' x y n,
    Copy vs wp x y wp' ->
    GetPhase x n wp ->
    GetPhase y n wp'.
  Proof.
    intros.
    inversion H; subst; clear H.
    assert (ph = n) by eauto; subst.
    eauto.
  Qed.

  Let sp_register:
    forall r x ph n,
    RegisterPre r x ph ->
    CanSignal (get_mode r) ->
    SignalPhase x n ph ->
    SignalPhase (get_task r) n (register r x ph).
  Proof.
    intros.
    inversion H1; subst.
    eauto using signal_phase_def, register_spec.
  Qed.

  Let sp_register_neq:
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

  Let sp_sound:
    forall vs vs' sp ph e ph' sp',
    WFPhases vs sp ->
    WFPhases vs' sp ->
    SP_Sound ph sp ->
    Phaser.Reduces ph e ph' ->
    UpdateSP vs vs' sp e sp' ->
    SP_Sound ph' sp'.
  Proof.
    unfold SP_Sound; intros.
    rename x into t.
    destruct e as (x, o).
    destruct o; inversion H2; simpl in *; subst;
    inversion H3; subst; clear H2 H3.
    - destruct (TID.eq_dec x t). {
        subst.
        apply signal_eq with (vs:=vs) (sp:=sp) (sp':=sp'); auto.
      }
      eapply inc_3 in H6; eauto.
    - destruct (TID.eq_dec x t); subst; eauto.
    - apply drop_inv with (y:=t) (n:=n) in H4; auto.
      destruct H4 as (Hx,Hy).
      eapply try_inc_3 in H6; eauto.
    - destruct (TID.eq_dec (get_task r) t). {
        subst.
        apply copy_inv_eq with (n:=n) in H10; auto.
      }
      eapply copy_3 in H10; eauto.
    - eauto.
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

  Let wp_signal:
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

  Let wp_wait_neq_drop:
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
    WFPhases vs wp ->
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
    - eauto.
    - destruct (TID.eq_dec t x). {
        subst.
        apply inc_inv in H5.
        rename n into xw.
        destruct H5 as (n, (Hg1, Hg2)).
        assert (xw = S n) by eauto; subst.
        eauto.
      }
      eapply inc_3 in H5; eauto.
    - apply drop_inv in H3; auto.
      destruct H3 as (?, Hg).
      eapply try_inc_3 in H5; eauto.
    - destruct (TID.eq_dec (get_task r) t). {
        subst.
        apply copy_inv_eq with (n:=n) in H9; auto.
      }
      eapply copy_3 in H9; eauto.
    - eauto.
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
    assert (ph = n) by eauto; subst.
    eauto.
  Qed.

  Let get_phases_set_phase_neq:
    forall x y n ps ps' n' vs,
    WFPhases vs ps ->
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
      contradiction H0.
      apply maps_to_to_task_of in H3.
      apply H in H7.
      eauto using task_of_fun_2.
  Qed.

  Let get_phases_inc_neq:
    forall x y n ps ps' vs,
    WFPhases vs ps ->
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
    forall x y n ps,
    y <> x ->
    GetPhase x n ps ->
    GetPhase x n (drop y ps).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    simpl.
    apply get_phase_def with (n:=n0); auto.
    eauto using Map_TID.remove_2.
  Qed.

  Let wp_complete_reg_2:
    forall vs wp n ph x y r,
    WFPhases vs wp ->
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
    WFPhases vs wp ->
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
    WFPhases vs wp ->
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
    WFPhases vs wp ->
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
    WFPhases vs wp ->
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
    forall vs wp n ph x y r,
    WFPhases vs wp ->
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
    WFPhases vs wp ->
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
    WFPhases vs sp ->
    WFPhases (update_nodes vs e) sp ->
    SP_Complete ph sp ->
    Phaser.Reduces ph e ph' ->
    UpdateSP vs (update_nodes vs e) sp e sp' ->
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
      apply get_phases_inc_neq with (y:=y) (ps':=sp') (vs:=vs) in H3; auto.
    - apply signal_phase_inv_wait in H4; auto.
    - apply signal_phase_drop_eq in H4.
      destruct H4.
      eapply try_inc_2 in H6; eauto.
    - eapply sp_complete_reg_1; eauto.
    - eapply sp_complete_reg_2; eauto.
  Qed.

  Let wf_phases_inc:
    forall vs wp t x n wp',
    WFPhases vs wp ->
    Map_TID.MapsTo t n (fst wp') ->
    Inc (x :: vs) wp x wp' ->
    TaskOf n t (x :: vs).
  Proof.
    intros.
    assert (Hx := H1);
    apply inc_inv in H1.
    destruct H1 as (w, (Hg1, Hg2)).
    inversion Hx; subst; clear Hx.
    inversion H2; subst; clear H2.
    simpl_node.
    simpl in *.
    assert (ph = w) by eauto; subst.
    rewrite Map_TID_Facts.add_mapsto_iff in *.
    destruct H0 as [(mt,?)|(Hneq,mt)]. {
      subst.
      auto using task_of_eq.
    }
    auto using task_of_cons.
  Qed.

  Let wf_phases_drop:
    forall vs wp t n x ws' vs',
    WFPhases vs wp ->
    Map_TID.MapsTo t n (fst (drop x ws')) ->
    TryInc vs' wp x ws' ->
    TaskOf n t (x :: vs).
  Proof.
    unfold drop; intros.
    inversion H1; subst; clear H1. {
      destruct ws' as (ns, ps).
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
      eauto using Map_TID.add_3, task_of_cons.
    }
    destruct ws'.
    simpl in *.
    eauto using task_of_cons, Map_TID.remove_3.
  Qed.

  Let wf_phases_reg:
    forall vs wp t n wp' r x,
    WFPhases vs wp ->
    Map_TID.MapsTo t n (fst wp') ->
    Copy (get_task r :: x :: vs) wp x (get_task r) wp' ->
    TaskOf n t (get_task r :: x :: vs).
  Proof.
    intros.
    inversion H1; subst; clear H1.
    inversion H3; subst; clear H3.
    simpl in *.
    rewrite Map_TID_Facts.add_mapsto_iff in *.
    destruct H0 as [(?,?)|(?,mt)]. {
      subst.
      simpl_node.
      auto using task_of_eq.
    }
    auto using task_of_cons.
  Qed.

  Let wf_phases_wp:
    forall vs wp ph e ph' wp',
    WFPhases vs wp ->
    Phaser.Reduces ph e ph' ->
    UpdateWP (update_nodes vs e) wp e wp' ->
    WFPhases (update_nodes vs e) wp'.
  Proof.
    intros; unfold WFPhases, NodesDefined; intros.
    rename x into t.
    destruct e as (?,[]); inversion H0; simpl in *; subst;
    inversion H1; subst; clear H0 H1; eauto using task_of_cons.
  Qed.

  Let wf_phases_sp:
    forall vs sp ph e ph' sp',
    WFPhases vs sp ->
    Phaser.Reduces ph e ph' ->
    UpdateSP vs (update_nodes vs e) sp e sp' ->
    WFPhases (update_nodes vs e) sp'.
  Proof.
    intros; unfold WFPhases, NodesDefined; intros.
    rename x into t.
    destruct e as (?,[]); inversion H0; simpl in *; subst;
    inversion H1; subst; clear H0 H1; eauto using task_of_cons.
    destruct H4.
    inversion H1; subst; clear H1.
    simpl in *.
    rewrite Map_TID_Facts.add_mapsto_iff in *.
    destruct H2 as [(?,?)|(?,mt)]. {
      subst.
      auto using maps_to_to_task_of, task_of_cons.
    }
    auto using task_of_cons.
  Qed.

  Inductive Sound ph b : Prop :=
  | sound_def:
    WFPhases (get_nodes b) (get_sp b) ->
    WFPhases (get_nodes b) (get_wp b) ->
    SP_Sound ph (get_sp b) ->
    WP_Sound ph (get_wp b) ->
    Sound ph b.

  Let wp_phases_up:
    forall vs ps e,
    WFPhases vs ps ->
    WFPhases (update_nodes vs e) ps.
  Proof.
    unfold WFPhases, NodesDefined; intros.
    destruct e as (y, []); simpl; auto using task_of_cons.
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
      subst; auto.
    - remember (update_nodes _ _) as vs.
      apply wp_sound with (vs:=vs) (wp:=get_wp b) (ph:=ph) (e:=e); subst; auto.
  Qed.

  Inductive Complete ph b : Prop :=
  | complete_def:
    WFPhases (get_nodes b) (get_sp b) ->
    WFPhases (get_nodes b) (get_wp b) ->
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
    - remember (update_nodes _ _) as vs.
      apply sp_complete with (vs:=get_nodes b) (sp:=get_sp b) (ph:=ph) (e:=e); subst; auto.
    - remember (update_nodes _ _) as vs.
      apply wp_complete with (vs:=vs) (wp:=get_wp b) (ph:=ph) (e:=e); subst; auto.
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
    eauto.
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
    eauto using wf_def.
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
    forall x n n' ws vs,
    GetPhase x n ws ->
    List.In x vs ->
    exists ws', SetPhase vs ws x n' ws'.
  Proof.
    intros.
    destruct ws as (ns, ps).
    apply in_to_maps_to in H0; auto using TID.eq_dec.
    destruct H0 as (n'', Hmt).
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

  Let copy_some:
    forall vs x y sp sp',
    copy vs x y sp = Some sp' ->
    Copy vs sp x y sp'.
  Proof.
    unfold copy; intros.
    remember (get_phase x sp).
    symmetry in Heqo.
    destruct o. {
      apply get_phase_some in Heqo.
      apply set_phase_some in H.
      eauto using copy_def.
    }
    inversion H.
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
    forall vs vs' e sp sp',
    update_sp vs vs' e sp = Some sp' ->
    UpdateSP vs vs' sp e sp'.
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
        auto using update_sp_register_can_signal.
      }
      inversion H; subst; auto using update_sp_register_cannot_signal.
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
        auto using update_wp_register_can_wait.
      }
      inversion H; subst; auto using update_wp_phased_cannot_wait.
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
    remember (update_sp _ _ _ _).
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
          split; eauto.
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
