Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
Require Import Aniceto.Pair.
Require Import Aniceto.List.

Require Import Phasers.Phaser.
Require Import Phasers.Taskview.
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
  | update_wp_phased_can_wait:
    forall ws' x y r,
    CanWait r ->
    Copy vs ws x y ws' ->
    UpdateWP vs ws (x, ASYNC_PHASED y r) ws'
  | update_wp_phased_cannot_wait:
    forall x y r,
    ~ CanWait r ->
    UpdateWP vs ws (x, ASYNC_PHASED y r) ws
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
    if can_wait r then copy vs x y wp
    else None
  | WAIT => inc vs wp x
  | DROP => Some (drop x wp)
  | _ => Some wp
  end.

  Inductive UpdateSP (vs:list tid) (ws:phases): event -> phases -> Prop :=
  | update_sp_async:
    forall x y,
    UpdateSP vs ws (x, ASYNC y) ws
  | update_sp_phased_can_signal:
    forall ws' x y r,
    CanSignal r ->
    Copy vs ws x y ws' ->
    UpdateSP vs ws (x, ASYNC_PHASED y r) ws'
  | update_sp_phased_cannot_signal:
    forall x y r,
    ~ CanSignal r ->
    UpdateSP vs ws (x, ASYNC_PHASED y r) ws
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
    if can_signal r then copy vs x y wp
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

  Definition builder_empty := {| get_nodes := nil; get_sp:= ph_empty; get_wp := ph_empty |}.

  Definition builder_make x := {| get_nodes := (x::nil); get_sp:= ph_make x; get_wp := ph_make x |}.

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

  Let of_op (o:Phaser.op) :=
  match o with
  | Phaser.SIGNAL => SIGNAL
  | Phaser.WAIT => WAIT
  | Phaser.DROP => DROP
  | Phaser.REGISTER r => ASYNC_PHASED (Phaser.get_task r) (Phaser.get_mode r)
  end.

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

  Let NodesDefined (vs:list tid) (m:Map_TID.t node) : Prop :=
  forall x n, Map_TID.MapsTo x n m -> TaskOf n x vs. (* nodes are mapped to the correct owner *)

  Let WFPhases (vs:list tid) (ps:phases) := NodesDefined vs (fst ps).

  Let set_phase_3:
    forall t sp' sp x vs ph ph',
    WFPhases vs sp ->
    GetPhase t ph sp' ->
    x <> t ->
    SetPhase vs sp x ph' sp' ->
    GetPhase t ph sp.
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
    forall sp x y n sp',
    Drop sp x sp' ->
    GetPhase y n sp' ->
    x <> y /\ GetPhase y n sp.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
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
    forall x y sp sp' vs n,
    GetPhase y n sp' ->
    Copy vs sp x y sp' ->
    GetPhase x n sp.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eapply set_phase_to_get_phase in H2; eauto.
    assert (ph = n) by eauto.
    subst.
    trivial.
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
    forall vs sp ph x o ph' sp',
    WFPhases vs sp ->
    SP_Sound ph sp ->
    Phaser.Reduces ph x o ph' ->
    UpdateSP vs sp (x, of_op o) sp' ->
    SP_Sound ph' sp'.
  Proof.
    unfold SP_Sound; intros.
    rename x0 into t.
    destruct o; inversion H1; simpl in *; subst;
    inversion H2; subst; clear H2 H1.
    - destruct (TID.eq_dec x t). {
        subst.
        eapply signal_eq; eauto.
      }
      eapply inc_3 in H6; eauto.
    - destruct (TID.eq_dec x t); subst; eauto.
    - apply drop_inv with (y:=t) (n:=n) in H6; auto.
      destruct H6 as (Hx,Hy).
      eauto.
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
      auto using signal_preserves_wait_phase, Phaser.signal_eq.
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
    eauto using wait_phase_def, Phaser.wait_eq.
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
    forall vs wp ph x o ph' wp',
    WFPhases vs wp ->
    WP_Sound ph wp ->
    Phaser.Reduces ph x o ph' ->
    UpdateWP vs wp (x, of_op o) wp' ->
    WP_Sound ph' wp'.
  Proof.
    intros; unfold WP_Sound; intros.
    rename x0 into t.
    destruct o; inversion H1; simpl in *; subst;
    inversion H2; subst; clear H2 H1.
    - eauto.
    - destruct (TID.eq_dec t x). {
        subst.
        apply inc_inv in H6.
        rename n into xw.
        destruct H6 as (n, (Hg1, Hg2)).
        assert (xw = S n) by eauto; subst.
        eauto.
      }
      eapply inc_3 in H6; eauto.
    - eapply drop_inv in H6; eauto.
      destruct H6 as (?, Hg).
      eauto.
    - destruct (TID.eq_dec (get_task r) t). {
        subst.
        apply copy_inv_eq with (n:=n) in H10; auto.
      }
      eapply copy_3 in H10; eauto.
    - eauto.
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
    forall vs wp t n wp' x,
    WFPhases vs wp ->
    Map_TID.MapsTo t n (fst wp') ->
    Drop wp x wp' ->
    TaskOf n t (x :: vs).
  Proof.
    intros.
    inversion H1; subst; clear H1.
    simpl in *.
    apply Map_TID.remove_3 in H0.
    auto using task_of_cons.
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
    forall vs wp ph x o ph' wp',
    WFPhases vs wp ->
    Phaser.Reduces ph x o ph' ->
    UpdateWP (update_nodes vs (x, of_op o)) wp (x, of_op o) wp' ->
    WFPhases (update_nodes vs (x, of_op o)) wp'.
  Proof.
    intros; unfold WFPhases, NodesDefined; intros.
    rename x0 into t.
    destruct o; inversion H0; simpl in *; subst;
    inversion H1; subst; clear H0 H1; eauto using task_of_cons.
  Qed.

  Let wf_phases_sp:
    forall vs sp ph x o ph' sp',
    WFPhases vs sp ->
    Phaser.Reduces ph x o ph' ->
    UpdateSP (update_nodes vs (x, of_op o)) sp (x, of_op o) sp' ->
    WFPhases (update_nodes vs (x, of_op o)) sp'.
  Proof.
    intros; unfold WFPhases, NodesDefined; intros.
    rename x0 into t.
    destruct o; inversion H0; simpl in *; subst;
    inversion H1; subst; clear H0 H1; eauto using task_of_cons.
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
    forall b ph x o ph' b',
    Sound ph b ->
    Phaser.Reduces ph x o ph' ->
    UpdateBuilder b (x, of_op o) b' ->
    Sound ph' b'.
  Proof.
    intros.
    inversion H;  subst; clear H.
    inversion H1; subst; clear H1.
    assert (Hsp := H2).
    assert (Hwp := H3).
    eapply wf_phases_sp in H2; simpl; eauto.
    eapply wf_phases_wp in H3; simpl; eauto.
    apply sound_def; simpl; auto.
    - remember (update_nodes _ _) as vs.
      apply sp_sound with (vs:=vs) (sp:=get_sp b) (ph:=ph) (x:=x) (o:=o); subst; auto.
    - remember (update_nodes _ _) as vs.
      apply wp_sound with (vs:=vs) (wp:=get_wp b) (ph:=ph) (x:=x) (o:=o); subst; auto.
  Qed.
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
(*
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

Extraction "ocaml/cg.ml" build.
