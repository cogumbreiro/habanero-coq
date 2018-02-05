(*
State: (task -> (finisih * finishes)) * (finish -> tasks)
t0, init f0
t0, begin_finish f1;
t0, begin_task t1;
t1, end_task f;
t0, begin_finish f2;
t0, begin_task t2;
t2, begin_task t3;
t2, end_task f2;
t3, end_task f2;
t0, end_finish f3;
t0, begin_finish f3
t0, begin_task t4
t4, end_task f3
t0, end_finish f3
*)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Tid.
Require Import Fid.
Require Import Aniceto.Graphs.DAG.
Require Import Aniceto.List.
Require Import Aniceto.Graphs.FGraph.

  (**
    An example:
    [[
                                                    // (p, INIT f1)
    int iters = 0; delta = epsilon+1;
    while ( delta > epsilon ) {
      finish {                                      // (p, BEGIN_FINISH f2)
        for ( jj = 1 ; jj <= n ; jj++ ) {
          final int j = jj;
          async {                                   // (p, BEGIN_TASK t_i)
            newA[j] = (oldA[j-1]+oldA[j+1])/2.0f ;
            diff[j] = Math.abs(newA[j]-oldA[j]);
          }                                         // (t_i, END_TASK)
        }
      }
      delta = diff.sum(); iters++;
      temp = newA; newA = oldA; oldA = temp;
    } // while
    System.out.println("Iterations: " + iters);
                                                   // (p, END_TASK)
    ]]
    
   *)

  (** When a task starts it is bound to a finish; when a finish has zero
      bound tasks it is ready to synchronize;
      each task maintains a stack of finish scopes it opened. *)

  Structure task := {
    bind: fid;
    open: list fid;
  }.

  (** Upon creation a task is initialized with its bound finish [f]. *)

  Definition make f := {| bind := f; open := nil |}.

  (** The state of the program keeps track of the finish state per task. *)

  Definition state := Map_TID.t task.

  (** The initial state of the program is empty. *)

  Definition empty : state := Map_TID.empty task.

  (** These are the existing operations. Action [init f]
  is invoked at the beginning of a program by the first task.
  To start a finish scope we have operation [BEGIN_FINISH].
  To end a finish scope we have operation [END_FINISH].
  A task may spawn another with operation [BEGIN_TASK].
  The last operation a task invokes is [END_TASK] to signal
  its termination. *)

  Inductive op :=
  | INIT: fid -> op
  | BEGIN_FINISH: fid -> op
  | END_FINISH: op
  | BEGIN_TASK: tid -> op
  | END_TASK: op.

  (** We call an action to the pair [tid] and [op]eration. *)

  Definition action := (tid * op) % type.

  (** The Inner-most Enclosing Finish (IEF) is defined as expected. *)

  Definition ief (ft:task) :=
  match ft with
  | {| bind := f; open := nil |} => f
  | {| bind := g; open := (f::l)%list |} =>  f
  end.

  Inductive IEF x f s: Prop :=
  | ief_nil:
    Map_TID.MapsTo x {| bind := f; open := nil |} s ->
    IEF x f s
  | ief_cons:
    forall g l,
    Map_TID.MapsTo x {| bind := g; open := f::l |} s ->
    IEF x f s.

  Definition get_ief x s :=
  match Map_TID.find x s with
  | Some ft => Some (ief ft)
  | None => None
  end.

  (** For simplictiy we define the bind operation on a state. *)

  Inductive Bind : tid -> fid -> state -> Prop :=
  | bind_def:
    forall t f l s,
    Map_TID.MapsTo t {| bind := f; open := l |} s ->
    Bind t f s.

  (** We also define the open operation on a state *)

  Inductive Open : tid -> fid -> state -> Prop :=
  | open_def:
    forall t f l s g,
    List.In f l ->
    Map_TID.MapsTo t {| bind := g; open := l |} s ->
    Open t f s.

  (** The current open operation is the top of the open stack. *)

  Inductive Current : tid -> fid -> state -> Prop :=
  | current_def:
    forall t f l s g,
    Map_TID.MapsTo t {| bind := g; open := (f::l) |} s ->
    Current t f s.

  (** We say that a finish-id is in a state if it is mentioned in a bind
  or a open relation. *)

  Inductive In (f:fid) s : Prop :=
  | in_bind:
    forall t,
    Bind t f s ->
    In f s
  | in_open:
    forall t,
    Open t f s ->
    In f s.

Module Task.
Section Defs.
  Inductive Bind: fid -> task -> Prop :=
  | bind_def:
    forall f l,
    Bind f {| bind := f; open := l |}.

  Definition bind_dec (f:fid) (ft:task) : { Bind f ft } + { ~ Bind f ft }.
  Proof.
    destruct ft as (g, l).
    destruct (FID.eq_dec f g). {
      subst; auto using bind_def.
    }
    right; unfold not; intros N.
    inversion N; subst.
    contradiction.
  Defined.

  Inductive Open: fid -> task -> Prop :=
  | open_def:
    forall f g l,
    List.In f l ->
    Open f {| bind := g; open := l |}.

  Definition open_dec f ft : { Open f ft } + { ~ Open f ft }.
  Proof.
    destruct ft as (g, l).
    destruct (List.in_dec FID.eq_dec f l). {
      auto using open_def.
    }
    right; unfold not; intros N.
    inversion N; subst.
    contradiction.
  Defined.

  Inductive In: fid -> task -> Prop :=
  | in_bind:
    forall f ft,
    Bind f ft ->
    In f ft
  | in_open:
    forall f ft,
    Open f ft ->
    In f ft.

  Definition in_dec f ft : { In f ft } + { ~ In f ft }.
  Proof.
    destruct (bind_dec f ft); auto using in_bind.
    destruct (open_dec f ft); auto using in_open.
    right; unfold not; intros N.
    inversion N; subst; contradiction.
  Defined.
End Defs.
End Task.

  (** A finish is empty if there is no task that is bound to it. *)

  Inductive Empty f s : Prop :=
  | empty_def:
    (forall x, ~ Bind x f s) ->
    Empty f s.

  (** We are now ready to define the semantics of the async-finish API. *)

  Inductive Reduces : state -> action -> state -> Prop :=

  (** The first task [t] of an async-finish computation initializes a
  finish [f] (where [f] is not a member of state [s]). *)
  | reduces_init:
    forall s t f,
    ~ In f s ->
    ~ Map_TID.In t s ->
    Reduces s (t, INIT f) (Map_TID.add t (make f) s)

  (** An existing task [t] pushes a finish scope [f] in its stack [l] of
      open finishes; we must ensure that [f] is not mentioned in
      state [s]. *)
  | reduces_begin_finish:
    forall t f s l g,
    ~ In f s ->
    Map_TID.MapsTo t {| bind := g; open := l |} s ->
    Reduces s (t, BEGIN_FINISH f) (
      Map_TID.add t {| bind := g; open := f::l |} s)

  (** Synchronization happens when [f] is at the top of open tasks
    and [f] is empty; the side effect is that the task pops [f] from the stack
    of open finishes. *)
  | reduces_end_finish:
    forall s t f l g,
    Map_TID.MapsTo t {| bind := g; open := (f::l) % list |} s ->
    Empty f s ->
    Reduces s (t, END_FINISH) (Map_TID.add t {| bind := g; open := l |} s)

  (** A task [t] spawns a task [u]. The new task [u] is bound to the
      IEF of [t]. XXX: replace this by Prop *)
  | reduces_begin_task:
    forall s t u ft,
    ~ Map_TID.In u s ->
    Map_TID.MapsTo t ft s ->
    Reduces s (t, BEGIN_TASK u) (Map_TID.add u (make (ief ft)) s)

  (** A task [t] executes operation [END_TASK] at the end of its lifecycle;
      we ensure  that the task has zero finish scopes. *)
  | reduces_end_task:
    forall t f s ,
    Map_TID.MapsTo t {| bind := f; open := nil |} s ->
    Reduces s (t, END_TASK) (Map_TID.remove t s).

  Inductive Valid s : tid -> op -> Prop :=
  | valid_init:
    forall f t,
    ~ In f s ->
    ~ Map_TID.In t s ->
    Valid s t (INIT f)
  | valid_begin_finish:
    forall t f,
    Map_TID.In t s ->
    ~ In f s ->
    Valid s t (BEGIN_FINISH f)
  | valid_end_finish:
    forall t f g l,
    Map_TID.MapsTo t {| bind := g; open := (f::l) % list |} s ->
    Valid s t END_FINISH
  | valid_begin_task:
    forall t u,
    ~ Map_TID.In u s ->
    Map_TID.In t s ->
    Valid s t (BEGIN_TASK u)
  | typecheck_end_task:
    forall t f,
    Map_TID.MapsTo t {| bind := f; open := nil |} s ->
    Valid s t END_TASK.

  Definition op_fid (o:op) :=
  match o with
  | INIT f | BEGIN_FINISH f => Some f
  | _ => None
  end.

  Inductive ValidFid (s:state) x o f: Prop :=
  | valid_fid_some:
    op_fid o = Some f ->
    ValidFid s x o f
  | valid_fid_none:
    op_fid o = None ->
    IEF x f s ->
    ValidFid s x o f.

  Inductive FEdge s : (fid * fid) -> Prop :=
  | f_edge_def:
    forall f g t,
    Bind t f s ->
    Open t g s ->
    FEdge s (f, g).

  Inductive CEdge s : (fid * fid) -> Prop :=
  | c_edge_def:
    forall f g t,
    Bind t f s ->
    Current t g s ->
    CEdge s (f, g).

Section Defs.
  Let bind_inv_add:
    forall u g t s ft,
    Bind u g (Map_TID.add t ft s) ->
    (t = u /\ exists l, ft = {| bind := g; open := l |}) \/ (t <> u /\ Bind u g s).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_TID_Facts.add_mapsto_iff in H0.
    destruct H0 as [(?,?)|(?,?)]; eauto using bind_def.
  Qed.

  Lemma bind_inv_add_make:
    forall t u f g s,
    Bind t f (Map_TID.add u (make g) s) ->
    (t = u /\ f = g) \/ 
    (Bind t f s /\ u <> t).
  Proof.
    unfold make; intros.
    match goal with
    | H: Bind _ _ _ |- _  =>  apply bind_inv_add in H;
      destruct H as [(?,(l,R))|(?,i)]
    end. {
      simpl in *.
      inversion R; subst; clear R.
      auto.
    }
    auto.
  Qed.

  Lemma ief_fun:
    forall x f g s,
    IEF x f s ->
    IEF x g s ->
    g = f.
  Proof.
    intros.
    inversion H; inversion H0; subst; clear H H0;
    match goal with H: Map_TID.MapsTo _ _ _, H1: Map_TID.MapsTo _ _ _ |- _
    =>
      eapply Map_TID_Facts.MapsTo_fun in H;
      try apply H1;
      inversion H;
      auto
    end.
  Qed.

  Definition current (ft:task) :=
  match ft with
  | {| bind := f; open := nil |} => None
  | {| bind := g; open := (f::l)%list |} =>  Some f
  end.

  Definition task_edges (ft:task) :=
  List.map (fun f => (bind ft, f)) (open ft).

  Definition f_edges (s:state) : list (fid * fid) := 
  List.flat_map task_edges (Map_TID_Extra.values s).

  Definition c_edges (s:state) : list (fid * fid) := 
  let c_edge (ft:task) :=
  match current ft with
  | Some g => Some (bind ft, g)
  | None => None
  end in
  List.omap c_edge (Map_TID_Extra.values s).

  Lemma bind_eq:
    forall t ft s,
    Map_TID.MapsTo t ft s ->
    Bind t (bind ft) s.
  Proof.
    intros.
    destruct ft; simpl in *.
    eauto using bind_def.
  Qed.

  Lemma in_to_bind:
    forall t s,
    Map_TID.In t s ->
    exists f, Bind t f s.
  Proof.
    intros.
    apply Map_TID_Extra.in_to_mapsto in H.
    destruct H as (ft, mt).
    eauto using bind_eq.
  Qed.

  Lemma not_bind_empty:
    forall t f,
    ~ Bind t f empty.
  Proof.
    unfold not, empty; intros ? ? N.
    inversion N; subst; clear N.
    apply Map_TID_Facts.empty_mapsto_iff in H; auto.
  Qed.

  Lemma open_eq:
    forall f t ft s,
    Map_TID.MapsTo t ft s ->
    List.In f (open ft) ->
    Open t f s.
  Proof.
    intros.
    destruct ft.
    simpl in *.
    eauto using open_def.
  Qed.

  Lemma f_edge_eq:
    forall t f ft s,
    Map_TID.MapsTo t ft s ->
    List.In f (open ft) ->
    FEdge s (bind ft, f).
  Proof.
    eauto using f_edge_def, bind_eq, open_eq.
  Qed.

  Lemma in_to_f_edge:
    forall p s,
    List.In p (f_edges s) ->
    FEdge s p.
  Proof.
    unfold f_edges, task_edges.
    intros.
    apply in_flat_map in H.
    destruct H as (ft, (Hi, Hj)).
    apply Map_TID_Extra.values_spec_1 in Hi.
    destruct Hi as (t, mt).
    apply in_map_iff in Hj.
    destruct Hj as (f, (R, Hi)).
    destruct p as (?, g).
    symmetry in R; inversion R; subst; clear R.
    eauto using f_edge_eq.
  Qed.

  Lemma f_edge_to_in:
    forall p s,
    FEdge s p ->
    List.In p (f_edges s).
  Proof.
    unfold f_edges, task_edges.
    intros.
    rewrite in_flat_map.
    inversion H; subst; clear H.
    inversion H0; subst.
    inversion H1; subst.
    eapply Map_TID_Facts.MapsTo_fun in H; eauto.
    inversion H; subst; clear H.
    exists {| bind := f; open := l |}.
    split. {
      eauto using Map_TID_Extra.values_spec_2.
    }
    rewrite in_map_iff; eauto.
  Qed.

  Lemma f_edge_spec:
    forall s p,
    FEdge s p <-> (FGraph.Edge (f_edges s)) p.
  Proof.
    unfold FGraph.Edge in *; intros; split; auto using f_edge_to_in, in_to_f_edge.
  Qed.

  Lemma c_edge_to_in:
    forall p s,
    CEdge s p ->
    List.In p (c_edges s).
  Proof.
    unfold c_edges.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst.
    inversion H1; subst.
    eapply in_omap_1; eauto using Map_TID_Extra.values_spec_2.
    simpl in *.
    eapply Map_TID_Facts.MapsTo_fun in H; eauto.
    inversion H; subst; clear H.
    trivial.
  Qed.

  Lemma in_to_c_edge:
    forall p s,
    List.In p (c_edges s) ->
    CEdge s p.
  Proof.
    unfold c_edges.
    intros.
    apply in_omap_2 in H.
    destruct H as ([], (Hi, Hj)).
    apply Map_TID_Extra.values_spec_1 in Hi.
    destruct Hi as (t, mt).
    simpl in *.
    destruct open0. {
      inversion Hj.
    }
    inversion Hj; subst; clear Hj.
    eauto using bind_def, current_def, c_edge_def.
  Qed.

  Lemma open_inv_add:
    forall t g s u ft,
    Open t g (Map_TID.add u ft s) ->
    (u = t /\ List.In g (open ft)) \/ (u <> t /\ Open t g s).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_TID_Facts.add_mapsto_iff in H1.
    destruct H1 as [(?,?)|(?,?)]. {
      subst; auto.
    }
    eauto using open_def.
  Qed.

  Lemma open_inv_add_make:
    forall t g f s u,
    Open t g (Map_TID.add u (make f) s) ->
    u <> t /\ Open t g s.
  Proof.
    unfold make; intros.
    apply open_inv_add in H.
    destruct H as [(?,?)|(?,?)]. {
      contradiction.
    }
    auto.
  Qed.

  Let f_edge_add_make:
    forall f t s p,
    ~ In f s ->
    FEdge (Map_TID.add t (make f) s) p ->
    FEdge s p.
  Proof.
    intros.
    match goal with
    | H: FEdge _ _ |- _ =>
      inversion H; subst; clear H
    end.
    match goal with
    | H: Open _ _ _ |- _ =>
      apply open_inv_add_make in H;
      destruct H as (?, Hs)
    end.
    assert (g <> f). {
      unfold not; intros; subst.
      match goal with
      | H: ~ In _ _ |- _ => contradict H
      end.
      eauto using in_open.
    }
    match goal with
    | H: Bind _ _ _ |- _ =>
      apply bind_inv_add_make in H; auto;
      destruct H as [(?,?)|(?,?)]; subst; try contradiction
    end.
    unfold Edge.
    eauto using f_edge_to_in, f_edge_def.
  Qed.

  Let dag_fgraph_edge_to_f_edge:
    forall s,
    DAG (FGraph.Edge (f_edges s)) ->
    DAG (FEdge s).
  Proof.
    intros.
    apply dag_impl with (E:=Edge (f_edges s)); auto.
    intros; unfold FGraph.Edge in *.
    auto using f_edge_to_in.
  Qed.

  Lemma dag_f_edge_to_fgraph_edge:
    forall s,
    DAG (FEdge s) ->
    DAG (Edge (f_edges s)).
  Proof.
    intros.
    apply dag_impl with (E:=FEdge s); auto.
    intros; unfold FGraph.Edge in *.
    auto using in_to_f_edge.
  Qed.

  Let dag_c_edge_to_fgraph_edge:
    forall s,
    DAG (CEdge s) ->
    DAG (Edge (c_edges s)).
  Proof.
    intros.
    apply dag_impl with (E:=CEdge s); auto.
    intros; unfold FGraph.Edge in *.
    auto using in_to_c_edge.
  Qed.

  Let f_edge_inv_add_begin_finish:
    forall t f l g s x y,
    FEdge (Map_TID.add t {| bind := g; open := f :: l |} s) (x, y) ->
    Map_TID.MapsTo t {| bind := g; open := l |} s ->
    (g = x /\ f = y) \/ FEdge s (x, y).
  Proof.
    intros.
    match goal with
    H: FEdge _ _ |- _ => inversion H; subst; clear H
    end.
    match goal with H: Open _ _ _ |- _ => apply open_inv_add in H;
      rename H into Hs
    end.
    match goal with
    H: Bind _ _ _ |- _ => apply bind_inv_add in H;
    destruct H as [(?,(k,R))|(?,?)]
    end. {
      inversion R; clear R.
      destruct Hs as [(?,Hi)|(?,?)]. {
        simpl in *.
        destruct Hi. {
          auto.
        }
        subst.
        eauto using bind_def, open_def, f_edge_def.
      }
      subst.
      contradiction.
    }
    destruct Hs as [(?,Hi)|(?,?)]. {
      subst; contradiction.
    }
    eauto using f_edge_def.
  Qed.

  Let f_edges_rw_add_begin_finish_1:
    forall t g f l s p,
    Edge (f_edges (Map_TID.add t {| bind := g; open := f :: l |} s)) p ->
    Map_TID.MapsTo t {| bind := g; open := l |} s ->
    Edge ((g,f)::(f_edges s)) p.
  Proof.
    unfold Edge; intros.
    apply in_to_f_edge in H.
    destruct p as (x, y).
    apply f_edge_inv_add_begin_finish in H; auto.
    destruct H as [(?,?)|He]. {
      subst.
      auto using in_eq.
    }
    auto using in_cons, f_edge_to_in.
  Qed.

  Lemma f_edge_fst_to_in:
    forall s f g,
    FEdge s (f, g) ->
    In f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using in_bind.
  Qed.

  Lemma f_edge_snd_to_in:
    forall s f g,
    FEdge s (f, g) ->
    In g s.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using in_open.
  Qed.

  Lemma reaches_fst_to_in:
    forall f g s,
    Graph.Reaches (FEdge s) f g ->
    In f s.
  Proof.
    intros.
    apply Graph.reaches_to_in_fst in H.
    inversion H; subst; clear H.
    destruct x as (a,b), H0 as (He,Hi).
    inversion Hi; subst; clear Hi; simpl. {
      eauto using f_edge_fst_to_in.
    }
    eauto using f_edge_snd_to_in.
  Qed.

  Lemma reaches_edge_to_f_edge:
    forall s f g,
    Graph.Reaches (Edge (f_edges s)) f g ->
    Graph.Reaches (FEdge s) f g.
  Proof.
    intros.
    apply Graph.reaches_impl with (E:=Edge (f_edges s)); unfold Edge; auto using in_to_f_edge.
  Qed.

  Lemma open_inv_add_eq:
    forall t g f l s,
    Open t g (Map_TID.add t {| bind := f; open := l |} s) ->
    List.In g l.
  Proof.
    intros.
    apply open_inv_add in H.
    destruct H as [(?,?)|(N,_)]; try contradiction.
    auto.
  Qed.

  Lemma open_inv_add_neq:
    forall t g f l s u,
    Open t g (Map_TID.add u {| bind := f; open := l |} s) ->
    t <> u ->
    Open t g s.
  Proof.
    intros.
    apply open_inv_add in H.
    destruct H as [(?,?)|(N,?)]; subst; try contradiction.
    auto.
  Qed.

  Lemma f_edge_finished:
    forall t g l s f p,
    FEdge (Map_TID.add t {| bind := g; open := l |} s) p ->
    Map_TID.MapsTo t {| bind := g; open := f :: l |} s ->
    Empty f s  ->
    FEdge s p.
  Proof.
    intros.
    inversion H; subst; clear H.
    match goal with
      H2: Bind _ _ _ |- _ =>
      apply bind_inv_add in H2;
      destruct H2 as [(?, (?, R))|(?,?)]
    end. {
      inversion R; subst; clear R.
      match goal with H: Open _ _ _ |- _ => apply open_inv_add_eq in H end.
      eauto using f_edge_def, bind_def, in_cons, open_def.
    }
    match goal with H: Open _ _ _ |- _ => apply open_inv_add_neq in H;auto end.
    eauto using f_edge_def.
  Qed.

  Lemma f_edge_begin_task:
    forall u ft s p,
    FEdge (Map_TID.add u (make (ief ft)) s) p ->
    FEdge s p.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply bind_inv_add_make in H0.
    destruct H0 as [(?,?)|(?,Hr)]. {
      subst.
      apply open_inv_add_make in H1.
      destruct H1 as (N,_); contradiction.
    }
    apply open_inv_add_make in H1.
    destruct H1; eauto using f_edge_def.
  Qed.

  Lemma bind_inv_remove:
    forall t f u s,
    Bind t f (Map_TID.remove u s) ->
    u <> t /\ Bind t f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_TID_Facts.remove_mapsto_iff in H0.
    destruct H0.
    eauto using bind_def.
  Qed.

  Lemma open_inv_remove:
    forall t f u s,
    Open t f (Map_TID.remove u s) ->
    u <> t /\ Open t f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_TID_Facts.remove_mapsto_iff in H1.
    destruct H1.
    eauto using open_def.
  Qed.

  Lemma f_edge_end_task:
    forall t s p f,
    FEdge (Map_TID.remove t s) p ->
    Map_TID.MapsTo t {| bind := f; open := [] |} s ->
    FEdge s p.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply bind_inv_remove in H1.
    destruct H1 as (?,Hr).
    apply open_inv_remove in H2.
    destruct H2 as (?,Hs).
    eauto using f_edge_def.
  Qed.

  Lemma f_dag_reduces:
    forall s a s',
    DAG (FGraph.Edge (f_edges s)) ->
    Reduces s a s' ->
    DAG (FGraph.Edge (f_edges s')).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - apply dag_f_edge_to_fgraph_edge, dag_impl with (E:=FEdge s);
      eauto using f_edge_begin_task, f_edge_finished.
    - apply dag_impl with (E:=Edge (((g,f)::(f_edges s)))). {
        eauto.
      }
      assert (f <> g). {
        unfold not; intros; subst.
        assert (In g s). {
          eauto using bind_def, in_bind.
        }
        contradiction.
      }
      apply f_dag_cons; auto using FID.eq_dec.
      unfold not; intros N.
      apply reaches_edge_to_f_edge,reaches_fst_to_in in N.
      contradiction.
    - apply dag_f_edge_to_fgraph_edge, dag_impl with (E:=FEdge s);
      eauto using f_edge_begin_task, f_edge_finished.
    - apply dag_f_edge_to_fgraph_edge, dag_impl with (E:=FEdge s);
      eauto using f_edge_begin_task.
    - apply dag_f_edge_to_fgraph_edge, dag_impl with (E:=FEdge s);
      eauto using f_edge_begin_task, f_edge_finished, f_edge_end_task.
  Qed.

  Lemma f_edge_to_edge:
    forall s p,
    FEdge s p ->
    Edge (f_edges s) p.
  Proof.
    unfold Edge; auto using f_edge_to_in.
  Qed.

  Lemma edge_to_f_edge:
    forall s p,
    Edge (f_edges s) p ->
    FEdge s p.
  Proof.
    unfold Edge; auto using in_to_f_edge.
  Qed.

  Lemma c_edge_to_edge:
    forall s p,
    CEdge s p ->
    Edge (c_edges s) p.
  Proof.
    unfold Edge; auto using c_edge_to_in.
  Qed.

  Lemma edge_to_c_edge:
    forall s p,
    Edge (c_edges s) p ->
    CEdge s p.
  Proof.
    unfold Edge; auto using in_to_c_edge.
  Qed.

  Lemma open_nil_to_not_open:
    forall x g s,
    Map_TID.MapsTo x {| bind := g; open := [] |} s ->
    forall f, ~ Open x f s.
  Proof.
    unfold not; intros.
    inversion H0; subst; clear H0.
    eapply Map_TID_Facts.MapsTo_fun in H; eauto.
    inversion H; subst; clear H.
    contradiction.
  Qed.

  Lemma open_nil_to_not_current:
    forall x g s,
    Map_TID.MapsTo x {| bind := g; open := [] |} s ->
    forall f, ~ Current x f s.
  Proof.
    unfold not; intros.
    inversion H0; subst; clear H0.
    eapply Map_TID_Facts.MapsTo_fun in H; eauto.
    inversion H; subst; clear H.
  Qed.

  Let dag_cond:
    forall s, 
    DAG (Edge (c_edges s)) ->
    (forall x, Map_TID.In x s -> forall f, ~ Current x f s) \/
    (exists t f, Current t f s /\ forall u, Bind u f s -> forall g, ~ Current u g s).
  Proof.
    intros.
    remember (c_edges s).
    destruct l. {
      left; intros.
      apply Map_TID_Extra.in_to_mapsto in H0.
      destruct H0 as (ft, mt).
      destruct ft as (g, l).
      destruct l. {
        eauto using open_nil_to_not_current.
      }
      assert (He: CEdge s (g, f0)) by eauto using List.in_eq, current_def, c_edge_def, bind_def.
      apply c_edge_to_edge in He.
      rewrite <- Heql in *.
      inversion He.
    }
    right.
    assert (p :: l <> []). {
      unfold not; intros N; inversion N.
    }
    eapply dag_infimum in H; eauto using FID.eq_dec.
    destruct H as (f, (?,?)).
    destruct H as ((a,b),(He,[])); subst; simpl; simpl in H1. {
       apply Graph.edge_to_reaches in He.
       apply H1 in He.
       contradiction.
    }
    rewrite Heql in He.
    apply edge_to_c_edge in He.
    inversion He; subst; clear He.
    exists t; exists b; split; auto.
    unfold not; intros.
    assert (He : CEdge s (b, g)) by eauto using c_edge_def.
    match goal with H: CEdge _ _ |- _ =>
      apply c_edge_to_edge in H;
      rewrite <- Heql in *;
      apply Graph.edge_to_reaches in H
    end.
    apply H1 in He.
    assumption.
  Qed.

  Lemma dag_reduces:
    forall s a s',
    DAG (FEdge s) ->
    Reduces s a s' ->
    DAG (FEdge s').
  Proof.
    eauto using dag_f_edge_to_fgraph_edge, dag_fgraph_edge_to_f_edge, f_dag_reduces.
  Qed.

  Inductive Blocking: op -> Prop :=
  | blocking_def:
    Blocking END_FINISH.

  Inductive Nonblocking: op -> Prop :=
  | nonblocking_init:
    forall f,
    Nonblocking (INIT f)
  | nonblocking_begin_finish:
    forall f,
    Nonblocking (BEGIN_FINISH f)
  | nonblocking_begin_task:
    forall t,
    Nonblocking (BEGIN_TASK t)
  | nonblocking_end_task:
    Nonblocking END_TASK.

  Definition blocking_dec o:
    { Blocking o } + { Nonblocking o }.
  Proof.
    destruct o; auto using blocking_def, nonblocking_init, nonblocking_begin_task, nonblocking_end_task, nonblocking_begin_finish.
  Defined.

  Lemma nonblocking_to_not_blocking:
    forall o,
    Nonblocking o -> ~ Blocking o.
  Proof.
    unfold not; intros ? ? N.
    inversion N.
    inversion H; subst; inversion H1.
  Qed.

  Lemma not_blocking_to_nonblocking:
    forall o,
    ~ Blocking o -> Nonblocking o.
  Proof.
    unfold not.
    intros ? N.
    destruct o;
    auto using nonblocking_init,
      nonblocking_begin_task,
      nonblocking_end_task,
      nonblocking_begin_finish.
    contradiction N.
    auto using blocking_def.
  Qed.

  Lemma blocking_to_not_unblocking:
    forall o,
    Blocking o -> ~ Nonblocking o.
  Proof.
    unfold not.
    intros ? ? N.
    inversion H; subst; clear H.
    inversion N.
  Qed.

  Lemma not_unblocking_to_blocking:
    forall o,
    ~ Nonblocking o -> Blocking o.
  Proof.
    intros.
    destruct o;
    auto using blocking_def;
    contradiction H;
    auto using nonblocking_init,
      nonblocking_begin_task,
      nonblocking_end_task,
      nonblocking_begin_finish.
  Qed.

  Lemma progress_nonblocking:
    forall s t o,
    Valid s t o ->
    Nonblocking o ->
    exists s', Reduces s (t, o) s'.
  Proof.
    intros.
    inversion H0; subst; clear H0;
    inversion H; subst; clear H;
    eauto using reduces_init, reduces_end_task;
    match goal with [ H: Map_TID.In _ _ |- _ ] =>
      apply Map_TID_Extra.in_to_mapsto in H;
      destruct H as ((?,?), mt) end.
    - eauto using reduces_begin_finish.
    - eauto using reduces_begin_task.
  Qed.

  Inductive Nonempty (f:fid) (s:state) : Prop :=
  | nonempty_def:
    forall x,
    Bind x f s ->
    Nonempty f s.

  Lemma nonempty_to_in:
    forall f s,
    Nonempty f s ->
    In f s.
  Proof.
    intros.
    inversion H.
    eauto using in_bind.
  Qed.

  Let has_bind t f s :=
  match Map_TID.find t s with
  | Some ft => if FID.eq_dec f (bind ft) then true else false
  | _ => false
  end.

  Section IEF_dec.
    Let ief_to_in:
      forall x f s,
      IEF x f s -> Map_TID.In x s.
    Proof.
      intros.
      inversion H; eauto using Map_TID_Extra.mapsto_to_in.
    Qed.

    Lemma ief_to_some:
      forall x s f,
      IEF x f s -> get_ief x s = Some f.
    Proof.
      intros.
      unfold get_ief.
      destruct (Map_TID_Extra.find_rw x s) as [(R,Hx)|(ft, (R,?))]; rewrite R. {
        assert (Map_TID.In x s) by eauto.
        contradiction.
      }
      inversion H; subst; clear H;
      remember {| bind := _; open := _ |} as ft';
      assert (ft' = ft) by eauto using Map_TID_Facts.MapsTo_fun;
      subst; simpl; trivial.
    Qed.

    Lemma some_to_ief:
      forall x s f,
      get_ief x s = Some f -> IEF x f s.
    Proof.
      unfold get_ief; intros.
      destruct (Map_TID_Extra.find_rw x s) as [(R,Hx)|(ft, (R,?))]; rewrite R in *; clear R. {
        inversion H.
      }
      destruct ft as (r, []); inversion H; subst; clear H. {
        auto using ief_nil.
      }
      eauto using ief_cons.
    Qed.

    Lemma none_to_not_ief:
      forall x s f,
      get_ief x s = None ->
      ~ IEF x f s.
    Proof.
      intros.
      unfold not; intros N.
      apply ief_to_some in N.
      rewrite N in *; inversion H.
    Qed.

    Definition valid_fid s x o :=
    match op_fid o with
    | Some f => Some f
    | None => get_ief x s
    end.

    Lemma some_to_valid_fid:
      forall s f x o,
      valid_fid s x o = Some f ->
      ValidFid s x o f.
    Proof.
      unfold valid_fid; intros.
      remember (op_fid o).
      destruct o0; inversion H; subst. {
        auto using valid_fid_some.
      }
      auto using some_to_ief, valid_fid_none.
    Qed.

    Lemma valid_fid_to_some:
      forall s f x o,
      ValidFid s x o f ->
      valid_fid s x o = Some f.
    Proof.
      intros.
      inversion H; subst; clear H; unfold valid_fid;
      rewrite H0; trivial.
      auto using ief_to_some.
    Qed.

    Lemma in_to_ief:
      forall x s,
      Map_TID.In x s ->
      exists f, IEF x f s.
    Proof.
      intros.
      apply Map_TID_Extra.in_to_mapsto in H.
      destruct H as ((f, [|l]), mt); eauto using ief_nil, ief_cons.
    Qed.

    Lemma valid_fid_incl_valid:
      forall s x o,
      Valid s x o ->
      exists f, ValidFid s x o f.
    Proof.
      intros.
      inversion H; subst; clear H;
      try (exists f; apply valid_fid_some; simpl; auto; fail). (* handle some-cases *)
      - assert (IEF x f s) by eauto using ief_cons, ief_nil.
        eauto using valid_fid_none.
      - assert (X: exists f, IEF x f s) by eauto using in_to_ief.
        destruct X.
        eauto using valid_fid_none.
      - eauto using valid_fid_none, ief_nil.
    Qed.

    Lemma maps_to_to_ief:
      forall x ft s,
      Map_TID.MapsTo x ft s ->
      IEF x (ief ft) s.
    Proof.
      intros.
      destruct ft as (f, l).
      destruct l; simpl. {
        auto using ief_nil.
      }
      eauto using ief_cons.
    Qed.

    Lemma ief_inv_1:
      forall x ft s f,
      Map_TID.MapsTo x ft s ->
      IEF x f s ->
      ief ft = f.
    Proof.
      intros.
      apply ief_to_some in H0.
      unfold get_ief in *.
      destruct (Map_TID_Extra.find_rw x s) as [(R,mt)|(ft',(R,?))];
      rewrite R in *; inversion H0; subst; clear H0.
      assert (ft' = ft) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      trivial.
    Qed.

    Lemma not_ief_to_none:
      forall x s,
      (forall f, ~ IEF x f s) ->
      get_ief x s = None.
    Proof.
      intros.
      unfold get_ief.
      destruct (Map_TID_Extra.find_rw x s) as [(R,Hx)|(ft, (R,?))]; rewrite R in *; clear R. {
        trivial.
      }
      apply maps_to_to_ief in H0.
      apply H in H0.
      contradiction.
    Qed.
  End IEF_dec.

  Lemma bind_to_in:
    forall t f s,
    Bind t f s ->
    Map_TID.In t s.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Lemma bind_fun:
    forall t f s g,
    Bind t f s ->
    Bind t g s ->
    f = g.
  Proof.
    intros.
    inversion H; inversion H0; subst; clear H H0.
    match goal with [ H1: Map_TID.MapsTo t ?x s, H2: Map_TID.MapsTo t ?y s |- _] =>
      assert (R: x = y) by eauto using Map_TID_Facts.MapsTo_fun;
      inversion R; subst; clear R
    end.
    trivial.
  Qed.

  Lemma bind_dec t f s:
    { Bind t f s } + { ~ Bind t f s }.
  Proof.
    remember (has_bind t f s).
    symmetry in Heqb;
    unfold has_bind in *.
    destruct b. {
      left.
      destruct (Map_TID_Extra.find_rw t s) as [(R,?)|((g,l),(R,?))];
      rewrite R in *.
      - inversion Heqb.
      - simpl in *.
        destruct (FID.eq_dec f g). {
          subst.
          eauto using bind_def.
        }
        inversion Heqb.
    }
    right.
    destruct (Map_TID_Extra.find_rw t s) as [(R,?)|((g,l),(R,?))];
    rewrite R in *. {
      unfold not; intros N.
      apply bind_to_in in N.
      contradiction.
    }
    simpl in *.
    destruct (FID.eq_dec f g). {
      inversion Heqb.
    }
    unfold not; intros N.
    assert (Bind t g s) by eauto using bind_def.
    assert (f = g)  by eauto using bind_fun.
    contradiction.
  Defined.

  Let filter_bind f s :=
  Map_TID_Extra.filter (fun t ft => if FID.eq_dec f (bind ft) then true else false) s.

  Lemma nonempty_empty_dec f s:
    { Nonempty f s } + { Empty f s }.
  Proof.
    destruct (Map_TID_Extra.any_in_dec (filter_bind f s)) as [(t,Hi)|X];
    unfold filter_bind in *. {
      left.
      apply Map_TID_Extra.in_to_mapsto in Hi.
      destruct Hi as (ft, mt).
      apply Map_TID_Extra.filter_spec in mt; auto using tid_eq_rw.
      destruct mt as (mt, Hx).
      destruct (FID.eq_dec f (bind ft)). {
        subst.
        eauto using nonempty_def, bind_eq.
      }
      inversion Hx.
    }
    right.
    destruct X as (_, He).
    rewrite Map_TID_Extra.empty_filter_spec in He; auto using tid_eq_rw.
    apply empty_def; intros.
    unfold not; intros N.
    inversion N; subst; clear N.
    apply He in H.
    simpl in *.
    destruct (FID.eq_dec f f). {
      inversion H.
    }
    contradiction.
  Defined.

  Let current_to_open:
    forall t f s,
    Current t f s ->
    Open t f s.
  Proof.
    intros.
    inversion H; subst.
    eauto using open_def, List.in_eq.
  Qed.

  Let c_edge_to_f_edge:
    forall s e,
    CEdge s e ->
    FEdge s e.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using f_edge_def, current_to_open.
  Qed.

  Let dag_f_edge_to_c_edge:
    forall s,
    DAG (FEdge s) ->
    DAG (CEdge s).
  Proof.
    intros.
    apply dag_impl with (E:=FEdge s); auto using c_edge_to_f_edge.
  Qed.

  Lemma current_fun:
    forall t f g s,
    Current t f s ->
    Current t g s ->
    f = g.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    apply Map_TID_Facts.MapsTo_fun with (e:={| bind := g1; open := g :: l0 |}) in H1; auto.
    inversion H1; subst; auto.
  Qed.

  Lemma progress_empty:
    forall t f s,
    Empty f s ->
    Current t f s ->
    forall o,
    Valid s t o ->
    exists s', Reduces s (t, o) s'.
  Proof.
    intros.
    destruct (blocking_dec o). {
      inversion b; subst; clear b.
      inversion H1; subst.
      assert (f0 = f). {
        assert (Current t f0 s) by eauto using current_def.
        eauto using current_fun.
      }
      subst.
      exists ((Map_TID.add t {| bind := g; open := l |} s)).
      eapply reduces_end_finish; eauto.
    }
    auto using progress_nonblocking.
  Qed.

  (** An enabled task can reduce with any operation. *)
  Definition Enabled s t :=
  forall o, Valid s t o -> exists s', Reduces s (t, o) s'.

  Tactic Notation "expect" uconstr(X) constr(f) :=
  (match goal with
  [ H: X |- _ ] => f H
  end).

  Let bind_to_ief:
    forall x f s,
    (forall f, ~ Current x f s) ->
    Bind x f s ->
    IEF x f s.
  Proof.
    intros.
    match goal with [H: Bind x _ _ |- _ ] => inversion H; subst; clear H end.
    destruct l. {
      auto using ief_nil.
    }
    assert (X:Current x f0 s) by eauto using current_def.
    contradict X; eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Theorem progress:
    forall s,
    (* Given that a finish-state is a DAG *)
    DAG (FEdge s) ->
    (* And that state is not empty *)
    ~ Map_TID.Empty s ->
    (* Then there is some [f] such that *)
    exists f,
    ((* [f] is nonempty and every task in [f] reduces. *)
      Nonempty f s
      /\
      (forall x, Bind x f s -> Enabled s x)
      /\
      (forall x, Bind x f s -> IEF x f s)
    )
    \/
    ((* Or [f] is empty, and [t]'s current finish-scope is [f] *)
      Empty f s
      /\
      exists x, Current x f s /\ Enabled s x
    ).
  Proof.
    intros.
    unfold Enabled.
    apply Map_TID_Extra.nonempty_in in H0.
    apply dag_f_edge_to_c_edge,
          dag_c_edge_to_fgraph_edge,
          dag_cond in H.
    destruct H as [H|(y, (f, (Hs, Hr)))]. {
      destruct H0 as (y, Hi).
      apply Map_TID_Extra.in_to_mapsto in Hi.
      destruct Hi as ((g,l), mt).
      assert (Hr: Bind y g s) by eauto using bind_def.
      exists g.
      left.
      split; eauto using nonempty_def.
      assert (forall x f, ~Current x f s). {
        unfold not; intros ? ? N.
        inversion N; subst; clear N.
        assert (X:Current x f s) by eauto using current_def.
        contradict X; eauto using Map_TID_Extra.mapsto_to_in.
      }
      split; auto.
      intros.
      destruct (blocking_dec o). {
        inversion b; subst; clear b.
        match goal with H: Valid _ _ _ |- _ => inversion H; subst; clear H end.
        assert (g0 = g) by eauto using bind_fun, bind_def; subst.
        assert (Xc: Current x f s) by eauto using current_def.
        contradict Xc.
        eauto using Map_TID_Extra.mapsto_to_in.
      }
      eauto using progress_nonblocking.
    }
    destruct (nonempty_empty_dec f s). {
      exists f.
      left; split; auto.
      split. {
        intros.
        destruct (blocking_dec o). {
          inversion b; subst; clear b.
          subst.
          match goal with H: Valid _ _ _ |- _ => inversion H; subst; clear H end.
          assert (g = f) by eauto using bind_fun, bind_def; subst.
          assert (X: ~ Current x f0 s) by eauto using Map_TID_Extra.mapsto_to_in.
          contradict X; eauto using current_def.
        }
        eauto using progress_nonblocking.
      }
      eauto using bind_to_ief.
    }
    exists f.
    right;
    split; eauto using progress_empty.
  Qed.
End Defs.

Section Props.

  Lemma bind_inv_add:
    forall x y ft s f,
    Bind y f (Map_TID.add x ft s) ->
    (x = y /\ Task.Bind f ft) \/ Bind y f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_TID_Facts.add_mapsto_iff in H0.
    destruct H0 as [(?,?)|(?,?)].
    + subst.
      auto using Task.bind_def.
    + eauto using bind_def, in_bind.
  Qed.

  Lemma in_inv_add:
    forall f x ft s,
    In f (Map_TID.add x ft s) ->
    Task.In f ft \/ In f s.
  Proof.
    intros.
    inversion H.
    - apply bind_inv_add in H0.
      destruct H0 as [(?, ?)|?].
      + auto using Task.in_bind.
      + eauto using in_bind.
    - apply open_inv_add in H0.
      destruct H0 as [(?,?)|(?,?)]. {
        destruct ft in *; simpl in *.
        auto using Task.in_open, Task.open_def.
      }
      eauto using in_open.
  Qed.

  Let task_bind_to_bind:
    forall x ft s f,
    Map_TID.MapsTo x ft s ->
    Task.Bind f ft ->
    Bind x f s.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eauto using bind_def.
  Qed.

  Let task_open_to_open:
    forall x ft s f,
    Map_TID.MapsTo x ft s ->
    Task.Open f ft ->
    Open x f s.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eauto using open_def.
  Qed.

  Let task_in_to_in:
    forall x ft s f,
    Task.In f ft ->
    Map_TID.MapsTo x ft s ->
    In f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    + eauto using task_bind_to_bind, in_bind.
    + eauto using task_open_to_open, in_open.
  Qed.

  Let task_in_inv_eq_make:
    forall f g,
    Task.In f (make g) ->
    f = g.
  Proof.
    intros.
    unfold make in *.
    inversion H; subst; clear H;
    inversion H0; subst; clear H0.
    - trivial.
    - inversion H2.
  Qed.

  Let task_bind_inv_eq:
    forall f g l,
    Task.Bind f {| bind := g; open := l |} ->
    g = f.
  Proof.
    intros.
    inversion H; auto.
  Qed.

  Let task_bind_cons:
    forall f g l h,
    Task.Bind f {| bind := g; open := l |} ->
    Task.Bind f {| bind := g; open := h::l |}.
  Proof.
    intros.
    inversion H; subst; clear H.
    auto using Task.bind_def.
  Qed.

  Let task_open_cons:
    forall f g l h,
    Task.Open f {| bind := g; open := l |} ->
    Task.Open f {| bind := g; open := h::l |}.
  Proof.
    intros.
    inversion H; subst; clear H.
    auto using Task.open_def, List.in_cons.
  Qed.

  Let task_in_cons:
    forall f g l h,
    Task.In f {| bind := g; open := l |} ->
    Task.In f {| bind := g; open := h::l |}.
  Proof.
    intros.
    inversion H; subst; clear H. {
      auto using task_bind_cons, Task.in_bind.
    }
    auto using task_open_cons, Task.in_open.
  Qed.

  Let in_ief:
    forall x ft s,
    Map_TID.MapsTo x ft s ->
    In (ief ft) s.
  Proof.
    intros.
    destruct ft as (f, [|g]); simpl.
    + eauto using in_bind, bind_def.
    + eauto using in_open, in_eq, open_def.
  Qed.

  Let bind_inv_remove:
    forall x f s y,
    Bind y f (Map_TID.remove x s) ->
    x <> y /\ Bind y f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_TID_Facts.remove_mapsto_iff in H0.
    destruct H0 as (?, ?).
    eauto using bind_def.
  Qed.

  Let open_inv_remove:
    forall x f s y,
    Open y f (Map_TID.remove x s) ->
    x <> y /\ Open y f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_TID_Facts.remove_mapsto_iff in H1.
    destruct H1 as (?, ?).
    eauto using open_def.
  Qed.

  Let in_inv_remove:
    forall x s f,
    In f (Map_TID.remove x s) ->
    In f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    - apply bind_inv_remove in H0.
      destruct H0.
      eauto using in_bind.
    - apply open_inv_remove in H0.
      destruct H0.
      eauto using in_open.
  Qed.

  Lemma reduces_in_inv:
    forall x f o s s',
    In f s' ->
    Reduces s (x, o) s' ->
    (o = INIT f /\ ~ In f s) \/
    (o = BEGIN_FINISH f /\ ~ In f s) \/
    In f s.
  Proof.
    intros.
    inversion H0; subst; clear H0;
    try (apply in_inv_add in H; destruct H; auto).
    - match goal with H: Task.In _ (make _) |- _ =>
        apply task_in_inv_eq_make in H
      end.
      subst; auto.
    - match goal with H: Task.In _ _ |- _ =>
        inversion H; subst; clear H
      end.
      + assert (g = f) by eauto.
        subst.
        eauto using in_bind, bind_def.
      + match goal with H: Task.Open _ _ |- _ =>
          inversion H; subst; clear H
        end.
        match goal with H: List.In _ _ |- _ =>
          inversion H; subst; clear H
        end.
        * auto.
        * eauto using open_def, in_open.
    - eauto using task_in_to_in, task_in_cons.
    - match goal with H: Task.In _ (make _) |- _ =>
        apply task_in_inv_eq_make in H
      end; subst.
      eauto using in_ief.
    - eauto using in_inv_remove.
  Qed.

  Let bind_add_neq:
    forall y f s x ft,
    Bind y f s ->
    x <> y ->
    Bind y f (Map_TID.add x ft s).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using bind_def, Map_TID.add_2.
  Qed.

  Lemma bind_reduces:
    forall x y f s s' o,
    Bind y f s ->
    Reduces s (x, o) s' ->
    (y = x /\ exists g, o = INIT g) \/
    (y = x /\ o = END_TASK) \/
    Bind y f s'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - destruct (TID.eq_dec x y); subst. {
        eauto 4.
      }
      eauto using bind_add_neq.
    - destruct (TID.eq_dec x y); subst. {
        assert (Bind y g s) by eauto using bind_def.
        assert (f = g) by eauto using bind_fun.
        subst.
        eauto using bind_def, Map_TID.add_1.
      }
      eauto using bind_add_neq.
    - destruct (TID.eq_dec x y); subst. {
        assert (Bind y g s) by eauto using bind_def.
        assert (f = g) by eauto using bind_fun.
        subst.
        eauto using bind_def, Map_TID.add_1.
      }
      eauto using bind_add_neq.
    - destruct (TID.eq_dec y u); subst. {
        apply bind_to_in in H.
        contradiction.
      }
      eauto using bind_add_neq.
    - destruct (TID.eq_dec y x); subst. {
        auto.
      }
      assert (Bind x f0 s) by eauto using bind_def.
      right.
      right.
      inversion H; subst; clear H.
      eapply bind_def; eauto using Map_TID.remove_2.
  Qed.

  Let open_add_neq:
    forall y f s x ft,
    Open y f s ->
    x <> y ->
    Open y f (Map_TID.add x ft s).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using open_def, Map_TID.add_2.
  Qed.

  Lemma open_to_in:
    forall x f s,
    Open x f s ->
    Map_TID.In x s.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Definition in_dec (f:fid) (s:state) :
    { In f s } + { ~ In f s }.
  Proof.
    remember (fun (x:tid) ft => if Task.in_dec f ft then true else false) as helper.
    destruct (Map_TID_Extra.exists_dec tid_eq_rw helper s) as [((x,ft),(mt, Heq))|(_,Hx)]. {
      simpl in *.
      rewrite Heqhelper in *.
      destruct (Task.in_dec f ft). {
        eauto using task_in_to_in.
      }
      inversion Heq.
    }
    right.
    unfold not; intros N; inversion N; clear N.
    - inversion H; subst; clear H.
      apply Hx in H0.
      destruct (Task.in_dec f {| bind := f; open := l |}). {
        inversion H0.
      }
      assert (Task.In f {| bind := f; open := l |}) by auto using Task.in_bind, Task.bind_def.
      contradiction.
    - inversion H; subst; clear H.
      apply Hx in H1.
      destruct (Task.in_dec f {| bind := g; open := l |}). {
        inversion H1.
      }
      assert (Task.In f {| bind := g; open := l |}) by auto using Task.in_open, Task.open_def.
      contradiction.
  Defined.

  Inductive reduces_err :=
  | TASK_EXIST: tid -> reduces_err
  | TASK_NOT_EXIST: tid -> reduces_err
  | FINISH_EXIST: fid -> reduces_err
  | FINISH_NOT_EXIST: fid -> reduces_err
  | FINISH_NONEMPTY: fid -> reduces_err
  | FINISH_OPEN_EMPTY: reduces_err.

  Definition reduces s x o : state + reduces_err :=
  match o with
  | INIT f =>
    if in_dec f s then inr (FINISH_EXIST f) else
    match Map_TID.find x s with
    | Some _ => inr (TASK_EXIST x)
    | None => inl (Map_TID.add x (make f) s)
    end
  | BEGIN_FINISH f =>
    if in_dec f s then inr (TASK_EXIST x) else
    match Map_TID.find x s with
    | None => inr (TASK_NOT_EXIST x)
    | Some {| bind := g; open := l|} => inl (Map_TID.add x {| bind := g; open := f :: l |} s)
    end
  | END_FINISH =>
    match Map_TID.find x s with
    | Some {| bind := g; open := f ::l|} =>
      if nonempty_empty_dec f s then inr (FINISH_NONEMPTY f) else
       inl (Map_TID.add x {| bind := g; open := l |} s)
    | Some {| bind := g; open := [] |} => inr FINISH_OPEN_EMPTY
    | None => inr (TASK_NOT_EXIST x)
    end
  | BEGIN_TASK y =>
    match Map_TID.find y s, Map_TID.find x s with
    | None, Some ft => inl (Map_TID.add y (make (ief ft)) s)
    | Some _, _ => inr (TASK_EXIST y)
    | _, None => inr (TASK_NOT_EXIST x)
    end
  | END_TASK =>
    match Map_TID.find x s with
    | Some {| bind := f; open := [] |} => inl (Map_TID.remove x s)
    | _ => inr (TASK_NOT_EXIST x)
    end
  end.

  Lemma reduces_some_to_prop:
    forall s x o s',
    reduces s x o = inl s' ->
    Reduces s (x, o) s'.
  Proof.
    intros.
    destruct o; simpl in *.
    - destruct (in_dec f s). {
        inversion H.
      }
      destruct (Map_TID_Extra.find_rw x s) as [(R,Hx)|(?,(R,Hx))]; rewrite R in *; clear R. {
        inversion H; subst; clear H.
        auto using reduces_init.
      }
      inversion H.
    - destruct (in_dec f s). {
        inversion H.
      }
      destruct (Map_TID_Extra.find_rw x s) as [(R,Hx)|((g,l),(R,Hx))];
      rewrite R in *; clear R;
      inversion H; subst; clear H.
      auto using reduces_begin_finish.
    - destruct (Map_TID_Extra.find_rw x s) as [(R,Hx)|((g,l),(R,Hx))];
      rewrite R in *; clear R;
      inversion H; subst; clear H.
      destruct l. {
        inversion H1.
      }
      destruct (nonempty_empty_dec f s);
      inversion H1; subst; clear H1.
      eauto using reduces_end_finish.
    - destruct (Map_TID_Extra.find_rw x s) as [(R,Hx)|((g,l),(R,Hx))];
      rewrite R in *; clear R. {
        destruct (Map_TID_Extra.find_rw t s) as [(R,Hy)|((h,m),(R,Hy))];
        rewrite R in *; clear R;
        inversion H.
      }
      destruct (Map_TID_Extra.find_rw t s) as [(R,Hy)|(ft,(R,Hy))];
      rewrite R in *; clear R;
      inversion H; subst; clear H.
      remember(make _) as ft.
      assert (R: ft = make (ief {| bind := g; open := l |})). {
        rewrite Heqft in *; simpl.
        auto.
      }
      rewrite R in *; clear R.
      auto using reduces_begin_task.
    - destruct (Map_TID_Extra.find_rw x s) as [(R,Hx)|((g,l),(R,Hx))];
      rewrite R in *; clear R. {
        inversion H.
      }
      destruct l; inversion H; subst; clear H.
      eauto using reduces_end_task.
  Qed.

  Lemma empty_to_not_nonempty:
    forall f s,
    Empty f s ->
    ~ Nonempty f s.
  Proof.
    intros.
    unfold not; intros N.
    inversion H; subst; clear H.
    inversion N; subst; clear N.
    assert (~ Bind x f s) by auto.
    contradiction.
  Qed.

  Lemma nonempty_to_not_empty:
    forall f s,
    Nonempty f s ->
    ~ Empty f s.
  Proof.
    unfold not; intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    assert (~ Bind x f s) by auto.
    contradiction.
  Qed.

  Lemma reduces_prop_to_some:
    forall s x o s',
    Reduces s (x, o) s' ->
    reduces s x o = inl s'.
  Proof.
    intros.
    inversion H; subst; clear H; simpl.
    - destruct (in_dec f s). {
        contradiction.
      }
      destruct (Map_TID_Extra.find_rw x s) as [(R,Hx)|((g,l),(R,Hx))];
      rewrite R in *; clear R. {
        trivial.
      }
      apply Map_TID_Extra.mapsto_to_in in Hx.
      contradiction.
    - destruct (in_dec f s). {
        contradiction.
      }
      destruct (Map_TID_Extra.find_rw x s) as [(R,Hx)|(ft,(R,Hx))];
      rewrite R in *; clear R. {
        apply Map_TID_Extra.mapsto_to_in in H5.
        contradiction.
      }
      assert (ft = {| bind := g; open := l |}) by
      eauto using Map_TID_Facts.MapsTo_fun; subst.
      trivial.
    - destruct (Map_TID_Extra.find_rw x s) as [(R,Hx)|(ft,(R,Hx))];
      rewrite R in *; clear R. {
        apply Map_TID_Extra.mapsto_to_in in H3.
        contradiction.
      }
      assert (ft = {| bind := g; open := f:: l |}) by
      eauto using Map_TID_Facts.MapsTo_fun; subst.
      destruct (FID.eq_dec f f). {
        destruct (nonempty_empty_dec f s). {
          apply nonempty_to_not_empty in n.
          contradiction.
        }
        trivial.
      }
      contradiction.
    - destruct (Map_TID_Extra.find_rw x s) as [(R,Hx)|(ft',(R,Hx))];
      rewrite R in *; clear R. {
        contradict Hx.
        eauto using Map_TID_Extra.mapsto_to_in.
      }
      assert (ft' = ft) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      destruct (Map_TID_Extra.find_rw u s) as [(R,Hy)|(ft',(R,Hy))];
      rewrite R in *; clear R. {
        trivial.
      }
      apply Map_TID_Extra.mapsto_to_in in Hy; contradiction.
    - destruct (Map_TID_Extra.find_rw x s) as [(R,Hx)|(ft',(R,Hx))];
      rewrite R in *; clear R. {
        contradict Hx.
        eauto using Map_TID_Extra.mapsto_to_in.
      }
      assert (ft' = {| bind := f; open := [] |}) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      trivial.
  Qed.

  Lemma open_reduces_inv_end_finish:
    forall x f s s' g,
    Open x f s ->
    IEF x g s ->
    Reduces s (x, END_FINISH) s' ->
    f = g \/ (f <> g /\ Open x f s').
  Proof.
    intros.
    inversion H1; subst; clear H1.
    assert (f0 = g). {
      inversion H0; subst; clear H0;
      match goal with H1: Map_TID.MapsTo _ ?v1 _, H2: Map_TID.MapsTo _ ?v2 _ |- _
      => assert (R: v1 = v2) by eauto using Map_TID_Facts.MapsTo_fun; inversion R; subst; clear R
      end.
      trivial.
    }
    subst.
    inversion H; subst; clear H.
    match goal with H1: Map_TID.MapsTo _ ?v1 _, H2: Map_TID.MapsTo _ ?v2 _ |- _
    => assert (R: v1 = v2) by eauto using Map_TID_Facts.MapsTo_fun; inversion R; subst;
    clear R H1
    end.
    inversion H1; subst; clear H1; auto.
    destruct (FID.eq_dec f g). {
      auto.
    }
    eauto using Map_TID.add_1, open_def.
  Qed.

  Lemma open_reduces:
    forall x y f s s' o,
    Open y f s ->
    Reduces s (x, o) s' ->
    (y = x /\ o = END_FINISH) \/
    Open y f s'.
  Proof.
    intros.
    inversion H0; subst; clear H0;
    destruct (TID.eq_dec x y); subst; try (right; auto using open_add_neq; fail).
    - apply open_to_in in H.
      contradiction.
    - inversion H; subst; clear H.
      match goal with
      H1: Map_TID.MapsTo y ?a _, H2: Map_TID.MapsTo y ?b _ |- _ =>
      assert(R: a = b) by eauto using Map_TID_Facts.MapsTo_fun;
      inversion R; subst; clear R
      end.
      assert (List.In f (f0::l0)) by auto using List.in_cons.
      eauto 4 using open_def, Map_TID.add_1.
    - inversion H; subst; clear H.
      match goal with
      H1: Map_TID.MapsTo y ?a _, H2: Map_TID.MapsTo y ?b _ |- _ =>
      assert(R: b = a) by eauto using Map_TID_Facts.MapsTo_fun;
      inversion R; subst; clear R
      end.
      auto.
    - destruct (TID.eq_dec u y); subst; try (right; auto using open_add_neq; fail).
      assert (Map_TID.In y s) by eauto using open_to_in.
      contradiction.
    - destruct (TID.eq_dec u y); subst; try (right; auto using open_add_neq; fail).
      assert (Map_TID.In y s) by eauto using open_to_in.
      contradiction.
    - inversion H; subst; clear H.
      match goal with
      H1: Map_TID.MapsTo y ?a _, H2: Map_TID.MapsTo y ?b _ |- _ =>
      assert(R: b = a) by eauto using Map_TID_Facts.MapsTo_fun;
      inversion R; subst; clear R
      end.
      match goal with H: List.In _ _ |- _ => inversion H end.
    - right.
      inversion H; subst; clear H.
      eapply open_def; eauto using Map_TID.remove_2.
  Qed.
  Lemma bind_or_open_reduces:
    forall y f s o s' x,
    Bind y f s \/ Open y f s ->
    Reduces s (x, o) s' ->
    (Bind y f s /\ y = x /\ exists g, o = INIT g) \/
    (Bind y f s /\ y = x /\ o = END_TASK) \/
    (Open y f s /\ y = x /\ o = END_FINISH) \/
    Bind y f s' \/
    Open y f s'.
  Proof.
    intros.
    destruct H.
    - edestruct bind_reduces as [(?,?)|[Hx|Hy]]; eauto.
    - edestruct open_reduces; eauto.
  Qed.

  Lemma bind_make_1:
    forall x f s,
    Bind x f (Map_TID.add x (make f) s).
  Proof.
    intros.
    apply bind_def with (l:=nil); unfold make; simpl.
    auto using Map_TID.add_1.
  Qed.

  Lemma reduces_inv_ief_bind:
    forall f x y s s',
    IEF x f s ->
    Reduces s (x, BEGIN_TASK y) s' ->
    Bind y f s'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    assert (ief ft = f) by eauto using ief_inv_1.
    subst.
    auto using bind_make_1.
  Qed.

  Lemma not_open_empty:
    forall x f,
    ~ Open f x empty.
  Proof.
    unfold not, empty; intros.
    inversion H; subst; clear H.
    rewrite Map_TID_Facts.empty_mapsto_iff in *.
    contradiction.
  Qed.

  Lemma not_in_empty:
    forall x,
    ~ In x empty.
  Proof.
    intros.
    unfold not; intros N.
    inversion N; subst; clear N. {
      apply not_bind_empty in H.
      contradiction.
    }
    apply not_open_empty in H.
    contradiction.
  Qed.
End Props.

Module Trace.
  Definition t := (list (tid * op)) % type.

  Inductive ReducesN: state -> t -> Prop :=
  | reduces_n_nil:
    ReducesN empty nil
  | reduces_n_cons:
    forall t l o s s',
    ReducesN s l ->
    Reduces s (t, o) s' ->
    ReducesN s' ((t,o)::l).

  Section Props.
    Theorem reduces_n_to_dag:
      forall l s,
      ReducesN s l ->
      DAG (FEdge s).
    Proof.
      induction l; intros; inversion H; subst; clear H.
      - unfold DAG, not; intros.
        apply Graph.reaches_to_in_fst in H.
        destruct H as (?,(?,?)).
        inversion H; subst; clear H.
        apply not_bind_empty in H1; auto.
      - assert (DAG (FEdge s0)) by auto.
        eauto using dag_reduces.
    Qed.

    Corollary progress_ex:
      forall s l,
      (* Given that a finish-state is a DAG *)
      ReducesN s l ->
      (* And that state is not empty *)
      ~ Map_TID.Empty s ->
      (* Then there is some [f] such that *)
      exists f,
      ((* [f] is nonempty and every task in [f] reduces. *)
        Nonempty f s
        /\
        (forall t, Bind t f s -> Enabled s t)
        /\
        (forall x, Bind x f s -> IEF x f s)
      )
      \/
      ((* Or [f] is empty, and [t]'s current finish-scope is [f] *)
        Empty f s
        /\
        exists t, Current t f s /\ Enabled s t
      ).
    Proof.
      intros.
      edestruct progress as (f, [Hx|Hx]); eauto using reduces_n_to_dag.
    Qed.

    Corollary progress:
      forall s l,
      (* Given that a finish-state is a DAG *)
      ReducesN s l ->
      (* And that state is not empty *)
      ~ Map_TID.Empty s ->
      (* Then there is some [f] such that *)
      exists t,
      Enabled s t.
    Proof.
      intros.
      edestruct progress as (f, [([],(?,?))|(Hx,(t,(?,?)))]);
        eauto using reduces_n_to_dag.
    Qed.
  End Props.
End Trace.

