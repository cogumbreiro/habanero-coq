(*
State: (task -> (finisih * finishes)) * (finish -> tasks)
t0, init f0
t0, begin_finish f1;
t0, begin_task t1;
t1, end_task f1;
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
Require Import Vars.
Require Import Aniceto.Graphs.DAG.
Require Import Aniceto.List.
Require Import Aniceto.Graphs.FGraph.

Section Defs.

  Structure task := {
    root: fid;
    started: list fid;
  }.

  Definition make f := {| root := f; started := nil |}.

  Definition state := Map_TID.t task.

  Definition empty : state := Map_TID.empty task.

  Inductive op :=
  | INIT
  | BEGIN_FINISH
  | END_FINISH
  | BEGIN_TASK: tid -> op
  | END_TASK: op.

  Definition action := (tid * op) % type.

  Definition ief (ft:task) :=
  match ft with
  | {| root := f; started := nil |} => f
  | {| root := g; started := (f::l)%list |} =>  f
  end.

  Inductive Root : tid -> fid -> state -> Prop :=
  | root_def:
    forall t f l s,
    Map_TID.MapsTo t {| root := f; started := l |} s ->
    Root t f s.

  Inductive Started : tid -> fid -> state -> Prop :=
  | started_def:
    forall t f l s g,
    List.In f l ->
    Map_TID.MapsTo t {| root := g; started := l |} s ->
    Started t f s.

  Inductive Current : tid -> fid -> state -> Prop :=
  | current_def:
    forall t f l s g,
    Map_TID.MapsTo t {| root := g; started := (f::l) |} s ->
    Current t f s.

  Inductive In (f:fid) s : Prop :=
  | in_root:
    forall t,
    Root t f s ->
    In f s
  | in_started:
    forall t,
    Started t f s ->
    In f s.

  Inductive Empty f s : Prop :=
  | empty_def:
    (forall t, ~ Root t f s) ->
    Empty f s.

  Inductive Reduces : state -> action -> state -> Prop :=
  | reduces_init:
    forall s t f,
    ~ In f s ->
    ~ Map_TID.In t s ->
    Reduces s (t, INIT) (Map_TID.add t (make f) s)
  | reduces_begin_finish:
    forall t f s l g,
    ~ In f s ->
    Map_TID.MapsTo t {| root := g; started := l |} s ->
    Reduces s (t, BEGIN_FINISH) (
      Map_TID.add t {| root := g; started := f::l |} s)
  | reduces_end_finish:
    forall s t f l g,
    Map_TID.MapsTo t {| root := g; started := (f::l) % list |} s ->
    Empty f s ->
    Reduces s (t, END_FINISH) (Map_TID.add t {| root := g; started := l |} s)
  | reduces_begin_task:
    forall s t u ft,
    ~ Map_TID.In u s ->
    Map_TID.MapsTo t ft s ->
    Reduces s (t, BEGIN_TASK u) (Map_TID.add u (make (ief ft)) s)
  | reduces_end_task:
    forall t f s ,
    Map_TID.MapsTo t {| root := f; started := nil |} s ->
    Reduces s (t, END_TASK) (Map_TID.remove t s).

  Inductive Valid s : tid -> op -> Prop :=
  | valid_init:
    forall f t,
    ~ In f s ->
    ~ Map_TID.In t s ->
    Valid s t INIT
  | valid_begin_finish:
    forall t f,
    Map_TID.In t s ->
    ~ In f s ->
    Valid s t BEGIN_FINISH
  | valid_end_finish:
    forall t f g l,
    Map_TID.MapsTo t {| root := g; started := (f::l) % list |} s ->
    Valid s t END_FINISH
  | valid_begin_task:
    forall t u,
    ~ Map_TID.In u s ->
    Map_TID.In t s ->
    Valid s t (BEGIN_TASK u)
  | typecheck_end_task:
    forall t f,
    Map_TID.MapsTo t {| root := f; started := nil |} s ->
    Valid s t END_TASK.

  Inductive FEdge s : (fid * fid) -> Prop :=
  | f_edge_def:
    forall f g t,
    Root t f s ->
    Started t g s ->
    FEdge s (f, g).

  Inductive CEdge s : (fid * fid) -> Prop :=
  | c_edge_def:
    forall f g t,
    Root t f s ->
    Current t g s ->
    CEdge s (f, g).

  Let root_inv_add:
    forall u g t s ft,
    Root u g (Map_TID.add t ft s) ->
    (t = u /\ exists l, ft = {| root := g; started := l |}) \/ (t <> u /\ Root u g s).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_TID_Facts.add_mapsto_iff in H0.
    destruct H0 as [(?,?)|(?,?)]; eauto using root_def.
  Qed.

  Lemma root_inv_add_make:
    forall t u f g s,
    Root t f (Map_TID.add u (make g) s) ->
    (t = u /\ f = g) \/ 
    (Root t f s /\ u <> t).
  Proof.
    unfold make; intros.
    match goal with
    | H: Root _ _ _ |- _  =>  apply root_inv_add in H;
      destruct H as [(?,(l,R))|(?,i)]
    end. {
      simpl in *.
      inversion R; subst; clear R.
      auto.
    }
    auto.
  Qed.

  Definition current (ft:task) :=
  match ft with
  | {| root := f; started := nil |} => None
  | {| root := g; started := (f::l)%list |} =>  Some f
  end.

  Definition task_edges (ft:task) :=
  List.map (fun f => (root ft, f)) (started ft).

  Definition f_edges (s:state) : list (fid * fid) := 
  List.flat_map task_edges (Map_TID_Extra.values s).

  Definition c_edges (s:state) : list (fid * fid) := 
  let c_edge (ft:task) :=
  match current ft with
  | Some g => Some (root ft, g)
  | None => None
  end in
  List.omap c_edge (Map_TID_Extra.values s).

  Lemma root_eq:
    forall t ft s,
    Map_TID.MapsTo t ft s ->
    Root t (root ft) s.
  Proof.
    intros.
    destruct ft; simpl in *.
    eauto using root_def.
  Qed.

  Lemma in_to_root:
    forall t s,
    Map_TID.In t s ->
    exists f, Root t f s.
  Proof.
    intros.
    apply Map_TID_Extra.in_to_mapsto in H.
    destruct H as (ft, mt).
    eauto using root_eq.
  Qed.

  Lemma not_root_empty:
    forall t f,
    ~ Root t f empty.
  Proof.
    unfold not, empty; intros ? ? N.
    inversion N; subst; clear N.
    apply Map_TID_Facts.empty_mapsto_iff in H; auto.
  Qed.

  Lemma started_eq:
    forall f t ft s,
    Map_TID.MapsTo t ft s ->
    List.In f (started ft) ->
    Started t f s.
  Proof.
    intros.
    destruct ft.
    simpl in *.
    eauto using started_def.
  Qed.

  Lemma f_edge_eq:
    forall t f ft s,
    Map_TID.MapsTo t ft s ->
    List.In f (started ft) ->
    FEdge s (root ft, f).
  Proof.
    eauto using f_edge_def, root_eq, started_eq.
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
    exists {| root := f; started := l |}.
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
    destruct started0. {
      inversion Hj.
    }
    inversion Hj; subst; clear Hj.
    eauto using root_def, current_def, c_edge_def.
  Qed.

  Lemma started_inv_add:
    forall t g s u ft,
    Started t g (Map_TID.add u ft s) ->
    (u = t /\ List.In g (started ft)) \/ (u <> t /\ Started t g s).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_TID_Facts.add_mapsto_iff in H1.
    destruct H1 as [(?,?)|(?,?)]. {
      subst; auto.
    }
    eauto using started_def.
  Qed.

  Lemma started_inv_add_make:
    forall t g f s u,
    Started t g (Map_TID.add u (make f) s) ->
    u <> t /\ Started t g s.
  Proof.
    unfold make; intros.
    apply started_inv_add in H.
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
    | H: Started _ _ _ |- _ =>
      apply started_inv_add_make in H;
      destruct H as (?, Hs)
    end.
    assert (g <> f). {
      unfold not; intros; subst.
      match goal with
      | H: ~ In _ _ |- _ => contradict H
      end.
      eauto using in_started.
    }
    match goal with
    | H: Root _ _ _ |- _ =>
      apply root_inv_add_make in H; auto;
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
    FEdge (Map_TID.add t {| root := g; started := f :: l |} s) (x, y) ->
    Map_TID.MapsTo t {| root := g; started := l |} s ->
    (g = x /\ f = y) \/ FEdge s (x, y).
  Proof.
    intros.
    match goal with
    H: FEdge _ _ |- _ => inversion H; subst; clear H
    end.
    match goal with H: Started _ _ _ |- _ => apply started_inv_add in H;
      rename H into Hs
    end.
    match goal with
    H: Root _ _ _ |- _ => apply root_inv_add in H;
    destruct H as [(?,(k,R))|(?,?)]
    end. {
      inversion R; clear R.
      destruct Hs as [(?,Hi)|(?,?)]. {
        simpl in *.
        destruct Hi. {
          auto.
        }
        subst.
        eauto using root_def, started_def, f_edge_def.
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
    Edge (f_edges (Map_TID.add t {| root := g; started := f :: l |} s)) p ->
    Map_TID.MapsTo t {| root := g; started := l |} s ->
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
    eauto using in_root.
  Qed.

  Lemma f_edge_snd_to_in:
    forall s f g,
    FEdge s (f, g) ->
    In g s.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using in_started.
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

  Lemma started_inv_add_eq:
    forall t g f l s,
    Started t g (Map_TID.add t {| root := f; started := l |} s) ->
    List.In g l.
  Proof.
    intros.
    apply started_inv_add in H.
    destruct H as [(?,?)|(N,_)]; try contradiction.
    auto.
  Qed.

  Lemma started_inv_add_neq:
    forall t g f l s u,
    Started t g (Map_TID.add u {| root := f; started := l |} s) ->
    t <> u ->
    Started t g s.
  Proof.
    intros.
    apply started_inv_add in H.
    destruct H as [(?,?)|(N,?)]; subst; try contradiction.
    auto.
  Qed.

  Lemma f_edge_finished:
    forall t g l s f p,
    FEdge (Map_TID.add t {| root := g; started := l |} s) p ->
    Map_TID.MapsTo t {| root := g; started := f :: l |} s ->
    Empty f s  ->
    FEdge s p.
  Proof.
    intros.
    inversion H; subst; clear H.
    match goal with
      H2: Root _ _ _ |- _ =>
      apply root_inv_add in H2;
      destruct H2 as [(?, (?, R))|(?,?)]
    end. {
      inversion R; subst; clear R.
      match goal with H: Started _ _ _ |- _ => apply started_inv_add_eq in H end.
      eauto using f_edge_def, root_def, in_cons, started_def.
    }
    match goal with H: Started _ _ _ |- _ => apply started_inv_add_neq in H;auto end.
    eauto using f_edge_def.
  Qed.

  Lemma f_edge_begin_task:
    forall u ft s p,
    FEdge (Map_TID.add u (make (ief ft)) s) p ->
    FEdge s p.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply root_inv_add_make in H0.
    destruct H0 as [(?,?)|(?,Hr)]. {
      subst.
      apply started_inv_add_make in H1.
      destruct H1 as (N,_); contradiction.
    }
    apply started_inv_add_make in H1.
    destruct H1; eauto using f_edge_def.
  Qed.

  Lemma root_inv_remove:
    forall t f u s,
    Root t f (Map_TID.remove u s) ->
    u <> t /\ Root t f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_TID_Facts.remove_mapsto_iff in H0.
    destruct H0.
    eauto using root_def.
  Qed.

  Lemma started_inv_remove:
    forall t f u s,
    Started t f (Map_TID.remove u s) ->
    u <> t /\ Started t f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_TID_Facts.remove_mapsto_iff in H1.
    destruct H1.
    eauto using started_def.
  Qed.

  Lemma f_edge_end_task:
    forall t s p f,
    FEdge (Map_TID.remove t s) p ->
    Map_TID.MapsTo t {| root := f; started := [] |} s ->
    FEdge s p.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply root_inv_remove in H1.
    destruct H1 as (?,Hr).
    apply started_inv_remove in H2.
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
          eauto using root_def, in_root.
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

  Lemma started_nil_to_not_started:
    forall x g s,
    Map_TID.MapsTo x {| root := g; started := [] |} s ->
    forall f, ~ Started x f s.
  Proof.
    unfold not; intros.
    inversion H0; subst; clear H0.
    eapply Map_TID_Facts.MapsTo_fun in H; eauto.
    inversion H; subst; clear H.
    contradiction.
  Qed.

  Lemma started_nil_to_not_current:
    forall x g s,
    Map_TID.MapsTo x {| root := g; started := [] |} s ->
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
    (exists t f, Current t f s /\ forall u, Root u f s -> forall g, ~ Current u g s).
  Proof.
    intros.
    remember (c_edges s).
    destruct l. {
      left; intros.
      apply Map_TID_Extra.in_to_mapsto in H0.
      destruct H0 as (ft, mt).
      destruct ft as (g, l).
      destruct l. {
        eauto using started_nil_to_not_current.
      }
      assert (He: CEdge s (g, f0)) by eauto using List.in_eq, current_def, c_edge_def, root_def.
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

  Lemma progress_nonblocking:
    forall s t o,
    Valid s t o ->
    o <> END_FINISH ->
    exists s', Reduces s (t, o) s'.
  Proof.
    intros.
    destruct o; try contradiction; inversion H; subst; clear H;
    eauto using reduces_init, reduces_end_task;
    match goal with [ H: Map_TID.In _ _ |- _ ] =>
      apply Map_TID_Extra.in_to_mapsto in H;
      destruct H as ((?,?), mt) end.
    - eauto using reduces_begin_finish.
    - eauto using reduces_begin_task.
  Qed.

  Lemma end_finish_or:
    forall o,
    o = END_FINISH \/ o <> END_FINISH.
  Proof.
    intros.
    destruct o; auto;
    right; unfold not; intros N; inversion N.
  Qed.

  Inductive Nonempty (f:fid) (s:state) : Prop :=
  | nonempty_def:
    forall t,
    Root t f s ->
    Nonempty f s.

  Let has_root t f s :=
  match Map_TID.find t s with
  | Some ft => if FID.eq_dec f (root ft) then true else false
  | _ => false
  end.

  Lemma root_to_in:
    forall t f s,
    Root t f s ->
    Map_TID.In t s.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Lemma root_fun:
    forall t f s g,
    Root t f s ->
    Root t g s ->
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

  Lemma root_dec t f s:
    { Root t f s } + { ~ Root t f s }.
  Proof.
    remember (has_root t f s).
    symmetry in Heqb;
    unfold has_root in *.
    destruct b. {
      left.
      destruct (Map_TID_Extra.find_rw t s) as [(R,?)|((g,l),(R,?))];
      rewrite R in *.
      - inversion Heqb.
      - simpl in *.
        destruct (FID.eq_dec f g). {
          subst.
          eauto using root_def.
        }
        inversion Heqb.
    }
    right.
    destruct (Map_TID_Extra.find_rw t s) as [(R,?)|((g,l),(R,?))];
    rewrite R in *. {
      unfold not; intros N.
      apply root_to_in in N.
      contradiction.
    }
    simpl in *.
    destruct (FID.eq_dec f g). {
      inversion Heqb.
    }
    unfold not; intros N.
    assert (Root t g s) by eauto using root_def.
    assert (f = g)  by eauto using root_fun.
    contradiction.
  Defined.

  Let filter_root f s :=
  Map_TID_Extra.filter (fun t ft => if FID.eq_dec f (root ft) then true else false) s.

  Lemma empty_nonempty_dec f s:
    { Nonempty f s } + { Empty f s }.
  Proof.
    destruct (Map_TID_Extra.any_in_dec (filter_root f s)) as [(t,Hi)|X];
    unfold filter_root in *. {
      left.
      apply Map_TID_Extra.in_to_mapsto in Hi.
      destruct Hi as (ft, mt).
      apply Map_TID_Extra.filter_spec in mt; auto using tid_eq_rw.
      destruct mt as (mt, Hx).
      destruct (FID.eq_dec f (root ft)). {
        subst.
        eauto using nonempty_def, root_eq.
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

  Let current_to_started:
    forall t f s,
    Current t f s ->
    Started t f s.
  Proof.
    intros.
    inversion H; subst.
    eauto using started_def, List.in_eq.
  Qed.

  Let c_edge_to_f_edge:
    forall s e,
    CEdge s e ->
    FEdge s e.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using f_edge_def, current_to_started.
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
    apply Map_TID_Facts.MapsTo_fun with (e:={| root := g1; started := g :: l0 |}) in H1; auto.
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
    destruct (end_finish_or o). {
      subst.
      inversion H1; subst.
      assert (f0 = f). {
        assert (Current t f0 s) by eauto using current_def.
        eauto using current_fun.
      }
      subst.
      exists ((Map_TID.add t {| root := g; started := l |} s)).
      eapply reduces_end_finish; eauto.
    }
    auto using progress_nonblocking.
  Qed.

  (** An enabled task can reduce with any operation. *)
  Definition Enabled s t :=
  forall o, Valid s t o -> exists s', Reduces s (t, o) s'.

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
      (forall t, Root t f s -> Enabled s t)
    )
    \/
    ((* Or [f] is empty, and [t]'s current finish-scope is [f] *)
      Empty f s
      /\
      exists t, Current t f s /\ Enabled s t
    ).
  Proof.
    intros.
    unfold Enabled.
    apply Map_TID_Extra.nonempty_in in H0.
    apply dag_f_edge_to_c_edge,
          dag_c_edge_to_fgraph_edge,
          dag_cond in H.
    destruct H as [H|H]. {
      destruct H0 as (t, Hi).
      apply Map_TID_Extra.in_to_mapsto in Hi.
      destruct Hi as ((g,l), mt).
      assert (Hr: Root t g s) by eauto using root_def.
      exists g.
      left.
      split. {
        eauto using nonempty_def.
      }
      intros.
      assert (X: o = END_FINISH \/ o <> END_FINISH) by eauto using end_finish_or;
      destruct X. {
        subst.
        match goal with H: Valid _ _ _ |- _ => inversion H; subst; clear H end.
        assert (g0 = g) by eauto using root_fun, root_def; subst.
        assert (~ Current t0 f s) by eauto using Map_TID_Extra.mapsto_to_in.
        assert (Current t0 f s) by eauto using current_def.
        contradiction.
      }
      eauto using progress_nonblocking.
    }
    destruct H as (t, (f, (Hs, Hr))).
    destruct (empty_nonempty_dec f s). {
      exists f.
      left; split; auto.
      intros.
      assert (X: o = END_FINISH \/ o <> END_FINISH) by eauto using end_finish_or;
      destruct X. {
        subst.
        match goal with H: Valid _ _ _ |- _ => inversion H; subst; clear H end.
        assert (g = f) by eauto using root_fun, root_def; subst.
        assert (~ Current t0 f0 s) by eauto using Map_TID_Extra.mapsto_to_in.
        assert (Current t0 f0 s) by eauto using current_def.
        contradiction.
      }
      eauto using progress_nonblocking.
    }
    exists f.
    right;
    split; eauto using progress_empty.
  Qed.

End Defs.


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
        apply not_root_empty in H1; auto.
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
        forall t, Root t f s -> Enabled s t
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
      edestruct progress as (f, [([],?)|(Hx,(t,(?,?)))]);
        eauto using reduces_n_to_dag.
    Qed.
  End Props.
End Trace.
