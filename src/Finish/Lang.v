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
  | INIT: fid -> op
  | BEGIN_FINISH: fid -> op
  | END_FINISH: fid -> op
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

  Inductive IEF x f s: Prop :=
  | ief_nil:
    Map_TID.MapsTo x {| root := f; started := nil |} s ->
    IEF x f s
  | ief_cons:
    forall g l,
    Map_TID.MapsTo x {| root := g; started := f::l |} s ->
    IEF x f s.

  Definition get_ief x s :=
  match Map_TID.find x s with
  | Some ft => Some (ief ft)
  | None => None
  end.

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
    (forall x, ~ Root x f s) ->
    Empty f s.

  Inductive Reduces : state -> action -> state -> Prop :=
  | reduces_init:
    forall s t f,
    ~ In f s ->
    ~ Map_TID.In t s ->
    Reduces s (t, INIT f) (Map_TID.add t (make f) s)
  | reduces_begin_finish:
    forall t f s l g,
    ~ In f s ->
    Map_TID.MapsTo t {| root := g; started := l |} s ->
    Reduces s (t, BEGIN_FINISH f) (
      Map_TID.add t {| root := g; started := f::l |} s)
  | reduces_end_finish:
    forall s t f l g,
    Map_TID.MapsTo t {| root := g; started := (f::l) % list |} s ->
    Empty f s ->
    Reduces s (t, END_FINISH f) (Map_TID.add t {| root := g; started := l |} s)
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
    Valid s t (INIT f)
  | valid_begin_finish:
    forall t f,
    Map_TID.In t s ->
    ~ In f s ->
    Valid s t (BEGIN_FINISH f)
  | valid_end_finish:
    forall t f g l,
    Map_TID.MapsTo t {| root := g; started := (f::l) % list |} s ->
    Valid s t (END_FINISH f)
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

  Inductive Blocking: op -> Prop :=
  | blocking_def:
    forall f,
    Blocking (END_FINISH f).

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
    Root x f s ->
    Nonempty f s.

  Lemma nonempty_to_in:
    forall f s,
    Nonempty f s ->
    In f s.
  Proof.
    intros.
    inversion H.
    eauto using in_root.
  Qed.

  Let has_root t f s :=
  match Map_TID.find t s with
  | Some ft => if FID.eq_dec f (root ft) then true else false
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
      remember {| root := _; started := _ |} as ft';
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

    Let maps_to_to_ief:
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
    destruct (blocking_dec o). {
      inversion b; subst; clear b.
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

  Tactic Notation "expect" uconstr(X) constr(f) :=
  (match goal with
  [ H: X |- _ ] => f H
  end).

  Let root_to_ief:
    forall x f s,
    (forall f, ~ Current x f s) ->
    Root x f s ->
    IEF x f s.
  Proof.
    intros.
    match goal with [H: Root x _ _ |- _ ] => inversion H; subst; clear H end.
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
      (forall x, Root x f s -> Enabled s x)
      /\
      (forall x, Root x f s -> IEF x f s)
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
      assert (Hr: Root y g s) by eauto using root_def.
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
        assert (g0 = g) by eauto using root_fun, root_def; subst.
        assert (Xc: Current x f s) by eauto using current_def.
        contradict Xc.
        eauto using Map_TID_Extra.mapsto_to_in.
      }
      eauto using progress_nonblocking.
    }
    destruct (empty_nonempty_dec f s). {
      exists f.
      left; split; auto.
      split. {
        intros.
        destruct (blocking_dec o). {
          inversion b; subst; clear b.
          subst.
          match goal with H: Valid _ _ _ |- _ => inversion H; subst; clear H end.
          assert (g = f) by eauto using root_fun, root_def; subst.
          assert (X: ~ Current x f0 s) by eauto using Map_TID_Extra.mapsto_to_in.
          contradict X; eauto using current_def.
        }
        eauto using progress_nonblocking.
      }
      eauto using root_to_ief.
    }
    exists f.
    right;
    split; eauto using progress_empty.
  Qed.
End Defs.

Module Task.

  Inductive Root: fid -> task -> Prop :=
  | root_def:
    forall f l,
    Root f {| root := f; started := l |}.

  Inductive Started: fid -> task -> Prop :=
  | started_def:
    forall f g l,
    List.In f l ->
    Started f {| root := g; started := l |}.

  Inductive In: fid -> task -> Prop :=
  | in_root:
    forall f ft,
    Root f ft ->
    In f ft
  | in_started:
    forall f ft,
    Started f ft ->
    In f ft.
End Task.

Section Props.

  Lemma root_inv_add:
    forall x y ft s f,
    Root y f (Map_TID.add x ft s) ->
    (x = y /\ Task.Root f ft) \/ Root y f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_TID_Facts.add_mapsto_iff in H0.
    destruct H0 as [(?,?)|(?,?)].
    + subst.
      auto using Task.root_def.
    + eauto using root_def, in_root.
  Qed.

  Lemma in_inv_add:
    forall f x ft s,
    In f (Map_TID.add x ft s) ->
    Task.In f ft \/ In f s.
  Proof.
    intros.
    inversion H.
    - apply root_inv_add in H0.
      destruct H0 as [(?, ?)|?].
      + auto using Task.in_root.
      + eauto using in_root.
    - apply started_inv_add in H0.
      destruct H0 as [(?,?)|(?,?)]. {
        destruct ft in *; simpl in *.
        auto using Task.in_started, Task.started_def.
      }
      eauto using in_started.
  Qed.

  Let task_root_to_root:
    forall x ft s f,
    Map_TID.MapsTo x ft s ->
    Task.Root f ft ->
    Root x f s.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eauto using root_def.
  Qed.

  Let task_started_to_started:
    forall x ft s f,
    Map_TID.MapsTo x ft s ->
    Task.Started f ft ->
    Started x f s.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eauto using started_def.
  Qed.

  Let task_in_to_in:
    forall x ft s f,
    Task.In f ft ->
    Map_TID.MapsTo x ft s ->
    In f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    + eauto using task_root_to_root, in_root.
    + eauto using task_started_to_started, in_started.
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

  Let task_root_inv_eq:
    forall f g l,
    Task.Root f {| root := g; started := l |} ->
    g = f.
  Proof.
    intros.
    inversion H; auto.
  Qed.

  Let task_root_cons:
    forall f g l h,
    Task.Root f {| root := g; started := l |} ->
    Task.Root f {| root := g; started := h::l |}.
  Proof.
    intros.
    inversion H; subst; clear H.
    auto using Task.root_def.
  Qed.

  Let task_started_cons:
    forall f g l h,
    Task.Started f {| root := g; started := l |} ->
    Task.Started f {| root := g; started := h::l |}.
  Proof.
    intros.
    inversion H; subst; clear H.
    auto using Task.started_def, List.in_cons.
  Qed.

  Let task_in_cons:
    forall f g l h,
    Task.In f {| root := g; started := l |} ->
    Task.In f {| root := g; started := h::l |}.
  Proof.
    intros.
    inversion H; subst; clear H. {
      auto using task_root_cons, Task.in_root.
    }
    auto using task_started_cons, Task.in_started.
  Qed.

  Let in_ief:
    forall x ft s,
    Map_TID.MapsTo x ft s ->
    In (ief ft) s.
  Proof.
    intros.
    destruct ft as (f, [|g]); simpl.
    + eauto using in_root, root_def.
    + eauto using in_started, in_eq, started_def.
  Qed.

  Let root_inv_remove:
    forall x f s y,
    Root y f (Map_TID.remove x s) ->
    x <> y /\ Root y f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_TID_Facts.remove_mapsto_iff in H0.
    destruct H0 as (?, ?).
    eauto using root_def.
  Qed.

  Let started_inv_remove:
    forall x f s y,
    Started y f (Map_TID.remove x s) ->
    x <> y /\ Started y f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply Map_TID_Facts.remove_mapsto_iff in H1.
    destruct H1 as (?, ?).
    eauto using started_def.
  Qed.

  Let in_inv_remove:
    forall x s f,
    In f (Map_TID.remove x s) ->
    In f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    - apply root_inv_remove in H0.
      destruct H0.
      eauto using in_root.
    - apply started_inv_remove in H0.
      destruct H0.
      eauto using in_started.
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
        eauto using in_root, root_def.
      + match goal with H: Task.Started _ _ |- _ =>
          inversion H; subst; clear H
        end.
        match goal with H: List.In _ _ |- _ =>
          inversion H; subst; clear H
        end.
        * auto.
        * eauto using started_def, in_started.
    - eauto using task_in_to_in, task_in_cons.
    - match goal with H: Task.In _ (make _) |- _ =>
        apply task_in_inv_eq_make in H
      end; subst.
      eauto using in_ief.
    - eauto using in_inv_remove.
  Qed.

  Let root_add_neq:
    forall y f s x ft,
    Root y f s ->
    x <> y ->
    Root y f (Map_TID.add x ft s).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using root_def, Map_TID.add_2.
  Qed.

  Lemma root_reduces:
    forall x y f s s' o,
    Root y f s ->
    Reduces s (x, o) s' ->
    (y = x /\ exists g, o = INIT g) \/
    (y = x /\ o = END_TASK) \/
    Root y f s'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - destruct (TID.eq_dec x y); subst. {
        eauto 4.
      }
      eauto using root_add_neq.
    - destruct (TID.eq_dec x y); subst. {
        assert (Root y g s) by eauto using root_def.
        assert (f = g) by eauto using root_fun.
        subst.
        eauto using root_def, Map_TID.add_1.
      }
      eauto using root_add_neq.
    - destruct (TID.eq_dec x y); subst. {
        assert (Root y g s) by eauto using root_def.
        assert (f = g) by eauto using root_fun.
        subst.
        eauto using root_def, Map_TID.add_1.
      }
      eauto using root_add_neq.
    - destruct (TID.eq_dec y u); subst. {
        apply root_to_in in H.
        contradiction.
      }
      eauto using root_add_neq.
    - destruct (TID.eq_dec y x); subst. {
        auto.
      }
      assert (Root x f0 s) by eauto using root_def.
      right.
      right.
      inversion H; subst; clear H.
      eapply root_def; eauto using Map_TID.remove_2.
  Qed.

  Let started_add_neq:
    forall y f s x ft,
    Started y f s ->
    x <> y ->
    Started y f (Map_TID.add x ft s).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using started_def, Map_TID.add_2.
  Qed.

  Lemma started_to_in:
    forall x f s,
    Started x f s ->
    Map_TID.In x s.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Lemma started_reduces:
    forall x y f s s' o,
    Started y f s ->
    Reduces s (x, o) s' ->
    (y = x /\ o = END_FINISH f) \/
    Started y f s'.
  Proof.
    intros.
    inversion H0; subst; clear H0;
    destruct (TID.eq_dec x y); subst; try (right; auto using started_add_neq; fail).
    - apply started_to_in in H.
      contradiction.
    - inversion H; subst; clear H.
      match goal with
      H1: Map_TID.MapsTo y ?a _, H2: Map_TID.MapsTo y ?b _ |- _ =>
      assert(R: a = b) by eauto using Map_TID_Facts.MapsTo_fun;
      inversion R; subst; clear R
      end.
      assert (List.In f (f0::l0)) by auto using List.in_cons.
      eauto 4 using started_def, Map_TID.add_1.
    - inversion H; subst; clear H.
      match goal with
      H1: Map_TID.MapsTo y ?a _, H2: Map_TID.MapsTo y ?b _ |- _ =>
      assert(R: b = a) by eauto using Map_TID_Facts.MapsTo_fun;
      inversion R; subst; clear R
      end.
      match goal with H: List.In _ _ |- _ =>
        inversion H; subst; clear H
      end; auto.
      eauto 4 using started_def, Map_TID.add_1.
    - destruct (TID.eq_dec u y); subst; try (right; auto using started_add_neq; fail).
      assert (Map_TID.In y s) by eauto using started_to_in.
      contradiction.
    - destruct (TID.eq_dec u y); subst; try (right; auto using started_add_neq; fail).
      assert (Map_TID.In y s) by eauto using started_to_in.
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
      eapply started_def; eauto using Map_TID.remove_2.
  Qed.
  Lemma root_or_started_reduces:
    forall y f s o s' x,
    Root y f s \/ Started y f s ->
    Reduces s (x, o) s' ->
    (Root y f s /\ y = x /\ exists g, o = INIT g) \/
    (Root y f s /\ y = x /\ o = END_TASK) \/
    (Started y f s /\ y = x /\ o = END_FINISH f) \/
    Root y f s' \/
    Started y f s'.
  Proof.
    intros.
    destruct H.
    - edestruct root_reduces as [(?,?)|[Hx|Hy]]; eauto.
    - edestruct started_reduces; eauto.
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
        (forall t, Root t f s -> Enabled s t)
        /\
        (forall x, Root x f s -> IEF x f s)
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
