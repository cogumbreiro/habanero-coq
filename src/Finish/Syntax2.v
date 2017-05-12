(*
State: (task -> (finisih * finishes)) * (finish -> tasks)
t0, init f0
t0, finish f1;
t0, async t1;
t1, end f1;
t0, finish f2;
t0, async t2;
t2, async t3;
t2, end f2;
t3, end f2;
t0, await f3;
t0, finish f3
t0, async t4
t4, end f3
t0, await f3
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
  | FINISH
  | AWAIT
  | ASYNC: tid -> op
  | END: op.

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
  | reduces_finish:
    forall t f s l g,
    ~ In f s ->
    Map_TID.MapsTo t {| root := g; started := l |} s ->
    Reduces s (t, FINISH) (
      Map_TID.add t {| root := g; started := f::l |} s)
  | reduces_await:
    forall s t f l g,
    Map_TID.MapsTo t {| root := g; started := (f::l) % list |} s ->
    Empty f s ->
    Reduces s (t, AWAIT) (Map_TID.add t {| root := g; started := l |} s)
  | reduces_async:
    forall s t u ft,
    ~ Map_TID.In u s ->
    Map_TID.MapsTo t ft s ->
    Reduces s (t, ASYNC u) (Map_TID.add u (make (ief ft)) s)
  | reduces_end:
    forall t f s ,
    Map_TID.MapsTo t {| root := f; started := nil |} s ->
    Reduces s (t, END) (Map_TID.remove t s).

  Inductive Typecheck s : action -> Prop :=
  | typecheck_init:
    forall f t,
    ~ In f s ->
    ~ Map_TID.In t s ->
    Typecheck s (t, INIT)
  | typecheck_finish:
    forall t f,
    Map_TID.In t s ->
    ~ In f s ->
    Typecheck s (t, FINISH)
  | typecheck_await:
    forall t f g l,
    Map_TID.MapsTo t {| root := g; started := (f::l) % list |} s ->
    Typecheck s (t, AWAIT)
  | typecheck_async:
    forall t u,
    ~ Map_TID.In u s ->
    Map_TID.In t s ->
    Typecheck s (t, ASYNC u)
  | typecheck_end:
    forall t f,
    Map_TID.MapsTo t {| root := f; started := nil |} s ->
    Typecheck s (t, END).

  Inductive FEdge s : (fid * fid) -> Prop :=
  | f_edge_def:
    forall f g t,
    Root t f s ->
    Started t g s ->
    FEdge s (f, g).

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

  Definition task_edges (ft:task) :=
    List.map (fun f => (root ft, f)) (started ft).

  Definition f_edges (s:state) : list (fid * fid) := 
    List.flat_map task_edges (Map_TID_Extra.values s).

  Lemma root_eq:
    forall t ft s,
    Map_TID.MapsTo t ft s ->
    Root t (root ft) s.
  Proof.
    intros.
    destruct ft; simpl in *.
    eauto using root_def.
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

  Let f_edge_inv_add_finish:
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

  Let f_edges_rw_add_finish_1:
    forall t g f l s p,
    Edge (f_edges (Map_TID.add t {| root := g; started := f :: l |} s)) p ->
    Map_TID.MapsTo t {| root := g; started := l |} s ->
    Edge ((g,f)::(f_edges s)) p.
  Proof.
    unfold Edge; intros.
    apply in_to_f_edge in H.
    destruct p as (x, y).
    apply f_edge_inv_add_finish in H; auto.
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

  Lemma f_edge_async:
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

  Lemma f_edge_end:
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
      eauto using f_edge_async, f_edge_finished.
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
      eauto using f_edge_async, f_edge_finished.
    - apply dag_f_edge_to_fgraph_edge, dag_impl with (E:=FEdge s);
      eauto using f_edge_async.
    - apply dag_f_edge_to_fgraph_edge, dag_impl with (E:=FEdge s);
      eauto using f_edge_async, f_edge_finished, f_edge_end.
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

  Let dag_cond:
    forall s, 
    DAG (Edge (f_edges s)) ->
    (forall x, Map_TID.In x s -> forall f, ~ Started x f s) \/
    (exists t f, Started t f s /\ forall u, Root u f s -> forall g, ~ Started u g s).
  Proof.
    intros.
    remember (f_edges s).
    destruct l. {
      left; intros.
      apply Map_TID_Extra.in_to_mapsto in H0.
      destruct H0 as (ft, mt).
      destruct ft as (g, l).
      destruct l. {
        eauto using started_nil_to_not_started.
      }
      assert (He: FEdge s (g, f0)) by eauto using List.in_eq, started_def, f_edge_def, root_def.
      apply f_edge_to_edge in He.
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
    apply edge_to_f_edge in He.
    inversion He; subst; clear He.
    exists t; exists b; split; auto.
    unfold not; intros.
    assert (He : FEdge s (b, g)) by eauto using f_edge_def.
    match goal with H: FEdge _ _ |- _ =>
      apply f_edge_to_edge in H;
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
    Typecheck s (t, o) ->
    o <> AWAIT ->
    exists s', Reduces s (t, o) s'.
  Proof.
    intros.
    destruct o; try contradiction; inversion H; subst; clear H;
    eauto using reduces_init, reduces_end.
    - apply Map_TID_Extra.in_to_mapsto in H2.
      destruct H2 as (ft, mt).
      destruct ft as (g, l).
      eauto using reduces_finish.
    - apply Map_TID_Extra.in_to_mapsto in H4.
      destruct H4 as (ft, mt).
      exists (Map_TID.add t0 (make (ief ft)) s).
      eauto using reduces_async.
  Qed.

  Let await_or:
    forall o,
    o = AWAIT \/ o <> AWAIT.
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

  Theorem progress:
    forall s,
    (* Given that a finish-state is a DAG *)
    DAG (FEdge s) ->
    (* And that state is not empty *)
    ~ Map_TID.Empty s ->
    (* Then there is some f such that *)
    exists f,
    (Nonempty f s /\
      (forall u o, Typecheck s (u, o) -> exists s', Reduces s (u, o) s')
    )
    \/
    (exists t, Started t f s /\ Empty f s)
    \/
    (exists t, Started t f s /\ Nonempty f s /\
    (* Any task in f is able to execute a finish-operation. *)
    (forall u,
    Root u f s ->
    forall o,
    Typecheck s (u, o) ->
    exists s', Reduces s (u, o) s')).
  Proof.
    intros.
    apply Map_TID_Extra.nonempty_in in H0.
    apply dag_f_edge_to_fgraph_edge in H.
    apply dag_cond in H.
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
      intros u; intros.
      assert (X: o = AWAIT \/ o <> AWAIT) by eauto using await_or;
      destruct X. {
        subst.
        match goal with H: Typecheck _ _ |- _ => inversion H; subst; clear H end.
        assert (~ Started u f s) by eauto using Map_TID_Extra.mapsto_to_in.
        assert (Started u f s) by eauto using started_def, List.in_eq.
        contradiction.
      }
      eauto using progress_nonblocking.
    }
    destruct H as (t, (f, (Hs, Hr))).
    exists f.
    right.
    destruct (empty_nonempty_dec f s); eauto.
    right.
    exists t; try (repeat split; auto).
    intros u; intros.
    assert (X: o = AWAIT \/ o <> AWAIT) by eauto using await_or;
    destruct X. {
      subst.
      match goal with H: Typecheck _ _ |- _ => inversion H; subst; clear H
      end.
      assert (~ Started u f0 s) by eauto using Map_TID_Extra.mapsto_to_in.
      assert (Started u f0 s) by eauto using started_def, List.in_eq.
      contradiction.
    }
    eauto using progress_nonblocking.
  Qed.
End Defs.
