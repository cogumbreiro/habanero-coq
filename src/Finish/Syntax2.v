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

Section Defs.

  Structure task := {
    root: fid;
    started: list fid;
  }.

  Definition make f := {| root := f; started := nil |}.

  Definition state := Map_TID.t task.

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

(*  Forall 

  Inductive Pending f l s : Prop :=
  | pending_def:
    (forall t, List.In t l -> Root t f s) ->
    (*forall t, Root t f s -> List.In t l) ->*)
    Pending f l s.
*)
  Inductive Leaf t s: Prop :=
  | leaf_def:
    forall f,
    Map_TID.MapsTo t {| root := f; started := nil |} s ->
    Leaf t s.

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

  Inductive Finished f (s:state) : Prop :=
  | finished_def:
    forall t,
    Started t f s ->
    Empty f s ->
    Finished f s.

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
    Finished f s ->
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

  Inductive Nonempty : fid -> state -> Prop :=
  | nonempty_def:
    forall t f s,
    Root t f s ->
    Nonempty f s.

  Inductive Enabled: tid -> state -> Prop :=
  | enabled_ready:
    forall f s t,
    Map_TID.MapsTo t {| root := f; started := nil |} s ->
    Enabled t s
  | enabled_leaf:
    forall f g l s t,
    Finished g s ->
    Map_TID.MapsTo t {| root := f; started := g::l |} s ->
    Enabled t s.

  Inductive Flat: fid -> state ->  Prop :=
  | flat_def:
    forall s f,
    (forall t, Root t f s -> Enabled t s) ->
    Nonempty f s ->
    Flat f s.

  Inductive HasFlat (s: state) : Prop :=
  | has_flat_def:
    forall f,
    Flat f s ->
    HasFlat s.

  Let nonempty_in:
    forall f s,
    Nonempty f s ->
    In f s.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using in_root.
  Qed.

  Structure FinishInd s (P:fid -> list tid -> Prop) := {
    finish_ind_nil:
      forall f,
      Empty f s ->
      P f nil;
    finish_ind_leaf:
      forall f t l,
      P f l ->
      Leaf t s ->
      P f (t::l)%list;
   finish_ind_cons:
      forall f l t g k,
      P f l ->
      List.Forall (fun u => Root u f s) l ->
      Root t f s ->
      P g k ->
      P g (t::k)%list
  }.

  Inductive FEdge s : (fid * fid) -> Prop :=
  | f_edge_def:
    forall f g t,
    Root t f s ->
    Started t g s ->
    FEdge s (f, g).

  Inductive TEdge s : (tid * tid) -> Prop :=
  | t_edge_def:
    forall f u t,
    Started t f s ->
    Root u f s ->
    TEdge s (t, u).


(*
  Lemma flat_cons:
    forall fs ts f t,
    Flat (ts, fs) f ->
    forall g,
    Enabled ft,
    Flat (Map_TID.add t (make g) ts, fs) f.
  Proof.
    
  Qed.
  *)

(* ---- *)
(*
  Inductive Leaf: state -> fid -> Prop :=
  | leaf_def:
    forall fs ts l f,
    Map_FID.MapsTo f l fs ->
    (forall t, List.In t l -> Enabled (ts,fs) t) ->
    Leaf (ts, fs) f.
*)

(*
  Let enabled_task_add_2:
    forall fs ft l f,
    ~ Map_FID.In f fs ->
    EnabledTask fs ft ->
    EnabledTask (Map_FID.add f l fs) ft.
  Proof.
    intros.
    inversion H0; subst; clear H0; auto using enabled_task_ready.
    assert (f <> g). {
      unfold not; intros; subst.
      apply Map_FID_Extra.mapsto_to_in in H1.
      contradiction.
    }
    auto using enabled_task_leaf, Map_FID.add_2.
  Qed.
*)
(*
  Let enabled_add_2:
    forall s t f ft t',
    ~ In f s ->
    t <> t' ->
    Enabled t s ->
    Enabled t (Map_TID.add t' ft s).
  Proof.
    intros.
    inversion H1; subst; clear H1. {
      eauto using enabled_ready, Map_TID.add_2.
    }
    eapply enabled_leaf with (f:=f0); eauto.
    eauto using enabled_leaf, Map_TID.add_2.
    apply enabled_def with (ft:=ft0); auto using Map_TID.add_2.
  Qed.
  *)

(*
  Let enabled_task_remove_2:
    forall fs ft f,
    EnabledTask fs ft ->
    EnabledTask (Map_FID.remove f fs) ft.
  Proof.
    intros.
    inversion H; subst; clear H.
    - auto using enabled_task_ready.
    - apply enabled_task_leaf.
  Qed.


  Let enabled_remove_2:
    forall t u ft ts fs f,
    t <> u ->
    Map_FID.MapsTo f nil fs ->
    Enabled (ts, fs) t ->
    Enabled
      (Map_TID.add u ft ts, Map_FID.remove f fs) t.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    apply enabled_def with (ft:=ft0); auto using Map_TID.add_2.
    inver
    - 
  Qed.
*)
(*
  Let enabled_to_in:
    forall t ts fs,
    Enabled (ts, fs) t ->
    Map_TID.In t ts.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Let enabled_add_3:
    forall fs t l f ts ft t',
    ~ Map_FID.In f fs ->
    ~ Map_TID.In t' ts ->
    Enabled (ts,fs) t ->
    Enabled (Map_TID.add t' ft ts, Map_FID.add f l fs) t.
  Proof.
    intros.
    assert (t <> t'). {
      unfold not; intros; subst.
      contradiction H0.
      eauto.
    }
    auto.
  Qed.

  Let nonempty_add_2:
    forall fs f g ft,
    f <> g ->
    Nonempty fs f ->
    Nonempty (Map_FID.add g ft fs) f.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    eauto using nonempty_def, Map_FID.add_2.
  Qed.

  Let enabled_ready:
    forall ts fs f g t,
    Enabled
      (Map_TID.add t {| root := g; started := nil |} ts,
      Map_FID.remove (elt:=list tid) f fs) t.
  Proof.
    eauto using Map_TID.add_1, enabled_task_ready, enabled_def.
  Qed.*)
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
(*
  Let root_inv_add_make:
    forall t u f g s,
    Root t f (Map_TID.add u (make g) s) ->
    f <> g ->
    Root t f s /\ u <> t.
  Proof.
    intros.
    match goal with
    | H: Root _ _ _ |- _  =>  apply root_inv in H;
      destruct H as [(?,(l,R))|(?,i)]
    end. {
      unfold make in *; simpl in *; subst.
      inversion R; subst; clear R.
      contradiction.
    }
    auto.
  Qed.
*)
  Let started_add_2:
    forall t f s u ft,
    Started t f s ->
    t <> u ->
    Started t f (Map_TID.add u ft s).
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply started_def; eauto using Map_TID.add_2.
  Qed.

  Let root_add_2:
    forall t f s u ft,
    Root t f s ->
    t <> u ->
    Root t f (Map_TID.add u ft s).
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply root_def; eauto using Map_TID.add_2.
  Qed.

  Let started_to_in:
    forall t f s,
    Started t f s ->
    Map_TID.In t s.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Let root_to_in:
    forall t f s,
    Root t f s ->
    Map_TID.In t s.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Let nonempty_add_2:
    forall t s f ft,
    Nonempty f s ->
    ~ Map_TID.In t s ->
    Nonempty f (Map_TID.add t ft s).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply nonempty_def with (t:=t0).
    assert (t<> t0). {
      unfold not; intros; subst.
      contradiction H0; eauto.
    }
    eauto.
  Qed.

  Let empty_to_not_root:
    forall f s,
    Empty f s ->
    forall t,
    ~ Root t f s.
  Proof.
    intros.
    inversion H; auto.
  Qed.

  Let finished_make:
    forall f s t g,
    Finished g s ->
    ~ In f s ->
    ~ Map_TID.In t s ->
    Finished g (Map_TID.add t (make f) s).
  Proof.
    intros.
    inversion H; subst; clear H.
    assert (t0 <> t). {
      unfold not; intros; subst.
      contradiction H1; eauto.
    }
    apply finished_def with (t:=t0); auto using started_add_2.
    apply empty_def; unfold not; intros.
    match goal with
    | H: Root _ _ _ |- _ =>
      apply root_inv_add in H;
      unfold make in *; simpl in *;
      destruct H as [(?,(l',R))|(?,?)]
    end. {
      inversion R; subst; clear R.
      contradiction H0.
      eauto using in_started.
    }
    match goal with
    | H: Root _ _ _ |- _ => contradict H; auto
    end.
  Qed.

  Let flat_to_finished:
    forall f s g l t, 
    Flat f s ->
    Map_TID.MapsTo t {| root := f; started := g :: l |} s ->
    Finished g s.
  Proof.
    intros.
    inversion H; subst; clear H.
    assert (e: Enabled t s) by
      eauto using root_def.
    inversion e; subst; clear e. {
      match goal with
      | [ H1: Map_TID.MapsTo ?t ?x1 ?s, H2: Map_TID.MapsTo ?t ?x2 ?s |- _] =>
        assert (R: x1 = x2) by eauto using Map_TID_Facts.MapsTo_fun;
        inversion R; subst; auto
      end.
    }
    assert (g0 = g). {
      match goal with
      | [ H1: Map_TID.MapsTo ?t ?x1 ?s, H2: Map_TID.MapsTo ?t ?x2 ?s |- _] =>
        assert (R: x1 = x2) by eauto using Map_TID_Facts.MapsTo_fun;
        inversion R; subst; auto
      end.
    }
    subst.
    assumption.
  Qed.

  Theorem flat_reduces:
    forall f s,
    Flat f s ->
    forall t o,
    Root t f s ->
    Typecheck s (t, o) ->
    exists s', Reduces s (t,o) s'.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    - eauto using reduces_init.
    - apply Map_TID_Extra.in_to_mapsto in H4.
      destruct H4 as ([], mt).
      eauto using reduces_finish.
    - assert (g = f). {
        inversion H0; subst; clear H0.
        match goal with
        | [ H1: Map_TID.MapsTo ?t ?x1 ?s, H2: Map_TID.MapsTo ?t ?x2 ?s |- _] =>
          assert (R: x1 = x2) by eauto using Map_TID_Facts.MapsTo_fun;
          inversion R; subst; auto
        end.
      }
      subst.
      exists (Map_TID.add t {| root := f; started := l |} s).
      eapply reduces_await; eauto.
    - apply Map_TID_Extra.in_to_mapsto in H5.
      destruct H5 as (ft, mt).
      eauto using reduces_async.
    - eauto using reduces_end.
  Qed.

(*
  Let enabled_add_2:
    forall u s t ft,
    Enabled u s ->
    t <> u ->
    Enabled u (Map_TID.add t ft s).
  Proof.
    intros.
    inversion H; subst; clear H. {
      eauto using enabled_ready, Map_TID.add_2.
    }
    assert (Finished g (Map_TID.add t ft s)). {
      apply finished_def; unfold not; intros.
      apply root_inv in H.
      destruct H as [(?,(l',?))|(?,?)]. {
        subst.
        inversion H1; subst; clear H1.
        specialize (H u).
        apply root_def in H2.
        contradiction.
      }
    }
    eapply enabled_leaf; eauto.
    eauto using enabled_leaf, Map_TID.add_2.
  Qed.
*)
(*
  Let finished_async:
    forall g s f t,
    Finished g s ->
    ~ In f s ->
    Finished g (Map_TID.add t (make f) s).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply finished_def; intros.
    unfold not; intros.
    apply root_inv in H. 
    destruct H as [(?,(l,R))|?]. {
      unfold make in *.
      inversion R; clear R. subst; clear R.
    }
  Qed.
    *)
  
  Let finished_eq_finish:
    forall t g f l s,
    Map_TID.MapsTo t {| root := g; started := l |} s ->
    ~ In f s ->
    Finished f (Map_TID.add t {| root := g; started := f :: l |} s).
  Proof.
    intros.
    apply finished_def with (t:=t). {
      eauto using started_def, List.in_eq, Map_TID.add_1.
    }
    apply empty_def.
    unfold not; intros u; intros.
    apply root_inv_add in H1.
    contradiction H0.
    destruct H1 as [(?,(l',R))|(?,?)]. {
      inversion R; subst; clear R.
      eauto using in_root, root_def.
    }
    eauto using in_root.
  Qed.

  Let enabled_eq_finish:
    forall t g f l s,
    Map_TID.MapsTo t {| root := g; started := l |} s ->
    ~ In f s ->
    Enabled t (Map_TID.add t {| root := g; started := f :: l |} s).
  Proof.
    eauto using enabled_leaf, Map_TID.add_1.
  Qed.

  Let root_fun:
    forall t f g s,
    Root t f s ->
    Root t g s ->
    f = g.
  Proof.
    intros.
    inversion H; inversion H0; subst.
    match goal with
    | [ H1: Map_TID.MapsTo ?t ?x1 ?s, H2: Map_TID.MapsTo ?t ?x2 ?s |- _] =>
      assert (R: x1 = x2) by eauto using Map_TID_Facts.MapsTo_fun;
      inversion R; subst; auto
    end.
  Qed.

  Let started_add_finish:
    forall h t g l s f u,
    Started t h s ->
    Map_TID.MapsTo u {| root := g; started := l |} s ->
    Started t h (Map_TID.add u {| root := g; started := f :: l |} s).
  Proof.
    intros.
    inversion H; subst; clear H.
    destruct (TID.eq_dec t u). {
      subst.
      match goal with
      | [ H1: Map_TID.MapsTo ?t ?x1 ?s, H2: Map_TID.MapsTo ?t ?x2 ?s |- _] =>
        assert (R: x1 = x2) by eauto using Map_TID_Facts.MapsTo_fun;
        inversion R; subst; clear R H2
      end.
      eauto using started_def, List.in_cons, Map_TID.add_1.
    }
    eauto using started_def, Map_TID.add_2.
  Qed.

  Let finished_add_finish:
    forall h t g l s f,
    Finished h s ->
    Map_TID.MapsTo t {| root := g; started := l |} s ->
    Finished h (Map_TID.add t {| root := g; started := f :: l |} s).
  Proof.
    intros.
    inversion H; subst; clear H.
    apply finished_def with (t:=t0); auto.
    inversion H2; subst; clear H2.
    apply empty_def.
    unfold not; intros.
    apply root_inv_add in H2.
    destruct H2 as [(?,(l', R))|(?,?)]. {
      inversion R; subst; clear R.
      assert (N: ~ Root t1 h s) by eauto.
      contradiction N.
      eauto using root_def.
    }
    assert (N: ~ Root t1 h s) by eauto.
    contradiction.
  Qed.

  Let root_add_finish:
    forall f g h l s t u,
    Root t f s ->
    Map_TID.MapsTo u {| root := g; started := l |} s ->
    Root t f (Map_TID.add u {| root := g; started := h :: l |} s).
  Proof.
    intros.
    inversion H; subst; clear H.
    destruct (TID.eq_dec u t). {
      subst.
      match goal with
      | [ H1: Map_TID.MapsTo ?t ?x1 ?s, H2: Map_TID.MapsTo ?t ?x2 ?s |- _] =>
        assert (R: x1 = x2) by eauto using Map_TID_Facts.MapsTo_fun;
        inversion R; subst; clear R H2
      end.
      eauto using root_def, Map_TID.add_1.
    }
    eauto using root_def, Map_TID.add_2.
  Qed.

  Let nonempty_add_finish:
    forall f g h l s t,
    Nonempty f s ->
    Map_TID.MapsTo t {| root := g; started := l |} s ->
    Nonempty f (Map_TID.add t {| root := g; started := h :: l |} s).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using nonempty_def.
  Qed.

  Let finished_to_empty:
    forall f s,
    Finished f s ->
    ~ Nonempty f s.
  Proof.
    unfold not; intros.
    inversion H0; inversion H; subst; clear H H0.
    assert (~ Root t f s) by auto.
    contradiction.
  Qed.

  Definition task_edges (ft:task) :=
    List.map (fun f => (root ft, f)) (started ft).

  Definition f_edges (s:state) : list (fid * fid) := 
    List.flat_map task_edges (Map_TID_Extra.values s).
Require Import Aniceto.List.
Require Import Aniceto.Graphs.FGraph.

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

  Let dag_f_edge_to_fgraph_edge:
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

  Lemma finish_dag:
    forall s a s',
    DAG (FGraph.Edge (f_edges s)) ->
    Reduces s a s' ->
    DAG (FGraph.Edge (f_edges s')).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - simpl.
      assert (DAG (FEdge s)) by auto.
      apply dag_f_edge_to_fgraph_edge.
      apply dag_impl with (E:=FEdge s); auto; intros.
      eauto using f_edge_add_make.
    - apply dag_impl with (E:=Edge (((g,f)::(f_edges s)))). {
        eauto.
      }
      apply f_dag_cons; auto using FID.eq_dec.
  Qed.
(*
  Lemma finish_ind:
    forall s P, 
    FinishInd s P ->
    forall l f,
    (forall t, List.In t l -> Root t f s) ->
    (forall t, Root t f s -> List.In t l) ->
    P f l.
  Proof.
    induction l; intros. {
      eapply finish_ind_nil; eauto.
    }
    assert (Root a f s). {
      inversion H0; auto using List.in_eq.
    }
    assert (P f l). {
      inversion H0.
    }
    - 
  Qed.
*)

  Lemma has_flat_reduces:
    forall s s' a,
    HasFlat s ->
    Reduces s a s' ->
    HasFlat s'.
  Proof.
    intros.
    inversion H0; subst; clear H0;
    inversion H; subst; clear H;
    inversion H0; subst; clear H0.
    - apply has_flat_def with (f:=f0).
      assert (f <> f0). {
        unfold not; intros; subst.
        contradiction H1.
        auto.
      }
      apply flat_def; intros; eauto.
      apply root_inv_add_make in H4; auto; destruct H4 as (i,?).
      clear H0.
      apply H in i.
      inversion i; subst; clear i; eauto using enabled_ready, enabled_leaf, Map_TID.add_2.
    - assert (f <> f0). {
        unfold not; intros; subst.
        contradiction H1.
        eauto using Map_FID_Extra.mapsto_to_in.
      }
      apply has_flat_def with (f:=f0).
      apply flat_def with (f:=f0); auto.
      intros.
      match goal with
      | H: Root _ _ _ |- _ =>
        apply root_inv in H;
        destruct H as [(?,(l',R))|(?,?)]
      end. {
        inversion R; subst; clear R.
        eauto.
      }
      assert (Enabled t0 s). {
        auto.
      }
      rename t0 into u.
      inversion H6; subst; clear H6. {
        eauto using enabled_ready, Map_TID.add_2.
      }
      subst.
      eapply enabled_leaf with (f:=f1) (g:=g0) (l:=l0); eauto using Map_TID.add_2.
    - destruct (FID.eq_dec f0 f). {
        subst.
        apply finished_to_empty in H2.
        contradiction.
      }
      destruct (FID.eq_dec f0 g). {
        subst.
      }
      (* suppose t was enabled, then we need to see if the next f is a leaf. *)
      destruct l. {
        assert (Flat f0 s) by eauto using flat_def.
        apply has_flat_def with (f:=f0).
        
        apply flat_def.
        + intros.
          apply root_inv in H0.
          destruct H0 as [(?,(l,R))|(?,?)]. {
            inversion R; subst; clear R.
            eauto using enabled_ready, Map_TID.add_1.
          }
          assert (e: Enabled t0 s) by eauto.
          inversion e; subst; clear e. {
            eauto using enabled_ready, Map_TID.add_2.
          }
          inversion H5; subst.
          eapply enabled_leaf; eauto using Map_TID.add_2.
          apply finished_def with (t:=t1). {
            assert (t1 <> t). {
              unfold not; intros; subst.
              assert (~ Root t0 
            }
          }
          eauto using enabled_ready, Map_TID.add_2.
          eapply enabled_leaf; eauto.
          apply H5 in H.
          inversion H; subst; clear H.
          destruct (TID.eq_dec t t0). {
            subst; auto.
          }
          apply enabled_def with (ft:=ft); auto using Map_TID.add_2.
          inversion H9; subst; clear H9. {
            auto using enabled_task_ready.
          }
          apply enabled_task_leaf.
          destruct (FID.eq_dec g0 f). {
            subst.
          }
        + auto using Map_FID.remove_2.
      }
        assert (t <> t0). {
          unfold not; intros; subst.
        }
  Qed.

  Lemma progress:
    exists t,
    

