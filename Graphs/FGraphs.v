Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Graphs.Core.
Require Import PairUtil.
Require Import ListUtil.
Require Import Bool.
Require Import SigUtil.
Require Import ListSetUtil.

Set Implicit Arguments.

Section FGRAPHS.

Variable V:Type.

Variable eq_dec : forall (v1 v2:V), {v1 = v2} + {v1 <> v2}.

Let edge := (V*V)%type.
Let fgraph := list edge.

Definition Edge (g:fgraph) (e:edge) := List.In e g.

Lemma edge_def:
  forall e g,
  List.In e g ->
  Edge g e.
Proof.
  intros.
  unfold Edge.
  assumption.
Qed.

Lemma edge_eq:
  forall e g,
  Edge (e :: g) e.
Proof.
  intros.
  unfold Edge.
  apply in_eq.
Qed.

Definition In (v:V) (g:fgraph) := Core.In (Edge g) v.

Lemma in_def:
  forall v e g,
  pair_In v e ->
  Edge g e ->
  In v g.
Proof.
  intros.
  apply Core.in_def with (e:=e); repeat auto.
Qed.

Lemma in_left:
  forall v v' g,
  Edge g (v, v') ->
  In v g.
Proof.
  intros.
  apply Core.in_left with (v':=v'); auto.
Qed.

Lemma in_right:
  forall v v' g,
  Edge g (v', v) ->
  In v g.
Proof.
  intros.
  apply Core.in_right with (v':=v'); auto.
Qed.

Lemma in_nil:
  forall v,
  In v nil -> False.
Proof.
  intros.
  inversion H.
  inversion H0.
  inversion H1.
Qed.

Lemma in_cons:
  forall v e g,
  In v g ->
  In v (e :: g).
Proof.
  intros.
  inversion H.
  destruct H0.
  assert (x_in : List.In x (e::g)).
  apply List.in_cons. assumption.
  apply in_def with (e := x); repeat auto.
Qed.

Lemma pred_in_cycle:
  forall v w E,
  Cycle E w ->
  In v w ->
  exists v', E (v', v) /\ Edge w (v', v).
Proof.
  intros.
  destruct H0 as ((v1, v2), (Hin, Hpin)).
  assert (Hw : Walk E w).
  inversion H; auto.
  inversion Hpin.
  - subst; simpl in *.
    apply Core.pred_in_cycle with (v1:=v1) (v2:=v2) in H.
    destruct H as (v3, H).
    exists v3.
    intuition.
    + apply in_edge with (w:=w); repeat auto.
    + auto.
  - subst; simpl in *.
    exists v1.
    intuition.
    apply in_edge with (w:=w); repeat auto.
Qed.

Lemma succ_in_cycle:
  forall v w E,
  Cycle E w ->
  In v w ->
  exists v', E (v, v') /\ Edge w (v, v').
Proof.
  intros.
  destruct H0 as ((v1, v2), (Hin, Hpin)).
  assert (Hw : Walk E w).
  inversion H; auto.
  inversion Hpin.
  - subst; simpl in *.
    exists v2.
    intuition.
    apply in_edge with (w:=w); repeat auto.
  - subst; simpl in *.
    apply Core.succ_in_cycle with (v1:=v1) (v2:=v2) in H.
    destruct H as (v3, H).
    exists v3.
    intuition.
    + apply in_edge with (w:=w); repeat auto.
    + auto.
Qed.


Definition mem (v:V) (g:fgraph) : bool :=
  existsb (fun e => pair_mem eq_dec v e) g.

Lemma mem_prop:
  forall v g,
  mem v g = true ->
  In v g.
Proof.
  intros.
  unfold mem in *.
  apply existsb_exists in H.
  destruct H as (x, (x_in_g, mem_in_x)).
  apply pair_mem_prop in mem_in_x.
  apply in_def with (e:=x); repeat auto.
Qed.

Lemma mem_from_prop:
  forall v g,
  In v g ->
  mem v g = true.
Proof.
  intros.
  unfold In in *.
  destruct H as (e, (e_in_g, v_in_e)).
  unfold mem.
  rewrite existsb_exists.
  exists e.
  apply pair_mem_from_prop with (eq_dec:=eq_dec) in v_in_e.
  auto.
Qed.

Definition subgraph g g' := Core.subgraph (Edge g) (Edge g').

Lemma subgraph_incl:
  forall g g',
  incl g g' <->
  subgraph g g'.
Proof.
  split.
  - intros.
    unfold subgraph.
    unfold Core.subgraph.
    intros.
    unfold Edge in *.
    unfold incl in *.
    apply H; auto.
  - intros.
    unfold subgraph in *.
    unfold Core.subgraph in *.
    unfold Edge in *.
    unfold incl.
    assumption.
Qed.

Lemma subgraph_filter:
  forall g f,
  subgraph (filter f g) g.
Proof.
  intros.
  assert (Hx := filter_incl f g).
  apply subgraph_incl.
  auto.
Qed.

Lemma subgraph_edge:
  forall (g g':fgraph) e,
  subgraph g g' ->
  (Edge g) e ->
  (Edge g') e.
Proof.
  intros.
  unfold subgraph in *.
  apply Core.subgraph_edge with (E:=Edge g) (E':=Edge g'); repeat auto.
Qed.

Lemma subgraph_in:
  forall (g g':fgraph) v,
  subgraph g g' ->
  In v g ->
  In v g'.
Proof.
  intros.
  unfold In in *.
  unfold subgraph in *.
  apply Core.subgraph_in with (E:=Edge g); repeat auto.
Qed.

Lemma subgraph_walk:
  forall (g g':fgraph) w,
  subgraph g g' ->
  Walk (Edge g) w ->
  Walk (Edge g') w.
Proof.
  intros.
  unfold subgraph in *.
  apply Core.subgraph_walk with (E:=Edge g) (E':=Edge g'); repeat auto.
Qed.

Lemma walk_is_subgraph:
  forall g w,
  Walk (Edge g) w ->
  subgraph w g.
Proof.
  intros.
  unfold subgraph.
  unfold Core.subgraph.
  intros.
  apply in_edge with (e:=e) in H.
  assumption.
  unfold Edge in *.
  assumption.
Qed.

Lemma subgraph_cycle:
  forall (g g':fgraph) w,
  subgraph g g' ->
  Cycle (Edge g) w ->
  Cycle (Edge g') w.
Proof.
  intros.
  unfold subgraph in *.
  apply Core.subgraph_cycle with (E:=Edge g) (E':=Edge g'); repeat auto.
Qed.

Lemma subgraph_cons:
  forall (g:fgraph) e,
  subgraph g (cons e g).
Proof.
  intros.
  unfold subgraph.
  unfold Core.subgraph.
  intros.
  apply List.in_cons.
  assumption.
Qed.

Lemma cycle_add:
  forall (g:fgraph) e w,
  Cycle (Edge g) w ->
  Cycle (Edge (cons e g)) w.
Proof.
  intros.
  assert (sub := subgraph_cons g e).
  apply subgraph_cycle with (g:=g); repeat assumption.
Qed.

Inductive HasIncoming : fgraph -> V -> Prop :=
  has_incoming_def:
    forall v v' g,
    Edge g (v', v) ->
    HasIncoming g v.

Lemma has_incoming_cons:
  forall e g v,
  HasIncoming g v ->
  HasIncoming (e :: g) v.
Proof.
  intros.
  inversion H. subst.
  unfold Edge in *.
  apply List.in_cons with (a:=e) in H0.
  apply has_incoming_def with (v':=v').
  auto.
Qed.

Inductive HasOutgoing : fgraph -> V -> Prop :=
  has_outgoing_def:
    forall v v' g,
    Edge g (v, v') ->
    HasOutgoing g v.

Lemma has_outgoing_cons:
  forall e g v,
  HasOutgoing g v ->
  HasOutgoing (e :: g) v.
Proof.
  intros.
  inversion H. subst.
  unfold Edge in *.
  apply List.in_cons with (a:=e) in H0.
  apply has_outgoing_def with (v':=v').
  auto.
Qed.

Definition has_incoming (g:fgraph) (v:V) : bool :=
  existsb (fun e => if eq_dec v (snd e) then true else false) g.

Lemma has_incoming_prop:
  forall g v,
  has_incoming g v = true ->
  HasIncoming g v.
Proof.
  intros.
  unfold has_incoming in H.
  apply existsb_exists in H.
  destruct H as (x, (x_in_g, v_in_x)).
  destruct x as (v1, v2).
  simpl in *.
  destruct (eq_dec v v2).
  - subst.
    apply edge_def in x_in_g.
    apply has_incoming_def with (v':=v1); assumption.
  - inversion v_in_x.
Qed.

Lemma has_incoming_from_prop:
  forall g v,
  HasIncoming g v ->
  has_incoming g v = true.
Proof.
  intros.
  unfold has_incoming.
  apply existsb_exists.
  inversion H.
  subst.
  exists (v', v).
  unfold Edge in H0.
  split.
  assumption.
  - simpl. destruct (eq_dec v v). auto. contradiction n.
    trivial.
Qed.

Lemma has_incoming_in_snd:
  forall e w,
  List.In e w ->
  HasIncoming w (snd e).
Proof.
  intros.
  destruct e.
  simpl.
  apply has_incoming_def with (v':=v).
  unfold Edge.
  assumption.
Qed.

Let edge_eq_dec := pair_eq_dec eq_dec.

Definition rm_sources (g:fgraph) :=
  feedback_filter edge_eq_dec (fun g' e => has_incoming g' (fst e)) g.

Lemma rm_sources_incl:
  forall g,
  incl (rm_sources g) g.
Proof.
  intros.
  unfold rm_sources.
  apply feedback_filter_incl.
Qed.

Lemma rm_sources_subgraph:
  forall g,
  subgraph (rm_sources g) g.
Proof.
  intros.
  apply subgraph_incl.
  apply rm_sources_incl.
Qed.

Lemma rm_sources_in:
  forall v g,
  In v (rm_sources g) ->
  In v g.
Proof.
  intros.
  apply (subgraph_in (g:=rm_sources g)).
  apply rm_sources_subgraph.
  assumption.
Qed.

Lemma rm_sources_has_incoming:
  forall g v,
  In v (rm_sources g) ->
  HasIncoming (rm_sources g) v.
Proof.
  intros.
  unfold rm_sources in *.
  destruct H as (e, (e_in_g, v_in_e)).
  assert (Hx := e_in_g).
  unfold Edge in e_in_g.
  apply feedback_filter_in_f in e_in_g.
  apply has_incoming_prop in e_in_g.
  inversion v_in_e.
  - rewrite <- H in e_in_g.
    assumption.
  - remember (feedback_filter edge_eq_dec
              (fun (g' : list (V * V)) (e0 : V * V) =>
               has_incoming g' (fst e0)) g) as rm_g.
    destruct e as (v1, v2).
    simpl in *.
    rewrite <- H in *.
    apply has_incoming_def with (v' := v1).
    unfold Edge.
    assumption.
Qed.

Lemma filter_edge_in:
  forall e f g,
  Edge g e ->
  f e = true ->
  Edge (filter f g) e.
Proof.
  intros.
  apply edge_def.
  apply filter_In.
  intuition.
Qed.

Lemma filter_vertex_in:
  forall v e f g,
  pair_In v e ->
  Edge g e ->
  f e = true ->
  In v (filter f g).
Proof.
  intros.
  unfold In.
  unfold Core.In.
  exists e.
  intuition.
  apply filter_edge_in; repeat auto.
Qed.

Lemma has_outgoing_filter:
  forall g v,
  let fg := (fun e : V * V => has_incoming g (fst e)) in
  In v (filter fg g) ->
  HasOutgoing g v ->
  HasOutgoing (filter fg g) v.
Proof.
  intros.
  inversion H.
  subst.
  destruct H1.
  destruct x.
  inversion H2.
  - simpl in H3.
    rewrite H3 in *.
    apply has_outgoing_def with (v':=v1).
    assumption.
  - simpl in H3. subst.
    (* let's check the edge in the original graph *)
    inversion H0; subst; clear H0.
    remember (fg (v1, v')) as b.
    symmetry in Heqb.
    destruct b.
    + apply has_outgoing_def with (v' := v').
      apply filter_edge_in; repeat auto.
    + (* absurd case *)
      unfold fg in Heqb.
      simpl in Heqb.
      assert (Hx: has_incoming g v1 = true).
      apply has_incoming_from_prop.
      apply has_incoming_def with (v':=v0).
      apply subgraph_edge with (g:=(filter fg g)).
      apply subgraph_filter.
      assumption.
      (* eoa *)
      rewrite Hx in Heqb.
      inversion Heqb.
Qed.

Lemma has_outgoing_rm_incl:
  forall v g,
  HasOutgoing g v ->
  In v (rm_sources g) ->
  HasOutgoing (rm_sources g) v.
Proof.
  intros.
  unfold rm_sources in *.
  remember (fun (g' : list (V * V)) e => has_incoming g' (fst e)) as f.
  functional induction (feedback_filter edge_eq_dec f g).
  - assumption.
  - rename l into g.
    remember (fun (g' : list (V * V)) (e0 : V * V) => has_incoming g' (fst e0)) as f.
    remember (fun e : V * V => has_incoming g (fst e)) as ff.
    apply IHl.
    rewrite Heqff.
    apply has_outgoing_filter.
    inversion H0.
    destruct H1.
    unfold In.
    unfold Edge in *.
    exists x.
    intuition.
    apply feedback_filter_in in H1.
    subst.
    assumption.
    assumption.
    assumption.
Qed.

Definition Forall (P: V -> Prop) (g:fgraph) :=
  Core.Forall (Edge g) P.

Lemma subgraph_forall:
  forall g g' P,
  subgraph g g' ->
  Forall P g' ->
  Forall P g.
Proof.
  intros.
  unfold Forall in *.
  unfold subgraph in *.
  apply Core.subgraph_forall with (E':=Edge g'); repeat auto.
Qed.

Lemma forall_incl:
  forall g (P P': V -> Prop),
  (forall x, P x -> P' x) ->
  Forall P g ->
  Forall P' g.
Proof.
  intros.
  unfold Forall in *.
  apply Core.forall_incl with (P:=P); repeat auto.
Qed.

Lemma forall_inv:
  forall (v:V) g (e:edge) P,
  Forall P (e :: g) ->
  Forall P g.
Proof.
  intros.
  apply subgraph_forall with (g':= e :: g).
  apply subgraph_incl.
  apply incl_tl.
  apply incl_refl.
  assumption.
Qed.

Definition AllOutgoing g : Prop := Forall (fun v => HasOutgoing g v) g.

Lemma all_outgoing_in:
  forall v g,
  In v g ->
  AllOutgoing g ->
  HasOutgoing g v.
Proof.
  intros.
  unfold AllOutgoing in *.
  unfold Forall in *.
  apply H0; assumption.
Qed.

Lemma all_outgoing_rm_incl:
  forall g,
  AllOutgoing g ->
  AllOutgoing (rm_sources g).
Proof.
  intros.
  unfold AllOutgoing in *.
  unfold Forall in *.
  unfold Core.Forall in *.
  intros.
  apply has_outgoing_rm_incl.
  apply rm_sources_in in H0.
  apply H; assumption.
  assumption.
Qed.

Definition AllIncoming g : Prop := Forall (fun v => HasIncoming g v) g.

(* Returns all incoming edges *)
Fixpoint get_incoming (g:fgraph) v : list edge :=
  match g with
    | e :: g' =>
      let res := get_incoming g' v in
      if eq_dec (snd e) v
      then e :: res
      else res
    | nil => nil
  end.

Lemma get_incoming_inv:
  forall v1 v2 v g,
  List.In (v1, v2) (get_incoming g v) ->
  v2 = v.
Proof.
  intros.
  induction g.
  - simpl in H. inversion H.
  - destruct a.
    simpl in H.
    destruct (eq_dec v3 v).
    + subst.
      inversion H.
      * inversion H0.
        trivial.
      * apply IHg; assumption.
    + apply IHg.
      assumption.
Qed.

Lemma all_incoming_prop:
  forall v v' g,
  Edge g (v', v) ->
  List.In (v', v) (get_incoming g v).
Proof.
  intros.
  induction g.
  - inversion H. (* absurd *)
  - destruct a.
    simpl.
    destruct (eq_dec v1 v).
    + subst.
      destruct H.
      * inversion H.
        subst.
        apply in_eq.
      * apply IHg in H; clear IHg.
        apply List.in_cons; assumption.
    + apply IHg.
      unfold Edge in *.
      inversion H.
      inversion H0.
      subst.
      contradiction n.
      trivial.
      assumption.
Qed.

Lemma all_incoming_from_prop:
  forall e g v,
  List.In e (get_incoming g v) ->
  Edge g e.
Proof.
  intros.
  induction g.
  - simpl in H. inversion H.
  - simpl in H.
    unfold Edge.
    destruct a.
    simpl in H.
    destruct (eq_dec v1 v).
    + inversion H.
      * inversion H0; subst.
        apply List.in_eq.
      * apply IHg in H0.
        unfold Edge in H0.
        apply List.in_cons.
        assumption.
    + apply IHg in H.
      unfold Edge in H.
      apply List.in_cons.
      assumption.
Qed.

Lemma subgraph_get_incoming:
  forall g v,
  subgraph (get_incoming g v) g.
Proof.
  intros.
  unfold subgraph.
  unfold Core.subgraph.
  intros.
  unfold Edge in H.
  apply all_incoming_from_prop with (v:=v).
  assumption.
Qed.

Lemma has_incoming_neq_nil:
  forall g v,
  HasIncoming g v <->
  get_incoming g v <> nil.
Proof.
  intros.
  split.
  + intros.
    inversion H.
    subst.
    apply all_incoming_prop in H0.
    remember (get_incoming g v).
    destruct l.
    - inversion H0.
    - intuition.
      inversion H1.
  + intros.
    remember (get_incoming g v) as g'.
    destruct g'.
    - contradiction H; trivial.
    - assert (List.In e (get_incoming g v)).
      rewrite <- Heqg';
      apply in_eq.
      (* eoa *)
      assert (Hx := H0).
      destruct e.
      apply get_incoming_inv in H0.
      subst.
      apply has_incoming_def with (v':=v0).
      apply all_incoming_from_prop in Hx.
      assumption.
Qed.

Lemma all_incoming_in:
  forall v g,
  In v g ->
  AllIncoming g ->
  HasIncoming g v.
Proof.
  intros.
  unfold AllIncoming in *.
  unfold Forall in *.
  apply H0; assumption.
Qed.

Lemma all_incoming_rm_incl:
  forall g,
  AllOutgoing g ->
  AllIncoming (rm_sources g).
Proof.
  intros.
  unfold AllOutgoing in *.
  unfold AllIncoming.
  unfold Forall in *.
  unfold Core.Forall in *.
  intros.
  apply rm_sources_has_incoming.
  assumption.
Qed.

Lemma rm_filter_nonempty:
  forall g,
  AllOutgoing g ->
  let fg := fun (e:edge) => has_incoming g (fst e) in
  (exists v, In v g) ->
  exists v, In v (filter fg g).
Proof.
  intros.
  destruct H0 as (v, H0).
  inversion H0.
  destruct H1.
  destruct x as (vi, vo).
  assert (vo_out: HasOutgoing g vo).
  apply all_outgoing_in.
  apply in_right with (v':=vi); auto.
  assumption.
  (* eoa *)
  inversion vo_out.
  subst.
  exists v'.
  apply filter_vertex_in with (e:=(vo, v')); repeat auto.
  apply pair_in_right.
  unfold fg.
  simpl.
  apply has_incoming_from_prop.
  apply has_incoming_def with (v':= vi).
  apply edge_def; auto.
Qed.

Let subgraph_forall_filter:
  forall P f g,
  Forall P g ->
  Forall P (filter f g).
Proof.
  intros.
  apply subgraph_forall with (g':=g).
  apply subgraph_filter.
  assumption.
Qed.

Let rm_sources_nonempty':
  forall g,
  let g' := (rm_sources g) in
  AllOutgoing g ->
  (exists v, In v g) ->
  AllOutgoing g' ->
  AllIncoming g' ->
  exists v', In v' g'.
Proof.
  intros.
  unfold rm_sources in *.
  remember (fun (g' : list (V * V)) (e : V * V) => has_incoming g' (fst e)) as fg.
  functional induction (feedback_filter edge_eq_dec fg g).
  - auto.
  - unfold g' in *.
    rename l into g.
    remember (feedback_filter (pair_eq_dec eq_dec) fg (filter (fg g) g)) as gf.
    apply IHl.
    (* 1 *)
    unfold AllOutgoing.
    unfold Forall.
    unfold Core.Forall.
    intros.
    rewrite Heqfg.
    rewrite Heqfg in H3.
    unfold AllOutgoing in H.
    unfold Forall in H.
    inversion H3.
    destruct H4.
    unfold Edge in H4.
    apply filter_in in H4.
    apply has_outgoing_filter; repeat auto.
    apply H.
    unfold In.
    exists x.
    auto.
    (* 2 *)
    rewrite Heqfg.
    apply rm_filter_nonempty; repeat auto.
    (* 3 *)
    assumption.
    (* 4 *)
    assumption.
Qed.

Lemma nonempty_exists_vertex:
  forall g,
  g <> nil <->
  exists v, In v g.
Proof.
  intros.
  split.
  + intros; destruct g.
    - contradiction H.
      trivial.
    - destruct e.
      exists v.
      apply in_left with (v':=v0).
      apply edge_eq.
  + intros.
    intuition.
    destruct H.
    inversion H.
    destruct H1.
    subst.
    inversion H1.
Qed.

Lemma rm_sources_nonempty:
  forall g,
  AllOutgoing g ->
  g <> nil ->
  AllOutgoing (rm_sources g) ->
  AllIncoming (rm_sources g) ->
  rm_sources g <> nil.
Proof.
  intros.
  apply nonempty_exists_vertex in H0.
  apply nonempty_exists_vertex.
  apply rm_sources_nonempty'; repeat auto.
Qed.

Theorem exists_has_incoming:
  forall g,
  AllOutgoing g ->
  g <> nil ->
  exists (g':fgraph),
  subgraph g' g /\
  AllOutgoing g' /\
  AllIncoming g' /\
  g' <> nil.
Proof.
  intros.
  exists (rm_sources g).
  assert (Ha : AllOutgoing (rm_sources g)).
  apply all_outgoing_rm_incl; assumption.
  assert (Hb : AllIncoming (rm_sources g)).
  apply all_incoming_rm_incl; assumption.
  split.
  - unfold rm_sources.
    unfold subgraph.
    apply feedback_filter_incl.
  - split. assumption.
    split. assumption.
    apply rm_sources_nonempty; repeat auto.
Qed.

Definition prepend (w:list edge) (g:fgraph) : option edge :=
  match w with
    | e :: _ => 
      match (get_incoming g (fst e)) with
        | e :: _ => Some e
        | nil => None
      end
    | nil => None
  end.

Lemma prepend_walk:
  forall g w e,
  Walk (Edge g) w ->
  prepend w g = Some e ->
  Linked e w.
Proof.
  intros.
  destruct w.
  - unfold Linked. auto.
  - simpl in H0.
    destruct p.
    simpl in *.
    remember (get_incoming g v).
    destruct l.
    inversion H0.
    destruct e0.
    assert (List.In (v1, v2) (get_incoming g v)).
    rewrite <- Heql. apply in_eq.
    apply get_incoming_inv in H1.
    destruct e.
    inversion H0.
    subst.
    unfold Linked.
    auto.
Qed.

Lemma prepend_edge:
  forall g w e,
  prepend w g = Some e ->
  Edge g e \/ Edge w e.
Proof.
  intros.
  unfold Edge.
  destruct w.
  - simpl in *.
    destruct g.
    * inversion H.
    * inversion H; intuition; apply List.in_eq.
  - simpl in *.
    destruct e0.
    simpl in *.
    remember (get_incoming g v).
    destruct l.
    + inversion H.
    + inversion H; subst; clear H.
      assert (Edge (get_incoming g v) e).
      assert (List.In e (get_incoming g v)).
      rewrite <- Heql.
      apply in_eq.
      unfold Edge. assumption.
      assert (List.In e g).
      assert (Edge g e).
      apply subgraph_edge with (g:=(get_incoming g v)).
      apply subgraph_get_incoming.
      assumption.
      unfold Edge in H0; assumption.
      intuition.
Qed.

Fixpoint cut (v:V) (w:list edge) :=
  match w with
    | nil => nil
    | e :: w' =>
      if eq_dec v (snd e)
      then e :: nil
      else e :: (cut v w')
  end.

Lemma starts_with_cons_inv:
  forall e w (v:V),
  StartsWith (e :: w) v ->
  fst e = v.
Proof.
  intros.
  destruct H.
  destruct H as (w', (H1, H2)).
  inversion H1.
  auto.
Qed.

Lemma starts_with_cons:
  forall e w (v:V),
  fst e = v ->
  StartsWith (e :: w) v.
Proof.
  intros.
  unfold StartsWith.
  exists e.
  exists w.
  intuition.
Qed.

Lemma cut_starts_with:
  forall v v' w,
  StartsWith w v ->
  StartsWith (cut v' w) v.
Proof.
  intros.
  destruct w.
  - destruct H.
    destruct H.
    destruct H.
    inversion H.
  - simpl.
    (*unfold StartsWith.*)
    destruct (eq_dec v' (snd p)).
    + apply starts_with_cons_inv in H.
      apply starts_with_cons; repeat auto.
    + apply starts_with_cons_inv in H.
      apply starts_with_cons; repeat auto.
Qed.

Lemma cut_ends_with:
  forall v w,
  HasIncoming w v ->
  EndsWith (cut v w) v.
Proof.
  intros.
  induction w.
  - inversion H. inversion H0.
  - inversion H.
    subst.
    unfold Edge in H0.
    apply in_inv in H0.
    destruct H0.
    + destruct a.
      inversion H0; subst; clear H0.
      exists (v', v).
      intuition.
      simpl.
      destruct (eq_dec v v).
      * apply end_nil.
      * assert (v = v); auto.
        apply f in H0; inversion H0.
    + assert (Hedge: Edge w (v', v)). unfold Edge; assumption.
      apply has_incoming_def in Hedge.
      apply IHw in Hedge.
      destruct Hedge.
      destruct H1.
      simpl.
      destruct (eq_dec v (snd a)).
      * destruct x; destruct a.
        simpl in *; subst.
        exists (v2, v3).
        simpl.
        intuition.
        apply end_nil.
      * exists x.
        intuition.
        apply end_cons.
        assumption.
Qed.

Lemma cut_is_linked:
  forall a v w,
  Linked a w ->
  Linked a (cut v w).
Proof.
  intros.
  induction w.
  - auto.
  - simpl.
    destruct (eq_dec v (snd a0)).
    + inversion H.
      auto.
    + auto.
Qed.

Lemma cut_is_walk:
  forall g w v,
  Walk (Edge g) w ->
  Walk (Edge g) (cut v w).
Proof.
  intros.
  induction w.
  - simpl. assumption.
  - inversion H.
    subst.
    apply IHw in H2.
    simpl.
    destruct (eq_dec v (snd a)).
    + apply edge_to_walk.
      assumption.
    + apply walk_cons.
      assumption.
      assumption.
      apply cut_is_linked.
      auto.
Qed.

Definition sublen (p:(list edge * fgraph)) :=
  let (w, g) := p in
  length w - length g.

Section FIND_CYCLE.

Variable g:fgraph.

Definition IsWalkOf w := Walk (Edge g) w /\ NoDup w.

Definition WalkOf := { w : list edge | Walk (Edge g) w /\ NoDup w /\ w <> nil}.

Lemma prepend_edge2:
  forall w g e,
  prepend w g = Some e ->
  Walk (Edge g) w ->
  Edge g e.
Proof.
  intros.
  apply prepend_edge in H.
  destruct H.
  assumption.
  apply walk_is_subgraph in H0.
  apply subgraph_edge with (g:=w).
  assumption.
  assumption.
Qed.

Lemma prepend_edge3:
  forall w g e,
  prepend w g = Some e ->
  subgraph w g ->
  List.In e g.
Proof.
  intros.
  apply prepend_edge in H.
  unfold Edge in *.
  destruct H.
  - assumption.
  - unfold subgraph in *.
    unfold Core.subgraph in *.
    unfold Edge in *.
    apply H0.
    assumption.
Qed.

Definition ConsOf (w:list edge) := {e: edge | Walk (Edge g) (e :: w) }.

Definition CycleOf := { c:list edge | Cycle (Edge g) c}.

Definition BuildCycle w := { v: V | HasIncoming w v /\ StartsWith w v }.

Lemma choose_option:
  forall {A} (o:option A),
  sum {x | o = Some x} {_:option A | o = None} .
Proof.
  intros.
  destruct o.
  - refine (inl (Sig_yes a)).
    auto.
  - refine (inr (Sig_yes None)).
    auto.
Defined.

Lemma choose_prepend:
  forall w,
  option {e | prepend w g = Some e}.
Proof.
  intros.
  remember (prepend w g).
  destruct o.
  - refine (Some (Sig_yes e)).
    auto.
  - refine None.
Defined.


Lemma next_edge_ok:
  forall (w:WalkOf) (e:{e | prepend (Sig_take w) g = Some e}),
  ConsOf (Sig_take w).
Proof.
  intros.
  destruct e as (e, H).
  destruct w as (w, (H1, (H2, H3))).
  refine (Sig_yes e).
  apply walk_cons.
  auto.
  intuition.
  apply prepend_edge2 with (w:=w).
  auto.
  intuition.
  apply prepend_walk with (g:=g).
  intuition.
  auto.
Defined.

Definition next_edge (w:WalkOf) : option (ConsOf (Sig_take w)) :=
  match choose_option (prepend (Sig_take w) g) with
    | inl e => Some (next_edge_ok w e)
    | inr _ => None
  end.

Lemma next_edge_nil_inv:
  forall w,
  next_edge w = None ->
  prepend (Sig_take w) g = None.
Proof.
  intros.
  destruct w.
  unfold next_edge in H.
  remember (choose_option (prepend x g)).
  destruct s.
  + inversion H.
  + destruct s.
    assumption.
Qed.

Lemma starts_with_linked:
  forall (e:edge) w,
  w <> nil ->
  Linked e w ->
  StartsWith w (snd e).
Proof.
  intros.
  destruct e.
  compute in H.
  destruct w.
  destruct H. trivial.
  destruct p.
  compute in H0.
  simpl.
  subst.
  apply starts_with_cons.
  auto.
Qed.

Definition try_prepend: forall (w:WalkOf) (e:ConsOf (Sig_take w)),
 sum WalkOf (BuildCycle (Sig_take w)).
Proof.
  intros.
  destruct e as (e, H).
  destruct w as (w, (H1, (H2,H3))).
  destruct (in_dec edge_eq_dec e w).
  - refine (inr (Sig_yes (snd e))).
    split.
    + apply has_incoming_in_snd.
      assumption.
    + inversion H; subst.
      destruct e.
      destruct w.
      inversion i.
      apply starts_with_linked.
      * intuition.
      * assumption.
  - refine (inl (Sig_yes (e :: w))).
    intuition.
    apply NoDup_cons; repeat auto.
    inversion H0.
Defined.

Definition lendiff (w:WalkOf) :=
  set_length edge_eq_dec g - set_length edge_eq_dec (Sig_take w).

Definition build_cycle: forall (w:WalkOf) (v:BuildCycle (Sig_take w)), CycleOf.
Proof.
  intros.
  destruct w as (w, (H1, H2)).
  destruct v as (v, (H3, H4)). 
  refine (Sig_yes (cut v w)).
  apply cycle_def2 with (v:=v).
  apply cut_starts_with; assumption.
  apply cut_ends_with; assumption.
  apply cut_is_walk; repeat auto.
Defined.

Function find_cycle (w:WalkOf)
  {measure lendiff } : option CycleOf :=
  match next_edge w with
    | Some e =>
      match try_prepend w e with
        | inr v => Some (build_cycle w v)
        | inl w' => find_cycle w'
      end
    | None => None
  end.
Proof.
  intros.
  simpl in *.
  destruct e.
  destruct w.
  destruct x.
  simpl in *.
  destruct a.
  destruct (in_dec edge_eq_dec (v, v0)).
  + destruct a; inversion teq0. (* absurd *)
  + destruct a; inversion teq0.
    destruct w'.
    inversion H0.
    unfold lendiff.
    destruct a.
    apply set_length_minus.
    - assumption.
    - assert (Hx:= w0).
      apply walk_is_subgraph in Hx.
      apply subgraph_incl.
      assumption.
Defined.

Lemma find_cycle_total:
  forall (w:WalkOf),
  AllIncoming g ->
  g <> nil ->
  exists w', find_cycle w = Some w'.
Proof.
  intros.
  functional induction (find_cycle w).
  - destruct w as (w, (Hw1, (Hw2, Hw3))).
    destruct v as (v, (Hb1, Hb2)).
    eauto.
  - apply IHo.
  - apply next_edge_nil_inv in e.
    destruct w as (w, (Hw1, (Hw2, Hw3))).
    destruct w.
    contradiction Hw3; trivial. (* absurd *)
    simpl in e.
    remember (get_incoming g (fst e0)).
    destruct l.
    + 
    apply all_incoming_in with (v:=fst e0) in H.
    rewrite has_incoming_neq_nil in H.
    contradiction H; auto.
    unfold In.
    unfold Core.In.
    exists e0.
    destruct e0.
    intuition.
    * inversion Hw1.
      subst.
      auto.
    * apply pair_in_left.
  + inversion e.
Qed.

End FIND_CYCLE.

Theorem all_pos_idegree_impl_cycle:
  forall g (w:list edge),
  AllIncoming g ->
  g <> nil ->
  exists w, Cycle (Edge g) w.
Proof.
  intros.
  destruct g.
  contradiction H0; trivial.
  assert (Walk (Edge (e::g)) (e::nil)).
  assert (Edge (e::g) e).
  apply edge_eq.
  apply edge_to_walk.
  assumption.
  assert (w':WalkOf (e::g)).
  refine (Sig_yes (e::nil)).
  intuition.
  apply NoDup_cons.
  auto.
  apply NoDup_nil.
  inversion H2.
  (* eoa *)
  assert (exists c, find_cycle w' = Some c).
  apply find_cycle_total; repeat auto.
  destruct H2.
  destruct x.
  exists x.
  assumption.
Qed.

Theorem all_pos_odegree_impl_cycle:
  forall g,
  g <> nil ->
  AllOutgoing g ->
  exists w, Cycle (Edge g) w.
Proof.
  intros.
  destruct (exists_has_incoming H0 H) as
  (g', (H1, (H2, (H3, H4)))).
  apply all_pos_idegree_impl_cycle in H3; repeat auto.
  destruct H3.
  exists x.
  apply subgraph_cycle with (g':=g) in H3; repeat auto.
Qed.

End FGRAPHS.

Implicit Arguments Edge.
Implicit Arguments In.
Implicit Arguments subgraph.
Implicit Arguments HasIncoming.
Implicit Arguments HasOutgoing.
