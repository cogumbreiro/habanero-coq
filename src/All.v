Require HJ.Finish.Syntax.
Module F := HJ.Finish.Syntax.
Require Import HJ.Phasers.Phasermap.
Require Import HJ.Vars.
Require Import HJ.Finish.IEF.
Require Import HJ.Common.
Notation fstate := (Map_FID.t phasermap).


Inductive state := mk_state {
  get_finish: F.finish;
  get_fstate: fstate
}.

Definition set_fstate (s:state) (m:fstate)  :=
  mk_state s.(get_finish) m.

Definition put_phasermap (s:state) (f:fid) (m:phasermap) :  state :=
  set_fstate s (Map_FID.add f m s.(get_fstate)).

Definition set_finish (s:state) (f:F.finish) : state :=
  mk_state f s.(get_fstate).

Module Semantics.

Require Import HJ.Phasers.Lang.
Require HJ.Finish.Semantics.
Module FS := HJ.Finish.Semantics.

Inductive op := 
  | BEGIN_ASYNC : phased -> op
  | END_ASYNC
  | BEGIN_FINISH
  | END_FINISH
  | PH_NEW : phid -> op
  | PH_SIGNAL : phid -> op
  | PH_DROP : phid -> op
  | SIGNAL_ALL : op
  | WAIT_ALL : op.

Inductive packet :=
  | only_p: Phasermap.op -> packet
  | only_f: FS.op -> packet
  | both: Phasermap.op -> FS.op -> packet.

Definition translate (o:op) : packet :=
  match o with
  (* Copies registry from spawner and registers task in finish scope of spawner*)
  | BEGIN_ASYNC ps  => both (ASYNC ps) (FS.BEGIN_ASYNC (get_new_task ps))
  (* Drops all phasers and removes task from finish scope *)
  | END_ASYNC => both DROP_ALL FS.END_ASYNC
  (* Pushes a finish scope  *)
  | BEGIN_FINISH => only_f FS.BEGIN_FINISH
  (* Drops all phasers and pops a finish scope *)
  | END_FINISH => both DROP_ALL FS.END_FINISH
  (* Phaser-only operations: *)
  | PH_NEW p => only_p (Phasermap.PH_NEW p)
  | PH_SIGNAL p => only_p (Phasermap.PH_SIGNAL p)
  | PH_DROP p => only_p (Phasermap.PH_DROP p)
  | SIGNAL_ALL => only_p Phasermap.SIGNAL_ALL
  | WAIT_ALL => only_p Phasermap.WAIT_ALL
  end.

Definition as_f_op (o:op) :=
  match translate o with
  | only_f o => Some o
  | both _ o => Some o
  | only_p _ => None
  end.

Lemma translate_only_f_impl_as_f_op:
  forall i o,
  translate i = only_f o ->
  as_f_op i = Some o.
Proof.
  intros; destruct i; try (simpl in *; inversion H); compute; auto.
Qed.

Lemma translate_both_impl_as_f_op:
  forall i o o',
  translate i = both o o' ->
  as_f_op i = Some o'.
Proof.
  intros; destruct i; try (simpl in *; inversion H); compute; auto.
Qed.

Lemma translate_only_p_impl_as_f_op:
  forall i o,
  translate i = only_p o ->
  as_f_op i = None.
Proof.
  intros; destruct i; try (simpl in *; inversion H); compute; auto.
Qed.

Definition as_p_op (o:op) :=
  match translate o with
  | only_p o => Some o
  | both o _ => Some o
  | only_f _ => None
  end.

Lemma as_p_op_some_impl_translate:
  forall i o,
  as_p_op i = Some o ->
  (translate i = only_p o) \/ (exists o', translate i = both o o').
Proof.
  intros.
  unfold as_p_op in H.
  remember (translate _).
  destruct p; try (inversion H; subst; intuition).
  right.
  exists o1.
  trivial.
Qed.

Inductive PhasermapOf (s:state) (t:tid) (l:fid) (m:phasermap) : Prop :=
  phasermap_of:
    forall f',
    IEF t f' ->
    FIDPath f' l (get_finish s) ->
    Map_FID.MapsTo l m s.(get_fstate) ->
    PhasermapOf s t l m.

Definition context := (phasermap * F.finish) % type.
Inductive ContextOf (s:state) (t:tid) : context -> Prop :=
  context_of_def:
    forall f m,
    PhasermapOf s t f m ->
    ContextOf s t (m, (get_finish s)).

Inductive CtxReduce (ctx:context) (t:tid) (o:op) : context -> Prop :=
  | reduce_p:
    forall m o',
    translate o = only_p o' ->
    Phasermap.Reduces (fst ctx) t o' m ->
    CtxReduce ctx t o (m, snd ctx)
  | reduce_f:
    forall f o',
    translate o = only_f o' ->
    FS.Reduce (snd ctx) t o' f ->
    CtxReduce ctx t o (fst ctx, f)
  | reduce_both:
    forall m o_p f o_f,
    translate o = both o_p o_f ->
    Phasermap.Reduces (fst ctx) t o_p m ->
    FS.Reduce (snd ctx) t o_f f ->
    CtxReduce ctx t o (m, f).

Inductive Reduce (s:state) (t:tid) (o:op) : state -> Prop :=
  reduce_def:
    forall f m ctx,
    PhasermapOf s t f m ->
    CtxReduce (m, get_finish s) t o ctx ->
    Reduce s t o (set_finish (put_phasermap s f (fst ctx)) (snd ctx)).

End Semantics.


Module Typesystem.
  Import Semantics.
  Require HJ.Phasers.Typesystem.
  Require HJ.Finish.Typesystem.
  Module P_T := HJ.Phasers.Typesystem.
  Module F_T := HJ.Finish.Typesystem.
  
  Inductive Check (ctx:context) (t:tid): op -> Prop :=
  | check_only_p:
    forall i o,
    translate i = only_p o ->
    P_T.Check (fst ctx) t o ->
    Check ctx t i
  | check_only_f:
    forall i o,
    translate i = only_f o ->
    F_T.Check (snd ctx) t o ->
    Check ctx t i
  | check_both:
    forall i o o',
    translate i = both o o' ->
    F_T.Check (snd ctx) t o' ->
    P_T.Check (fst ctx) t o ->
    Check ctx t i.

  Lemma check_inv_f_check:
    forall p f t i o,
    Check (p, f) t i ->
    as_f_op i = Some o ->
    F_T.Check f t o.
  Proof.
    intros.
    inversion H; (subst; simpl in *).
    - apply translate_only_p_impl_as_f_op in H1.
      rewrite H1 in H0.
      inversion H0.
    - apply translate_only_f_impl_as_f_op in H1.
      rewrite H1 in H0.
      inversion H0.
      subst.
      assumption.
    - apply translate_both_impl_as_f_op in H1.
      rewrite H1 in H0.
      inversion H0.
      subst.
      assumption.
  Qed.

  Lemma check_change_finish:
    forall t f f' i m,
    F.Registered t f ->
    Check (m, f') t i ->
    Check (m, f) t i.
  Proof.
    intros.
    inversion H0; subst; simpl in *.
    - eauto using check_only_p.
    - apply check_only_f with (o); auto.
      simpl.
  Admitted.
End Typesystem.

Require HJ.Phasers.Progress.
Module P_P := HJ.Phasers.Progress.
Require HJ.Finish.Progress.
Module F_P := HJ.Finish.Progress.

Module Progress.
  Import Semantics.
  Import Typesystem.

  Inductive PRequests p reqs : Prop :=
    p_requests_def:
      (forall t o,
        Map_TID.MapsTo t o (P_P.get_requests p) ->
        exists i, Map_TID.MapsTo t i reqs /\ as_p_op i = Some o) ->
      (forall t i o,
        Map_TID.MapsTo t i reqs ->
        as_p_op i = Some o ->
        Map_TID.MapsTo t o (P_P.get_requests p)) ->
      PRequests p reqs.

  Section CtxProgress.
    Variable f:F.finish.
    Variable p:P_P.state.

    Variable reqs: Map_TID.t op.
    Variable reqs_checked : RequestToCheck (Check ((P_P.get_state p),f)) reqs.
    Let ReqsChecked:
      forall t i,
      Map_TID.MapsTo t i reqs -> Check ((P_P.get_state p),f) t i.
    Proof.
      inversion reqs_checked.
      auto.
    Qed.
    Variable p_reqs_spec: PRequests p reqs.

    Let p_reqs_spec_1:
      forall t o,
      Map_TID.MapsTo t o (P_P.get_requests p) ->
      exists i, Map_TID.MapsTo t i reqs /\ as_p_op i = Some o.
    Proof.
      intros.
      inversion p_reqs_spec; eauto.
    Qed.

    Let p_reqs_spec_2:
      forall t i o,
      Map_TID.MapsTo t i reqs ->
      as_p_op i = Some o ->
      Map_TID.MapsTo t o (P_P.get_requests p).
    Proof.
      intros.
      inversion p_reqs_spec; eauto.
    Qed.

    Require Import HJ.Finish.Progress.
    Variable IsFlat:
      Flat f.

    Variable pm_wf:
      Welformedness.Phasermap.Welformed (P_P.get_state p).

    Let progress_only_f:
      forall t i o,
      Map_TID.MapsTo t i reqs ->
      translate i = only_f o ->
      exists f', CtxReduce ((P_P.get_state p), f) t i ((P_P.get_state p), f').
    Proof.
      intros.
      assert (R: exists f', FS.Reduce f t o f'). {
        assert (F_T.Check f t o). {
          eauto using check_inv_f_check, translate_only_f_impl_as_f_op.
        }
        auto using flat_reduces.
      }
      destruct R as (f', R).
      exists f'.
      apply reduce_f with (o); auto.
    Qed.
    
    Let is_p_impl_reqs_f_spec_1:
      (forall t i, Map_TID.MapsTo t i reqs ->  exists o, as_p_op i = Some o) ->
      forall t i,
      Map_TID.MapsTo t i reqs ->
      (exists o, as_p_op i = Some o /\ Map_TID.MapsTo t o (P_P.get_requests p)).
    Proof.
      intros IsP.
      intros.
      assert (Hx := H).
      apply IsP in H.
      destruct H as (o, ?).
      exists o; intuition.
      eauto.
    Qed.

    Let empty_to_f_empty:
      ~ Map_TID.Empty reqs ->
      (forall t i, Map_TID.MapsTo t i reqs ->  exists o, as_p_op i = Some o) ->
      ~ Map_TID.Empty (P_P.get_requests p).
    Proof.
      intros.
      apply Map_TID_Extra.nonempty_in.
      apply Map_TID_Extra.nonempty_in in H.
      destruct H as (k, Hmt).
      apply Map_TID_Extra.in_to_mapsto in Hmt.
      destruct Hmt as (i, Hmt).
      assert (Hx: exists o, as_p_op i = Some o). {
        eauto.
      }
      exists k.
      destruct Hx as (o, Hx).
      eauto using Map_TID_Extra.mapsto_to_in.
    Qed.

    Let progress_all_p:
      ~ Map_TID.Empty reqs ->
      (forall t i, Map_TID.MapsTo t i reqs ->  exists o, as_p_op i = Some o) ->
      exists t i ctx, Map_TID.MapsTo t i reqs /\ CtxReduce ((P_P.get_state p), f) t i ctx.
    Proof.
      intros.
      assert (R : ~ Map_TID.Empty (P_P.get_requests p)) by auto.
      apply P_P.progress in R; auto.
      destruct R as (t, (o_p, (m, R))).
      inversion R.
      exists t.
      apply p_reqs_spec_1 in H1.
      destruct H1 as (i, (?,?)).
      exists i.
      apply as_p_op_some_impl_translate in H3.
      destruct H3 as [?|(o_f, ?)].
      - exists (m, f).
        split; auto.
        apply reduce_p with (o_p); auto.
      - assert (Hx := H3).
        apply translate_both_impl_as_f_op in  H3.
        assert (RF: exists f', FS.Reduce f t o_f f'). {
          assert (F_T.Check f t o_f). {
            apply ReqsChecked in H1.
            eauto using check_inv_f_check.
          }
          auto using flat_reduces.
        }
        destruct RF as (f', RF).
        exists (m, f').
        split;
        eauto using reduce_both.
    Qed.

    Let find_only_f (t:tid) (i:op) : bool :=
      match translate i with
      | only_f _ => true
      | _ => false
      end.
      
    Let find_only_f_to_some:
      forall t i,
      find_only_f t i = true ->
      exists o,  translate i = only_f o.
    Proof.
      intros.
      unfold find_only_f in *.
      remember (translate _) as i'.
      symmetry in Heqi'.
      destruct i'; try (inversion H).
      exists o; trivial.
    Qed.
    
    Let find_none_impl_some_p:
      forall t i,
      find_only_f t i = false ->
      exists o, as_p_op i = Some o.
    Proof.
      intros.
      unfold find_only_f  in H.
      unfold as_p_op.
      remember (translate i) as i'.
      destruct i'.
      - exists o; trivial.
      - inversion H.
      - exists o; trivial.
    Qed.

    Theorem ctx_progress:
      ~ Map_TID.Empty reqs ->
      exists t i ctx, Map_TID.MapsTo t i reqs /\ CtxReduce (P_P.get_state p, f) t i ctx.
    Proof.
      intros.
      destruct (Map_TID_Extra.pred_choice reqs find_only_f)
        as [(t,(i,(?,?)))|?]; auto with *.
      - exists t.
        exists i.
        assert (R: exists f', CtxReduce ((P_P.get_state p), f) t i ((P_P.get_state p), f')). {
          apply find_only_f_to_some in H1.
          destruct H1.
          eauto.
        }
        destruct R as (f', ?).
        exists (P_P.get_state p, f').
        intuition.
     - apply progress_all_p; auto.
       intros.
       apply e in H0.
       eauto using find_none_impl_some_p.
    Qed.
  End CtxProgress.

  Section CtxTrans.
    Import Lang.FinishNotations.
    Open Scope finish_scope.

    Lemma ctx_reduce_le_some:
      forall m f t o o' ctx f',
      CtxReduce (m, f) t o ctx ->
      as_f_op o = Some o' ->
      FS.Disjoint f' o' ->
      f <= f' ->
      exists ctx', CtxReduce (m, f') t o ctx'.
    Proof.
      intros.
      destruct ctx as (m1, f1).
      inversion H; subst; simpl in *.
      - apply translate_only_p_impl_as_f_op in H5.
        rewrite H5 in H0.
        inversion H0.
      - assert (Hx := H5).
        apply translate_only_f_impl_as_f_op in Hx.
        rewrite Hx in H0.
        inversion H0; subst; clear H0.
        apply F_P.reduce_le with (f3:=f') in H6; auto.
        destruct H6 as (f4, R).
        exists (m1, f4).
        apply reduce_f with (o':=o'); simpl; auto.
      - assert (Hx := H5).
        apply translate_both_impl_as_f_op in Hx.
        rewrite H0 in Hx.
        inversion Hx; subst; clear Hx.
        apply F_P.reduce_le with (f3:=f') in H7; auto.
        destruct H7 as (f4, ?).
        exists (m1, f4).
        apply reduce_both with (o_p:=o_p) (o_f:=o_f); simpl; auto.
    Qed.

    Lemma ctx_reduce_le_none:
      forall m f t o ctx f',
      CtxReduce (m, f) t o ctx ->
      as_f_op o = None ->
      exists ctx', CtxReduce (m, f') t o ctx'.
    Proof.
      intros.
      assert (X: exists o', translate o = only_p o'). {
        destruct o; compute in H0; inversion H0; simpl; eauto.
      }
      destruct X as (o_p, X).
      inversion H; simpl in *.
      - rewrite H1 in X.
        inversion X; subst; clear X.
        exists (m0, f').
        apply reduce_p with (o':=o_p); auto.
      - rewrite H1 in X.
        inversion X.
      - rewrite H1 in X.
        inversion X.
    Qed.
  End CtxTrans.

  Section ApplyCtx.
  Variable s: state.
  Require HJ.Finish.Lang.
  Import Lang.FinishNotations.
  Open Scope finish_scope.

  Variable le_to_fid:
    forall f f',
    f <= f' -> exists i, FIDPath f i f'.
  Variable fid_path_le:
    forall f l f',
    FIDPath f l f' ->
    f <= f'.

  Notation ROOT := (get_finish s).

  Variable exists_flat:
    exists f h m,
    FIDPath f h ROOT /\
    Progress.Flat f /\ 
    Map_FID.MapsTo h m (get_fstate s).

  Notation FRequestOf f := (RequestOf (Finish.Typesystem.Check f)).
  Variable request_of_fid:
    forall l f,
    FIDPath f l ROOT ->
    exists r, FRequestOf f r.

  Variable reqs: Map_TID.t op.

  Variable reqs_disjoint:
    forall t o o',
    Map_TID.MapsTo t o reqs ->
    as_f_op o = Some o' ->
    FS.Disjoint ROOT o'.

  Inductive WFContext h f : Prop :=
    get_context_def:
      forall p reqs1 reqs2,
      Map_TID_Props.Partition reqs reqs1 reqs2 ->
      PRequests p reqs1 ->
      RequestToCheck (Check (P_P.get_state p, f)) reqs1 ->
      Welformedness.Phasermap.Welformed (P_P.get_state p) ->
      Map_FID.MapsTo h (P_P.get_state p) (get_fstate s) ->
      (forall t o, Map_TID.MapsTo t o reqs1 -> F.Registered t f) ->
      ~ Map_TID.Empty reqs1 ->
      WFContext h f.

  Variable get_wf_context:
    forall h f,
    FIDPath f h ROOT ->
    WFContext h f.

  Let flat_to_ief:
    forall t f,
    F.Registered t f ->
    Progress.Flat f ->
    IEF t f.
  Proof.
    intros.
    apply ief_def.
    - inversion H0.
      intros.
      inversion H3.
      apply H1 in H4.
      inversion H4.
      subst.
      auto using FS.in_absurd_nil.
    - assumption.
  Qed.

  Theorem progress:
    ~ Map_TID.Empty reqs ->
    exists t i s',
    Map_TID.MapsTo t i reqs /\ Reduce s t i s'.
  Proof.
    intros.
    destruct (exists_flat) as (f, (h, (?,(?,(Hflat,?))))).
    assert (X := H0).
    apply get_wf_context in X.
    destruct X.
    rename H5 into W.
    rename H3 into P.
    rename H4 into R.
    destruct (ctx_progress f p reqs1 R P Hflat W H8) as (t,(o,(ctx,(Rmt,Rctx)))).
    exists t.
    exists o.
    inversion R.
    assert (F.Registered t f) by eauto.
    assert (IEF t f) by eauto.
    assert (Q: PhasermapOf s t h (P_P.get_state p)) by eauto using phasermap_of.
    assert (Map_TID.MapsTo t o reqs). {
      unfold Map_TID_Props.Partition in *.
      destruct H2 as (_,?).
      rewrite H2.
      intuition.
    }
    assert (Rc : exists ctx', CtxReduce (P_P.get_state p, ROOT) t o ctx'). {
      remember (as_f_op o) as o1.
      destruct o1 as [o1|].
      - eauto using ctx_reduce_le_some.
      - eauto using ctx_reduce_le_none.
    }
    destruct Rc as (ctx', Rc).
    eauto using reduce_def.
  Qed.