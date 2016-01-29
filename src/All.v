Require HJ.Finish.Syntax.
Module F := HJ.Finish.Syntax.
Require Import HJ.Phasers.Phasermap.
Require Import HJ.Vars.
Require Import HJ.Finish.IEF.
Require Import HJ.Common.
Require HJ.Phasers.Progress.

Notation phasermap_t := Progress.ProgressSpec.phasermap_t.
Notation fstate := (Map_FID.t phasermap_t).


Inductive state := mk_state {
  get_finish: F.finish;
  get_fstate: fstate
}.

Definition set_fstate (s:state) (m:fstate)  :=
  mk_state s.(get_finish) m.

Definition put_phasermap (s:state) (f:fid) (m:phasermap_t) :  state :=
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

Ltac translate_solver := intros i; intros; destruct i; try (simpl in *; inversion H); compute; auto.

Lemma translate_only_f_impl_as_f_op:
  forall i o,
  translate i = only_f o ->
  as_f_op i = Some o.
Proof.
  translate_solver.
Qed.

Lemma translate_both_impl_as_f_op:
  forall i o o',
  translate i = both o o' ->
  as_f_op i = Some o'.
Proof.
  translate_solver.
Qed.

Lemma translate_only_p_impl_as_f_op:
  forall i o,
  translate i = only_p o ->
  as_f_op i = None.
Proof.
  translate_solver.
Qed.

Definition as_p_op (o:op) :=
  match translate o with
  | only_p o => Some o
  | both o _ => Some o
  | only_f _ => None
  end.

Lemma translate_only_p_impl_as_p_op:
  forall i o,
  translate i = only_p o ->
  as_p_op i = Some o.
Proof.
  translate_solver.
Qed.

Lemma translate_both_impl_as_p_op:
  forall i o o',
  translate i = both o o' ->
  as_p_op i = Some o.
Proof.
  translate_solver.
Qed.

Lemma translate_only_f_impl_as_p_op:
  forall i o,
  translate i = only_f o ->
  as_p_op i = None.
Proof.
  translate_solver.
Qed.

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

Definition context := (phasermap_t * F.finish) % type.

Inductive ContextOf (s:state) (t:tid) : context -> Prop :=
  context_of_def:
    forall f l m,
    IEF t f ->
    FIDPath f l (get_finish s) ->
    Map_FID.MapsTo l m s.(get_fstate) ->
    ContextOf s t (m, (get_finish s)).

Import Progress.ProgressSpec.

Inductive CtxReduces (ctx:context) (t:tid) (o:op) : context -> Prop :=
  | reduces_p:
    forall m o',
    translate o = only_p o' ->
    Phasermap.Reduces (pm_t_value (fst ctx)) t o' (pm_t_value m) ->
    CtxReduces ctx t o (m, snd ctx)
  | reduces_f:
    forall f o',
    translate o = only_f o' ->
    FS.Reduce (snd ctx) t o' f ->
    CtxReduces ctx t o (fst ctx , f)
  | reduces_both:
    forall m o_p f o_f,
    translate o = both o_p o_f ->
    Phasermap.Reduces (pm_t_value (fst ctx)) t o_p (pm_t_value m) ->
    FS.Reduce (snd ctx) t o_f f ->
    CtxReduces ctx t o (m, f).

End Semantics.


Module Typesystem.
  Import Semantics.
  Require HJ.Phasers.Typesystem.
  Require HJ.Finish.Typesystem.
  Import Progress.ProgressSpec.
  Module P_T := HJ.Phasers.Typesystem.
  Module F_T := HJ.Finish.Typesystem.
  
  Inductive Check (ctx:context) (t:tid): op -> Prop :=
  | check_only_p:
    forall i o,
    translate i = only_p o ->
    P_T.Check (pm_t_value (fst ctx)) t o ->
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
    P_T.Check (pm_t_value (fst ctx)) t o ->
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

  Import P_P.ProgressSpec.

  Inductive ProgressArg reqs m : Prop :=
    | some_f_req:
      forall  t i o,
      Map_TID.MapsTo t i reqs ->
      translate i = only_f o ->
      ProgressArg reqs m
    | only_p_req:
      forall (r:pm_request (pm_t_value m)),
      (forall t i, Map_TID.MapsTo t i reqs -> exists o, as_p_op i = Some o  /\ Map_TID.MapsTo t o (pm_request_value r)) ->
      (forall t o, Map_TID.MapsTo t o (pm_request_value r) -> exists i, as_p_op i = Some o /\ Map_TID.MapsTo t i reqs) ->
      ~ Map_TID.Empty reqs ->
      ProgressArg reqs m.

  Section CtxProgress.
    Import P_P.ProgressSpec.

    Variable f:F.finish.
    Variable p:phasermap_t.
    Let pm := pm_t_value p.

    Variable reqs: Map_TID.t op.
    Variable hp: ProgressArg reqs p.

    Let ctx := (p, f).

    Variable ReqsChecked:
      forall t i,
      Map_TID.MapsTo t i reqs -> Check ctx t i.

    Require Import HJ.Finish.Progress.
    Variable IsFlat:
      Flat f.

    Let pm_wf:
      Welformedness.Phasermap.WellFormed pm.
    Proof.
      destruct p.
      eauto.
    Qed.

    Let progress_only_f:
      forall t i o,
      Map_TID.MapsTo t i reqs ->
      translate i = only_f o ->
      exists f', CtxReduces ctx t i (p, f').
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
      apply reduces_f with (o); auto.
    Qed.

    Let is_p_impl_reqs_f_spec_1 (r:pm_request pm):
      (forall t i, Map_TID.MapsTo t i reqs ->  exists o, as_p_op i = Some o /\ Map_TID.MapsTo t o (pm_request_value r)) ->
      forall t i,
      Map_TID.MapsTo t i reqs ->
      (exists o, as_p_op i = Some o /\ Map_TID.MapsTo t o (pm_request_value r)).
    Proof.
      intros IsP.
      intros.
      assert (Hx := H).
      apply IsP in H.
      destruct H as (o, ?).
      exists o; intuition.
    Qed.

    Let empty_to_f_empty (r:pm_request pm):
      ~ Map_TID.Empty reqs ->
      (forall t i, Map_TID.MapsTo t i reqs ->  exists o, as_p_op i = Some o /\ Map_TID.MapsTo t o (pm_request_value r)) ->
      ~ Map_TID.Empty (pm_request_value r).
    Proof.
      intros.
      apply Map_TID_Extra.nonempty_in.
      apply Map_TID_Extra.nonempty_in in H.
      destruct H as (k, Hmt).
      apply Map_TID_Extra.in_to_mapsto in Hmt.
      destruct Hmt as (i, Hmt).
      apply H0 in Hmt.
      exists k.
      destruct Hmt as (o, (_,Hx)).
      eauto using Map_TID_Extra.mapsto_to_in.
    Qed.

    Let progress_all_p
      (r:pm_request pm)
      (p_reqs_spec_1:
        forall t o, Map_TID.MapsTo t o (pm_request_value r) ->
        exists i, as_p_op i = Some o /\ Map_TID.MapsTo t i reqs):
      ~ Map_TID.Empty reqs ->
      (forall t i, Map_TID.MapsTo t i reqs ->  exists o, as_p_op i = Some o  /\ Map_TID.MapsTo t o (pm_request_value r)) ->
      exists t i ctx', Map_TID.MapsTo t i reqs /\ CtxReduces ctx t i ctx'.
    Proof.
      intros.
      destruct (progress r) as (t, (o_p, (m, (mt, R)))).
      exists t.
      inversion R.
      apply p_reqs_spec_1 in mt.
      destruct mt as (i, (Hx,mt)).
      exists i.
      apply as_p_op_some_impl_translate in Hx.
      destruct Hx as [?|(o_f, Hx)].
      - exists (m, f).
        split; auto.
        apply reduces_p with (o_p); auto.
      - assert (Hy := Hx).
        apply translate_both_impl_as_f_op in Hx.
        assert (RF: exists f', FS.Reduce f t o_f f'). {
          assert (F_T.Check f t o_f) by
          eauto using check_inv_f_check.
          auto using flat_reduces.
        }
        destruct RF as (f', RF).
        exists (m, f').
        split;
        eauto using reduces_both.
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
      exists t i ctx', Map_TID.MapsTo t i reqs /\ CtxReduces ctx t i ctx'.
    Proof.
      intros.
      destruct hp.
      - exists t.
        exists i.
        assert (Hc : exists f', CtxReduces ctx t i (p, f')) by eauto.
        destruct Hc as (f', Hc).
        eauto.
      - apply progress_all_p with (r:=r); eauto.
    Qed.
  End CtxProgress.

  Section CtxTrans.
    Import Lang.FinishNotations.
    Open Scope finish_scope.

    Lemma ctx_reduce_le_some:
      forall m f t o o' ctx f',
      CtxReduces (m, f) t o ctx ->
      as_f_op o = Some o' ->
      FS.Disjoint f' o' ->
      f <= f' ->
      exists ctx', CtxReduces (m, f') t o ctx'.
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
        apply reduces_f with (o':=o'); simpl; auto.
      - assert (Hx := H5).
        apply translate_both_impl_as_f_op in Hx.
        rewrite H0 in Hx.
        inversion Hx; subst; clear Hx.
        apply F_P.reduce_le with (f3:=f') in H7; auto.
        destruct H7 as (f4, ?).
        exists (m1, f4).
        apply reduces_both with (o_p:=o_p) (o_f:=o_f); simpl; auto.
    Qed.

    Lemma ctx_reduce_le_none:
      forall m f t o ctx f',
      CtxReduces (m, f) t o ctx ->
      as_f_op o = None ->
      exists ctx', CtxReduces (m, f') t o ctx'.
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
        apply reduces_p with (o':=o_p); auto.
      - rewrite H1 in X.
        inversion X.
      - rewrite H1 in X.
        inversion X.
    Qed.
  End CtxTrans.

  Section ApplyCtx.
  Variable s: state.
  Require HJ.Finish.Lang.
  Require HJ.Finish.Semantics.
  Import Lang.FinishNotations.
  Open Scope finish_scope.


  Notation ROOT := (get_finish s).

  Variable finish_t_spec_2: UniqueIEF ROOT.
  Variable finish_t_spec_1: IEFFun ROOT.

  Variable get_fstate_spec:
    forall x l,
    FIDPath x l ROOT ->
    exists m, Map_FID.MapsTo l m (get_fstate s).

  Let exists_flat:
    F_P.Nonempty ROOT ->
    exists f h m,
    FIDPath f h ROOT /\
    Progress.Flat f /\ 
    Map_FID.MapsTo h m (get_fstate s).
  Proof.
    intros.
    apply F_P.find_flat in H.
    destruct H as (x, (Hf, Hr)).
    exists x.
    apply le_to_fid_path in Hr.
    destruct Hr as (p, Hp).
    exists p.
    assert (Hx := Hp).
    apply get_fstate_spec in Hx.
    destruct Hx as (m, Hx).
    exists m.
    intuition.
  Qed.

  Variable reqs: Map_TID.t op.

  Require Import HJ.Finish.LangDec.
  Require Import Coq.Classes.Morphisms.

  Let split_reqs_aux f (t:tid) (o:op) := is_registered t f.
  Program Instance split_reqs_aux_Proper f: Proper (TID.eq ==> eq ==> eq) (split_reqs_aux f) := {
  }.
  Next Obligation.
    auto with *.
  Qed.
    
  Let restrict f := fst (Map_TID_Props.partition (split_reqs_aux f) reqs).

  Variable in_reqs:
    forall t,
    FS.In t ROOT ->
    Map_TID.In t reqs.

  Let maspto_restrict:
    forall f h t,
    FIDPath f h ROOT ->
    F.Registered t f ->
    (exists o, Map_TID.MapsTo t o (restrict f) /\ Map_TID.MapsTo t o reqs).
  Proof.
    intros.
    assert (Hin: Map_TID.In t reqs). {
      assert (FS.In t ROOT). {
        assert (f <= ROOT) by eauto using fid_path_to_le.
        eauto using FS.in_def.
      }
      eauto.
    }
    apply Map_TID_Extra.in_to_mapsto in Hin.
    destruct Hin as (o,mt).
    exists o.
    intuition.
    unfold restrict.
    rewrite Map_TID_Props.partition_iff_1 with (f:=split_reqs_aux f) (m:=reqs); auto using split_reqs_aux_Proper.
    intuition.
    unfold split_reqs_aux.
    auto using is_registered_from_prop.
  Qed.
  
  Let mapsto_restrict_2:
    forall t o f,
    Map_TID.MapsTo t o (restrict f) ->
    Map_TID.MapsTo t o reqs.
  Proof.
    intros.
    unfold restrict in *.
    rewrite Map_TID_Props.partition_iff_1 in H; eauto.
    - intuition.
    - auto using split_reqs_aux_Proper.
  Qed.

  Let mapsto_restruct_3:
    forall t o f,
    Map_TID.MapsTo t o reqs ->
    F.Registered t f ->
    Map_TID.MapsTo t o (restrict f).
  Proof.
    intros.
    unfold restrict in *.
    rewrite Map_TID_Props.partition_iff_1  with (m:=reqs) (f:=split_reqs_aux f); auto.
    - intuition.
      unfold split_reqs_aux.
      auto using is_registered_from_prop.
    - auto using split_reqs_aux_Proper.
  Qed.

  Let in_restrict:
    forall f t m h,
    FIDPath f h ROOT ->
    Map_FID.MapsTo h m (get_fstate s) ->
    Map_TID.In t (restrict f) ->
    F.Registered t f.
  Proof.
    intros.
    apply Map_TID_Extra.in_to_mapsto in H1.
    destruct H1 as (o, mt).
    unfold restrict in *.
    rewrite Map_TID_Props.partition_iff_1  with (m:=reqs) (f:=split_reqs_aux f) in mt;
    auto using split_reqs_aux_Proper.
    destruct mt as (mt, C).
    unfold split_reqs_aux in *.
    auto using is_registered_to_prop.
  Qed.

  Require Import Aniceto.Option.

  Let is_f_req (t:tid) (o:op) :=
    match translate o with
    | only_f _ => true
    | _ => false
    end.

  Let is_f_req_to_prop:
    forall t o,
    is_f_req t o = true ->
    exists o', translate o = only_f o'.
  Proof.
    intros.
    unfold is_f_req in *.
    destruct (translate o); try inversion H.
    eauto.
  Qed.

  Let to_p_reqs_aux (t:tid) := as_p_op.
  Let to_p_reqs r := Map_TID_Extra.omap to_p_reqs_aux r.

  Variable in_pm_in_f:
    forall f t m h,
    FIDPath f h ROOT ->
    Map_FID.MapsTo h m (get_fstate s) ->
    In t (pm_t_value m) ->
    F.Registered t f.

  Let p_reqs_spec_1_1:
    forall f t m h,
    FIDPath f h ROOT ->
    Map_FID.MapsTo h m (get_fstate s) ->
    In t (pm_t_value m) ->
    (exists o, Map_TID.MapsTo t o reqs /\ F.Registered t f).
  Proof.
    intros.
    assert (F.Registered t f) by eauto.
    assert (FS.In t ROOT). {
      eauto using FS.in_def, fid_path_to_le.
    }
    assert (Hin: Map_TID.In t reqs) by auto.
    apply Map_TID_Extra.in_to_mapsto in Hin.
    destruct Hin as (o, mt).
    eauto.
  Qed.

  Variable p_reqs_spec_2:
    forall f t m h o,
    FIDPath f h ROOT ->
    Map_FID.MapsTo h m (get_fstate s) ->
    Map_TID.MapsTo t o reqs ->
    Check (m, ROOT) t o.    

  Let is_f_req_as_p_op:
    forall t o,
    is_f_req t o = false ->
    exists o', as_p_op o = Some o'.
  Proof.
    intros.
    remember (translate o) as x.
    symmetry in Heqx.
    destruct x as [x|x|].
    - eauto using translate_only_p_impl_as_p_op.
    - unfold is_f_req in *.
      rewrite Heqx in *.
      inversion H.
    - eauto using translate_both_impl_as_p_op.
  Qed.

  Let to_p_reqs_restrict_1:
    forall t o f h m,
    FIDPath f h ROOT ->
    Map_FID.MapsTo h m (get_fstate s) ->
    Map_TID.MapsTo t o (to_p_reqs (restrict f)) ->
    exists o', as_p_op o' = Some o /\ Map_TID.MapsTo t o' (restrict f).
  Proof.
    intros.
    unfold to_p_reqs in *.
    unfold to_p_reqs_aux in *.
    apply Map_TID_Extra.omap_2 in H1; auto using tid_eq_rw.
  Qed.

  Variable Hn: ~ Map_TID.Empty reqs.

  Let get_reqs_for:
    forall f h m,
    FIDPath f h ROOT ->
    Map_FID.MapsTo h m (get_fstate s) ->
    F_P.Flat f ->
    ProgressArg (restrict f) m.
  Proof.
    intros.
    destruct (Map_TID_Extra.pred_choice (restrict f) is_f_req); auto with *.
    - destruct e as (t, (o, (mt, Hx))).
      apply is_f_req_to_prop in Hx.
      destruct Hx as (o', Hx).
      eauto using some_f_req.
    - remember (to_p_reqs (restrict f)) as r.
      assert (S1: forall t, In t (pm_t_value m) -> Map_TID.In t r). {
        intros.
        apply p_reqs_spec_1_1 with (h:=h) (f:=f) in H2; eauto.
        destruct H2 as (o, (mt, Hc)).
        assert (mt_r: Map_TID.MapsTo t o (restrict f)) by eauto.
        subst.
        assert (Hx: exists x, Map_TID.MapsTo t x (to_p_reqs (restrict f))). {
          assert (Hx: exists x, as_p_op o = Some x) by eauto.
          destruct Hx as (x, Hx).
          exists x.
          unfold to_p_reqs.
          eauto using tid_eq_rw, Map_TID_Extra.omap_1.
        }
        destruct Hx as (x, Hx).
        eauto using Map_TID_Extra.mapsto_to_in.
      }
      assert (S2: forall t i, Map_TID.MapsTo t i r ->
                        Phasers.Typesystem.Check (pm_t_value m) t i). {
        intros.
        subst.
        apply to_p_reqs_restrict_1 with (h:=h) (m:=m) in H2; auto.
        destruct H2 as (o, (He, mt)).
        assert (Hc: Check (m,ROOT) t o) by eauto.
        inversion Hc; subst.
        - simpl in *.
          assert (o0 = i). {
            apply translate_only_p_impl_as_p_op in H2.
            rewrite H2 in He.
            inversion He; auto.
          }
          subst; auto.
        - apply translate_only_f_impl_as_p_op in H2.
          rewrite H2 in He; inversion He.
        - simpl in *.
          assert (o0 = i). {
            apply translate_both_impl_as_p_op in H2.
            rewrite H2 in He.
            inversion He; auto.
          }
          subst; auto.
      }
      assert (S3: ~ Map_TID.Empty r). {
        assert (Hf: exists t, F.Registered t f). {
          inversion H1.
          inversion H3.
          subst.
          eauto using Progress.in_to_registered.
        }
        destruct Hf as (t, Hf).
        assert (mt: exists o, Map_TID.MapsTo t o (restrict f)). {
          assert (mt: exists o : op, Map_TID.MapsTo t o reqs). {
            assert (Hin: FS.In t ROOT). {
              eauto using FS.in_def, fid_path_to_le.
            }
            apply in_reqs in Hin.
            auto using Map_TID_Extra.in_to_mapsto.
          }
          destruct mt as (o, mt).
          eauto.
        }
        destruct mt as (o, mt).
        assert (Hx: exists x, Map_TID.MapsTo t x r). {
          subst.
          assert (Hx: exists x, as_p_op o = Some x) by eauto.
          destruct Hx as (x, Hx).
          exists x.
          unfold to_p_reqs.
          eauto using tid_eq_rw, Map_TID_Extra.omap_1.
        }
        rewrite Map_TID_Extra.nonempty_in.
        destruct Hx as (x, Hx).
        exists t.
        eauto using Map_TID_Extra.mapsto_to_in.
      }
      remember (Build_pm_request S1 S2 S3) as pr.
      apply only_p_req with (r:=pr); subst; simpl in *.
      + intros.
        assert (Hx: exists x, Map_TID.MapsTo t x (to_p_reqs (restrict f))). {
          subst.
          assert (Hx: exists x, as_p_op i = Some x) by eauto.
          destruct Hx as (x, Hx).
          exists x.
          unfold to_p_reqs.
          eauto using tid_eq_rw, Map_TID_Extra.omap_1.
        }
        destruct Hx as (x, mt).
        exists x.
        assert (Hx:=mt).
        apply to_p_reqs_restrict_1 with (h:=h) (m:=m) in mt; auto.
        destruct mt as (o', (?, mt)).
        intuition.
        assert (o' = i). {
          assert (Map_TID.MapsTo t i reqs) by eauto.
          eauto using Map_TID_Facts.MapsTo_fun.
        }
        subst.
        assumption.
      + intros.
        apply to_p_reqs_restrict_1 with (h:=h) (m:=m) in H2; auto.
      + apply Map_TID_Extra.nonempty_in in S3.
        destruct S3 as (t, Hin).
        rewrite Map_TID_Extra.nonempty_in.
        apply Map_TID_Extra.in_to_mapsto in Hin.
        destruct Hin as (o, mt).
        apply to_p_reqs_restrict_1 with (h:=h) (m:=m) in mt; auto.
        destruct mt as (o', (?, mt)).
        exists t.
        eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Let f_check_flat:
    forall f h t o i m,
    FIDPath f h ROOT ->
    IEF t f ->
    Map_FID.MapsTo h m (get_fstate s) ->
    Map_TID.MapsTo t i reqs ->
    Check (m, ROOT) t i ->
    as_f_op i = Some o ->
    F_T.Check ROOT t o ->
    F_T.Check f t o.
  Proof.
    intros.
    inversion H5.
    assert (f <= ROOT) by eauto using fid_path_to_le.
    apply check_ief with (x:=ROOT); auto.
  Qed.

  Let check_flat:
    forall f h t i m,
    FIDPath f h ROOT ->
    IEF t f ->
    Map_FID.MapsTo h m (get_fstate s) ->
    Map_TID.MapsTo t i reqs ->
    Check (m, ROOT) t i ->
    Check (m, f) t i.
  Proof.
    intros.
    inversion H3; subst; simpl in *.
    - eauto using check_only_p.
    - eauto using check_only_f, translate_only_f_impl_as_f_op.
    - eauto using check_both, translate_both_impl_as_f_op.
  Qed.

  Let flat_to_ief:
    forall t f,
    F.Registered t f ->
    Progress.Flat f ->
    IEF t f.
  Proof.
    intros.
    destruct H.
    destruct a as [|x].
    - auto using ief_ready.
    - apply ief_blocked with (x:=x); auto.
      destruct H0.
      apply H0 in H.
      inversion H.
      auto using F.registered_absurd_nil.
  Qed.

  Variable reqs_to_in:
     forall t o,
     Map_TID.MapsTo t o reqs ->
     FS.In t ROOT.

  Let root_nonempty:
    ~ Map_TID.Empty reqs ->
    F_P.Nonempty ROOT.
  Proof.
    intros.
    apply Map_TID_Extra.nonempty_in in H.
    destruct H as (t, Hin).
    apply Map_TID_Extra.in_to_mapsto in Hin.
    destruct Hin as (o, mt).
    eauto using F_P.nonempty_def.
  Qed.

  Let progress_arg_nonempty:
    forall r m,
    ProgressArg r m ->
    ~ Map_TID.Empty r.
  Proof.
    intros.
    inversion H.
    - rewrite Map_TID_Extra.nonempty_in.
      eauto using Map_TID_Extra.mapsto_to_in.
    - assumption.
  Qed.

  Theorem progress:
    exists t i h f m c',
    Map_TID.MapsTo t i reqs /\
    FIDPath f h ROOT /\
    Map_FID.MapsTo h m (get_fstate s) /\
    CtxReduces (m,f) t i c'.
  Proof.
    intros.
    destruct (exists_flat) as (f, (h, (?,(?,(Hflat,?))))); eauto.
    assert (Hx: ProgressArg (restrict f) x) by eauto.
    apply ctx_progress with (f:=f) in Hx; eauto.
    - destruct Hx as (t, (i, (ctx', (mt, Hc)))).
      repeat eexists; intuition; eauto.
    - intros.
      assert (IEF t f) by eauto using Map_TID_Extra.mapsto_to_in.
      eauto.
  Qed.
End ApplyCtx.
