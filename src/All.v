Require HJ.Phasers.Progress.
Require HJ.Phasers.Lang.
Require HJ.Phasers.Typesystem.
Require HJ.Finish.Syntax2.

Require Import HJ.Vars.
Require Import HJ.Phasers.Phasermap.

Module F := HJ.Finish.Syntax2.

Notation fstate := (Map_FID.t phasermap_t).


Inductive state := mk_state {
  get_finish: F.state;
  get_fstate: fstate
}.

Definition set_fstate (s:state) (m:fstate)  :=
  mk_state s.(get_finish) m.

Definition put_phasermap (s:state) (f:fid) (m:phasermap_t) :  state :=
  set_fstate s (Map_FID.add f m s.(get_fstate)).

Definition set_finish (s:state) (f:F.state) : state :=
  mk_state f s.(get_fstate).

Module Semantics.
  Import HJ.Phasers.Lang.

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

  Inductive op_kind :=
  | phaser_op
  | finish_op
  | task_op.

  Definition get_op_kind (o:op) :=
  match o with
  | PH_NEW _
  | PH_SIGNAL _
  | PH_DROP _
  | SIGNAL_ALL
  | WAIT_ALL => phaser_op
  | BEGIN_FINISH
  | END_FINISH => finish_op
  | _  => task_op
  end.

  Definition is_finish_op (o:op) :=
  match o with
  end.

  Inductive packet :=
  | only_p: Phasermap.op -> packet
  | only_f: F.op -> packet
  | both: Phasermap.op -> F.op -> packet.

  Definition translate (o:op) : packet :=
  match o with
  (* Copies registry from spawner and registers task in finish scope of spawner*)
  | BEGIN_ASYNC ps  => both (ASYNC ps) (F.ASYNC (get_new_task ps))
  (* Drops all phasers and removes task from finish scope *)
  | END_ASYNC => both DROP_ALL F.END
  (* Pushes a finish scope  *)
  | BEGIN_FINISH => only_f F.FINISH
  (* Drops all phasers and pops a finish scope *)
  | END_FINISH => both DROP_ALL F.AWAIT
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

  Definition context := (phasermap_t * F.state) % type.

  (* XXX: before a await on f, the task must not hold any phasers held by f *)

  Inductive CtxReduces (ctx:context) (t:tid) (o:op) : context -> Prop :=
  | reduces_p:
    forall m o',
    translate o = only_p o' ->
    Phasermap.ReducesT (fst ctx) (t, o') m ->
    CtxReduces ctx t o (m, snd ctx)
  | reduces_f:
    forall f o',
    translate o = only_f o' ->
    F.Reduces (snd ctx) (t, o') f ->
    CtxReduces ctx t o (fst ctx , f)
  | reduces_both:
    forall m o_p f o_f,
    translate o = both o_p o_f ->
    Phasermap.ReducesT (fst ctx) (t, o_p) m ->
    F.Reduces (snd ctx) (t, o_f) f ->
    CtxReduces ctx t o (m, f).

End Semantics.

Module Typesystem.
  Import Semantics.
  Module P_T := HJ.Phasers.Typesystem.
  Module P_R := HJ.Phasers.SubjectReduction.
  Module F_T := HJ.Finish.Syntax2.

  Inductive Valid (ctx:context) (t:tid): op -> Prop :=
  | valid_only_p:
    forall i o,
    translate i = only_p o ->
    P_T.Op.Valid (Phasermap.state (fst ctx)) t o ->
    Valid ctx t i
  | valid_only_f:
    forall i o,
    translate i = only_f o ->
    F_T.Valid (snd ctx) t o ->
    Valid ctx t i
  | valid_both:
    forall i o o',
    translate i = both o o' ->
    F_T.Valid (snd ctx) t o' ->
    P_T.Op.Valid (Phasermap.state (fst ctx)) t o ->
    Valid ctx t i.

  Lemma valid_inv_f_check:
    forall p f t i o,
    Valid (p, f) t i ->
    as_f_op i = Some o ->
    F_T.Valid f t o.
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

End Typesystem.

Module P_P := HJ.Phasers.Progress.
(*Require HJ.Finish.Progress.*)
Module F_P := HJ.Finish.Syntax2.

Module Progress.
  Import Semantics.
  Import Typesystem.

  Section CtxProgress.

    (** Given the id of a IEF *)
    Variable ief: fid.

    (** Let [ief] have a type [f]. *)
    Variable f:F.state.
    Variable ief_defined:
      F.In ief f.

    (** Let [p] be the phaser map of [f]. *)
    Variable p:phasermap_t.
    Let ctx := (p, f).

    (** For the sake of progress, say that state [f] is nonemty *)
    Variable nonempty:
       ~ Map_TID.Empty f.

    (** Assume that [f] is a DAG *)
    (* XXX: Q1: Shouldn't it suffice for [f] to be well typed? *)
    Variable IsDAG: DAG.DAG (F.FEdge f).

    (** Say that any task in the phaser map is either the root task or
      started in [f]. *)
    (* XXX: Q1: Shouldn't this be part of the notion of well-typed? *)
    Variable task_mem:
      forall t pm,
      Phasermap.In t pm ->
      F.Root t ief f \/ F.Started t ief f.

    Let reduces_t:
      forall o pm t,
      Reduces (Phasermap.state p) t o pm ->
      exists pm_t, ReducesT p (t, o) pm_t.
    Proof.
      intros.
      assert (Hr: ReducesN pm ( (t,o)::(history p))%list ). {
        destruct p; eauto using reduces_n_cons.
      }
      exists {|
        Phasermap.state := pm;
        history := ((t,o)::(history p))%list;
        phasermap_spec := Hr
      |}.
      apply reduces_t_def; subst; auto.
    Qed.

    Let reduces_p_ex:
      forall o o' pm' t,
      Semantics.translate o = Semantics.only_p o' ->
      Reduces (Phasermap.state p) t o' pm' ->
      exists ctx', Semantics.CtxReduces ctx t o ctx'.
    Proof.
      intros.
      assert (R: exists pm_t, ReducesT p (t, o') pm_t) by eauto.
      destruct R as (pm_t, ?).
      exists (pm_t, snd ctx).
      eapply Semantics.reduces_p; eauto.
    Qed.


    Section Case1.
      (** Case 1 of the proof: every task in [ief] that typechecks can execute *)
      Variable ief_nonempty: F.Nonempty ief f.
      Variable ief_can_run:
        forall t o,
        F.Root t ief f ->
        F.Valid f t o ->
        exists f', F.Reduces f (t, o) f'.

      Let reduces_f_ex:
        forall o o' t,
        F.Root t ief f ->
        Semantics.translate o = Semantics.only_f o' ->
        F_T.Valid (snd ctx) t o' ->
        exists ctx', Semantics.CtxReduces ctx t o ctx'.
      Proof.
        intros.
        destruct ief_can_run with (t:=t) (o:=o') as (f', Hr); auto.
        exists (fst ctx, f').
        eapply Semantics.reduces_f; eauto.
      Qed.

      Let reduces_both:
        forall o o_f o_p t pm',
        F.Root t ief f ->
        Semantics.translate o = Semantics.both o_p o_f ->
        F_T.Valid (snd ctx) t o_f ->
        Reduces (Phasermap.state p) t o_p pm' ->
        exists ctx', Semantics.CtxReduces ctx t o ctx'.
      Proof.
        intros.
        assert (R: exists pm_t, ReducesT p (t, o_p) pm_t) by eauto.
        destruct R as (pm_t, ?).
        destruct ief_can_run with (t:=t) (o:=o_f) as (f', Hr); auto.
        exists (pm_t, f').
        eapply Semantics.reduces_both; eauto.
      Qed.

      Let ctx_progress_aux (nonempty_tids:
          LEDec.pm_tids (Phasermap.state p) <> nil):
        exists (k:op_kind),
        k <> task_op /\
        exists t,
        forall o,
        get_op_kind o = k ->
        Valid ctx t o ->
        exists ctx', Semantics.CtxReduces ctx t o ctx'.
      Proof.
        destruct p as (pm, l, ?).
        simpl in *.
        eapply P_P.progress_ex in nonempty_tids; eauto.
        destruct nonempty_tids as (t, (Hi, ?)).
        apply task_mem in Hi.
        destruct Hi. {
          exists phaser_op.
          split. {
            unfold not; intros N; inversion N.
          }
          exists t; intros.
          match goal with H: Valid _ _ _ |- _ =>
            inversion H; subst; clear H
          end.
          - assert (X: exists m, Reduces pm t o0 m) by eauto;
            destruct X; eauto using reduces_p_ex.
          - destruct o; simpl in *; inversion H1; simpl in *; inversion H3.
          - destruct o; simpl in *; inversion H1; simpl in *; inversion H3.
        }
        exists finish_op.
        split. {
          unfold not; intros N; inversion N.
        }
        inversion ief_nonempty.
        exists t0.
        intros.
        destruct o;
        inversion H2;
        inversion H3; subst; simpl in *; inversion H4; subst; clear H4 H2.
        - assert (translate BEGIN_FINISH = only_f F.FINISH) by (simpl; auto).
          eauto.
        - assert (Hp: exists m, Reduces pm t0 DROP_ALL m). {
            apply P_P.progress_unblocking_simple;
             eauto using P_R.reduces_n_to_valid.
            unfold not; intros N; inversion N.
          }
          destruct Hp as (m, Hp).
          assert (Hf: exists g, F.Reduces f (t0, F.AWAIT) g) by eauto.
          destruct Hf as (g, Hf).
          eapply reduces_both; simpl; eauto.
      Qed.

      Lemma ctx_progress_1:
        exists (k:op_kind),
        k <> task_op /\
        exists t,
        forall o,
        get_op_kind o = k ->
        Valid ctx t o ->
        exists ctx', Semantics.CtxReduces ctx t o ctx'.
      Proof.
        assert (E: LEDec.pm_tids (Phasermap.state p) = nil \/ LEDec.pm_tids (Phasermap.state p) <> nil). {
          remember (LEDec.pm_tids _).
          destruct l; auto.
          right.
          unfold not; intros N.
          inversion N.
        }
        destruct E; auto using ctx_progress_aux.
        inversion ief_nonempty.
        apply ctx_progress_aux; auto.
        exists t.
        intros.
        inversion H1; subst; clear H1.
        - apply P_P.progress_empty with (l:=history p) in H3;
          eauto using phasermap_spec.
          destruct H3 as (?, ?).
          eauto.
        - eauto.
        - apply P_P.progress_empty with (l:=history p) in H4;
          eauto using phasermap_spec.
          destruct H4 as (?, ?).
          eauto.
      Qed.
    End Case1.
(*
    Let ctx_progress_1 (ief_nonempty: F.Nonempty ief f)
    (R: forall u o, F.Typecheck f (u, o) -> exists s', F.Reduces f (u, o) s'):
      exists t,
      forall o,
      Valid ctx t o ->
      exists ctx', Semantics.CtxReduces ctx t o ctx'.
    Proof.
      assert (E: LEDec.pm_tids (Phasermap.state p) = nil \/ LEDec.pm_tids (Phasermap.state p) <> nil). {
        remember (LEDec.pm_tids _).
        destruct l; auto.
        right.
        unfold not; intros N.
        inversion N.
      }
      destruct E; auto.
      inversion ief_nonempty.
      exists t.
      intros.
      inversion H1; subst; clear H1.
      - apply P_P.progress_empty with (l:=history p) in H3;
        eauto using phasermap_spec.
        destruct H3 as (?, ?).
        eauto.
      - eauto.
      - apply P_P.progress_empty with (l:=history p) in H4;
        eauto using phasermap_spec.
        destruct H4 as (?, ?).
        eauto.
    Qed.*)
    (*
    Let ctx_progress_empty t (Hs: F.Started t ief f) (ief_empty: F.Empty ief f):
      forall o,
      Valid ctx t o ->
      exists ctx', Semantics.CtxReduces ctx t o ctx'.
    Proof.
      intros.
      assert (E: LEDec.pm_tids (Phasermap.state p) = nil \/ LEDec.pm_tids (Phasermap.state p) <> nil). {
        remember (LEDec.pm_tids _).
        destruct l; auto.
        right.
        unfold not; intros N.
        inversion N.
      }
      destruct E; auto.
      inversion ief_empty.
      exists t.
      intros.
      inversion H1; subst; clear H1.
    Qed.
    *)
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

  Require Import HJ.Finish.LangDec.
  Require Import Coq.Classes.Morphisms.

  Let split_reqs_aux f (t:tid) (o:op) := is_registered t f.
  Program Instance split_reqs_aux_Proper f: Proper (TID.eq ==> eq ==> eq) (split_reqs_aux f) := {
  }.
  Next Obligation.
    auto with *.
  Qed.

  Require Import Aniceto.Option.

  Variable in_pm_in_f:
    forall f t m h,
    FIDPath f h ROOT ->
    Map_FID.MapsTo h m (get_fstate s) ->
    In t (Phasermap.state m) ->
    F.Registered t f.

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

  Variable root_nonempty:
    F_P.Nonempty ROOT.

  Theorem progress:
    exists t h f m,
    FIDPath f h ROOT /\
    Map_FID.MapsTo h m (get_fstate s) /\
    forall i,
    Valid (m, f) t i ->
    exists c', CtxReduces (m,f) t i c'.
  Proof.
    intros.
    destruct (exists_flat) as (f, (h, (?,(?,(Hflat,?))))); eauto.
    apply ctx_progress with (p:=x) in Hflat; auto.
    destruct Hflat as (t, ?).
    exists t.
    exists h.
    exists f.
    exists x.
    split; auto.
  Qed.
End ApplyCtx.
