Require HJ.Finish.Syntax2.
Module F := HJ.Finish.Syntax2.
Require Import HJ.Phasers.Phasermap.
Require Import HJ.Vars.
(*Require Import HJ.Common.*)
Require HJ.Phasers.Progress.
Require HJ.Phasers.Phasermap.

(*Notation phasermap_t := phasermap.*)
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

Require Import HJ.Phasers.Lang.
(*Require HJ.Finish.Semantics.*)
(*Module FS := HJ.Finish.Semantics.*)

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
(*
Inductive ContextOf (s:state) (t:tid) : context -> Prop :=
  context_of_def:
    forall f l m,
    IEF t f ->
    FIDPath f l (get_finish s) ->
    Map_FID.MapsTo l m s.(get_fstate) ->
    ContextOf s t (m, (get_finish s)).
*)
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
  Require HJ.Phasers.Typesystem.
  Require HJ.Finish.Typesystem.
(*  Import Progress.ProgressSpec.*)
  Module P_T := HJ.Phasers.Typesystem.
  Module F_T := HJ.Finish.Syntax2.

  Inductive Check (ctx:context) (t:tid): op -> Prop :=
  | check_only_p:
    forall i o,
    translate i = only_p o ->
    P_T.Check (Phasermap.state (fst ctx)) t o ->
    Check ctx t i
  | check_only_f:
    forall i o,
    translate i = only_f o ->
    F_T.Typecheck (snd ctx) (t, o) ->
    Check ctx t i
  | check_both:
    forall i o o',
    translate i = both o o' ->
    F_T.Typecheck (snd ctx) (t, o') ->
    P_T.Check (Phasermap.state (fst ctx)) t o ->
    Check ctx t i.

  Lemma check_inv_f_check:
    forall p f t i o,
    Check (p, f) t i ->
    as_f_op i = Some o ->
    F_T.Typecheck f (t, o).
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
(*
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
  Admitted.*)
End Typesystem.

Require HJ.Phasers.Progress.
Module P_P := HJ.Phasers.Progress.
(*Require HJ.Finish.Progress.*)
Module F_P := HJ.Finish.Syntax2.

Module Progress.
  Import Semantics.
  Import Typesystem.

  Section CtxProgress.
    Variable ief: fid.
    Variable f:F.state.
    Variable p:phasermap_t.

    Variable IsDAG: DAG.DAG (F.FEdge f).
    Variable nonempty: 
       ~ Map_TID.Empty f.

    Variable ief_defined:
      F.In ief f.

    Variable task_mem:
      forall t pm,
      Phasermap.In t pm ->
      F.Root t ief f.

    Variable f_prog:
      forall t,
      F.Root t ief f ->
      forall o,
      F.Typecheck f (t, o) -> exists g, F.Reduces f (t, o) g.

    Let ctx := (p, f).

    (*
    Require Import HJ.Finish.Progress.
    Variable IsFlat:
      Flat f.
*)
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

    Let reduces_f_ex:
      forall o o' t,
      F.Root t ief f ->
      Semantics.translate o = Semantics.only_f o' ->
      F_T.Typecheck (snd ctx) (t, o') ->
      exists ctx', Semantics.CtxReduces ctx t o ctx'.
    Proof.
      intros.
      apply f_prog in H1; auto.
      destruct H1 as (f', Hr).
      exists (fst ctx, f').
      eapply Semantics.reduces_f; eauto.
    Qed.

    Let reduces_both:
      forall o o_f o_p t pm',
      F.Root t ief f ->
      Semantics.translate o = Semantics.both o_p o_f ->
      F_T.Typecheck (snd ctx) (t, o_f) ->
      Reduces (Phasermap.state p) t o_p pm' ->
      exists ctx', Semantics.CtxReduces ctx t o ctx'.
    Proof.
      intros.
      assert (R: exists pm_t, ReducesT p (t, o_p) pm_t) by eauto.
      destruct R as (pm_t, ?).
      apply f_prog in H1; auto.
      destruct H1 as (f', Hr).
      exists (pm_t, f').
      eapply Semantics.reduces_both; eauto.
    Qed.

    Let ctx_progress_aux (nonempty_tids:
      LEDec.pm_tids (Phasermap.state p) <> nil):
      exists t,
      forall o,
      Check ctx t o ->
      exists ctx', Semantics.CtxReduces ctx t o ctx'.
    Proof.
      destruct p as (pm, l, ?).
      simpl in *.
      eapply P_P.progress_ex in nonempty_tids; eauto.
      destruct nonempty_tids as (t, (Hi, ?)).
      apply task_mem in Hi.
      exists t.
      intros.
      match goal with H: Check _ _ _ |- _ =>
        inversion H; subst; clear H
      end.
      - assert (X: exists m, Reduces pm t o0 m) by eauto;
        destruct X; eauto.
      - eauto.
      - assert (X: exists m, Reduces pm t o0 m) by eauto;
        destruct X; eauto.
    Qed.

    Lemma ctx_progress:
      exists t,
      forall o,
      Check ctx t o ->
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
(*      inversion H; subst; clear H.*)
      apply in_to_registered in H2; auto.
      exists t.
      intros.
      inversion H1; subst; clear H1.
      - apply P_P.progress_empty with (l:=history p) in H4;
        eauto using phasermap_spec.
        destruct H4 as (?, ?).
        eauto.
      - eauto.
      - apply P_P.progress_empty with (l:=history p) in H5;
        eauto using phasermap_spec.
        destruct H5 as (?, ?).
        eauto.
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
    Check (m, f) t i ->
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
