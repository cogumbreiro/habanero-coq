Require HJ.Phasers.Progress.
Require HJ.Phasers.Lang.
Require HJ.Phasers.Typesystem.
Require HJ.Finish.Syntax2.
Require HJ.Finish.DF.
Require HJ.Phasers.DF.

Require Import HJ.Vars.
Require Import HJ.Phasers.Phasermap.

Module F := HJ.Finish.Syntax2.
Module P := HJ.Phasers.Lang.

Notation finish_t := Finish.DF.t.
Notation phasermap_t := Phasers.DF.t.
Notation pm_state := Phasers.DF.state.
Notation f_state := Finish.DF.state.

Module Semantics.
  Import HJ.Phasers.Lang.

  Inductive op :=
  | INIT: fid -> op
  | BEGIN_ASYNC : phased -> op
  | END_ASYNC
  | BEGIN_FINISH: fid -> op
  | END_FINISH: fid -> op
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
  | INIT _
  | BEGIN_ASYNC _
  | END_ASYNC => task_op
  | BEGIN_FINISH _ 
  | END_FINISH _ => finish_op
  | PH_NEW _
  | PH_SIGNAL _
  | PH_DROP _
  | SIGNAL_ALL
  | WAIT_ALL => phaser_op
  end.

  Inductive packet :=
  | only_p: Phasermap.op -> packet
  | only_f: F.op -> packet
  | both: Phasermap.op -> F.op -> packet.

  Definition translate (o:op) : packet :=
  match o with
  | INIT f => only_f (F.INIT f)
  (* Copies registry from spawner and registers task in finish scope of spawner*)
  | BEGIN_ASYNC ps => both (ASYNC ps) (F.BEGIN_TASK (get_new_task ps))
  (* Drops all phasers and removes task from finish scope *)
  | END_ASYNC => both DROP_ALL F.END_TASK
  (* Pushes a finish scope  *)
  | BEGIN_FINISH f => only_f (F.BEGIN_FINISH f)
  (* Drops all phasers and pops a finish scope *)
  | END_FINISH f => both DROP_ALL (F.END_FINISH f)
  (* Phaser-only operations: *)
  | PH_NEW p => only_p (Phasermap.PH_NEW p)
  | PH_SIGNAL p => only_p (Phasermap.PH_SIGNAL p)
  | PH_DROP p => only_p (Phasermap.PH_DROP p)
  | SIGNAL_ALL => only_p Phasermap.SIGNAL_ALL
  | WAIT_ALL => only_p Phasermap.WAIT_ALL
  end.

  Definition creates_finish (o:op) :=
  match o with
  | INIT f => Some f
  | BEGIN_FINISH f => Some f
  | _ => None
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

  Definition context := (phasermap_t * finish_t) % type.

  (* XXX: before a await on f, the task must not hold any phasers held by f *)

  Inductive CtxReduces (ctx:context) (t:tid) (o:op) : context -> Prop :=
  | reduces_p:
    forall m o',
    translate o = only_p o' ->
    Phasers.DF.Reduces (fst ctx) (t, o') m ->
    CtxReduces ctx t o (m, snd ctx)
  | reduces_f:
    forall f o',
    translate o = only_f o' ->
    Finish.DF.Reduces (snd ctx) (t, o') f ->
    CtxReduces ctx t o (fst ctx , f)
  | reduces_both:
    forall m o_p f o_f,
    translate o = both o_p o_f ->
    Phasers.DF.Reduces (fst ctx) (t, o_p) m ->
    Finish.DF.Reduces (snd ctx) (t, o_f) f ->
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
    P_T.Op.Valid (pm_state (fst ctx)) t o ->
    Valid ctx t i
  | valid_only_f:
    forall i o,
    translate i = only_f o ->
    F_T.Valid (f_state (snd ctx)) t o ->
    Valid ctx t i
  | valid_both:
    forall i o o',
    translate i = both o o' ->
    F_T.Valid (f_state (snd ctx)) t o' ->
    P_T.Op.Valid (pm_state (fst ctx)) t o ->
    Valid ctx t i.

  Lemma valid_inv_f_check:
    forall p f t i o,
    Valid (p, f) t i ->
    as_f_op i = Some o ->
    F_T.Valid (f_state f) t o.
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


Module State.

  Definition InclFtoP {elt} fs ps :=
    forall x, F.In x fs -> Map_FID.In (elt:=elt) x ps.

  Definition InclPtoF {elt} ps fs :=
    forall x, Map_FID.In (elt:=elt) x ps -> F.In x fs.

  Definition TaskToFinish ps fs :=
    forall x pm f,
    Map_FID.MapsTo f pm ps ->
    Phasermap.In x (pm_state pm) ->
    F.Root x f fs \/ F.Started x f fs.

  Structure t := make {
    finishes: finish_t;
    phasers: Map_FID.t phasermap_t;
  }.

(*
  Lemma incl_f_to_p:
    forall (s:t),
    forall x,
    F.In x (f_state (finishes s)) ->
    Map_FID.In x (phasers s).
  Proof.
    intros.
    apply spec_1; auto.
  Qed.

  Lemma incl_p_to_f:
    forall (s:t),
    forall x,
    Map_FID.In x (phasers s) ->
    F.In x (f_state (finishes s)).
  Proof.
    intros.
    apply spec_2; auto.
  Qed.

  Lemma task_mem:
    forall (s:t),
    forall x pm f,
    Map_FID.MapsTo f pm (phasers s) ->
    Phasermap.In x (pm_state pm) ->
    F.Root x f (f_state (finishes s)) \/ F.Started x f (f_state (finishes s)).
  Proof.
    intros.
    eapply spec_3 in H; eauto.
  Qed.
*)
  Import Progress.
  Import Semantics.
  Module F := Syntax2.

  Inductive GetPhasermap s: (tid*op) -> (fid * phasermap_t) -> Prop :=
  | get_phasermap_none:
    forall x o f pm,
    F.IEF x f (f_state (finishes s)) ->
    Map_FID.MapsTo f pm (phasers s) ->
    creates_finish o = None ->
    GetPhasermap s (x,o) (f, pm)
  | get_phasermap_some:
    forall x o f,
    Semantics.creates_finish o = Some f ->
    GetPhasermap s (x, o) (f, DF.make).

  Definition get_phasermap s (a:tid*op) :=
  let (x, o) := a in
  match creates_finish o with
  | None =>
    match F.get_ief x (f_state (finishes s)) with
    | Some f =>
      match Map_FID.find f (phasers s) with
      | Some m => Some (f, m)
      | _ => None
      end
    | _ => None
    end
  | Some f => Some (f, DF.make)
  end.

  Section GetPhasermap_dec.

    Lemma some_to_get_phasermap:
      forall s a m,
      get_phasermap s a = Some m -> GetPhasermap s a m.
    Proof.
      unfold get_phasermap; intros.
      destruct a as (x,o).
      remember (creates_finish _).
      symmetry in Heqo0.
      destruct o0. {
        inversion H; subst.
        eauto using get_phasermap_some.
      }
      remember (F.get_ief x _).
      symmetry in Heqo1.
      destruct o0. {
        apply F.some_to_ief in Heqo1.
        destruct (Map_FID_Extra.find_rw f (phasers s)) as [(R,?)|(?,(R,?))];
        rewrite R in *; inversion H; subst; clear H.
        auto using get_phasermap_none.
      }
      inversion H.
    Qed.

    Let get_phasermap_inv_none_ief:
      forall s x o m,
      GetPhasermap s (x, o) m ->
      creates_finish o = None ->
      exists f, F.IEF x f (f_state (finishes s)).
    Proof.
      intros.
      inversion H; subst; clear H. {
        eauto.
      }
      match goal with [
        H1: creates_finish _ = None,
        H2: creates_finish _ = Some _ |- _
      ] => rewrite H1 in *; inversion H2
      end.
    Qed.

    Lemma get_phasermap_to_some:
      forall s a m,
      GetPhasermap s a m -> get_phasermap s a  = Some m.
    Proof.
      intros; unfold get_phasermap.
      destruct a.
      remember (creates_finish o).
      destruct o0. {
        inversion H; subst; clear H;
          match goal with [
            H1: creates_finish _ = _,
            H2: _ = creates_finish _ |- _ 
          ] => rewrite H1 in *; inversion H2
          end.
        subst.
        trivial.
      }
      remember (F.get_ief _ _).
      symmetry in Heqo1.
      destruct o0. {
        match goal with H: F.get_ief _ _ = _ |- _ => apply F.some_to_ief in H end.
        inversion H; subst; clear H. {
          assert (f0 = f) by eauto using F.ief_fun; subst.
          match goal with
          H: Map_FID.MapsTo _ _ _ |- _ =>
            apply Map_FID_Facts.find_mapsto_iff in H; rewrite H
          end.
          trivial.
        }
        match goal with [
          H1: creates_finish _ = _,
          H2: _ = creates_finish _ |- _ 
        ] => rewrite H1 in *; inversion H2
        end.
      }
      edestruct get_phasermap_inv_none_ief as (f, Hx); eauto.
      contradict Hx.
      auto using F.none_to_not_ief.
    Qed.
  End GetPhasermap_dec.

  Inductive GetContext s a : (fid*context) -> Prop :=
  | get_context_def:
    forall f pm,
    GetPhasermap s a (f, pm) ->
    GetContext s a (f, (pm, finishes s)).

  Definition get_context s a :=
  match get_phasermap s a with
  | Some (f, pm) => Some (f, (pm, finishes s))
  | _ => None
  end.

  Section GetContext_dec.
    Lemma get_context_to_some:
      forall s a ctx,
      GetContext s a ctx ->
      get_context s a = Some ctx.
    Proof.
      intros.
      inversion H; subst; clear H.
      unfold get_context.
      apply get_phasermap_to_some in H0.
      rewrite H0.
      trivial.
    Qed.

    Lemma some_to_get_context:
      forall s a ctx,
      get_context s a = Some ctx ->
      GetContext s a ctx.
    Proof.
      intros.
      unfold get_context in *.
      remember (get_phasermap _ _).
      symmetry in Heqo.
      destruct o. {
        apply some_to_get_phasermap in Heqo.
        inversion H; subst; clear H.
        destruct p.
        match goal with
        H: Some _ = Some _ |- _ => inversion H; subst
        end.
        auto using get_context_def.
      }
      inversion H.
    Qed.

    Lemma get_context_fun:
      forall s a ctx ctx',
      GetContext s a ctx ->
      GetContext s a ctx' ->
      ctx' = ctx.
    Proof.
      intros.
      apply get_context_to_some in H.
      apply get_context_to_some in H0.
      rewrite H in *.
      inversion H0.
      auto.
    Qed.
  End GetContext_dec.

  Inductive Reduces: t -> (tid*op) -> t -> Prop :=
  | reduces_def:
    forall s x o s' pm' f ctx (*S1 S2 S3*),
    GetContext s (x, o) (f, ctx) ->
    Semantics.CtxReduces ctx x o (pm', s') ->
    Reduces s (x, o) {|
      finishes := s';
      phasers := Map_FID.add f pm' (phasers s);
      (*spec_1 := S1; spec_2:=S2; spec_3:=S3*)
    |}.
(*
  Section SR.
    Lemma ctx_to_reduces:
      forall s x o f ctx pm' fs',
      GetContext s (x, o) (f, ctx) ->
      Semantics.CtxReduces ctx x o (pm', fs') ->
      exists S1 S2 S3,
      Reduces s (x, o) {|
        finishes := fs';
        phasers := Map_FID.add f pm' (phasers s);
        spec_1 := S1; spec_2:=S2; spec_3:=S3
      |}.
    Proof.
      intros.
      inversion H0; subst; clear H0.
      - 
    Qed.
  End SR.
*)
  Inductive Valid s x o : Prop :=
  | valid_def:
    forall f ctx,
    GetContext s (x, o) (f, ctx) ->
    Typesystem.Valid ctx x o ->
    Valid s x o.

  Definition Nonempty s := (~ Map_TID.Empty (f_state (finishes s))).
(*
  Section Props.

    Definition get_context s a :=
    
  
    Lemma get_context_fun:
  End Props.*)
End State.

Module P_P := HJ.Phasers.DF.
(*Require HJ.Finish.Progress.*)
Module F_P := HJ.Finish.DF.

Module Progress.
  Import Semantics.
  Import Typesystem.
  Import State.
  Section Defs.
  Variable s:State.t.
  Variable spec_1: InclFtoP (f_state (finishes s)) (phasers s).
  Variable spec_2: InclPtoF (phasers s) (f_state (finishes s)).
  Variable spec_3: TaskToFinish (phasers s) (f_state (finishes s)).

  Notation CanReduce s x o := (exists s', Reduces s (x, o) s').

  Section CtxProgress.

    (** Given the id of a IEF *)
    Variable f: fid.

    (** Let [ief] have a type [f]. *)
    Notation ffs := (State.finishes s).
    Notation fs := (f_state ffs).
    Variable ief_defined:
      F.In f fs.
    Variable p : phasermap_t.
    Variable mt: Map_FID.MapsTo f p (phasers s).
    Notation pm := (pm_state p).

    (** Let [p] be the phaser map of [f]. *)
    Let ctx : context := (p, ffs).

    (** For the sake of progress, say that state [f] is nonemty *)
    Variable nonempty:
       ~ Map_TID.Empty fs.

    Let incl_f_to_p:
      forall x,
      F.In x (f_state (finishes s)) ->
      Map_FID.In x (phasers s).
    Proof.
      auto.
    Qed.

    Let incl_p_to_f:
      forall x,
      Map_FID.In x (phasers s) ->
      F.In x (f_state (finishes s)).
    Proof.
      auto.
    Qed.

    Let task_mem:
      forall x pm f,
      Map_FID.MapsTo f pm (phasers s) ->
      Phasermap.In x (pm_state pm) ->
      F.Root x f (f_state (finishes s)) \/ F.Started x f (f_state (finishes s)).
    Proof.
      auto.
    Qed.

    (** Say that any task in the phaser map is either the root task or
      started in [f]. *)

    Let reduces_p_ex:
      forall o o' pm pm' x,
      Semantics.translate o = Semantics.only_p o' ->
      Phasers.DF.Reduces pm (x, o') pm' ->
      exists ctx', Semantics.CtxReduces (pm, ffs) x o ctx'.
    Proof.
      intros.
      assert (R: exists pm_t, Phasers.DF.Reduces pm (x, o') pm_t) by eauto.
      destruct R as (pm_t, ?).
      eexists.
      eapply Semantics.reduces_p; eauto.
    Qed.

    Section Case1.
      (** Case 1 of the proof: every task in [ief] that typechecks can execute *)
      Variable ief_nonempty: F.Nonempty f fs.
      Variable ief_can_run:
        forall x,
        F.Root x f fs ->
        Finish.DF.Enabled ffs x.

      Let reduces_f_ex:
        forall o o' x pm,
        F.Root x f fs ->
        Semantics.translate o = Semantics.only_f o' ->
        F_T.Valid fs x o' ->
        exists ctx', Semantics.CtxReduces (pm, ffs) x o ctx'.
      Proof.
        intros.
        destruct ief_can_run with (x:=x) (o:=o') as (f', Hr); eauto.
        exists (pm, f').
        eapply Semantics.reduces_f; eauto.
      Qed.

      Let reduces_both:
        forall o o_f o_p x pm pm',
        F.Root x f fs ->
        Semantics.translate o = Semantics.both o_p o_f ->
        F_T.Valid fs x o_f ->
        Phasers.DF.Reduces pm (x, o_p) pm' ->
        exists ctx', Semantics.CtxReduces (pm, ffs) x o ctx'.
      Proof.
        intros.
        assert (R: exists pm_t, Phasers.DF.Reduces pm (x, o_p) pm_t) by eauto.
        destruct R as (pm_t, ?).
        destruct ief_can_run with (x:=x) (o:=o_f) as (f', Hr); auto.
        exists (pm_t, f').
        eapply Semantics.reduces_both; eauto.
      Qed.

      Let ctx_progress_empty
        (pm_is_empty: Empty pm):
        exists x,
        Syntax2.Root x f fs /\
        (forall o,
        Typesystem.Valid ctx x o ->
        exists ctx', Semantics.CtxReduces ctx x o ctx').
      Proof.
        inversion ief_nonempty.
        exists x; split; auto.
        intros.
        inversion H0; subst.
        - apply Phasers.DF.progress_empty with (x:=x) in pm_is_empty.
          unfold DF.Enabled in *.
          edestruct pm_is_empty; eauto.
          eapply reduces_p_ex; eauto.
        - eapply reduces_f_ex; eauto.
        - apply Phasers.DF.progress_empty with (x:=x) in pm_is_empty.
          unfold DF.Enabled in *.
          edestruct pm_is_empty; eauto.
          eapply reduces_both; eauto.
      Qed.

      Let ctx_progress_nonempty (nonempty_tids: Phasermap.Nonempty pm):
        exists (k:op_kind),
        k <> task_op /\
        exists x,
        Syntax2.Root x f fs /\
        (forall o,
        get_op_kind o = k ->
        Typesystem.Valid ctx x o ->
        exists ctx', Semantics.CtxReduces ctx x o ctx').
      Proof.
        simpl in *.
        eapply Phasers.DF.progress in nonempty_tids.
        destruct nonempty_tids as (y, (Hi, Hd)).
        unfold DF.Enabled in *.
        eapply task_mem in Hi; eauto.
        destruct Hi. {
          exists phaser_op.
          split. {
            unfold not; intros N; inversion N.
          }
          exists y; split; auto; intros.
          match goal with H: Typesystem.Valid _ _ _ |- _ =>
            inversion H; subst; clear H
          end.
          - edestruct Hd; eauto; eapply reduces_p_ex; eauto.
          - eauto; eapply reduces_f_ex; eauto.
          - edestruct Hd; eauto; eapply reduces_both; eauto.
        }
        exists finish_op.
        split. {
          unfold not; intros N; inversion N.
        }
        inversion ief_nonempty.
        exists x; split; auto.
        intros ? ? Hv.
        inversion Hv; subst; simpl in *;
        destruct o; simpl in *;
        inversion H1; inversion H2; subst; clear H2. {
          assert (Hx: exists s', Finish.DF.Reduces ffs (x, F.BEGIN_FINISH f0) s'). {
            auto using F.nonblocking_begin_finish, Finish.DF.progress_nonblocking.
          }
          destruct Hx as (s', Hx).
          exists (fst ctx, s').
          eapply reduces_f; eauto.
          simpl; auto.
        }
        assert (Hp: exists m, DF.Reduces p (x, DROP_ALL) m). {
          apply DF.progress_unblocking; auto.
          unfold not; intros N; inversion N.
        }
        assert (Finish.DF.Enabled ffs x) by auto.
        unfold Finish.DF.Enabled in *.
        destruct Hp as (m, Hp).
        assert (Hf: exists g, Finish.DF.Reduces ffs (x, F.END_FINISH f0) g) by auto.
        destruct Hf as (g, Hf).
        eapply reduces_both; simpl; eauto.
      Qed.

      Lemma ctx_progress:
        exists (k:op_kind),
        k <> task_op /\
        exists x,
        Syntax2.Root x f fs /\
        (forall o,
          get_op_kind o = k ->
          Typesystem.Valid ctx x o ->
          exists ctx', Semantics.CtxReduces ctx x o ctx').
      Proof.
        destruct (LEDec.empty_nonempty_dec (pm_state p));
          auto using ctx_progress_nonempty.
        exists phaser_op.
        split. {
          unfold not; intros N; inversion N.
        }
        edestruct ctx_progress_empty as (x, (?,?)); eauto.
      Qed.
    End Case1.
  End CtxProgress.

  Import State.

  Let progress_push_finish:
    forall x o f,
    Valid s x o ->
    creates_finish o = Some f ->
    CanReduce s x o.
  Proof.
    intros.
    assert (GetContext s (x, o) (f, (DF.make, finishes s)))
    by auto using get_context_def, get_phasermap_some.
    assert (Hc: exists ctx', CtxReduces (DF.make, finishes s) x o ctx'). {
      remember (DF.make, finishes s) as ctx.
      assert (Hf: exists o_f, translate o = only_f o_f). {
        destruct o; inversion H0; subst; simpl; eauto.
      }
      destruct Hf as (o_f, Hf).
      assert (Hr: exists sf, Finish.DF.Reduces (snd ctx) (x, o_f) sf). { 
        assert (Syntax2.Nonblocking o_f). {
          destruct o; inversion H0; subst; simpl in *;
          inversion Hf; subst;
          eauto using Syntax2.nonblocking_init, Syntax2.nonblocking_begin_finish.
        }
        inversion H; subst.
        apply Finish.DF.progress_nonblocking; simpl; auto.
        destruct o; inversion H0; subst; simpl in *;
        inversion Hf; subst;
        match goal with H: Typesystem.Valid _ _ _ |- _ =>
          inversion H; subst; clear H
        end;
        match goal with H1: translate _ = _ |- _ =>
          simpl in H1; inversion H1
        end;
        match goal with [ H1: GetContext _ _ ?c1, H2: GetContext _ _ ?c2 |- _ ]
        => 
          assert (Heq :c1 = c2) by eauto using get_context_fun;
          inversion Heq; subst; clear Heq
        end;
        auto.
      }
      destruct Hr as (fs, Hr).
      exists (fst ctx, fs).
      eauto using reduces_f.
    }
    destruct Hc as ((?,?), Hc).
    eauto using State.reduces_def.
  Qed.

  Theorem progress:
    forall (s:State.t),
    Nonempty s ->
    exists (k:op_kind),
    k <> task_op /\
    exists x,
    forall o,
    get_op_kind o = k ->
    Valid s x o ->
    exists s', Reduces s (x, o) s'.
  Proof.
    intros.
    edestruct Finish.DF.progress_ex as (f,[(Hx, (Hy,Hz))|Hx]); eauto. {
      assert (Hc: exists pm, Map_FID.MapsTo f pm (phasers s)). {
        assert (F.In f (f_state (finishes s))) by auto using Syntax2.nonempty_to_in.
        auto using Map_FID_Extra.in_to_mapsto, incl_f_to_p.
      }
      destruct Hc as (pm, Hmt).
      (* -- *)
      destruct (ctx_progress _ _ _ Hmt Hx Hy) as (k, (?, (x, (?,?)))).
      exists k.
      split; auto.
      exists x.
      intros.
      remember (creates_finish o).
      destruct o0. {
        
      }
      assert (Typesystem.Valid (pm, finishes s) x o). {
        match goal with H: State.Valid _ _ _ |- _ =>
          inversion H; subst; clear H
        end.
      }
      (* -- *)
      destruct ctx_progress with (ief:=f) (s:=finishes s) (p:=pm)
        as (k, (?, (x, (root, prog))));
      eauto using spec_3.
      exists k; split; auto.
      exists x.
      intros.
      match goal with [H: Valid _ _ _ |- _] => inversion H; subst end.
      assert (ctx = (pm, finishes s)). {
        destruct ctx as (pm', fs).
        match goal with [H: GetContext _ _ _ |- _] => inversion H; subst; clear H end.
        assert (pm' = pm); subst; auto.
        match goal with [H: GetPhasermap _ _ _ |- _ ] => inversion H; subst; clear H end. {
          assert (f0 = f) by eauto using F.ief_fun.
          subst.
          eauto using Map_FID_Facts.MapsTo_fun.
        }
        destruct o; match goal with H: creates_finish _ = _ |- _ => inversion H; subst end.
        - simpl in *.
          contradiction.
        - simpl in *.
          match goal with H: Typesystem.Valid _ _ _|- _ =>
            inversion H; subst; clear H;
            match goal with H: translate _ = _ |- _ =>
              inversion H; subst; clear H
            end
          end.
          match goal with H: Typesystem.F_T.Valid _ _ _ |- _ =>
            inversion H; subst; clear H
          end.
          match goal with H: ~  Typesystem.F_T.In _ _ |- _ =>
            contradict H
          end.
          
      assert (exists ctx', CtxReduces (pm, finishes s)
    }
  Qed.
End Progress.
    
(*
  Definition set_phasers (s:t) m
    (S1: forall x, F.In x (finishes s) <-> Map_FID.In x m) : t :=
  make (finishes s) m S1.

  Definition set_finishes (s:t) m
    (S1: forall x, F.In x m <-> Map_FID.In x (phasers s)): t :=
  make m (phasers s) S1.

  Definition put_phasermap (s:t) (f:fid) (m:phasermap_t) 
  (S1: forall x, F.In x (finishes s)): t.
  Proof.
    refine (set_phasers s (Map_FID.add f m (phasers s)) _).
    split; intros;
    rewrite Map_FID_Facts.add_in_iff in *.
    - destruct s.
      simpl in *.
      rewrite spec_2 in H.
      auto.
    - destruct H.
      + subst.
        auto.
      + auto.
  Qed.*)
  (*
  Definition set_finish (s:t) (u:tid) (m:F.task)
  (S1: forall x, F.In x (finishes s)): t.
  Proof.
    refine (set_finishes s (Map_TID.add u m (finishes s)) _).
    intros.
    split; intros.
    - apply Map_FID_Facts.add_in_iff in H.
  Qed.
  mk_state f s.(get_fstate).*)
End State.

    Lemma ctx_progress:
      forall ctx,
      exists (k:op_kind),
      k <> task_op /\
      exists t,
      forall o,
      get_op_kind o = k ->
      Valid ctx t o ->
      exists ctx', Semantics.CtxReduces ctx t o ctx'.
    Proof.
      intros.
      F_P.progress
    Qed.

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
