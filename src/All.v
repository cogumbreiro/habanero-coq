Require HJ.Phasers.Progress.
Require HJ.Phasers.Lang.
Require HJ.Phasers.Typesystem.
Require HJ.Finish.Lang.
Require HJ.Finish.DF.
Require HJ.Phasers.DF.

Require Coq.Lists.List.

Require Import HJ.Tid.
Require Import HJ.Fid.
Require Import HJ.Vars.
Require Import HJ.Phasers.Phasermap.

Module F := HJ.Finish.Lang.
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

  Inductive Valid (ctx:context) (t:tid): op -> Prop :=
  | valid_only_p:
    forall i o,
    translate i = only_p o ->
    P_T.Op.Valid (pm_state (fst ctx)) t o ->
    Valid ctx t i
  | valid_only_f:
    forall i o,
    translate i = only_f o ->
    F.Valid (f_state (snd ctx)) t o ->
    Valid ctx t i
  | valid_both:
    forall i o o',
    translate i = both o o' ->
    F.Valid (f_state (snd ctx)) t o' ->
    P_T.Op.Valid (pm_state (fst ctx)) t o ->
    Valid ctx t i.

  Lemma valid_inv_f_check:
    forall p f t i o,
    Valid (p, f) t i ->
    as_f_op i = Some o ->
    F.Valid (f_state f) t o.
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
  Structure t := make {
    finishes: finish_t;
    phasers: Map_FID.t phasermap_t;
  }.

  Definition empty := {| finishes := Finish.DF.empty; phasers := Map_FID.empty phasermap_t |}.

  Import Progress.
  Import Semantics.

  Inductive GetPhasermap s: (tid*op) -> (fid*phasermap_t) -> Prop :=
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
        eauto using get_phasermap_none.
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

    Lemma get_phasermap_fun:
      forall s a m n,
      GetPhasermap s a m ->
      GetPhasermap s a n ->
      n = m.
    Proof.
      intros.
      apply get_phasermap_to_some in H.
      apply get_phasermap_to_some in H0.
      rewrite H in H0; inversion H0; auto.
    Qed.
  End GetPhasermap_dec.

  Inductive Reduces: t -> (tid*op) -> t -> Prop :=
  | reduces_def:
    forall s x o s' pm' f pm,
    GetPhasermap s (x, o) (f, pm) ->
    Semantics.CtxReduces (pm, (finishes s)) x o (pm', s') ->
    Reduces s (x, o) {|
      finishes := s';
      phasers := Map_FID.add f pm' (phasers s);
    |}.

  Inductive Valid s x o : Prop :=
  | valid_def:
    forall f pm,
    GetPhasermap s (x, o) (f, pm) ->
    Typesystem.Valid (pm, (finishes s)) x o ->
    Valid s x o.

  Definition Nonempty s := (~ Map_TID.Empty (f_state (finishes s))).

End State.

Module P_P := HJ.Phasers.DF.
Module F_P := HJ.Finish.DF.

Module Progress.
  Import Semantics.
  Import Typesystem.
  Import State.

  Definition InclFtoP {elt} fs ps :=
    forall x, F.In x fs -> Map_FID.In (elt:=elt) x ps.

  Definition TaskToFinish ps fs :=
    forall x pm f,
    Map_FID.MapsTo f pm ps ->
    Phasermap.In x (pm_state pm) ->
    F.Bind x f fs \/ F.Open x f fs.

  Section Defs.
  Variable s:State.t.
  Variable spec_1: InclFtoP (f_state (finishes s)) (phasers s).
  Variable spec_2: TaskToFinish (phasers s) (f_state (finishes s)).

  Notation CanReduce s x o := (exists s', Reduces s (x, o) s').

    Let incl_f_to_p:
      forall x,
      F.In x (f_state (finishes s)) ->
      Map_FID.In x (phasers s).
    Proof.
      auto.
    Qed.

    Let task_mem:
      forall x pm f,
      Map_FID.MapsTo f pm (phasers s) ->
      Phasermap.In x (pm_state pm) ->
      F.Bind x f (f_state (finishes s)) \/ F.Open x f (f_state (finishes s)).
    Proof.
      auto.
    Qed.

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
        F.Bind x f fs ->
        Finish.DF.Enabled ffs x.

      Let reduces_f_ex:
        forall o o' x pm,
        F.Bind x f fs ->
        Semantics.translate o = Semantics.only_f o' ->
        F.Valid fs x o' ->
        exists ctx', Semantics.CtxReduces (pm, ffs) x o ctx'.
      Proof.
        intros.
        destruct ief_can_run with (x:=x) (o:=o') as (f', Hr); eauto.
        exists (pm, f').
        eapply Semantics.reduces_f; eauto.
      Qed.

      Let reduces_both:
        forall o o_f o_p x pm pm',
        F.Bind x f fs ->
        Semantics.translate o = Semantics.both o_p o_f ->
        F.Valid fs x o_f ->
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

      Lemma ctx_progress_empty
        (pm_is_empty: Empty pm):
        exists x,
        F.Bind x f fs /\
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
        F.Bind x f fs /\
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
          apply P_P.progress_nonblocking; auto.
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
        F.Bind x f fs /\
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
    assert (GetPhasermap s (x, o) (f, DF.make))
    by auto using get_phasermap_some.
    assert (Hc: exists ctx', CtxReduces (DF.make, finishes s) x o ctx'). {
      remember (DF.make, finishes s) as ctx.
      assert (Hf: exists o_f, translate o = only_f o_f). {
        destruct o; inversion H0; subst; simpl; eauto.
      }
      destruct Hf as (o_f, Hf).
      assert (Hr: exists sf, Finish.DF.Reduces (snd ctx) (x, o_f) sf). { 
        assert (F.Nonblocking o_f). {
          destruct o; inversion H0; subst; simpl in *;
          inversion Hf; subst;
          eauto using F.nonblocking_init, F.nonblocking_begin_finish.
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
        match goal with [ H1: GetPhasermap _ _ ?m1, H2: GetPhasermap _ _ ?m2 |- _ ]
        => 
          assert (Heq: m1 = m2) by eauto using get_phasermap_fun;
          inversion Heq; subst; clear Heq
        end; auto.
      }
      destruct Hr as (fs, Hr).
      exists (fst ctx, fs).
      eauto using reduces_f.
    }
    destruct Hc as ((?,?), Hc).
    eauto using State.reduces_def.
  Qed.

  Theorem progress:
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
    edestruct Finish.DF.progress_ex as (f,[(Hx, (Hy,Hz))|(Hx,(x,(Hy,Hz)))]); eauto. {
      assert (Hc: exists pm, Map_FID.MapsTo f pm (phasers s)). {
        assert (F.In f (f_state (finishes s))) by auto using F.nonempty_to_in.
        auto using Map_FID_Extra.in_to_mapsto.
      }
      destruct Hc as (pm, Hmt).
      (* -- *)
      destruct (ctx_progress _ _  Hmt Hx Hy) as (k, (?, (x, (?,?)))).
      exists k.
      split; auto.
      exists x.
      intros.
      remember (creates_finish o).
      symmetry in Heqo0.
      destruct o0; eauto.
      match goal with H: Valid _ _ _ |- _ => inversion H end.
      assert (pm0 = pm). {
        assert (F.IEF x f (f_state (finishes s))) by auto.
        match goal with H: GetPhasermap _ _ _ |- _ =>
          inversion H; subst; clear H;
          match goal with
            H1: creates_finish _ = _,
            H2: creates_finish _ = _ |- _ =>
            rewrite H1 in H2; inversion H2; clear H2
          end
        end.
        match goal with
        H3: F.IEF _ ?f1 _,
        H4: F.IEF _ ?f2 _ |- _ => assert (f2 = f1) by eauto using F.ief_fun
        end.
        subst.
        match goal with
        H3: Map_FID.MapsTo _ ?m1 _,
        H4: Map_FID.MapsTo _ ?m2 _ |- _ => assert (m2 = m1) by eauto using Map_FID_Facts.MapsTo_fun
        end.
        subst.
        trivial.
      }
      subst.
      assert (Hc: exists ctx', CtxReduces (pm, finishes s) x o ctx') by eauto.
      destruct Hc as ((pm', fs'), Hc).
      eauto using reduces_def.
    }
    (* we can run any operation, but for simplicity sake, let's do finish *)
    exists finish_op.
    split. {
      unfold not; intros N; inversion N.
    }
    exists x.
    intros.
    destruct o; match goal with
      H: get_op_kind _ = _ |- _ => inversion H; subst; clear H
    end. {
      assert (creates_finish (BEGIN_FINISH f0) = Some f0) by auto.
      eauto.
    }
    match goal with H: Valid _ _ ?o |- _ =>
      remember o as of;
      inversion H; subst; clear H
    end;
    match goal with H: Typesystem.Valid _ _ _ |- _ =>
      inversion H; subst; clear H
    end;
    match goal with H: translate _ = _ |- _ =>
      simpl in H; inversion H
    end; subst.
    edestruct Hz as (f', ?); eauto.
    assert (R: exists pm', DF.Reduces (fst (pm, finishes s)) (x, DROP_ALL) pm'). {
      apply P_P.progress_nonblocking; auto.
      unfold not; intros N; inversion N.
    }
    destruct R as (pm', Rp).
    eauto using reduces_def, reduces_both.
  Qed.
End Defs.
End Progress.

Module SR.
Section Defs.
  Let get_phasermap_inv_eq_init:
    forall s x g f pm, 
    State.GetPhasermap s (x, Semantics.INIT g) (f, pm) ->
    g = f.
  Proof.
    intros.
    inversion H; subst; clear H; simpl in *;
    match goal with H: Some _ = _ |- _ => inversion H end.
    trivial.
  Qed.
  Let get_phasermap_inv_eq_begin_finish:
    forall s x g f pm, 
    State.GetPhasermap s (x, Semantics.BEGIN_FINISH g) (f, pm) ->
    g = f.
  Proof.
    intros.
    inversion H; subst; clear H; simpl in *;
    match goal with H: Some _ = _ |- _ => inversion H end.
    trivial.
  Qed.
  Lemma sr_incl_f_to_p:
    forall s s' x o,
    Progress.InclFtoP (f_state (State.finishes s)) (State.phasers s) ->
    State.Reduces s (x, o) s' ->
    Progress.InclFtoP (f_state (State.finishes s')) (State.phasers s').
  Proof.
    intros.
    unfold Progress.InclFtoP in *; intros y; intros.
    inversion H0; subst; clear H0; simpl in *.
    rewrite Map_FID_Facts.add_in_iff.
    match goal with H: Semantics.CtxReduces _ _ _ _ |- _ =>
    inversion H; subst; clear H
    end; simpl in *;
    try (
      match goal with H:F.Reduces _ _ _ |- _ =>
      inversion H; subst; clear H
      end
    );
    try (
    match goal with H:Finish.DF.Reduces _ _ _ |- _ => inversion H; subst; clear H end
    ).
    - auto.
    - edestruct F.reduces_in_inv as [(?,?)|[(?,?)|?]]; eauto 3. (* don't try too hard *)
      + subst.
        destruct o; match goal with H: Semantics.translate _ = _ |- _ =>
          simpl in *;
          inversion H; symmetry in H; subst
        end.
        assert (y = f) by (eapply get_phasermap_inv_eq_init; eauto).
        auto.
      + subst.
        destruct o; match goal with H: Semantics.translate _ = _ |- _ =>
          simpl in *;
          inversion H; symmetry in H; subst
        end.
        assert (y = f) by (eapply get_phasermap_inv_eq_begin_finish; eauto).
        auto.
    - edestruct F.reduces_in_inv as [(?,?)|[(?,?)|?]]; eauto 3; (* whithout this number it gets sluggish *)
      subst;
      destruct o; match goal with H: Semantics.translate _ = _ |- _ =>
        simpl in *;
        inversion H; symmetry in H; subst
      end.
  Qed.

  Let ief_to_root_or_started:
    forall x f s,
    F.IEF x f (f_state (State.finishes s)) ->
    F.Bind x f (f_state (State.finishes s)) \/ F.Open x f (f_state (State.finishes s)).
  Proof.
    intros.
    inversion H; subst; clear H.
    - eauto using F.bind_def.
    - eauto using F.open_def, List.in_eq.
  Qed.

  Let not_in_make:
    forall x,
    ~ In x (pm_state DF.make).
  Proof.
    unfold not; intros x N.
    inversion N; subst; clear N.
    unfold DF.make in *; simpl in *.
    unfold make in *.
    apply Map_PHID_Facts.empty_mapsto_iff in H.
    assumption.
  Qed.

  Lemma sr_task_to_finish:
    forall s s' x o,
    Progress.TaskToFinish (State.phasers s) (f_state (State.finishes s)) ->
    State.Reduces s (x, o) s' ->
    Progress.TaskToFinish (State.phasers s') (f_state (State.finishes s')).
  Proof.
    intros.
    unfold Progress.TaskToFinish in *; intros y pm'; intros.
    inversion H0; subst; clear H0; simpl in *.
    apply Map_FID_Facts.add_mapsto_iff in H1.
    destruct H1 as [(?,?)|(?,?)]; subst. { (* mapsto *)
      match goal with H: State.GetPhasermap _ _ _ |- _ =>
      inversion H; subst; clear H; simpl in *
      end. {
        match goal with H: Semantics.CtxReduces _ _ _ _ |- _ =>
        inversion H; subst; clear H
        end; simpl in *.
        - match goal with H: DF.Reduces _ _ _ |- _ =>
            inversion H; subst; clear H
          end.
          edestruct Phasermap.reduces_in_inv as [(?,(?,?))|[(?,(?,?))|?]]; eauto 4;
          subst;
          destruct o; match goal with
            H: Semantics.translate _ = _ |- _ =>
            inversion H; subst; clear H; auto
          end.
        - match goal with H: Finish.DF.Reduces _ _ _ |- _ =>
          inversion H; subst; clear H end.
          eapply H in H2; eauto.
          eapply F.bind_or_open_reduces in H2; eauto 1.
          destruct H2 as [(Hx,(?,(g,?)))|[(Hx,(?,?))|[(Hx,(?,?))|Hx]]]; subst;
          try (
            match goal with
              H1: Semantics.translate _ = _,
              H2: Semantics.creates_finish _ = _ |- _ =>
              destruct o; inversion H1; subst;
              inversion H2
            end
          ).
        - match goal with H: DF.Reduces _ _ _ |- _ =>
            inversion H; subst; clear H
          end.
          edestruct Phasermap.reduces_in_inv as [(?,(?,?))|[(?,(?,?))|?]]; eauto 4;
          subst;
          destruct o; match goal with
            H: Semantics.translate _ = _ |- _ =>
            inversion H; subst; clear H; auto
          end.
          + eauto using DF.reduces_inv_ief_root.
          + eapply H in H0; eauto.
            match goal with H: Finish.DF.Reduces _ _ _ |- _ =>
            inversion H; subst; clear H end.
            eapply F.bind_or_open_reduces in H0; eauto 1.
            destruct H0 as [(Hx,(?,(g,?)))|[(Hx,(?,?))|[(Hx,(?,?))|Hx]]]; subst;
            try (
              match goal with
                H1: Semantics.translate _ = _,
                H2: Semantics.creates_finish _ = _ |- _ =>
                destruct o; inversion H1; subst;
                inversion H2
              end
            );
            try (inversion H1); auto.
          + eapply H in H0; eauto.
            match goal with H: Finish.DF.Reduces _ _ _ |- _ =>
            inversion H; subst; clear H end.
            eapply F.bind_or_open_reduces in H0; eauto 1.
            destruct H0 as [(Hx,(?,(g,?)))|[(Hx,(?,?))|[(Hx,(?,?))|Hx]]]; subst;
            try (
              match goal with
                H1: Semantics.translate _ = _,
                H2: Semantics.creates_finish _ = _ |- _ =>
                destruct o; inversion H1; subst;
                inversion H2
              end
            );
            try (inversion H1); auto.
            match goal with H: Reduces _ _ _ _ |- _ =>
              apply Phasermap.reduces_drop_all_not_in in H
            end.
            contradiction.
          + eapply H in H0; eauto.
            match goal with H: Finish.DF.Reduces _ _ _ |- _ =>
            inversion H; subst; clear H end.
            eapply F.bind_or_open_reduces in H0; eauto 1.
            destruct H0 as [(Hx,(?,(g,?)))|[(Hx,(?,?))|[(Hx,(?,?))|Hx]]]; subst;
            try (
              match goal with
                H1: Semantics.translate _ = _,
                H2: Semantics.creates_finish _ = _ |- _ =>
                destruct o; inversion H1; subst;
                inversion H2
              end
            );
            try (inversion H1); auto.
            match goal with H: Reduces _ _ _ _ |- _ =>
              apply Phasermap.reduces_drop_all_not_in in H
            end.
            contradiction.
      } (* else of getphasermap *)
      match goal with H: Semantics.creates_finish _ = _ |- _ =>
      destruct o; inversion H; subst; clear H end;
      match goal with H: Semantics.CtxReduces _ _ _ _ |- _ =>
        inversion H; subst; clear H
      end;
      match goal with H: Semantics.translate _ = _ |- _ =>
        inversion H; subst; clear H
      end; simpl in *;
      apply Phasermap.not_in_make in H2; contradiction.
    } (* else of mapsto *)
    match goal with H: State.GetPhasermap _ _ _ |- _ =>
    inversion H; subst; clear H; simpl in *
    end. {
      match goal with H: Semantics.CtxReduces _ _ _ _ |- _ =>
        inversion H; subst; clear H; simpl in *
      end.
      - eauto.
      - match goal with
          H1: Semantics.translate _ = _,
          H2: Semantics.creates_finish _ = _
        |- _ =>
          destruct o; simpl in *; inversion H1; inversion H2
        end.
      - eapply H in H2; eauto.
        match goal with H: Finish.DF.Reduces _ _ _ |- _ =>
        inversion H; subst; clear H end.
        eapply F.bind_or_open_reduces in H2; eauto 1.
        destruct H2 as [(Hx,(?,(g,?)))|[(Hx,(?,?))|[(Hx,(?,?))|Hx]]]; subst;
        try (
          match goal with
            H1: Semantics.translate _ = _,
            H2: Semantics.creates_finish _ = _ |- _ =>
            destruct o; inversion H1; subst;
            inversion H2
          end
        ); auto.
        + assert (f0 = f). {
            assert (F.IEF x f (f_state (State.finishes s))). {
              match goal with H: Lang.Reduces _ _ _ |- _ =>
              inversion H; subst; clear H
              end.
              simpl in *.
              assert (f1 = f). {
                inversion Hx; subst; clear Hx.
                match goal with
                  H1: Map_TID.MapsTo x ?a _,
                  H2: Map_TID.MapsTo x ?b _ |- _ =>
                assert (R: a = b) by eauto using Map_TID_Facts.MapsTo_fun; subst;
                inversion R; subst; clear R
                end.
                trivial.
              }
              subst; auto using F.ief_nil.
            }
            eauto using F.ief_fun.
          }
          contradiction.
        + assert (f0 = f). {
            assert (F.IEF x f (f_state (State.finishes s))). {
              match goal with H: Lang.Reduces _ _ _ |- _ =>
              inversion H; subst; clear H
              end.
              simpl in *.
              eauto using F.ief_cons.
            }
            eauto using F.ief_fun.
          }
          contradiction.
    }
    match goal with H: Semantics.creates_finish _ = _ |- _ =>
    destruct o; inversion H; subst; clear H end;
    match goal with H: Semantics.CtxReduces _ _ _ _ |- _ =>
      inversion H; subst; clear H
    end;
    match goal with H: Semantics.translate _ = _ |- _ =>
      inversion H; subst; clear H
    end; simpl in *;
    match goal with H: Finish.DF.Reduces _ _ _ |- _ =>
    inversion H; subst; clear H end;
    match goal with H: F.Reduces _ _ _ |- _ =>
    assert (Hr := H);
    eapply F.bind_or_open_reduces in H ; eauto;
    destruct H as [(Hx,(?,(g,?)))|[(Hx,(?,?))|[(Hx,(?,?))|Hx]]]; subst
    end; try inversion H4; subst; auto.
    apply F.bind_to_in in Hx.
    inversion Hr; subst.
    contradiction.
  Qed.
End Defs.
End SR.

Import Coq.Lists.List.

Module Trace.

  Definition t := (list (tid * Semantics.op)) % type.

  Inductive ReducesN: State.t -> t -> Prop :=
  | reduces_n_nil:
    ReducesN State.empty nil
  | reduces_n_cons:
    forall t l o s s',
    ReducesN s l ->
    State.Reduces s (t, o) s' ->
    ReducesN s' ((t,o)::l).

End Trace.


Module DF.
Section Defs.

  Structure t := {
    state : State.t;
    history : Trace.t;
    spec: Trace.ReducesN state history
  }.

  (** A typed reduction *)

  Inductive Reduces: t -> (tid*Semantics.op) -> t -> Prop :=
  | reduces_def:
    forall t o s1 s2,
    State.Reduces (state s1) (t, o) (state s2) ->
    history s2 = (t,o)::(history s1) ->
    Reduces s1 (t, o) s2.

  Let incl_f_to_p_aux:
    forall h s,
    Trace.ReducesN s h ->
    Progress.InclFtoP (f_state (State.finishes s)) (State.phasers s).
  Proof.
    induction h; intros; simpl in *. {
      inversion H; subst; clear H.
      unfold Progress.InclFtoP; intros.
      apply F.not_in_empty in H.
      contradiction.
    }
    inversion H; subst; clear H.
    apply IHh in H3; clear IHh.
    eauto using SR.sr_incl_f_to_p.
  Qed.

  Let incl_f_to_p:
    forall s,
    Progress.InclFtoP (f_state (State.finishes (state s))) (State.phasers (state s)).
  Proof.
    intros.
    destruct s; simpl in *.
    eauto.
  Qed.

  Let task_to_finish_aux:
    forall h s,
    Trace.ReducesN s h ->
    Progress.TaskToFinish (State.phasers s) (f_state (State.finishes s)).
  Proof.
    induction h; intros;
    inversion H; subst; clear H. {
      unfold Progress.TaskToFinish; intros.
      unfold State.empty in *; simpl in *.
      rewrite Map_FID_Facts.empty_mapsto_iff in *.
      contradiction.
    }
    apply IHh in H3; clear IHh.
    eauto using SR.sr_task_to_finish.
  Qed.

  Let task_to_finish:
    forall s,
    Progress.TaskToFinish (State.phasers (state s)) (f_state (State.finishes (state s))).
  Proof.
    intros.
    destruct s; simpl in *.
    eauto.
  Qed.

  Theorem progress:
    forall (s:t),
    State.Nonempty (state s) ->
    exists k,
    k <> Semantics.task_op /\
    (exists x,
      forall o, Semantics.get_op_kind o = k ->
      State.Valid (state s) x o -> exists s', Reduces s (x, o) s').
  Proof.
    intros.
    edestruct Progress.progress as (k, (?,(x,Hx))); eauto.
    exists k.
    split; auto.
    exists x; intros.
    edestruct Hx as (s', Hr); eauto 1.
    assert (R: Trace.ReducesN s' ((x,o)::history s)). {
      eapply Trace.reduces_n_cons; eauto using spec.
    }
    exists ({| state := s'; history := (x,o)::history s; spec:= R|}).
    eapply reduces_def; simpl; auto.
  Qed.

End Defs.
End DF.
