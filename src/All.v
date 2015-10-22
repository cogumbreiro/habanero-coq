Require HJ.AsyncFinish.Syntax.
Module F := HJ.AsyncFinish.Syntax.
Require HJ.Phasers.Lang.
Module P := HJ.Phasers.Lang.
Require Import HJ.Vars.
Require Import HJ.AsyncFinish.IEF.

Notation fstate := (Map_FID.t P.phasermap).


Inductive state := mk_state {
  get_finish: F.finish;
  get_fstate: fstate
}.

Definition set_fstate (s:state) (m:fstate)  :=
  mk_state s.(get_finish) m.

Definition put_phasermap (s:state) (f:fid) (m:P.phasermap) :  state :=
  set_fstate s (Map_FID.add f m s.(get_fstate)).

Definition set_finish (s:state) (f:F.finish) : state :=
  mk_state f s.(get_fstate).

Module Semantics.

Require Import HJ.Phasers.Lang.
Require HJ.AsyncFinish.Semantics.
Module FS := HJ.AsyncFinish.Semantics.

Inductive op := 
  | BEGIN_ASYNC : list phased -> tid -> op
  | END_ASYNC
  | BEGIN_FINISH
  | END_FINISH
  | PH_NEW : phid -> op
  | PH_SIGNAL : phid -> op
  | PH_DROP : phid -> op
  | SIGNAL_ALL : op
  | WAIT_ALL : op.

Inductive packet :=
  | only_p: P.op -> packet
  | only_f: FS.op -> packet
  | both: P.op -> FS.op -> packet.

Definition translate (o:op) : packet :=
  match o with
  (* Copies registry from spawner and registers task in finish scope of spawner*)
  | BEGIN_ASYNC ps t => both (P.ASYNC ps t) (FS.BEGIN_ASYNC t)
  (* Drops all phasers and removes task from finish scope *)
  | END_ASYNC => both P.DROP_ALL FS.END_ASYNC
  (* Pushes a finish scope  *)
  | BEGIN_FINISH => only_f FS.BEGIN_FINISH
  (* Drops all phasers and pops a finish scope *)
  | END_FINISH => both P.DROP_ALL FS.END_FINISH
  (* Phaser-only operations: *)
  | PH_NEW p => only_p (P.PH_NEW p)
  | PH_SIGNAL p => only_p (P.PH_SIGNAL p)
  | PH_DROP p => only_p (P.PH_DROP p)
  | SIGNAL_ALL => only_p P.SIGNAL_ALL
  | WAIT_ALL => only_p P.WAIT_ALL
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

Inductive PhasermapOf (s:state) (t:tid) (f:fid) (m:phasermap) : Prop :=
  phasermap_of:
    FID (get_finish s) t f ->
    Map_FID.MapsTo f m s.(get_fstate) ->
    PhasermapOf s t f m.
(*
Structure context := mk_context {
  get_phasermap: P.phasermap;
  get_finish: F.finish;
}.
*)
Definition context := (P.phasermap * F.finish) % type.
Inductive ContextOf (s:state) (t:tid) : context -> Prop :=
  context_of_def:
    forall f m,
    PhasermapOf s t f m ->
    ContextOf s t (m, (get_finish s)).

Inductive CtxReduce (ctx:context) (t:tid) (o:op) : context -> Prop :=
  | reduce_p:
    forall m o',
    translate o = only_p o' ->
    P.Reduce (fst ctx) t o' m ->
    CtxReduce ctx t o (m, snd ctx)
  | reduce_f:
    forall f o',
    translate o = only_f o' ->
    FS.Reduce (snd ctx) t o' f ->
    CtxReduce ctx t o (fst ctx, f)
  | reduce_both:
    forall m o' f o'',
    translate o = both o' o'' ->
    P.Reduce (fst ctx) t o' m ->
    FS.Reduce (snd ctx) t o'' f ->
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
  Require HJ.AsyncFinish.Typesystem.
  Module P_T := HJ.Phasers.Typesystem.
  Module F_T := HJ.AsyncFinish.Typesystem.
  
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

End Typesystem.

Require HJ.Phasers.Progress.
Module P_P := HJ.Phasers.Progress.

Module Progress.
  Import Semantics.
  Import Typesystem.
  Definition requests := Map_TID.t op.
  Definition r_state := (state * requests) % type.

  Inductive Redex (s:r_state) (t:tid) (i:op) (s':state) : Prop :=
    redex_def:
      Map_TID.MapsTo t i (snd s) ->
      Reduce (fst s) t i s' ->
      Redex s t i s'.

  Section SimpleProgress.
    Variable f:F.finish.
    Variable f_IsValid: F_T.Valid f.
    Variable p:P.phasermap.
    Variable p_IsValid: P_T.Valid p.
    Variable reqs: Map_TID.t op.
    Variable ReqsChecked:
      forall t i,
      Map_TID.MapsTo t i reqs -> Check (p,f) t i.
    Require Import HJ.AsyncFinish.Progress.
    Variable IsFlat:
      Flat f.
    Variable p_reqs: Map_TID.t P.op.
    Variable p_reqs_spec_1:
      forall t o,
      Map_TID.MapsTo t o p_reqs ->
      exists i, Map_TID.MapsTo t i reqs /\ as_p_op i = Some o.
    Variable p_reqs_spec_2:
      forall t i o,
      Map_TID.MapsTo t i reqs ->
      as_p_op i = Some o ->
      Map_TID.MapsTo t o p_reqs.
      
    Variable f_reqs: Map_TID.t FS.op.
    Variable f_reqs_spec_1:
      forall t o,
      Map_TID.MapsTo t o f_reqs ->
      exists i, Map_TID.MapsTo t i reqs /\ as_f_op i = Some o.
    Variable f_reqs_spec_2:
      forall t i o,
      Map_TID.MapsTo t i reqs ->
      as_f_op i = Some o ->
      Map_TID.MapsTo t o f_reqs.
    
    Theorem progress_only_f:
      forall t i o,
      Map_TID.MapsTo t i reqs ->
      translate i = only_f o ->
      exists f', CtxReduce (p, f) t i (p, f').
    Proof.
      intros.
      assert (Hx := H0).
      apply translate_only_f_impl_as_f_op in Hx.
      assert (Hy := Hx).
      apply f_reqs_spec_2 with (t:=t) in Hx; auto.
      assert (R: exists f', FS.Reduce f t o f'). {
        assert (F_T.Check f t o). {
          eauto using check_inv_f_check.
        }
        auto using flat_reduces.
      }
      destruct R as (f', R).
      exists f'.
      apply reduce_f with (o); auto.
    Qed.
    
    Lemma is_p_impl_reqs_f_spec_1:
      (forall t i, Map_TID.MapsTo t i reqs ->  exists o, as_p_op i = Some o) ->
      forall t i,
      Map_TID.MapsTo t i reqs ->
      (exists o, as_p_op i = Some o /\ Map_TID.MapsTo t o p_reqs).
    Proof.
      intros IsP.
      intros.
      assert (Hx := H).
      apply IsP in H.
      destruct H as (o, ?).
      exists o; intuition.
      eauto.
    Qed.


    Theorem progress_all_p:
      (forall t i, Map_TID.MapsTo t i reqs ->  exists o, as_p_op i = Some o) ->
      exists t i ctx, CtxReduce (p, f) t i ctx.
    Proof.
      Print progress.
      
    Qed.
    

    Theorem progress:
      ~ Map_TID.Empty reqs ->
      exists t i ctx, CtxReduce (p, f) t i ctx.
    Proof.
      intros.
      
    Qed.
      
    Theorem progress:
      ~ Map_TID.Empty reqs ->
      exists t i ctx, CtxReduce (p, f) t i ctx.
    Proof.
      
    Qed.
      
  Section Progress.

  Variable s: state.
  Variable reqs: Map_TID.t op.
  Variable ReqsChecked:
    forall t i ctx,
    Map_TID.MapsTo t i reqs -> ContextOf s t ctx -> Check ctx t i.

  Theorem progress:
    ~ Map_TID.Empty reqs ->
    exists t i s',
    Redex (s,reqs) t i s'.
  Proof.