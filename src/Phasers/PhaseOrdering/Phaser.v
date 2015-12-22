Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.

Require Import HJ.Vars.
Require Import HJ.Phasers.Regmode.
Require Import HJ.Phasers.Taskview.
Require Import HJ.Phasers.Phaser.
Require Import HJ.Phasers.Welformedness.
Require Import HJ.Phasers.PhaseOrdering.Taskview.
Import Welformedness.Taskview.
Import Welformedness.Phaser.
Import PhaseOrdering.Taskview.

Set Implict Arguments.

Section Defs.
  Inductive Rel (R: taskview -> taskview -> Prop) (ph1 ph2:phaser) : Prop := 
    ph_rel_def:
      (forall t1 t2 v1 v2,
        Map_TID.MapsTo t1 v1 ph1 ->
        Map_TID.MapsTo t2 v2 ph2 ->
        R v1 v2) ->
      Rel R ph1 ph2.

  Inductive HappensBefore (ph1 ph2:phaser) : Prop :=
    ph_happens_before_def:
      forall t1 t2 v1 v2,
      Map_TID.MapsTo t1 v1 ph1 ->
      Map_TID.MapsTo t2 v2 ph2 ->
      HB v1 v2 ->
      HappensBefore ph1 ph2.


  Definition Ge := Rel Taskview.NHB.
  Definition Le := Rel Taskview.MHP.

  Definition NHB := Rel Taskview.NHB.
  Definition WaitsFor x y := HappensBefore x y.

End Defs.

Module Notations.
  Infix "<" := HappensBefore : phaser_scope.
  Infix ">" := WaitsFor : phaser_scope.
  Infix ">=" := Ge : phaser_scope.
  Infix "<=" := Le : phaser_scope.
End Notations.

Section Facts.
(*
  Import Taskview.
  Require Import HJ.Phasers.Regmode.
  Require Import HJ.Phasers.Taskview.
  Import Welformedness.Taskview.

  Require Import HJ.Phasers.Phaser.
  Import Welformedness.Phaser.
*)
  Lemma ph_rel_inv:
    forall R ph1 ph2 t1 t2 v1 v2,
    Map_TID.MapsTo t1 v1 ph1 ->
    Map_TID.MapsTo t2 v2 ph2 ->
    Rel R ph1 ph2 ->
    R v1 v2.
  Proof.
    intros.
    inversion H1.
    eauto.
  Qed.

  Lemma ph_hb_to_not_chb:
    forall ph1 ph2,
    HappensBefore ph1 ph2 ->
    ~ NHB ph1 ph2.
  Proof.
    intros.
    intuition.
    inversion H.
    inversion H0.
    assert (Taskview.NHB v1 v2) by eauto.
    assert (~ Taskview.NHB v1 v2) by auto using tv_hb_to_not_ge.
    contradiction H6.
  Qed.

  Lemma ph_chb_to_not_hb:
    forall ph1 ph2,
    NHB ph1 ph2 ->
    ~ HappensBefore ph1 ph2.
  Proof.
    intros.
    intuition.
    inversion H.
    inversion H0.
    assert (Taskview.NHB v1 v2) by eauto.
    assert (~ Taskview.NHB v1 v2) by auto using tv_hb_to_not_ge.
    contradiction H6.
  Qed.

  Lemma ph_hb_trans:
    forall ph1 ph2 ph3,
    HappensBefore ph1 ph2 ->
    HappensBefore ph2 ph3 ->
    NHB ph2 ph2 ->
    HappensBefore ph1 ph3.
  Proof.
    intros.
    inversion H.
    inversion H0.
    clear H H0.
    assert (Taskview.NHB v0 v2) by (inversion H1; eauto).
    eauto using lt_trans_ex, ph_happens_before_def.
  Qed.

  Lemma hb_irreflexive:
    forall ph,
    NHB ph ph ->
    ~ (HappensBefore ph ph).
  Proof.
    intros.
    auto using ph_chb_to_not_hb.
  Qed.

  Section Antisym.
  Variable x y:phaser.

  Variable wx: Welformed x.
  Variable wy: Welformed y.
  Variable gx: NHB x x.
  Variable gy: NHB y y.

  Lemma ph_hb_antisym:
    HappensBefore x y ->
    ~ (HappensBefore y x).
  Proof.
    intros.
    apply ph_chb_to_not_hb.
    apply ph_rel_def.
    intros.
    destruct (tv_hb_ge_dec v1 v2); auto.
    inversion H.
    assert (HB v1 v3). {
      inversion gx.
      assert (Taskview.NHB v0 v2) by eauto.
      eauto using lt_trans_ex.
    }
    assert (~ Taskview.NHB v1 v3) by eauto using tv_hb_to_not_ge.
    assert (Taskview.NHB v1 v3) by (inversion gy; eauto).
    contradiction.
  Qed.
  End Antisym.

  Let ph_ge_refl_preserves_reduces_some:
    forall ph ph' t o o',
    Welformed ph ->
    NHB ph ph ->
    Reduces ph t o ph' ->
    as_tv_op o = Some o' ->
    NHB ph' ph'.
  Proof.
    intros.
    assert (Hin : Map_TID.In t ph) by eauto using ph_in.
    apply Map_TID_Extra.in_to_mapsto in Hin.
    destruct Hin as (v, Hmt).
    assert (Taskview.Reduces v o' (eval o' v)) by
        eauto using ph_reduces_to_tv_reduce.
      assert (ph' = Map_TID.add t (Taskview.eval o' v) ph) by
        eauto using ph_to_tv_correct.
      subst.
      apply ph_rel_def.
      intros.
      apply Map_TID_Facts.add_mapsto_iff in H4.
      destruct H4 as [(?,?)|(?,?)].
      + subst.
        apply Map_TID_Facts.add_mapsto_iff in H5.
        destruct H5 as [(?,?)|(?,?)].
        * subst.
          eauto using
            tv_reduces_preserves_welformed,
            ph_welformed_to_tv_welformed,
            tv_welformed_to_ge_refl.
        * apply tv_lhs_eval_ge with (v2:=v2) in H3;
          eauto using ph_welformed_to_tv_welformed.
          eapply ph_rel_inv; eauto.
      + apply Map_TID_Facts.add_mapsto_iff in H5.
        destruct H5 as [(?,?)|(?,?)].
        * subst.
          assert (R : Taskview.NHB v1 v) by (inversion H0; eauto).
          inversion R; clear R.
          - destruct o'; simpl in *.
            {
              rewrite <- signal_preserves_wait_phase in *.
              auto using tv_nhb_ge.
            }
            apply as_tv_op_inv_wait in H2.
            subst.
            inversion H1; simpl in *; destruct H7.
            assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun.
            subst.
            inversion H9; subst.
            {
              assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun.
              subst.
              auto using tv_nhb_so.
            }
            {
              assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
              destruct (Regmode.signal_cap_wo_dec (mode v1)). {
                destruct H8.
                apply tv_nhb_ge.
                assert (signal_phase v1 >= (signal_phase v)) by (inversion H12; eauto).
                rewrite wait_wait_phase.
                intuition.
              }
              auto using tv_nhb_wo.
            }
          - apply tv_nhb_so.
            rewrite eval_preserves_mode.
            assumption.
          - auto using tv_nhb_wo.
        * inversion H0; eauto.
  Qed.

  Let ph_ge_refl_preserves_reduces_drop:
    forall ph ph' t,
    NHB ph ph ->
    Reduces ph t DROP ph' ->
    NHB ph' ph'.
  Proof.
    intros.
    inversion H0.
    subst.
    unfold drop in *.
    apply ph_rel_def.
    intros; simpl in *.
    apply Map_TID.remove_3 in H3.
    apply Map_TID.remove_3 in H2.
    inversion H; eauto.
  Qed.

  Let tv_nhb_register_left:
    forall r v1 v2,
    r_le (get_mode r) (mode v1) ->
    Taskview.NHB v1 v2 ->
    Taskview.NHB (set_mode v1 (get_mode r)) v2.
  Proof.
    intros ? ? ? Hle Hge.
    inversion Hge.
    * apply tv_nhb_ge.
      rewrite set_mode_preserves_signal_phase.
      assumption.
    * auto using tv_nhb_so.
    * rewrite H in Hle.
      inversion Hle.
      rewrite <- H.
      rewrite set_mode_ident.
      assumption.
  Qed.

  Let tv_nhb_register_both:
    forall r v,
    r_le (get_mode r) (mode v) ->
    Taskview.NHB v v ->
    Taskview.NHB (set_mode v (get_mode r)) (set_mode v (get_mode r)).
  Proof.
    intros.
    destruct (get_mode r); auto using tv_nhb_so, tv_nhb_wo.
    inversion H.
    subst.
    rewrite H3.
    rewrite set_mode_ident.
    assumption.  
  Qed.

  Let tv_nhb_register_right:
    forall v1 v2 r,
    r_le (get_mode r) (mode v2) ->
    Taskview.NHB v1 v2 ->
    Taskview.NHB v1 (set_mode v2 (get_mode r)).
  Proof.
    intros ? ? r Hle Hge.
    inversion Hge.
    * apply tv_nhb_ge.
      rewrite set_mode_preserves_wait_phase.
      assumption.
    * rewrite H in Hle.
      inversion Hle.
      rewrite H1 in *.
      rewrite <- H.
      rewrite set_mode_ident.
      assumption.
    * auto using tv_nhb_wo.
  Qed.

  Let ph_ge_refl_preserves_reduces_register:
    forall t r ph ph',
    NHB ph ph ->
    Reduces ph t (REGISTER r) ph' ->
    NHB ph' ph'.
  Proof.
    intros ? ? ? ? Hge R.
    inversion R; subst; simpl in *.
    destruct H.
    destruct R.
    simpl in *.
    assert (R:=H0).
    apply ph_register_rw with (r:=r) in R; auto.
    rewrite R; clear R.
    apply ph_rel_def.
    intros ? ? ? ? Hmt1 Hmt2.
    apply Map_TID_Facts.add_mapsto_iff in Hmt1;
    destruct Hmt1 as [(?,?)|(?,?)].
    - subst.
      apply Map_TID_Facts.add_mapsto_iff in Hmt2;
      destruct Hmt2 as [(?,?)|(?,?)].
      + subst.
        assert (Taskview.NHB v v) by (inversion Hge; eauto).
        auto using tv_nhb_register_both.
      + assert (Taskview.NHB v v2) by (inversion Hge; eauto).
        auto using tv_nhb_register_left.
    - apply Map_TID_Facts.add_mapsto_iff in Hmt2;
      destruct Hmt2 as [(?,?)|(?,?)].
      + subst.
        assert (Taskview.NHB v1 v) by (inversion Hge; eauto).
        auto using tv_nhb_register_right.
      + inversion Hge; eauto.
  Qed.

  Theorem ph_ge_refl_preserves_reduce:
    forall ph t o ph',
    Welformed ph ->
    NHB ph ph ->
    Phaser.Reduces ph t o ph' ->
    NHB ph' ph'.
  Proof.
    intros.
    remember (as_tv_op o) as o'.
    symmetry in Heqo'.
    destruct o' as [o'|].
    - eauto using ph_ge_refl_preserves_reduces_some.
    - destruct o; try (simpl in Heqo'; inversion Heqo'); clear Heqo'.
      + eauto using ph_ge_refl_preserves_reduces_drop.
      + eauto using ph_ge_refl_preserves_reduces_register.
  Qed.

  Let ph_ge_reduces_some:
    forall ph t o o' ph',
    Welformed ph ->
    NHB ph ph ->
    Reduces ph t o ph' ->
    as_tv_op o = Some o' ->
    NHB ph' ph.
  Proof.
    intros.
    assert (Hin : Map_TID.In t ph) by eauto using ph_in.
    apply Map_TID_Extra.in_to_mapsto in Hin.
    destruct Hin as (v, Hmt).
    assert (Taskview.Reduces v o' (Taskview.eval o' v)) by
    eauto using ph_reduces_to_tv_reduce.
    assert (ph' = Map_TID.add t (Taskview.eval o' v) ph) by
    eauto using ph_to_tv_correct.
    subst.
    apply ph_rel_def.
    intros.
    apply Map_TID_Facts.add_mapsto_iff in H4;
    destruct H4 as [(?,?)|(?,?)].
    - subst.
      assert (Taskview.Welformed v) by (inversion H; eauto).
      assert (Taskview.NHB v v2) by (inversion H0; eauto).
      eauto using tv_lhs_eval_ge.
    - inversion H0; eauto.
  Qed.

  Lemma ph_ge_reduce:
    forall ph t o ph',
    Welformed ph ->
    NHB ph ph ->
    Reduces ph t o ph' ->
    NHB ph' ph.
  Proof.
    intros ? ? ? ? WF Hge R.
    remember(as_tv_op o) as o'.
    symmetry in Heqo'.
    destruct o' as [o'|]; eauto using ph_ge_reduces_some.
    (destruct o; simpl in Heqo'; inversion Heqo'); clear Heqo'.
    - inversion R; subst;  simpl in *.
      unfold drop in *.
      apply ph_rel_def.
      intros.
      apply Map_TID.remove_3 in H0.
      inversion Hge; eauto.
    - destruct R; simpl in *.
      destruct H.
      assert (R:=H0).
      apply ph_register_rw with (r:=r) in R; auto.
      rewrite R; clear R.
      apply ph_rel_def; intros.
      apply Map_TID_Facts.add_mapsto_iff in H2;
      destruct H2 as [(?,?)|(?,?)].
      + subst.
        assert (Taskview.NHB v v2) by (inversion Hge; eauto).
        auto using tv_nhb_register_left.
      + inversion Hge; eauto.
  Qed.

  Section Trans.
    Inductive Update : op -> Prop :=
      | update_signal:
        Update SIGNAL
      | update_wait:
        Update WAIT
      | update_register:
        forall r,
        Update (REGISTER r).

    Hint Constructors Update.

    (** Reduces for update-operations *)

    Inductive ReducesUpdates p1 t o p2 : Prop :=
      reduces_updates_def:
        Update o ->
        Reduces p1 t o p2 ->
        ReducesUpdates p1 t o p2.

    Hint Constructors ReducesUpdates.

    Inductive ReducesDestructs p1 t : op -> phaser -> Prop :=
      reduces_destructs_def:
        forall p2,
        Reduces p1 t DROP p2 ->
        ReducesDestructs p1 t DROP p2.

    Hint Constructors ReducesDestructs.

    Lemma case_reduces:
      forall ph1 t o ph2,
      Reduces ph1 t o ph2 ->
      { ReducesUpdates ph1 t o ph2 } + { ReducesDestructs ph1 t o ph2 }.
    Proof.
      intros.
      destruct o; (solve [left; auto | right; auto]).
    Qed.

    Lemma reduces_mapsto_neq:
      forall t v ph1 t' o ph2,
      Map_TID.MapsTo t v ph1 ->
      t' <> t ->
      Reduces ph1 t' o ph2 ->
      Map_TID.MapsTo t v ph2.
    Proof.
      intros.
      assert (Hin : Map_TID.In t' ph1) by eauto using ph_in.
      apply Map_TID_Extra.in_to_mapsto in Hin.
      destruct Hin as (v', Hmt').
      assert (R:=Hmt').
      destruct H1.
      destruct o; simpl in *.
      - apply ph_signal_rw in R. rewrite R.
        auto using Map_TID.add_2.
      - apply ph_wait_rw in R; rewrite R.
        auto using Map_TID.add_2.
      - inversion H1; destruct H2; subst; simpl in *; unfold drop in *.
        auto using Map_TID.remove_2.
      - destruct H1.
        apply ph_register_rw with (r:=r) in R. rewrite R.
        apply Map_TID.add_2; auto.
        intuition.
        subst.
        contradiction H1.
        eauto using Map_TID_Extra.mapsto_to_in.
    Qed.

    Lemma reduces_mapsto_neq_rtl:
      forall t v ph1 t' o ph2,
      Map_TID.MapsTo t v ph2 ->
      t' <> t ->
      Reduces ph1 t' o ph2 ->
      Map_TID.MapsTo t v ph1 \/ exists r, o = REGISTER r /\ t = (get_task r).
    Proof.
      intros.
      assert (Hin : Map_TID.In t' ph1) by eauto using ph_in.
      apply Map_TID_Extra.in_to_mapsto in Hin.
      destruct Hin as (v', Hmt').
      destruct H1.
      assert (R:=Hmt').
      destruct o; simpl in *;  destruct H1.
      - left.
        apply ph_signal_rw in R.
        rewrite R in H.
        eauto using Map_TID.add_3.
      - apply ph_wait_rw in R; rewrite R in H.
        left; eauto using Map_TID.add_3.
      - unfold drop in *.
        left; eauto using Map_TID.remove_3.
      - destruct (TID.eq_dec t (get_task r)).
        + eauto.
        + left.
          apply ph_register_rw with (r:=r) in R; auto; rewrite R in *.
          rewrite Map_TID_Facts.add_mapsto_iff in H.
          destruct H.
          * destruct H.
            symmetry in H.
            contradiction.
          * destruct H; assumption.
    Qed.

    Lemma reduces_update_inv:
      forall t v ph1 t' o ph2,
      Map_TID.MapsTo t v ph1 ->
      ReducesUpdates ph1 t' o ph2 ->
      { Map_TID.MapsTo t v ph2 } + { exists o', (as_tv_op o = Some o' /\ t' = t /\ Map_TID.MapsTo t (Taskview.eval o' v) ph2) }.
    Proof.
      intros.
      destruct H0.
      destruct (TID.eq_dec t' t). {
        subst.
        assert (rw:=H).
        destruct H1.
        destruct o; simpl in *; try destruct H1.
        - right.
          exists Taskview.SIGNAL.
          intuition.
          apply ph_signal_rw in rw; auto; rewrite rw.
          auto using Map_TID.add_1.
        - right; exists Taskview.WAIT; intuition.
          apply ph_wait_rw in rw; rewrite rw.
          auto using Map_TID.add_1.
        - left.
          inversion H0.
        - left.
          apply ph_register_rw with (r:=r) in rw.
          rewrite rw in *.
          apply Map_TID.add_2; auto.
          inversion H1.
          remember (set_mode _ _) as v'.
          intuition; subst.
          contradiction H2.
          eauto using Map_TID_Extra.mapsto_to_in.
      }
      left.
      eauto using reduces_mapsto_neq.
    Qed.
  End Trans.

  Lemma ph_reduces_updates_preserves_ge_left:
    forall x y z t o,
    Welformed y ->
    NHB y x ->
    ReducesUpdates y t o z ->
    NHB z x.
  Proof.
    intros.
    apply ph_rel_def.
    intros tz tx vz vx; intros.
    destruct (TID.eq_dec t tz). {
      subst.
      rename H1 into r.
      assert (i: Map_TID.In tz y) by (inversion r; eauto using ph_in).
      apply Map_TID_Extra.in_to_mapsto in i.
      destruct i as (v, mt).
      assert (R:=r).
      apply reduces_update_inv with (t:=tz) (v:=v) in r; auto.
      destruct r. {
        assert (v = vz) by eauto using Map_TID_Facts.MapsTo_fun.
        subst.
        inversion H0; eauto.
      }
      destruct e as (o', (Hv, (_, Hmt))).
      assert (vz = Taskview.eval o' v) by eauto using Map_TID_Facts.MapsTo_fun.
      subst.
      assert (Taskview.Reduces v o' (Taskview.eval o' v))
      by (inversion R; eauto using ph_reduces_to_tv_reduce).
      assert (Taskview.NHB v vx) by (inversion H0; eauto).
      assert (Taskview.Welformed v) by (inversion H; eauto).
      eauto using tv_nhb_eval_lhs.
    }
    destruct H1.
    assert (R := H4).
    apply reduces_mapsto_neq_rtl with (t:=tz) (v:=vz) in H4; auto.
    destruct H4. { inversion H0; eauto. }
    destruct H4 as (r, (?, ?)).
    subst.
    clear H1.
    destruct R.
    simpl in *.
    destruct H1.
    assert (R:=H4).
    apply ph_register_rw with (r:=r) in R; auto; rewrite R in *; clear R.
    assert (vz = set_mode v (get_mode r)). {
      apply Map_TID_Facts.add_mapsto_iff in H2.
      destruct H2.
      + intuition.
      + destruct H2.
        contradiction H2.
        trivial.
    }
    subst.
    assert (Taskview.NHB v vx)
    by (inversion H0; eauto).
    eauto using tv_nhb_register_left.
  Qed.

  Lemma ph_reduces_drop_preserves_ge_left:
    forall x y z t,
    NHB y x ->
    Reduces y t DROP z ->
    NHB z x.
  Proof.
    intros.
    apply ph_rel_def; intros tz tx vz vx; intros.
    destruct H0; simpl in *.
    apply drop_mapsto_inv in H1.
    destruct H1.
    inversion H; eauto.
  Qed.

  Require Import Coq.Relations.Relation_Operators.
  Require Import Coq.Relations.Operators_Properties.

  Lemma ph_s_reduces_preserves_ge_left:
    forall x y z,
    Welformed y ->
    NHB y x ->
    SReduces y z ->
    NHB z x.
  Proof.
    intros.
    destruct H1.
    apply case_reduces in H1.
    destruct H1.
    - eauto using ph_reduces_updates_preserves_ge_left.
    - destruct r; eauto using ph_reduces_drop_preserves_ge_left.
  Qed.
  
  Lemma ph_s_reduces_trans_refl_welformed:
    forall x y,
    Welformed x ->
    clos_refl_trans phaser SReduces x y ->
    Welformed y.
  Proof.
    intros.
    induction H0; auto.
    destruct H0.
    eauto using ph_reduces_preserves_welformed.
  Qed.

  Lemma ph_s_reduces_trans_refl_ge_refl:
    forall x y,
    Welformed x ->
    NHB x x ->
    clos_refl_trans phaser SReduces x y ->
    NHB y y.
  Proof.
    intros.
    induction H1; auto.
    - destruct H1.
      eauto using ph_ge_refl_preserves_reduce.
    - assert (Welformed y) by eauto using ph_s_reduces_trans_refl_welformed.
      eauto.
  Qed.

  Lemma ph_s_reduces_trans_refl_ge:
    forall x y,
    Welformed x ->
    NHB x x ->
    clos_refl_trans phaser SReduces x y ->
    NHB y x.
  Proof.
    intros.
    rewrite clos_rt_rtn1_iff in H1.
    induction H1; auto.
    assert (Welformed y) by (rewrite <- clos_rt_rtn1_iff in H2; eauto using ph_s_reduces_trans_refl_welformed).
    apply ph_s_reduces_preserves_ge_left with (y); auto.
  Qed.

  (* 
  Suppose~$\Ph \Rwait \Phy \Rsignal \Phz$ and that $\Mode[\Ph(\Tid)] = \SW$.
  %
  We have that~$\Ph \HB \Phz$.
  *)
  Section EX2.
  Variable x y z: phaser.
  Variable t: tid.
  Variable R1: Reduces x t SIGNAL y.
  Variable R2: Reduces y t WAIT z.
  Variable v: taskview.
  Variable mt1: Map_TID.MapsTo t v x.
  Variable is_sw: mode v = SIGNAL_WAIT.
  Variable wf: Taskview.Welformed v.

  Example ex2:
    HappensBefore x z.
  Proof.
    intros.
    inversion R1; simpl in *; clear R1.
    subst; inversion H; clear H.
    assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst; clear H0.
    assert (Map_TID.MapsTo t (Taskview.signal v) (signal t x)) by eauto using signal_mapsto_spec.
    inversion R2; simpl in *; clear R2.
    subst.
    assert (Map_TID.MapsTo t (Taskview.wait (Taskview.signal v)) (wait t (signal t x))) by eauto using wait_mapsto_spec.
    apply ph_happens_before_def with (t1:=t) (t2:=t) (v1:=v) (v2:=(Taskview.wait (Taskview.signal v))); auto.
    inversion H0.
    assert (v0 = (Taskview.signal v)) by eauto using Map_TID_Facts.MapsTo_fun; subst; clear H0.
    apply tv_ex_2; auto.
  Qed.
  End EX2.

  Import Notations.
  Open Scope phaser_scope.

  Lemma ph_signal_lhs_ge_rhs:
    forall x t,
    x >= x ->
    SignalPre t x ->
    x >= signal t x.
  Proof.
    intros.
    inversion H0.
    apply ph_rel_def.
    intros.
    apply signal_mapsto_inv in H4.
    destruct H4 as [(?,(v',(?,?)))|(?,?)].
    - subst.
      assert (v' = v) by eauto using Map_TID_Facts.MapsTo_fun; subst; clear H6.
      assert (Taskview.NHB v1 v). {
        inversion H; eauto.
      }
      auto using signal_preserves_rhs.
    - inversion H; eauto.
  Qed.

  Lemma ph_wait_lhs_ge_rhs:
    forall x t,
    x >= x ->
    WaitPre t x ->
    x >= wait t x.
  Proof.
    intros.
    inversion H0; clear H0.
    apply ph_rel_def.
    intros.
    apply wait_mapsto_inv in H4.
    destruct H4 as [(?,(v',(?,?)))|(?,?)].
    - subst.
      assert (v' = v) by eauto using Map_TID_Facts.MapsTo_fun; subst; clear H6.
      assert (Taskview.NHB v1 v). {
        inversion H; eauto.
      }
      inversion H3; subst.
      + assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst; clear H5.
        apply tv_nhb_so.
        rewrite wait_preserves_mode.
        assumption.
      + assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst; clear H5.
        inversion H7.
        assert (Hx := H5 _ _ H0).
        apply wait_preserves_rhs; auto.
    - inversion H; eauto.
  Qed.

  Lemma ph_register_lhs_ge_rhs:
    forall x r t,
    x >= x ->
    RegisterPre r t x ->
    x >= register r t x.
  Proof.
    intros.
    inversion H0; clear  H0.
    apply ph_rel_def.
    intros.
    apply ph_register_inv_mapsto in H4 as [?|(?,(v',(?,?)))]. {
      inversion H; eauto.
    }
    subst.
    assert (v' = v) by eauto using Map_TID_Facts.MapsTo_fun; subst; clear H5.
    apply tv_nhb_register_right; auto.
    inversion H; eauto.
  Qed.

  Lemma ph_drop_lhs_ge_rhs:
    forall x t,
    x >= x ->
    DropPre t x ->
    x >= drop t x.
  Proof.
    intros.
    inversion H0.
    apply ph_rel_def.
    intros.
    apply drop_mapsto_inv in H3.
    destruct H3 as (?,?).
    inversion H; eauto.
  Qed.

  Lemma reduces_ne:
    forall x y,
    Ge x x ->
    SReduces x y ->
    x >= y.
  Proof.
    intros.
    inversion H0; clear H0.
    inversion H1.
    destruct o; simpl in *; subst; clear H1.
    - auto using ph_signal_lhs_ge_rhs.
    - auto using ph_wait_lhs_ge_rhs.
    - auto using ph_drop_lhs_ge_rhs.
    - auto using ph_register_lhs_ge_rhs.
  Qed.
End Facts.

