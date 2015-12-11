Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.

Require Import HJ.Vars.
Require Import HJ.Phasers.Welformedness.

Set Implict Arguments.

(**
  Phase-ordering is a phaser-level property that considers the
  relationship between two arbitrary taskviews.
  It is a correctness property that lets us reason about the "temporal" ordering
  of a taskview, with respect to a given reduction relation.
  
  Phase ordering is a way
  to compare the various members, the taskviews, of a phaser. We say that
  v1 <= v2 if (i) the wait phase of v1 is smaller than or equals the signal phase
  of v2, (ii) v2 has signal-only mode, or (iii) v1 has wait-only mode. 
  
  
  There are two important ideas behind the Phase Ordering property, both
  capture how phaser synchronization develops. The first idea is that
  phase ordering defines the correctness of synchronization: for any
  taskviews v1 and v2 picked from the same phaser we have that v1 <= v2,
  that is the wait phase of v1 is at *most* as great as the signal-phase of v2,
  but not greater. For instance, after executing a wait, the task's signal
  phase must be greater-than or equal other members' wait phase. 
  
  
*)
Module Taskview.
  Require Import HJ.Phasers.Regmode.
  Require Import HJ.Phasers.Taskview.
  Import Welformedness.Taskview.

  Inductive Lt v1 v2 : Prop :=
    tv_lt_def:
      signal_phase v1 < wait_phase v2 ->
      SignalCap (mode v1) ->
      WaitCap (mode v2) ->
      Lt v1 v2.

  (** v2 is beghind of v1, or v1 and v2 intersect. *)

  Inductive Ge v1 v2 : Prop := 
    | tv_ge_ge:
       signal_phase v1 >= wait_phase v2 ->
       Ge v1 v2
    | tv_ge_so:
      mode v2 = SIGNAL_ONLY ->
      Ge v1 v2
    | tv_ge_wo:
      mode v1 = WAIT_ONLY ->
      Ge v1 v2.

  Definition Le v1 v2 := Ge v2 v1.

  Definition Gt v1 v2 := Lt v2 v1.

  Module Notations.
    Infix "<" := Lt : phaser_scope.
    Infix ">" := Gt : phaser_scope.
    Infix "<=" := Le : phaser_scope.
    Infix ">=" := Ge : phaser_scope.
  End Notations.

  Open Scope phaser_scope.
  Import Notations.

  Section Facts.    

  Lemma le_spec:
    forall v1 v2,
    v1 <= v2 <-> v2 >= v1.
  Proof.
    split; auto.
  Qed.

  Lemma lt_spec:
    forall v1 v2,
    v1 < v2 <-> v2 > v1.
  Proof.
    split; auto.
  Qed.

  Lemma tv_ge_dec:
    forall v1 v2,
    { v1 >= v2 } + { ~ v1 >= v2 }.
  Proof.
    intros.
    destruct (ge_dec (signal_phase v1) (wait_phase v2)).
    { left; auto using tv_ge_ge. }
    destruct (regmode_eq_dec (mode v2) SIGNAL_ONLY).
    { left; auto using tv_ge_so. }
    destruct (regmode_eq_dec (mode v1) WAIT_ONLY).
    { left; auto using tv_ge_wo. }
    right.
    intuition.
  Qed.

  Lemma tv_lt_dec:
    forall v1 v2,
    { v1 < v2 } + { ~ v1 < v2 }.
  Proof.
    intros.
    destruct (wait_cap_dec (mode v2)). {
      destruct (signal_cap_dec (mode v1)). {
        destruct (lt_dec (signal_phase v1) (wait_phase v2)). {
          left; auto using tv_lt_def.
        }
        right; intuition.
      }
      right; intuition.
    }
    right; intuition.
  Qed.

  Lemma tv_ge_to_not_lt:
    forall v1 v2,
    Ge v1 v2 -> ~ Lt v1 v2.
  Proof.
    intros.
    intuition.
    - destruct H0; inversion H3.
    - destruct H2; inversion H3.
  Qed.

  Lemma tv_lt_to_not_ge:
    forall v1 v2,
    Lt v1 v2 -> ~ Ge v1 v2.
  Proof.
    intros.
    intuition.
    - destruct H; inversion H3.
    - inversion H2; rewrite H3 in *; inversion H4.
  Qed.

  Lemma tv_not_lt_to_ge:
    forall v1 v2,
    ~ Lt v1 v2 -> Ge v1 v2.
  Proof.
    intros.
    destruct (ge_dec (signal_phase v1) (wait_phase v2)).
    { auto using tv_ge_ge. }
    destruct (regmode_eq_dec (mode v2) SIGNAL_ONLY).
    { auto using tv_ge_so. }
    destruct (regmode_eq_dec (mode v1) WAIT_ONLY).
    { auto using tv_ge_wo. }
    assert (Lt v1 v2). {
      assert (signal_phase v1 < wait_phase v2) % nat by intuition.
      auto using tv_lt_def, neq_wo_to_signal_cap, neq_so_to_wait_cap.
    }
    contradiction.
  Qed.

  Lemma tv_not_lt_rw_tv_ge:
    forall v1 v2,
    ~ Lt v1 v2 <-> Ge v1 v2.
  Proof.
    split; auto using tv_not_lt_to_ge, tv_ge_to_not_lt.
  Qed.

  Lemma tv_not_ge_to_lt:
    forall v1 v2,
    ~ Ge v1 v2 -> Lt v1 v2.
  Proof.
    intros.
    destruct (wait_cap_dec (mode v2)). {
      destruct (signal_cap_dec (mode v1)). {
        destruct (lt_dec (signal_phase v1) (wait_phase v2)). {
          auto using tv_lt_def.
        }
        assert (Ge v1 v2). {
          assert (signal_phase v1 >= wait_phase v2) % nat by intuition.
          auto using tv_ge_ge.
        }
        contradiction.
      }
      assert (Ge v1 v2) by
        auto using tv_ge_wo, not_signal_cap_to_wo.
      contradiction.
    }
    assert (Ge v1 v2) by
      auto using tv_ge_so, not_wait_cap_to_so.
    contradiction.
  Qed.

  Lemma tv_not_ge_rw_lt:
    forall v1 v2,
    ~ Ge v1 v2 <-> Lt v1 v2.
  Proof.
    split; auto using tv_not_ge_to_lt, tv_lt_to_not_ge.
  Qed.

  Lemma tv_lt_ge_dec:
    forall v1 v2,
    { Lt v1 v2 } + { Ge v1 v2 }.
  Proof.
    intros.
    destruct (tv_lt_dec v1 v2);
    auto using tv_not_lt_to_ge.
  Qed.

  Lemma tv_welformed_to_ge_refl:
    forall v,
    Welformed v ->
    Ge v v.
  Proof.
    intros.
    inversion H;
      apply tv_ge_ge;
      intuition.
  Qed.

  Let signal_preserves_lhs:
    forall v,
    Welformed v ->
    forall v',
    Ge v v' ->
    Ge (Taskview.signal v) v'.
  Proof.
    intros.
    inversion H0; subst.
    - apply tv_ge_ge.
      destruct (signal_phase_signal_inv _ H); intuition.
    - auto using tv_ge_so.
    - rewrite <- signal_preserves_mode in *.
      auto using tv_ge_wo.
  Qed.

  Let tv_signal_ge_lhs:
    forall v v',
    Welformed v ->
    Reduces v SIGNAL v' ->
    Ge v' v.
  Proof.
    intros.
    inversion H0.
    subst.
    apply signal_preserves_lhs; auto using tv_welformed_to_ge_refl.
  Qed.

  Let tv_wait_ge_lhs:
    forall v,
    WaitPre v ->
    Ge (wait v) v.
  Proof.
    intros.
    destruct H.
    apply tv_ge_ge.
    intuition.
 Qed.

  Lemma tv_ge_reduces:
    forall v o v',
    Welformed v ->
    Reduces v o v' ->
    Ge v' v.
  Proof.
    intros.
    inversion H0; subst.
    - auto using tv_signal_ge_lhs.
    - auto using tv_wait_ge_lhs.
  Qed.

  Let tv_ge_reduces_trans_sw:
    forall x o y o' z,
    Welformed x ->
    Welformed y ->
    Welformed z ->
    Reduces x o y ->
    Reduces y o' z ->
    mode x = SIGNAL_WAIT ->
    (signal_phase z >= wait_phase x)%nat.
  Proof.
    intros.
    assert (Ge z y) by eauto using tv_ge_reduces.
    assert (Ge y x) by eauto using tv_ge_reduces.
    destruct o.
    - apply reduces_rw_signal in H2.
      destruct o'.
      + apply reduces_rw_signal in H3.
        assert (R: mode z = mode x). {
          subst.
          repeat rewrite signal_preserves_mode in *.
          trivial.
        }
        assert (WaitCap (mode z)). {
          rewrite R.
          rewrite H4.
          apply wait_cap_sw.
        }
        subst.
        assert (WaitCap (mode x)). {
          rewrite H4.
          apply wait_cap_sw.
        }
        rewrite signal_signal_wait_cap; auto.
        rewrite signal_wait_cap_signal_phase; (intuition || auto).
      + apply reduces_rw_wait in H3.
        assert (wait_phase x <= signal_phase x)%nat by auto
          using welformed_wait_phase_le_signal_phase.
        subst.
        rewrite wait_preserves_signal_phase.
        assert (signal_phase x <= signal_phase (signal x)) % nat. {
          auto using signal_phase_le_signal.
        }
        intuition.
    - assert (WaitCap (mode x)). {
        rewrite H4.
        auto using wait_cap_sw.
      }
      assert (o' = SIGNAL) by eauto using reduces_trans_inv.
      subst.
      assert (R: signal_phase y = wait_phase y) by eauto using reduces_wait_inv_wait_cap.
      inversion H2; subst.
      inversion H3; subst.
      rewrite wait_preserves_signal_phase in *.
      rewrite signal_wait_cap_signal_phase in *; auto.
      rewrite wait_wait_phase in *.
      intuition.
  Qed.

  Lemma tv_ge_trans_helper
    (x y z: taskview)
    (Hcont:mode x <> WAIT_ONLY -> mode z <> SIGNAL_ONLY -> (signal_phase x >= wait_phase z)%nat):
    x >= y ->
    y >= z ->
    x >= z.
  Proof.
    intros.
    destruct (regmode_eq_dec (mode x) WAIT_ONLY).
    {
      auto using tv_ge_wo.
    }
    destruct (regmode_eq_dec (mode z) SIGNAL_ONLY). {
      auto using tv_ge_so.
    }
    auto using tv_ge_ge.
  Qed.

  Lemma tv_eval_preserves_le:
    forall v1 v2 o,
    Welformed v1 ->
    (signal_phase v1 >= wait_phase v2)%nat ->
    (signal_phase (eval o v1) >= wait_phase v2)%nat.
  Proof.
    intros.
    destruct o; simpl.
    - apply signal_phase_le_signal in H.
      intuition.
    - assumption.
  Qed.

  Lemma tv_lhs_eval_ge:
    forall v1 v2 v1' o,
    Welformed v1 ->
    Ge v1 v2 ->
    Reduces v1 o v1' ->
    Ge v1' v2.
  Proof.
    intros.
    inversion H0.
    - apply tv_ge_ge.
      apply reduces_spec in H1.
      subst.
      auto using tv_eval_preserves_le.
    - auto using tv_ge_so.
    - apply reduces_preserves_mode in H1.
      rewrite H2 in H1.
      auto using tv_ge_wo.
  Qed.

  Lemma tv_ge_eval_rhs:
    forall v1 v2 o,
    Ge v1 (eval o v2) ->
    Reduces v2 o (eval o v2) ->
    Ge v1 v2.
  Proof.
    intros.
    inversion H.
    - apply tv_ge_ge.
      destruct o; simpl in *.
      + rewrite signal_preserves_wait_phase in *.
        assumption.
      + inversion H0.
        intuition.
    - rewrite eval_preserves_mode in H1.
      auto using tv_ge_so.
    - auto using tv_ge_wo.
  Qed.

  Lemma tv_ge_eval_lhs:
    forall v1 v2 o,
    Welformed v1 ->
    Ge v1 v2 ->
    Reduces v1 o (eval o v1) ->
    Ge (eval o v1) v2.
  Proof.
    intros.
    inversion H0.
    - apply tv_ge_ge.
      destruct o; simpl in *.
      + apply signal_phase_signal_inv in H; intuition.
      + assumption.
    - auto using tv_ge_so.
    - apply tv_ge_wo.
      rewrite eval_preserves_mode.
      assumption.
  Qed.

  Lemma lt_irreflexive:
    forall v,
    Welformed v ->
    ~ (Lt v v).
  Proof.
    intros.
    rewrite tv_not_lt_rw_tv_ge.
    auto using tv_welformed_to_ge_refl.
  Qed.

  Lemma lt_trans:
    forall x y z,
    Welformed y ->
    x < y ->
    y < z ->
    x < z.
  Proof.
    intros.
    inversion H0.
    inversion H1.
    apply tv_lt_def; auto.
    assert (wait_phase y <= signal_phase y)%nat
    by auto using welformed_wait_phase_le_signal_phase.
    intuition.
  Qed.

  Section Antisym.

  Variable x y:taskview.
  
  Variable wfx: Welformed x.
  Variable wfy: Welformed y.

  Lemma lt_antisym:
    x < y ->
    ~ (y < x).
  Proof.
    intros.
    rewrite tv_not_lt_rw_tv_ge.
    inversion H; clear H.
    destruct x as (sx, wx, rx).
    destruct y as (sy, wy, ry).
    simpl in *.
    inversion H1; clear H1. {
      subst.
      inversion H2; clear H2. {
        subst; simpl in *.
        apply tv_ge_ge.
        simpl in *.
        inversion wfx; simpl in *; subst;
        inversion wfy; simpl in *; subst; intuition.
      }
      subst.
      auto using tv_ge_wo.
    }
    subst.
    auto using tv_ge_so.
  Qed.
  End Antisym.

  Lemma lt_trans_ex:
    forall x y y' z,
    x < y ->
    y <= y' ->
    y' < z ->
    x < z.
  Proof.
    intros.
    inversion H; clear H.
    inversion H1; clear H1.
    apply tv_lt_def; auto.
    inversion H0.
    - intuition.
    - rewrite H1 in *.
      inversion H4.
    - rewrite H1 in *.
      inversion H5.
  Qed.
  End Facts.
End Taskview.

Module Phaser.
  Import Taskview.
  Require Import HJ.Phasers.Regmode.
  Require Import HJ.Phasers.Taskview.
  Import Welformedness.Taskview.

  Require Import HJ.Phasers.Phaser.
  Import Welformedness.Phaser.

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
      Lt v1 v2 ->
      HappensBefore ph1 ph2.

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
   

  Definition Le := Rel Taskview.Le.

  Definition Ge := Rel Taskview.Ge.

  Lemma ph_hb_to_not_chb:
    forall ph1 ph2,
    HappensBefore ph1 ph2 ->
    ~ Ge ph1 ph2.
  Proof.
    intros.
    intuition.
    inversion H.
    inversion H0.
    assert (Taskview.Ge v1 v2) by eauto.
    assert (~ Taskview.Ge v1 v2) by auto using tv_lt_to_not_ge.
    contradiction H6.
  Qed.

  Lemma ph_chb_to_not_hb:
    forall ph1 ph2,
    Ge ph1 ph2 ->
    ~ HappensBefore ph1 ph2.
  Proof.
    intros.
    intuition.
    inversion H.
    inversion H0.
    assert (Taskview.Ge v1 v2) by eauto.
    assert (~ Taskview.Ge v1 v2) by auto using tv_lt_to_not_ge.
    contradiction H6.
  Qed.

  Lemma ph_hb_trans:
    forall ph1 ph2 ph3,
    HappensBefore ph1 ph2 ->
    HappensBefore ph2 ph3 ->
    Ge ph2 ph2 ->
    HappensBefore ph1 ph3.
  Proof.
    intros.
    inversion H.
    inversion H0.
    clear H H0.
    assert (Taskview.Ge v0 v2) by (inversion H1; eauto).
    eauto using lt_trans_ex, ph_happens_before_def.
  Qed.

  Lemma hb_irreflexive:
    forall ph,
    Ge ph ph ->
    ~ (HappensBefore ph ph).
  Proof.
    intros.
    auto using ph_chb_to_not_hb.
  Qed.

  Section Antisym.

  Variable x y:phaser.

  Variable wx: Welformed x.
  Variable wy: Welformed y.
  Variable gx: Ge x x.
  Variable gy: Ge y y.

  Lemma ph_hb_antisym:
    HappensBefore x y ->
    ~ (HappensBefore y x).
  Proof.
    intros.
    apply ph_chb_to_not_hb.
    apply ph_rel_def.
    intros.
    destruct (tv_lt_ge_dec v1 v2); auto.
    inversion H.
    assert (Lt v1 v3). {
      inversion gx.
      assert (Taskview.Ge v0 v2) by eauto.
      eauto using lt_trans_ex.
    }
    assert (~ Taskview.Ge v1 v3) by eauto using tv_lt_to_not_ge.
    assert (Taskview.Ge v1 v3) by (inversion gy; eauto).
    contradiction.
  Qed.
  End Antisym.

  Let ph_ge_refl_preserves_reduces_some:
    forall ph ph' t o o',
    Welformed ph ->
    Ge ph ph ->
    Reduces ph t o ph' ->
    as_tv_op o = Some o' ->
    Ge ph' ph'.
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
          assert (R : Taskview.Ge v1 v) by (inversion H0; eauto).
          inversion R; clear R.
          - destruct o'; simpl in *.
            {
              rewrite <- signal_preserves_wait_phase in *.
              auto using tv_ge_ge.
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
              auto using tv_ge_so.
            }
            {
              assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
              destruct (signal_cap_wo_dec (mode v1)). {
                destruct H8.
                apply tv_ge_ge.
                assert (signal_phase v1 >= (signal_phase v)) by (inversion H12; eauto).
                rewrite wait_wait_phase.
                intuition.
              }
              auto using tv_ge_wo.
            }
          - apply tv_ge_so.
            rewrite eval_preserves_mode.
            assumption.
          - auto using tv_ge_wo.
        * inversion H0; eauto.
  Qed.

  Let ph_ge_refl_preserves_reduces_drop:
    forall ph ph' t,
    Ge ph ph ->
    Reduces ph t DROP ph' ->
    Ge ph' ph'.
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

  Let tv_ge_register_left:
    forall r v1 v2,
    r_le (get_mode r) (mode v1) ->
    Taskview.Ge v1 v2 ->
    Taskview.Ge (set_mode v1 (get_mode r)) v2.
  Proof.
    intros ? ? ? Hle Hge.
    inversion Hge.
    * apply tv_ge_ge.
      rewrite set_mode_preserves_signal_phase.
      assumption.
    * auto using tv_ge_so.
    * rewrite H in Hle.
      inversion Hle.
      rewrite <- H.
      rewrite set_mode_ident.
      assumption.
  Qed.

  Let tv_ge_register_both:
    forall r v,
    r_le (get_mode r) (mode v) ->
    Taskview.Ge v v ->
    Taskview.Ge (set_mode v (get_mode r)) (set_mode v (get_mode r)).
  Proof.
    intros.
    destruct (get_mode r); auto using tv_ge_so, tv_ge_wo.
    inversion H.
    subst.
    rewrite H3.
    rewrite set_mode_ident.
    assumption.  
  Qed.

  Let tv_ge_register_right:
    forall v1 v2 r,
    r_le (get_mode r) (mode v2) ->
    Taskview.Ge v1 v2 ->
    Taskview.Ge v1 (set_mode v2 (get_mode r)).
  Proof.
    intros ? ? r Hle Hge.
    inversion Hge.
    * apply tv_ge_ge.
      rewrite set_mode_preserves_wait_phase.
      assumption.
    * rewrite H in Hle.
      inversion Hle.
      rewrite H1 in *.
      rewrite <- H.
      rewrite set_mode_ident.
      assumption.
    * auto using tv_ge_wo.
  Qed.

  Let ph_ge_refl_preserves_reduces_register:
    forall t r ph ph',
    Ge ph ph ->
    Reduces ph t (REGISTER r) ph' ->
    Ge ph' ph'.
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
        assert (Taskview.Ge v v) by (inversion Hge; eauto).
        auto using tv_ge_register_both.
      + assert (Taskview.Ge v v2) by (inversion Hge; eauto).
        auto using tv_ge_register_left.
    - apply Map_TID_Facts.add_mapsto_iff in Hmt2;
      destruct Hmt2 as [(?,?)|(?,?)].
      + subst.
        assert (Taskview.Ge v1 v) by (inversion Hge; eauto).
        auto using tv_ge_register_right.
      + inversion Hge; eauto.
  Qed.

  Theorem ph_ge_refl_preserves_reduce:
    forall ph t o ph',
    Welformed ph ->
    Ge ph ph ->
    Phaser.Reduces ph t o ph' ->
    Ge ph' ph'.
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
    Ge ph ph ->
    Reduces ph t o ph' ->
    as_tv_op o = Some o' ->
    Ge ph' ph.
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
      assert (Taskview.Ge v v2) by (inversion H0; eauto).
      eauto using tv_lhs_eval_ge.
    - inversion H0; eauto.
  Qed.

  Lemma ph_ge_reduce:
    forall ph t o ph',
    Welformed ph ->
    Ge ph ph ->
    Reduces ph t o ph' ->
    Ge ph' ph.
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
        assert (Taskview.Ge v v2) by (inversion Hge; eauto).
        auto using tv_ge_register_left.
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
    Ge y x ->
    ReducesUpdates y t o z ->
    Ge z x.
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
      assert (Taskview.Ge v vx) by (inversion H0; eauto).
      assert (Taskview.Welformed v) by (inversion H; eauto).
      eauto using tv_ge_eval_lhs.
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
    assert (Taskview.Ge v vx)
    by (inversion H0; eauto).
    eauto using tv_ge_register_left.
  Qed.

  Lemma ph_reduces_drop_preserves_ge_left:
    forall x y z t,
    Ge y x ->
    Reduces y t DROP z ->
    Ge z x.
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
    Ge y x ->
    SReduces y z ->
    Ge z x.
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
    Ge x x ->
    clos_refl_trans phaser SReduces x y ->
    Ge y y.
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
    Ge x x ->
    clos_refl_trans phaser SReduces x y ->
    Ge y x.
  Proof.
    intros.
    rewrite clos_rt_rtn1_iff in H1.
    induction H1; auto.
    assert (Welformed y) by (rewrite <- clos_rt_rtn1_iff in H2; eauto using ph_s_reduces_trans_refl_welformed).
    apply ph_s_reduces_preserves_ge_left with (y); auto.
  Qed.

  Section ReducesPreservesAwait.
  Variable ph: phaser.
  Variable n: nat.
  Variable wf: Welformed ph.
  Variable W: Await ph n.

  Lemma ph_signal_preserves_await:
    forall t,
    SignalPre t ph ->
    Await (signal t ph) n.
  Proof.
    intros.
    apply await_def.
    intros ? ? mt1 Hs.
    apply signal_mapsto_inv in mt1.
    destruct mt1.
    - destruct a as (E, (v', (R, mt2))).
      symmetry in E.
      subst.
      rewrite signal_preserves_mode in Hs.
      assert (signal_phase v' >= n) by (inversion W; eauto).
      assert (signal_phase v' <= signal_phase (Taskview.signal v')). {
        assert (Taskview.Welformed v') by (inversion wf; eauto).
        eauto using signal_phase_le_signal.
      }
      intuition.
    - destruct a.
      inversion W; eauto.
  Qed.

  Lemma ph_wait_preserves_await:
    forall t,
    WaitPre t ph ->
    Await (wait t ph) n.
  Proof.
    intros.
    apply await_def.
    intros ? ? mt1 Hs.
    apply wait_mapsto_inv in mt1.
    destruct mt1.
    - destruct a as (E, (v', (R, mt2))).
      symmetry in E.
      subst.
      rewrite wait_preserves_mode in Hs.
      assert (signal_phase v' >= n) by (inversion W; eauto).
      rewrite wait_preserves_signal_phase.
      assumption.
    - destruct a.
      inversion W; eauto.
  Qed.

  Lemma ph_drop_preserves_await:
    forall t,
    DropPre t ph ->
    Await (drop t ph) n.
  Proof.
    intros.
    apply await_def.
    intros ? ? mt1 Hs.
    apply drop_mapsto_inv in mt1.
    destruct mt1.
    inversion W; eauto.
  Qed.

  Lemma ph_register_preserves_await:
    forall r t,
    RegisterPre r t ph ->
    Await (register r t ph) n.
  Proof.
    intros.
    apply await_def.
    intros ? ? mt1 Hs.
    apply ph_register_inv_mapsto in mt1.
    destruct mt1.
    - inversion W; eauto.
    - destruct H0 as (R1, (v', (mt2, R2))).
      subst.
      rewrite set_mode_preserves_signal_phase.
      inversion W.
      apply H0 with (t:=t); auto.
      rewrite mode_set_mode_rw in *.
      inversion H.
      assert (v' = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      inversion H3.
      * rewrite H5 in *.
        rewrite H6 in *.
        assumption.
      * rewrite H5 in *.
        rewrite H6 in *.
        assumption.
      * subst.
        auto using signal_cap_sw.
  Qed.
    

  Lemma ph_reduces_preserves_await:
    forall ph' t o,
    Reduces ph t o ph' ->
    Await ph' n.
  Proof.
    intros.
    destruct o; inversion H; simpl in *; subst.
    - auto using ph_signal_preserves_await.
    - auto using ph_wait_preserves_await.
    - auto using ph_drop_preserves_await.
    - auto using ph_register_preserves_await.
  Qed.
  End ReducesPreservesAwait.

  Section PhReducesAwaitEnabled.
    Variable ph1 ph2 ph1': phaser.
    Variable wf1: Welformed ph1.
    Variable t t': tid.
    Variable o: op.
    Variable Hneq: t' <> t.
    Variable R1: Reduces ph1 t WAIT ph1'.
    Variable R2: Reduces ph1 t' o ph2.

  Axiom ph_reduces_disjoint:
    forall ph t o ph' v,
    t' <> t ->
    Map_TID.MapsTo t v ph ->
    Reduces ph t' o ph' ->
    Map_TID.MapsTo t v ph'.

  Lemma ph_reduces_preserves_wait:
    Reduces ph2 t WAIT (wait t ph2).
  Proof.
    intros.
    inversion R1;
    simpl in *; clear R1; subst.
    inversion H; clear H; subst.
    assert (Map_TID.MapsTo t v ph2)
    by eauto using ph_reduces_disjoint.
    apply ph_reduces.
    simpl in *.
    apply wait_pre with (v:=v); auto.
    inversion H2; subst.
    - assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      eauto using sync_so.
    - assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      eauto using sync_wait, ph_reduces_preserves_await.
  Qed.
  End PhReducesAwaitEnabled.

End Phaser.


  
