Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.

Require Import HJ.Vars.
Require Import HJ.Phasers.Welformedness.

Set Implict Arguments.

Module Taskview.
  Require Import HJ.Phasers.Taskview.
  Import Taskview.Semantics.
  Import Welformedness.Taskview.

  Inductive Lt v1 v2 : Prop :=
    tv_lt_def:
      signal_phase v1 < wait_phase v2 ->
      SignalCap (mode v1) ->
      WaitCap (mode v2) ->
      Lt v1 v2.

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

(*
  Let signal_preserves_rhs:
    forall v v',
    Ge v v' ->
    Ge v (Taskview.signal v').
  Proof.
    intros.
    unfold Taskview.signal.
    destruct v';
    inversion H; simpl in *;
    first [
      solve [(apply tv_ge_ge;
      simpl in  *;
      destruct mode; (simpl in *; auto))] |
      (subst; auto using tv_ge_so, tv_ge_wo) ].
  Qed.

  Let wait_preserves_rhs:
    forall v,
    (wait_phase v < signal_phase v) % nat ->
    Welformed v ->
    Ge v (Taskview.wait v).
  Proof.
    intros.
    apply tv_ge_ge.
    rewrite wait_wait_phase.
    intuition.
  Qed.
*)
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
(*
  Lemma tv_ge_reduce:
    forall v o v',
    Welformed v ->
    Reduce v o v' ->
    Ge v v'.
  Proof.
    intros.
    assert (Hx := H0).
    apply reduce_spec in Hx.
    subst.
    assert (Ge v v) by auto using tv_welformed_to_ge_refl.
    destruct o; simpl.
    - auto using signal_preserves_rhs.
    - inversion H0.
      auto using wait_preserves_rhs.
  Qed.
*)
  Let tv_signal_ge_lhs:
    forall v v',
    Welformed v ->
    Reduce v SIGNAL v' ->
    Ge v' v.
  Proof.
    intros.
    inversion H0.
    subst.
    apply signal_preserves_lhs; auto using tv_welformed_to_ge_refl.
  Qed.

  Let tv_wait_ge_lhs:
    forall v,
    (wait_phase v < signal_phase v) % nat ->
    Ge (wait v) v.
  Proof.
    intros.
    apply tv_ge_ge.
    intuition.
 Qed.

  Lemma tv_ge_reduce:
    forall v o v',
    Welformed v ->
    Reduce v o v' ->
    Ge v' v.
  Proof.
    intros.
    inversion H0; subst.
    - auto using tv_signal_ge_lhs.
    - auto using tv_wait_ge_lhs.
  Qed.

  Let tv_ge_reduce_trans_sw:
    forall x o y o' z,
    Welformed x ->
    Welformed y ->
    Welformed z ->
    Reduce x o y ->
    Reduce y o' z ->
    mode x = SIGNAL_WAIT ->
    (signal_phase z >= wait_phase x)%nat.
  Proof.
    intros.
    assert (Ge z y) by eauto using tv_ge_reduce.
    assert (Ge y x) by eauto using tv_ge_reduce.
    destruct o.
    - apply reduce_rw_signal in H2.
      destruct o'.
      + apply reduce_rw_signal in H3.
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
      + apply reduce_rw_wait in H3.
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
      assert (o' = SIGNAL) by eauto using reduce_trans_inv.
      subst.
      assert (R: signal_phase y = wait_phase y) by eauto using reduce_wait_inv_wait_cap.
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

  Lemma tv_ge_reduce_trans:
    forall x o y o' z,
    Welformed x ->
    Welformed y ->
    Welformed z ->
    Reduce x o y ->
    Reduce y o' z ->
    z >= x.
  Proof.
    intros.
    assert (Ge z y) by eauto using tv_ge_reduce.
    assert (Ge y x) by eauto using tv_ge_reduce.
    assert (R1: mode y = mode x) by
      eauto using reduce_preserves_mode.
    assert (R2: mode z = mode y). {
      eauto using reduce_preserves_mode.
    }
    assert (R3: mode x = mode z) by
      (transitivity (mode y); auto).
    apply tv_ge_trans_helper with (y); auto.
    intros.
    assert (mode y = SIGNAL_WAIT). {
      destruct (mode y).
      - rewrite R1 in H7.
        contradiction H7.
        trivial.
      - rewrite R2 in H6.
        contradiction H6.
        trivial.
      - trivial.
    }
    assert (mode x = SIGNAL_WAIT). {
      rewrite <- R1.
      assumption.
    }
    eauto using tv_ge_reduce_trans_sw.
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
    Reduce v1 o v1' ->
    Ge v1' v2.
  Proof.
    intros.
    inversion H0.
    - apply tv_ge_ge.
      apply reduce_spec in H1.
      subst.
      auto using tv_eval_preserves_le.
    - auto using tv_ge_so.
    - apply reduce_preserves_mode in H1.
      rewrite H2 in H1.
      auto using tv_ge_wo.
  Qed.

  Lemma tv_ge_eval_rhs:
    forall v1 v2 o,
    Ge v1 (Semantics.eval o v2) ->
    Reduce v2 o (Semantics.eval o v2) ->
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
    Reduce v1 o (Semantics.eval o v1) ->
    Ge (Semantics.eval o v1) v2.
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

  (**
    In a wellformed phaser there is a well-defined difference
    between wait-phases. Let [vm] be the minimum wait-phase of a
    phaser, then the wait-phase of any phaser is given by

    Example 1:
     WO:(0, 0)
        (1, 0)
        (1, 1)
        (2, 1)
     SO:(5, 3)

   (*1, 0) >= (2, 1*)
   (*2, 1) >= (1, 0*)
   (1,0) >= (2+k, 3)
   (*1, 0) >= (1, 1*)
   (*2, 1) >= (1, 0*)
   
   (1,0) >= (0,0) WO (OK)
 WO:(0,0) >= *
 SO:(5, 3) >= (1, 0 )
   * >= (5,3):SO
   

    Example 2, if the smallest is not-signalled, then
    the wait phase difference is the same. The biggest
    signal-difference is 1.
    
        (0, 0)
        (1, 0)
    
  *)
  End Facts.
End Taskview.

Module Phaser.
  Import Taskview.
  Require Import HJ.Phasers.Taskview.
  Import Welformedness.Taskview.

  Require Import HJ.Phasers.Phaser.
  Import Phaser.Semantics.
  Import Welformedness.Phaser.

  Inductive Rel (R: taskview -> taskview -> Prop) (ph1 ph2:phaser) : Prop := 
    ph_rel_def:
      (forall t1 t2 v1 v2,
        Map_TID.MapsTo t1 v1 ph1 ->
        Map_TID.MapsTo t2 v2 ph2 ->
        R v1 v2) ->
      Rel R ph1 ph2.

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

  Let ph_ge_refl_preserves_reduce_some:
    forall ph ph' t o o',
    Welformed ph ->
    Ge ph ph ->
    Reduction ph t o ph' ->
    as_tv_op o = Some o' ->
    Ge ph' ph'.
  Proof.
    intros.
    assert (Hin : Map_TID.In t ph) by eauto using ph_in.
    apply Map_TID_Extra.in_to_mapsto in Hin.
    destruct Hin as (v, Hmt).
    assert (Semantics.Reduce v o' (Semantics.eval o' v)) by
        eauto using ph_reduce_to_tv_reduce.
      assert (ph' = Map_TID.add t (Semantics.eval o' v) ph) by
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
            tv_reduction_preserves_welformed,
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
            inversion H1.
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
                assert (signal_phase v1 >= S (wait_phase v)) by eauto.
                apply tv_ge_ge.
                intuition.
              }
              auto using tv_ge_wo.
            }
            contradiction H10.
            eauto using Map_TID_Extra.mapsto_to_in.
          - apply tv_ge_so.
            rewrite Semantics.eval_preserves_mode.
            assumption.
          - auto using tv_ge_wo.
        * inversion H0; eauto.
  Qed.

  Let ph_ge_refl_preserves_reduce_drop:
    forall ph ph' t,
    Ge ph ph ->
    Reduction ph t DROP ph' ->
    Ge ph' ph'.
  Proof.
    intros.
    inversion H0.
    subst.
    unfold drop in *.
    apply ph_rel_def.
    intros.
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

  Let ph_ge_refl_preserves_reduce_register:
    forall t r ph ph',
    Ge ph ph ->
    Reduction ph t (REGISTER r) ph' ->
    Ge ph' ph'.
  Proof.
    intros ? ? ? ? Hge R.
    inversion R; subst.
    apply ph_register_spec with (v:=v) in R; auto.
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
    Phaser.Semantics.Reduction ph t o ph' ->
    Ge ph' ph'.
  Proof.
    intros.
    remember (as_tv_op o) as o'.
    symmetry in Heqo'.
    destruct o' as [o'|].
    - eauto using ph_ge_refl_preserves_reduce_some.
    - destruct o; try (simpl in Heqo'; inversion Heqo'); clear Heqo'.
      + eauto using ph_ge_refl_preserves_reduce_drop.
      + eauto using ph_ge_refl_preserves_reduce_register.
  Qed.

  Let ph_ge_reduce_some:
    forall ph t o o' ph',
    Welformed ph ->
    Ge ph ph ->
    Reduction ph t o ph' ->
    as_tv_op o = Some o' ->
    Ge ph' ph.
  Proof.
    intros.
    assert (Hin : Map_TID.In t ph) by eauto using ph_in.
    apply Map_TID_Extra.in_to_mapsto in Hin.
    destruct Hin as (v, Hmt).
    assert (Semantics.Reduce v o' (Semantics.eval o' v)) by
    eauto using ph_reduce_to_tv_reduce.
    assert (ph' = Map_TID.add t (Semantics.eval o' v) ph) by
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
    Reduction ph t o ph' ->
    Ge ph' ph.
  Proof.
    intros ? ? ? ? WF Hge R.
    remember(as_tv_op o) as o'.
    symmetry in Heqo'.
    destruct o' as [o'|]; eauto using ph_ge_reduce_some.
    (destruct o; simpl in Heqo'; inversion Heqo'); clear Heqo'.
    - inversion R; subst.
      unfold drop in *.
      apply ph_rel_def.
      intros.
      apply Map_TID.remove_3 in H0.
      inversion Hge; eauto.
    - inversion R.
      subst.
      apply ph_register_spec with (v:=v) in R; auto.
      rewrite R; clear R.
      apply ph_rel_def; intros.
      apply Map_TID_Facts.add_mapsto_iff in H;
      destruct H as [(?,?)|(?,?)].
      + subst.
        assert (Taskview.Ge v v2) by (inversion Hge; eauto).
        auto using tv_ge_register_left.
      + inversion Hge; eauto.
  Qed.


  Lemma ph_ge_equal_rhs:
    forall ph1 ph2 ph2',
    Map_TID.Equal ph2 ph2' ->
    Ge ph2' ph1 ->
    Ge ph2 ph1.
  Proof.
    intros ? ? ? Heq G.
    unfold Map_TID.Equal in *.
    inversion G.
    apply ph_rel_def.
    intros.
    rewrite Map_TID_Facts.find_mapsto_iff in H0.
    rewrite Heq in H0.
    rewrite <- Map_TID_Facts.find_mapsto_iff in H0.
    eauto.
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
        Reduction p1 t o p2 ->
        ReducesUpdates p1 t o p2.

    Hint Constructors ReducesUpdates.

    Inductive ReducesDestructs p1 t : op -> phaser -> Prop :=
      reduces_destructs_def:
        forall p2,
        Reduction p1 t DROP p2 ->
        ReducesDestructs p1 t DROP p2.

    Hint Constructors ReducesDestructs.

    Lemma case_reduces:
      forall ph1 t o ph2,
      Reduction ph1 t o ph2 ->
      { ReducesUpdates ph1 t o ph2 } + { ReducesDestructs ph1 t o ph2 }.
    Proof.
      intros.
      destruct o; (solve [left; auto | right; auto]).
    Qed.
    
    Let reduces_signal_preserves_in:
      forall t ph1 t' o ph2,
      Map_TID.In t ph1 ->
      Update o ->
      Reduction ph1 t' o ph2 ->
      Map_TID.In t ph2.
    Proof.
      intros.
      assert (Hin : Map_TID.In t' ph1) by eauto using ph_in.
      apply Map_TID_Extra.in_to_mapsto in Hin.
      destruct Hin as (v, Hmt).
      inversion H0; subst; clear H0.
      - apply ph_signal_spec with (v:=v) in H1; auto.
        rewrite H1.
        auto using Map_TID_Extra.add_in.
      - apply ph_wait_spec with (v:=v) in H1; auto.
        rewrite H1.
        auto using Map_TID_Extra.add_in.
      - apply ph_register_spec with (v:=v) in H1; auto.
        rewrite H1.
        auto using Map_TID_Extra.add_in.
    Qed.

    Lemma reduces_mapsto_neq:
      forall t v ph1 t' o ph2,
      Map_TID.MapsTo t v ph1 ->
      t' <> t ->
      Reduction ph1 t' o ph2 ->
      Map_TID.MapsTo t v ph2.
    Proof.
      intros.
      assert (Hin : Map_TID.In t' ph1) by eauto using ph_in.
      apply Map_TID_Extra.in_to_mapsto in Hin.
      destruct Hin as (v', Hmt').
      destruct o.
      - apply ph_signal_spec with (v:=v') in H1; auto; rewrite H1.
        auto using Map_TID.add_2.
      - apply ph_wait_spec with (v:=v') in H1; auto; rewrite H1.
        auto using Map_TID.add_2.
      - inversion H1; unfold drop in *.
        auto using Map_TID.remove_2.
      - inversion H1; subst.
        apply ph_register_spec with (v:=v') in H1; auto; rewrite H1.
        apply Map_TID.add_2; auto.
        intuition.
        subst.
        contradiction H3.
        eauto using Map_TID_Extra.mapsto_to_in.
    Qed.

    Lemma reduces_mapsto_neq_rtl:
      forall t v ph1 t' o ph2,
      Map_TID.MapsTo t v ph2 ->
      t' <> t ->
      Reduction ph1 t' o ph2 ->
      Map_TID.MapsTo t v ph1 \/ exists r, o = REGISTER r /\ t = (get_task r).
    Proof.
      intros.
      assert (Hin : Map_TID.In t' ph1) by eauto using ph_in.
      apply Map_TID_Extra.in_to_mapsto in Hin.
      destruct Hin as (v', Hmt').
      destruct o.
      - apply ph_signal_spec with (v:=v') in H1; auto.
        rewrite H1 in H.
        left;
        eauto using Map_TID.add_3.
      - apply ph_wait_spec with (v:=v') in H1; auto; rewrite H1 in H.
        left; eauto using Map_TID.add_3.
      - inversion H1; unfold drop in *.
        rewrite <- H4 in *.
        left; eauto using Map_TID.remove_3.
      - inversion H1; subst.
        destruct (TID.eq_dec t (get_task r)).
        + eauto.
        + left.
          apply ph_register_spec with (v:=v') in H1; auto; rewrite H1 in *.
          rewrite Map_TID_Facts.add_mapsto_iff in H.
          destruct H.
          * destruct H.
            symmetry in H.
            contradiction.
          * destruct H; assumption.
    Qed.

    Lemma reduces_drop_mapsto_eq:
      forall t v ph1 ph2 t',
      Map_TID.MapsTo t v ph2 ->
      Reduction ph1 t' DROP ph2 ->
      t' <> t /\ Map_TID.MapsTo t v ph1.
    Proof.
      intros.
      inversion H0.
      unfold drop in *.
      rewrite <- H3 in H.
      rewrite Map_TID_Facts.remove_mapsto_iff in H.
      assumption.
    Qed.

    Lemma reduces_update_inv:
      forall t v ph1 t' o ph2,
      Map_TID.MapsTo t v ph1 ->
      ReducesUpdates ph1 t' o ph2 ->
      { Map_TID.MapsTo t v ph2 } + { exists o', (as_tv_op o = Some o' /\ t' = t /\ Map_TID.MapsTo t (Semantics.eval o' v) ph2) }.
    Proof.
      intros.
      destruct H0.
      destruct (TID.eq_dec t' t). {
        subst.
        destruct o.
        - right.
          exists Taskview.Semantics.SIGNAL.
          intuition.
          apply ph_signal_spec with (v:=v) in H1; auto; rewrite H1.
          auto using Map_TID.add_1.
        - right; exists Taskview.Semantics.WAIT; intuition.
          apply ph_wait_spec with (v:=v) in H1; auto; rewrite H1.
          auto using Map_TID.add_1.
        - left.
          inversion H0.
        - left.
          inversion H1; subst.
          apply ph_register_spec with (v:=v) in H1; auto; rewrite H1.
          apply Map_TID.add_2; auto.
          remember (set_mode _ _) as v'.
          intuition; subst.
          contradiction H3.
          eauto using Map_TID_Extra.mapsto_to_in.
      }
      left.
      eauto using reduces_mapsto_neq.
    Qed.
(*
    Lemma reduces_update_rev_inv:
      forall t v ph1 t' o ph2,
      Map_TID.MapsTo t v ph2 ->
      ReducesUpdates ph1 t' o ph2 ->
      { Map_TID.MapsTo t v ph1 } + { exists o', (as_tv_op o = Some o' /\ t' = t /\ Map_TID.MapsTo t (Semantics.eval o' v) ph2) }.
    Proof.
*)
    Lemma ph_trans_aux_1:
      forall ph1 ph2 ph3 : phaser,
      forall t t' o o',
      ReducesUpdates ph1 t o ph2  ->
      Reduction ph2 t' o' ph3 ->
      Ge ph3 ph2 ->
      Ge ph2 ph1 ->
      Ge ph3 ph1.
    Proof.
      intros.
      apply ph_rel_def.
      intros.
      destruct (reduces_update_inv _ _  _ _ _  _ H4 H).
      - inversion H1; eauto.
      - destruct e as (t_o, (Htv, (?, Hmt))); subst.
        apply tv_ge_eval_rhs with (t_o).
        + inversion H1; eauto. 
        + inversion H.
          eauto using ph_reduce_to_tv_reduce.
    Qed.

    Notation WF ph := (Ge ph ph).
    Variable ph1 : phaser.
    Variable ph2 : phaser.
    Variable ph3 : phaser.
    Variable wf1: WF ph1.
    Variable wf2: WF ph2.
    Variable wf3: WF ph3.
    Variable W1: Welformed ph1.
    Variable W2: Welformed ph2.
    Variable W3: Welformed ph3.

    Let trans2:
      forall t t',
      Reduction ph1 t DROP ph2  ->
      Reduction ph2 t' DROP ph3 ->
      Ge ph3 ph2 ->
      Ge ph2 ph3 ->
      Ge ph3 ph1.
    Proof.
      intros ? ? R1 R2 G1 G2.
      apply ph_rel_def.
      intros.
      assert (Map_TID.MapsTo t1 v1 ph2). {
        apply reduces_drop_mapsto_eq with (t:=t1) (v:=v1) in R2; auto.
        destruct R2.
        assumption.
      }
      assert (Map_TID.MapsTo t1 v1 ph1). {
        apply reduces_drop_mapsto_eq with (t:=t1) (v:=v1) in R1; auto.
        destruct R1.
        assumption.
      }
      inversion wf1; eauto.
    Qed.
    
    Let has_task (o:op) :=
    match o with
    | REGISTER r => Some (get_task r)
    | _ => None
    end.

    Let ph_drop_register_commutes:
      forall t t' r,
      Reduction ph1 t DROP ph2  ->
      Reduction ph2 t' (REGISTER r) ph3 ->
      t <> get_task r ->
      exists ph2',
      (Reduction ph1 t' (REGISTER r) ph2'  /\
      exists ph3',
      Reduction ph2' t DROP ph3' /\ Map_TID.Equal ph3 ph3').
    Proof.
      intros.
      inversion H.
      apply ph_drop_spec in H; auto; rewrite H in *; clear H4 H.
      inversion H0.
      apply ph_register_spec with (v:=v) in H0; auto; rewrite H0 in *; clear H6 H H0 r0.
      exists (register t' r ph1).
      split.
      - apply reduction_register with (v).
        + unfold not; intros.
          contradiction H3.
          apply Map_TID_Facts.remove_neq_in_iff; auto.
        + eauto using Map_TID.remove_3.
        + auto.
      - remember (register t' r ph1) as ph2'.
        exists (drop t ph2').
        split.
        + apply reduction_drop.
    Admitted.

    Let trans3_sd:
      forall t r,
      Reduction ph1 (get_task r) DROP ph2 ->
      Reduction ph2 t (REGISTER r) ph3 ->
      Ge ph3 ph2 ->
      Ge ph2 ph1 ->
      Ge ph3 ph1.
    Proof.
      intros ? ? R1 R2 G1 G2.
      apply ph_rel_def.
      intros.
      destruct (TID.eq_dec t1 (get_task r)). {
        inversion R1; subst.
    Admitted.

    Let trans3_drop_register':
      forall t t' r,
      Reduction ph1 t DROP ph2 ->
      Reduction ph2 t' (REGISTER r) ph3 ->
      Ge ph3 ph2 ->
      Ge ph2 ph1 ->
      Ge ph3 ph1.
    Proof.
      intros ? ? ? R1 R2 G1 G2.
      destruct (TID.eq_dec t (get_task r)). {
        subst.
        eauto using trans3_sd.
      }
      assert (Hx := ph_drop_register_commutes _ _ _ R1 R2 n).
      destruct Hx as (ph2', (R1', (ph3', (R2', Heq)))).
      assert (Ge ph3' ph1). {
        assert (ReducesUpdates ph1 t' (REGISTER r) ph2') by
        auto using reduces_updates_def.
        assert (WF ph2') by
        eauto using ph_ge_refl_preserves_reduce.
        eauto using ph_trans_aux_1, ph_ge_reduce, ph_reduce_preserves_welformed.
      }
      eauto using ph_ge_equal_rhs.
    Qed.

    Let trans3:
      forall t o t',
      Reduction ph1 t DROP ph2  ->
      ReducesUpdates ph2 t' o ph3 ->
      Ge ph3 ph2 ->
      Ge ph2 ph1 ->
      Ge ph3 ph1.
    Proof.
      intros ? ? ? R1 R2 G1 G2.
      (* -- *)
      assert (i: Map_TID.In t' ph2) by (inversion R2;  eauto using ph_in).
      apply Map_TID_Extra.in_to_mapsto in i.
      destruct i as (v, mt).
      apply ph_rel_def; intros.
      destruct (TID.eq_dec t t2). {
        subst.
        destruct (TID.eq_dec t' t1). {
          subst.
          destruct (reduces_update_inv _ _  _ _ _  _ mt R2).
          + assert (v = v1)
            by eauto using Map_TID_Facts.MapsTo_fun; subst.
            inversion G2; eauto.
          + destruct e as (o', (Hv, (_, mt2))).
          assert (v1 = (Semantics.eval o' v))
          by eauto using Map_TID_Facts.MapsTo_fun; subst.
          clear H.
          assert (Taskview.Ge v v2) by (inversion G2; eauto).
          assert (Semantics.Reduce v o' (Semantics.eval o' v))
          by (inversion R2; eauto using ph_reduce_to_tv_reduce).
          assert (Taskview.Welformed v) by (inversion W2; eauto).
          eauto using tv_ge_eval_lhs.
        }
            
      }
      (* -- *)
      remember (has_task o) as m.
      symmetry in Heqm.
      apply ph_rel_def; intros.
      destruct (TID.eq_dec t t2). {
        subst.
        destruct (TID.eq_dec t' t2). {
          subst.
          assert (i: Map_TID.In t2 ph2) by (inversion R2;  eauto using ph_in).
          apply Map_TID_Extra.in_to_mapsto in i.
          destruct i as (v, mt).
          assert (Map_TID.MapsTo t2 v ph1). {
            apply reduces_drop_mapsto_eq with (t:=t2) (v:=v) in R1; auto.
            intuition.
          }
          assert (v = v2) by eauto using Map_TID_Facts.MapsTo_fun; subst.
          destruct (reduces_update_inv _ _  _ _ _  _ mt R2).
          + inversion wf3.
            eauto.
          + destruct e as (o', (Hx, (?, Hmt))).
            assert (Taskview.Ge v1 (Semantics.eval o' v2)). {
              inversion wf3; eauto.
            }
            assert (Semantics.Reduce v2 o' (Semantics.eval o' v2)). {
              inversion R2.
              eauto using ph_reduce_to_tv_reduce.
            }
            eauto using tv_ge_eval_rhs.
        }
        assert (Map_TID.MapsTo t2 v2 ph2 \/ exists r, o = REGISTER r /\ t2 = get_task r). {
          inversion R2.
          apply reduces_mapsto_neq_rtl with (t':=t') (ph2:=ph3); auto.
        }
        inversion wf2.
        assert
      }
    Qed.

    Variable t: tid.
    Variable t': tid.
    Variable o: op.
    Variable o': op.
    Variable R1: Reduction ph3 t o ph2.
    Variable R2: Reduction ph2 t' o' ph1.
    Variable G1: Ge ph1 ph2.
    Variable G2: Ge ph2 ph3.
    Lemma ge_ph_trans:
      Ge ph1 ph3.
    Proof.
      intros.
      apply ph_rel_def.
      intros tz tx z x mtz mtx.
      rename t' into ty.
      assert (i: Map_TID.In ty ph2) by eauto using ph_in.
      apply Map_TID_Extra.in_to_mapsto in i.
      destruct i as (y, mty).
      assert (Taskview.Ge z y) by (inversion G1; eauto).
      assert (Taskview.Ge y x) by (inversion G2; eauto).
      apply tv_ge_trans_helper with (y:=y); auto.
      intros.
      inversion H0.
      - 
      destruct (regmode_eq_dec (mode v2) WAIT_ONLY).
      {
        auto using tv_ge_wo.
        assert (mode x = WAIT_ONLY). {
        assert (mode y = WAIT_ONLY). {
          apply reduce_preserves_mode in H3.
          rewrite <- H3.
          assumption.
        }
        apply reduce_preserves_mode in H2.
        rewrite <- H2.
        assumption.
      }
      auto using tv_ge_wo.
    }
    destruct (regmode_eq_dec (mode z) SIGNAL_ONLY). {
      assert (mode x = SIGNAL_ONLY). {
        assert (mode y = SIGNAL_ONLY). {
          apply reduce_preserves_mode in H3.
          rewrite <- H3.
          assumption.
        }
        apply reduce_preserves_mode in H2.
        rewrite <- H2.
        assumption.
      }
      auto using tv_ge_so.
    }
    assert (mode z = SIGNAL_WAIT). {
      destruct (mode z);
        intuition.
    }
    assert (mode x = SIGNAL_WAIT). {
      transitivity (mode z); auto.
    }
      
    Qed.
  


End Phaser.

Module Phasermap.

Inductive PmRel (R: phaser -> phaser -> Prop) (m1 m2:phasermap) : Prop :=
  pm_rel_def:
    (forall p ph1 ph2,
      Map_PHID.MapsTo p ph1 m1 ->
      Map_PHID.MapsTo p ph2 m2 ->
      R ph1 ph2) ->
    PmRel R m1 m2.

Definition PmGe := PmRel PhGe.

Inductive Welformed (m:phasermap) :=
  pm_welformed_def:
    PmGe m m ->
    Welformed m.



Inductive TvValid (v:taskview) : Prop :=
  tv_valid_def:
    wait_phase <= signal_phase v - >
    TvValid  v

Inductive ValidPh (ph:phaser) : Prop := 
  valid_ph_def:
    (forall t v, Map_TID.MapsTo t v ph -> 


Lemma signal_respects_tv_ge_2:
  forall v,
  TvGe v v ->
  TvGe v (Taskview.signal v).
Proof.
  intros.
  unfold Taskview.signal.
  destruct v.
  inversion H; simpl in *.
  - apply tv_ge_ge.
    simpl in  *.
    destruct mode; (simpl in *; auto).
  - subst.
    auto using tv_ge_so.
  - subst.
    apply tv_ge_wo.
    auto.
Qed.
Import Phaser.

Lemma ph_update_respects_ph_ge
  (f: taskview -> taskview)
  (Hge1: forall v, TvGe v v -> TvGe (f v) (f v))
  (Hge2: forall v v', TvGe v v' -> TvGe (f v) v')
  (Hge3: forall v v', TvGe v v' -> TvGe v (f v')):
  forall t ph,
  PhGe ph ph ->
  PhGe (update t f ph) (update t f ph).
Proof.
  intros.
  unfold PhGe in *.
  unfold update in *.
  inversion H.
  apply ph_rel_def.
  intros.
  remember (Map_TID.find _ _) as o.
  symmetry in Heqo.
  destruct o.
  - rename t0 into v.
    apply Map_TID_Facts.add_mapsto_iff in H1.
    apply Map_TID_Facts.add_mapsto_iff in H2.
    destruct H1, H2;(
      destruct H1, H2;
      repeat subst;
      apply Map_TID_Facts.find_mapsto_iff in Heqo;
      eauto
    ).
  - eauto.
Qed.



Inductive Prec t1 m1 t2 m2 : Prop :=
  prec_def:
    forall p ph1 ph2 (v1 v2:taskview),
    Map_PHID.MapsTo p ph1 m1 ->
    Map_PHID.MapsTo p ph2 m2 ->
    Map_TID.MapsTo t1 v1 ph1 ->
    Map_TID.MapsTo t2 v2 ph2 ->
    TvPrec v1 v2 ->
    Prec t1 m1 t2 m2.

Inductive Registered (t:tid) (p:phid) (m:phasermap) :=
  registered_def:
    forall ph,
    Map_PHID.MapsTo p ph m ->
    Map_TID.In t ph ->
    Registered t p m.
    

Inductive Related (i1 i2:timestamp) : Prop :=
  related_def:
    forall p,
    Registered (fst i1) p (snd i1) ->
    Registered (fst i2) p (snd i2) ->
    Related i1 i2.

Lemma phase_ordering_step:
  forall m t1 t2 o1 o2 m1 m2,
  (* both tasks are related on at least one phaser *)
  Related (t1,m1) (t2,m2) ->
  Reduce m t1 o1 m1 ->
  Reduce m1 t2 o2 m2 ->
  ~ Prec (t2, m2) (t1, m1).
Proof.
  intros.
  intuition.
  inversion H2.
  simpl in *.
  inversion H0; subst.
  simpl in *.
  inversion H; subst.
  -  
Admitted.


(** Reduction rule that hides the task and operation. *)

Inductive SilentReduction (m m':phasermap) : Prop :=
  silent_reduce_def:
    forall t o,
    Reduce m t o m' ->
    SilentReduction m m'.

Require Import Coq.Relations.Relation_Operators.

Definition StarReduce := clos_trans phasermap SilentReduction.

Lemma phase_ordering_step:
  forall m m',
  SilentReduction m m' ->
  forall t' t, ~ Prec (t', m') (t, m).
Proof.
  intros.
  destruct H as (t'', o, H).
  
Admitted.

Theorem phase_ordering_correct:
  forall m1 m2,
  StarReduce m1 m2 ->
  forall t1 t2,
  ~ Prec (t2,m2) (t1,m1).
Proof.
  intros m1 m2 H.
  induction H; intros.
  - auto using phase_ordering_step.
  - intuition.

(*
 Is it possible for i1 < i2 an i2 < i1?
*)

(*
  M ->^(i1,t1) -> M1 ->*^(i2,t2) -> M1
  \/
  M ->^(i2,t2) -> M2 ->*^(i1,t1) -> M1

Here we only consider two triplets:

(i1,t1,M1) and (i2, t2, M2)

Although, for the discussions only i an M is important.
*)

(*
The activity executing i1 is registered on phaser ph as
wait-only. Then S(ph, i1) = ∞, and the S(ph, i1) <
W(ph, i2) precondition will be false.

Can we conclude anything about the precondition being false?

*)

(*
The activity executing i1 is registered on phaser ph as
signal-only. If S(ph, i1) < W(ph, i2) then i2 is being
executed by an activity that has waited on the phaser
more times than the activity executing i1 has signaled.
It must be that i1 is executed before i2 , because i2
could not be executed without at least one more signal
from the activity executing i1 .

If t1 <ph t2, then
  M ->^(i1,t1) -> M1 ->*^(i2,t2) -> M1
and
  ~ M ->^(i2,t2) -> M2 ->*^(i1,t1) -> M1

*)

(*
 The activity executing i1 is registered on phaser ph
as signal-wait. If S(ph, i1 ) < W(ph, i2) then the same
argument follows as in the signal case above. If i1
occurs in a split phase then we cannot establish any
order on the activities executing in the next wait phase
W(ph, i1) + 1 because we have signaled that they may
continue on to phase W(ph, i1 ) + 1. The inequality
will only hold for instructions two wait phases ahead,
W(ph, i1) + 2.
---

If t1 <ph t2 and SPLIT-PHASE t1 - t2 = 1, then what can we conclude?

---

Can we use the phase-ordering property to verify the correctness of the semantics?

For instance, can we just state that for any:
forall m m',
m reducesto m' ->
forall t t', ~ (t', m') < (t, m)
?
*)
Example case3:
  forall x y a b ph,
  x <> y ->
  Map_TID.MapsTo x a ph ->
  Map_TID.MapsTo y b ph ->
  signal_phase a < wait_phase b ->
  WaitCap a ->
  SignalCap b ->
  (forall v, signal_phase v >= wait_phase v) ->
  signal_phase a = wait_phase a + 1 ->
  (forall t, t <> x -> forall v, Map_TID.MapsTo t v ph -> signal_phase v = wait_phase v) ->
  signal_phase b >= wait_phase a + 1.
Proof.
  intros.
  assert (RW: signal_phase b = wait_phase b) by eauto; rewrite RW in *; clear RW H7.
  rewrite H6 in *; clear H6.
  intuition.
Qed.

(*
Lemma phase_ordering:
  forall m x y p ph,
  Map_PHID.MapsTo p ph m ->
  Sync ph 1 ->
  Map_TID.MapsTo x (TV 0 0 SIGNAL_WAIT) ph ->
  Map_TID.MapsTo y (TV 2 2 SIGNAL_WAIT) ph ->
  exists m', Reduce m x WAIT_ALL m'.
Proof.
  intros.
  exists (mapi ph 
Qed.
*)
Lemma phase_ordering:
  forall m x y m',
  Prec m x y ->
  ~ Reduce m x WAIT_ALL m'.
Proof.
  intros.
  intuition.
  inversion H0; clear H0; subst.
  destruct H.
  apply H1 in H; clear H1.
  inversion H; subst.
  - assert (v0 = v) by eauto using Map_TID_Extra.F.MapsTo_fun; subst.
    inversion H4;
    rewrite H6 in H7; inversion H7.
  - assert (v0 = v) by eauto using Map_TID_Extra.F.MapsTo_fun; subst.
    assert (Hx : signal_phase v' >= wait_phase v + 1) by (unfold Await in *; eauto).
    clear H7.
    (* 
      signal_phase v' >= wait_phase v + 1
      signal_phase v < wait_phase v'
      ---
      v' > v + 1
      v < v'
      ---
      y + k >= x + 1
      x + l < y
      ---
      y >= x + 1 - k
      x + l < y
      ---
      l < 1 - k
      ---
      if k = 0 -> true
      if k > 1 -> false
      ---
      if signal_phase v' = wait_phase v'
      then true
      else false
      *)
      
      assert (n: ~signal_phase v' < wait_phase v)). {
        intuition.
      }
    contradiction n.
    
    
Qed.  