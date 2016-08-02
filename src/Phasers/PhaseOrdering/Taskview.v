Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.

Require Import HJ.Vars.
Require Import HJ.Phasers.WellFormed.

Set Implict Arguments.

(** Phase-ordering corresponds to a happens-before relation between taskviews. *)

Section Defs.
  Require Import HJ.Phasers.Regmode.
  Require Import HJ.Phasers.Taskview.
  Import WellFormed.Taskview.

  (** Taskview [v1] happened before [v2] when [v1] 
    signalled fewer times than [v2] observed. *)

  Inductive HappensBefore v1 v2 : Prop :=
    tv_hb_def:
      signal_phase v1 < wait_phase v2 ->
      CanSignal (mode v1) ->
      CanWait (mode v2) ->
      HappensBefore v1 v2.

  (** The negation of [HappensBefore] is [Facilitates]. *)

  Inductive Facilitates v1 v2 : Prop := 
    | tv_nhb_ge:
       signal_phase v1 >= wait_phase v2 ->
       Facilitates v1 v2
    | tv_nhb_so:
      mode v2 = SIGNAL_ONLY ->
      Facilitates v1 v2
    | tv_nhb_wo:
      mode v1 = WAIT_ONLY ->
      Facilitates v1 v2.

  Definition MayHappenParallel v1 v2 := Facilitates v2 v1.

  Definition BlockedBy v1 v2 := HappensBefore v2 v1.

  Definition get_wait_phase v :=
  match (mode v) with
  | SIGNAL_ONLY => 0
  | _ => wait_phase v
  end.

  Definition get_signal_phase v :=
  match (mode v) with
  | WAIT_ONLY => 0
  | _ => signal_phase v
  end.

  Definition union v1 v2 :=
  {| mode := union (mode v1) (mode v2);
     signal_phase := max (get_signal_phase v1) (get_signal_phase v2);
     wait_phase:=max (get_wait_phase v1) (get_wait_phase v2) |}.

End Defs.


Module Notations.
  Infix "<" := HappensBefore : phaser_scope.
  Infix ">" := BlockedBy : phaser_scope.
  Infix "<=" := MayHappenParallel : phaser_scope.
  Infix ">=" := Facilitates : phaser_scope.
End Notations.


Section Facts.    
  Open Scope phaser_scope.
  Import Notations.
  Import WellFormed.Taskview.

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

  Lemma tv_nhb_dec:
    forall v1 v2,
    { v1 >= v2 } + { ~ v1 >= v2 }.
  Proof.
    intros.
    destruct (ge_dec (signal_phase v1) (wait_phase v2)).
    { left; auto using tv_nhb_ge. }
    destruct (regmode_eq_dec (mode v2) SIGNAL_ONLY).
    { left; auto using tv_nhb_so. }
    destruct (regmode_eq_dec (mode v1) WAIT_ONLY).
    { left; auto using tv_nhb_wo. }
    right.
    intuition.
  Qed.

  Lemma tv_hb_dec:
    forall v1 v2,
    { v1 < v2 } + { ~ v1 < v2 }.
  Proof.
    intros.
    destruct (can_wait_dec (mode v2)). {
      destruct (can_signal (mode v1)). {
        destruct (lt_dec (signal_phase v1) (wait_phase v2)). {
          left; auto using tv_hb_def.
        }
        right; intuition.
      }
      right; intuition.
    }
    right; intuition.
  Qed.

  Lemma tv_nhb_to_not_lt:
    forall v1 v2,
    v1 >= v2 -> ~ v1 < v2.
  Proof.
    intros.
    intuition.
    - destruct H0; inversion H3.
    - destruct H2; inversion H3.
  Qed.

  Lemma tv_hb_to_not_ge:
    forall v1 v2,
    v1 < v2 -> ~ v1 >= v2.
  Proof.
    intros.
    intuition.
    - destruct H; inversion H3.
    - inversion H2; rewrite H3 in *; inversion H4.
  Qed.

  Lemma tv_not_lt_to_ge:
    forall v1 v2,
    ~ v1 < v2 -> v1 >= v2.
  Proof.
    intros.
    destruct (ge_dec (signal_phase v1) (wait_phase v2)).
    { auto using tv_nhb_ge. }
    destruct (regmode_eq_dec (mode v2) SIGNAL_ONLY).
    { auto using tv_nhb_so. }
    destruct (regmode_eq_dec (mode v1) WAIT_ONLY).
    { auto using tv_nhb_wo. }
    assert (HappensBefore v1 v2). {
      assert (signal_phase v1 < wait_phase v2) % nat by intuition.
      auto using tv_hb_def, neq_wo_to_can_signal, neq_so_to_can_wait.
    }
    contradiction.
  Qed.

  Lemma tv_not_lt_rw_tv_ge:
    forall v1 v2,
    ~ v1 < v2 <-> v1 >= v2.
  Proof.
    split; auto using tv_not_lt_to_ge, tv_nhb_to_not_lt.
  Qed.

  Lemma tv_not_ge_to_lt:
    forall v1 v2,
    ~ v1 >= v2 -> v1 < v2.
  Proof.
    intros.
    destruct (can_wait_dec (mode v2)). {
      destruct (can_signal (mode v1)). {
        destruct (lt_dec (signal_phase v1) (wait_phase v2)). {
          auto using tv_hb_def.
        }
        assert (Facilitates v1 v2). {
          assert (signal_phase v1 >= wait_phase v2) % nat by intuition.
          auto using tv_nhb_ge.
        }
        contradiction.
      }
      assert (Facilitates v1 v2) by
        auto using tv_nhb_wo, not_can_signal_to_wo.
      contradiction.
    }
    assert (Facilitates v1 v2) by
      auto using tv_nhb_so, not_can_wait_to_so.
    contradiction.
  Qed.

  Lemma tv_not_ge_rw_lt:
    forall v1 v2,
    ~ v1 >= v2 <-> v1 < v2.
  Proof.
    split; auto using tv_not_ge_to_lt, tv_hb_to_not_ge.
  Qed.

  Lemma tv_hb_ge_dec:
    forall v1 v2,
    { v1 < v2 } + { v1 >= v2 }.
  Proof.
    intros.
    destruct (tv_hb_dec v1 v2);
    auto using tv_not_lt_to_ge.
  Qed.

  Lemma tv_well_formed_to_ge_refl:
    forall v,
    WellFormed v ->
    v >= v.
  Proof.
    intros.
    inversion H;
      try (apply tv_nhb_ge;
      intuition || fail).
    - auto using tv_nhb_so.
    - auto using tv_nhb_wo.
  Qed.

  Let signal_preserves_lhs:
    forall v,
    WellFormed v ->
    forall v',
    v >= v' ->
    (Taskview.signal v) >= v'.
  Proof.
    intros.
    inversion H0; subst.
    - apply tv_nhb_ge.
      simpl; intuition.
    - auto using tv_nhb_so.
    - rewrite <- signal_preserves_mode in *.
      auto using tv_nhb_wo.
  Qed.

  Lemma signal_preserves_rhs:
    forall v1 v2,
    v1 >= v2 ->
    v1 >= (Taskview.signal v2).
  Proof.
    intros.
    inversion H; subst.
    - apply tv_nhb_ge.
      rewrite signal_preserves_wait_phase.
      assumption.
    - apply tv_nhb_so.
      rewrite signal_preserves_mode.
      assumption.
    - auto using tv_nhb_wo.
  Qed.

  Section wait_preserves_rhs.
  Variable v1 v2: taskview.
  Variable G1: v1 >= v2.
  Variable L1: CanSignal (mode v1) -> (signal_phase v1 >= S (wait_phase v2) )%nat.
  Variable L2: WaitPre v2.
  Lemma wait_preserves_rhs:
    v1 >= (wait v2).
  Proof.
    intros.
    inversion G1; subst; clear G1.
    - destruct (can_signal_wo_dec (mode v1)). {
        apply tv_nhb_ge.
        simpl.
        apply L1 in c; clear L1.
        intuition.
      }
      auto using tv_nhb_wo.
    - apply tv_nhb_so.
      rewrite wait_preserves_mode.
      assumption.
    - auto using tv_nhb_wo.
  Qed.
  End wait_preserves_rhs.

  Let tv_signal_ge_lhs:
    forall v v',
    WellFormed v ->
    Reduces v SIGNAL v' ->
    Facilitates v' v.
  Proof.
    intros.
    inversion H0.
    subst.
    apply signal_preserves_lhs; auto using tv_well_formed_to_ge_refl.
  Qed.

  Let tv_wait_ge_lhs:
    forall v,
    WaitPre v ->
    Facilitates (wait v) v.
  Proof.
    intros.
    destruct H.
    - apply tv_nhb_wo.
      rewrite wait_preserves_mode.
      assumption.
    - apply tv_nhb_ge.
      rewrite wait_preserves_signal_phase.
      intuition.
 Qed.

  Let tv_nhb_reduces:
    forall v o v',
    WellFormed v ->
    Reduces v o v' ->
    Facilitates v' v.
  Proof.
    intros.
    inversion H0; subst.
    - auto using tv_signal_ge_lhs.
    - auto using tv_wait_ge_lhs.
  Qed.

  Let tv_nhb_reduces_trans_sw:
    forall x o y o' z,
    WellFormed x ->
    WellFormed y ->
    WellFormed z ->
    Reduces x o y ->
    Reduces y o' z ->
    mode x = SIGNAL_WAIT ->
    (signal_phase z >= wait_phase x)%nat.
  Proof.
    intros.
    assert (Facilitates z y) by eauto using tv_nhb_reduces.
    assert (Facilitates y x) by eauto using tv_nhb_reduces.
    destruct o.
    - inversion H2.
      assert (o' = WAIT) by eauto using reduces_signal_inv_sw; subst.
      apply reduces_rw_signal in H2.
      apply reduces_rw_wait in H3.
      subst.
      rewrite wait_preserves_signal_phase.
      simpl.
      assert (wait_phase x = signal_phase x). {
        inversion H7.
        - trivial.
        - rewrite H4 in H3.
        inversion H3.
      }
      intuition.
    - assert (CanWait (mode x)). {
        rewrite H4.
        auto using can_wait_sw.
      }
      assert (o' = SIGNAL) by eauto using reduces_wait_inv_sw; subst.
      assert (R: signal_phase y = wait_phase y) by eauto using reduces_wait_inv_can_wait.
      inversion H2; subst.
      inversion H3; subst.
      rewrite wait_preserves_signal_phase in *.
      rewrite signal_can_wait_signal_phase in *; auto.
      rewrite wait_wait_phase in *.
      intuition.
  Qed.

  Let tv_eval_preserves_le:
    forall v1 v2 o,
    WellFormed v1 ->
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
    WellFormed v1 ->
    Facilitates v1 v2 ->
    Reduces v1 o v1' ->
    Facilitates v1' v2.
  Proof.
    intros.
    inversion H0.
    - apply tv_nhb_ge.
      apply reduces_spec in H1.
      subst.
      auto using tv_eval_preserves_le.
    - auto using tv_nhb_so.
    - apply reduces_preserves_mode in H1.
      rewrite H2 in H1.
      auto using tv_nhb_wo.
  Qed.

  Lemma tv_nhb_eval_lhs:
    forall v1 v2 o,
    WellFormed v1 ->
    Facilitates v1 v2 ->
    Reduces v1 o (eval o v1) ->
    Facilitates (eval o v1) v2.
  Proof.
    intros.
    inversion H0.
    - apply tv_nhb_ge.
      destruct o; simpl in *.
      + intuition.
      + assumption.
    - auto using tv_nhb_so.
    - apply tv_nhb_wo.
      rewrite eval_preserves_mode.
      assumption.
  Qed.

  Theorem tv_lt_irreflexive:
    forall v,
    WellFormed v ->
    ~ (HappensBefore v v).
  Proof.
    intros.
    rewrite tv_not_lt_rw_tv_ge.
    auto using tv_well_formed_to_ge_refl.
  Qed.

  Theorem tv_lt_trans:
    forall x y z,
    WellFormed y ->
    x < y ->
    y < z ->
    x < z.
  Proof.
    intros.
    inversion H0.
    inversion H1.
    apply tv_hb_def; auto.
    assert (mode y = SIGNAL_WAIT) by eauto using can_signal_can_wait_to_sw.
    assert (wait_phase y <= signal_phase y)%nat. {
      apply tv_well_formed_inv_sw in H8; auto.
      destruct H8; intuition.
    }
    intuition.
  Qed.

  Section Antisym.

  Variable x y:taskview.
  
  Variable wfx: WellFormed x.
  Variable wfy: WellFormed y.

  Theorem tv_lt_antisym:
    x < y ->
    ~ (y < x).
  Proof.
    intros.
    rewrite tv_not_lt_rw_tv_ge.
    inversion H; clear H.
    simpl in *.
    inversion H1; clear H1. {
      subst.
      inversion H2; clear H2. {
        symmetry in H3.
        symmetry in H1.
        apply tv_nhb_ge.
        assert (wait_phase x <= signal_phase x) % nat by
        auto using well_formed_wait_phase_le_signal_phase.
        assert (wait_phase y <= signal_phase y) % nat by
        auto using well_formed_wait_phase_le_signal_phase.
        intuition.
      }
      subst.
      auto using tv_nhb_wo.
    }
    subst.
    auto using tv_nhb_so.
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
    apply tv_hb_def; auto.
    inversion H0.
    - intuition.
    - rewrite H1 in *.
      inversion H4.
    - rewrite H1 in *.
      inversion H5.
  Qed.

  Let wait_phase_fst_can_wait:
    forall v1 v2,
    CanWait (mode v1) ->
    (wait_phase v1 <= wait_phase (union v1 v2))%nat.
  Proof.
    intros.
    inversion H; subst; clear H; unfold union; simpl;
    unfold get_wait_phase;
    rewrite <- H1;
    auto using Max.le_max_l, Max.le_max_r.
  Qed.

  Let wait_phase_snd_can_wait:
    forall v1 v2,
    CanWait (mode v2) ->
    (wait_phase v2 <= wait_phase (union v1 v2))%nat.
  Proof.
    intros.
    inversion H; subst; clear H; unfold union; simpl;
    unfold get_wait_phase;
    rewrite <- H1;
    auto using Max.le_max_l, Max.le_max_r.
  Qed.

  Let can_wait_union_fst:
    forall r1 r2,
    CanWait r1 ->
    CanWait (Regmode.union r1 r2).
  Proof.
    intros.
    inversion H;simpl; auto using can_wait_sw, can_wait_wo.
    destruct r2; auto.
  Qed.

  Let can_wait_union_snd:
    forall r1 r2,
    CanWait r2 ->
    CanWait (Regmode.union r1 r2).
  Proof.
    intros.
    destruct r1; auto.
    inversion H;simpl; auto using can_wait_sw, can_wait_wo.
  Qed.

  Lemma union_lt_fst:
    forall v1 v2 v,
    v < v1 ->
    v < (union v1 v2).
  Proof.
    intros.
    inversion H; subst.
    apply tv_hb_def.
    - assert (wait_phase v1 <= wait_phase (union v1 v2))%nat by eauto.
      omega.
    - assumption.
    - unfold union; simpl.
      auto.
  Qed.

  Lemma union_lt_snd:
    forall v1 v2 v,
    v < v2 ->
    v < (union v1 v2).
  Proof.
    intros.
    inversion H; subst.
    apply tv_hb_def.
    - assert (wait_phase v2 <= wait_phase (union v1 v2))%nat by eauto.
      omega.
    - assumption.
    - unfold union; simpl.
      auto.
  Qed.

  Let can_wait_inv_union:
    forall r1 r2,
    CanWait (Regmode.union r1 r2) ->
    CanWait r1 \/ CanWait r2.
  Proof.
    unfold Regmode.union; intros.
    destruct r1; auto.
    destruct r2; auto.
  Qed.

  Lemma union_lt:
    forall v v1 v2,
    v < union v1 v2 ->
    v < v1 \/ v < v2.
  Proof.
    unfold union, get_wait_phase, get_signal_phase; intros.
    inversion H; simpl in *; clear H.
    apply can_wait_inv_union in H2.
    destruct (regmode_eq_dec (mode v1) SIGNAL_ONLY). {
      rewrite e in *.
      destruct (regmode_eq_dec (mode v2) SIGNAL_ONLY). {
        rewrite e0 in *.
        destruct H2 as [N|N]; inversion N.
      }
      destruct H2 as [N|N]. {
        inversion N.
      }
      simpl in *.
      assert (signal_phase v < wait_phase v2) % nat. {
        destruct (mode v2); auto.
        omega.
      }
      auto using tv_hb_def.
    }
    assert (R: match mode v1 with
        | SIGNAL_ONLY => 0
        | WAIT_ONLY => wait_phase v1
        | SIGNAL_WAIT => wait_phase v1
        end = wait_phase v1). {
      destruct (mode v1); auto.
      contradiction n; auto.
    }
    rewrite R in *; clear R.
    destruct (regmode_eq_dec (mode v2) SIGNAL_ONLY). {
      rewrite e in *.
      rewrite Max.max_0_r in *.
      destruct H2. {
        auto using tv_hb_def.
      }
      inversion H.
    }
    assert (R: match mode v2 with
        | SIGNAL_ONLY => 0
        | WAIT_ONLY => wait_phase v2
        | SIGNAL_WAIT => wait_phase v2
        end = wait_phase v2). {
      destruct (mode v2); auto.
      contradiction n0; auto.
    }
    rewrite R in *; clear R.
    destruct (Max.max_dec (wait_phase v1) (wait_phase v2)). {
      rewrite e in *.
      apply neq_so_to_can_wait in n.
      auto using tv_hb_def.
    }
    rewrite e in *.
    apply neq_so_to_can_wait in n0.
    auto using tv_hb_def.
  Qed.

  Theorem tv_hb_union_spec:
    forall v v1 v2,
    v < union v1 v2 <->
    (v < v1 \/ v < v2).
  Proof.
    intros.
    split; intros.
    - auto using union_lt.
    - destruct H;
      auto using union_lt_snd, union_lt_fst.
  Qed.

  Example tv_ex_1:
    {| signal_phase := 0; wait_phase := 0; mode := SIGNAL_WAIT |} <
    {| signal_phase := 1; wait_phase := 1; mode := SIGNAL_WAIT |}.
  Proof.
    eauto using tv_hb_def.
  Qed.

  Example tv_ex_2:
    forall (v:taskview),
    SignalPre v ->
    WaitPre (signal v) ->
    mode v = SIGNAL_WAIT ->
    v < (wait (signal v)).
  Proof.
    intros.
    inversion H0; clear H0. {
      rewrite signal_preserves_mode in *.
      rewrite H1 in H2.
      inversion H2.
    }
    apply tv_hb_def.
    - rewrite wait_wait_phase in *.
      rewrite signal_preserves_wait_phase in *.
      simpl in *.
      intuition.
    - rewrite H1.
      apply can_signal_sw.
    - rewrite wait_preserves_mode.
      rewrite signal_preserves_mode.
      rewrite H1.
      apply can_wait_sw.
  Qed.
End Facts.

