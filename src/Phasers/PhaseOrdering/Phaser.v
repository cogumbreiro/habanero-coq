Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.

Require Import HJ.Vars.
Require Import HJ.Phasers.Regmode.
Require Import HJ.Phasers.Taskview.
Require Import HJ.Phasers.Phaser.
Require Import HJ.Phasers.WellFormed.
Require Import HJ.Phasers.PhaseOrdering.Taskview.
Import WellFormed.Taskview.
Import WellFormed.Phaser.
Import PhaseOrdering.Taskview.

Set Implicit Arguments.

Section Defs.
  Inductive Forall (R: taskview -> taskview -> Prop) (ph1 ph2:phaser) : Prop := 
    ph_rel_def:
      (forall t1 t2 v1 v2,
        Map_TID.MapsTo t1 v1 ph1 ->
        Map_TID.MapsTo t2 v2 ph2 ->
        R v1 v2) ->
      Forall R ph1 ph2.

  Definition Facilitates := Forall Taskview.Facilitates.

  Inductive HappensBefore (ph1 ph2:phaser) : Prop :=
    ph_happens_before_def:
      forall t1 t2 v1 v2,
      Map_TID.MapsTo t1 v1 ph1 ->
      Map_TID.MapsTo t2 v2 ph2 ->
      Taskview.HappensBefore v1 v2 ->
      HappensBefore ph1 ph2.


  Definition MayHappenParallel x y := Facilitates y x.

  Definition BlockedBy x y := HappensBefore x y.

  Inductive WellOrdered x : Prop :=
    well_ordered_def:
      Facilitates x x ->
      WellOrdered x.

  Inductive Par x y: Prop :=
    par_def:
      Facilitates x y ->
      Facilitates y x ->
      Par x y.

End Defs.

Module Notations.
  Infix "<" := HappensBefore : phaser_scope.
  Infix ">" := BlockedBy : phaser_scope.
  Infix "<=" := MayHappenParallel : phaser_scope.
  Infix ">=" := Facilitates : phaser_scope.
  Infix "||" := Par : phaser_scope.
End Notations.

Section Facts.

  Lemma ph_rel_inv:
    forall R ph1 ph2 t1 t2 v1 v2,
    Map_TID.MapsTo t1 v1 ph1 ->
    Map_TID.MapsTo t2 v2 ph2 ->
    Forall R ph1 ph2 ->
    R v1 v2.
  Proof.
    intros.
    inversion H1.
    eauto.
  Qed.

  Lemma well_ordered_to_facilitates:
    forall v1 v2 t1 t2 ph,
    WellOrdered ph ->
    Map_TID.MapsTo t1 v1 ph ->
    Map_TID.MapsTo t2 v2 ph ->
    Taskview.Facilitates v1 v2.
  Proof.
    intros.
    destruct H as (Hx).
    inversion Hx.
    eauto.
  Qed.

  Lemma ph_hb_to_not_chb:
    forall ph1 ph2,
    HappensBefore ph1 ph2 ->
    ~ Facilitates ph1 ph2.
  Proof.
    intros.
    intuition.
    inversion H.
    inversion H0.
    assert (Taskview.Facilitates v1 v2) by eauto.
    assert (~ Taskview.Facilitates v1 v2) by auto using tv_hb_to_not_ge.
    contradiction H6.
  Qed.

  Lemma ph_chb_to_not_hb:
    forall ph1 ph2,
    Facilitates ph1 ph2 ->
    ~ HappensBefore ph1 ph2.
  Proof.
    intros.
    intuition.
    inversion H.
    inversion H0.
    assert (Taskview.Facilitates v1 v2) by eauto.
    assert (~ Taskview.Facilitates v1 v2) by auto using tv_hb_to_not_ge.
    contradiction H6.
  Qed.

  Lemma ph_hb_trans:
    forall ph1 ph2 ph3,
    HappensBefore ph1 ph2 ->
    HappensBefore ph2 ph3 ->
    WellOrdered ph2 ->
    HappensBefore ph1 ph3.
  Proof.
    intros.
    destruct H1.
    inversion H.
    inversion H0.
    clear H H0.
    assert (Taskview.Facilitates v0 v2) by (inversion H1; eauto).
    eauto using lt_trans_ex, ph_happens_before_def.
  Qed.

  Lemma ph_hb_irreflexive:
    forall ph,
    WellOrdered ph ->
    ~ (HappensBefore ph ph).
  Proof.
    intros.
    inversion H.
    auto using ph_chb_to_not_hb.
  Qed.

  Section Antisym.
  Variable x y:phaser.

  Variable wx: WellFormed x.
  Variable wy: WellFormed y.
  Variable gx: WellOrdered x.
  Variable gy: WellOrdered y.

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
    assert (Taskview.HappensBefore v1 v3). {
      inversion gx as (gx').
      inversion gx'.
      assert (Taskview.Facilitates v0 v2) by eauto.
      eauto using lt_trans_ex.
    }
    assert (~ Taskview.Facilitates v1 v3) by eauto using tv_hb_to_not_ge.
    assert (Taskview.Facilitates v1 v3) by (inversion gy as (gy'); inversion gy'; eauto).
    contradiction.
  Qed.
  End Antisym.

  Let ph_ge_refl_preserves_reduces_some:
    forall ph ph' t o o',
    WellFormed ph ->
    WellOrdered ph ->
    Reduces ph (t, o) ph' ->
    as_tv_op o = Some o' ->
    Facilitates ph' ph'.
  Proof.
    intros.
    assert (Hin : Map_TID.In t ph) by eauto using register_inv_in.
    apply Map_TID_Extra.in_to_mapsto in Hin.
    destruct Hin as (v, Hmt).
    assert (Taskview.Reduces v o' (Taskview.reduces o' v)) by
        eauto using ph_reduces_to_tv_reduce.
      assert (ph' = Map_TID.add t (Taskview.reduces o' v) ph) by
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
            tv_reduces_preserves_well_formed,
            ph_well_formed_to_tv_well_formed,
            tv_well_formed_to_ge_refl.
        * apply tv_lhs_eval_ge with (v2:=v2) in H3;
          eauto using ph_well_formed_to_tv_well_formed, well_ordered_to_facilitates.
      + apply Map_TID_Facts.add_mapsto_iff in H5.
        destruct H5 as [(?,?)|(?,?)].
        * subst.
          assert (R : Taskview.Facilitates v1 v) by
          eauto using well_ordered_to_facilitates.
          inversion R; clear R.
          - destruct o'; simpl in *.
            {
              rewrite <- signal_preserves_wait_phase in *.
              auto using tv_nhb_ge.
            }
            apply as_tv_op_inv_wait in H2.
            subst.
            inversion H1; simpl in *; subst; clear H1.
            inversion H3; simpl in *; subst; clear H3.
            inversion H7; subst; clear H7.
            inversion H8; subst; clear H8.
            simpl_red.
            rename v0 into v2.
            destruct (Regmode.can_signal_wo (mode v1)). {
              apply tv_nhb_ge.
              rewrite wait_wait_phase.
              eauto.
            }
            auto using tv_nhb_wo.
          - apply tv_nhb_so.
            rewrite reduces_preserves_mode.
            assumption.
          - auto using tv_nhb_wo.
        * eauto using well_ordered_to_facilitates.
  Qed.

  Let ph_ge_refl_preserves_reduces_drop:
    forall ph ph' t,
    WellOrdered ph ->
    Reduces ph (t, DROP) ph' ->
    WellOrdered ph'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    inversion H4; subst; clear H4; simpl in *.
    unfold drop in *.
    apply well_ordered_def.
    apply ph_rel_def.
    intros; simpl in *.
    apply Map_TID.remove_3 in H1.
    apply Map_TID.remove_3 in H2.
    eauto using well_ordered_to_facilitates.
  Qed.

  Definition wo_phaser := { ph: phaser | WellOrdered ph }.

  Instance HappensBefore_StrictOrder : StrictOrder
    (fun (x y:wo_phaser) => HappensBefore (proj1_sig x) (proj1_sig y)).
  Proof.
    apply Build_StrictOrder.
    - unfold Irreflexive, Reflexive, complement.
      intros.
      destruct x; simpl in *.
      apply ph_hb_irreflexive in H; auto.
    - unfold Transitive.
      intros.
      destruct x as (x, ?), y as (y, ?), z as (z, ?);
      simpl in *.
      eauto using ph_hb_trans.
  Qed.

  Let exists_dec := Map_TID_Extra.exists_dec (elt:=taskview) tid_eq_rw.

  Let tv_hb x y := if tv_hb_dec x y then true else false.

  Let hb_dec x y :=
  exists_dec
  (fun _ v1 =>
    match exists_dec (fun _ v2 => tv_hb v1 v2) y with
    | inl _ => true
    | inr _ => false
    end
  )
  x.

  Lemma hb_mhp_dec x y:
    { HappensBefore x y}
    +
    { MayHappenParallel y x }.
  Proof.
    destruct (hb_dec x y). {
      left.
      destruct s as ((?,v1), (?,?)); simpl in *.
      destruct (exists_dec _ y). {
        destruct s as ((?,v2),(?,?)); simpl in *.
        unfold tv_hb in H2.
        destruct (tv_hb_dec v1 v2). {
          eauto using ph_happens_before_def.
        }
        inversion H2.
      }
      inversion H0.
    }
    right.
    destruct s.
    apply ph_rel_def.
    intros.
    apply e in H.
    destruct (exists_dec _ y). {
      inversion H.
    }
    destruct s.
    apply e0 in H0.
    unfold tv_hb in *.
    destruct (tv_hb_dec v1 v2). {
      inversion H0.
    }
    auto using tv_not_lt_to_ge.
  Defined.

  Lemma well_ordered_dec x:
    { WellOrdered x } + { ~ WellOrdered x }.
  Proof.
    destruct (hb_mhp_dec x x). {
      right.
      unfold not; intros.
      destruct H.
      apply ph_hb_to_not_chb in h.
      contradiction.
    }
    auto using well_ordered_def.
  Defined.

  Lemma hb_to_not_mhp:
    forall x y,
    HappensBefore x y ->
    ~ MayHappenParallel y x.
  Proof.
    intros.
    inversion H.
    unfold not; intros N.
    inversion N.
    assert (Taskview.Facilitates v1 v2) by eauto.
    apply tv_hb_to_not_ge in H2.
    contradiction.
  Qed.

  Lemma not_mhp_to_hb:
    forall x y,
    ~ MayHappenParallel y x ->
    HappensBefore x y.
  Proof.
    intros.
    destruct (hb_mhp_dec x y); auto.
    contradiction.
  Qed.

  Lemma mhp_to_not_hb:
    forall x y,
    MayHappenParallel x y ->
    ~ HappensBefore y x.
  Proof.
    unfold not; intros.
    destruct H0, H.
    assert (Taskview.Facilitates v1 v2) by eauto.
    apply tv_hb_to_not_ge in H2.
    contradiction.
  Qed.

  Lemma not_hb_to_mhp:
    forall x y,
    ~ HappensBefore y x ->
    MayHappenParallel x y.
  Proof.
    intros.
    apply ph_rel_def; intros.
    destruct (Taskview.tv_hb_ge_dec v1 v2). {
      contradiction H.
      eauto using ph_happens_before_def.
    }
    assumption.
  Qed.

  Let tv_nhb_register_left:
    forall r v1 v2,
    r_le (get_mode r) (mode v1) ->
    Taskview.Facilitates v1 v2 ->
    Taskview.Facilitates (set_mode v1 (get_mode r)) v2.
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
    Taskview.Facilitates v v ->
    Taskview.Facilitates (set_mode v (get_mode r)) (set_mode v (get_mode r)).
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
    Taskview.Facilitates v1 v2 ->
    Taskview.Facilitates v1 (set_mode v2 (get_mode r)).
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
    WellOrdered ph ->
    Reduces ph (t, (REGISTER r)) ph' ->
    WellOrdered ph'.
  Proof.
    intros ? ? ? ? Hge R.
    inversion R; subst; simpl in *; clear R.
    inversion H2; subst; clear H2.
    assert (R:=H0).
    apply register_rw with (r:=r) in R; auto.
    rewrite R; clear R.
    apply well_ordered_def.
    apply ph_rel_def.
    intros ? ? ? ? Hmt1 Hmt2.
    apply Map_TID_Facts.add_mapsto_iff in Hmt1;
    destruct Hmt1 as [(?,?)|(?,?)].
    - subst.
      apply Map_TID_Facts.add_mapsto_iff in Hmt2;
      destruct Hmt2 as [(?,?)|(?,?)].
      + subst.
        eauto using well_ordered_to_facilitates, tv_nhb_register_both.
      + eauto using well_ordered_to_facilitates, tv_nhb_register_left.
    - apply Map_TID_Facts.add_mapsto_iff in Hmt2;
      destruct Hmt2 as [(?,?)|(?,?)].
      + subst.
        eauto using well_ordered_to_facilitates, tv_nhb_register_right.
      + eauto using well_ordered_to_facilitates.
  Qed.

  Theorem ph_ge_refl_preserves_reduce:
    forall ph t o ph',
    WellFormed ph ->
    WellOrdered ph ->
    Phaser.Reduces ph (t, o) ph' ->
    WellOrdered ph'.
  Proof.
    intros.
    remember (as_tv_op o) as o'.
    symmetry in Heqo'.
    destruct o' as [o'|].
    - apply well_ordered_def; inversion H0; eauto using ph_ge_refl_preserves_reduces_some.
    - destruct o; try (simpl in Heqo'; inversion Heqo'); clear Heqo'.
      + eauto using ph_ge_refl_preserves_reduces_drop.
      + eauto using ph_ge_refl_preserves_reduces_register.
  Qed.

  Let ph_ge_reduces_some:
    forall ph t o o' ph',
    WellFormed ph ->
    WellOrdered ph ->
    Reduces ph (t, o) ph' ->
    as_tv_op o = Some o' ->
    Facilitates ph' ph.
  Proof.
    intros.
    assert (Hin : Map_TID.In t ph) by eauto using register_inv_in.
    apply Map_TID_Extra.in_to_mapsto in Hin.
    destruct Hin as (v, Hmt).
    assert (Taskview.Reduces v o' (Taskview.reduces o' v)) by
    eauto using ph_reduces_to_tv_reduce.
    assert (ph' = Map_TID.add t (Taskview.reduces o' v) ph) by
    eauto using ph_to_tv_correct.
    subst.
    apply ph_rel_def.
    intros.
    apply Map_TID_Facts.add_mapsto_iff in H4;
    destruct H4 as [(?,?)|(?,?)].
    - subst.
      assert (Taskview.WellFormed v) by (inversion H; eauto).
      assert (Taskview.Facilitates v v2) by eauto using well_ordered_to_facilitates.
      eauto using tv_lhs_eval_ge.
    - eauto using well_ordered_to_facilitates.
  Qed.

  Lemma ph_ge_reduce:
    forall ph t o ph',
    WellFormed ph ->
    WellOrdered ph ->
    Reduces ph (t, o) ph' ->
    Facilitates ph' ph.
  Proof.
    intros ? ? ? ? WF Hge R.
    remember(as_tv_op o) as o'.
    symmetry in Heqo'.
    destruct o' as [o'|]; eauto using ph_ge_reduces_some.
    (destruct o; simpl in Heqo'; inversion Heqo'); clear Heqo';
    inversion R; subst;  simpl in *; clear R;
    inversion H2; subst; clear H2.
    - unfold drop in *.
      apply ph_rel_def.
      intros.
      apply Map_TID.remove_3 in H0.
      eauto using well_ordered_to_facilitates.
    - assert (R:= H0).
      apply register_rw with (r:=r) in H0; auto.
      rewrite H0 in *; clear H0.
      apply ph_rel_def; intros.
      apply Map_TID_Facts.add_mapsto_iff in H0;
      destruct H0 as [(?,?)|(?,?)].
      + subst.
        eauto using well_ordered_to_facilitates, tv_nhb_register_left.
      + eauto using well_ordered_to_facilitates.
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

    Inductive ReducesUpdates p1 : event -> phaser -> Prop :=
      reduces_updates_def:
        forall t o p2,
        Update o ->
        Reduces p1 (t, o) p2 ->
        ReducesUpdates p1 (t, o) p2.

    Hint Constructors ReducesUpdates.

    Inductive ReducesDestructs p1 : event -> phaser -> Prop :=
      reduces_destructs_def:
        forall p2 t,
        Reduces p1 (t, DROP) p2 ->
        ReducesDestructs p1 (t, DROP) p2.

    Hint Constructors ReducesDestructs.

    Lemma case_reduces:
      forall ph1 e ph2,
      Reduces ph1 e ph2 ->
      { ReducesUpdates ph1 e ph2 } + { ReducesDestructs ph1 e ph2 }.
    Proof.
      intros.
      destruct e as (?,[]); try (solve [left; auto | right; auto]).
    Qed.

    Lemma reduces_mapsto_neq:
      forall t v ph1 t' o ph2,
      Map_TID.MapsTo t v ph1 ->
      t' <> t ->
      Reduces ph1 (t', o) ph2 ->
      Map_TID.MapsTo t v ph2.
    Proof.
      intros.
      assert (Hin : Map_TID.In t' ph1) by eauto using register_inv_in.
      apply Map_TID_Extra.in_to_mapsto in Hin.
      destruct Hin as (v', Hmt').
      assert (R:=Hmt').
      inversion H1; subst; clear H1.
      destruct o; simpl in *;
      inversion H5; subst; clear H5.
      - apply signal_rw in R. rewrite R.
        auto using Map_TID.add_2.
      - apply wait_rw in R; rewrite R.
        auto using Map_TID.add_2.
      - unfold drop in *.
        auto using Map_TID.remove_2.
      - apply register_rw with (r:=r) in R. rewrite R.
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
      Reduces ph1 (t', o) ph2 ->
      Map_TID.MapsTo t v ph1 \/ exists r, o = REGISTER r /\ t = (get_task r).
    Proof.
      intros.
      assert (Hin : Map_TID.In t' ph1) by eauto using register_inv_in.
      apply Map_TID_Extra.in_to_mapsto in Hin.
      destruct Hin as (v', Hmt').
      inversion H1; subst; clear H1.
      assert (R:=Hmt').
      destruct o; simpl in *;
      inversion H5; subst; simpl in *; clear H5.
      - left.
        apply signal_rw in R.
        rewrite R in H.
        eauto using Map_TID.add_3.
      - apply wait_rw in R; rewrite R in H.
        left; eauto using Map_TID.add_3.
      - unfold drop in *.
        left; eauto using Map_TID.remove_3.
      - destruct (TID.eq_dec t (get_task r)).
        + eauto.
        + left.
          apply register_rw with (r:=r) in R; auto; rewrite R in *.
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
      ReducesUpdates ph1 (t', o) ph2 ->
      { Map_TID.MapsTo t v ph2 } + { exists o', (as_tv_op o = Some o' /\ t' = t /\ Map_TID.MapsTo t (Taskview.reduces o' v) ph2) }.
    Proof.
      intros.
      destruct (TID.eq_dec t' t). {
        subst.
        assert (rw:=H).
        destruct o; simpl in *; try destruct H1.
        - right.
          exists Taskview.SIGNAL.
          intuition.
          inversion H0; subst; clear H0.
          simpl_red.
          auto using signal_1.
        - right; exists Taskview.WAIT; intuition.
          inversion H0; subst; clear H0.
          simpl_red.
          auto using wait_1.
        - left.
          inversion H0; inversion H3.
        - left.
          inversion H0; subst; clear H0.
          simpl_red.
          auto using register_1.
      }
      left.
      inversion H0; subst; clear H0.
      eauto using reduces_mapsto_neq.
    Qed.
  End Trans.

  Lemma ph_reduces_updates_preserves_ge_left:
    forall x y z t o,
    WellFormed y ->
    Facilitates y x ->
    ReducesUpdates y (t, o) z ->
    Facilitates z x.
  Proof.
    intros.
    apply ph_rel_def.
    intros tz tx vz vx; intros.
    destruct (TID.eq_dec t tz). {
      subst.
      rename H1 into r.
      assert (i: Map_TID.In tz y) by (inversion r; eauto using register_inv_in).
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
      assert (vz = Taskview.reduces o' v) by eauto using Map_TID_Facts.MapsTo_fun.
      subst.
      assert (Taskview.Reduces v o' (Taskview.reduces o' v))
      by (inversion R; eauto using ph_reduces_to_tv_reduce).
      assert (Taskview.Facilitates v vx) by (inversion H0; eauto).
      assert (Taskview.WellFormed v) by (inversion H; eauto).
      eauto using tv_nhb_eval_lhs.
    }
    inversion H1; subst; clear H1.
    assert (R := H8).
    apply reduces_mapsto_neq_rtl with (t:=tz) (v:=vz) in R; auto.
    destruct R as [?|R]. { inversion H0; eauto. }
    destruct R as (r, (?, ?)).
    subst.
    simpl_red.
    assert (R: vz = set_mode v (get_mode r)). {
      eapply register_inv_1; eauto.
    }
    rewrite R in *; clear R.
    assert (Taskview.Facilitates v vx)
    by (inversion H0; eauto).
    eauto using tv_nhb_register_left.
  Qed.

  Lemma ph_reduces_drop_preserves_ge_left:
    forall x y z t,
    Facilitates y x ->
    Reduces y (t, DROP) z ->
    Facilitates z x.
  Proof.
    intros.
    apply ph_rel_def; intros tz tx vz vx; intros.
    simpl_red.
    apply drop_mapsto_inv in H1.
    destruct H1.
    inversion H; eauto.
  Qed.

  Require Import Coq.Relations.Relation_Operators.
  Require Import Coq.Relations.Operators_Properties.

  Lemma ph_s_reduces_preserves_ge_left:
    forall x y z,
    WellFormed y ->
    Facilitates y x ->
    SReduces y z ->
    Facilitates z x.
  Proof.
    intros.
    destruct H1.
    apply case_reduces in H1.
    destruct H1.
    - eauto using ph_reduces_updates_preserves_ge_left.
    - destruct r; eauto using ph_reduces_drop_preserves_ge_left.
  Qed.
  
  Lemma ph_s_reduces_trans_refl_well_formed:
    forall x y,
    WellFormed x ->
    clos_refl_trans phaser SReduces x y ->
    WellFormed y.
  Proof.
    intros.
    induction H0; auto.
    destruct H0.
    eauto using ph_reduces_preserves_well_formed.
  Qed.

  Lemma ph_s_reduces_trans_refl_ge_refl:
    forall x y,
    WellFormed x ->
    WellOrdered x ->
    clos_refl_trans phaser SReduces x y ->
    WellOrdered y.
  Proof.
    intros.
    induction H1; auto.
    - destruct H1.
      eauto using ph_ge_refl_preserves_reduce.
    - assert (WellFormed y) by eauto using ph_s_reduces_trans_refl_well_formed.
      eauto.
  Qed.

  Lemma ph_s_reduces_trans_refl_ge:
    forall x y,
    WellFormed x ->
    WellOrdered x ->
    clos_refl_trans phaser SReduces x y ->
    Facilitates y x.
  Proof.
    intros.
    rewrite clos_rt_rtn1_iff in H1.
    induction H1.
    - inversion H0; auto.
    - assert (WellFormed y). {
        rewrite <- clos_rt_rtn1_iff in H2.
        eauto using ph_s_reduces_trans_refl_well_formed.
      }
      eauto using ph_s_reduces_preserves_ge_left.
  Qed.

  Import Notations.
  Open Scope phaser_scope.

  Lemma ph_signal_lhs_ge_rhs:
    forall x t,
    WellOrdered x ->
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
      eauto using well_ordered_to_facilitates, signal_preserves_rhs.
    - eauto using well_ordered_to_facilitates.
  Qed.

  Lemma ph_wait_lhs_ge_rhs:
    forall x t,
    WellOrdered x ->
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
      assert (Taskview.Facilitates v1 v) by eauto using well_ordered_to_facilitates.
      rename v into v2.
      destruct H3.
      apply wait_preserves_rhs; eauto.
    - eauto using well_ordered_to_facilitates.
  Qed.

  Lemma ph_register_lhs_ge_rhs:
    forall x r t,
    WellOrdered x ->
    RegisterPre r t x ->
    x >= register r t x.
  Proof.
    intros.
    inversion H0; clear H0.
    apply ph_rel_def.
    intros.
    apply register_inv_mapsto in H4 as [?|(?,(v',(?,?)))]. {
      eauto using well_ordered_to_facilitates.
    }
    subst.
    assert (v' = v) by eauto using Map_TID_Facts.MapsTo_fun; subst; clear H5.
    apply tv_nhb_register_right; auto.
    eauto using well_ordered_to_facilitates.
  Qed.

  Lemma ph_drop_lhs_ge_rhs:
    forall x t,
    WellOrdered x ->
    DropPre t x ->
    x >= drop t x.
  Proof.
    intros.
    inversion H0.
    apply ph_rel_def.
    intros.
    apply drop_mapsto_inv in H3.
    destruct H3 as (?,?).
    eauto using well_ordered_to_facilitates.
  Qed.

  Lemma reduces_ne:
    forall x y,
    WellOrdered x ->
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

  Lemma reduces_par:
    forall x y,
    WellFormed x ->
    WellOrdered x ->
    SReduces x y ->
    x || y.
  Proof.
    intros.
    inversion H1.
    apply par_def.
    - eauto using reduces_ne.
    - eauto using ph_ge_reduce.
  Qed.

  Lemma ph_par_symm:
    forall x y,
    x || y <-> y || x.
  Proof.
    split; intros;
    inversion H; eauto using par_def.
  Qed.
End Facts.

