Require Import HJ.Tid.
Require Import HJ.Phasers.Regmode.
Require Import HJ.Phasers.Taskview.
Require Import Compare_dec.

Section Defs.

  (**
    A phaser is a map from task names [tid] into taskviews, represented
    by parametric type [Map_TID.t].
   *)

  Definition phaser := Map_TID.t taskview.

  (**
    The following record defines the specification of a phaser operation.
    An operation is issued by a task of type [tid] and targets a [phaser].
    The pre condition [can_run] must be satisfied to execute the implementation [run] on
    a given phaser.
   *)


  Record rule := mk_rule {
    pre: tid -> phaser -> Prop;
    pre_dec t ph : { pre t ph } + { ~ pre t ph };
    exec: tid ->  phaser -> phaser
  }.

  (**
    Function [make] creates a new phaser and registers task [t] with it.
    Task [t] becomes registered with the initial taskview [Taskview.make].
  *)

  Definition make t := Map_TID.add t Taskview.make (Map_TID.empty taskview).

  (** * Signal *)

  (**
    Function [update] targets a phaser [ph] and is used internally to mutate
    the taskview associated with task [t] using function [f] to mutate.
    If task [t] is not registered in [ph], then the phaser is left unchanged.
  *)

  Definition update (t:tid) (f:taskview -> taskview) (ph:phaser) : phaser :=
    match Map_TID.find t ph with
    | Some v => Map_TID.add t (f v) ph
    | None => ph
    end.

  (** For the signal to take any effect the task must be registered with the phaser. *)

  Inductive SignalPre (t:tid) (ph:phaser) : Prop :=
    signal_pre_def:
      forall v,
      Map_TID.MapsTo t v ph ->
      Taskview.SignalPre v ->
      SignalPre t ph.

  Definition signal_pre t ph :
    { SignalPre t ph } + { ~ SignalPre t ph }.
  Proof.
    remember (Map_TID.find t ph).
    symmetry in Heqo.
    destruct o as [v|]. {
      rewrite <- Map_TID_Facts.find_mapsto_iff in *.
      destruct (Taskview.signal_pre v). {
        eauto using signal_pre_def.
      }
      right; unfold not; intros N.
      contradiction n.
      inversion N.
      assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      assumption.
    }
    right; unfold not; intros N.
    inversion N.
    rewrite Map_TID_Facts.find_mapsto_iff in *.
    rewrite H in *.
    inversion Heqo.
  Defined.

  (**
    Signal just applies [Taskview.signal] to the taskview associated with
    task [t].
   *)

  Definition signal (t:tid) : phaser -> phaser := update t Taskview.signal.

  (**
    We now pair the pre condition with the implementation. This is later used
    in the definition of the operational semantics.
   *)

  Definition signal_op := mk_rule SignalPre signal_pre signal.

  (**
    Function [try_signal] can be called without a pre-condition. It is crucial for
    the definition of an instruction that signals all phasers.
   *)

  Definition try_signal (t:tid) : phaser -> phaser := update t Taskview.try_signal.

  (** * Wait *)

  (**
    Predicate [Phase ph n] holds when phase [n] is visible in phaser [ph].
    This means that all signalers have signaled at least [n] times.
    Predicate [Phase] _disregards_ any task registered with a [WAIT_ONLY] mode,
    regardless of its signal phase.
   *)

  Inductive Phase ph n : Prop :=
    phase_def:
      (forall t v,
        Map_TID.MapsTo t v ph ->
        CanSignal (mode v) ->
        signal_phase v >= n) ->
      Phase ph n.

  Definition signalers ph : list (tid * nat) :=
  let handle_task (p:tid * taskview) :=
    let (t, v) := p in
    if can_signal (mode v) then Some (t, signal_phase v)
    else None
  in
  List.omap handle_task (Map_TID.elements ph).

  Let signalers_1:
    forall x v ph,
    Map_TID.MapsTo x v ph ->
    CanSignal (mode v) ->
    List.In (x, signal_phase v) (signalers ph).
  Proof.
    intros.
    unfold signalers.
    apply List.in_omap_1 with (x:=(x,v)). {
      rewrite Map_TID_Extra.maps_to_iff_in_elements in H; auto.
    }
    destruct (can_signal (mode v)). {
      trivial.
    }
    contradiction.
  Qed.

  Let signalers_2:
    forall x n ph,
    List.In (x, n) (signalers ph) ->
    exists v, Map_TID.MapsTo x v ph /\ CanSignal (mode v) /\ n = signal_phase v.
  Proof.
    unfold signalers; intros.
    apply List.in_omap_2 in H.
    destruct H as ((y, v), (Hi, Hp)).
    rewrite <- Map_TID_Extra.maps_to_iff_in_elements in Hi; auto.
    destruct (can_signal (mode v)). {
      inversion Hp; subst.
      eauto.
    }
    inversion Hp.
  Qed.

  Definition phase ph n:
    { Phase ph n } + { ~ Phase ph n }.
  Proof.
    remember (List.forallb (fun p => if ge_dec (snd p) n then true else false) (signalers ph)).
    symmetry in Heqb.
    destruct b. {
      rewrite List.forallb_forall in Heqb.
      left.
      apply phase_def.
      intros x; intros.
      assert (Hx: List.In (x, signal_phase v) (signalers ph)) by auto.
      apply Heqb in Hx.
      simpl in *.
      destruct (ge_dec (signal_phase v) n). {
        assumption.
      }
      inversion Hx.
    }
    right; unfold not; intros N.
    rewrite List.forallb_existsb in *.
    rewrite Bool.negb_false_iff in *.
    apply List.existsb_exists in Heqb.
    destruct Heqb as ((x,n'),(Hi, Hn)).
    rewrite Bool.negb_true_iff in *.
    simpl in *.
    apply signalers_2 in Hi.
    destruct Hi as (v, (Hm, (?,?))).
    destruct (ge_dec n' n). {
      inversion Hn.
    }
    inversion N.
    apply H1 in Hm; auto.
    subst.
    contradiction.
  Defined.

  (**
    Wait consists of thee pre-conditions: (i) task [t] is registered in phaser [ph],
    (ii) task [t] has signalled as per [Taskview.WaitPre],
    and (iii) task [t] must be able to synchronize with the other members through phaser [ph].
    *)

  Inductive WaitPre t ph : Prop  := 
    wait_pre_def:
      forall v,
      Map_TID.MapsTo t v ph ->
      Taskview.WaitPre v ->
      Phase ph (S (wait_phase v)) ->
      WaitPre t ph.

  Definition wait_pre x ph:
    { WaitPre x ph } + { ~ WaitPre x ph }.
  Proof.
    remember (Map_TID.find x ph).
    symmetry in Heqo.
    destruct o as [v|]. {
      rewrite <- Map_TID_Facts.find_mapsto_iff in *.
      destruct (Taskview.wait_pre v). {
        destruct (phase ph (S (wait_phase v))). {
          eauto using wait_pre_def.
        }
        right.
        unfold not; intros N.
        destruct N.
        assert (v0 = v) by eauto using  Map_TID_Facts.MapsTo_fun; subst.
        contradiction n.
      }
      right.
      unfold not; intros N.
      destruct N.
      assert (v0 = v) by eauto using  Map_TID_Facts.MapsTo_fun; subst.
      contradiction n.
    }
    right; unfold not; intros N.
    inversion N.
    rewrite Map_TID_Facts.find_mapsto_iff in *.
    rewrite H in *.
    inversion Heqo.
  Defined.

  (** Operationally, wait applies [Taskview.wait] on the taskview associated with task [t].*)

  Definition wait (t:tid) : phaser -> phaser := update t Taskview.wait.

  Definition wait_op := mk_rule WaitPre wait_pre wait.

  (**
    Function [try_wait] can be invoked by any *registered* task, needed to defined
    the deadlock-free operation [Phasermap.wait_all].
    *)

  Inductive TryWaitPre t ph : Prop :=
    | try_wait_pre_can_wait:
      WaitPre t ph ->
      TryWaitPre t ph
    | try_wait_pre_so:
      forall v,
      Map_TID.MapsTo t v ph ->
      mode v = SIGNAL_ONLY ->
      TryWaitPre t ph.

  Definition try_wait := wait.

  Definition try_wait_pre x ph:
    { TryWaitPre x ph } + { ~ TryWaitPre x ph }.
  Proof.
    destruct (wait_pre x ph). {
      auto using try_wait_pre_can_wait.
    }
    remember (Map_TID.find x ph).
    symmetry in Heqo.
    destruct o as [v|]. {
      rewrite <- Map_TID_Facts.find_mapsto_iff in *.
      destruct (regmode_eq (mode v) SIGNAL_ONLY). {
        eauto using try_wait_pre_so.
      }
      right; unfold not; intros N.
      inversion N. {
        contradiction.
      }
      assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst; contradiction.
    }
    right; unfold not; intros N.
    inversion N. { contradiction. }
    rewrite Map_TID_Facts.find_mapsto_iff in *.
    rewrite H in *.
    inversion Heqo.
  Qed.

  (** * Drop *)

  (**
    Function [drop] removes the taskview associated with the given task.
    The pre-condition to issue a [drop] is that task [t] must be registered
    in phaser [ph].
    *)

  Inductive DropPre t (ph:phaser) : Prop :=
    drop_pre_def:
      Map_TID.In t ph ->
      DropPre t ph.

  Definition drop_pre x ph:
    { DropPre x ph } + { ~ DropPre x ph }.
  Proof.
    remember (Map_TID.find x ph).
    symmetry in Heqo.
    destruct o. {
      rewrite <- Map_TID_Facts.find_mapsto_iff in *.
      apply Map_TID_Extra.mapsto_to_in in Heqo.
      auto using drop_pre_def.
    }
    right; unfold not; intros N.
    inversion N.
    rewrite <- Map_TID_Facts.not_find_in_iff in *.
    contradiction.
  Defined.

  Definition drop : tid -> phaser -> phaser := @Map_TID.remove taskview.

  Definition drop_op := mk_rule DropPre drop_pre drop.

  (** * Register *)

  (**
    Function [register] embodies the invocation of an async phased, and
    it requires the task being registered and the registration mode of the task.
    *)

  Record registry := mk_registry {
    get_task: tid;
    get_mode: regmode
  }.

  (**
    Register has two pre-conditions: (i) task [get_task r] must be
    unknown to phaser [ph], and (ii) the mode in registry [r] cannot escalate the
    capabilities of the issuer.
  *)

  Import Regmode.Notations.
  Open Scope reg_scope.

  Inductive RegisterPre r t ph : Prop :=
    register_pre_def:
      forall v,
      ~ Map_TID.In (get_task r) ph ->
      Map_TID.MapsTo t v ph ->
      get_mode r <= mode v ->
      RegisterPre r t ph.

  Definition register_pre r x ph:
    { RegisterPre r x ph } + { ~ RegisterPre r x ph }.
  Proof.
    remember (Map_TID.find (get_task r) ph).
    remember (Map_TID.find x ph).
    symmetry in Heqo.
    symmetry in Heqo0.
    destruct o. {
      right; unfold not; intros N.
      inversion N.
      contradiction H.
      rewrite <- Map_TID_Facts.find_mapsto_iff in *.
      eauto using Map_TID_Extra.mapsto_to_in.
    }
    rewrite <- Map_TID_Facts.not_find_in_iff in Heqo.
    destruct o0 as [v|]. {
      rewrite <- Map_TID_Facts.find_mapsto_iff in *.
      destruct (Regmode.le_dec (get_mode r) (mode v)). {
        eauto using register_pre_def.
      }
      right; unfold not; intros N; inversion N;
      assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst; contradiction.
    }
    rewrite <- Map_TID_Facts.not_find_in_iff in *.
    right; unfold not; intros N; inversion N.
    contradiction Heqo0.
    eauto using Map_TID_Extra.mapsto_to_in.
  Defined.

  Lemma register_pre_to_in:
    forall r t ph,
    RegisterPre r t ph ->
    Map_TID.In t ph.
  Proof.
    intros.
    inversion H.
    eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  (**
    Operationally, register adds task [get_task r]  to the phaser, assigning new taskview
    that is a copy of the issuer's taskview with the mode set to [get_mode r].
    *)

  Definition register (r:registry) (t:tid) (ph:phaser) : phaser := 
    match Map_TID.find t ph with
    | Some v => Map_TID.add (get_task r) (set_mode v (get_mode r)) ph
    | None => ph
    end.

  Definition register_op r := mk_rule (RegisterPre r) (register_pre r) (register r).


  (** * Operational semantics *)

  (** The operational semantics defines a closed set of the possible operations:
    signal, wait, drop (that deregisters the issuer),
    and register (that adds a new task to the phaser). *)

  Inductive op := SIGNAL | WAIT | DROP | REGISTER : registry -> op.

  (** Function [reduces] interprets operation [o] as its operation specification [Op]. *)

  Definition select_rule o :=
    match o with
    | SIGNAL => signal_op
    | WAIT => wait_op
    | DROP => drop_op
    | REGISTER r => register_op r
    end.

  (**
    Relation [Reduces] defines the operational semantics.
  *)

  Definition event := (tid * op) % type.

  Inductive Reduces ph: event -> phaser -> Prop :=
    reduces_def:
      forall t o,
      pre (select_rule o) t ph ->
      Reduces ph (t, o) (exec (select_rule o) t ph).

  Definition reduces (e:event) ph : option phaser :=
  if pre_dec (select_rule (snd e)) (fst e) ph
  then Some (exec (select_rule (snd e)) (fst e) ph)
  else None.

  Lemma reduces_1:
    forall e ph ph',
    reduces e ph = Some ph' ->
    Reduces ph e ph'.
  Proof.
    unfold reduces; intros.
    destruct e as (x, o).
    simpl in *.
    destruct (pre_dec (select_rule o)). {
      inversion H; subst.
      auto using reduces_def.
    }
    inversion H.
  Qed.

  Lemma reduces_2:
    forall e ph ph',
    Reduces ph e ph' ->
    reduces e ph = Some ph'.
  Proof.
    intros.
    unfold reduces.
    destruct e as (x, o).
    inversion H; subst; clear H.
    simpl.
    destruct (pre_dec (select_rule o) x ph). {
      trivial.
    }
    contradiction.
  Qed.

  Lemma reduces_3:
    forall e ph,
    reduces e ph = None ->
    forall ph', ~ Reduces ph e ph'.
  Proof.
    intros.
    unfold not; intros N.
    apply reduces_2 in N.
    rewrite N in *.
    inversion H.
  Qed.

  Fixpoint reduces_trace (l:list event) :=
  match l with
  | nil => Some (Map_TID.empty taskview)
  | (e :: nil) % list => reduces e (make (fst e))
  | (e::l) % list =>
    match reduces_trace l with
    | Some ph => reduces e ph
    | _ => None
    end
  end.

  (** Relation [SReducess] simply omits the task and operation of relation [Reduces]. *)

  Inductive SReduces (ph1:phaser) (ph2:phaser) : Prop :=
    ph_s_reduces:
      forall t o,
      Reduces ph1 (t, o) ph2 ->
      SReduces ph1 ph2.

  (** Finally, we declare a function that converts a [Phaser.op] to a [Taskview.op]. *)

  Definition as_tv_op (o:op) :=
    match o with
    | SIGNAL => Some Taskview.SIGNAL
    | WAIT =>  Some Taskview.WAIT
    | _ => None
    end.

End Defs.

(* * * * * * * * * * * *)

Section Facts.

  Let as_tv_op_inv_signal:
    forall o,
    as_tv_op o = Some Taskview.SIGNAL ->
    o = SIGNAL.
  Proof.
    intros.
    destruct o; auto; simpl in *; try (inversion H).
  Qed.

  Lemma as_tv_op_inv_wait:
    forall o,
    as_tv_op o = Some Taskview.WAIT ->
    o = WAIT.
  Proof.
    intros.
    destruct o; auto; simpl in *; try (inversion H).
  Qed.

  Lemma reduces_spec:
    forall ph t o ph',
    Reduces ph (t, o) ph' ->
    ph' = exec (select_rule o) t ph.
  Proof.
    intros.
    destruct o;
    simpl; inversion H; auto.
  Qed.

  Let update_rw:
    forall t v f ph,
    Map_TID.MapsTo t v ph ->
    update t f ph = Map_TID.add t (f v) ph.
  Proof.
    intros.
    unfold update.
      remember (Map_TID.find _ _).
      symmetry in Heqo.
      destruct o as [v'|].
      {
        apply Map_TID_Facts.find_mapsto_iff in Heqo.
        assert (v' = v) by eauto using Map_TID_Facts.MapsTo_fun.
        subst; clear Heqo.
        trivial.
      }
      apply Map_TID_Facts.not_find_in_iff in Heqo.
      contradiction Heqo.
      eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Lemma signal_rw:
    forall t v ph,
    Map_TID.MapsTo t v ph ->
    signal t ph = Map_TID.add t (Taskview.signal v) ph.
  Proof.
    intros.
    eauto.
  Qed.

  Lemma wait_rw:
    forall t v ph,
    Map_TID.MapsTo t v ph ->
    wait t ph = Map_TID.add t (Taskview.wait v) ph.
  Proof.
    intros.
    eauto.
  Qed.

  Lemma ph_drop_rw:
    forall t ph,
    drop t ph = Map_TID.remove t ph.
  Proof.
    unfold drop; auto.
  Qed.

  Lemma register_rw:
    forall t v r ph,
    Map_TID.MapsTo t v ph ->
    register r t ph = Map_TID.add (get_task r) (set_mode v (get_mode r)) ph.
  Proof.
    intros.
    unfold register in *.
    remember (Map_TID.find _ _ ).
    symmetry in Heqo.
    destruct o as [v'|].
    - rewrite Map_TID_Facts.find_mapsto_iff in *.
      assert (v' = v). {
        rewrite H in *.
        inversion Heqo.
        trivial.
      }
      subst.
      trivial.
    - apply Map_TID_Facts.not_find_in_iff in Heqo.
      contradiction Heqo.
      eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Lemma register_mapsto_neq:
    forall t t' t'' v ph r,
    t'' <> t' ->
    Map_TID.MapsTo t'' v
       (register {| get_task := t'; get_mode := r |} t ph) ->
    Map_TID.MapsTo t'' v ph.
  Proof.
    unfold register.
    intros.
    destruct (Map_TID_Extra.find_rw t ph) as [(R,?)|(v',(R,mt))]. {
      rewrite R in *; clear R.
      assumption.
    }
    rewrite R in *; clear R.
    rewrite Map_TID_Facts.add_mapsto_iff in H0.
    destruct H0 as [(?,?)|(?,?)].
    - simpl in *.
      subst.
      contradiction H; trivial.
    - assumption.
  Qed.

  Let register_in_1:
    forall t' r ph t,
    Map_TID.In t (register {| get_task := t'; get_mode := r |} t ph) ->
    Map_TID.In t ph.
  Proof.
    intros.
    unfold register in *.
    destruct (Map_TID_Extra.find_rw t ph) as [(R,?)|(v',(R,mt))]. {
      rewrite R in *; clear R.
      contradiction.
    }
    rewrite R in *; clear R.
    simpl in *.
    rewrite Map_TID_Facts.add_in_iff in *.
    destruct H;
    subst;
    eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Lemma register_mapsto_eq:
    forall t' v r ph t,
    Map_TID.In t ph ->
    Map_TID.MapsTo t' v (register {| get_task := t'; get_mode := r |} t ph) ->
    exists v',
    Map_TID.MapsTo t v' ph /\ v = Taskview.set_mode v' r.
  Proof.
    unfold register.
    intros.
    destruct (Map_TID_Extra.find_rw t ph) as [(R,?)|(v',(R,mt))]. {
      contradiction.
    }
    rewrite R in *; clear R.
    simpl in *.
    assert (v = set_mode v' r). {
      assert (Map_TID.MapsTo t' (set_mode v' r) (Map_TID.add t' (set_mode v' r) ph))
      by eauto using Map_TID.add_1.
      eauto using Map_TID_Facts.MapsTo_fun.
    }
    eauto.
  Qed.

  Lemma register_inv_mapsto:
    forall x y z v r ph,
    Map_TID.MapsTo x v (register {| get_task := y; get_mode := r |} z ph) ->
    Map_TID.MapsTo x v ph
    \/ (x = y /\ exists v', Map_TID.MapsTo z v' ph /\ v = set_mode v' r).
  Proof.
    unfold register.
    intros.
    destruct (Map_TID_Extra.find_rw z ph) as [(R,?)|(v',(R,mt))]. {
      rewrite R in *; clear R.
      intuition.
    }
    rewrite R in *; clear R.
    rewrite Map_TID_Facts.add_mapsto_iff in H.
    destruct H as [(?,?)|(?,?)].
    - right.
      simpl in *.
      subst.
      intuition.
      exists v'.
      intuition.
    - intuition.
  Qed.

  Lemma register_inv_in:
    forall ph t o ph',
    Reduces ph (t, o) ph' ->
    Map_TID.In t ph.
  Proof.
    intros.
    inversion H.
    destruct o;
    simpl in *; subst; inversion H; subst;
    inversion H1; subst; eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Lemma drop_mapsto_inv:
    forall t v ph t',
    Map_TID.MapsTo t v (drop t' ph) ->
    t' <> t /\ Map_TID.MapsTo t v ph.
  Proof.
    intros.
    unfold drop in *.
    rewrite Map_TID_Facts.remove_mapsto_iff in H.
    assumption.
  Qed.

  Let update_mapsto_eq:
    forall t f v ph,
    Map_TID.MapsTo t v (update t f ph) ->
    exists v', v = f v' /\ Map_TID.MapsTo t v' ph.
  Proof.
    intros.
    unfold update in *.
    remember (Map_TID.find _ _).
    symmetry in Heqo.
    destruct o as [v'|].
    - exists v'.
      assert (Map_TID.MapsTo t (f v') (Map_TID.add t (f v') ph)) by eauto using Map_TID.add_1.
      assert (v = f v') by eauto using Map_TID_Facts.MapsTo_fun.
      intuition.
      subst.
      apply Map_TID_Facts.find_mapsto_iff.
      assumption.
    - apply Map_TID_Facts.not_find_mapsto_iff in Heqo.
      contradiction Heqo.
      eauto using Map_TID_Extra.mapsto_to_in.
  Qed.

  Let update_mapsto_neq:
    forall t v t' f ph,
    Map_TID.MapsTo t v (update t' f ph) ->
    t' <> t ->
    Map_TID.MapsTo t v ph.
  Proof.
    intros.
    unfold update in *.
    remember (Map_TID.find _ _).
    symmetry in Heqo.
    destruct o as [v'|];
    eauto using Map_TID.add_3.
  Qed.

  Let update_mapsto_spec:
    forall t v ph f,
    Map_TID.MapsTo t v ph ->
    Map_TID.MapsTo t (f v) (update t f ph).
  Proof.
    intros.
    unfold update.
    destruct (Map_TID_Extra.find_rw t ph) as [(?,?)|(v',(R,mt))].
    - contradiction H1.
      eauto using Map_TID_Extra.mapsto_to_in.
    - rewrite R.
      assert (v' = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      auto using Map_TID.add_1.
  Qed.

  Let update_2:
    forall x y v ph f,
    x <> y ->
    Map_TID.MapsTo x v ph ->
    Map_TID.MapsTo x v (update y f ph).
  Proof.
    intros.
    unfold update.
    destruct (Map_TID_Extra.find_rw y ph) as [(R,?)|(v',(R,mt))];
    rewrite R in *; clear R. {
      assumption.
    }
    eauto using Map_TID.add_2.
  Qed.

  Let signal_mapsto_eq:
    forall t v ph,
    Map_TID.MapsTo t v (signal t ph) ->
    exists v', v = Taskview.signal v' /\ Map_TID.MapsTo t v' ph.
  Proof.
    intros.
    unfold signal in *.
    eauto using update_mapsto_eq.
  Qed.

  Lemma signal_1:
    forall x v ph,
    Map_TID.MapsTo x v ph ->
    Map_TID.MapsTo x (Taskview.signal v) (signal x ph).
  Proof.
    unfold signal.
    eauto.
  Qed.

  Lemma wait_1:
    forall x v ph,
    Map_TID.MapsTo x v ph ->
    Map_TID.MapsTo x (Taskview.wait v) (wait x ph).
  Proof.
    unfold wait.
    eauto.
  Qed.

  Lemma register_1:
    forall x v r ph,
    Map_TID.MapsTo x v ph ->
    ~ Map_TID.In (get_task r) ph ->
    Map_TID.MapsTo x v (register r x ph).
  Proof.
    intros.
    assert (get_task r <> x). {
      unfold not; intros; subst.
      contradiction H0.
      eauto using Map_TID_Extra.mapsto_to_in.
    }
    assert (R:=H).
    apply register_rw with (r:=r) in R; auto.
    rewrite R in *.
    apply Map_TID.add_2; auto.
  Qed.

  Lemma try_signal_mapsto_eq:
    forall t v ph,
    Map_TID.MapsTo t v (try_signal t ph) ->
    exists v', v = Taskview.try_signal v' /\ Map_TID.MapsTo t v' ph.
  Proof.
    intros.
    unfold signal in *.
    eauto using update_mapsto_eq.
  Qed.

  Lemma signal_mapsto_neq:
    forall t v t' ph,
    Map_TID.MapsTo t v (signal t' ph) ->
    t' <> t ->
    Map_TID.MapsTo t v ph.
  Proof.
    intros.
    unfold signal in *.
    eauto using update_mapsto_neq.
  Qed.

  Lemma try_signal_mapsto_neq:
    forall t v t' ph,
    Map_TID.MapsTo t v (try_signal t' ph) ->
    t' <> t ->
    Map_TID.MapsTo t v ph.
  Proof.
    intros.
    unfold try_signal in *.
    eauto using update_mapsto_neq.
  Qed.

  Lemma signal_mapsto_inv:
    forall  t v t' ph,
    Map_TID.MapsTo t v (signal t' ph) ->
    { t' = t /\ exists v', (v = Taskview.signal v' /\ Map_TID.MapsTo t v' ph) } +
    { t' <> t /\ Map_TID.MapsTo t v ph }.
  Proof.
    intros.
    destruct (TID.eq_dec t' t). {
      subst.
      intuition.
    }
    right.
    intuition.
    eauto using signal_mapsto_neq.
  Qed.

  Lemma try_signal_mapsto_inv:
    forall  t v t' ph,
    Map_TID.MapsTo t v (try_signal t' ph) ->
    { t' = t /\ exists v', (v = Taskview.try_signal v' /\ Map_TID.MapsTo t v' ph) } +
    { t' <> t /\ Map_TID.MapsTo t v ph }.
  Proof.
    intros.
    destruct (TID.eq_dec t' t). {
      subst.
      left; intuition.
    }
    right.
    intuition.
    eauto using try_signal_mapsto_neq.
  Qed.

  Lemma signal_mapsto_spec:
    forall t v ph,
    Map_TID.MapsTo t v ph ->
    Map_TID.MapsTo t (Taskview.signal v) (signal t ph).
  Proof.
    intros.
    apply update_mapsto_spec; auto.
  Qed.

  Lemma signal_2:
    forall x y v ph,
    x <> y ->
    Map_TID.MapsTo x v ph ->
    Map_TID.MapsTo x v (signal y ph).
  Proof.
    unfold signal; auto.
  Qed.

  Lemma wait_2:
    forall x y v ph,
    x <> y ->
    Map_TID.MapsTo x v ph ->
    Map_TID.MapsTo x v (wait y ph).
  Proof.
    unfold wait; auto.
  Qed.

  Lemma drop_2:
    forall x y v ph,
    x <> y ->
    Map_TID.MapsTo x v ph ->
    Map_TID.MapsTo x v (drop y ph).
  Proof.
    unfold drop; auto using Map_TID.remove_2.
  Qed.

  Lemma register_2:
    forall x y v r ph,
    x <> get_task r ->
    Map_TID.MapsTo x v ph ->
    Map_TID.MapsTo x v (register r y ph).
  Proof.
    unfold register.
    intros.
    destruct (Map_TID_Extra.find_rw y ph) as [(R,Hin)|(v',(R,mt))];
    rewrite R in *; clear R. {
      assumption.
    }
    eauto using Map_TID.add_2.
  Qed.

  Lemma register_spec:
    forall x v r ph,
    Map_TID.MapsTo x v ph ->
    Map_TID.MapsTo (get_task r) (set_mode v (get_mode r)) (register r x ph).
  Proof.
    intros.
    unfold register.
    destruct (Map_TID_Extra.find_rw x ph) as [(R,Hin)|(v',(R,mt))];
    rewrite R in *; clear R. {
      contradiction Hin.
      eauto using Map_TID_Extra.mapsto_to_in.
    }
    assert (v'=v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
    eauto using Map_TID.add_1.
  Qed.

  Lemma register_inv_1:
    forall v v' r ph t,
    Map_TID.MapsTo (get_task r) v' (register r t ph) ->
    Map_TID.MapsTo t v ph ->
    v' = set_mode v (get_mode r).
  Proof.
    intros.
    assert (Map_TID.MapsTo (get_task r) (set_mode v (get_mode r)) (register r t ph))
    by eauto using register_spec.
    eauto using Map_TID_Facts.MapsTo_fun.
  Qed.

  Lemma signal_inv_1:
    forall t v ph,
    Map_TID.MapsTo t v (signal t ph) ->
    exists v', Map_TID.MapsTo t v' ph /\ v = Taskview.signal v'.
  Proof.
    intros.
    apply signal_mapsto_inv in H.
    destruct H as [(_,(v',(?,?)))|(N,_)]. {
      eauto.
    }
    intuition.
  Qed.
    
  Lemma wait_mapsto_eq:
    forall t v ph,
    Map_TID.MapsTo t v (wait t ph) ->
    exists v', v = Taskview.wait v' /\ Map_TID.MapsTo t v' ph.
  Proof.
    intros.
    unfold signal in *.
    eauto using update_mapsto_eq.
  Qed.

  Lemma wait_mapsto_spec:
    forall t v ph,
    Map_TID.MapsTo t v ph ->
    Map_TID.MapsTo t (Taskview.wait v) (wait t ph).
  Proof.
    intros.
    apply update_mapsto_spec; auto.
  Qed.

  Lemma wait_mapsto_neq:
    forall t v t' ph,
    Map_TID.MapsTo t v (wait t' ph) ->
    t' <> t ->
    Map_TID.MapsTo t v ph.
  Proof.
    intros.
    unfold signal in *.
    eauto using update_mapsto_neq.
  Qed.

  Lemma wait_mapsto_inv:
    forall  t v t' ph,
    Map_TID.MapsTo t v (wait t' ph) ->
    { t' = t /\ exists v', (v = Taskview.wait v' /\ Map_TID.MapsTo t v' ph) } +
    { t' <> t /\ Map_TID.MapsTo t v ph }.
  Proof.
    intros.
    destruct (TID.eq_dec t' t). {
      subst.
      left. intuition.
    }
    right.
    intuition.
    eauto using wait_mapsto_neq.
  Qed.

  Lemma make_mapsto:
    forall t v t',
    Map_TID.MapsTo t v (make t') ->
    t' = t /\ v = Taskview.make.
  Proof.
    intros.
    unfold make in *.
    rewrite Map_TID_Facts.add_mapsto_iff in H.
    destruct H.
    - intuition.
    - destruct H.
      apply Map_TID_Facts.empty_mapsto_iff in H0.
      inversion H0.
  Qed.

  (**
    The importance of function [as_tv_op] is captured by the following two properties.
    If the phaser operation is convertible to a taskview operation, then
    then resulting taskview update is [Taskview.Semantics.reduces o' v].
  *)

  Lemma ph_to_tv_correct:
    forall ph t o o' ph' v,
    Reduces ph (t, o) ph' ->
    as_tv_op o = Some o' ->
    Map_TID.MapsTo t v ph ->
    ph' = Map_TID.add t (Taskview.reduces o' v) ph.
  Proof.
    intros.
    destruct o'; simpl.
    - apply as_tv_op_inv_signal in H0; subst.
      inversion H; simpl in *; subst; simpl in *.
      auto using signal_rw.
    - apply as_tv_op_inv_wait in H0; subst.
      inversion H; simpl in *.
      auto using wait_rw.
  Qed.
  
  (**
    The second property states that if the phaser-operation is convertible to
    a taskview-operation, then the taskview reduces with the resulting operation.
  *)

  Lemma ph_reduces_to_tv_reduce:
    forall ph t o o' ph' v,
    Reduces ph (t, o) ph' ->
    as_tv_op o = Some o' ->
    Map_TID.MapsTo t v ph ->
    Taskview.Reduces v o' (Taskview.reduces o' v).
  Proof.
    intros.
    destruct o'; simpl.
    - apply as_tv_op_inv_signal in H0; subst.
      inversion H; subst; simpl in *; clear H.
      inversion H4.
      assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun; subst.
      auto using tv_reduces_signal.
    - apply as_tv_op_inv_wait in H0; subst.
      inversion H; subst; simpl in *; clear H.
      apply tv_reduces_wait.
      inversion H4.
      assert (v0 = v) by eauto using Map_TID_Facts.MapsTo_fun.
      subst.
      intuition.
  Qed.

  Theorem reduces_dec e ph:
    {ph':phaser| Reduces ph e ph'}+{x:unit| forall ph', ~ Reduces ph e ph' }.
  Proof.
    remember (reduces e ph).
    symmetry in Heqo.
    destruct o.
    + eauto using reduces_1.
    + right.
      exists tt.
      eauto using reduces_3.
  Defined.

End Facts.

  Ltac simpl_red :=
  repeat match goal with
  | [ H : Reduces _ (_, _) _ |- _ ] =>
     inversion H; subst; simpl in *; clear H
  | [ H : SignalPre _ _ |- _ ] =>
     inversion H; subst; simpl in *; clear H
  | [ H : WaitPre _ _ |- _ ] =>
     inversion H; subst; simpl in *; clear H
  | [ H : DropPre _ _ |- _ ] =>
     inversion H; subst; simpl in *; clear H
  | [ H : RegisterPre _ _ _ |- _ ] =>
     inversion H; subst; simpl in *; clear H
  | [ H1 : Map_TID.MapsTo ?t ?v ?ph, H2 : Map_TID.MapsTo ?t ?v ?ph |- _ ] =>
    clear H2
  | [ H1 : Map_TID.MapsTo ?t ?v1 ?ph, H2 : Map_TID.MapsTo ?t ?v2 ?ph |- _ ] =>
    let H := fresh "H" in
    assert (H: v1 = v2) by eauto using Map_TID_Facts.MapsTo_fun;
    rewrite H in *;
    clear H
  end.
