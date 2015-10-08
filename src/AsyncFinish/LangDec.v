Require Import HJ.AsyncFinish.Lang.
Import Lang.Semantics.
Require Import HJ.Vars.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Aniceto.List.

Let find_child_aux (t:tid) (p:l_task) := if TID.eq_dec (fst p) t then true else false.

Definition find_child (l:list l_task) (t:tid) : option task :=
  match (find (find_child_aux t) l) with
  | Some (_, a) => Some a
  | None  => None
  end.

Require Import HJ.AsyncFinish.Typesystem.
Require Import Coq.Lists.SetoidList.

Let find_child_aux_rw_eq:
  forall t a,
  find_child_aux t (t, a) = true.
Proof.
  intros.
  unfold find_child_aux.
  simpl.
  destruct (TID.eq_dec t t); auto.
Qed.

Let find_child_aux_rw_neq:
  forall t' t a,
  t' <> t ->
  find_child_aux t (t', a) = false.
Proof.
  intros.
  unfold find_child_aux.
  simpl.
  destruct (TID.eq_dec t' t); intuition.
Qed.

Lemma find_child_rw_eq:
  forall t a l,
  find_child ((t,a)::l) t = Some a.
Proof.
  intros.
  unfold find_child.
  simpl.
  rewrite find_child_aux_rw_eq.
  trivial.
Qed.

Lemma find_child_rw_neq:
  forall t' t a l,
  t' <> t ->
  find_child ((t' ,a)::l) t = find_child l t.
Proof.
  intros.
  unfold find_child.
  simpl.
  assert (Heq : find_child_aux t (t', a) = false). {
    auto using find_child_aux_rw_neq.
  }
  rewrite Heq.
  trivial.
Qed.

Lemma find_child_spec_1:
  forall l t a,
  IsMap l ->
  Child t a (Node l) ->
  find_child l t = Some a.
Proof.
  intros l.
  induction l.
  - intros.
    inversion H0.
    inversion H1.
  - intros.
    destruct H0.
    inversion H0.
    + subst.
      auto using find_child_rw_eq.
    + destruct a as (t', a').
      destruct (TID.eq_dec t' t).
      * inversion H.
        subst.
        contradiction H4.
        rewrite InA_altdef.
        rewrite Exists_exists.
        exists (t, a0).
        intuition.
        apply Map_TID_Extra.eq_key_unfold.
        trivial.
      * simpl.
        assert (Heq  : find_child ((t', a') :: l) t = find_child l t). {
          auto using find_child_rw_neq.
        } 
        rewrite Heq.
        apply IHl.
        { inversion H. assumption. }
        { apply child_def. auto. }
Qed.

Lemma find_child_spec_2:
  forall l t a,
  find_child l t = Some a ->
  Child t a (Node l).
Proof.
  intros l.
  induction l.
  - intros.
    inversion H.
  - intros.
    destruct a as (t', a).
    destruct (TID.eq_dec t' t).
    + subst.
      rewrite find_child_rw_eq in H.
      inversion H.
      subst.
      auto using child_eq.
    + rewrite find_child_rw_neq in H; auto.
      auto using child_cons.
Qed.

Lemma find_child_spec:
  forall l t a,
  IsMap l ->
  (find_child l t = Some a <-> Child t a (Node l)).
Proof.
  intros.
  split.
  - apply find_child_spec_2.
  - auto using find_child_spec_1.
Qed.

Section IEF.

Variable check: finish -> bool.

Fixpoint accum_finish (accum:list tid) (f:finish) : option (list tid) :=
  if check f then Some accum
  else
  match f with
  | Node l =>
    (fix aux (l:list l_task) :=
      match l with
      | cons (t, Blocked f') l =>
        match accum_finish (t::accum) f' with
        | Some x => Some x
        | None => aux l
        end
      | cons (t, Ready) l => aux l
      | nil => None
      end
    ) l
  end.

End IEF.

Definition child_mem (t:tid) (f:finish) := 
  match find_child (get_tasks f) t with
  | Some _ =>  true
  | _ => false
  end.

Inductive In (t:tid) (f:finish) : Prop :=
  in_def:
    forall a,
    Child t a f ->
    In t f.

Lemma in_impl_child_mem:
  forall t l,
  IsMap l ->
  In t (Node l) ->
  child_mem t (Node l) = true.
Proof.
  intros.
  inversion H0.
  unfold child_mem.
  assert (Heq  : find_child (get_tasks (Node l)) t = Some a). {
    auto using find_child_spec_1.
  }
  rewrite Heq.
  trivial.
Qed.

Lemma child_mem_impl_in:
  forall t l,
  IsMap l ->
  child_mem t (Node l) = true ->
  In t (Node l).
Proof.
  intros.
  unfold child_mem in *.
  remember (find_child  _ _) as  o.
  symmetry in Heqo.
  destruct o.
  - eauto using in_def, find_child_spec_2.
  - inversion H0.
Qed.

Definition ief_base (t:tid) : finish -> option (list tid) :=
  accum_finish (child_mem t) nil.

(** Some test cases. *)

Goal
  let t1 := 1 in
  ief_base t1 (Node ((t1,Ready):: nil)) = Some nil.
Proof.
  auto.
Qed.

Goal
  let t1 := 1 in
  let t2 := 2 in
  ief_base t1 (Node ((t2,Blocked (Node ((t1,Ready)::nil)) ):: nil)) = Some (t2::nil).
Proof.
  auto.
Qed.

Goal
  let t1 := 1 in
  let t2 := 2 in
  let t3 := 3 in
  let t4 := 4 in
  ief_base t1 (Node ((t2,Blocked (Node ((t3,Ready)::nil)) )::
                             (t4,Blocked (Node ((t1,Ready)::nil)) ):: nil)) = Some (t4::nil).
Proof.
  auto.
Qed.

(** ief_base spec *)
Inductive IEFBase (t:tid) : finish -> list tid -> Prop :=
  | ief_base_eq:
    forall a f,
    Child t a f ->
    IEFBase t f (t :: nil)
  | ief_base_cons:
    forall f f' t' l,
    IEFBase t f' l ->
    Child t' (Blocked f') f  ->
    IEFBase t f (t'::l).

Lemma ief_base_spec_1:
  forall l' l t,
  IEFBase t (Node l') l ->
  IsMap l' ->
  ief_base t (Node l') = Some l.
Proof.
  intros.
  unfold ief_base.
  induction H0.
  - inversion H.
    apply child_leaf_absurd in H0.
    inversion H0.
    subst.
    apply child_leaf_absurd in H1.
    inversion H1.
 - inversion H.
   + subst.
    destruct f.
    simpl.
    assert (child_mem t (Node l) = true). {
      assert (In t (Node l)). {
        eauto using in_def.
      }
      apply in_impl_child_mem; auto.
    unfold accum_finish.
    destruct f.
    simpl.
  
  intros f.
  induction f using finish_ind_strong.
  - intros.
    inversion H.
    subst.
    destruct H0.
  inversion H.
  - subst.
Qed.

Definition get_ief_aux (t:tid) (f:finish) :=
  iterate_ief
    (* return type *)
    (option (list tid))
    (* test if child is in the lead *)
    (fun (f:finish) =>
      match find_child (get_tasks f) t with
      | Some _ => true
      | _ =>  false
      end
    )
    (* leaf handler *)
    (fun (leaf:finish) => Some (cons t nil))
    (fun 
    

Function get_ief (t:tid) (f:finish) : option (list tid) :=
  let check := 
      (* Return true if this finish should be handled *)
      (fun (p:l_task) =>
        match get_ief t (as_finish(snd p)) with
        | Some l => true
        | None =>
          (* Did not get an IEF, return true if [t] is a child *)
          if TID.eq_dec (fst p) t then true else false
        end)
  in
  match f with
  | Node l =>
    match find check l with
    | Some (t', a) =>
      match a with
      | Blocked f => None
      | Ready => Some (cons t nil)
      end
    | None => None
    end
  end.

Variable update : finish -> tid -> task -> option finish.

Fixpoint update_ief (f:finish) (t:tid) : option finish := 
  iterate_finish
    (* iterate_next *)
    (* iterate_end *)
    (* iterate_mismatch *)
  match f with
  | Node l =>
    (fix aux (l:list l_task) : option finish :=
      match l with
      | cons (t',a) l =>
        if TID.eq_dec t' t then (
          (* t' = t *)
          match a with
          | Blocked f =>
            (* Check if we have a nested finish: *)
            match update_ief f t with
            (* If we have a nested finish, then rewrite the finish tree *)
            | Some f' => Some (Node (cons (t', Blocked f') l))
            (* Otherwise, just update the finish *)
            | None  => update f t a
            end 
          (* matched task, so just rewrite the finish *)
          | Ready => update f t a
          end
        ) else (
          (* no match, delegate to the finish if possible *)
          match a with
          | Blocked f' =>
            match update_ief f t with
            | Some f' => Some (Node (cons (t', Blocked f') l))
            | None =>
              (* Check if we need to rewrite the return of aux *)
              match aux l with
              | Some (Node l) => Some (Node (cons (t', a) l))
              | None => None
              end
            end
          | Ready => 
            (* Check if we need to rewrite the return of aux *)
            match aux l with
            | Some (Node l) => Some (Node (cons (t', a) l))
            | None => None
            end
          end
        )
      | nil => None
      end
    ) l
  end.

Fixpoint run (f:finish) (t:tid) (o:op) : option finish :=
  match o with
  | BEGIN_ASYNC t' =>
      
  | END_ASYNC =>
  | BEGIN_FINISH =>
  | END_FINISH =>
  end.

  | begin_async:
    forall t',
    Leaf t f ->
    ~ In t' f ->
    Reduce f t (BEGIN_ASYNC t') (put f (t', Ready))
  | end_async:
    Leaf t f ->
    Reduce f t END_ASYNC (remove f t)
  | begin_finish:
    Leaf t f ->
    Reduce f t BEGIN_FINISH (put f (t, Blocked (mk_finish t)))
  | end_finish:
    Child t (Blocked (Node nil)) f ->
    Reduce f t END_FINISH (put f (t, Ready))
  | reduce_nested:
    forall t' o f' f'',
    Disjoint f o ->
    Child t' (Blocked f') f ->
    Reduce f' t o f'' ->
    Reduce f t o (put f (t', Blocked f'')).
