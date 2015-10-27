Require Import Coq.Lists.List.
Require Import Aniceto.List.
Require Import Aniceto.Spec.
Require Import Aniceto.Option.
Require Coq.Program.Wf.

Require Import HJ.AsyncFinish.Lang.
Require HJ.AsyncFinish.Lang.
Module L := HJ.AsyncFinish.Lang.

Import Lang.
Require Import HJ.Vars.
Require Import Coq.Init.Datatypes.

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
  IsMap (Node l) ->
  Child (t, a) (Node l) ->
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
        inversion H3.
        subst.
        contradiction H6.
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
        { inversion H. inversion H3. auto using is_map_def. }
        { apply child_def. auto. }
Qed.

Lemma find_child_spec_2:
  forall l t a,
  find_child l t = Some a ->
  Child (t, a) (Node l).
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
  IsMap (Node l) ->
  (find_child l t = Some a <-> Child (t, a) (Node l)).
Proof.
  intros.
  split.
  - apply find_child_spec_2.
  - auto using find_child_spec_1.
Qed.

Definition child f := find_child (get_tasks f). 

Lemma child_spec_1:
  forall f,
  IsMap f ->
  forall t a,
  Child (t, a) f ->
  child f t = Some a.
Proof.
  intros.
  unfold child.
  destruct f.
  auto using find_child_spec_1.
Qed.

Lemma child_spec_2:
  forall f t a,
  child f t = Some a ->
  Child (t, a) f.
Proof.
  intros.
  unfold child.
  destruct f.
  auto using find_child_spec_2.
Qed.

Section SpecChild.
Variable f:finish.
Variable t:tid.
Variable is_map : IsMap f.

Global Program Instance Spec_child : Spec (fun (a:task) => Child (t, a) f) (child f t).
Next Obligation.
  auto using child_spec_1.
Qed.
Next Obligation.
  auto using child_spec_2.
Qed.
Lemma child_rw:
  forall a,
  (child f t = Some a <-> Child (t, a) f).
Proof.
  eapply spec_rw.
  auto with *.
Qed.

Definition child_dec := (spec_dec (s:=Spec_child)).

End SpecChild.

Definition is_registered f t : bool := is_some (child f t).

Section BSpecChild.
Variable f:finish.
Variable t:tid.
Variable H: IsMap f.
Print BSpec.
Global Program Instance BSpec_registered : BSpec task (fun (a:task) => Child (t, a) f) (child f t) (Registered t f).
Next Obligation.
  auto with *.
Qed.
Next Obligation.
  eauto using registered_def.
Qed.
Next Obligation.
  inversion H0.
  exists a.
  assumption.
Qed.
End BSpecChild.

Lemma is_registered_spec_1:
  forall t f,
  IsMap f ->
  Registered t f ->
  is_registered f t = true.
Proof.
  unfold is_registered.
  intros.
  eapply bspec_impl_is_some; eauto with *.
Qed.
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)

Lemma find_child_incl:
  forall t p l,
  find_child ((p :: l)) t = None ->
  find_child l t = None.
Proof.
  intros.
  unfold find_child in *.
  remember (find _ (p::l)).
  symmetry in Heqo.
  destruct o.
  - destruct l0.
    inversion H.
  - apply find_none_incl in Heqo.
    rewrite Heqo.
    trivial.
Qed.


Section IEF.

Variable check: finish -> bool.

Fixpoint get_children (f:finish) : list (tid * finish) :=
  match f with
  | Node l =>
    (fix aux (l:list l_task) :=
      match l with
      | ((t, Blocked f') :: l) => (t, f') :: (aux l)
      | (t, Ready) :: l => aux l
      | nil => nil
      end) l
  end.

Lemma get_children_spec_1:
  forall t f f',
  List.In (t, f) (get_children f') ->
  Child t (Blocked f) f'.
Proof.
  intros.
  destruct f'.
  simpl in H.
  induction l as [|(t', [|f''])].
  - inversion H.
  - auto using child_cons_perm.
  - destruct H.
    + inversion H; subst; clear H.
      auto using child_eq.
    + auto using child_cons_perm.
Qed.

Lemma get_children_spec_2:
  forall t f f',
  Child t (Blocked f) f' ->
  List.In (t, f) (get_children f').
Proof.
  intros.
  destruct H.
  destruct f'.
  simpl in *.
  induction l as [|(t', [|f''])].
  - inversion H.
  - inversion H.
    + inversion H0.
    + auto.
  - inversion H.
    + inversion H0.
      subst.
      apply List.in_eq.
    + auto using List.in_cons.
Qed.

Lemma get_children_spec:
  forall t f f',
  Child t (Blocked f) f' <-> List.In (t, f) (get_children f').
Proof.
  intros.
  split.
  apply get_children_spec_2.
  apply get_children_spec_1.
Qed.

Lemma get_children_forall:
  forall f,
  Forall (fun (p:(tid*finish)) => Child (fst p) (Blocked (snd p)) f) (get_children f).
Proof.
  intros.
  apply Forall_forall.
  intros.
  destruct x as (t, f').
  simpl in *.
  apply get_children_spec_1.
  assumption.
Qed.

Definition ChildrenOf (f:finish) : list (tid * finish) -> Prop := Forall (fun (p:(tid*finish)) => Child (fst p) (Blocked (snd p)) f).

Lemma children_of_cons {f} {p} {l}:
  ChildrenOf f (p::l) ->
  ChildrenOf f l.
Proof.
  intros.
  unfold ChildrenOf in *.
  inversion H.
  assumption.
Qed.

Definition children_of f := {x : list (tid * finish) | ChildrenOf f x }.

Program Definition get_blocked (f:finish) : children_of f := get_children f.
Next Obligation.
  unfold ChildrenOf.
  apply get_children_forall.
Qed.

Fixpoint size (f:finish) := 
  S (
  match f with
  | Node l =>
    (fix aux (l:list l_task) :=
      match l with
      | cons (t, Blocked f') l => S (size f') + aux l
      | cons (t, Ready) l => S (aux l)
      | nil => 0
      end
    ) l
  end).

Definition l_size (f:finish) (l:children_of f) :=
  match l with
  | exist l _ => length l
  end.

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

Inductive Path : list tid -> finish -> Prop :=
  | path_nil:
    forall f,
    check f = true ->
    Path nil f
  | path_cons:
    forall t l f f',
    Path l f' ->
    check f = false ->
    Child t (Blocked f') f ->
    Path (t::l) f.

Inductive SubFinish : finish -> finish -> Prop :=
  sub_finish_def:
    forall f t f',
    Child t (Blocked f) f' ->
    SubFinish f f'.

Lemma sub_finish_eq:
  forall (f:finish) (t:tid) (l:list l_task),
  SubFinish f (Node ((t,Blocked f)::l)).
Proof.
  intros.
  eauto using sub_finish_def, child_eq.
Qed.

Section LT_IND.

Hypothesis P : finish -> Prop.
Hypothesis Htrans: forall f f', P f -> SubFinish f f' -> P f'.
Hypothesis Hnil: P (Node nil).
Hypothesis Hcons: forall t l, P (Node l) -> P (Node ((t, Ready)::l)).

Fixpoint sub_finish_ind (f:finish) : P f :=
match f with
| Node l =>
    (fix aux (l:list l_task) : P (Node l) :=
    match l as x return P (Node x) with 
    | nil => Hnil
    | (t,Ready) :: l => Hcons t l (aux l)
    | (t, Blocked f') :: l => Htrans f' (Node ((t, Blocked f')::l)) (sub_finish_ind f') (sub_finish_eq f' t l)
    end) l
end.

End LT_IND.

Lemma sub_finish_absurd_nil:
  forall f,
  ~ SubFinish f (Node nil).
Proof.
  unfold not.
  intros.
  inversion H.
  subst.
  apply child_leaf_absurd in H0.
  assumption.
Qed.

Lemma sub_finish_cons_ready:
  forall f t l,
  SubFinish f (Node l) ->
  SubFinish f (Node ((t, Ready)::l)).
Admitted.

Lemma sub_finish_inv_cons_ready:
  forall f t l,
  SubFinish f (Node ((t, Ready)::l)) ->
  SubFinish f (Node l).
Admitted.

Lemma path_cons_ready:
  forall p t l,
  Path p (Node l) ->
  Path p (Node ((t, Ready)::l)).
Admitted.
  
Variable check_contract:
  forall p l,
  check (Node (p :: l)) = false ->
  check (Node l) = false.
  
Lemma accum_finish_contract:
  forall t l r,
  accum_finish nil (Node ((t, Ready) :: l)) = Some r ->
  accum_finish nil (Node l) = Some r.
Admitted.

Lemma accum_to_path:
  forall f r,
  accum_finish nil f = Some r ->
  Path r f.
Proof.
  intros f.
  induction f using sub_finish_ind.
  - intros.
    inversion H.
    subst.
    destruct f2.
    simpl in H0.
    remember (check _).
    destruct b.
    + inversion H0.
      subst.
      symmetry in Heqb.
      auto using path_nil.
    + destruct r.
      {  }
  - intros.
    simpl in H.
    remember (check _).
    destruct b.
    + inversion H.
      subst.
      auto using path_nil.
    + inversion H.
  - intros.
    simpl in H.
    remember (check _).
    destruct b.
    + inversion H.
      subst.
      auto using path_nil.
    + apply path_cons_ready.
      destruct l as [|p].
      * inversion H.
      * apply IHf.
        simpl.
        assert (He : check (Node (p :: l)) = false). {
          symmetry in Heqb.
          eauto using check_contract.
        }
        rewrite He.
        auto.
Qed.    
    

(*
Lemma accum_finish_cons:
  forall f f' t a r,
  check f = false ->
  accum_finish a f' = Some r ->
  Child t (Blocked  f') f ->
  (forall p l, f = Node (p::l) -> check (Node l) = false) ->
(*  (forall l, f = Node ((t, (Blocked f'))::l) ->  *)
  IsMap f ->
  accum_finish (t :: a) f = Some r.
Proof.
  intros f.
  induction f using finish_ind_strong.
  - intros.
    apply child_leaf_absurd in H1.
    inversion H1.
  - intros.
    unfold accum_finish.
    rewrite H.
    assert (accum_finish (t0 :: a) (Node l) = Some r). {
      apply IHf with (f':=f'); auto.
      - eauto.
      - 
    }
    unfold accum_finish in *.
    apply IHf.
    assert (He :  check (Node ((t, Ready) :: l)) = false). {
      auto.
    }
    rewrite He.
    rewrite H.
    simpl.
    unfo
    
    assert (accum_finish (t :: a) (Node ((t0, Ready) :: l)) = accum_finish (t :: a) (Node l))
(*  simpl.*)
(*  rewrite H.*)
  induction l.
  - apply child_leaf_absurd in H1.
    inversion H1.
  - destruct a0 as (t', [|f'']).
    + 
Qed.
*)

Section AccumFinishInv.
Variable t:tid.
Variable l:list l_task.
Variable p:l_task.
Variable RW1 : check (Node (p::l)) = false.
Variable RW2 : check (Node l) = false.
Variable a: list tid.

Variable RW3:
  match (snd p) with
  | Ready => True
  | Blocked f=> accum_finish ((fst p)::a) f = None
  end.

Lemma accum_rw_cons_tl:
  accum_finish a (Node (p::l)) = accum_finish a (Node l).
Proof.
  intros.
  destruct p as (t', [|f']).
  - simpl in RW3.
    simpl.
    rewrite RW1.
    rewrite RW2.
    trivial.
  - simpl in RW3.
    simpl.
    rewrite RW1.
    rewrite RW2.
    rewrite RW3.
    trivial.
Qed.
End AccumFinishInv.

Lemma accum_rw_cons_tl_ready:
  forall  a t l,
  check (Node ((t, Ready) :: l)) = false ->
  check (Node l) = false ->
  accum_finish a (Node ((t,Ready)::l)) = accum_finish a (Node l).
Proof.
  intros.
  apply accum_rw_cons_tl; auto.
  simpl.
  trivial.
Qed.

Section AccumFinishInv2.
Variable t:tid.
Variable l:list l_task.
Variable t':tid.
Variable f:finish.
Variable RW1 : check (Node (((t', Blocked f)::l))) = false.
Variable RW2 : check (Node l) = false.
Variable a: list tid.
Variable r: list tid.
Variable RW3: accum_finish (t'::a) f = Some r.

Lemma accum_rw_cons_hd:
  accum_finish a (Node ((t', Blocked f)::l)) = Some r.
Proof.
  intros.
  simpl.
  rewrite RW1.
  rewrite RW3.
  trivial.
Qed.
End AccumFinishInv2.

Inductive Accum : list tid -> finish -> list tid -> Prop :=
  | accum_check_true: 
    forall f a,
    check f = true ->
    Accum a f a
  | accum_check_false:
    forall a fs l,
    check (Node fs) = false ->
    AccumChild a fs l ->
    Accum a (Node fs) l
with AccumChild : list tid -> list l_task -> list tid -> Prop :=
  | accum_ok:
    forall a t f fs l,
    Accum (t::a) f l ->
    AccumChild a ((t, Blocked f)::fs) l
  | accum_cons:
    forall t a x fs l,
    AccumChild a fs l ->
    AccumChild a ((t, x)::fs) l.

Lemma accum_spec_1:
  forall a f r,
  accum_finish a f = Some r ->
  Accum a f r.
Proof.
  intros.
  induction f using finish_ind_strong2 (*with (Q:=fun (x:l_task) => x = x*).
  - simpl in H.
    remember (check _).
    destruct b.
    + inversion H; subst.
      auto using accum_check_true.
    + inversion H.
  - simpl in H.
    remember (check _).
    symmetry in Heqb.
    destruct b.
    + inversion H; subst.
      auto using accum_check_true.
    + apply accum_check_false; auto.
      
      
  destruct f.
  simpl in H.
  remember (check _).
  destruct b.
  { (* easy case *)
    inversion H; subst.
    auto using accum_check_true.
  }
  apply accum_check_false; auto.
  induction l.
  - inversion H.
  - destruct a as (t, [|f']).
    + apply accum_cons.
      apply IHl; auto.
      symmetry in Heqb.
      symmetry.
      eauto.
    + destruct (accum_finish _ f').
      
      apply accum_cons.
      apply IHl; auto.
      * symmetry in Heqb.
        symmetry.
        eauto.
      *  
Qed.
*)
End IEF.

Definition child_mem (t:tid) (f:finish) := 
  match find_child (get_tasks f) t with
  | Some _ =>  true
  | _ => false
  end.

Lemma child_mem_false_inv:
  forall t p l,
  child_mem t (Node ((p :: l))) = false ->
  child_mem t (Node l) = false.
Proof.
  intros.
  unfold child_mem in *.
  remember ( find_child (get_tasks (Node (p :: l))) t).
  symmetry in Heqo.
  destruct o.
  - inversion H.
  - apply find_child_incl in Heqo.
    simpl.
    rewrite Heqo.
    trivial.
Qed.




(*
Variable check_incl:
forall p fs, check (Node (p::fs)) = false -> check (Node fs) = false.
*)
Require Import Coq.Bool.Sumbool.


Definition ChildOf f := {f' : finish | L.Lt f' f }.

Definition SubSet {A} l := {l' : list A | incl l' l}.  


Lemma in_impl_child_mem:
  forall t f,
  IsMap f ->
  ChildIn t f ->
  child_mem t f = true.
Proof.
  intros.
  destruct f.
  inversion H0.
  unfold child_mem.
  assert (Heq  : find_child (get_tasks (Node l)) t = Some a). {
    auto using find_child_spec_1.
  }
  rewrite Heq.
  trivial.
Qed.

Lemma child_mem_impl_in:
  forall f  t,
  child_mem t f = true ->
  ChildIn t f.
Proof.
  intros.
  destruct f.
  unfold child_mem in *.
  remember (find_child  _ _) as  o.
  symmetry in Heqo.
  destruct o.
  - eauto using in_def, find_child_spec_2.
  - inversion H.
Qed.

Lemma not_in_impl_child_mem:
  forall f t,
  ~ ChildIn t f ->
  child_mem t f = false.
Proof.
  intros.
  remember (child_mem _ _).
  symmetry in Heqb.
  destruct b.
  - contradiction H. auto using child_mem_impl_in.
  - trivial. 
Qed.

Lemma not_child_mem_impl_in:
  forall f  t,
  IsMap f ->
  child_mem t f = false ->
  ~ ChildIn t f.
Proof.
  intros.
  unfold not.
  intros.
  apply in_impl_child_mem in H1; auto.
  rewrite H0 in H1.
  inversion H1.
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
    IEFBase t f nil
  | ief_base_cons:
    forall f f' t' l,
    IEFBase t f' l ->
    Child t' (Blocked f') f  ->
    ~ ChildIn t f ->
    IEFBase t f (t'::l).

Lemma ief_base_leaf:
  forall t f,
  Valid f ->
  IEFBase t f nil ->
  ief_base t f = Some nil.
Proof.
  intros.
  destruct f.
  inversion H0.
  subst.
  unfold ief_base.
  simpl.
  assert (Hin : ChildIn t (Node l)). {
   eauto using in_def.
  }
  apply in_impl_child_mem in Hin.
  + rewrite Hin.
    trivial.
  + auto using valid_impl_is_map.
Qed.

Let ief_base_inv_1:
  forall t t' l,
  IsMap (Node ((t', Ready) :: l)) ->
  ~ ChildIn t (Node ((t', Ready) :: l)) ->
  ief_base t (Node ((t', Ready) :: l)) = ief_base t (Node l).
Proof.
  intros.
  unfold ief_base.
  apply not_in_impl_child_mem in H0; auto.
  apply accum_rw_cons_tl; auto.
  - eauto using child_mem_false_inv.
  - simpl; trivial.
Qed.

Lemma ief_base_leaf_absurd:
  forall t l,
  ~ IEFBase t (Node nil) l.
Proof.
  intros.
  unfold not.
  intros.
  inversion H; (
    subst;
    eauto using child_leaf_absurd).
Qed.

Lemma ief_base_impl_in:
  forall t f l,
  IEFBase t f l ->
  In t f.
Proof.
  intros.
  induction H.
  - eauto using in_child.
  - eauto using in_trans, lt_def.
Qed.

Let ief_base_tl_ready:
  forall t t' l,
  ~ ChildIn t (Node ((t', Ready) :: l)) ->
  ief_base t (Node ((t', Ready) :: l)) = ief_base t (Node l).
Proof.
  intros.
  assert (Hc : child_mem t (Node ((t', Ready) :: l)) = false). {
    auto using not_in_impl_child_mem.
  }
  eauto using accum_rw_cons_tl_ready, child_mem_false_inv.
Qed.

Let ief_base_base_case:
  forall f l t,
  Valid f ->
  IEFBase t f l ->
  ChildIn t f ->
  IsMap f ->
  ief_base t f = Some nil.
Proof.
  intros.
  unfold ief_base.
  auto using accum_finish_base, in_impl_child_mem.
Qed.

Let ief_base_some_cons:
  forall t f f' t' l,
  ief_base t f' = Some l ->
  child_mem t f = false ->
  Child t' (Blocked f') f ->
  ief_base t f = Some (t' :: l).
Proof.
  intros.
  destruct f.
(*  unfold ief_base.
  simpl.
  rewrite H0.*)
  induction l0.
  - apply child_leaf_absurd in H1.
    inversion H1.
  - assert (ief_base t (Node (a :: l0)) = ief_base t (Node l0)). {
      unfold ief_base.
      
    }
  destruct a as (t'', a).
    apply child_inv_cons in H1.
    destruct H1 as [(?,?)|?].
    + subst.
      assert (Hc : child_mem t (Node l0) = false). {
        eauto using child_mem_false_inv. 
      }
      apply IHl0 in Hc; auto.
      * rewrite Hc.
        
      apply child_cons.
    destruct a as (t'', [|f'']).
    + assert (Hc : child_mem t (Node l0) = false). {
        eauto using child_mem_false_inv. 
      }
      apply IHl0 in Hc; auto.
      apply child_cons.
    
Qed.


Lemma ief_base_spec_1:
  forall f l t,
  Valid f ->
  IEFBase t f l ->
  ief_base t f = Some l.
Proof.
  intros f.
  induction f using finish_ind_strong.
  - intros.
    apply ief_base_leaf_absurd in H0.
    inversion H0.
  - intros.
    inversion H0.
    + subst.
      auto using ief_base_leaf.
    + subst.
      assert (RW : ief_base t0 (Node ((t, Ready) :: l)) = ief_base t0 (Node l)). {
        auto using ief_base_tl_ready.
      }
      rewrite RW.
      apply ief_base_base_case in H1.
      * 
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
