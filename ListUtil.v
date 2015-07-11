Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Bool.
Require Import Recdef. (* Required by Function *)
Require Import Coq.Arith.Wf_nat. (* Required implicitly by measure obligations *)

Section LISTS.

Variable A:Type.
Variable eq_dec : forall (v1 v2:A), {v1 = v2} + {v1 <> v2}.
Variable f : A -> bool.

Lemma in_cons_neq:
  forall {A:Type} (x y:A) l,
  In x (y :: l) ->
  x <> y ->
  In x l.
Proof.
  intros.
  inversion H.
  contradiction H0.
  auto.
  assumption.
Qed.

Lemma filter_length:
  forall l,
  length (filter f l) <= length l.
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    destruct (f a).
    + simpl.
      auto with *.
    + auto with *.
Qed.

Lemma filter_inv:
  forall l,
  {l = filter f l} + {length l > length (filter f l)}.
Proof.
  intros.
  induction l.
  - left.
    auto.
  - destruct IHl.
    + simpl.
      rewrite <- e in *; clear e.
      destruct (f a).
      * left.
        auto.
      * right.
        auto with *.
    + simpl.
      destruct (f a);(
        right;
        simpl;
        auto with *
      ).
Qed.

Lemma filter_incl:
  forall l,
  incl (filter f l) l.
Proof.
  intros.
  unfold incl.
  intros.
  rewrite filter_In in H.
  intuition.
Qed.

Lemma filter_in:
  forall x l,
  In x (filter f l) ->
  In x l.
Proof.
  intros.
  assert (f_i := filter_incl l).
  unfold incl in f_i.
  apply f_i.
  assumption.
Qed.

Lemma filter_refl:
  forall l,
  filter f l = l ->
  incl l (filter f l).
Proof.
  intros.
  induction l.
  - simpl.
    unfold incl.
    intros.
    inversion H0.
  - simpl in *.
    destruct (f a); (
      rewrite H;
      apply incl_refl).
Qed.

Lemma filter_forallb:
  forall l,
  filter f l = l <->
  forallb f l = true.
Proof.
  intros.
  split.
  - intros.
    induction l.
    + auto.
    + assert (Hfa : f a = true).
      assert (Ha : In a (filter f (a :: l))).
      rewrite H.
      apply in_eq.
      rewrite filter_In in Ha.
      intuition.
      simpl in *.
      destruct (f a).
      * inversion H.
        rewrite H1.
        auto.
      * inversion Hfa. (*absurd *)
  - intros. induction l.
    auto.
    simpl in *.
    rewrite Bool.andb_true_iff in H.
    destruct H as (Hl, Hr).
    apply IHl in Hr.
    destruct (f a).
    + rewrite Hr. trivial.
    + inversion Hl.
Qed.

Lemma existsb_inv:
  forall {B:Type} (a:B) l g,
  existsb g (a :: l) = true ->
  g a = false ->
  existsb g l = true.
Proof.
  intros.
  simpl in H.
  rewrite H0 in H.
  auto.
Qed.

Lemma forallb_existsb:
  forall l,
  forallb f l = negb (existsb (fun x => negb (f x)) l).
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    rewrite negb_orb.
    rewrite negb_involutive.
    rewrite <- IHl.
    auto.
Qed.

Lemma Forall_forallb:
  forall l,
  Forall (fun x => Is_true (f x)) l <->
  forallb f l = true.
Proof.
  split.
  + intro.
    rewrite forallb_forall.
    intros.
    rewrite Forall_forall in H.
    apply H in H0.
    apply Is_true_eq_true in H0.
    trivial.
  + intros.
    rewrite forallb_forall in H.
    rewrite Forall_forall.
    intros.
    apply Is_true_eq_left.
    apply H.
    assumption.
Qed.

End LISTS.

Implicit Arguments filter_inv.

Section FEEDBACK.
Variable A:Type.
Variable eq_dec : forall (v1 v2:A), {v1 = v2} + {v1 <> v2}.
Variable f : list A -> A -> bool.

Function feedback_filter (l:list A) {measure length l} :=
  let fl := filter (f l) l in
  if list_eq_dec eq_dec l fl then l 
  else feedback_filter fl.
Proof.
  intros.
  destruct (filter_inv (f l) l).
  - contradiction anonymous.
  - auto.
Defined.

Lemma feedback_filter_incl:
  forall l,
  incl (feedback_filter l) l.
Proof.
  intros.
  elim l using feedback_filter_rec.
  - intros.
    apply incl_refl.
  - intros. clear l. rename l0 into l.
    remember (filter (f l) l) as l'.
    assert (Hx : incl l' l).
    rewrite Heql'.
    apply filter_incl.
    apply incl_tran with (m:=l'); repeat auto.
Qed.

Lemma feedback_filter_simpl:
  forall l,
  filter (f l) l = l ->
  feedback_filter l = l.
Proof.
  intros.
  rewrite feedback_filter_equation.
  destruct (list_eq_dec eq_dec l (filter (f l) l)).
  - auto.
  - contradiction n.
    auto.
Qed.

Let if_list_eq_dec_eq:
  forall {B:Type} l (a b:B),
  (if list_eq_dec eq_dec l l then a else b) = a.
Proof.
  intros.
  destruct (list_eq_dec eq_dec l l).
  - auto.
  - contradiction n.
    auto.
Qed.

Let if_list_eq_filter_forallb:
  forall {B:Type} l (a b:B),
  (if list_eq_dec eq_dec l (filter (f l) l) then a else b)
  = (if forallb (f l) l then a else b).
Proof.
  intros.
  remember (filter (f l) l) as fl.
  symmetry in Heqfl.
  remember (forallb (f l) l) as flb.
  symmetry in Heqflb.
  destruct flb.
  - rewrite <- filter_forallb in Heqflb.
    rewrite Heqfl in Heqflb.
    rewrite Heqflb.
    apply if_list_eq_dec_eq.
  - destruct (list_eq_dec eq_dec l fl).
    + rewrite <- e in Heqfl.
      rewrite filter_forallb in Heqfl.
      rewrite Heqfl in Heqflb.
      inversion Heqflb.
    + auto.
Qed.

Let feedback_filter_equation2:
  forall l : list A,
  feedback_filter l =
  (if forallb (f l) l
  then l
  else feedback_filter (filter (f l) l)).
Proof.
  intros.
  rewrite feedback_filter_equation.
  rewrite if_list_eq_filter_forallb.
  auto.
Qed.

Lemma feedback_filter_prop:
  forall l fl,
  feedback_filter l = fl <->
  (Forall (fun x=>Is_true (f l x)) l /\ fl = l)
  \/
  (exists x, In x l /\ Is_true (negb (f l x)) /\ fl = feedback_filter (filter (f l) l)).
Proof.
  intros.
  split.
  - intros.
    rewrite feedback_filter_equation2 in H.
    remember (forallb (f l) l) as flb.
    symmetry in Heqflb.
    destruct flb.
    + rewrite forallb_forall in Heqflb.
      left.
      rewrite Forall_forall.
      intuition.
      apply Is_true_eq_left.
      apply Heqflb in H0.
      assumption.
    + right.
      rewrite forallb_existsb in Heqflb.
      rewrite negb_false_iff in Heqflb.
      rewrite existsb_exists in Heqflb.
      destruct Heqflb as (x, (x_in, flx)).
      exists x.
      apply Is_true_eq_left in flx.
      intuition.
   - intros.
     rewrite feedback_filter_equation2.
     destruct H as [(H1,H2)|(x, (H1, (H2, H3)))].
     + apply Forall_forallb in H1.
       rewrite H1.
       auto.
     + rewrite <- H3.
       remember (forallb (f l) l) as c.
       symmetry in Heqc.
       destruct c.
       * rewrite forallb_forall in Heqc.
         apply Heqc in H1.
         apply Is_true_eq_true in H2.
         rewrite negb_true_iff in H2.
         rewrite H1 in H2.
         inversion H2.
       * auto.
Qed.


Lemma feedback_filter_in_f:
  forall x l,
  In x (feedback_filter l) -> f (feedback_filter l) x = true.
Proof.
  intros.
  functional induction (feedback_filter l).
  - assert (Hf := _x).
    symmetry in Hf.
    rewrite filter_forallb in Hf.
    rewrite forallb_forall in Hf.
    apply Hf in H.
    assumption.
  - apply IHl0. auto.
Qed.

Lemma feedback_filter_in:
  forall x l,
  In x (feedback_filter l) ->
  In x l.
Proof.
  intros.
  assert (Hx := feedback_filter_incl l).
  unfold incl in Hx.
  apply Hx; assumption.
Qed.
End FEEDBACK.

Section PARTITION.
Variable A : Type.
Variable f : A -> bool.

Lemma partition_iff_1 :
  forall x l,
  (In x (fst (partition f l)) <-> In x l /\ f x = true).
Proof.
  intros.
  split.
  - intros.
    induction l.
    simpl in *.
    inversion H.
    simpl in H.
    remember (f a) as fa.
    symmetry in Heqfa.
    remember (partition f l) as pf.
    symmetry in Heqpf.
    destruct pf as (pfl, pfr).
    destruct fa.
    + simpl in *.
      destruct H.
      * subst.
        intuition.
      * apply IHl in H; clear IHl.
        destruct H.
        intuition.
    + simpl in *.
      apply IHl in H; clear IHl.
      destruct H.
      intuition.
 - intros.
   destruct H.
   induction l.
   auto.
   simpl in *.
   remember (f a).
   destruct H, b.
   + subst.
     remember (partition f l).
     destruct p.
     simpl.
     auto.
   + subst.
     rewrite H0 in Heqb.
     inversion Heqb.
   + remember (partition f l).
     destruct p.
     simpl in *.
     apply IHl in H.
     intuition.
   + apply IHl in H.
     remember (partition f l).
     destruct p.
     auto.
Qed.

Lemma partition_iff_2 :
  forall x l,
  (In x (snd (partition f l)) <-> In x l /\ f x = false).
Proof.
  intros.
  split.
  - intros.
    induction l.
    simpl in *.
    inversion H.
    simpl in H.
    remember (f a) as fa.
    symmetry in Heqfa.
    remember (partition f l) as pf.
    symmetry in Heqpf.
    destruct pf as (pfl, pfr).
    destruct fa.
    + simpl in *.
      apply IHl in H; clear IHl.
      destruct H.
      intuition.
    + simpl in *.
      destruct H.
      * subst.
        intuition.
      * apply IHl in H; clear IHl.
        destruct H.
        intuition.
 - intros.
   destruct H.
   induction l.
   auto.
   simpl in *.
   remember (f a).
   destruct H, b.
   + subst.
     rewrite H0 in Heqb.
     inversion Heqb.
   + subst.
     remember (partition f l).
     destruct p.
     simpl.
     auto.
   + remember (partition f l).
     destruct p.
     simpl in *.
     apply IHl in H.
     intuition.
   + apply IHl in H.
     remember (partition f l).
     destruct p.
     simpl in *.
     auto with *.
Qed.

Lemma partition_in :
  forall x l,
  In x l ->
  {In x (fst (partition f l)) /\ f x = true} +
  {In x (snd (partition f l)) /\ f x = false}.
Proof.
  intros.
  remember (f x).
  symmetry in Heqb.
  destruct b.
  - left.
    intuition.
    apply partition_iff_1.
    auto.
  - right.
    intuition.
    apply partition_iff_2.
    auto.
Qed.

Lemma partition_length:
  forall l,
  length (snd (partition f l)) <= length l.
Proof.
  intros.
  induction l.
  auto.
  simpl.
  remember (partition f l) as p.
  symmetry in Heqp.
  destruct p as (pl, pr).
  simpl in *.
  remember (f a) as fa.
  destruct fa.
  - simpl.
    auto.
  - simpl.
    auto with *.
Qed.

End PARTITION.

Lemma split_in_r:
  forall {L R:Type} (r:R) (lst:list (L * R)),
  In r (snd (split lst)) ->
  exists (l:L), In (l, r) lst.
Proof.
  intros.
  induction lst.
  inversion H.
  destruct a.
  simpl in *.
  remember (split lst).
  destruct p as (ll, lr).
  simpl in *.
  destruct H.
  - subst.
    exists l.
    intuition.
  - apply IHlst in H.
    destruct H as (l', Hin).
    exists l'.
    intuition.
Qed.

Lemma split_in_l:
  forall {L R:Type} (l:L) (lst:list (L * R)),
  In l (fst (split lst)) ->
  exists (r:R), In (l, r) lst.
Proof.
  intros.
  induction lst.
  inversion H.
  destruct a.
  simpl in *.
  remember (split lst).
  destruct p as (ll, lr).
  simpl in *.
  destruct H.
  - subst.
    exists r.
    intuition.
  - apply IHlst in H.
    destruct H as (r', Hin).
    exists r'.
    intuition.
Qed.


Fixpoint split_alt {A:Type} {B:Type} (l:list (A*B) %type) : (list A * list B) % type:=
  match l with
    | nil => (nil, nil)
    | (x, y) :: l => (x :: (fst (split_alt l)), y :: (snd (split_alt l)))
  end.

Lemma split_alt_spec:
  forall {A:Type} {B:Type} (l:list (A*B) %type),
  split l = split_alt l.
Proof.
  intros.
  induction l.
  - auto.
  - simpl. intuition.
    rewrite IHl.
    remember (split_alt l) as l'.
    destruct l' as (lhs, rhs).
    auto.
Qed.

Lemma in_fst_split:
  forall {A:Type} {B:Type} (l:list (A*B)%type) (lhs:A),
  List.In lhs (fst (split l)) ->
  exists rhs, List.In (lhs, rhs) l.
Proof.
  intros.
  induction l.
  { inversion H. (* absurd *) }
  destruct a.
  rewrite split_alt_spec in H.
  simpl in H.
  destruct H.
  + subst.
    exists b.
    apply in_eq.
  + rewrite <- split_alt_spec in H.
    apply IHl in H; clear IHl.
    destruct H as (r, Hin).
    exists r.
    apply in_cons; assumption.
Qed.

Lemma in_snd_split:
  forall {A:Type} {B:Type} (l:list (A*B)%type) (rhs:B),
  List.In rhs (snd (split l)) ->
  exists (lhs:A), List.In (lhs, rhs) l.
Proof.
  intros.
  induction l.
  { inversion H. (* absurd *) }
  destruct a.
  rewrite split_alt_spec in H.
  simpl in H.
  destruct H.
  + subst.
    exists a.
    apply in_eq.
  + rewrite <- split_alt_spec in H.
    apply IHl in H; clear IHl.
    destruct H as (r, Hin).
    exists r.
    apply in_cons; assumption.
Qed.

Require Import Coq.Lists.SetoidList.

Section INA_IN.
  Let ina_to_in:
    forall {A:Type} (P: A -> A -> Prop) (P_eq: forall x y, P x y <-> x = y) (a:A) l,
    InA P a l ->
    List.In a l.
  Proof.
    intros. induction l.
    + inversion H.
    + inversion H; subst; clear H.
      * apply P_eq in H1.
        subst.
        apply in_eq.
      * apply in_cons.
        apply IHl.
        assumption.
  Qed.

  Let in_to_ina:
    forall {A:Type} (P: A -> A -> Prop) (P_eq: forall x y, P x y <-> x = y) (a:A) l,
    List.In a l ->
    InA P a l.
  Proof.
    intros. induction l.
    + inversion H.
    + inversion H; subst; clear H.
      * apply InA_cons_hd.
        rewrite P_eq; auto.
      * apply InA_cons_tl.
        apply IHl.
        assumption.
  Qed.
  
  Lemma ina_in_iff:
    forall {A:Type} (P: A -> A -> Prop) (P_eq: forall x y, P x y <-> x = y) (a:A) l,
    InA P a l <-> List.In a l.
  Proof.
    intros.
    split.
    - apply ina_to_in. assumption.
    - apply in_to_ina. assumption.
  Qed.
End INA_IN.

Section NODUPA_NODUP.
  Let nodupa_to_nodup:
    forall {A:Type} (P: A -> A -> Prop) (P_eq: forall x y, P x y <-> x = y) l,
    NoDupA P l ->
    NoDup l.
  Proof.
    intros.
    induction l.
    - apply NoDup_nil.
    - apply NoDup_cons.
      + intuition.
        inversion H; clear H; subst.
        rewrite ina_in_iff in H3.
        contradiction H0.
        assumption.
      + inversion H; clear H; subst.
        apply IHl.
        assumption.
  Qed.

  Let nodup_to_nodupa:
    forall {A:Type} (P: A -> A -> Prop) (P_eq: forall x y, P x y <-> x = y) l,
    NoDup l ->
    NoDupA P l.
  Proof.
    intros.
    induction l.
    - apply NoDupA_nil.
    - inversion H; clear H; subst.
      apply IHl in H3; clear IHl.
      apply NoDupA_cons.
      intuition.
      rewrite ina_in_iff in H.
      contradiction H.
      assumption.
      assumption.
  Qed.
  
  Lemma nodupa_nodup_iff:
    forall {A:Type} (P: A -> A -> Prop) (P_eq: forall x y, P x y <-> x = y) l,
    NoDupA P l <-> NoDup l.
  Proof.
    intros.
    split.
    - apply nodupa_to_nodup. assumption.
    - apply nodup_to_nodupa. assumption.
  Qed.
End NODUPA_NODUP.
Implicit Arguments filter_incl.
Implicit Arguments feedback_filter.
Implicit Arguments feedback_filter_equation.
