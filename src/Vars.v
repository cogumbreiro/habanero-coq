(* begin hide *)
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FMapAVL.
Require Coq.FSets.FMapFacts.
Require Coq.FSets.FSetProperties.
Require Coq.FSets.FSetBridge.
Require Import Aniceto.Map.
Require Import Aniceto.Set.
Require Import Aniceto.EqDec.


Module PHID := Nat_as_OT.
Module Set_PHID := FSetAVL.Make PHID.
Module Set_PHID_Extra := SetUtil Set_PHID.
Module Map_PHID := FMapAVL.Make PHID.
Module Map_PHID_Facts := FMapFacts.Facts Map_PHID.
Module Map_PHID_Props := FMapFacts.Properties Map_PHID.
Module Map_PHID_Extra := MapUtil Map_PHID.

Definition phid := PHID.t.
Definition set_phid := Set_PHID.t.

Lemma phid_eq_rw:
  forall k k' : phid, k = k' <-> k = k'.
Proof.
  intros.
  auto with *.
Qed.

(* end hide  *)