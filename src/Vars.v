Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FMapAVL.
Require Coq.FSets.FMapFacts.
Require Coq.FSets.FSetProperties.
Require Import Aniceto.Map.
Require Import Aniceto.Set.

Module TID := Nat_as_OT.
Module TID_Facts := OrderedTypeFacts TID.
Module Set_TID := FSetAVL.Make TID.
Module Set_TID_Props := FSetProperties.Properties Set_TID.
Module Set_TID_Extra := SetUtil Set_TID.
Module Map_TID := FMapAVL.Make TID.
Module Map_TID_Facts := FMapFacts.Facts Map_TID.
Module Map_TID_Props := FMapFacts.Properties Map_TID.
Module Map_TID_Extra := MapUtil Map_TID.

Definition tid := TID.t.
Definition set_tid := Set_TID.t.

Module PHID := Nat_as_OT.
Module Set_PHID := FSetAVL.Make PHID.
Module Set_PHID_Extra := SetUtil Set_PHID.
Module Map_PHID := FMapAVL.Make PHID.
Module Map_PHID_Facts := FMapFacts.Facts Map_PHID.
Module Map_PHID_Props := FMapFacts.Properties Map_PHID.
Module Map_PHID_Extra := MapUtil Map_PHID.

Definition phid := PHID.t.
Definition set_phid := Set_PHID.t.

Module FID := Nat_as_OT.
Module Set_FID := FSetAVL.Make FID.
Module Set_FID_Extra := SetUtil Set_FID.
Module Map_FID := FMapAVL.Make FID.
Module Map_FID_Facts := FMapFacts.Facts Map_FID.
Module Map_FID_Props := FMapFacts.Properties Map_FID.
Module Map_FID_Extra := MapUtil Map_FID.

Definition fid := FID.t.
Definition set_fid := Set_FID.t.
