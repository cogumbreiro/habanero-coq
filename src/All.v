Require HJ.AsyncFinish.Lang.
Module F := HJ.AsyncFinish.Lang.
Require HJ.Phasers.Lang.
Module P := HJ.Phasers.Lang.
Require Import HJ.Vars.
Require Import HJ.AsyncFinish.IEF.

Notation fstate := (Map_FID.t P.phasermap).

Inductive state := mk_state {
  get_finish: F.finish;
  get_fstate: fstate
}.

Definition set_fstate (s:state) (m:fstate)  :=
  mk_state s.(get_finish) m.

Definition put_phasermap (s:state) (f:fid) (m:P.phasermap) :  state :=
  set_fstate s (Map_FID.add f m s.(get_fstate)).

Definition set_finish (s:state) (f:F.finish) : state :=
  mk_state f s.(get_fstate).

Module Semantics.

Require Import HJ.Phasers.Lang.
Import F.Semantics.
Module FS := F.Semantics.

Inductive op := 
  | BEGIN_ASYNC : list phased -> tid -> op
  | END_ASYNC
  | BEGIN_FINISH
  | END_FINISH
  | PH_NEW : phid -> op
  | PH_SIGNAL : phid -> op
  | PH_DROP : phid -> op
  | SIGNAL_ALL : op
  | WAIT_ALL : op.

Inductive packet :=
  | only_p: P.op -> packet
  | only_f: FS.op -> packet
  | both: P.op -> FS.op -> packet.

Definition translate (o:op) : packet :=
  match o with
  | BEGIN_ASYNC ps t => both (P.ASYNC ps t) (FS.BEGIN_ASYNC t)
  | END_ASYNC => both (P.DROP_ALL) (FS.END_ASYNC)
  | BEGIN_FINISH => only_f FS.BEGIN_FINISH
  | END_FINISH => only_f FS.END_FINISH
  | PH_NEW p => only_p (P.PH_NEW p)
  | PH_SIGNAL p => only_p (P.PH_SIGNAL p)
  | PH_DROP p => only_p (P.PH_DROP p)
  | SIGNAL_ALL => only_p (P.SIGNAL_ALL)
  | WAIT_ALL => only_p (P.WAIT_ALL)
  end.

Inductive PhasermapOf (s:state) (t:tid) (f:fid) (m:phasermap) : Prop :=
  phasermap_of:
    FID (get_finish s) t f ->
    Map_FID.MapsTo f m s.(get_fstate) ->
    PhasermapOf s t f m.

Inductive Reduce (s:state) (t:tid) (o:op) : state -> Prop :=
  | reduce_p:
    forall f m m' o',
    PhasermapOf s t f m ->
    translate o = only_p o' ->
    P.Reduce m t o' m' ->
    Reduce s t o (put_phasermap s f m')
  | reduce_f:
    forall f' o',
    translate o = only_f o' ->
    FS.Reduce (get_finish s) t o' f' ->
    Reduce s t o (set_finish s f')
  | reduce_both:
    forall m i m' o' f' o'',
    translate o = both o' o'' ->
    PhasermapOf s t i m ->
    P.Reduce m t o' m' ->
    FS.Reduce (get_finish s) t o'' f' ->
    Reduce s t o
      (set_finish (put_phasermap s i m') f').
End Semantics.
