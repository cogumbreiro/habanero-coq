Require HJ.AsyncFinish.Lang.
Module F := HJ.AsyncFinish.Lang.
Require HJ.Phasers.Lang.
Module P := HJ.Phasers.Lang.
Require Import HJ.Vars.

Definition finish_state := Map_TID.t (list P.phasermap).

Inductive state := mk_state {
  get_finish: F.finish;
  get_fstate: finish_state
}.

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

Definition set_phasermaps (t:tid) (l:list phasermap) (s:state) : finish_state :=
  Map_TID.add t l s.(get_fstate).

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

Variable IEFPath: F.finish -> tid -> list tid -> Prop.
Variable PathToPhaser: list tid -> phasermap -> Prop.

Inductive GetPhasermap: tid -> phasermap -> state -> Prop :=
  get_phasermap_def:
    forall t m s p,
    IEFPath (get_finish s) t p ->
    PathToPhaser p m ->
    GetPhasermap t m s.

Variable set_phasermap : state -> tid -> phasermap -> state.
Variable set_finish : state -> F.finish -> state.
Variable update : state -> F.finish -> tid -> phasermap -> state.
Inductive Reduce (s:state) (t:tid) (o:op) : state -> Prop :=
  | reduce_p:
    forall m m' o',
    GetPhasermap t m s ->
    translate o = only_p o' ->
    P.Reduce m t o' m' ->
    Reduce s t o (set_phasermap s t m')
  | reduce_f:
    forall f' o',
    translate o = only_f o' ->
    FS.Reduce (get_finish s) t o' f' ->
    Reduce s t o (set_finish s f')
  | reduce_both:
    forall m m' o' f' o'',
    translate o = both o' o'' ->
    GetPhasermap t m s ->
    P.Reduce m t o' m' ->
    FS.Reduce (get_finish s) t o'' f' ->
    Reduce s t o (update s f' t m').

