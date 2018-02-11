
type __ = Obj.t

type unit0 =
| Tt

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



module type DecidableTypeOrig =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac :
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 sig
 end

module Nat :
 sig
  val eqb : int -> int -> bool

  val compare : int -> int -> comparison
 end

val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val rev : 'a1 list -> 'a1 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val partition : ('a1 -> bool) -> 'a1 list -> 'a1 list*'a1 list

val split : ('a1*'a2) list -> 'a1 list*'a2 list

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module OrderedTypeFacts :
 functor (O:OrderedType) ->
 sig
  module TO :
   sig
    type t = O.t
   end

  module IsTO :
   sig
   end

  module OrderTac :
   sig
   end

  val eq_dec : O.t -> O.t -> bool

  val lt_dec : O.t -> O.t -> bool

  val eqb : O.t -> O.t -> bool
 end

module KeyOrderedType :
 functor (O:OrderedType) ->
 sig
  module MO :
   sig
    module TO :
     sig
      type t = O.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : O.t -> O.t -> bool

    val lt_dec : O.t -> O.t -> bool

    val eqb : O.t -> O.t -> bool
   end
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val eq_dec : positive -> positive -> bool
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val max : z -> z -> z

  val eq_dec : z -> z -> bool
 end

module Nat_as_OT :
 sig
  val compare : int -> int -> int compare0
 end

module type DecidableType =
 DecidableTypeOrig

module type WS =
 sig
  module E :
   DecidableType

  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key*'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Raw :
 functor (X:OrderedType) ->
 sig
  module MX :
   sig
    module TO :
     sig
      type t = X.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : X.t -> X.t -> bool

    val lt_dec : X.t -> X.t -> bool

    val eqb : X.t -> X.t -> bool
   end

  module PX :
   sig
    module MO :
     sig
      module TO :
       sig
        type t = X.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end
   end

  type key = X.t

  type 'elt t = (X.t*'elt) list

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val mem : key -> 'a1 t -> bool

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * bool * 'elt coq_R_mem

  val coq_R_mem_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
    __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> __ ->
    __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
    coq_R_mem -> 'a2

  val coq_R_mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
    __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> __ ->
    __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
    coq_R_mem -> 'a2

  val mem_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
    __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
    __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

  val find : key -> 'a1 t -> 'a1 option

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt option
     * 'elt coq_R_find

  val coq_R_find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
    __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> __ ->
    __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option
    -> 'a1 coq_R_find -> 'a2

  val coq_R_find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
    __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> __ ->
    __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option
    -> 'a1 coq_R_find -> 'a2

  val find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
    __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
    __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt t * 'elt coq_R_add

  val coq_R_add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
    -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
    'a1 coq_R_add -> 'a2

  val coq_R_add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
    -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
    'a1 coq_R_add -> 'a2

  val add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

  val remove : key -> 'a1 t -> 'a1 t

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt t
     * 'elt coq_R_remove

  val coq_R_remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
    __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> __ ->
    __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
    coq_R_remove -> 'a2

  val coq_R_remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
    __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> __ ->
    __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
    coq_R_remove -> 'a2

  val remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
    __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
    __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

  val elements : 'a1 t -> 'a1 t

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t*'elt) list * 'a
     * ('elt, 'a) coq_R_fold

  val coq_R_fold_rect :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a2 -> ('a1, 'a2) coq_R_fold
    -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

  val coq_R_fold_rec :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a2 -> ('a1, 'a2) coq_R_fold
    -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

  val fold_rect :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t -> 'a2
    -> 'a3

  val fold_rec :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t -> 'a2
    -> 'a3

  val coq_R_fold_correct :
    (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t*'elt) list * X.t * 
     'elt * (X.t*'elt) list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t*'elt) list * X.t * 
     'elt * (X.t*'elt) list * X.t compare0
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

  val coq_R_equal_rect :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1)
    list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1
    t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
    (X.t*'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1
    t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool
    -> 'a1 coq_R_equal -> 'a2

  val coq_R_equal_rec :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1)
    list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1
    t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
    (X.t*'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1
    t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool
    -> 'a1 coq_R_equal -> 'a2

  val equal_rect :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1)
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
    (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t
    compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t
    -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

  val equal_rec :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1)
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
    (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t
    compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t
    -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

  val coq_R_equal_correct :
    ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val option_cons : key -> 'a1 option -> (key*'a1) list -> (key*'a1) list

  val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

  val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val combine : 'a1 t -> 'a2 t -> ('a1 option*'a2 option) t

  val fold_right_pair :
    ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1*'a2) list -> 'a3 -> 'a3

  val map2_alt :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key*'a3)
    list

  val at_least_one :
    'a1 option -> 'a2 option -> ('a1 option*'a2 option) option

  val at_least_one_then_f :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
    'a3 option
 end

module type Int =
 sig
  type t

  val i2z : t -> z

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int :
 sig
  type t = z

  val _0 : z

  val _1 : z

  val _2 : z

  val _3 : z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val max : z -> z -> z

  val eqb : z -> z -> bool

  val ltb : z -> z -> bool

  val leb : z -> z -> bool

  val eq_dec : z -> z -> bool

  val gt_le_dec : z -> z -> bool

  val ge_lt_dec : z -> z -> bool

  val i2z : t -> z
 end

module Coq_Raw :
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  val tree_rect :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
    -> 'a1 tree -> 'a2

  val tree_rec :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
    -> 'a1 tree -> 'a2

  val height : 'a1 tree -> I.t

  val cardinal : 'a1 tree -> int

  val empty : 'a1 tree

  val is_empty : 'a1 tree -> bool

  val mem : X.t -> 'a1 tree -> bool

  val find : X.t -> 'a1 tree -> 'a1 option

  val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

  val remove_min : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree*(key*'a1)

  val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

  val remove : X.t -> 'a1 tree -> 'a1 tree

  val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  val t_left : 'a1 triple -> 'a1 tree

  val t_opt : 'a1 triple -> 'a1 option

  val t_right : 'a1 triple -> 'a1 tree

  val split : X.t -> 'a1 tree -> 'a1 triple

  val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

  val elements_aux : (key*'a1) list -> 'a1 tree -> (key*'a1) list

  val elements : 'a1 tree -> (key*'a1) list

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  val enumeration_rect :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2

  val enumeration_rec :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2

  val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

  val equal_more :
    ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool

  val equal_cont :
    ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool

  val equal_end : 'a1 enumeration -> bool

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

  val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

  val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

  val map2_opt :
    (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
    ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
    tree

  module Proofs :
   sig
    module MX :
     sig
      module TO :
       sig
        type t = X.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end

    module PX :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end
     end

    module L :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end
       end

      type key = X.t

      type 'elt t = (X.t*'elt) list

      val empty : 'a1 t

      val is_empty : 'a1 t -> bool

      val mem : key -> 'a1 t -> bool

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt t
      | R_mem_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
      | R_mem_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
      | R_mem_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * bool
         * 'elt coq_R_mem

      val coq_R_mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
        bool -> 'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
        bool -> 'a1 coq_R_mem -> 'a2

      val mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

      val find : key -> 'a1 t -> 'a1 option

      type 'elt coq_R_find =
      | R_find_0 of 'elt t
      | R_find_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
      | R_find_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
      | R_find_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt option
         * 'elt coq_R_find

      val coq_R_find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) ->
        'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) ->
        'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

      val add : key -> 'a1 -> 'a1 t -> 'a1 t

      type 'elt coq_R_add =
      | R_add_0 of 'elt t
      | R_add_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
      | R_add_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
      | R_add_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt t
         * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
        'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
        'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

      val add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

      val remove : key -> 'a1 t -> 'a1 t

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt t
      | R_remove_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
      | R_remove_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
      | R_remove_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt t
         * 'elt coq_R_remove

      val coq_R_remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
        t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
        t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

      val remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1) list
        -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

      val elements : 'a1 t -> 'a1 t

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

      type ('elt, 'a) coq_R_fold =
      | R_fold_0 of 'elt t * 'a
      | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t*'elt) list * 'a
         * ('elt, 'a) coq_R_fold

      val coq_R_fold_rect :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3

      val coq_R_fold_rec :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3

      val fold_rect :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t
        -> 'a2 -> 'a3

      val fold_rec :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t
        -> 'a2 -> 'a3

      val coq_R_fold_correct :
        (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

      type 'elt coq_R_equal =
      | R_equal_0 of 'elt t * 'elt t
      | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t*'elt) list * 
         X.t * 'elt * (X.t*'elt) list * bool * 'elt coq_R_equal
      | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t*'elt) list * 
         X.t * 'elt * (X.t*'elt) list * X.t compare0
      | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

      val coq_R_equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
        'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t
        -> 'a1 -> (X.t*'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
        ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t
        -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

      val coq_R_equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
        'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t
        -> 'a1 -> (X.t*'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
        ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t
        -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

      val equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
        X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1) list ->
        __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t ->
        __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

      val equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
        (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
        X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1) list ->
        __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t ->
        __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

      val coq_R_equal_correct :
        ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

      val option_cons : key -> 'a1 option -> (key*'a1) list -> (key*'a1) list

      val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

      val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

      val combine : 'a1 t -> 'a2 t -> ('a1 option*'a2 option) t

      val fold_right_pair :
        ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1*'a2) list -> 'a3 -> 'a3

      val map2_alt :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
        (key*'a3) list

      val at_least_one :
        'a1 option -> 'a2 option -> ('a1 option*'a2 option) option

      val at_least_one_then_f :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option
        -> 'a3 option
     end

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem

    val coq_R_mem_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
      'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
      tree -> bool -> 'a1 coq_R_mem -> 'a2

    val coq_R_mem_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
      'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
      tree -> bool -> 'a1 coq_R_mem -> 'a2

    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find

    val coq_R_find_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

    val coq_R_find_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

    val coq_R_bal_rect :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
      'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
      -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
      __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      'a1 tree -> 'a1 coq_R_bal -> 'a2

    val coq_R_bal_rec :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
      'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
      -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
      __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      'a1 tree -> 'a1 coq_R_bal -> 'a2

    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add

    val coq_R_add_rect :
      key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

    val coq_R_add_rec :
      key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree*(key*'elt))
       * 'elt coq_R_remove_min * 'elt tree * (key*'elt)

    val coq_R_remove_min_rect :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
      -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree ->
      (key*'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
      tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2

    val coq_R_remove_min_rec :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
      -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree ->
      (key*'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
      tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2

    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key*'elt) * key * 'elt

    val coq_R_merge_rect :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key*'a1) ->
      __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
      'a1 coq_R_merge -> 'a2

    val coq_R_merge_rec :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key*'a1) ->
      __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
      'a1 coq_R_merge -> 'a2

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove

    val coq_R_remove_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

    val coq_R_remove_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key*'elt)

    val coq_R_concat_rect :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key*'a1) ->
      __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat ->
      'a2

    val coq_R_concat_rec :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key*'a1) ->
      __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat ->
      'a2

    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree

    val coq_R_split_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2)
      -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __
      -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option
      -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2

    val coq_R_split_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2)
      -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __
      -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option
      -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2

    type ('elt, 'x) coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option

    val coq_R_map_option_rect :
      (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
      tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3

    val coq_R_map_option_rec :
      (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
      tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3

    type ('elt, 'x0, 'x) coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'x0 tree
    | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
       * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt

    val coq_R_map2_opt_rect :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
      tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t -> __ ->
      'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree ->
      ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
      coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
      tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ ->
      'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
      'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3
      tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

    val coq_R_map2_opt_rec :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
      tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t -> __ ->
      'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree ->
      ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
      coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
      tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ ->
      'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
      'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3
      tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

    val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    val flatten_e : 'a1 enumeration -> (key*'a1) list
   end
 end

module IntMake :
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig
  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  module Raw :
   sig
    type key = X.t

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * I.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2

    val height : 'a1 tree -> I.t

    val cardinal : 'a1 tree -> int

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : X.t -> 'a1 tree -> bool

    val find : X.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree*(key*'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : X.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : X.t -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key*'a1) list -> 'a1 tree -> (key*'a1) list

    val elements : 'a1 tree -> (key*'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = X.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : X.t -> X.t -> bool

            val lt_dec : X.t -> X.t -> bool

            val eqb : X.t -> X.t -> bool
           end
         end

        type key = X.t

        type 'elt t = (X.t*'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * bool
           * 'elt coq_R_mem

        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) ->
          'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) ->
          'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

        val find : key -> 'a1 t -> 'a1 option

        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt option
           * 'elt coq_R_find

        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
          'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
          'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt t
           * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
          -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
          -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

        val remove : key -> 'a1 t -> 'a1 t

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt t
           * 'elt coq_R_remove

        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2)
          -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2)
          -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of 'elt t * 'a
        | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t*'elt) list * 'a
           * ('elt, 'a) coq_R_fold

        val coq_R_fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val coq_R_fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
          t -> 'a2 -> 'a3

        val fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
          t -> 'a2 -> 'a3

        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t*'elt) list * 
           X.t * 'elt * (X.t*'elt) list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t*'elt) list * 
           X.t * 'elt * (X.t*'elt) list * X.t compare0
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2
          -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
          X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t compare0 -> __ -> __ ->
          'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
          -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2
          -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
          X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t compare0 -> __ -> __ ->
          'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
          -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
          -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t
          -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
          -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t
          -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key*'a1) list -> (key*'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option*'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1*'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key*'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option*'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * bool * 'elt coq_R_mem

      val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
         I.t
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
         I.t
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2

      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * I.t * ('elt tree*(key*'elt))
         * 'elt coq_R_remove_min * 'elt tree * (key*'elt)

      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree ->
        (key*'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
        tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2

      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree ->
        (key*'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
        tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2

      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * (key*'elt) * key * 'elt

      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key*'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key*'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt tree * 'elt coq_R_remove

      val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * (key*'elt)

      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key*'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2

      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key*'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2

      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
         * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
         * 'elt tree

      val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2

      val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2

      type ('elt, 'x) coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option

      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3

      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3

      type ('elt, 'x0, 'x) coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'x0 tree
      | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 
         'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 
         'x0 tree * 'x0 option * 'x0 tree * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt

      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key*'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = E.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key*'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Make :
 functor (X:OrderedType) ->
 sig
  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  module Raw :
   sig
    type key = X.t

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val height : 'a1 tree -> Z_as_Int.t

    val cardinal : 'a1 tree -> int

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : X.t -> 'a1 tree -> bool

    val find : X.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree*(key*'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : X.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : X.t -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key*'a1) list -> 'a1 tree -> (key*'a1) list

    val elements : 'a1 tree -> (key*'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = X.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : X.t -> X.t -> bool

            val lt_dec : X.t -> X.t -> bool

            val eqb : X.t -> X.t -> bool
           end
         end

        type key = X.t

        type 'elt t = (X.t*'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * bool
           * 'elt coq_R_mem

        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) ->
          'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) ->
          'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

        val find : key -> 'a1 t -> 'a1 option

        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt option
           * 'elt coq_R_find

        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
          'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
          'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt t
           * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
          -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
          -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

        val remove : key -> 'a1 t -> 'a1 t

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t*'elt) list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t*'elt) list * 'elt t
           * 'elt coq_R_remove

        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2)
          -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2)
          -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of 'elt t * 'a
        | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t*'elt) list * 'a
           * ('elt, 'a) coq_R_fold

        val coq_R_fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val coq_R_fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
          t -> 'a2 -> 'a3

        val fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
          t -> 'a2 -> 'a3

        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t*'elt) list * 
           X.t * 'elt * (X.t*'elt) list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t*'elt) list * 
           X.t * 'elt * (X.t*'elt) list * X.t compare0
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2
          -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
          X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t compare0 -> __ -> __ ->
          'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
          -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2
          -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ ->
          X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t compare0 -> __ -> __ ->
          'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
          -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
          -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t
          -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 ->
          (X.t*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
          -> X.t -> 'a1 -> (X.t*'a1) list -> __ -> X.t -> 'a1 -> (X.t*'a1)
          list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t
          -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key*'a1) list -> (key*'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option*'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1*'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key*'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option*'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem

      val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
        'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
        'a1 coq_R_find -> 'a2

      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2

      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * Z_as_Int.t * ('elt tree*(key*'elt))
         * 'elt coq_R_remove_min * 'elt tree * (key*'elt)

      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min ->
        'a2 -> 'a1 tree -> (key*'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2

      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min ->
        'a2 -> 'a1 tree -> (key*'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2

      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key*'elt) * key * 'elt

      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key*'a1) -> __ -> key -> 'a1 -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key*'a1) -> __ -> key -> 'a1 -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

      val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2

      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key*'elt)

      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key*'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key*'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree

      val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      type ('elt, 'x) coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 
         'x tree * ('elt, 'x) coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option

      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      type ('elt, 'x0, 'x) coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'x0 tree
      | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt

      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key*'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = E.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key*'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module WFacts_fun :
 functor (E:DecidableType) ->
 functor (M:sig
  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key*'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end) ->
 sig
  val eqb : E.t -> E.t -> bool

  val coq_In_dec : 'a1 M.t -> M.key -> bool
 end

module WFacts :
 functor (M:WS) ->
 sig
  val eqb : M.E.t -> M.E.t -> bool

  val coq_In_dec : 'a1 M.t -> M.key -> bool
 end

module Facts :
 functor (M:WS) ->
 sig
  val eqb : M.E.t -> M.E.t -> bool

  val coq_In_dec : 'a1 M.t -> M.key -> bool
 end

module WProperties_fun :
 functor (E:DecidableType) ->
 functor (M:sig
  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key*'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end) ->
 sig
  module F :
   sig
    val eqb : E.t -> E.t -> bool

    val coq_In_dec : 'a1 M.t -> M.key -> bool
   end

  val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1*'a2) -> 'a3

  val of_list : (M.key*'a1) list -> 'a1 M.t

  val to_list : 'a1 M.t -> (M.key*'a1) list

  val fold_rec :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ -> 'a3)
    -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __ -> 'a3 ->
    'a3) -> 'a3

  val fold_rec_bis :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t ->
    'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __
    -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_nodep :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key -> 'a1 ->
    'a2 -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_weak :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 -> __
    -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ -> 'a3 ->
    'a3) -> 'a1 M.t -> 'a3

  val fold_rel :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2 ->
    'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4)
    -> 'a4

  val map_induction :
    ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1 ->
    __ -> __ -> 'a2) -> 'a1 M.t -> 'a2

  val map_induction_bis :
    ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 -> 'a1
    M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2

  val cardinal_inv_2 : 'a1 M.t -> int -> (M.key*'a1)

  val cardinal_inv_2b : 'a1 M.t -> (M.key*'a1)

  val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t

  val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

  val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

  val partition : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t*'a1 M.t

  val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val coq_Partition_In : 'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool

  val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool

  val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t

  val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t

  val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool

  val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool

  val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool

  val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool

  val partition_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t*'a1 M.t

  val partition_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t*'a1 M.t
 end

module WProperties :
 functor (M:WS) ->
 sig
  module F :
   sig
    val eqb : M.E.t -> M.E.t -> bool

    val coq_In_dec : 'a1 M.t -> M.key -> bool
   end

  val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1*'a2) -> 'a3

  val of_list : (M.key*'a1) list -> 'a1 M.t

  val to_list : 'a1 M.t -> (M.key*'a1) list

  val fold_rec :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ -> 'a3)
    -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __ -> 'a3 ->
    'a3) -> 'a3

  val fold_rec_bis :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t ->
    'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __
    -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_nodep :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key -> 'a1 ->
    'a2 -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_weak :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 -> __
    -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ -> 'a3 ->
    'a3) -> 'a1 M.t -> 'a3

  val fold_rel :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2 ->
    'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4)
    -> 'a4

  val map_induction :
    ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1 ->
    __ -> __ -> 'a2) -> 'a1 M.t -> 'a2

  val map_induction_bis :
    ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 -> 'a1
    M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2

  val cardinal_inv_2 : 'a1 M.t -> int -> (M.key*'a1)

  val cardinal_inv_2b : 'a1 M.t -> (M.key*'a1)

  val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t

  val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

  val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

  val partition : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t*'a1 M.t

  val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val coq_Partition_In : 'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool

  val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool

  val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t

  val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t

  val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool

  val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool

  val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool

  val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool

  val partition_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t*'a1 M.t

  val partition_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t*'a1 M.t
 end

module Properties :
 functor (M:WS) ->
 sig
  module F :
   sig
    val eqb : M.E.t -> M.E.t -> bool

    val coq_In_dec : 'a1 M.t -> M.key -> bool
   end

  val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1*'a2) -> 'a3

  val of_list : (M.key*'a1) list -> 'a1 M.t

  val to_list : 'a1 M.t -> (M.key*'a1) list

  val fold_rec :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ -> 'a3)
    -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __ -> 'a3 ->
    'a3) -> 'a3

  val fold_rec_bis :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t ->
    'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __
    -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_nodep :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key -> 'a1 ->
    'a2 -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_weak :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 -> __
    -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ -> 'a3 ->
    'a3) -> 'a1 M.t -> 'a3

  val fold_rel :
    (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2 ->
    'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4)
    -> 'a4

  val map_induction :
    ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1 ->
    __ -> __ -> 'a2) -> 'a1 M.t -> 'a2

  val map_induction_bis :
    ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 -> 'a1
    M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2

  val cardinal_inv_2 : 'a1 M.t -> int -> (M.key*'a1)

  val cardinal_inv_2b : 'a1 M.t -> (M.key*'a1)

  val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t

  val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

  val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

  val partition : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t*'a1 M.t

  val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

  val coq_Partition_In : 'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool

  val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool

  val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t

  val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t

  val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool

  val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool

  val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool

  val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool

  val partition_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t*'a1 M.t

  val partition_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t*'a1 M.t
 end

val omap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list

val supremum :
  'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1 compare0) -> 'a1 list -> 'a1

module MapUtil :
 functor (M:WS) ->
 sig
  module F :
   sig
    val eqb : M.E.t -> M.E.t -> bool

    val coq_In_dec : 'a1 M.t -> M.key -> bool
   end

  module P :
   sig
    module F :
     sig
      val eqb : M.E.t -> M.E.t -> bool

      val coq_In_dec : 'a1 M.t -> M.key -> bool
     end

    val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1*'a2) -> 'a3

    val of_list : (M.key*'a1) list -> 'a1 M.t

    val to_list : 'a1 M.t -> (M.key*'a1) list

    val fold_rec :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ ->
      'a3) -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __ ->
      'a3 -> 'a3) -> 'a3

    val fold_rec_bis :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t
      -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t
      -> __ -> __ -> 'a3 -> 'a3) -> 'a3

    val fold_rec_nodep :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key -> 'a1
      -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val fold_rec_weak :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 -> __
      -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ -> 'a3
      -> 'a3) -> 'a1 M.t -> 'a3

    val fold_rel :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2 ->
      'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 ->
      'a4) -> 'a4

    val map_induction :
      ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1 ->
      __ -> __ -> 'a2) -> 'a1 M.t -> 'a2

    val map_induction_bis :
      ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 -> 'a1
      M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2

    val cardinal_inv_2 : 'a1 M.t -> int -> (M.key*'a1)

    val cardinal_inv_2b : 'a1 M.t -> (M.key*'a1)

    val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t

    val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

    val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool

    val partition : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t*'a1 M.t

    val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

    val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

    val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t

    val coq_Partition_In : 'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool

    val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool

    val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t

    val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t

    val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool

    val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool

    val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool

    val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool

    val partition_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t*'a1 M.t

    val partition_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t*'a1 M.t
   end

  val filter_elements : ((M.key*'a1) -> bool) -> 'a1 M.t -> (M.key*'a1) list

  val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t

  val any_in_dec : 'a1 M.t -> (M.key, unit0) sum

  val in_choice : 'a1 M.t -> bool

  val pred_choice : 'a1 M.t -> (M.E.t -> 'a1 -> bool) -> bool

  val exists_dec :
    (M.key -> 'a1 -> bool) -> 'a1 M.t -> ((M.key*'a1), unit0) sum

  val lookup_dec : M.key -> 'a1 M.t -> ('a1, unit0) sum

  val keys : 'a1 M.t -> M.key list

  val in_dec : M.key -> 'a1 M.t -> bool

  val values : 'a1 M.t -> 'a1 list

  val find_rw : M.key -> 'a1 M.t -> bool

  val omap : (M.E.t -> 'a1 -> 'a2 option) -> 'a1 M.t -> 'a2 M.t

  val supremum :
    M.E.t -> (M.E.t -> M.E.t) -> (M.E.t -> M.E.t -> M.E.t compare0) -> 'a1
    M.t -> M.E.t
 end

type tid = int
  (* singleton inductive, whose constructor was taskid *)

module TID :
 sig
  type t = tid

  val compare : tid -> tid -> tid compare0

  val eq_dec : t -> t -> bool
 end

module Map_TID :
 sig
  module E :
   sig
    type t = tid

    val compare : tid -> tid -> tid compare0

    val eq_dec : tid -> tid -> bool
   end

  module Raw :
   sig
    type key = tid

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val height : 'a1 tree -> Z_as_Int.t

    val cardinal : 'a1 tree -> int

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : tid -> 'a1 tree -> bool

    val find : tid -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree*(key*'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : tid -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : tid -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key*'a1) list -> 'a1 tree -> (key*'a1) list

    val elements : 'a1 tree -> (key*'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> tid -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = tid
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : tid -> tid -> bool

        val lt_dec : tid -> tid -> bool

        val eqb : tid -> tid -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = tid
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : tid -> tid -> bool

          val lt_dec : tid -> tid -> bool

          val eqb : tid -> tid -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = tid
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : tid -> tid -> bool

          val lt_dec : tid -> tid -> bool

          val eqb : tid -> tid -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = tid
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : tid -> tid -> bool

            val lt_dec : tid -> tid -> bool

            val eqb : tid -> tid -> bool
           end
         end

        type key = tid

        type 'elt t = (tid*'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * tid * 'elt * (tid*'elt) list
        | R_mem_2 of 'elt t * tid * 'elt * (tid*'elt) list
        | R_mem_3 of 'elt t * tid * 'elt * (tid*'elt) list * bool
           * 'elt coq_R_mem

        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) ->
          'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) ->
          'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

        val find : key -> 'a1 t -> 'a1 option

        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * tid * 'elt * (tid*'elt) list
        | R_find_2 of 'elt t * tid * 'elt * (tid*'elt) list
        | R_find_3 of 'elt t * tid * 'elt * (tid*'elt) list * 'elt option
           * 'elt coq_R_find

        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
          'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
          'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * tid * 'elt * (tid*'elt) list
        | R_add_2 of 'elt t * tid * 'elt * (tid*'elt) list
        | R_add_3 of 'elt t * tid * 'elt * (tid*'elt) list * 'elt t
           * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
          -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
          -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

        val remove : key -> 'a1 t -> 'a1 t

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * tid * 'elt * (tid*'elt) list
        | R_remove_2 of 'elt t * tid * 'elt * (tid*'elt) list
        | R_remove_3 of 'elt t * tid * 'elt * (tid*'elt) list * 'elt t
           * 'elt coq_R_remove

        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2)
          -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2)
          -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of 'elt t * 'a
        | R_fold_1 of 'elt t * 'a * tid * 'elt * (tid*'elt) list * 'a
           * ('elt, 'a) coq_R_fold

        val coq_R_fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> tid -> 'a1 -> (tid*'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val coq_R_fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> tid -> 'a1 -> (tid*'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> tid -> 'a1 -> (tid*'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
          t -> 'a2 -> 'a3

        val fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> tid -> 'a1 -> (tid*'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
          t -> 'a2 -> 'a3

        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * tid * 'elt * (tid*'elt) list * 
           tid * 'elt * (tid*'elt) list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * tid * 'elt * (tid*'elt) list * 
           tid * 'elt * (tid*'elt) list * tid compare0
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> tid -> 'a1 -> (tid*'a1) list -> __ -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2
          -> 'a2) -> ('a1 t -> 'a1 t -> tid -> 'a1 -> (tid*'a1) list -> __ ->
          tid -> 'a1 -> (tid*'a1) list -> __ -> tid compare0 -> __ -> __ ->
          'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
          -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> tid -> 'a1 -> (tid*'a1) list -> __ -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2
          -> 'a2) -> ('a1 t -> 'a1 t -> tid -> 'a1 -> (tid*'a1) list -> __ ->
          tid -> 'a1 -> (tid*'a1) list -> __ -> tid compare0 -> __ -> __ ->
          'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
          -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> tid -> 'a1 -> (tid*'a1) list -> __ -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
          -> tid -> 'a1 -> (tid*'a1) list -> __ -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> tid compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t
          -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> tid -> 'a1 -> (tid*'a1) list -> __ -> tid -> 'a1 ->
          (tid*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
          -> tid -> 'a1 -> (tid*'a1) list -> __ -> tid -> 'a1 -> (tid*'a1)
          list -> __ -> tid compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t
          -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key*'a1) list -> (key*'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option*'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1*'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key*'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option*'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem

      val coq_R_mem_rect :
        tid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        tid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        tid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
        'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        tid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
        'a1 coq_R_find -> 'a2

      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2

      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * Z_as_Int.t * ('elt tree*(key*'elt))
         * 'elt coq_R_remove_min * 'elt tree * (key*'elt)

      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min ->
        'a2 -> 'a1 tree -> (key*'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2

      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min ->
        'a2 -> 'a1 tree -> (key*'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2

      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key*'elt) * key * 'elt

      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key*'a1) -> __ -> key -> 'a1 -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key*'a1) -> __ -> key -> 'a1 -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

      val coq_R_remove_rect :
        tid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        tid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2

      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key*'elt)

      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key*'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key*'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree

      val coq_R_split_rect :
        tid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      val coq_R_split_rec :
        tid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      type ('elt, 'x) coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 
         'x tree * ('elt, 'x) coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option

      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      type ('elt, 'x0, 'x) coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'x0 tree
      | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt

      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key*'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = tid

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key*'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Map_TID_Extra :
 sig
  module F :
   sig
    val eqb : tid -> tid -> bool

    val coq_In_dec : 'a1 Map_TID.t -> Map_TID.key -> bool
   end

  module P :
   sig
    module F :
     sig
      val eqb : tid -> tid -> bool

      val coq_In_dec : 'a1 Map_TID.t -> Map_TID.key -> bool
     end

    val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1*'a2) -> 'a3

    val of_list : (Map_TID.key*'a1) list -> 'a1 Map_TID.t

    val to_list : 'a1 Map_TID.t -> (Map_TID.key*'a1) list

    val fold_rec :
      (Map_TID.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 Map_TID.t -> ('a1
      Map_TID.t -> __ -> 'a3) -> (Map_TID.key -> 'a1 -> 'a2 -> 'a1 Map_TID.t
      -> 'a1 Map_TID.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

    val fold_rec_bis :
      (Map_TID.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 Map_TID.t -> ('a1
      Map_TID.t -> 'a1 Map_TID.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
      (Map_TID.key -> 'a1 -> 'a2 -> 'a1 Map_TID.t -> __ -> __ -> 'a3 -> 'a3)
      -> 'a3

    val fold_rec_nodep :
      (Map_TID.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 Map_TID.t -> 'a3 ->
      (Map_TID.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val fold_rec_weak :
      (Map_TID.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 Map_TID.t -> 'a1
      Map_TID.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (Map_TID.key -> 'a1 ->
      'a2 -> 'a1 Map_TID.t -> __ -> 'a3 -> 'a3) -> 'a1 Map_TID.t -> 'a3

    val fold_rel :
      (Map_TID.key -> 'a1 -> 'a2 -> 'a2) -> (Map_TID.key -> 'a1 -> 'a3 ->
      'a3) -> 'a2 -> 'a3 -> 'a1 Map_TID.t -> 'a4 -> (Map_TID.key -> 'a1 ->
      'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

    val map_induction :
      ('a1 Map_TID.t -> __ -> 'a2) -> ('a1 Map_TID.t -> 'a1 Map_TID.t -> 'a2
      -> Map_TID.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 Map_TID.t -> 'a2

    val map_induction_bis :
      ('a1 Map_TID.t -> 'a1 Map_TID.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
      (Map_TID.key -> 'a1 -> 'a1 Map_TID.t -> __ -> 'a2 -> 'a2) -> 'a1
      Map_TID.t -> 'a2

    val cardinal_inv_2 : 'a1 Map_TID.t -> int -> (Map_TID.key*'a1)

    val cardinal_inv_2b : 'a1 Map_TID.t -> (Map_TID.key*'a1)

    val filter :
      (Map_TID.key -> 'a1 -> bool) -> 'a1 Map_TID.t -> 'a1 Map_TID.t

    val for_all : (Map_TID.key -> 'a1 -> bool) -> 'a1 Map_TID.t -> bool

    val exists_ : (Map_TID.key -> 'a1 -> bool) -> 'a1 Map_TID.t -> bool

    val partition :
      (Map_TID.key -> 'a1 -> bool) -> 'a1 Map_TID.t -> 'a1 Map_TID.t*'a1
      Map_TID.t

    val update : 'a1 Map_TID.t -> 'a1 Map_TID.t -> 'a1 Map_TID.t

    val restrict : 'a1 Map_TID.t -> 'a1 Map_TID.t -> 'a1 Map_TID.t

    val diff : 'a1 Map_TID.t -> 'a1 Map_TID.t -> 'a1 Map_TID.t

    val coq_Partition_In :
      'a1 Map_TID.t -> 'a1 Map_TID.t -> 'a1 Map_TID.t -> Map_TID.key -> bool

    val update_dec :
      'a1 Map_TID.t -> 'a1 Map_TID.t -> Map_TID.key -> 'a1 -> bool

    val filter_dom : (Map_TID.key -> bool) -> 'a1 Map_TID.t -> 'a1 Map_TID.t

    val filter_range : ('a1 -> bool) -> 'a1 Map_TID.t -> 'a1 Map_TID.t

    val for_all_dom : (Map_TID.key -> bool) -> 'a1 Map_TID.t -> bool

    val for_all_range : ('a1 -> bool) -> 'a1 Map_TID.t -> bool

    val exists_dom : (Map_TID.key -> bool) -> 'a1 Map_TID.t -> bool

    val exists_range : ('a1 -> bool) -> 'a1 Map_TID.t -> bool

    val partition_dom :
      (Map_TID.key -> bool) -> 'a1 Map_TID.t -> 'a1 Map_TID.t*'a1 Map_TID.t

    val partition_range :
      ('a1 -> bool) -> 'a1 Map_TID.t -> 'a1 Map_TID.t*'a1 Map_TID.t
   end

  val filter_elements :
    ((Map_TID.key*'a1) -> bool) -> 'a1 Map_TID.t -> (Map_TID.key*'a1) list

  val filter : (Map_TID.key -> 'a1 -> bool) -> 'a1 Map_TID.t -> 'a1 Map_TID.t

  val any_in_dec : 'a1 Map_TID.t -> (Map_TID.key, unit0) sum

  val in_choice : 'a1 Map_TID.t -> bool

  val pred_choice : 'a1 Map_TID.t -> (tid -> 'a1 -> bool) -> bool

  val exists_dec :
    (Map_TID.key -> 'a1 -> bool) -> 'a1 Map_TID.t -> ((Map_TID.key*'a1),
    unit0) sum

  val lookup_dec : Map_TID.key -> 'a1 Map_TID.t -> ('a1, unit0) sum

  val keys : 'a1 Map_TID.t -> Map_TID.key list

  val in_dec : Map_TID.key -> 'a1 Map_TID.t -> bool

  val values : 'a1 Map_TID.t -> 'a1 list

  val find_rw : Map_TID.key -> 'a1 Map_TID.t -> bool

  val omap : (tid -> 'a1 -> 'a2 option) -> 'a1 Map_TID.t -> 'a2 Map_TID.t

  val supremum :
    tid -> (tid -> tid) -> (tid -> tid -> tid compare0) -> 'a1 Map_TID.t ->
    tid
 end

type fid = int
  (* singleton inductive, whose constructor was finishid *)

module FID :
 sig
  type t = fid

  val compare : fid -> fid -> fid compare0

  val eq_dec : t -> t -> bool
 end

module Map_FID :
 sig
  module E :
   sig
    type t = fid

    val compare : fid -> fid -> fid compare0

    val eq_dec : fid -> fid -> bool
   end

  module Raw :
   sig
    type key = fid

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val height : 'a1 tree -> Z_as_Int.t

    val cardinal : 'a1 tree -> int

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : fid -> 'a1 tree -> bool

    val find : fid -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree*(key*'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : fid -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : fid -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key*'a1) list -> 'a1 tree -> (key*'a1) list

    val elements : 'a1 tree -> (key*'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> fid -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = fid
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : fid -> fid -> bool

        val lt_dec : fid -> fid -> bool

        val eqb : fid -> fid -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = fid
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : fid -> fid -> bool

          val lt_dec : fid -> fid -> bool

          val eqb : fid -> fid -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = fid
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : fid -> fid -> bool

          val lt_dec : fid -> fid -> bool

          val eqb : fid -> fid -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = fid
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : fid -> fid -> bool

            val lt_dec : fid -> fid -> bool

            val eqb : fid -> fid -> bool
           end
         end

        type key = fid

        type 'elt t = (fid*'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * fid * 'elt * (fid*'elt) list
        | R_mem_2 of 'elt t * fid * 'elt * (fid*'elt) list
        | R_mem_3 of 'elt t * fid * 'elt * (fid*'elt) list * bool
           * 'elt coq_R_mem

        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) ->
          'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) ->
          'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

        val find : key -> 'a1 t -> 'a1 option

        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * fid * 'elt * (fid*'elt) list
        | R_find_2 of 'elt t * fid * 'elt * (fid*'elt) list
        | R_find_3 of 'elt t * fid * 'elt * (fid*'elt) list * 'elt option
           * 'elt coq_R_find

        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
          'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
          'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * fid * 'elt * (fid*'elt) list
        | R_add_2 of 'elt t * fid * 'elt * (fid*'elt) list
        | R_add_3 of 'elt t * fid * 'elt * (fid*'elt) list * 'elt t
           * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
          -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
          -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

        val remove : key -> 'a1 t -> 'a1 t

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * fid * 'elt * (fid*'elt) list
        | R_remove_2 of 'elt t * fid * 'elt * (fid*'elt) list
        | R_remove_3 of 'elt t * fid * 'elt * (fid*'elt) list * 'elt t
           * 'elt coq_R_remove

        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2)
          -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2)
          -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of 'elt t * 'a
        | R_fold_1 of 'elt t * 'a * fid * 'elt * (fid*'elt) list * 'a
           * ('elt, 'a) coq_R_fold

        val coq_R_fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> fid -> 'a1 -> (fid*'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val coq_R_fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> fid -> 'a1 -> (fid*'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> fid -> 'a1 -> (fid*'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
          t -> 'a2 -> 'a3

        val fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> fid -> 'a1 -> (fid*'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
          t -> 'a2 -> 'a3

        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * fid * 'elt * (fid*'elt) list * 
           fid * 'elt * (fid*'elt) list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * fid * 'elt * (fid*'elt) list * 
           fid * 'elt * (fid*'elt) list * fid compare0
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> fid -> 'a1 -> (fid*'a1) list -> __ -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2
          -> 'a2) -> ('a1 t -> 'a1 t -> fid -> 'a1 -> (fid*'a1) list -> __ ->
          fid -> 'a1 -> (fid*'a1) list -> __ -> fid compare0 -> __ -> __ ->
          'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
          -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> fid -> 'a1 -> (fid*'a1) list -> __ -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2
          -> 'a2) -> ('a1 t -> 'a1 t -> fid -> 'a1 -> (fid*'a1) list -> __ ->
          fid -> 'a1 -> (fid*'a1) list -> __ -> fid compare0 -> __ -> __ ->
          'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
          -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> fid -> 'a1 -> (fid*'a1) list -> __ -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
          -> fid -> 'a1 -> (fid*'a1) list -> __ -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> fid compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t
          -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> fid -> 'a1 -> (fid*'a1) list -> __ -> fid -> 'a1 ->
          (fid*'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
          -> fid -> 'a1 -> (fid*'a1) list -> __ -> fid -> 'a1 -> (fid*'a1)
          list -> __ -> fid compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t
          -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key*'a1) list -> (key*'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option*'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1*'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key*'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option*'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem

      val coq_R_mem_rect :
        fid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        fid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        fid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
        'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        fid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
        'a1 coq_R_find -> 'a2

      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2

      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * Z_as_Int.t * ('elt tree*(key*'elt))
         * 'elt coq_R_remove_min * 'elt tree * (key*'elt)

      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min ->
        'a2 -> 'a1 tree -> (key*'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2

      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min ->
        'a2 -> 'a1 tree -> (key*'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> ('a1 tree*(key*'a1)) -> 'a1 coq_R_remove_min -> 'a2

      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key*'elt) * key * 'elt

      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key*'a1) -> __ -> key -> 'a1 -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key*'a1) -> __ -> key -> 'a1 -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

      val coq_R_remove_rect :
        fid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        fid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2

      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key*'elt)

      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key*'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key*'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree

      val coq_R_split_rect :
        fid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      val coq_R_split_rec :
        fid -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      type ('elt, 'x) coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 
         'x tree * ('elt, 'x) coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option

      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      type ('elt, 'x0, 'x) coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'x0 tree
      | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt

      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key*'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = fid

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key*'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Map_FID_Extra :
 sig
  module F :
   sig
    val eqb : fid -> fid -> bool

    val coq_In_dec : 'a1 Map_FID.t -> Map_FID.key -> bool
   end

  module P :
   sig
    module F :
     sig
      val eqb : fid -> fid -> bool

      val coq_In_dec : 'a1 Map_FID.t -> Map_FID.key -> bool
     end

    val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1*'a2) -> 'a3

    val of_list : (Map_FID.key*'a1) list -> 'a1 Map_FID.t

    val to_list : 'a1 Map_FID.t -> (Map_FID.key*'a1) list

    val fold_rec :
      (Map_FID.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 Map_FID.t -> ('a1
      Map_FID.t -> __ -> 'a3) -> (Map_FID.key -> 'a1 -> 'a2 -> 'a1 Map_FID.t
      -> 'a1 Map_FID.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

    val fold_rec_bis :
      (Map_FID.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 Map_FID.t -> ('a1
      Map_FID.t -> 'a1 Map_FID.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
      (Map_FID.key -> 'a1 -> 'a2 -> 'a1 Map_FID.t -> __ -> __ -> 'a3 -> 'a3)
      -> 'a3

    val fold_rec_nodep :
      (Map_FID.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 Map_FID.t -> 'a3 ->
      (Map_FID.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val fold_rec_weak :
      (Map_FID.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 Map_FID.t -> 'a1
      Map_FID.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (Map_FID.key -> 'a1 ->
      'a2 -> 'a1 Map_FID.t -> __ -> 'a3 -> 'a3) -> 'a1 Map_FID.t -> 'a3

    val fold_rel :
      (Map_FID.key -> 'a1 -> 'a2 -> 'a2) -> (Map_FID.key -> 'a1 -> 'a3 ->
      'a3) -> 'a2 -> 'a3 -> 'a1 Map_FID.t -> 'a4 -> (Map_FID.key -> 'a1 ->
      'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

    val map_induction :
      ('a1 Map_FID.t -> __ -> 'a2) -> ('a1 Map_FID.t -> 'a1 Map_FID.t -> 'a2
      -> Map_FID.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 Map_FID.t -> 'a2

    val map_induction_bis :
      ('a1 Map_FID.t -> 'a1 Map_FID.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
      (Map_FID.key -> 'a1 -> 'a1 Map_FID.t -> __ -> 'a2 -> 'a2) -> 'a1
      Map_FID.t -> 'a2

    val cardinal_inv_2 : 'a1 Map_FID.t -> int -> (Map_FID.key*'a1)

    val cardinal_inv_2b : 'a1 Map_FID.t -> (Map_FID.key*'a1)

    val filter :
      (Map_FID.key -> 'a1 -> bool) -> 'a1 Map_FID.t -> 'a1 Map_FID.t

    val for_all : (Map_FID.key -> 'a1 -> bool) -> 'a1 Map_FID.t -> bool

    val exists_ : (Map_FID.key -> 'a1 -> bool) -> 'a1 Map_FID.t -> bool

    val partition :
      (Map_FID.key -> 'a1 -> bool) -> 'a1 Map_FID.t -> 'a1 Map_FID.t*'a1
      Map_FID.t

    val update : 'a1 Map_FID.t -> 'a1 Map_FID.t -> 'a1 Map_FID.t

    val restrict : 'a1 Map_FID.t -> 'a1 Map_FID.t -> 'a1 Map_FID.t

    val diff : 'a1 Map_FID.t -> 'a1 Map_FID.t -> 'a1 Map_FID.t

    val coq_Partition_In :
      'a1 Map_FID.t -> 'a1 Map_FID.t -> 'a1 Map_FID.t -> Map_FID.key -> bool

    val update_dec :
      'a1 Map_FID.t -> 'a1 Map_FID.t -> Map_FID.key -> 'a1 -> bool

    val filter_dom : (Map_FID.key -> bool) -> 'a1 Map_FID.t -> 'a1 Map_FID.t

    val filter_range : ('a1 -> bool) -> 'a1 Map_FID.t -> 'a1 Map_FID.t

    val for_all_dom : (Map_FID.key -> bool) -> 'a1 Map_FID.t -> bool

    val for_all_range : ('a1 -> bool) -> 'a1 Map_FID.t -> bool

    val exists_dom : (Map_FID.key -> bool) -> 'a1 Map_FID.t -> bool

    val exists_range : ('a1 -> bool) -> 'a1 Map_FID.t -> bool

    val partition_dom :
      (Map_FID.key -> bool) -> 'a1 Map_FID.t -> 'a1 Map_FID.t*'a1 Map_FID.t

    val partition_range :
      ('a1 -> bool) -> 'a1 Map_FID.t -> 'a1 Map_FID.t*'a1 Map_FID.t
   end

  val filter_elements :
    ((Map_FID.key*'a1) -> bool) -> 'a1 Map_FID.t -> (Map_FID.key*'a1) list

  val filter : (Map_FID.key -> 'a1 -> bool) -> 'a1 Map_FID.t -> 'a1 Map_FID.t

  val any_in_dec : 'a1 Map_FID.t -> (Map_FID.key, unit0) sum

  val in_choice : 'a1 Map_FID.t -> bool

  val pred_choice : 'a1 Map_FID.t -> (fid -> 'a1 -> bool) -> bool

  val exists_dec :
    (Map_FID.key -> 'a1 -> bool) -> 'a1 Map_FID.t -> ((Map_FID.key*'a1),
    unit0) sum

  val lookup_dec : Map_FID.key -> 'a1 Map_FID.t -> ('a1, unit0) sum

  val keys : 'a1 Map_FID.t -> Map_FID.key list

  val in_dec : Map_FID.key -> 'a1 Map_FID.t -> bool

  val values : 'a1 Map_FID.t -> 'a1 list

  val find_rw : Map_FID.key -> 'a1 Map_FID.t -> bool

  val omap : (fid -> 'a1 -> 'a2 option) -> 'a1 Map_FID.t -> 'a2 Map_FID.t

  val supremum :
    fid -> (fid -> fid) -> (fid -> fid -> fid compare0) -> 'a1 Map_FID.t ->
    fid
 end

type task = { bind : fid; open0 : fid list }

val bind : task -> fid

val make : fid -> task

type state = task Map_TID.t

type op =
| INIT of fid
| BEGIN_FINISH of fid
| END_FINISH
| BEGIN_TASK of tid
| END_TASK

type action = tid*op

val ief : task -> fid

module Task :
 sig
  val bind_dec : fid -> task -> bool

  val open_dec : fid -> task -> bool

  val in_dec : fid -> task -> bool
 end

val nonempty_empty_dec : fid -> state -> bool

val in_dec0 : fid -> state -> bool

type reduces_err =
| TASK_EXIST of tid
| TASK_NOT_EXIST of tid
| FINISH_EXIST of fid
| FINISH_NOT_EXIST of fid
| FINISH_NONEMPTY of fid
| FINISH_OPEN_EMPTY

val reduces : state -> Map_TID.key -> op -> (state, reduces_err) sum

type package_op =
| PKG_INIT
| PKG_BEGIN_FINISH
| PKG_END_FINISH
| PKG_BEGIN_TASK
| PKG_END_TASK

val nat_to_op : int -> package_op option

val op_to_nat : package_op -> int

val nat_to_args : package_op -> int -> int list

type pkg_parse_err =
| PKG_PARSE_NOARGS_EXPECTED
| PKG_PARSE_TASK_EXPECTED

type package = { pkg_task : tid; pkg_op : package_op; pkg_id : fid;
                 pkg_time : int; pkg_args : int list; pkg_lineno : int option }

val pkg_task : package -> tid

val pkg_op : package -> package_op

val pkg_id : package -> fid

val pkg_time : package -> int

val pkg_args : package -> int list

val pkg_parse : package -> (op, pkg_parse_err) sum

type enq = int*package list

val enq_zero : enq

val enq_cons : package -> enq -> int*package list

val enq_step : int -> package list -> package list*(int*package list)

val enq_partition : int -> package list -> package list*(int*package list)

type buffer = enq Map_FID.t

type checks = { checks_buffer : buffer; checks_state : state }

val checks_buffer : checks -> buffer

val checks_state : checks -> state

val buffer_add : package -> buffer -> package list*buffer

val buffer_add_all : package list -> buffer -> package list*buffer

type parse_trace_err =
| PARSE_TRACE_ERR of int * pkg_parse_err

val parse_trace : package list -> (action list, parse_trace_err) sum

type reduces_n_err =
| REDUCES_N_ERROR of int * reduces_err

val reduces_n : state -> action list -> (state, reduces_n_err) sum

type checks_err =
| CHECKS_REDUCES_N_ERROR of package * reduces_err
| CHECKS_INTERNAL_ERROR
| CHECKS_PARSE_TRACE_ERROR of parse_trace_err

val get : int -> 'a1 list -> 'a1 option

val checks_add : package -> checks -> (checks, checks_err) sum

val checks_make : checks

val count_enqueued : checks -> int

val checks_load : package list -> (checks, checks_err) sum
