open Ctypes
open Foreign
open Finish
(* Define a struct of callbacks (C function pointers) *)

let habanero_op = Ctypes.typedef Ctypes.int "enum habanero_op"

type habanero_checks = [ `C ] structure

let habanero_checks : habanero_checks typ = structure "habanero_checks"

let habanero_checks_new () : habanero_checks ptr =
    let result = Finish.checks_make in
    Root.create result |> from_voidp habanero_checks

let habanero_checks_free p =
  if (ptr_compare (to_voidp p) null) == 0
  then ()
  else to_voidp p |> Root.release

type action_t
type habanero_action = action_t structure
let struct_habanero_action : action_t structure typ = structure "habanero_action"
let habanero_action = typedef struct_habanero_action "habanero_action"
let (--) s f = field struct_habanero_action s f
let a_task = "task" -- int
let a_op = "op" -- habanero_op
let a_id = "id" -- int
let a_time = "time" -- int
let a_arg = "arg" -- int
let () = seal struct_habanero_action

let pkg_new a : Finish.package =
    {
        Finish.pkg_task = getf a a_task;
        Finish.pkg_op = getf a a_op;
        Finish.pkg_id = getf a a_id;
        Finish.pkg_time = getf a a_time;
        Finish.pkg_arg = getf a a_arg;
    }

let habanero_check (s:habanero_checks ptr) (a:habanero_action) : int =
    let ptr = to_voidp s in
    let s = Root.get ptr in
    match Finish.checks_add (pkg_new a) s with
    | Inl s' -> Root.set ptr s'; 1
    | Inr _ -> 0

module Stubs(I : Cstubs_inverted.INTERNAL) =
struct
  (* Expose the type 'struct handlers' to C. *)
  let () = I.enum [
    ("INIT", Int64.of_int 0);
    ("BEGIN_FINISH", Int64.of_int 1);
    ("END_FINISH", Int64.of_int 2);
    ("BEGIN_TASK", Int64.of_int 3);
    ("END_TASK", Int64.of_int 4)] habanero_op

  let () = I.structure struct_habanero_action
  let () = I.typedef struct_habanero_action "habanero_action"
  let () = I.structure habanero_checks
  let () = I.internal "habanero_checks_new" (void @-> returning (ptr habanero_checks)) habanero_checks_new
  let () = I.internal "habanero_checks_free" (ptr habanero_checks @-> returning void) habanero_checks_free
  let () = I.internal "habanero_checks_add" (ptr habanero_checks @-> habanero_action @-> returning int)
    habanero_check
end
