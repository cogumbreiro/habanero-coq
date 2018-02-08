open Ctypes
open Foreign
open Finish
open List
open Hsem

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

(** Converts a C habanero_action into a Finish.package *)

let pkg_new a : Finish.package option =
  match nat_to_op (getf a a_op) with
  | Some o -> Some {
      pkg_task = getf a a_task;
      pkg_op = o;
      pkg_id = getf a a_id;
      pkg_time = getf a a_time;
      pkg_args = nat_to_args o (getf a a_arg);
      pkg_lineno = None
    }
  | None -> None

let habanero_check (s:habanero_checks ptr) (a:habanero_action) : int =
  let ptr = to_voidp s in
  let s = Root.get ptr in
  match pkg_new a with
  | None -> 0
  | Some p ->
    match Finish.checks_add p s with
    | Inl s' -> Root.set ptr s'; 1
    | Inr _ -> 0

let habanero_count (s: habanero_checks ptr): int =
  to_voidp s |> Root.get |> Finish.count_enqueued

let habanero_parse (filename:string) on_error : habanero_checks ptr =
  let stream_file c = Stream.from (fun _ ->
     try Some (input_line c) with End_of_file -> None) in
  let chk = ref Finish.checks_make in (* initialize hchecks *)
  let chan = open_in filename in
  let lineno = ref 0 in
  try (
    Stream.iter (fun line ->
      lineno := !lineno + 1;
      let line = String.trim line in
      if (line <> "") && (String.get line 0 <> '#') then (
        let pkg = json_to_package (Yojson.Basic.from_string line) (Some !lineno)  in
        match Finish.checks_add pkg !chk with
        | Inl s' -> chk := s'
        | Inr e -> raise (Err (run_err_to_string e))
      ) else () (* nothing to do *)
    ) (stream_file chan);
    close_in chan;
    Root.create (!chk) |> from_voidp habanero_checks
  ) with
  | Err e ->
    on_error e;
    null |> from_voidp habanero_checks

module Stubs(I : Cstubs_inverted.INTERNAL) =
struct
  (* Expose the type 'struct handlers' to C. *)
  let () = I.enum (List.map (fun (k, v) -> (k, op_to_nat v |> Int64.of_int)) all_ops) habanero_op
  let () = I.structure struct_habanero_action
  let () = I.typedef struct_habanero_action "habanero_action"
  let () = I.structure habanero_checks
  let () = I.internal "habanero_checks_new" (void @-> returning (ptr habanero_checks)) habanero_checks_new
  let () = I.internal "habanero_checks_free" (ptr habanero_checks @-> returning void) habanero_checks_free
  let () = I.internal "habanero_checks_add" (ptr habanero_checks @-> habanero_action @-> returning int)
    habanero_check
  let () = I.internal "habanero_checks_open" (string @-> funptr (string @-> returning void) @-> returning (ptr habanero_checks)) habanero_parse
  let () = I.internal "habanero_checks_count_enqueued" (ptr habanero_checks @-> returning int) habanero_count
end
