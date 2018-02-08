(* Define a struct of callbacks (C function pointers) *)
open Finish
open List

let all_ops = [
  ("INIT", PKG_INIT);
  ("BEGIN_FINISH", PKG_BEGIN_FINISH);
  ("END_FINISH", PKG_END_FINISH);
  ("BEGIN_TASK", PKG_BEGIN_TASK);
  ("END_TASK", PKG_END_TASK)
]

exception Err of string

let json_to_package j lineno =
  let open Yojson.Basic.Util in
  try (
    let op = member "op" j |> to_string in
    try (
      {
        pkg_task = member "task" j |> to_int;
        pkg_op = List.find (fun x -> fst x = op) all_ops |> snd;
        pkg_id = member "id" j |> to_int;
        pkg_time = member "time" j |> to_int;
        pkg_args = member "args" j |> to_list |> List.map to_int;
        pkg_lineno = lineno
      }
    ) with | Not_found -> raise (Err ("Unknown operation " ^ op))
  ) with | Type_error (e,_) -> raise (Err ("Error parsing an action: " ^ e))

let run_err_to_string (r:Finish.checks_err) : string =
  let pkg_parse_err_to_string e =
  match e with
  | PKG_PARSE_NOARGS_EXPECTED -> "No arguments expected."
  | PKG_PARSE_TASK_EXPECTED -> "Expected 1 task identifier."
  in
  let parse_trace_err_to_string e =
    match e with
    | PARSE_TRACE_ERR (n, e) -> 
      "Error parsing action " ^ string_of_int n ^ ": " ^
      pkg_parse_err_to_string e
  in
  let reduces_err_to_string (e:Finish.reduces_err) =
    match e with
    | TASK_EXIST x -> "Expecting task " ^ string_of_int x ^ " to be new, but it already exists."
    | TASK_NOT_EXIST x -> "Task " ^ string_of_int x ^ " does not exist."
    | FINISH_EXIST x -> "Expecting finish " ^ string_of_int x ^ " to be new, but it already exists."
    | FINISH_NOT_EXIST x -> "Finish " ^ string_of_int x ^ " does not exist."
    | FINISH_NONEMPTY x -> "Invoked END_FINISH, but finish " ^ string_of_int x ^ " is not empty."
    | FINISH_OPEN_EMPTY -> "Invoked END_FINISH, but there are 0 open finish scopes."
  in
  let reduces_n_err_to_string n e =
    "Error checking action #" ^ string_of_int n ^": " ^
    reduces_err_to_string e
  in
  match r with
  | CHECKS_PARSE_TRACE_ERROR e -> parse_trace_err_to_string e
  | CHECKS_REDUCES_N_ERROR (p, e) -> (
    match p.pkg_lineno with
    | Some n -> reduces_n_err_to_string n e
    | None -> reduces_err_to_string e
  )
  | CHECKS_INTERNAL_ERROR -> "Internal error!"

let parse (filename:string) =
  let stream_file c = Stream.from (fun _ ->
     try Some (input_line c) with End_of_file -> None) in
  let chk = ref Finish.checks_make in (* initialize hchecks *)
  let chan = open_in filename in
  let lineno = ref 0 in
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
  !chk

