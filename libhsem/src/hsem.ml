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

let string_to_op (o:string) : package_op = List.find (fun x -> fst x = o) all_ops |> snd
let op_to_string (o:package_op) : string = List.find (fun x -> snd x = o) all_ops |> fst

let err_line_prefix msg lineno =match lineno with
  | Some l ->
    let msg = if msg = "" then "" else msg ^ " " in
    "Error " ^ msg ^ "at line #" ^ string_of_int l ^ ": "
  | None -> ""

let json_to_package j lineno =
  let open Yojson.Basic.Util in
  try begin
    let o : string = member "op" j |> to_string in
    let replace_null d j = match j with
      | `Null -> d
      | _ -> j
    in
    try {
      pkg_task = member "task" j |> to_int;
      pkg_op = string_to_op o;
      pkg_id = member "id" j |> to_int;
      pkg_time = member "time" j |> to_int;
      pkg_args = member "args" j |> replace_null (`List []) |> to_list |> List.map to_int;
      pkg_lineno = lineno
    } with | Not_found -> raise (Err (err_line_prefix "parsing" lineno ^ "Unknown operation " ^ o))
  end with | Type_error (e,_) -> raise (Err (err_line_prefix "parsing" lineno ^ e))

let package_to_json p =
  let open Yojson.Basic.Util in
  let lineno = match p.pkg_lineno with
    | Some x -> `Int x
    | _ -> `Null
  in
  `Assoc [
    "pkg_task", `Int (pkg_task p);
    "pkg_op", `String (op_to_string (pkg_op p));
    "pkg_id", `Int (pkg_id p);
    "pkg_time", `Int (pkg_time p);
    "pkg_args", `List (pkg_args p |> List.map (fun x -> `Int x));
    "pkg_lineno", lineno
  ]


let run_err_to_string (r:Finish.checks_err) : string =
  let pkg_parse_err_to_string e = match e with
    | PKG_PARSE_NOARGS_EXPECTED -> "Expected 0 arguments."
    | PKG_PARSE_TASK_EXPECTED -> "Expected 1 task identifier."
  in
  let reduces_err_to_string (e:Finish.reduces_err) = match e with
    | TASK_EXIST x -> "Expecting task " ^ string_of_int x ^ " to be new, but it already exists."
    | TASK_NOT_EXIST x -> "Task " ^ string_of_int x ^ " does not exist."
    | FINISH_EXIST x -> "Expecting finish " ^ string_of_int x ^ " to be new, but it already exists."
    | FINISH_NOT_EXIST x -> "Finish " ^ string_of_int x ^ " does not exist."
    | FINISH_NONEMPTY x -> "Invoked END_FINISH, but finish " ^ string_of_int x ^ " is not empty."
    | FINISH_OPEN_EMPTY -> "Invoked END_FINISH, but there are 0 open finish scopes."
  in
  let reduces_n_err_to_string n e =
    "Error checking line #" ^ string_of_int n ^": " ^
    reduces_err_to_string e
  in
  match r with
  | CHECKS_PARSE_TRACE_ERROR (p, e) -> (
    let args : string = Yojson.Basic.pretty_to_string (`List (pkg_args p |> List.map (fun x -> `Int x))) in
    err_line_prefix "parsing" p.pkg_lineno ^ pkg_parse_err_to_string e ^ " Obtained: " ^ args
  )
  | CHECKS_REDUCES_N_ERROR (p, e) -> (
    match p.pkg_lineno with
    | Some n -> reduces_n_err_to_string n e
    | None -> reduces_err_to_string e
  )
  | CHECKS_INTERNAL_ERROR -> "Unexpected internal error."

let parse (filename:string) =
  let stream_file c = Stream.from (fun _ ->
     try Some (input_line c) with End_of_file -> None) in
  let chk = ref Finish.checks_make in (* initialize hchecks *)
  let chan = open_in filename in
  let lineno = ref 0 in
  let do_iter line =
    lineno := !lineno + 1;
    let line = String.trim line in
    if (line <> "") && (String.get line 0 <> '#') then begin
      try begin
        let j = Yojson.Basic.from_string line in
        let pkg = json_to_package j (Some !lineno)  in
        match Finish.checks_add pkg !chk with
        | Inl s' -> chk := s'
        | Inr e -> raise (Err (run_err_to_string e))
      end with Yojson.Json_error e -> raise (Err(err_line_prefix "parsing" (Some !lineno) ^ e))
    end
  in
  Stream.iter do_iter (stream_file chan);
  close_in chan;
  !chk

